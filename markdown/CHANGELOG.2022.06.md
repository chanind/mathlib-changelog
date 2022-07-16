## [2022-06-30 21:59:47](https://github.com/leanprover-community/mathlib/commit/9229b0e)
chore(data/nat/factorization/basic): delete `import tactic.linarith` ([#15075](https://github.com/leanprover-community/mathlib/pull/15075))
Removes the import of `tactic.linarith` that's no longer needed.
#### Estimated changes
Modified src/data/nat/factorization/basic.lean




## [2022-06-30 21:59:46](https://github.com/leanprover-community/mathlib/commit/e7425e7)
feat(data/fin/basic): `induction_zero` and `induction_succ` lemmas ([#15060](https://github.com/leanprover-community/mathlib/pull/15060))
This pull request introduces `fin.induction_zero` and `fin.induction_succ` simp lemmas for `fin.induction`, similar to `fin.cases_zero` and `fin.cases_succ` for `fin.cases`.
#### Estimated changes
Modified src/data/fin/basic.lean
- \+ *lemma* fin.induction_succ
- \+ *lemma* fin.induction_zero



## [2022-06-30 19:45:49](https://github.com/leanprover-community/mathlib/commit/806bbb0)
refactor(algebra/group/defs): rename has_scalar to has_smul ([#14559](https://github.com/leanprover-community/mathlib/pull/14559))
Discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/scalar.20smul.20naming.20discrepancy
#### Estimated changes
Modified scripts/nolints.txt


Modified src/algebra/algebra/basic.lean
- \+/\- *lemma* alg_hom.map_smul_of_tower

Modified src/algebra/algebra/subalgebra/basic.lean
- \+/\- *lemma* subalgebra.coe_algebra_map
- \+/\- *lemma* subalgebra.coe_smul
- \+/\- *lemma* subalgebra.smul_def

Modified src/algebra/algebra/tower.lean


Modified src/algebra/algebra/unitization.lean
- \+/\- *lemma* unitization.coe_smul
- \+/\- *lemma* unitization.fst_mul
- \+/\- *lemma* unitization.fst_smul
- \+/\- *lemma* unitization.inl_smul
- \+/\- *lemma* unitization.snd_mul
- \+/\- *lemma* unitization.snd_smul

Modified src/algebra/category/Module/filtered_colimits.lean


Modified src/algebra/direct_sum/module.lean


Modified src/algebra/direct_sum/ring.lean


Modified src/algebra/field/basic.lean


Modified src/algebra/free_algebra.lean
- \- *def* free_algebra.pre.has_scalar
- \+ *def* free_algebra.pre.has_smul

Modified src/algebra/graded_monoid.lean


Modified src/algebra/group/defs.lean


Modified src/algebra/group/inj_surj.lean


Modified src/algebra/group/ulift.lean


Modified src/algebra/group_power/basic.lean


Modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* units.smul_mk0

Modified src/algebra/hom/group_action.lean


Modified src/algebra/homology/additive.lean


Modified src/algebra/lie/basic.lean


Modified src/algebra/lie/free.lean


Modified src/algebra/lie/quotient.lean


Modified src/algebra/lie/subalgebra.lean


Modified src/algebra/lie/submodule.lean


Modified src/algebra/module/basic.lean
- \+/\- *structure* module.core

Modified src/algebra/module/hom.lean


Modified src/algebra/module/linear_map.lean
- \+/\- *lemma* linear_map.map_smul_of_tower

Modified src/algebra/module/pi.lean
- \+/\- *lemma* is_smul_regular.pi

Modified src/algebra/module/pointwise_pi.lean
- \+/\- *lemma* smul_pi_subset
- \+/\- *lemma* smul_univ_pi

Modified src/algebra/module/prod.lean


Modified src/algebra/module/submodule/basic.lean
- \+/\- *lemma* submodule.coe_smul_of_tower
- \+/\- *lemma* submodule.smul_mem_iff'
- \+/\- *lemma* submodule.smul_of_tower_mem

Modified src/algebra/module/submodule/lattice.lean


Modified src/algebra/module/torsion.lean
- \+/\- *def* module.is_torsion'
- \- *def* module.is_torsion_by_set.has_scalar
- \+ *def* module.is_torsion_by_set.has_smul

Modified src/algebra/module/ulift.lean
- \+/\- *lemma* ulift.smul_down'
- \+/\- *lemma* ulift.smul_down

Modified src/algebra/monoid_algebra/basic.lean


Modified src/algebra/opposites.lean
- \+/\- *lemma* mul_opposite.op_smul
- \+/\- *lemma* mul_opposite.unop_smul

Modified src/algebra/order/field.lean


Modified src/algebra/order/module.lean
- \+/\- *lemma* antitone_smul_left
- \+/\- *lemma* strict_anti_smul_left

Modified src/algebra/order/nonneg.lean


Modified src/algebra/order/ring.lean


Modified src/algebra/order/smul.lean
- \+/\- *lemma* monotone_smul_left
- \+/\- *lemma* order_dual.of_dual_smul
- \+/\- *lemma* order_dual.to_dual_smul
- \+/\- *lemma* strict_mono_smul_left

Modified src/algebra/periodic.lean
- \+/\- *lemma* function.periodic.smul

Modified src/algebra/punit_instances.lean


Modified src/algebra/regular/smul.lean
- \+/\- *def* is_smul_regular

Modified src/algebra/ring/basic.lean


Modified src/algebra/ring_quot.lean


Modified src/algebra/smul_with_zero.lean


Modified src/algebra/star/basic.lean


Modified src/algebra/star/pi.lean


Modified src/algebra/star/prod.lean


Modified src/algebra/star/self_adjoint.lean
- \+/\- *lemma* self_adjoint.coe_smul
- \+/\- *lemma* self_adjoint.smul_mem

Modified src/algebra/symmetrized.lean
- \+/\- *lemma* sym_alg.sym_smul
- \+/\- *lemma* sym_alg.unsym_smul

Modified src/algebra/triv_sq_zero_ext.lean
- \+/\- *lemma* triv_sq_zero_ext.fst_mul
- \+/\- *lemma* triv_sq_zero_ext.fst_smul
- \+/\- *lemma* triv_sq_zero_ext.inl_smul
- \+/\- *lemma* triv_sq_zero_ext.inr_smul
- \+/\- *lemma* triv_sq_zero_ext.snd_mul
- \+/\- *lemma* triv_sq_zero_ext.snd_smul

Modified src/algebra/tropical/basic.lean
- \+/\- *lemma* tropical.trop_smul
- \+/\- *lemma* tropical.untrop_pow

Modified src/analysis/box_integral/partition/additive.lean


Modified src/analysis/calculus/fderiv_symmetric.lean


Modified src/analysis/calculus/formal_multilinear_series.lean


Modified src/analysis/complex/upper_half_plane/basic.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/cone.lean
- \+/\- *structure* convex_cone

Modified src/analysis/convex/extreme.lean


Modified src/analysis/convex/function.lean


Modified src/analysis/convex/quasiconvex.lean


Modified src/analysis/convex/star.lean


Modified src/analysis/convex/strict.lean


Modified src/analysis/locally_convex/balanced_core_hull.lean


Modified src/analysis/locally_convex/basic.lean


Modified src/analysis/locally_convex/bounded.lean


Modified src/analysis/normed/group/hom.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/lp_space.lean


Modified src/analysis/seminorm.lean
- \+/\- *lemma* add_group_seminorm.coe_smul
- \+/\- *lemma* add_group_seminorm.smul_apply
- \+/\- *lemma* add_group_seminorm.smul_sup
- \+/\- *lemma* seminorm.coe_smul
- \+/\- *lemma* seminorm.smul_apply
- \+/\- *lemma* seminorm.smul_inf
- \+/\- *lemma* seminorm.smul_sup
- \+/\- *structure* seminorm

Modified src/data/bracket.lean


Modified src/data/complex/module.lean


Modified src/data/dfinsupp/basic.lean


Modified src/data/fin/vec_notation.lean


Modified src/data/finset/pointwise.lean


Modified src/data/finsupp/basic.lean
- \- *def* finsupp.comap_has_scalar
- \+ *def* finsupp.comap_has_smul

Modified src/data/finsupp/pointwise.lean


Modified src/data/finsupp/to_dfinsupp.lean


Modified src/data/holor.lean


Modified src/data/matrix/basic.lean
- \+/\- *lemma* is_smul_regular.matrix
- \+/\- *lemma* matrix.col_smul
- \+/\- *lemma* matrix.conj_transpose_smul
- \+/\- *theorem* matrix.diag_smul
- \+/\- *lemma* matrix.map_smul
- \+/\- *lemma* matrix.minor_smul
- \+/\- *lemma* matrix.row_smul
- \+/\- *lemma* matrix.transpose_smul

Modified src/data/matrix/block.lean
- \+/\- *lemma* matrix.from_blocks_smul

Modified src/data/matrix/hadamard.lean
- \+/\- *lemma* matrix.hadamard_smul
- \+/\- *lemma* matrix.smul_hadamard

Modified src/data/matrix/kronecker.lean
- \+/\- *lemma* matrix.kronecker_map_smul_left
- \+/\- *lemma* matrix.kronecker_map_smul_right

Modified src/data/matrix/notation.lean
- \+/\- *lemma* matrix.smul_vec2
- \+/\- *lemma* matrix.smul_vec3

Modified src/data/mv_polynomial/basic.lean


Modified src/data/polynomial/basic.lean


Modified src/data/polynomial/laurent.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.coe_smul

Modified src/data/real/nnreal.lean


Modified src/data/set/pointwise.lean
- \+/\- *lemma* set.image2_smul
- \+/\- *theorem* set.range_smul_range
- \+/\- *lemma* set.smul_set_range

Modified src/field_theory/intermediate_field.lean
- \+/\- *lemma* intermediate_field.coe_smul

Modified src/field_theory/ratfunc.lean
- \+/\- *lemma* ratfunc.of_fraction_ring_smul
- \+/\- *lemma* ratfunc.to_fraction_ring_smul

Modified src/field_theory/splitting_field.lean


Modified src/geometry/manifold/algebra/left_invariant_derivation.lean


Modified src/geometry/manifold/algebra/smooth_functions.lean


Modified src/geometry/manifold/derivation_bundle.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/group_action/conj_act.lean


Modified src/group_theory/group_action/defs.lean
- \- *lemma* has_scalar.comp.is_scalar_tower
- \- *def* has_scalar.comp.smul
- \- *lemma* has_scalar.comp.smul_comm_class'
- \- *lemma* has_scalar.comp.smul_comm_class
- \- *def* has_scalar.comp
- \+ *lemma* has_smul.comp.is_scalar_tower
- \+ *def* has_smul.comp.smul
- \+ *lemma* has_smul.comp.smul_comm_class'
- \+ *lemma* has_smul.comp.smul_comm_class
- \+ *def* has_smul.comp
- \+/\- *lemma* is_central_scalar.unop_smul_eq_smul
- \+/\- *lemma* is_scalar_tower.of_smul_one_mul
- \+/\- *lemma* mul_smul_comm
- \+/\- *lemma* smul_assoc
- \+/\- *lemma* smul_comm_class.of_mul_smul_one
- \+/\- *lemma* smul_comm_class.symm
- \+/\- *lemma* smul_left_injective'
- \+/\- *lemma* smul_mul_assoc
- \+/\- *lemma* smul_one_mul
- \+/\- *lemma* smul_one_smul
- \+/\- *lemma* smul_smul_smul_comm

Modified src/group_theory/group_action/embedding.lean


Modified src/group_theory/group_action/opposite.lean
- \+/\- *lemma* mul_opposite.op_smul_eq_op_smul_op
- \+/\- *lemma* mul_opposite.unop_smul_eq_unop_smul_unop

Modified src/group_theory/group_action/pi.lean
- \+/\- *lemma* function.extend_smul
- \+/\- *lemma* function.update_smul
- \+/\- *lemma* pi.smul_apply'
- \+/\- *lemma* pi.smul_apply
- \+/\- *lemma* pi.smul_def
- \+/\- *lemma* set.piecewise_smul

Modified src/group_theory/group_action/prod.lean


Modified src/group_theory/group_action/sigma.lean


Modified src/group_theory/group_action/sub_mul_action.lean
- \+/\- *lemma* sub_mul_action.smul_mem_iff'
- \+/\- *structure* sub_mul_action

Modified src/group_theory/group_action/sum.lean


Modified src/group_theory/group_action/units.lean
- \+/\- *lemma* units.smul_def
- \+/\- *lemma* units.smul_is_unit

Modified src/group_theory/monoid_localization.lean
- \+/\- *lemma* localization.smul_mk

Modified src/group_theory/subgroup/basic.lean


Modified src/group_theory/submonoid/operations.lean
- \+/\- *lemma* submonoid.smul_def

Modified src/linear_algebra/affine_space/affine_map.lean


Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/linear_pmap.lean


Modified src/linear_algebra/matrix/circulant.lean
- \+/\- *lemma* matrix.circulant_smul

Modified src/linear_algebra/matrix/symmetric.lean
- \+/\- *lemma* matrix.is_symm.smul

Modified src/linear_algebra/multilinear/basic.lean


Modified src/linear_algebra/pi_tensor_product.lean


Modified src/linear_algebra/quadratic_form/basic.lean


Modified src/linear_algebra/quotient.lean
- \+/\- *def* submodule.quotient.restrict_scalars_equiv

Modified src/linear_algebra/span.lean
- \+/\- *lemma* submodule.span_le_restrict_scalars
- \+/\- *lemma* submodule.span_singleton_group_smul_eq
- \+/\- *lemma* submodule.span_singleton_smul_le
- \+/\- *lemma* submodule.span_span_of_tower
- \+/\- *lemma* submodule.span_subset_span

Modified src/linear_algebra/tensor_product.lean
- \+/\- *def* tensor_product.smul.aux
- \+/\- *theorem* tensor_product.smul.aux_of

Modified src/logic/equiv/transfer_instance.lean
- \+/\- *lemma* equiv.smul_def

Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/decomposition/jordan.lean


Modified src/measure_theory/function/ae_eq_fun.lean


Modified src/measure_theory/function/conditional_expectation.lean
- \+/\- *lemma* measure_theory.ae_strongly_measurable'.const_smul

Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/function/simple_func_dense_lp.lean


Modified src/measure_theory/function/strongly_measurable.lean


Modified src/measure_theory/group/action.lean


Modified src/measure_theory/group/arithmetic.lean


Modified src/measure_theory/group/fundamental_domain.lean
- \+/\- *structure* measure_theory.is_fundamental_domain

Modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* measure_theory.simple_func.coe_smul
- \+/\- *lemma* measure_theory.simple_func.smul_apply
- \+/\- *lemma* measure_theory.simple_func.smul_eq_map

Modified src/measure_theory/measure/finite_measure_weak_convergence.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/outer_measure.lean
- \+/\- *theorem* measure_theory.outer_measure.smul_supr
- \+/\- *theorem* measure_theory.outer_measure.trim_smul

Modified src/measure_theory/measure/vector_measure.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.eventually_eq.const_smul
- \+/\- *lemma* filter.eventually_eq.smul

Modified src/order/filter/germ.lean
- \+/\- *lemma* filter.germ.coe_smul'
- \+/\- *lemma* filter.germ.coe_smul

Modified src/order/filter/pointwise.lean


Modified src/probability/stopping.lean
- \+/\- *lemma* measure_theory.adapted.smul

Modified src/ring_theory/adjoin/basic.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/algebraic.lean
- \- *def* polynomial.has_scalar_pi
- \+ *def* polynomial.has_smul_pi
- \+/\- *lemma* polynomial_smul_apply

Modified src/ring_theory/derivation.lean
- \+/\- *lemma* derivation.map_smul_of_tower

Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/graded_algebra/homogeneous_localization.lean


Modified src/ring_theory/hahn_series.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/localization/integer.lean


Modified src/ring_theory/localization/localization_localization.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/subring/basic.lean
- \+/\- *lemma* subring.smul_def

Modified src/ring_theory/subsemiring/basic.lean
- \+/\- *lemma* subsemiring.smul_def

Modified src/ring_theory/witt_vector/defs.lean


Modified src/ring_theory/witt_vector/truncated.lean


Modified src/tactic/abel.lean


Modified src/topology/algebra/const_mul_action.lean


Modified src/topology/algebra/continuous_affine_map.lean


Modified src/topology/algebra/module/basic.lean
- \+/\- *lemma* continuous_linear_map.map_smul_of_tower

Modified src/topology/algebra/module/multilinear.lean


Modified src/topology/algebra/module/weak_dual.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/mul_action.lean


Modified src/topology/algebra/uniform_mul_action.lean


Modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* continuous_map.coe_smul
- \+/\- *lemma* continuous_map.smul_apply
- \+/\- *lemma* continuous_map.smul_comp

Modified src/topology/continuous_function/bounded.lean


Modified src/topology/continuous_function/zero_at_infty.lean


Modified src/topology/instances/matrix.lean


Modified src/topology/locally_constant/algebra.lean
- \+/\- *lemma* locally_constant.coe_smul
- \+/\- *lemma* locally_constant.smul_apply

Modified src/topology/metric_space/algebra.lean


Modified test/has_scalar_comp_loop.lean
- \+/\- *def* foo

Modified test/instance_diamonds.lean


Modified test/to_additive.lean




## [2022-06-30 17:18:22](https://github.com/leanprover-community/mathlib/commit/c10efa6)
refactor(algebra/hom/group): generalize basic API of `monoid_hom` to `monoid_hom_class` ([#14997](https://github.com/leanprover-community/mathlib/pull/14997))
This PR generalizes part of the basic API of monoid homs to monoid_hom_class. This notably includes things like monoid_hom.mker, submonoid.map and submonoid.comap. I left the namespaces unchanged, for example `monoid_hom.mker` remains the same even though it is now defined for any `monoid_hom_class` morphism; this way dot notation still (mostly) works for actual monoid homs.
#### Estimated changes
Modified src/algebra/algebra/operations.lean


Modified src/algebra/hom/group.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/group_theory/submonoid/membership.lean
- \+/\- *lemma* submonoid.map_powers

Modified src/group_theory/submonoid/operations.lean
- \+/\- *lemma* monoid_hom.coe_mker
- \+/\- *lemma* monoid_hom.coe_mrange
- \+/\- *lemma* monoid_hom.comap_bot'
- \+/\- *lemma* monoid_hom.map_mclosure
- \+/\- *lemma* monoid_hom.mclosure_preimage_le
- \+/\- *lemma* monoid_hom.mem_mker
- \+/\- *lemma* monoid_hom.mem_mrange
- \+/\- *def* monoid_hom.mker
- \+/\- *def* monoid_hom.mrange
- \+/\- *lemma* monoid_hom.mrange_eq_map
- \+/\- *lemma* monoid_hom.mrange_top_iff_surjective
- \+/\- *lemma* monoid_hom.mrange_top_of_surjective
- \+/\- *lemma* submonoid.apply_coe_mem_map
- \+/\- *lemma* submonoid.coe_comap
- \+/\- *lemma* submonoid.coe_map
- \+/\- *def* submonoid.comap
- \+/\- *lemma* submonoid.comap_id
- \+/\- *lemma* submonoid.comap_inf
- \+/\- *lemma* submonoid.comap_infi
- \+/\- *lemma* submonoid.comap_map_comap
- \+/\- *lemma* submonoid.comap_top
- \+/\- *lemma* submonoid.gc_map_comap
- \+/\- *lemma* submonoid.le_comap_map
- \+/\- *lemma* submonoid.le_comap_of_map_le
- \+/\- *def* submonoid.map
- \+/\- *lemma* submonoid.map_bot
- \+/\- *lemma* submonoid.map_comap_le
- \+/\- *lemma* submonoid.map_comap_map
- \+/\- *lemma* submonoid.map_le_iff_le_comap
- \+/\- *lemma* submonoid.map_le_of_le_comap
- \+/\- *lemma* submonoid.map_sup
- \+/\- *lemma* submonoid.map_supr
- \+/\- *lemma* submonoid.mem_comap
- \+/\- *lemma* submonoid.mem_map
- \+/\- *lemma* submonoid.mem_map_iff_mem
- \+/\- *lemma* submonoid.mem_map_of_mem
- \+/\- *lemma* submonoid.monotone_comap
- \+/\- *lemma* submonoid.monotone_map

Modified src/group_theory/submonoid/pointwise.lean


Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.map_to_add_submonoid'

Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/local_properties.lean


Modified src/ring_theory/localization/integral.lean


Modified src/ring_theory/localization/localization_localization.lean


Modified src/ring_theory/non_zero_divisors.lean




## [2022-06-30 12:40:15](https://github.com/leanprover-community/mathlib/commit/eb85260)
feat(topology/compact_open):  continuous_comp left functor C(-, γ) ([#15068](https://github.com/leanprover-community/mathlib/pull/15068))
#### Estimated changes
Modified src/topology/compact_open.lean
- \+ *lemma* continuous_map.continuous_comp_left



## [2022-06-30 06:53:03](https://github.com/leanprover-community/mathlib/commit/050f9e6)
feat(number_theory/legendre_symbol/mul_character): alternative implementation ([#14768](https://github.com/leanprover-community/mathlib/pull/14768))
This is an alternative version of `number_theory/legendre_symbol/mul_character.lean`.
It defines `mul_character R R'` as a `monoid_hom` that sends non-units to zero.
This allows to define a `comm_group` structure on `mul_character R R'`.
There is an alternative implementation in [#14716](https://github.com/leanprover-community/mathlib/pull/14716) ([side by side comparison](https://github.com/leanprover-community/mathlib/compare/legendre_symbol_mul_char...variant)).
See the [discussion on Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Implementation.20of.20multiplicative.20characters).
#### Estimated changes
Added src/number_theory/legendre_symbol/mul_character.lean
- \+ *lemma* mul_char.coe_coe
- \+ *lemma* mul_char.coe_equiv_to_unit_hom
- \+ *lemma* mul_char.coe_mk
- \+ *lemma* mul_char.coe_to_fun_mul
- \+ *lemma* mul_char.coe_to_unit_hom
- \+ *def* mul_char.equiv_to_unit_hom
- \+ *lemma* mul_char.equiv_unit_hom_symm_coe
- \+ *lemma* mul_char.ext'
- \+ *lemma* mul_char.ext
- \+ *lemma* mul_char.ext_iff
- \+ *def* mul_char.inv
- \+ *lemma* mul_char.inv_apply'
- \+ *lemma* mul_char.inv_apply
- \+ *lemma* mul_char.inv_apply_eq_inv'
- \+ *lemma* mul_char.inv_apply_eq_inv
- \+ *lemma* mul_char.inv_mul
- \+ *lemma* mul_char.is_nontrivial.comp
- \+ *lemma* mul_char.is_nontrivial.sum_eq_zero
- \+ *def* mul_char.is_nontrivial
- \+ *lemma* mul_char.is_nontrivial_iff
- \+ *lemma* mul_char.is_quadratic.comp
- \+ *lemma* mul_char.is_quadratic.inv
- \+ *lemma* mul_char.is_quadratic.pow_char
- \+ *lemma* mul_char.is_quadratic.pow_even
- \+ *lemma* mul_char.is_quadratic.pow_odd
- \+ *lemma* mul_char.is_quadratic.sq_eq_one
- \+ *def* mul_char.is_quadratic
- \+ *lemma* mul_char.map_nonunit
- \+ *lemma* mul_char.map_one
- \+ *lemma* mul_char.map_zero
- \+ *def* mul_char.mul
- \+ *lemma* mul_char.mul_apply
- \+ *lemma* mul_char.mul_one
- \+ *def* mul_char.of_unit_hom
- \+ *lemma* mul_char.of_unit_hom_coe
- \+ *lemma* mul_char.of_unit_hom_eq
- \+ *lemma* mul_char.one_apply_coe
- \+ *lemma* mul_char.one_mul
- \+ *lemma* mul_char.pow_apply'
- \+ *lemma* mul_char.pow_apply_coe
- \+ *def* mul_char.ring_hom_comp
- \+ *lemma* mul_char.sum_one_eq_card_units
- \+ *lemma* mul_char.to_fun_eq_coe
- \+ *def* mul_char.to_unit_hom
- \+ *lemma* mul_char.to_unit_hom_eq
- \+ *def* mul_char.trivial
- \+ *structure* mul_char



## [2022-06-30 04:08:55](https://github.com/leanprover-community/mathlib/commit/ad154bd)
chore(scripts): update nolints.txt ([#15063](https://github.com/leanprover-community/mathlib/pull/15063))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-06-29 23:58:49](https://github.com/leanprover-community/mathlib/commit/5d8810a)
feat(set_theory/cardinal/*): simp lemmas for `to_nat` and `to_enat` ([#15059](https://github.com/leanprover-community/mathlib/pull/15059))
#### Estimated changes
Modified src/set_theory/cardinal/basic.lean
- \+ *theorem* cardinal.aleph_0_to_enat
- \+ *theorem* cardinal.aleph_0_to_nat

Modified src/set_theory/cardinal/continuum.lean
- \+ *theorem* cardinal.continuum_to_enat
- \+ *theorem* cardinal.continuum_to_nat

Modified src/set_theory/cardinal/ordinal.lean
- \+ *theorem* cardinal.aleph_to_enat
- \+ *theorem* cardinal.aleph_to_nat



## [2022-06-29 23:58:48](https://github.com/leanprover-community/mathlib/commit/68452ec)
feat(set_theory/game/pgame): golf `le_trans`  ([#14956](https://github.com/leanprover-community/mathlib/pull/14956))
This also adds `has_le.le.move_left_lf` and `has_le.le.lf_move_right` to enable dot notation. Note that we already have other pgame lemmas in the `has_le.le` namespace like `has_le.le.not_gf`.
To make this dot notation work even when these lemmas are partially-applied, we swap the arguments of `move_left_lf_of_le` and `lf_move_right_of_le`.
#### Estimated changes
Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/pgame.lean
- \+/\- *theorem* pgame.lf_move_right
- \+/\- *theorem* pgame.lf_move_right_of_le
- \+/\- *theorem* pgame.lf_of_le_mk
- \+/\- *theorem* pgame.lf_of_mk_le
- \+/\- *theorem* pgame.move_left_lf
- \+/\- *theorem* pgame.move_left_lf_of_le

Modified src/set_theory/surreal/basic.lean




## [2022-06-29 22:22:06](https://github.com/leanprover-community/mathlib/commit/501c1d4)
feat(linear_algebra/linear_pmap): add has_smul and ext ([#14915](https://github.com/leanprover-community/mathlib/pull/14915))
Adds the type-class `has_smul` for partially defined linear maps. We proof the ext lemma.
#### Estimated changes
Modified src/linear_algebra/linear_pmap.lean
- \+ *lemma* linear_pmap.coe_smul
- \+ *lemma* linear_pmap.ext
- \+ *lemma* linear_pmap.smul_apply



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
Modified src/algebra/direct_sum/internal.lean
- \+/\- *lemma* direct_sum.coe_ring_hom_of

Modified src/linear_algebra/clifford_algebra/grading.lean


Modified src/ring_theory/graded_algebra/basic.lean
- \+/\- *lemma* direct_sum.decompose_one
- \+ *def* direct_sum.decompose_ring_equiv
- \- *def* graded_algebra.proj_zero_ring_hom
- \+ *def* graded_algebra
- \+ *lemma* graded_ring.mem_support_iff
- \+ *def* graded_ring.proj
- \+ *lemma* graded_ring.proj_apply
- \+ *lemma* graded_ring.proj_recompose
- \+ *def* graded_ring.proj_zero_ring_hom

Modified src/ring_theory/graded_algebra/homogeneous_ideal.lean
- \+/\- *def* ideal.homogeneous_core'

Modified src/ring_theory/graded_algebra/radical.lean




## [2022-06-29 20:39:00](https://github.com/leanprover-community/mathlib/commit/1116684)
chore(set_theory/game/pgame): golf various theorems about relabellings ([#15054](https://github.com/leanprover-community/mathlib/pull/15054))
#### Estimated changes
Modified src/set_theory/game/basic.lean


Modified src/set_theory/game/pgame.lean
- \+/\- *theorem* pgame.relabelling.equiv
- \+/\- *theorem* pgame.relabelling.ge
- \+/\- *def* pgame.relabelling.is_empty
- \+/\- *theorem* pgame.relabelling.le
- \+/\- *def* pgame.relabelling.refl
- \+/\- *def* pgame.relabelling.restricted
- \+/\- *def* pgame.relabelling.symm
- \+/\- *def* pgame.relabelling.trans
- \+/\- *def* pgame.restricted.trans



## [2022-06-29 20:38:59](https://github.com/leanprover-community/mathlib/commit/108e3a0)
refactor(group_theory/coset): redefine quotient group to be quotient by action of subgroup ([#15045](https://github.com/leanprover-community/mathlib/pull/15045))
Given a group `α` and subgroup `s`, redefine the relation `left_rel` ("being in the same left coset") to
```lean
def left_rel : setoid α := mul_action.orbit_rel s.opposite α
```
This means that a quotient group is definitionally a quotient by a group action.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/two.20different.20quotients.20by.20subgroup)
#### Estimated changes
Modified src/algebra/category/Group/colimits.lean


Modified src/algebra/module/torsion.lean


Modified src/algebra/periodic.lean


Modified src/analysis/special_functions/trigonometric/angle.lean


Modified src/data/zmod/quotient.lean


Modified src/group_theory/abelianization.lean


Modified src/group_theory/complement.lean


Modified src/group_theory/coset.lean
- \+/\- *def* quotient_group.left_rel
- \+ *lemma* quotient_group.left_rel_apply
- \+ *lemma* quotient_group.left_rel_eq
- \+/\- *def* quotient_group.right_rel
- \+ *lemma* quotient_group.right_rel_apply
- \+ *lemma* quotient_group.right_rel_eq

Modified src/group_theory/double_coset.lean


Modified src/group_theory/group_action/quotient.lean


Modified src/group_theory/index.lean


Modified src/group_theory/quotient_group.lean
- \+ *lemma* quotient_group.mk'_eq_mk'

Modified src/group_theory/sylow.lean


Modified src/group_theory/transfer.lean


Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/quotient.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/class_group.lean
- \- *lemma* quotient_group.mk'_eq_mk'

Modified src/ring_theory/ideal/quotient.lean


Modified src/ring_theory/valuation/basic.lean




## [2022-06-29 20:38:58](https://github.com/leanprover-community/mathlib/commit/71985dc)
feat(field_theory/minpoly): generalize statements about GCD domains ([#14979](https://github.com/leanprover-community/mathlib/pull/14979))
Currently, the statements about the minimal polynomial over a GCD domain `R` require the element to be in a `K`-algebra, where `K` is the fraction field of `R`. We remove this assumption.
From flt-regular.
#### Estimated changes
Modified src/field_theory/minpoly.lean
- \+ *lemma* minpoly.gcd_domain_degree_le_of_ne_zero
- \+/\- *lemma* minpoly.gcd_domain_dvd
- \+ *lemma* minpoly.gcd_domain_eq_field_fractions'
- \+/\- *lemma* minpoly.gcd_domain_eq_field_fractions
- \+ *lemma* minpoly.gcd_domain_unique

Modified src/number_theory/cyclotomic/discriminant.lean


Modified src/number_theory/cyclotomic/rat.lean


Modified src/ring_theory/polynomial/content.lean
- \+ *lemma* polynomial.aeval_prim_part_eq_zero
- \+ *lemma* polynomial.eval₂_prim_part_eq_zero

Modified src/ring_theory/polynomial/cyclotomic/basic.lean


Modified src/ring_theory/polynomial/eisenstein.lean


Modified src/ring_theory/roots_of_unity.lean




## [2022-06-29 20:38:57](https://github.com/leanprover-community/mathlib/commit/6879dd0)
feat(model_theory/satisfiability): The Łoś–Vaught Test ([#14758](https://github.com/leanprover-community/mathlib/pull/14758))
Provides more API for elementary equivalence
Shows that a `κ`-categorical theory with only infinite models is complete.
#### Estimated changes
Modified docs/overview.yaml


Modified src/model_theory/bundled.lean
- \+ *def* equiv.bundled_induced
- \+ *def* equiv.bundled_induced_equiv
- \+ *def* first_order.language.elementarily_equivalent.to_Model

Modified src/model_theory/satisfiability.lean
- \+ *lemma* cardinal.categorical.is_complete
- \+ *theorem* cardinal.empty_infinite_Theory_is_complete
- \- *theorem* first_order.language.Theory.exists_elementary_embedding_card_eq
- \+ *theorem* first_order.language.Theory.exists_model_card_eq
- \+ *lemma* first_order.language.exists_elementarily_equivalent_card_eq
- \+ *theorem* first_order.language.exists_elementary_embedding_card_eq
- \+ *theorem* first_order.language.exists_elementary_embedding_card_eq_of_ge
- \+ *lemma* first_order.language.exists_elementary_embedding_card_eq_of_le

Modified src/model_theory/semantics.lean
- \+ *lemma* first_order.language.elementarily_equivalent.Theory_model
- \+ *lemma* first_order.language.elementarily_equivalent.Theory_model_iff
- \+ *lemma* first_order.language.elementarily_equivalent.complete_theory_eq
- \+ *lemma* first_order.language.elementarily_equivalent.infinite
- \+ *lemma* first_order.language.elementarily_equivalent.infinite_iff
- \+ *lemma* first_order.language.elementarily_equivalent.nonempty
- \+ *lemma* first_order.language.elementarily_equivalent.nonempty_iff
- \+ *lemma* first_order.language.elementarily_equivalent.realize_sentence
- \+ *lemma* first_order.language.elementarily_equivalent.symm
- \+ *lemma* first_order.language.elementarily_equivalent.trans
- \+ *lemma* first_order.language.equiv.elementarily_equivalent

Modified src/set_theory/cardinal/basic.lean
- \+ *lemma* cardinal.lift_mk_shrink''
- \+ *lemma* cardinal.lift_mk_shrink'
- \+ *lemma* cardinal.lift_mk_shrink



## [2022-06-29 18:27:22](https://github.com/leanprover-community/mathlib/commit/397d45f)
feat(algebra/order/monoid): `a + b ≤ c → a ≤ c` ([#15033](https://github.com/leanprover-community/mathlib/pull/15033))
Generalize four lemmas that were left by previous PRs before `canonically_ordered_monoid` was a thing.
#### Estimated changes
Modified src/algebra/order/monoid.lean
- \+ *lemma* le_of_mul_le_left
- \+ *lemma* le_of_mul_le_right

Modified src/data/matrix/rank.lean


Modified src/data/nat/basic.lean
- \- *lemma* nat.le_of_add_le_left
- \- *lemma* nat.le_of_add_le_right

Modified src/data/polynomial/coeff.lean


Modified src/data/polynomial/hasse_deriv.lean


Modified src/data/real/nnreal.lean
- \- *lemma* nnreal.le_of_add_le_left
- \- *lemma* nnreal.le_of_add_le_right

Modified src/ring_theory/power_series/basic.lean




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
Modified src/analysis/locally_convex/balanced_core_hull.lean
- \+/\- *lemma* balanced.hull_subset_of_subset
- \+/\- *lemma* balanced.subset_core_of_subset
- \+/\- *lemma* balanced_core_aux_balanced
- \+/\- *lemma* balanced_core_aux_maximal
- \- *lemma* balanced_core_aux_mem_iff
- \+ *lemma* balanced_core_empty
- \- *lemma* balanced_core_emptyset
- \+/\- *lemma* balanced_core_eq_Inter
- \- *lemma* balanced_core_is_closed
- \- *lemma* balanced_core_mem_iff
- \+/\- *lemma* balanced_core_mem_nhds_zero
- \+/\- *lemma* balanced_core_nonempty_iff
- \+/\- *lemma* balanced_core_subset
- \+/\- *lemma* balanced_core_subset_balanced_core_aux
- \+/\- *lemma* balanced_core_zero_mem
- \- *lemma* balanced_hull_mem_iff
- \+ *lemma* mem_balanced_core_aux_iff
- \+ *lemma* mem_balanced_core_iff
- \+ *lemma* mem_balanced_hull_iff
- \+/\- *lemma* subset_balanced_core

Modified src/analysis/locally_convex/basic.lean
- \+ *lemma* balanced_iff_smul_mem
- \- *lemma* balanced_mem
- \+ *lemma* balanced_zero
- \- *lemma* zero_singleton_balanced

Modified src/topology/algebra/module/finite_dimension.lean




## [2022-06-29 18:27:19](https://github.com/leanprover-community/mathlib/commit/478773b)
chore(data/nat/factorization/basic): golf rec_on_pos_prime_pos_coprime, remove import ([#14935](https://github.com/leanprover-community/mathlib/pull/14935))
Golf the proof of `rec_on_pos_prime_pos_coprime`, eliminating the need for `tactic.interval_cases`
#### Estimated changes
Modified src/data/nat/factorization/basic.lean




## [2022-06-29 17:31:54](https://github.com/leanprover-community/mathlib/commit/ee8d588)
refactor(logic/hydra): use `is_irrefl` ([#15039](https://github.com/leanprover-community/mathlib/pull/15039))
`is_irrefl` seems to be the more commonly used spelling
#### Estimated changes
Modified src/logic/hydra.lean
- \+/\- *lemma* acc.cut_expand
- \+/\- *lemma* relation.acc_of_singleton
- \+/\- *lemma* relation.cut_expand_iff
- \+/\- *theorem* relation.not_cut_expand_zero



## [2022-06-29 14:27:11](https://github.com/leanprover-community/mathlib/commit/c8ab806)
feat(tactic/alias.lean): use current namespace in alias ([#14961](https://github.com/leanprover-community/mathlib/pull/14961))
This makes `alias foo <- bar` use the current namespace to resolve the new alias name `bar`, for consistency with `def bar := foo` and leanprover-community/mathlib4[#293](https://github.com/leanprover-community/mathlib/pull/293).
#### Estimated changes
Modified scripts/nolints.txt


Modified src/algebra/group_power/lemmas.lean


Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/asymptotics/theta.lean


Modified src/analysis/calculus/implicit.lean


Modified src/analysis/calculus/inverse.lean


Modified src/analysis/normed/group/hom.lean


Modified src/analysis/special_functions/complex/log.lean


Modified src/category_theory/category/Bipointed.lean


Modified src/category_theory/category/Pointed.lean


Modified src/category_theory/category/Twop.lean


Modified src/category_theory/category/preorder.lean


Modified src/category_theory/functor/fully_faithful.lean


Modified src/combinatorics/simple_graph/clique.lean


Modified src/combinatorics/simple_graph/regularity/bound.lean


Modified src/data/finset/basic.lean


Modified src/data/finset/card.lean


Modified src/data/finset/locally_finite.lean


Modified src/data/finset/pointwise.lean


Modified src/data/finset/slice.lean


Modified src/data/finset/sym.lean


Modified src/data/fintype/basic.lean


Modified src/data/int/parity.lean


Modified src/data/list/basic.lean


Modified src/data/list/infix.lean


Modified src/data/list/nodup.lean


Modified src/data/list/pairwise.lean


Modified src/data/list/perm.lean


Modified src/data/multiset/basic.lean


Modified src/data/multiset/dedup.lean


Modified src/data/multiset/locally_finite.lean


Modified src/data/multiset/nodup.lean


Modified src/data/nat/cast.lean


Modified src/data/nat/factorial/basic.lean


Modified src/data/nat/pow.lean


Modified src/data/polynomial/degree/definitions.lean


Modified src/data/real/ennreal.lean


Modified src/data/set/basic.lean


Modified src/data/set/function.lean


Modified src/data/set/lattice.lean


Modified src/data/set/pairwise.lean


Modified src/data/set/pointwise.lean


Modified src/dynamics/flow.lean


Modified src/geometry/manifold/partition_of_unity.lean


Modified src/linear_algebra/matrix/to_linear_equiv.lean


Modified src/linear_algebra/span.lean


Modified src/logic/equiv/local_equiv.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/integral/integrable_on.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/measure_space_def.lean


Modified src/meta/expr.lean


Modified src/order/compactly_generated.lean


Modified src/order/compare.lean


Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean


Modified src/order/filter/germ.lean


Modified src/order/filter/small_sets.lean


Modified src/order/filter/ultrafilter.lean


Modified src/order/succ_pred/basic.lean


Modified src/order/sup_indep.lean


Modified src/order/synonym.lean


Modified src/probability/ident_distrib.lean


Modified src/ring_theory/multiplicity.lean


Modified src/set_theory/cardinal/basic.lean


Modified src/set_theory/game/pgame.lean


Modified src/set_theory/surreal/basic.lean


Modified src/tactic/alias.lean


Modified src/tactic/core.lean


Modified src/topology/bornology/basic.lean


Modified src/topology/local_homeomorph.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/metric_separated.lean




## [2022-06-29 14:27:10](https://github.com/leanprover-community/mathlib/commit/5de765c)
feat(linear_algebra/linear_pmap): definition of the graph ([#14920](https://github.com/leanprover-community/mathlib/pull/14920))
Define the graph of a partial linear map as the pushforward of the graph of the underlying linear map
and prove some elementary facts.
#### Estimated changes
Modified src/linear_algebra/linear_pmap.lean
- \+ *def* linear_pmap.graph
- \+ *lemma* linear_pmap.graph_fst_eq_zero_snd
- \+ *lemma* linear_pmap.mem_graph
- \+ *lemma* linear_pmap.mem_graph_iff'
- \+ *lemma* linear_pmap.mem_graph_iff
- \+ *lemma* linear_pmap.mem_graph_snd_inj'
- \+ *lemma* linear_pmap.mem_graph_snd_inj



## [2022-06-29 12:27:59](https://github.com/leanprover-community/mathlib/commit/aa812bd)
chore(group_theory/group_action/basic): split file ([#15044](https://github.com/leanprover-community/mathlib/pull/15044))
Split the file `group_theory/group_action/basic` to remove the dependency on `group_theory/quotient_group`, moving everything involving quotients to a new file `group_theory/group_action/quotient`.
#### Estimated changes
Modified src/algebra/polynomial/group_ring_action.lean


Modified src/category_theory/action.lean


Modified src/data/zmod/quotient.lean


Modified src/group_theory/commuting_probability.lean


Modified src/group_theory/complement.lean


Modified src/group_theory/group_action/basic.lean
- \- *lemma* mul_action.card_eq_sum_card_group_div_card_stabilizer'
- \- *lemma* mul_action.card_eq_sum_card_group_div_card_stabilizer
- \- *lemma* mul_action.card_orbit_mul_card_stabilizer_eq_card_group
- \- *theorem* mul_action.injective_of_quotient_stabilizer
- \- *def* mul_action.of_quotient_stabilizer
- \- *theorem* mul_action.of_quotient_stabilizer_mem_orbit
- \- *theorem* mul_action.of_quotient_stabilizer_mk
- \- *theorem* mul_action.of_quotient_stabilizer_smul
- \- *theorem* mul_action.orbit_equiv_quotient_stabilizer_symm_apply
- \- *lemma* mul_action.quotient.coe_smul_out'
- \- *lemma* mul_action.quotient.mk_smul_out'
- \- *lemma* mul_action.quotient.smul_coe
- \- *lemma* mul_action.quotient.smul_mk
- \- *lemma* mul_action.stabilizer_quotient
- \- *lemma* mul_action.sum_card_fixed_by_eq_card_orbits_mul_card_group
- \- *def* mul_action_hom.to_quotient
- \- *lemma* mul_action_hom.to_quotient_apply
- \- *lemma* subgroup.normal_core_eq_ker

Added src/group_theory/group_action/quotient.lean
- \+ *lemma* mul_action.card_eq_sum_card_group_div_card_stabilizer'
- \+ *lemma* mul_action.card_eq_sum_card_group_div_card_stabilizer
- \+ *lemma* mul_action.card_orbit_mul_card_stabilizer_eq_card_group
- \+ *theorem* mul_action.injective_of_quotient_stabilizer
- \+ *def* mul_action.of_quotient_stabilizer
- \+ *theorem* mul_action.of_quotient_stabilizer_mem_orbit
- \+ *theorem* mul_action.of_quotient_stabilizer_mk
- \+ *theorem* mul_action.of_quotient_stabilizer_smul
- \+ *theorem* mul_action.orbit_equiv_quotient_stabilizer_symm_apply
- \+ *lemma* mul_action.quotient.coe_smul_out'
- \+ *lemma* mul_action.quotient.mk_smul_out'
- \+ *lemma* mul_action.quotient.smul_coe
- \+ *lemma* mul_action.quotient.smul_mk
- \+ *lemma* mul_action.stabilizer_quotient
- \+ *lemma* mul_action.sum_card_fixed_by_eq_card_orbits_mul_card_group
- \+ *def* mul_action_hom.to_quotient
- \+ *lemma* mul_action_hom.to_quotient_apply
- \+ *lemma* subgroup.normal_core_eq_ker

Modified src/group_theory/p_group.lean


Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/quotient.lean


Modified src/topology/algebra/group.lean




## [2022-06-29 10:03:54](https://github.com/leanprover-community/mathlib/commit/ea9dae2)
refactor(topology/*): Use `disjoint` ([#14950](https://github.com/leanprover-community/mathlib/pull/14950))
Replace uses of `s ∩ t = ∅` by `disjoint s t` in the topology library. This shortens proofs.
#### Estimated changes
Modified src/data/set/basic.lean
- \- *theorem* set.subset_compl_iff_disjoint

Modified src/field_theory/krull_topology.lean


Modified src/group_theory/group_action/basic.lean
- \+ *lemma* mul_action.disjoint_image_image_iff

Modified src/measure_theory/constructions/polish.lean


Modified src/measure_theory/function/continuous_map_dense.lean


Modified src/measure_theory/measure/haar.lean


Modified src/topology/alexandroff.lean


Modified src/topology/algebra/const_mul_action.lean


Modified src/topology/algebra/continuous_monoid_hom.lean


Modified src/topology/algebra/order/basic.lean


Modified src/topology/basic.lean
- \+ *lemma* disjoint.frontier_left
- \+ *lemma* disjoint.frontier_right
- \- *lemma* is_open.inter_frontier_eq_empty_of_disjoint
- \+/\- *def* is_open
- \+/\- *lemma* is_open_univ

Modified src/topology/compact_open.lean
- \+ *lemma* continuous_map.gen_empty_right

Modified src/topology/connected.lean


Modified src/topology/local_homeomorph.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* emetric.ball_disjoint

Modified src/topology/order/priestley.lean


Modified src/topology/paracompact.lean


Modified src/topology/separation.lean
- \+/\- *lemma* t2_separation_compact_nhds
- \+/\- *lemma* t2_space_iff_nhds

Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/compact_separated.lean


Modified src/topology/uniform_space/separation.lean




## [2022-06-29 08:02:38](https://github.com/leanprover-community/mathlib/commit/03374ee)
feat(algebra/order/field): Linearly ordered semifields ([#15027](https://github.com/leanprover-community/mathlib/pull/15027))
Define `linear_ordered_semifield` and generalize lemmas within `algebra.order.field`.
#### Estimated changes
Modified src/algebra/field_power.lean
- \+/\- *lemma* div_pow_le
- \+/\- *lemma* min_le_of_zpow_le_max
- \+/\- *lemma* nat.zpow_ne_zero_of_pos
- \- *lemma* nat.zpow_pos_of_pos
- \+/\- *lemma* one_le_zpow_of_nonneg
- \+/\- *lemma* one_lt_zpow
- \+/\- *lemma* pos_div_pow_pos
- \+/\- *lemma* pow_le_max_of_min_le
- \+ *lemma* rat.cast_zpow
- \- *theorem* rat.cast_zpow
- \+/\- *lemma* ring_equiv.map_zpow
- \+/\- *lemma* ring_hom.map_zpow
- \+ *lemma* zpow_bit0_nonneg
- \- *theorem* zpow_bit0_nonneg
- \+ *lemma* zpow_bit0_pos
- \- *theorem* zpow_bit0_pos
- \+/\- *lemma* zpow_bit1_neg
- \+/\- *lemma* zpow_inj
- \+/\- *lemma* zpow_injective
- \+/\- *lemma* zpow_le_iff_le
- \+/\- *lemma* zpow_le_of_le
- \+/\- *lemma* zpow_le_one_of_nonpos
- \+/\- *lemma* zpow_lt_iff_lt
- \+/\- *lemma* zpow_nonneg
- \+/\- *lemma* zpow_pos_of_pos
- \+/\- *lemma* zpow_strict_anti
- \+/\- *lemma* zpow_strict_mono
- \+ *lemma* zpow_two_nonneg
- \- *theorem* zpow_two_nonneg
- \+ *lemma* zpow_two_pos_of_ne_zero
- \- *theorem* zpow_two_pos_of_ne_zero

Modified src/algebra/order/field.lean
- \+/\- *lemma* abs_one_div
- \+/\- *lemma* div_neg_iff
- \+/\- *lemma* div_pos_iff
- \+/\- *lemma* exists_add_lt_and_pos_of_lt
- \+/\- *def* function.injective.linear_ordered_field
- \+ *def* function.injective.linear_ordered_semifield
- \+/\- *lemma* max_div_div_right_of_nonpos
- \+/\- *lemma* min_div_div_right_of_nonpos
- \+/\- *theorem* nat.cast_le_pow_div_sub
- \+ *lemma* nat.cast_le_pow_sub_div_sub
- \- *theorem* nat.cast_le_pow_sub_div_sub
- \+/\- *lemma* sub_one_div_inv_le_two

Modified src/algebra/order/floor.lean


Modified src/data/int/log.lean


Modified src/data/nat/cast_field.lean


Modified src/number_theory/padics/padic_numbers.lean




## [2022-06-29 02:12:43](https://github.com/leanprover-community/mathlib/commit/55ec65a)
feat(topology/algebra/module/basic): define continuous_(semi)linear_map_class ([#14674](https://github.com/leanprover-community/mathlib/pull/14674))
This PR brings the morphism refactor to continuous (semi)linear maps. We define `continuous_semilinear_map_class` and `continuous_linear_map_class` in a way that parallels the non-continuous versions, along with a few extras (i.e. `add_monoid_hom_class` instance for `normed_group_hom`).
A few things I was not too sure about:
- When generalizing lemmas to a morphism class rather than a particular type of morphism, I used `𝓕` as the type (instead of just `F` as is done for most `fun_like` types) to avoid clashing with our convention of using `E`, `F`, etc for e.g. vector spaces.
- Namespacing: I placed lemmas like `isometry_of_norm`, `continuous_of_bound`, etc, under the `add_monoid_hom_class` namespace. Maybe the root namespace would make sense here.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/locally_convex/bounded.lean


Modified src/analysis/normed/group/SemiNormedGroup.lean


Modified src/analysis/normed/group/SemiNormedGroup/completion.lean


Modified src/analysis/normed/group/basic.lean
- \- *lemma* add_monoid_hom.continuous_of_bound
- \- *lemma* add_monoid_hom.isometry_iff_norm
- \- *lemma* add_monoid_hom.isometry_of_norm
- \- *lemma* add_monoid_hom.lipschitz_of_bound
- \- *lemma* add_monoid_hom.lipschitz_of_bound_nnnorm
- \+ *lemma* add_monoid_hom_class.antilipschitz_of_bound
- \+ *lemma* add_monoid_hom_class.bound_of_antilipschitz
- \+ *lemma* add_monoid_hom_class.continuous_of_bound
- \+ *lemma* add_monoid_hom_class.isometry_iff_norm
- \+ *lemma* add_monoid_hom_class.isometry_of_norm
- \+ *lemma* add_monoid_hom_class.lipschitz_of_bound
- \+ *lemma* add_monoid_hom_class.lipschitz_of_bound_nnnorm
- \+ *lemma* add_monoid_hom_class.uniform_continuous_of_bound

Modified src/analysis/normed/group/hom.lean
- \- *lemma* normed_group_hom.isometry_iff_norm
- \- *lemma* normed_group_hom.isometry_of_norm
- \- *lemma* normed_group_hom.map_add
- \- *lemma* normed_group_hom.map_neg
- \- *lemma* normed_group_hom.map_sub
- \- *lemma* normed_group_hom.map_sum
- \- *lemma* normed_group_hom.map_zero

Modified src/analysis/normed/group/hom_completion.lean


Modified src/analysis/normed/group/quotient.lean


Modified src/analysis/normed_space/banach_steinhaus.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/dual.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/linear_isometry.lean


Modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* continuous_linear_map.isometry_iff_norm
- \- *theorem* linear_map.antilipschitz_of_bound
- \- *lemma* linear_map.bound_of_antilipschitz
- \- *lemma* linear_map.bound_of_continuous
- \- *lemma* linear_map.bound_of_shell_semi_normed
- \- *lemma* linear_map.continuous_of_bound
- \- *lemma* linear_map.lipschitz_of_bound
- \- *lemma* linear_map.lipschitz_of_bound_nnnorm
- \- *lemma* linear_map.uniform_continuous_of_bound
- \+/\- *lemma* norm_image_of_norm_zero
- \+ *lemma* semilinear_map_class.bound_of_continuous
- \+ *lemma* semilinear_map_class.bound_of_shell_semi_normed

Modified src/analysis/normed_space/star/basic.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/integral/bochner.lean


Modified src/topology/algebra/module/basic.lean
- \- *lemma* continuous_linear_map.map_smul
- \- *lemma* continuous_linear_map.map_smulₛₗ
- \+ *abbreviation* continuous_linear_map_class

Modified src/topology/algebra/module/finite_dimension.lean


Modified src/topology/algebra/module/weak_dual.lean




## [2022-06-28 19:09:05](https://github.com/leanprover-community/mathlib/commit/08b07a6)
feat(order/succ_pred/basic): tag more lemmas with simp  ([#14998](https://github.com/leanprover-community/mathlib/pull/14998))
#### Estimated changes
Modified src/order/succ_pred/basic.lean
- \+/\- *lemma* order.Icc_pred_right
- \+/\- *lemma* order.Icc_succ_left
- \+/\- *lemma* order.Ico_succ_left
- \+/\- *lemma* order.Ico_succ_right
- \+/\- *lemma* order.Ioc_pred_left
- \+/\- *lemma* order.Ioc_pred_right
- \+/\- *lemma* order.Ioo_pred_left
- \+/\- *lemma* order.Ioo_succ_right
- \+/\- *lemma* order.le_pred_iff
- \+/\- *lemma* order.lt_succ_iff
- \+/\- *lemma* order.pred_le_pred_iff
- \+/\- *lemma* order.pred_lt_iff
- \+/\- *lemma* order.pred_lt_pred_iff
- \+/\- *lemma* order.succ_le_iff
- \+/\- *lemma* order.succ_le_succ_iff
- \+/\- *lemma* order.succ_lt_succ_iff



## [2022-06-28 19:09:03](https://github.com/leanprover-community/mathlib/commit/7db7667)
feat(order/boolean_algebra): Interaction of disjointness and complements ([#14925](https://github.com/leanprover-community/mathlib/pull/14925))
Prove `disjoint x yᶜ ↔ x ≤ y` and similar, transfer those results to `set`.
Lemma renames
* `subset_compl_iff_disjoint` → `subset_compl_iff_disjoint_right`
* `set.subset_compl_iff_disjoint` → `set.subset_compl_iff_disjoint_right`
* `disjoint_iff_le_compl_left` → `le_compl_iff_disjoint_left`
* `disjoint_iff_le_compl_right` → `le_compl_iff_disjoint_right`
#### Estimated changes
Modified src/algebra/support.lean


Modified src/analysis/convex/stone_separation.lean


Modified src/analysis/normed_space/riesz_lemma.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.compl_subset_comm
- \- *theorem* set.compl_subset_comm
- \+/\- *lemma* set.compl_subset_compl
- \+ *lemma* set.disjoint_compl_left_iff_subset
- \+ *lemma* set.disjoint_compl_right_iff_subset
- \+ *lemma* set.subset_compl_comm
- \- *theorem* set.subset_compl_comm
- \+ *lemma* set.subset_compl_iff_disjoint_left
- \+ *lemma* set.subset_compl_iff_disjoint_right

Modified src/data/set/lattice.lean
- \+ *lemma* set.disjoint_Union₂_left
- \+ *lemma* set.disjoint_Union₂_right
- \- *lemma* set.disjoint_iff_subset_compl_left
- \- *lemma* set.disjoint_iff_subset_compl_right
- \+ *lemma* set.disjoint_sUnion_left
- \+ *lemma* set.disjoint_sUnion_right

Modified src/group_theory/free_product.lean


Modified src/logic/equiv/embedding.lean


Modified src/order/boolean_algebra.lean
- \+ *lemma* disjoint_compl_left_iff
- \+ *lemma* disjoint_compl_right_iff
- \- *theorem* disjoint_iff_le_compl_left
- \- *theorem* disjoint_iff_le_compl_right
- \+ *lemma* le_compl_iff_disjoint_left
- \+ *lemma* le_compl_iff_disjoint_right

Modified src/order/complete_boolean_algebra.lean
- \+ *lemma* disjoint_supr₂_iff
- \+ *lemma* supr₂_disjoint_iff

Modified src/order/filter/bases.lean


Modified src/topology/basic.lean


Modified src/topology/metric_space/hausdorff_distance.lean




## [2022-06-28 15:21:02](https://github.com/leanprover-community/mathlib/commit/00c17d6)
feat(algebra/ring/boolean_ring): `bool` is a Boolean ring ([#15004](https://github.com/leanprover-community/mathlib/pull/15004))
and a few `bool` lemmas.
#### Estimated changes
Modified src/algebra/ring/boolean_ring.lean


Modified src/data/bool/basic.lean
- \+ *lemma* bool.band_bor_distrib_left
- \+ *lemma* bool.band_bor_distrib_right
- \+ *lemma* bool.band_bxor_distrib_left
- \+ *lemma* bool.band_bxor_distrib_right
- \+ *lemma* bool.bor_band_distrib_left
- \+ *lemma* bool.bor_band_distrib_right



## [2022-06-28 12:51:25](https://github.com/leanprover-community/mathlib/commit/78bc372)
feat(data/{finset, set}/basic): tweak `nonempty_coe_sort` and `is_empty_coe_sort` ([#14937](https://github.com/leanprover-community/mathlib/pull/14937))
This PR does the following:
- add lemmas `set.is_empty_coe_sort` and `finset.is_empty_coe_sort`
- made argument of both `nonempty_coe_sort` lemmas inferred
- fix some spacing
#### Estimated changes
Modified src/analysis/normed_space/is_R_or_C.lean


Modified src/data/finset/basic.lean
- \+/\- *lemma* finset.coe_nonempty
- \+ *lemma* finset.is_empty_coe_sort
- \+/\- *lemma* finset.nonempty.bex
- \+/\- *lemma* finset.nonempty_coe_sort

Modified src/data/set/basic.lean
- \+ *lemma* set.is_empty_coe_sort
- \+/\- *lemma* set.nonempty_coe_sort

Modified src/measure_theory/function/jacobian.lean


Modified src/topology/algebra/semigroup.lean




## [2022-06-28 09:03:25](https://github.com/leanprover-community/mathlib/commit/3594b63)
feat(probability_theory/independence): if a family of pi-systems is independent, then so are the generated measurable spaces ([#9387](https://github.com/leanprover-community/mathlib/pull/9387))
The main result in this PR is `Indep_sets.Indep`: if π-systems are independent as sets of sets, then the
measurable space structures they generate are independent. We already had a version of this for two pi-systems instead of a family.
In order to prove this, and as preparation for a next PR about Kolmogorov's 0-1 law, a definition `pi_Union_Inter` is introduced to build a particular pi-system from a family of pi-systems.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* sup_closed.inter
- \+ *def* sup_closed
- \+ *lemma* sup_closed_of_linear_order
- \+ *lemma* sup_closed_of_totally_ordered
- \+ *lemma* sup_closed_singleton

Modified src/measure_theory/measurable_space.lean
- \- *lemma* measurable_space.generate_from_mono
- \- *lemma* measurable_space.generate_from_sup_generate_from

Modified src/measure_theory/measurable_space_def.lean
- \+ *lemma* measurable_space.generate_from_insert_empty
- \+ *lemma* measurable_space.generate_from_insert_univ
- \+ *lemma* measurable_space.generate_from_mono
- \+ *lemma* measurable_space.generate_from_sup_generate_from

Modified src/measure_theory/pi_system.lean
- \+ *lemma* generate_from_pi_Union_Inter_le
- \+ *lemma* generate_from_pi_Union_Inter_measurable_space
- \+ *lemma* is_pi_system.insert_empty
- \+ *lemma* is_pi_system.insert_univ
- \+ *lemma* is_pi_system_pi_Union_Inter
- \+ *lemma* le_generate_from_pi_Union_Inter
- \+ *lemma* measurable_set_supr_of_mem_pi_Union_Inter
- \+/\- *lemma* mem_generate_pi_system_Union_elim'
- \+ *lemma* mem_pi_Union_Inter_of_measurable_set
- \+ *def* pi_Union_Inter
- \+ *lemma* pi_Union_Inter_mono_left
- \+ *lemma* subset_pi_Union_Inter

Modified src/probability/independence.lean
- \+ *theorem* probability_theory.Indep_sets.Indep
- \+ *theorem* probability_theory.Indep_sets.Indep_aux
- \+ *lemma* probability_theory.Indep_sets.pi_Union_Inter_singleton



## [2022-06-28 08:13:29](https://github.com/leanprover-community/mathlib/commit/728e074)
feat(measure_theory/function/lp_order): prove a `normed_lattice_add_comm_group` instance for Lp ([#14999](https://github.com/leanprover-community/mathlib/pull/14999))
#### Estimated changes
Modified src/measure_theory/function/ae_eq_fun.lean
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_abs

Modified src/measure_theory/function/lp_order.lean
- \+ *lemma* measure_theory.Lp.coe_fn_abs
- \+ *lemma* measure_theory.Lp.coe_fn_inf
- \+ *lemma* measure_theory.Lp.coe_fn_sup

Modified src/measure_theory/function/simple_func_dense_lp.lean




## [2022-06-28 03:59:01](https://github.com/leanprover-community/mathlib/commit/dcedc04)
feat(order/symm_diff): Triangle inequality for the symmetric difference ([#14847](https://github.com/leanprover-community/mathlib/pull/14847))
Prove that `a ∆ c ≤ a ∆ b ⊔ b ∆ c`.
#### Estimated changes
Modified src/order/boolean_algebra.lean
- \+ *lemma* sdiff_triangle

Modified src/order/symm_diff.lean
- \+ *lemma* le_symm_diff_iff_left
- \+ *lemma* le_symm_diff_iff_right
- \+ *lemma* symm_diff_triangle



## [2022-06-28 02:30:01](https://github.com/leanprover-community/mathlib/commit/ae3d572)
chore(topology/uniform_space/basic): Make `to_topological_space_inf` and `inf_uniformity` true by definition ([#14912](https://github.com/leanprover-community/mathlib/pull/14912))
Since the lattice API lets us provide a definition for `inf`, we may as well provide a nice one such that the obvious properties are true by rfl.
#### Estimated changes
Modified src/order/filter/lift.lean
- \+ *lemma* filter.lift'_inf_le

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* ball_inter



## [2022-06-28 00:05:04](https://github.com/leanprover-community/mathlib/commit/cf4d987)
chore(analysis/special_functions/trigonometric/angle): rfl lemmas for nat and int smul actions on angle ([#15003](https://github.com/leanprover-community/mathlib/pull/15003))
These can't be simp, because the simp-normal form is multiplication.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* real.angle.coe_nsmul
- \+ *lemma* real.angle.coe_zsmul



## [2022-06-28 00:05:02](https://github.com/leanprover-community/mathlib/commit/37bf8a2)
chore(topology/separation): Extract `set` product lemma ([#14958](https://github.com/leanprover-community/mathlib/pull/14958))
Move `prod_subset_compl_diagonal_iff_disjoint` to `data.set.prod`, where it belongs. Delete `diagonal_eq_range_diagonal_map` because it duplicates `set.diagonal_eq_range`. Move `set.disjoint_left`/`set.disjoint_right` to `data.set.basic` to avoid an import cycle.
Make variable semi-implicit in the RHS of `disjoint_left` and `disjoint_right`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* disjoint.inter_eq
- \+ *lemma* set.disjoint_left
- \+ *lemma* set.disjoint_right

Modified src/data/set/lattice.lean
- \- *lemma* disjoint.inter_eq
- \- *lemma* set.disjoint_left
- \- *theorem* set.disjoint_right

Modified src/data/set/prod.lean
- \+ *lemma* set.prod_subset_compl_diagonal_iff_disjoint

Modified src/linear_algebra/linear_independent.lean


Modified src/topology/basic.lean


Modified src/topology/separation.lean
- \- *lemma* diagonal_eq_range_diagonal_map
- \- *lemma* prod_subset_compl_diagonal_iff_disjoint

Modified src/topology/urysohns_lemma.lean




## [2022-06-28 00:05:01](https://github.com/leanprover-community/mathlib/commit/ee7f38c)
chore(data/set/basic): remove duplicate `nonempty_insert` in favor of `insert_nonempty` ([#14884](https://github.com/leanprover-community/mathlib/pull/14884))
This name matches e.g. `univ_nonempty` and `singleton_nonempty`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *theorem* set.insert_nonempty
- \- *lemma* set.nonempty_insert

Modified src/order/conditionally_complete_lattice.lean


Modified src/topology/algebra/order/compact.lean




## [2022-06-28 00:04:54](https://github.com/leanprover-community/mathlib/commit/365b2ee)
feat(data/bool): bnot_ne ([#10562](https://github.com/leanprover-community/mathlib/pull/10562))
#### Estimated changes
Modified src/data/bool/basic.lean
- \+ *lemma* bool.bnot_ne
- \+ *lemma* bool.bnot_not_eq
- \+ *lemma* bool.ne_bnot
- \+ *lemma* bool.not_eq_bnot



## [2022-06-27 21:32:09](https://github.com/leanprover-community/mathlib/commit/f6b728f)
feat(data/finset/pointwise): `•` and `⊆` ([#14968](https://github.com/leanprover-community/mathlib/pull/14968))
Port `set` lemmas to `finset`. Tag a few more lemmas with `norm_cast`. Add some missing `to_additive` attributes.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.image_subset_image_iff

Modified src/data/finset/pointwise.lean
- \+/\- *lemma* finset.coe_one
- \+ *lemma* finset.inv_smul_mem_iff
- \+ *lemma* finset.inv_smul_mem_iff₀
- \+ *lemma* finset.mem_inv_smul_finset_iff
- \+ *lemma* finset.mem_inv_smul_finset_iff₀
- \+/\- *lemma* finset.pairwise_disjoint_smul_iff
- \+ *lemma* finset.smul_finset_subset_iff
- \+ *lemma* finset.smul_finset_subset_iff₀
- \+ *lemma* finset.smul_finset_subset_smul_finset_iff
- \+ *lemma* finset.smul_finset_subset_smul_finset_iff₀
- \+ *lemma* finset.smul_finset_univ₀
- \+ *lemma* finset.smul_mem_smul_finset_iff
- \+ *lemma* finset.smul_mem_smul_finset_iff₀
- \+ *lemma* finset.smul_univ₀
- \+ *lemma* finset.subset_smul_finset_iff
- \+ *lemma* finset.subset_smul_finset_iff₀

Modified src/data/fintype/basic.lean
- \+/\- *lemma* finset.coe_univ

Modified src/data/set/pointwise.lean
- \+/\- *lemma* set.pairwise_disjoint_smul_iff



## [2022-06-27 21:32:08](https://github.com/leanprover-community/mathlib/commit/7c6cd38)
chore(set_theory/game/pgame): remove weird `simp` lemma ([#14954](https://github.com/leanprover-community/mathlib/pull/14954))
I added this back before there was much API on casting natural numbers to pre-games, as a safeguard in case I used the wrong `1`. In retrospective this theorem was kind of dumb.
#### Estimated changes
Modified src/set_theory/game/pgame.lean




## [2022-06-27 21:32:07](https://github.com/leanprover-community/mathlib/commit/2cdded9)
feat(data/multiset/basic): add multiset.filter_singleton ([#14938](https://github.com/leanprover-community/mathlib/pull/14938))
Adds a lemma, similar to `finset.filter_singleton`.
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.filter_singleton



## [2022-06-27 21:32:05](https://github.com/leanprover-community/mathlib/commit/927b468)
chore(data/nat/factorization/basic): golf pow_succ_factorization_not_dvd, remove import ([#14936](https://github.com/leanprover-community/mathlib/pull/14936))
Move `pow_succ_factorization_not_dvd` below `factorization_le_iff_dvd` and use this to golf it, eliminating the need for `tactic.linarith`
#### Estimated changes
Modified src/data/nat/factorization/basic.lean




## [2022-06-27 21:32:04](https://github.com/leanprover-community/mathlib/commit/f51286d)
feat(analysis/locally_convex/bounded): continuous linear image of bounded set is bounded ([#14907](https://github.com/leanprover-community/mathlib/pull/14907))
This is needed to prove that the usual strong topology on continuous linear maps satisfies `has_continuous_smul`.
#### Estimated changes
Modified src/analysis/locally_convex/bounded.lean
- \+ *lemma* bornology.is_vonN_bounded.image



## [2022-06-27 21:32:03](https://github.com/leanprover-community/mathlib/commit/cf50ac1)
chore(algebra/group/units): mark some lemmas as simp ([#14871](https://github.com/leanprover-community/mathlib/pull/14871))
These seem like fairly natural candidates for simp lemmas.
#### Estimated changes
Modified src/algebra/group/units.lean




## [2022-06-27 21:32:02](https://github.com/leanprover-community/mathlib/commit/cad1a6c)
feat(set_theory/cardinal/basic): lemmas about `#(finset α)` ([#14850](https://github.com/leanprover-community/mathlib/pull/14850))
This PR does the following:
- prove `mk_finset_of_fintype : #(finset α) = 2 ^ℕ fintype.card α` for `fintype α`
- rename `mk_finset_eq_mk` to `mk_finset_of_infinite` to match the former
- rename `mk_finset` to `mk_coe_finset` to avoid confusion with these two lemmas
#### Estimated changes
Modified src/field_theory/fixed.lean


Modified src/linear_algebra/dimension.lean


Modified src/set_theory/cardinal/basic.lean
- \+ *lemma* cardinal.mk_coe_finset
- \- *lemma* cardinal.mk_finset
- \+ *lemma* cardinal.mk_finset_of_fintype

Modified src/set_theory/cardinal/ordinal.lean
- \- *theorem* cardinal.mk_finset_eq_mk
- \+ *theorem* cardinal.mk_finset_of_infinite



## [2022-06-27 21:32:00](https://github.com/leanprover-community/mathlib/commit/fef4fb8)
refactor(topology/inseparable): redefine `specializes` and `inseparable` ([#14647](https://github.com/leanprover-community/mathlib/pull/14647))
* Redefine `specializes` and `inseparable` in terms of `nhds`.
* Review API.
* Define `inseparable_setoid` and `separation_quotient`.
* Add `function.surjective.subsingleton`.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum/basic.lean


Modified src/algebraic_geometry/properties.lean


Modified src/logic/unique.lean


Modified src/topology/inseparable.lean
- \+ *lemma* continuous.specialization_monotone
- \+ *lemma* inducing.inseparable_iff
- \+ *lemma* inducing.specializes_iff
- \+/\- *lemma* inseparable.map
- \+ *lemma* inseparable.map_of_continuous_at
- \+ *lemma* inseparable.mem_closed_iff
- \+ *lemma* inseparable.mem_open_iff
- \+ *lemma* inseparable.nhds_eq
- \+ *lemma* inseparable.refl
- \+ *lemma* inseparable.rfl
- \+ *lemma* inseparable.specializes'
- \+ *lemma* inseparable.specializes
- \+ *lemma* inseparable.symm
- \+ *lemma* inseparable.trans
- \+/\- *def* inseparable
- \+ *lemma* inseparable_def
- \- *lemma* inseparable_iff_closed
- \- *lemma* inseparable_iff_closure
- \+ *lemma* inseparable_iff_closure_eq
- \+ *lemma* inseparable_iff_forall_closed
- \+ *lemma* inseparable_iff_forall_open
- \+ *lemma* inseparable_iff_mem_closure
- \- *lemma* inseparable_iff_nhds_eq
- \+/\- *lemma* inseparable_iff_specializes_and
- \+ *lemma* inseparable_of_nhds_within_eq
- \+ *def* inseparable_setoid
- \+ *lemma* is_closed.not_inseparable
- \+ *lemma* is_closed.not_specializes
- \+ *lemma* is_open.not_inseparable
- \+ *lemma* is_open.not_specializes
- \+ *lemma* not_inseparable_iff_exists_open
- \+ *lemma* separation_quotient.continuous_mk
- \+ *lemma* separation_quotient.inducing_mk
- \+ *lemma* separation_quotient.is_closed_map_mk
- \+ *lemma* separation_quotient.is_open_map_mk
- \+ *lemma* separation_quotient.map_mk_nhds
- \+ *def* separation_quotient.mk
- \+ *lemma* separation_quotient.mk_eq_mk
- \+ *lemma* separation_quotient.preimage_image_mk_closed
- \+ *lemma* separation_quotient.preimage_image_mk_open
- \+ *lemma* separation_quotient.quotient_map_mk
- \+ *lemma* separation_quotient.range_mk
- \+ *lemma* separation_quotient.surjective_mk
- \+ *def* separation_quotient
- \- *lemma* specialization_order.monotone_of_continuous
- \+ *lemma* specializes.antisymm
- \+/\- *lemma* specializes.map
- \+ *lemma* specializes.map_of_continuous_at
- \+ *lemma* specializes.mem_closed
- \+ *lemma* specializes.mem_open
- \+/\- *lemma* specializes.trans
- \+/\- *def* specializes
- \- *lemma* specializes_def
- \+/\- *lemma* specializes_iff_closure_subset
- \+/\- *lemma* specializes_iff_forall_closed
- \+/\- *lemma* specializes_iff_forall_open
- \+ *lemma* specializes_iff_mem_closure
- \+ *lemma* specializes_iff_nhds
- \+ *lemma* specializes_iff_pure
- \+ *lemma* specializes_of_nhds_within
- \+/\- *lemma* specializes_refl
- \+/\- *lemma* specializes_rfl
- \+ *lemma* specializes_tfae
- \+/\- *lemma* subtype_inseparable_iff
- \+ *lemma* subtype_specializes_iff

Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/separation.lean
- \- *lemma* specializes_antisymm

Modified src/topology/sets/opens.lean


Modified src/topology/sober.lean




## [2022-06-27 19:03:59](https://github.com/leanprover-community/mathlib/commit/1cd2bf5)
feat(analysis/special_functions/log/deriv): more power series for log ([#14881](https://github.com/leanprover-community/mathlib/pull/14881))
This adds a power series expansion for `log ((a + 1) / a)`, and two lemmas that are needed for it. It's planned to be used in the proof of the Stirling formula.
#### Estimated changes
Modified src/analysis/special_functions/log/deriv.lean
- \+ *theorem* real.has_sum_log_one_add_inv
- \+ *lemma* real.has_sum_log_sub_log_of_abs_lt_1



## [2022-06-27 16:25:12](https://github.com/leanprover-community/mathlib/commit/68e0160)
chore(data/int/cast): redo [#14890](https://github.com/leanprover-community/mathlib/pull/14890), moving field-specific lemmas ([#14995](https://github.com/leanprover-community/mathlib/pull/14995))
In [#14894](https://github.com/leanprover-community/mathlib/pull/14894), I want to refer to the rational numbers in the definition of a field, meaning we can't have `algebra.field.basic` in the transitive imports of `data.rat.defs`.
Apparently this dependency was re-added, so I'm going to have to split it again...
#### Estimated changes
Modified src/data/int/cast.lean
- \- *lemma* int.cast_neg_nat_cast

Modified src/data/int/cast_field.lean
- \+ *lemma* int.cast_neg_nat_cast



## [2022-06-27 16:25:11](https://github.com/leanprover-community/mathlib/commit/2558b3b)
feat(*): Upgrade to lean 3.44.1c ([#14984](https://github.com/leanprover-community/mathlib/pull/14984))
The changes are:
* `reflected a` is now spelt `reflected _ a`, as the argument was made explicit to resolve type resolution issues. We need to add new instances for `with_top` and `with_bot` as these are no longer found via the `option` instance. These new instances are an improvement, as they can now use `bot` and `top` instead of `none`.
* Some nat order lemmas in core have been renamed or had their argument explicitness adjusted.
* `dsimp` now applies `iff` lemmas, which means it can end up making more progress than it used to. This appears to impact `split_ifs` too.
* `opposite.op_inj_iff` shouldn't be proved until after `opposite` is irreducible (where `iff.rfl` no longer works as a proof), otherwise `dsimp` is tricked into unfolding the irreducibility which puts the goal state in a form where no further lemmas can apply.
We skip Lean 3.44.0c because the support in that version for `iff` lemmas in `dsimp` had some unintended consequences which required many undesirable changes.
#### Estimated changes
Modified archive/100-theorems-list/45_partition.lean


Modified leanpkg.toml


Modified src/algebra/geom_sum.lean


Modified src/algebraic_geometry/gluing.lean


Modified src/algebraic_topology/simplex_category.lean


Modified src/combinatorics/simple_graph/regularity/bound.lean


Modified src/data/fin/tuple/basic.lean


Modified src/data/fin/vec_notation.lean


Modified src/data/int/basic.lean


Modified src/data/list/basic.lean


Modified src/data/list/sigma.lean


Modified src/data/matrix/pequiv.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/log.lean


Modified src/data/nat/pow.lean


Modified src/data/num/lemmas.lean


Modified src/data/opposite.lean
- \+/\- *lemma* opposite.op_inj_iff
- \+/\- *lemma* opposite.unop_inj_iff

Modified src/data/rat/defs.lean


Modified src/data/sigma/basic.lean


Modified src/data/vector/basic.lean


Modified src/dynamics/periodic_pts.lean


Modified src/linear_algebra/projective_space/basic.lean


Modified src/meta/univs.lean


Modified src/number_theory/dioph.lean


Modified src/number_theory/legendre_symbol/gauss_eisenstein_lemmas.lean


Modified src/number_theory/legendre_symbol/quadratic_reciprocity.lean


Modified src/number_theory/primorial.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/order/bounded_order.lean


Modified src/order/filter/at_top_bot.lean


Modified src/order/galois_connection.lean


Modified src/set_theory/ordinal/arithmetic.lean


Modified src/tactic/core.lean


Modified src/tactic/doc_commands.lean


Modified src/tactic/fix_reflect_string.lean


Modified src/tactic/linarith/datatypes.lean


Modified src/tactic/local_cache.lean


Modified src/tactic/omega/term.lean


Modified src/tactic/replacer.lean


Modified src/topology/discrete_quotient.lean


Modified src/topology/uniform_space/basic.lean




## [2022-06-27 13:50:22](https://github.com/leanprover-community/mathlib/commit/05565f4)
doc(analysis/convex/uniform_convex_space): End of sentence ([#14986](https://github.com/leanprover-community/mathlib/pull/14986))
I kept the suspense for a month.
#### Estimated changes
Modified src/analysis/convex/uniform.lean




## [2022-06-27 13:50:15](https://github.com/leanprover-community/mathlib/commit/5de7c34)
feat(order/*): Miscellaneous results about the product order ([#14977](https://github.com/leanprover-community/mathlib/pull/14977))
`≤`, `<`, `⩿`, `⋖`, `is_bot`, `is_top`, `is_min`, `is_max` in `α × β`.
#### Estimated changes
Modified src/order/basic.lean
- \+/\- *lemma* prod.lt_iff
- \+ *lemma* prod.mk_le_mk_iff_left
- \+ *lemma* prod.mk_le_mk_iff_right
- \+/\- *lemma* prod.mk_lt_mk
- \+ *lemma* prod.mk_lt_mk_iff_left
- \+ *lemma* prod.mk_lt_mk_iff_right
- \+/\- *lemma* prod.swap_lt_swap

Modified src/order/cover.lean
- \+ *lemma* prod.covby_iff
- \+ *lemma* prod.fst_eq_or_snd_eq_of_wcovby
- \+ *lemma* prod.mk_covby_mk_iff
- \+ *lemma* prod.mk_covby_mk_iff_left
- \+ *lemma* prod.mk_covby_mk_iff_right
- \+ *lemma* prod.mk_wcovby_mk_iff
- \+ *lemma* prod.mk_wcovby_mk_iff_left
- \+ *lemma* prod.mk_wcovby_mk_iff_right
- \+ *lemma* prod.swap_covby_swap
- \+ *lemma* prod.swap_wcovby_swap
- \+ *lemma* prod.wcovby_iff
- \+ *lemma* wcovby.fst
- \+ *lemma* wcovby.snd

Modified src/order/max.lean
- \+ *lemma* is_bot.fst
- \+ *lemma* is_bot.prod_mk
- \+ *lemma* is_bot.snd
- \+ *lemma* is_max.fst
- \+ *lemma* is_max.prod_mk
- \+ *lemma* is_max.snd
- \+ *lemma* is_min.fst
- \+ *lemma* is_min.prod_mk
- \+ *lemma* is_min.snd
- \+ *lemma* is_top.fst
- \+ *lemma* is_top.prod_mk
- \+ *lemma* is_top.snd
- \+ *lemma* prod.is_bot_iff
- \+ *lemma* prod.is_max_iff
- \+ *lemma* prod.is_min_iff
- \+ *lemma* prod.is_top_iff



## [2022-06-27 13:50:14](https://github.com/leanprover-community/mathlib/commit/f5d2cc8)
feat(measure_theory/function/l1_space): add some integrability lemmas ([#14931](https://github.com/leanprover-community/mathlib/pull/14931))
#### Estimated changes
Modified src/analysis/normed_space/lattice_ordered_group.lean
- \+ *lemma* norm_inf_le_add
- \+ *lemma* norm_sup_le_add

Modified src/measure_theory/function/l1_space.lean
- \+/\- *lemma* measure_theory.integrable.abs
- \+ *lemma* measure_theory.integrable.bdd_mul
- \+ *lemma* measure_theory.integrable.inf
- \+ *lemma* measure_theory.integrable.sup

Modified src/measure_theory/function/lp_order.lean
- \+ *lemma* measure_theory.mem_ℒp.abs
- \+ *lemma* measure_theory.mem_ℒp.inf
- \+ *lemma* measure_theory.mem_ℒp.sup



## [2022-06-27 13:50:13](https://github.com/leanprover-community/mathlib/commit/cf8b46d)
feat(analysis/convex/special_functions): `sqrt * log` is strictly convex on x>1 ([#14822](https://github.com/leanprover-community/mathlib/pull/14822))
This convexity result can be used to golf the proof of the main inequality in the proof of Bertrand's postulate ([#8002](https://github.com/leanprover-community/mathlib/pull/8002)).
#### Estimated changes
Modified src/analysis/convex/specific_functions.lean
- \+ *lemma* deriv2_sqrt_mul_log
- \+ *lemma* deriv_sqrt_mul_log
- \+ *lemma* strict_concave_on_sqrt_mul_log_Ioi



## [2022-06-27 13:50:12](https://github.com/leanprover-community/mathlib/commit/68d29f5)
feat(probability/stopping): measurability of sets related to stopping times, under countable/encodable assumptions ([#14750](https://github.com/leanprover-community/mathlib/pull/14750))
The file already contains similar lemmas under assumptions on the topology of the index set. The new results use countability hypotheses instead.
#### Estimated changes
Modified src/probability/stopping.lean




## [2022-06-27 11:38:35](https://github.com/leanprover-community/mathlib/commit/331df5a)
feat(probability/moments): moments and moment generating function of a real random variable ([#14755](https://github.com/leanprover-community/mathlib/pull/14755))
This PR defines moments, central moments, moment generating function and cumulant generating function.
#### Estimated changes
Added src/probability/moments.lean
- \+ *def* probability_theory.central_moment
- \+ *lemma* probability_theory.central_moment_one'
- \+ *lemma* probability_theory.central_moment_one
- \+ *lemma* probability_theory.central_moment_two_eq_variance
- \+ *lemma* probability_theory.central_moment_zero
- \+ *def* probability_theory.cgf
- \+ *lemma* probability_theory.cgf_const'
- \+ *lemma* probability_theory.cgf_const
- \+ *lemma* probability_theory.cgf_undef
- \+ *lemma* probability_theory.cgf_zero'
- \+ *lemma* probability_theory.cgf_zero
- \+ *lemma* probability_theory.cgf_zero_fun
- \+ *lemma* probability_theory.cgf_zero_measure
- \+ *lemma* probability_theory.indep_fun.cgf_add
- \+ *lemma* probability_theory.indep_fun.mgf_add
- \+ *def* probability_theory.mgf
- \+ *lemma* probability_theory.mgf_const'
- \+ *lemma* probability_theory.mgf_const
- \+ *lemma* probability_theory.mgf_nonneg
- \+ *lemma* probability_theory.mgf_pos'
- \+ *lemma* probability_theory.mgf_pos
- \+ *lemma* probability_theory.mgf_undef
- \+ *lemma* probability_theory.mgf_zero'
- \+ *lemma* probability_theory.mgf_zero
- \+ *lemma* probability_theory.mgf_zero_fun
- \+ *lemma* probability_theory.mgf_zero_measure
- \+ *def* probability_theory.moment
- \+ *lemma* probability_theory.moment_zero



## [2022-06-27 11:38:34](https://github.com/leanprover-community/mathlib/commit/3091b91)
feat(probability/stopping): if a filtration is sigma finite, then the measure restricted to the sigma algebra generated by a stopping time is sigma finite ([#14752](https://github.com/leanprover-community/mathlib/pull/14752))
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.sigma_finite_trim_mono

Modified src/probability/stopping.lean




## [2022-06-27 11:38:33](https://github.com/leanprover-community/mathlib/commit/72fbe5c)
feat(measure_theory/measure/finite_measure_weak_convergence): Characterize weak convergence of finite measures in terms of integrals of bounded continuous real-valued functions. ([#14578](https://github.com/leanprover-community/mathlib/pull/14578))
Weak convergence of measures was defined in terms of integrals of bounded continuous nnreal-valued functions. This PR shows the equivalence to the textbook condition in terms of integrals of bounded continuous real-valued functions.
Also the file `measure_theory/measure/finite_measure_weak_convergence.lean` is divided to sections with dosctrings for clarity.
#### Estimated changes
Modified src/algebra/order/ring.lean
- \+ *lemma* max_zero_add_max_neg_zero_eq_abs_self

Modified src/measure_theory/measure/finite_measure_weak_convergence.lean
- \+ *lemma* bounded_continuous_function.integral_eq_integral_nnreal_part_sub
- \+ *lemma* bounded_continuous_function.nnreal.to_real_lintegral_eq_integral
- \+ *lemma* measure_theory.finite_measure.integrable_of_bounded_continuous_to_nnreal
- \+ *lemma* measure_theory.finite_measure.integrable_of_bounded_continuous_to_real
- \- *lemma* measure_theory.finite_measure.lintegral_lt_top_of_bounded_continuous_to_nnreal
- \+ *lemma* measure_theory.finite_measure.lintegral_lt_top_of_bounded_continuous_to_real
- \+ *theorem* measure_theory.finite_measure.tendsto_iff_forall_integral_tendsto
- \+ *theorem* measure_theory.finite_measure.tendsto_of_forall_integral_tendsto
- \+/\- *def* measure_theory.finite_measure
- \+ *lemma* measure_theory.lintegral_lt_top_of_bounded_continuous_to_nnreal
- \- *lemma* measure_theory.probability_measure.lintegral_lt_top_of_bounded_continuous_to_nnreal
- \+ *theorem* measure_theory.probability_measure.tendsto_iff_forall_integral_tendsto

Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.abs_self_eq_nnreal_part_add_nnreal_part_neg
- \+ *def* bounded_continuous_function.nnnorm
- \+ *lemma* bounded_continuous_function.nnnorm_coe_fun_eq
- \+ *def* bounded_continuous_function.nnreal_part
- \+ *lemma* bounded_continuous_function.nnreal_part_coe_fun_eq
- \+ *lemma* bounded_continuous_function.self_eq_nnreal_part_sub_nnreal_part_neg



## [2022-06-27 09:14:45](https://github.com/leanprover-community/mathlib/commit/cf0649c)
chore(data/sigma/basic): make `sigma.reflect` universe-polymorphic ([#14934](https://github.com/leanprover-community/mathlib/pull/14934))
#### Estimated changes
Modified src/data/sigma/basic.lean




## [2022-06-27 07:39:57](https://github.com/leanprover-community/mathlib/commit/671c7c0)
chore(algebra/direct_sum/ring): add new `int_cast` and `nat_cast` fields to match `ring` and `semiring` ([#14976](https://github.com/leanprover-community/mathlib/pull/14976))
This was deliberately left to a follow up in [#12182](https://github.com/leanprover-community/mathlib/pull/12182)
#### Estimated changes
Modified src/algebra/direct_sum/internal.lean
- \+ *lemma* set_like.has_graded_one.int_cast_mem
- \+ *lemma* set_like.has_graded_one.nat_cast_mem

Modified src/algebra/direct_sum/ring.lean




## [2022-06-27 07:39:56](https://github.com/leanprover-community/mathlib/commit/af8ca85)
fix(linear_algebra/{exterior,clifford}_algebra/basic): add some missing namespaces ([#14975](https://github.com/leanprover-community/mathlib/pull/14975))
These lemmas are about the auxiliary `{exterior,clifford}_algebra.graded_algebra.ι` not `{exterior,clifford}_algebra.ι`, so should have `graded_algebra` in their names.
This is a follow up to [#12182](https://github.com/leanprover-community/mathlib/pull/12182)
#### Estimated changes
Modified src/linear_algebra/clifford_algebra/grading.lean
- \+ *lemma* clifford_algebra.graded_algebra.lift_ι_eq
- \- *lemma* clifford_algebra.lift_ι_eq

Modified src/linear_algebra/exterior_algebra/grading.lean
- \+ *def* exterior_algebra.graded_algebra.lift_ι
- \+ *lemma* exterior_algebra.graded_algebra.lift_ι_eq
- \- *def* exterior_algebra.lift_ι
- \- *lemma* exterior_algebra.lift_ι_eq



## [2022-06-27 04:03:50](https://github.com/leanprover-community/mathlib/commit/d4f8a45)
feat(algebra/group/units): add decidability instance for `is_unit` ([#14873](https://github.com/leanprover-community/mathlib/pull/14873))
This adds a decidability instance for the `is_unit` predicate. See [here](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Decidability.20of.20.60is_unit.60.20on.20finite.20rings/near/286543269).
#### Estimated changes
Modified src/algebra/group/units.lean




## [2022-06-27 03:03:23](https://github.com/leanprover-community/mathlib/commit/0b18823)
feat(set_theory/game/pgame): make `lt_iff_le_and_lf` true by def-eq ([#14983](https://github.com/leanprover-community/mathlib/pull/14983))
#### Estimated changes
Modified src/set_theory/game/basic.lean


Modified src/set_theory/game/ordinal.lean


Modified src/set_theory/game/pgame.lean
- \+/\- *theorem* pgame.lf_of_lt
- \+/\- *theorem* pgame.lt_iff_le_and_lf
- \+/\- *theorem* pgame.lt_of_le_of_lf

Modified src/set_theory/game/short.lean


Modified src/set_theory/surreal/basic.lean




## [2022-06-27 00:09:16](https://github.com/leanprover-community/mathlib/commit/894f92b)
refactor(order/upper_lower): Reverse the order on `upper_set` ([#14982](https://github.com/leanprover-community/mathlib/pull/14982))
Having `upper_set` being ordered by reverse inclusion makes it order-isomorphic to `lower_set` (and antichains once we have them as a type) and it matches the order on `filter`.
#### Estimated changes
Modified src/order/upper_lower.lean
- \+ *lemma* lower_set.compl_le_compl
- \+/\- *lemma* upper_set.Ici_Sup
- \+/\- *def* upper_set.Ici_Sup_hom
- \+ *lemma* upper_set.Ici_bot
- \+/\- *lemma* upper_set.Ici_sup
- \+/\- *def* upper_set.Ici_sup_hom
- \+/\- *lemma* upper_set.Ici_sup_hom_apply
- \+/\- *lemma* upper_set.Ici_supr
- \+/\- *lemma* upper_set.Ici_supr₂
- \- *lemma* upper_set.Ici_top
- \+ *lemma* upper_set.Icoi_le_Ioi
- \- *lemma* upper_set.Ioi_bot
- \- *lemma* upper_set.Ioi_le_Ici
- \+ *lemma* upper_set.Ioi_top
- \+/\- *lemma* upper_set.coe_Inf
- \+/\- *lemma* upper_set.coe_Sup
- \+/\- *lemma* upper_set.coe_bot
- \+/\- *lemma* upper_set.coe_inf
- \+/\- *lemma* upper_set.coe_infi
- \+/\- *lemma* upper_set.coe_infi₂
- \+/\- *lemma* upper_set.coe_sup
- \+/\- *lemma* upper_set.coe_supr
- \+/\- *lemma* upper_set.coe_supr₂
- \+/\- *lemma* upper_set.coe_top
- \+ *lemma* upper_set.compl_le_compl
- \+/\- *lemma* upper_set.mem_Inf_iff
- \+/\- *lemma* upper_set.mem_Sup_iff
- \+ *lemma* upper_set.mem_bot
- \+/\- *lemma* upper_set.mem_inf_iff
- \+/\- *lemma* upper_set.mem_infi_iff
- \+/\- *lemma* upper_set.mem_infi₂_iff
- \+/\- *lemma* upper_set.mem_sup_iff
- \+/\- *lemma* upper_set.mem_supr_iff
- \+/\- *lemma* upper_set.mem_supr₂_iff
- \- *lemma* upper_set.mem_top
- \- *lemma* upper_set.not_mem_bot
- \+ *lemma* upper_set.not_mem_top
- \+ *def* upper_set_iso_lower_set



## [2022-06-26 23:29:19](https://github.com/leanprover-community/mathlib/commit/f63d925)
feat(combinatorics/simple_graph/clique): The set of cliques ([#14827](https://github.com/leanprover-community/mathlib/pull/14827))
Define `simple_graph.clique_set`, the `set` analogue to `simple_graph.clique_finset`.
#### Estimated changes
Modified src/combinatorics/simple_graph/clique.lean
- \+/\- *lemma* simple_graph.clique_finset_mono
- \+ *def* simple_graph.clique_set
- \+ *lemma* simple_graph.clique_set_eq_empty_iff
- \+ *lemma* simple_graph.clique_set_mono'
- \+ *lemma* simple_graph.clique_set_mono
- \+ *lemma* simple_graph.coe_clique_finset
- \+/\- *lemma* simple_graph.mem_clique_finset_iff
- \+ *lemma* simple_graph.mem_clique_set_iff



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
Modified src/data/W/cardinal.lean


Modified src/linear_algebra/dimension.lean


Modified src/measure_theory/card_measurable_space.lean


Modified src/model_theory/encoding.lean


Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* csupr_mono'
- \+ *lemma* le_csupr_iff'

Modified src/set_theory/cardinal/basic.lean
- \+/\- *theorem* cardinal.bdd_above_iff_small
- \+ *theorem* cardinal.bdd_above_image
- \+ *theorem* cardinal.bdd_above_range_comp
- \+/\- *lemma* cardinal.le_powerlt
- \- *theorem* cardinal.le_sup
- \+ *lemma* cardinal.lift_Sup
- \+ *theorem* cardinal.lift_infi
- \- *lemma* cardinal.lift_sup
- \- *lemma* cardinal.lift_sup_le
- \- *lemma* cardinal.lift_sup_le_iff
- \- *lemma* cardinal.lift_sup_le_lift_sup'
- \- *lemma* cardinal.lift_sup_le_lift_sup
- \+ *lemma* cardinal.lift_supr
- \+ *lemma* cardinal.lift_supr_le
- \+ *lemma* cardinal.lift_supr_le_iff
- \+ *lemma* cardinal.lift_supr_le_lift_supr'
- \+ *lemma* cardinal.lift_supr_le_lift_supr
- \+/\- *lemma* cardinal.mk_Union_le
- \+/\- *lemma* cardinal.mk_sUnion_le
- \+/\- *def* cardinal.powerlt
- \- *theorem* cardinal.powerlt_aux
- \+/\- *lemma* cardinal.powerlt_le
- \+/\- *lemma* cardinal.powerlt_max
- \+ *lemma* cardinal.powerlt_min
- \+ *lemma* cardinal.powerlt_mono_left
- \+/\- *lemma* cardinal.powerlt_succ
- \+/\- *lemma* cardinal.powerlt_zero
- \- *theorem* cardinal.sum_le_sup
- \- *theorem* cardinal.sum_le_sup_lift
- \+ *theorem* cardinal.sum_le_supr
- \+ *theorem* cardinal.sum_le_supr_lift
- \- *def* cardinal.sup
- \- *theorem* cardinal.sup_eq_zero
- \- *theorem* cardinal.sup_le
- \- *theorem* cardinal.sup_le_iff
- \- *theorem* cardinal.sup_le_sum
- \- *theorem* cardinal.sup_le_sup
- \+ *theorem* cardinal.supr_le_sum

Modified src/set_theory/cardinal/cofinality.lean
- \- *theorem* cardinal.sup_lt_lift_of_is_regular
- \- *theorem* cardinal.sup_lt_of_is_regular
- \+ *theorem* cardinal.supr_lt_lift_of_is_regular
- \+ *theorem* cardinal.supr_lt_of_is_regular
- \- *theorem* ordinal.sup_lt
- \- *theorem* ordinal.sup_lt_lift
- \+ *theorem* ordinal.supr_lt
- \+ *theorem* ordinal.supr_lt_lift

Modified src/set_theory/cardinal/ordinal.lean


Modified src/set_theory/ordinal/arithmetic.lean
- \+ *theorem* ordinal.Sup_ord
- \- *theorem* ordinal.sup_ord
- \+ *theorem* ordinal.supr_ord



## [2022-06-26 19:48:44](https://github.com/leanprover-community/mathlib/commit/33112c4)
feat(data/nat/totient): more general multiplicativity lemmas for totient ([#14842](https://github.com/leanprover-community/mathlib/pull/14842))
Adds lemmas: 
`totient_gcd_mul_totient_mul : φ (a.gcd b) * φ (a * b) = φ a * φ b * (a.gcd b)`
`totient_super_multiplicative : φ a * φ b ≤ φ (a * b)`
`totient_gcd_mul_totient_mul` is Theorem 2.5(b) in Apostol (1976) Introduction to Analytic Number Theory.
Developed while reviewing @CBirkbeck 's [#14828](https://github.com/leanprover-community/mathlib/pull/14828)
#### Estimated changes
Modified src/data/nat/totient.lean
- \+ *lemma* nat.totient_gcd_mul_totient_mul
- \+ *lemma* nat.totient_super_multiplicative

Modified src/ring_theory/multiplicity.lean
- \+ *lemma* prod_factors_gcd_mul_prod_factors_mul



## [2022-06-26 18:50:48](https://github.com/leanprover-community/mathlib/commit/381733a)
feat(analysis/convex/stone_separation): Stone's separation theorem ([#14677](https://github.com/leanprover-community/mathlib/pull/14677))
Disjoint convexes can be separated by a convex whose complement is also convex.
#### Estimated changes
Added src/analysis/convex/stone_separation.lean
- \+ *lemma* exists_convex_convex_compl_subset
- \+ *lemma* not_disjoint_segment_convex_hull_triple



## [2022-06-26 17:01:08](https://github.com/leanprover-community/mathlib/commit/4111ed9)
docs(linear_algebra/invariant_basis_number): Drop a TODO ([#14973](https://github.com/leanprover-community/mathlib/pull/14973))
This TODO was fixed some time ago by @riccardobrasca, reference the relevant instance in the docstring.
#### Estimated changes
Modified src/linear_algebra/invariant_basis_number.lean




## [2022-06-26 17:01:07](https://github.com/leanprover-community/mathlib/commit/ca070dd)
feat(analysis/special_functions/trigonometric/angle): topology ([#14969](https://github.com/leanprover-community/mathlib/pull/14969))
Give `real.angle` the structure of a `topological_add_group` (rather
than just an `add_comm_group`), so that it's possible to talk about
continuity for functions involving this type, and add associated
continuity lemmas for `coe : ℝ → angle`, `real.angle.sin` and
`real.angle.cos`.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* real.angle.continuous_coe
- \+ *lemma* real.angle.continuous_cos
- \+ *lemma* real.angle.continuous_sin



## [2022-06-26 17:01:06](https://github.com/leanprover-community/mathlib/commit/28a6f0a)
feat(set_theory/surreal/basic): add `numeric.mk` lemma, golf ([#14962](https://github.com/leanprover-community/mathlib/pull/14962))
#### Estimated changes
Modified src/set_theory/surreal/basic.lean
- \+/\- *theorem* pgame.numeric.add
- \+/\- *theorem* pgame.numeric.le_move_right
- \+/\- *lemma* pgame.numeric.left_lt_right
- \+/\- *theorem* pgame.numeric.lt_move_right
- \+ *lemma* pgame.numeric.mk
- \+/\- *lemma* pgame.numeric.move_left
- \+/\- *theorem* pgame.numeric.move_left_le
- \+/\- *theorem* pgame.numeric.move_left_lt
- \+/\- *lemma* pgame.numeric.move_right
- \+/\- *lemma* pgame.numeric.sub
- \+/\- *lemma* pgame.numeric_def
- \+/\- *theorem* pgame.numeric_of_is_empty_left_moves



## [2022-06-26 17:01:05](https://github.com/leanprover-community/mathlib/commit/54352be)
feat(combinatorics/catalan): definition and equality of recursive and explicit definition ([#14869](https://github.com/leanprover-community/mathlib/pull/14869))
This PR defines the Catalan numbers via the recursive definition $$C (n+1) = \sum_{i=0}^n C (i) * C (n-i)$$. 
Furthermore, it shows that $$ n+1 | \binom {2n}{n}$$ and that the alternative $$C(n)=\frac{1}{n+1} \binom{2n}{n}$$ holds. 
The proof is based on the following stackexchange answer: https://math.stackexchange.com/questions/3304415/catalan-numbers-algebraic-proof-of-the-recurrence-relation which is quite elementary, so that the proof is relatively easy to formalise.
#### Estimated changes
Added src/combinatorics/catalan.lean
- \+ *def* catalan
- \+ *theorem* catalan_eq_central_binom_div
- \+ *lemma* catalan_one
- \+ *lemma* catalan_succ
- \+ *lemma* catalan_three
- \+ *lemma* catalan_two
- \+ *lemma* catalan_zero
- \+ *theorem* succ_mul_catalan_eq_central_binom

Modified src/data/nat/choose/central.lean
- \+ *lemma* nat.succ_dvd_central_binom
- \+ *lemma* nat.two_dvd_central_binom_of_one_le
- \+ *lemma* nat.two_dvd_central_binom_succ



## [2022-06-26 14:56:15](https://github.com/leanprover-community/mathlib/commit/ee7a886)
feat({data/{finset,set},order/filter}/pointwise): Missing `smul_comm_class` instances ([#14963](https://github.com/leanprover-community/mathlib/pull/14963))
Instances of the form `smul_comm_class α β (something γ)`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.image_comm
- \+ *lemma* finset.map_comm

Modified src/data/finset/pointwise.lean


Modified src/data/set/pointwise.lean
- \+/\- *lemma* set.smul_set_mono
- \+ *lemma* set.smul_set_subset_iff

Modified src/order/filter/pointwise.lean




## [2022-06-26 12:02:17](https://github.com/leanprover-community/mathlib/commit/32b08ef)
feat: `add_monoid_with_one`, `add_group_with_one` ([#12182](https://github.com/leanprover-community/mathlib/pull/12182))
Adds two type classes `add_monoid_with_one R` and `add_group_with_one R` with operations for `ℕ → R` and `ℤ → R`, resp.  The type classes extend `add_monoid` and `add_group` because those seem to be the weakest type classes where such a `+₀₁`-homomorphism is guaranteed to exist.  The `nat.cast` function as well as `coe : ℕ → R` are implemented in terms of `add_monoid_with_one R`, removing the infamous `nat.cast` diamond.  Fixes [#946](https://github.com/leanprover-community/mathlib/pull/946).
Some lemmas are less general now because the algebraic hierarchy is not fine-grained enough, or because the lawful coercion only exists for monoids and above.  This generality was not used in mathlib as far as I could tell.  For example:
 - `char_p.char_p_to_char_zero` now requires a group instead of a left-cancellative monoid, because we don't have the `add_left_cancel_monoid_with_one` class
 - `nat.norm_cast_le` now requires a seminormed ring instead of a seminormed group, because we don't have `semi_normed_group_with_one`
#### Estimated changes
Modified archive/100-theorems-list/16_abel_ruffini.lean


Modified archive/100-theorems-list/30_ballot_problem.lean


Modified archive/imo/imo2013_q5.lean


Modified archive/imo/imo2019_q4.lean


Modified counterexamples/phillips.lean


Modified src/algebra/algebra/operations.lean


Modified src/algebra/algebra/subalgebra/basic.lean


Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* int.cast_list_sum
- \+/\- *lemma* int.cast_multiset_sum
- \+/\- *lemma* int.cast_sum
- \+/\- *lemma* nat.cast_list_sum
- \+/\- *lemma* nat.cast_multiset_sum
- \+/\- *lemma* nat.cast_sum

Modified src/algebra/big_operators/pi.lean


Modified src/algebra/category/Ring/colimits.lean


Modified src/algebra/char_p/algebra.lean


Modified src/algebra/char_p/basic.lean
- \+/\- *lemma* char_p.cast_card_eq_zero
- \+/\- *theorem* char_p.cast_eq_zero
- \+/\- *lemma* char_p.char_p_to_char_zero
- \+/\- *theorem* char_p.congr
- \+/\- *theorem* char_p.eq
- \+/\- *lemma* char_p.int_cast_eq_zero_iff
- \+/\- *lemma* char_p.int_coe_eq_int_coe_iff

Modified src/algebra/char_p/char_and_card.lean


Modified src/algebra/char_zero.lean
- \- *theorem* char_zero_of_inj_zero
- \- *lemma* nat.cast_add_one_ne_zero
- \- *theorem* nat.cast_eq_one
- \- *theorem* nat.cast_eq_zero
- \- *theorem* nat.cast_inj
- \- *theorem* nat.cast_injective
- \- *theorem* nat.cast_ne_one
- \- *theorem* nat.cast_ne_zero
- \- *lemma* ordered_semiring.to_char_zero

Added src/algebra/char_zero/defs.lean
- \+ *theorem* char_zero_of_inj_zero
- \+ *lemma* nat.cast_add_one_ne_zero
- \+ *theorem* nat.cast_eq_one
- \+ *theorem* nat.cast_eq_zero
- \+ *theorem* nat.cast_inj
- \+ *theorem* nat.cast_injective
- \+ *theorem* nat.cast_ne_one
- \+ *theorem* nat.cast_ne_zero

Modified src/algebra/direct_sum/internal.lean


Modified src/algebra/direct_sum/ring.lean
- \+ *lemma* direct_sum.of_int_cast
- \+ *lemma* direct_sum.of_nat_cast

Modified src/algebra/field/basic.lean


Modified src/algebra/group/inj_surj.lean


Modified src/algebra/group/opposite.lean


Modified src/algebra/group/ulift.lean


Modified src/algebra/group/with_one.lean


Modified src/algebra/group_power/lemmas.lean
- \+/\- *theorem* nsmul_one
- \+/\- *theorem* zsmul_eq_mul
- \+/\- *lemma* zsmul_one

Modified src/algebra/group_with_zero/power.lean


Modified src/algebra/hom/group_instances.lean


Modified src/algebra/lie/universal_enveloping.lean


Modified src/algebra/module/basic.lean
- \+/\- *lemma* char_zero.of_module

Modified src/algebra/module/linear_map.lean


Modified src/algebra/monoid_algebra/basic.lean


Modified src/algebra/ne_zero.lean
- \+/\- *lemma* ne_zero.ne'
- \+/\- *lemma* ne_zero.not_char_dvd
- \+/\- *lemma* ne_zero.of_ne_zero_coe
- \+/\- *lemma* ne_zero.of_not_dvd
- \+/\- *lemma* ne_zero.pos_of_ne_zero_coe

Modified src/algebra/order/archimedean.lean


Modified src/algebra/order/field.lean


Modified src/algebra/order/floor.lean
- \+/\- *lemma* int.ceil_pos
- \+/\- *lemma* int.ceil_zero
- \+/\- *lemma* int.floor_add_nat
- \+/\- *lemma* int.floor_nat_add
- \+/\- *lemma* int.floor_nonneg
- \+/\- *lemma* int.floor_sub_nat
- \+/\- *lemma* int.floor_zero
- \+/\- *lemma* nat.ceil_eq_zero
- \+/\- *lemma* nat.ceil_zero
- \+/\- *lemma* nat.floor_zero
- \+/\- *lemma* nat.lt_floor_add_one

Modified src/algebra/order/module.lean


Modified src/algebra/order/nonneg.lean


Modified src/algebra/order/ring.lean
- \+ *theorem* nat.strict_mono_cast
- \+ *lemma* ordered_semiring.to_char_zero

Modified src/algebra/punit_instances.lean


Modified src/algebra/quaternion.lean


Modified src/algebra/ring/basic.lean


Modified src/algebra/ring/opposite.lean


Modified src/algebra/ring/prod.lean


Modified src/algebra/ring/ulift.lean


Modified src/algebra/ring_quot.lean


Modified src/algebra/squarefree.lean


Modified src/algebra/star/self_adjoint.lean


Modified src/algebra/triv_sq_zero_ext.lean
- \+ *lemma* triv_sq_zero_ext.fst_mk
- \+ *lemma* triv_sq_zero_ext.snd_mk

Modified src/algebra/tropical/basic.lean


Modified src/analysis/calculus/cont_diff.lean


Modified src/analysis/complex/basic.lean


Modified src/analysis/convex/specific_functions.lean


Modified src/analysis/normed/field/basic.lean
- \+ *lemma* nat.norm_cast_le

Modified src/analysis/normed/group/basic.lean
- \- *lemma* nat.norm_cast_le

Modified src/analysis/normed_space/enorm.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/spectrum.lean


Modified src/analysis/special_functions/gamma.lean


Modified src/analysis/special_functions/integrals.lean


Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/pow_deriv.lean


Modified src/analysis/special_functions/trigonometric/basic.lean


Modified src/analysis/special_functions/trigonometric/complex.lean


Modified src/analysis/specific_limits/basic.lean


Modified src/analysis/specific_limits/normed.lean


Modified src/analysis/subadditive.lean


Modified src/analysis/sum_integral_comparisons.lean


Modified src/combinatorics/simple_graph/regularity/bound.lean


Modified src/combinatorics/simple_graph/regularity/uniform.lean


Modified src/computability/language.lean


Modified src/computability/tm_to_partrec.lean
- \+ *theorem* turing.partrec_to_TM2.tr_nat_default
- \+/\- *theorem* turing.partrec_to_TM2.tr_nat_zero

Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/data/fin/basic.lean


Modified src/data/int/basic.lean
- \+/\- *theorem* int.coe_nat_abs
- \+/\- *theorem* int.coe_nat_eq_zero
- \+/\- *theorem* int.coe_nat_ne_zero
- \+/\- *lemma* int.coe_nat_nonneg
- \+/\- *theorem* int.coe_nat_pos
- \+ *lemma* int.neg_of_nat_ne_zero
- \+ *lemma* int.zero_ne_neg_of_nat

Modified src/data/int/cast.lean
- \- *theorem* int.cast_add
- \+/\- *def* int.cast_add_hom
- \- *theorem* int.cast_bit0
- \- *theorem* int.cast_bit1
- \- *theorem* int.cast_coe_nat'
- \- *theorem* int.cast_coe_nat
- \+/\- *lemma* int.cast_commute
- \- *lemma* int.cast_four
- \+/\- *theorem* int.cast_ite
- \+/\- *theorem* int.cast_mul
- \- *theorem* int.cast_neg
- \+ *lemma* int.cast_neg_nat_cast
- \- *theorem* int.cast_neg_of_nat
- \- *theorem* int.cast_neg_succ_of_nat
- \- *theorem* int.cast_of_nat
- \- *theorem* int.cast_one
- \- *theorem* int.cast_sub
- \- *theorem* int.cast_sub_nat_nat
- \- *lemma* int.cast_three
- \- *lemma* int.cast_two
- \- *theorem* int.cast_zero
- \+/\- *lemma* int.coe_cast_add_hom
- \- *theorem* int.coe_nat_bit0
- \- *theorem* int.coe_nat_bit1
- \- *theorem* int.nat_cast_eq_coe_nat
- \+/\- *lemma* mul_opposite.op_int_cast
- \+/\- *lemma* mul_opposite.unop_int_cast
- \+/\- *lemma* pi.coe_int
- \+/\- *lemma* pi.int_apply
- \+/\- *lemma* prod.fst_int_cast
- \+/\- *lemma* prod.snd_int_cast

Added src/data/int/cast/defs.lean
- \+ *theorem* int.cast_add
- \+ *theorem* int.cast_bit0
- \+ *theorem* int.cast_bit1
- \+ *theorem* int.cast_coe_nat
- \+ *lemma* int.cast_four
- \+ *theorem* int.cast_neg
- \+ *theorem* int.cast_neg_of_nat
- \+ *theorem* int.cast_neg_succ_of_nat
- \+ *theorem* int.cast_of_nat
- \+ *theorem* int.cast_one
- \+ *theorem* int.cast_sub
- \+ *theorem* int.cast_sub_nat_nat
- \+ *lemma* int.cast_three
- \+ *lemma* int.cast_two
- \+ *theorem* int.cast_zero
- \+ *theorem* int.coe_nat_bit0
- \+ *theorem* int.coe_nat_bit1
- \+ *lemma* int.neg_of_nat_eq
- \+ *theorem* nat.cast_pred
- \+ *theorem* nat.cast_sub

Modified src/data/int/char_zero.lean
- \+/\- *theorem* int.cast_eq_zero
- \+/\- *theorem* int.cast_inj
- \+/\- *theorem* int.cast_injective
- \+/\- *theorem* int.cast_ne_zero

Modified src/data/int/interval.lean


Modified src/data/matrix/basic.lean
- \+ *theorem* matrix.diagonal_eq_diagonal_iff

Modified src/data/mv_polynomial/basic.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/cast.lean
- \+/\- *lemma* add_monoid_hom.ext_nat
- \+/\- *lemma* ext_nat'
- \+/\- *lemma* map_nat_cast'
- \+/\- *lemma* mul_opposite.op_nat_cast
- \+/\- *lemma* mul_opposite.unop_nat_cast
- \- *lemma* nat.bin_cast_eq
- \- *theorem* nat.cast_add
- \+/\- *def* nat.cast_add_monoid_hom
- \- *theorem* nat.cast_add_one
- \- *theorem* nat.cast_bit0
- \- *theorem* nat.cast_bit1
- \- *theorem* nat.cast_ite
- \+/\- *theorem* nat.cast_mul
- \+/\- *theorem* nat.cast_nonneg
- \- *theorem* nat.cast_one
- \- *theorem* nat.cast_pred
- \+/\- *lemma* nat.cast_ring_hom_nat
- \- *theorem* nat.cast_sub
- \- *theorem* nat.cast_succ
- \- *lemma* nat.cast_two
- \+/\- *theorem* nat.cast_with_bot
- \- *theorem* nat.cast_zero
- \+/\- *lemma* nat.coe_cast_add_monoid_hom
- \- *theorem* nat.strict_mono_cast
- \+/\- *lemma* pi.coe_nat
- \+/\- *lemma* pi.nat_apply

Added src/data/nat/cast/defs.lean
- \+ *lemma* nat.bin_cast_eq
- \+ *theorem* nat.cast_add
- \+ *theorem* nat.cast_add_one
- \+ *theorem* nat.cast_bit0
- \+ *theorem* nat.cast_bit1
- \+ *theorem* nat.cast_ite
- \+ *theorem* nat.cast_one
- \+ *theorem* nat.cast_succ
- \+ *lemma* nat.cast_two
- \+ *theorem* nat.cast_zero

Modified src/data/nat/choose/sum.lean


Modified src/data/nat/digits.lean


Modified src/data/nat/enat.lean
- \+/\- *lemma* enat.coe_inj
- \+/\- *lemma* enat.dom_coe
- \+/\- *lemma* enat.some_eq_coe

Modified src/data/num/lemmas.lean
- \+ *theorem* num.add_of_nat'
- \+/\- *theorem* num.add_of_nat
- \+ *lemma* num.bit1_succ
- \+/\- *theorem* num.cast_of_znum
- \+/\- *theorem* num.cast_sub'
- \+/\- *theorem* num.cast_succ'
- \+/\- *theorem* num.cast_succ
- \+/\- *theorem* num.cast_to_int
- \+/\- *theorem* num.cast_to_nat
- \+ *theorem* num.of_int'_to_znum
- \+ *lemma* num.of_nat'_bit
- \+ *lemma* num.of_nat'_one
- \+ *lemma* num.of_nat'_succ
- \+ *lemma* num.of_nat'_zero
- \- *theorem* num.of_nat'_zero
- \+/\- *theorem* num.of_nat_cast
- \+/\- *theorem* num.of_nat_inj
- \- *theorem* num.of_nat_to_znum
- \- *theorem* num.of_nat_to_znum_neg
- \+ *theorem* num.of_to_nat'
- \+/\- *theorem* num.of_to_nat
- \+ *theorem* num.pred_succ
- \+ *theorem* num.succ_of_int'
- \+ *theorem* num.to_znum_neg_succ
- \+ *theorem* num.to_znum_succ
- \+/\- *theorem* pos_num.cast_add
- \+/\- *theorem* pos_num.cast_inj
- \+/\- *theorem* pos_num.cast_sub'
- \+/\- *theorem* pos_num.cast_succ
- \+/\- *theorem* pos_num.cast_to_int
- \+/\- *theorem* pos_num.cast_to_nat
- \+ *theorem* pos_num.of_to_nat'
- \+/\- *theorem* pos_num.of_to_nat
- \+/\- *theorem* znum.cast_add
- \+/\- *theorem* znum.cast_bit0
- \+/\- *theorem* znum.cast_bit1
- \+/\- *theorem* znum.cast_bitm1
- \+ *theorem* znum.cast_sub
- \+/\- *theorem* znum.cast_succ
- \+/\- *theorem* znum.cast_to_int
- \+/\- *theorem* znum.of_int'_eq
- \+ *theorem* znum.of_int'_neg
- \+/\- *theorem* znum.of_int_cast
- \+/\- *theorem* znum.of_nat_cast
- \+ *theorem* znum.of_nat_to_znum
- \+ *theorem* znum.of_nat_to_znum_neg
- \+ *theorem* znum.of_to_int'
- \+/\- *theorem* znum.of_to_int
- \+/\- *theorem* znum.to_of_int

Modified src/data/polynomial/basic.lean


Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/laurent.lean


Modified src/data/rat/cast.lean
- \+/\- *theorem* rat.cast_coe_nat

Modified src/data/rat/defs.lean
- \+/\- *theorem* rat.coe_int_eq_mk

Modified src/data/real/basic.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/cau_seq_completion.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/irrational.lean
- \+/\- *theorem* irrational.ne_zero

Modified src/data/real/pi/leibniz.lean


Modified src/data/zmod/basic.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/field_theory/adjoin.lean


Modified src/field_theory/intermediate_field.lean
- \+ *lemma* intermediate_field.coe_nat_mem

Modified src/field_theory/is_alg_closed/basic.lean


Modified src/field_theory/perfect_closure.lean
- \+ *lemma* perfect_closure.mk_zero_zero

Modified src/field_theory/ratfunc.lean


Modified src/field_theory/subfield.lean


Modified src/geometry/euclidean/basic.lean


Modified src/geometry/euclidean/triangle.lean


Modified src/geometry/manifold/instances/sphere.lean
- \+ *lemma* sphere_ext_iff
- \+ *lemma* stereographic'_symm_apply
- \+ *lemma* stereographic_apply

Modified src/group_theory/p_group.lean


Modified src/group_theory/perm/cycle/type.lean


Modified src/group_theory/specific_groups/dihedral.lean


Modified src/group_theory/specific_groups/quaternion.lean


Modified src/linear_algebra/clifford_algebra/grading.lean
- \+ *lemma* clifford_algebra.lift_ι_eq

Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/exterior_algebra/grading.lean
- \+ *def* exterior_algebra.lift_ι
- \+ *lemma* exterior_algebra.lift_ι_eq

Modified src/linear_algebra/linear_independent.lean


Modified src/linear_algebra/matrix/trace.lean


Modified src/linear_algebra/matrix/zpow.lean


Modified src/linear_algebra/quadratic_form/complex.lean


Modified src/logic/equiv/transfer_instance.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/measure/haar.lean


Modified src/measure_theory/probability_mass_function/constructions.lean


Modified src/number_theory/arithmetic_function.lean
- \+/\- *lemma* nat.arithmetic_function.coe_coe
- \+/\- *lemma* nat.arithmetic_function.int_coe_apply
- \+/\- *lemma* nat.arithmetic_function.int_coe_one
- \+/\- *lemma* nat.arithmetic_function.nat_coe_apply
- \+/\- *lemma* nat.arithmetic_function.nat_coe_one

Modified src/number_theory/bernoulli.lean


Modified src/number_theory/bernoulli_polynomials.lean


Modified src/number_theory/class_number/finite.lean


Modified src/number_theory/dioph.lean


Modified src/number_theory/legendre_symbol/quadratic_reciprocity.lean


Modified src/number_theory/liouville/basic.lean


Modified src/number_theory/liouville/measure.lean


Modified src/number_theory/liouville/residual.lean


Modified src/number_theory/lucas_lehmer.lean
- \+/\- *lemma* lucas_lehmer.X.int_coe_fst
- \+/\- *lemma* lucas_lehmer.X.int_coe_snd
- \+/\- *lemma* lucas_lehmer.X.nat_coe_fst
- \+/\- *lemma* lucas_lehmer.X.nat_coe_snd

Modified src/number_theory/modular.lean


Modified src/number_theory/padics/padic_integers.lean


Modified src/number_theory/padics/padic_numbers.lean


Modified src/number_theory/padics/ring_homs.lean


Modified src/number_theory/pell.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/number_theory/zsqrtd/basic.lean
- \+/\- *theorem* zsqrtd.coe_nat_im
- \+/\- *theorem* zsqrtd.coe_nat_re
- \+/\- *theorem* zsqrtd.coe_nat_val

Modified src/number_theory/zsqrtd/gaussian_int.lean
- \+/\- *lemma* gaussian_int.coe_nat_abs_norm

Modified src/order/filter/archimedean.lean


Modified src/order/filter/germ.lean


Modified src/probability/strong_law.lean


Modified src/ring_theory/dedekind_domain/ideal.lean


Modified src/ring_theory/discriminant.lean


Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* fractional_ideal.coe_nat_cast

Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/graded_algebra/basic.lean
- \+/\- *lemma* graded_algebra.mem_support_iff

Modified src/ring_theory/graded_algebra/homogeneous_localization.lean
- \+ *lemma* homogeneous_localization.int_cast_val
- \+ *lemma* homogeneous_localization.nat_cast_val

Modified src/ring_theory/hahn_series.lean


Modified src/ring_theory/ideal/quotient.lean


Modified src/ring_theory/int/basic.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/laurent_series.lean


Modified src/ring_theory/nullstellensatz.lean


Modified src/ring_theory/polynomial/bernstein.lean


Modified src/ring_theory/polynomial/cyclotomic/eval.lean


Modified src/ring_theory/polynomial/eisenstein.lean


Modified src/ring_theory/polynomial/pochhammer.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/subring/basic.lean


Modified src/ring_theory/subsemiring/basic.lean
- \+ *lemma* nat_cast_mem

Modified src/ring_theory/tensor_product.lean


Modified src/ring_theory/witt_vector/basic.lean
- \- *def* witt_vector.constant_coeff
- \- *def* witt_vector.map
- \+ *lemma* witt_vector.map_fun.int_cast
- \+ *lemma* witt_vector.map_fun.nat_cast

Modified src/ring_theory/witt_vector/defs.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/ring_theory/witt_vector/frobenius_fraction_field.lean
- \+ *lemma* witt_vector.exists_frobenius_solution_fraction_ring_aux

Modified src/ring_theory/witt_vector/mul_coeff.lean


Modified src/ring_theory/witt_vector/structure_polynomial.lean


Modified src/ring_theory/witt_vector/truncated.lean
- \- *def* witt_vector.truncate
- \+ *lemma* witt_vector.truncate_fun_int_cast
- \+ *lemma* witt_vector.truncate_fun_nat_cast

Modified src/ring_theory/witt_vector/verschiebung.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean


Modified src/set_theory/cardinal/basic.lean


Modified src/set_theory/game/basic.lean


Modified src/set_theory/game/pgame.lean
- \- *theorem* pgame.nat_one

Modified src/set_theory/ordinal/basic.lean


Modified src/set_theory/ordinal/natural_ops.lean


Modified src/set_theory/surreal/basic.lean


Modified src/set_theory/surreal/dyadic.lean


Modified src/tactic/norm_cast.lean


Modified src/tactic/norm_num.lean


Modified src/tactic/zify.lean


Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/continuous_function/algebra.lean
- \+ *lemma* continuous_map.coe_int_cast
- \+ *lemma* continuous_map.coe_nat_cast

Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.coe_int_cast
- \+ *lemma* bounded_continuous_function.coe_nat_cast

Modified src/topology/continuous_function/compact.lean


Modified src/topology/locally_constant/algebra.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/path_connected.lean


Modified test/norm_cast.lean


Modified test/norm_cast_lemma_order.lean


Modified test/norm_cast_sum_lambda.lean


Modified test/norm_num.lean


Modified test/transport/basic.lean


Modified test/zify.lean




## [2022-06-26 08:42:14](https://github.com/leanprover-community/mathlib/commit/871fcd8)
feat(data/zmod/algebra): add subsingleton instance for zmod-algebras ([#14946](https://github.com/leanprover-community/mathlib/pull/14946))
This will be used to eliminate a diamond with `galois_field.algebra` in a followup PR.
#### Estimated changes
Modified src/data/zmod/algebra.lean




## [2022-06-26 08:01:37](https://github.com/leanprover-community/mathlib/commit/e0ecaa9)
feat(set_theory/ordinal/notation): fast growing hierarchy ([#14072](https://github.com/leanprover-community/mathlib/pull/14072))
Adds a definition `onote.fast_growing` which yields elements of the [fast-growing hierarchy](https://en.wikipedia.org/wiki/Fast-growing_hierarchy) up to and including ε₀. Because it is built on `onote` instead of `ordinal`, the definition is fully computable, and you can work out some small elements. For example `fast_growing_ε₀ 2 = 2048` and `fast_growing_ε₀ 3` is... big.
#### Estimated changes
Modified src/set_theory/ordinal/notation.lean
- \+ *def* onote.fast_growing
- \+ *theorem* onote.fast_growing_def
- \+ *theorem* onote.fast_growing_limit
- \+ *theorem* onote.fast_growing_one
- \+ *theorem* onote.fast_growing_succ
- \+ *theorem* onote.fast_growing_two
- \+ *theorem* onote.fast_growing_zero'
- \+ *theorem* onote.fast_growing_zero
- \+ *def* onote.fast_growing_ε₀
- \+ *theorem* onote.fast_growing_ε₀_one
- \+ *theorem* onote.fast_growing_ε₀_two
- \+ *theorem* onote.fast_growing_ε₀_zero
- \+ *def* onote.fundamental_sequence
- \+ *theorem* onote.fundamental_sequence_has_prop
- \+ *def* onote.fundamental_sequence_prop



## [2022-06-26 04:37:04](https://github.com/leanprover-community/mathlib/commit/cfbb97f)
feat(data/{finset,set}/basic): More `∪`/`∩` laws ([#14952](https://github.com/leanprover-community/mathlib/pull/14952))
Specialise lattice lemmas to `set` and `finset`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.inter_inter_distrib_left
- \+ *lemma* finset.inter_inter_distrib_right
- \+ *lemma* finset.inter_inter_inter_comm
- \+ *lemma* finset.union_union_distrib_left
- \+ *lemma* finset.union_union_distrib_right
- \+ *lemma* finset.union_union_union_comm

Modified src/data/set/basic.lean
- \+ *lemma* set.inter_inter_distrib_left
- \+ *lemma* set.inter_inter_distrib_right
- \+ *lemma* set.inter_inter_inter_comm
- \+ *lemma* set.union_union_distrib_left
- \+ *lemma* set.union_union_distrib_right
- \+ *lemma* set.union_union_union_comm



## [2022-06-26 04:37:03](https://github.com/leanprover-community/mathlib/commit/ccb1cf3)
feat(data/set/lattice): Preimages are disjoint iff the sets are disjoint ([#14951](https://github.com/leanprover-community/mathlib/pull/14951))
Prove `disjoint (f ⁻¹' s) (f ⁻¹' t) ↔ disjoint s t` and `disjoint (f '' s) (f '' t) ↔ disjoint s t` when `f` is surjective/injective. Delete `set.disjoint_preimage` in favor of `disjoint.preimage`. Fix the statement of `set.preimage_eq_empty_iff` (the name referred to the RHS).
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* disjoint.inter_eq
- \+ *lemma* disjoint.of_image
- \+ *lemma* disjoint.of_preimage
- \+ *lemma* set.disjoint_image_iff
- \- *lemma* set.disjoint_preimage
- \+ *lemma* set.disjoint_preimage_iff
- \+/\- *lemma* set.preimage_eq_empty_iff

Modified src/topology/tietze_extension.lean




## [2022-06-26 03:02:54](https://github.com/leanprover-community/mathlib/commit/72cff84)
feat(order/symm_diff): The symmetric difference is involutive ([#14959](https://github.com/leanprover-community/mathlib/pull/14959))
`a ∆ (a ∆ b) = b` and `b ∆ a ∆ a = b`.
#### Estimated changes
Modified src/order/symm_diff.lean
- \+/\- *lemma* symm_diff_left_inj
- \+ *lemma* symm_diff_left_injective
- \+ *lemma* symm_diff_left_involutive
- \+ *lemma* symm_diff_left_surjective
- \+/\- *lemma* symm_diff_right_inj
- \+ *lemma* symm_diff_right_injective
- \+ *lemma* symm_diff_right_involutive
- \+ *lemma* symm_diff_right_surjective
- \+ *lemma* symm_diff_symm_diff_cancel_left
- \+ *lemma* symm_diff_symm_diff_cancel_right
- \- *lemma* symm_diff_symm_diff_self



## [2022-06-26 00:12:23](https://github.com/leanprover-community/mathlib/commit/b8c3e61)
refactor(*): Use `finset.Iix`/`finset.Ixi` ([#14448](https://github.com/leanprover-community/mathlib/pull/14448))
Now that `finset.Iix`/`finset.Ixi` work for empty types, there is no need for `univ.filter (λ j, j < i)` and similar.
#### Estimated changes
Modified src/algebra/big_operators/fin.lean
- \+ *lemma* fin.prod_Ioi_succ
- \+ *lemma* fin.prod_Ioi_zero
- \- *lemma* fin.prod_filter_succ_lt
- \- *lemma* fin.prod_filter_zero_lt

Modified src/data/fin/interval.lean
- \- *lemma* fin.card_filter_ge
- \- *lemma* fin.card_filter_gt
- \- *lemma* fin.card_filter_le
- \- *lemma* fin.card_filter_le_le
- \- *lemma* fin.card_filter_le_lt
- \- *lemma* fin.card_filter_lt
- \- *lemma* fin.card_filter_lt_le
- \- *lemma* fin.card_filter_lt_lt
- \- *lemma* fin.prod_filter_lt_mul_neg_eq_prod_off_diag

Modified src/data/finset/basic.lean
- \+/\- *lemma* finset.disjoint_left
- \+/\- *lemma* finset.disjoint_right

Modified src/data/finset/card.lean


Modified src/data/finset/locally_finite.lean
- \+ *lemma* finset.Ioi_disj_union_Iio
- \+ *lemma* finset.disjoint_Ioi_Iio
- \+ *lemma* finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag

Modified src/data/fintype/fin.lean
- \+ *lemma* fin.Ioi_succ
- \+ *lemma* fin.Ioi_zero_eq_map
- \- *lemma* fin.univ_filter_succ_lt
- \- *lemma* fin.univ_filter_zero_lt

Modified src/linear_algebra/vandermonde.lean


Modified src/ring_theory/discriminant.lean


Modified src/ring_theory/trace.lean




## [2022-06-25 21:12:47](https://github.com/leanprover-community/mathlib/commit/7ee73e4)
feat(data/fintype/basic): Constructing an equivalence from a left inverse ([#14816](https://github.com/leanprover-community/mathlib/pull/14816))
When `f : α → β`, `g : β → α` are inverses one way and `card α ≤ card β`, then they form an equivalence.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *def* equiv.of_left_inverse_of_card_le
- \+ *def* equiv.of_right_inverse_of_card_le
- \- *lemma* fintype.left_inverse_of_right_inverse_of_card_le
- \- *lemma* fintype.right_inverse_of_left_inverse_of_card_le
- \+ *lemma* function.left_inverse.right_inverse_of_card_le
- \+ *lemma* function.right_inverse.left_inverse_of_card_le

Modified src/data/zmod/basic.lean


Modified src/logic/function/basic.lean
- \+ *lemma* function.right_inverse.left_inverse_of_injective
- \+ *lemma* function.right_inverse.left_inverse_of_surjective



## [2022-06-25 21:12:46](https://github.com/leanprover-community/mathlib/commit/8812752)
feat(algebra/field/basic): Semifields ([#14683](https://github.com/leanprover-community/mathlib/pull/14683))
Define division semirings and semifields.
#### Estimated changes
Modified src/algebra/field/basic.lean
- \+/\- *lemma* add_div'
- \+/\- *lemma* add_div
- \+/\- *lemma* add_div_eq_mul_add_div
- \+/\- *lemma* div_add'
- \+/\- *lemma* div_add_div
- \+/\- *lemma* div_add_div_same
- \+/\- *lemma* div_add_one
- \+/\- *lemma* div_add_same
- \+/\- *lemma* field.to_is_field
- \+/\- *lemma* inv_add_inv
- \+/\- *lemma* is_field.nontrivial
- \+/\- *structure* is_field
- \+/\- *lemma* not_is_field_of_subsingleton
- \+/\- *lemma* one_add_div
- \+/\- *lemma* one_div_add_one_div
- \+/\- *lemma* ring_hom.map_div
- \+/\- *lemma* ring_hom.map_eq_zero
- \+/\- *lemma* ring_hom.map_inv
- \+/\- *lemma* ring_hom.map_ne_zero
- \+/\- *lemma* ring_hom.map_units_inv
- \+/\- *lemma* same_add_div
- \+ *lemma* semifield.to_is_field

Modified src/data/complex/basic.lean


Modified src/data/real/nnreal.lean


Modified src/number_theory/cyclotomic/basic.lean


Modified src/ring_theory/ideal/quotient.lean
- \+/\- *theorem* ideal.quotient.maximal_ideal_iff_is_field_quotient

Modified src/ring_theory/witt_vector/basic.lean




## [2022-06-25 20:02:11](https://github.com/leanprover-community/mathlib/commit/f9571f0)
feat(analysis/normed*): add instances about balls and spheres ([#14808](https://github.com/leanprover-community/mathlib/pull/14808))
Non-bc change: `has_inv.inv` on the unit circle is now defined using `has_inv.inv` instead of complex conjugation.
#### Estimated changes
Modified src/analysis/complex/circle.lean
- \+ *def* circle.of_conj_div_self
- \+/\- *def* circle.to_units
- \+/\- *def* circle
- \+/\- *lemma* coe_inv_circle
- \+/\- *lemma* coe_inv_circle_eq_conj

Added src/analysis/normed/field/unit_ball.lean
- \+ *def* submonoid.unit_closed_ball
- \+ *def* submonoid.unit_sphere
- \+ *def* subsemigroup.unit_ball
- \+ *def* subsemigroup.unit_closed_ball
- \+ *def* unit_sphere_to_units

Added src/analysis/normed/group/ball_sphere.lean
- \+ *lemma* coe_neg_ball
- \+ *lemma* coe_neg_closed_ball
- \+ *lemma* coe_neg_sphere

Modified src/analysis/normed/group/basic.lean
- \- *lemma* coe_neg_sphere

Added src/analysis/normed_space/ball_action.lean
- \+ *lemma* ne_neg_of_mem_sphere
- \+ *lemma* ne_neg_of_mem_unit_sphere

Modified src/analysis/normed_space/basic.lean
- \- *lemma* ne_neg_of_mem_sphere
- \- *lemma* ne_neg_of_mem_unit_sphere

Modified src/geometry/manifold/instances/sphere.lean




## [2022-06-25 13:57:10](https://github.com/leanprover-community/mathlib/commit/6f923bd)
chore(*): golf ([#14939](https://github.com/leanprover-community/mathlib/pull/14939))
Some golfs I made while working on a large refactor.
#### Estimated changes
Modified src/data/W/cardinal.lean


Modified src/data/analysis/filter.lean


Modified src/data/set/countable.lean


Modified src/data/set/finite.lean


Modified src/linear_algebra/dimension.lean


Modified src/topology/constructions.lean




## [2022-06-25 07:57:38](https://github.com/leanprover-community/mathlib/commit/07c83c8)
feat(linear_algebra/clifford_algebra/of_alternating): extend alternating maps to the exterior algebra ([#14803](https://github.com/leanprover-community/mathlib/pull/14803))
#### Estimated changes
Modified src/linear_algebra/exterior_algebra/basic.lean


Added src/linear_algebra/exterior_algebra/of_alternating.lean
- \+ *lemma* exterior_algebra.lhom_ext
- \+ *def* exterior_algebra.lift_alternating
- \+ *lemma* exterior_algebra.lift_alternating_algebra_map
- \+ *lemma* exterior_algebra.lift_alternating_apply_ι_multi
- \+ *lemma* exterior_algebra.lift_alternating_comp
- \+ *lemma* exterior_algebra.lift_alternating_comp_ι_multi
- \+ *def* exterior_algebra.lift_alternating_equiv
- \+ *lemma* exterior_algebra.lift_alternating_one
- \+ *lemma* exterior_algebra.lift_alternating_ι
- \+ *lemma* exterior_algebra.lift_alternating_ι_mul
- \+ *lemma* exterior_algebra.lift_alternating_ι_multi



## [2022-06-24 21:45:08](https://github.com/leanprover-community/mathlib/commit/4fd263b)
feat(representation_theory/character): characters of representations ([#14453](https://github.com/leanprover-community/mathlib/pull/14453))
#### Estimated changes
Modified src/algebra/category/FinVect.lean
- \+ *lemma* FinVect.iso.conj_eq_conj
- \+ *def* FinVect.iso_to_linear_equiv
- \+ *def* linear_equiv.to_FinVect_iso

Modified src/representation_theory/basic.lean
- \- *theorem* representation.char_conj
- \- *theorem* representation.char_mul_comm
- \- *theorem* representation.char_one
- \+/\- *lemma* representation.dual_apply
- \+ *lemma* representation.dual_tensor_hom_comm

Added src/representation_theory/character.lean
- \+ *lemma* fdRep.char_conj
- \+ *lemma* fdRep.char_dual
- \+ *lemma* fdRep.char_iso
- \+ *lemma* fdRep.char_lin_hom
- \+ *lemma* fdRep.char_mul_comm
- \+ *lemma* fdRep.char_one
- \+ *lemma* fdRep.char_tensor
- \+ *def* fdRep.character

Modified src/representation_theory/fdRep.lean
- \+ *lemma* fdRep.dual_tensor_iso_lin_hom_hom_hom
- \+ *lemma* fdRep.iso.conj_ρ
- \+ *def* fdRep.iso_to_linear_equiv
- \+ *def* fdRep.ρ



## [2022-06-24 19:24:10](https://github.com/leanprover-community/mathlib/commit/8bf85d7)
feat(algebra/indicator_function): add an apply version of `mul_indicator_finset_bUnion` ([#14919](https://github.com/leanprover-community/mathlib/pull/14919))
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+ *lemma* set.mul_indicator_finset_bUnion_apply



## [2022-06-24 19:24:09](https://github.com/leanprover-community/mathlib/commit/f94a64f)
feat(probability/martingale): add some lemmas for submartingales ([#14904](https://github.com/leanprover-community/mathlib/pull/14904))
#### Estimated changes
Modified src/probability/martingale.lean
- \+ *lemma* measure_theory.submartingale.condexp_sub_nonneg
- \+ *lemma* measure_theory.submartingale_iff_condexp_sub_nonneg
- \+ *lemma* measure_theory.submartingale_nat
- \+ *lemma* measure_theory.submartingale_of_condexp_sub_nonneg
- \+ *lemma* measure_theory.submartingale_of_condexp_sub_nonneg_nat
- \+ *lemma* measure_theory.submartingale_of_set_integral_le_succ



## [2022-06-24 19:24:08](https://github.com/leanprover-community/mathlib/commit/40fa2d8)
feat(topology/metric_space): a countably generated uniformity is metrizable ([#14052](https://github.com/leanprover-community/mathlib/pull/14052))
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_eq_zero_iff'

Modified src/data/nat/lattice.lean
- \+ *lemma* nat.Sup_mem

Added src/topology/metric_space/metrizable_uniformity.lean
- \+ *lemma* pseudo_metric_space.dist_of_prenndist
- \+ *lemma* pseudo_metric_space.dist_of_prenndist_le
- \+ *lemma* pseudo_metric_space.le_two_mul_dist_of_prenndist
- \+ *lemma* uniform_space.metrizable_space



## [2022-06-24 17:15:45](https://github.com/leanprover-community/mathlib/commit/fe322e1)
refactor(algebra/order/monoid): use typeclasses instead of lemmas ([#14848](https://github.com/leanprover-community/mathlib/pull/14848))
Use `covariant_class`/`contravariant_class` instead of type-specific `mul_le_mul_left` etc lemmas. Also, rewrite some proofs to use API about inequalities on `with_top`/`with_bot` instead of the exact form of the current definition.
#### Estimated changes
Modified src/algebra/order/monoid.lean
- \+ *lemma* exists_one_lt_mul_of_lt
- \- *lemma* exists_pos_mul_of_lt
- \- *lemma* with_zero.lt_of_mul_lt_mul_left
- \- *lemma* with_zero.mul_le_mul_left
- \+ *lemma* with_zero.zero_eq_bot
- \+/\- *lemma* with_zero.zero_le



## [2022-06-24 15:26:20](https://github.com/leanprover-community/mathlib/commit/0e5f278)
feat(linear_algebra/{multilinear, alternating}): add `cod_restrict` and lemmas ([#14927](https://github.com/leanprover-community/mathlib/pull/14927))
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *def* alternating_map.cod_restrict
- \+ *lemma* linear_map.comp_alternating_map_cod_restrict
- \+ *lemma* linear_map.subtype_comp_alternating_map_cod_restrict

Modified src/linear_algebra/multilinear/basic.lean
- \+ *lemma* linear_map.comp_multilinear_map_cod_restrict
- \+ *lemma* linear_map.subtype_comp_multilinear_map_cod_restrict
- \+ *def* multilinear_map.cod_restrict



## [2022-06-24 15:26:19](https://github.com/leanprover-community/mathlib/commit/3e326fc)
feat(data/finite/basic): add missing instances ([#14913](https://github.com/leanprover-community/mathlib/pull/14913))
* Add `finite` instances for `prod`, `pprod`, `sigma`, and `psigma`.
* Don't depend on `classical.choice` in `finite_iff_nonempty_fintype`.
* Move `not_finite_iff_infinite` up, use it to golf some proofs.
#### Estimated changes
Modified src/data/finite/basic.lean




## [2022-06-24 15:26:17](https://github.com/leanprover-community/mathlib/commit/363bbd2)
chore(topology/basic): golf a proof ([#14911](https://github.com/leanprover-community/mathlib/pull/14911))
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* mem_closure_of_frequently_of_tendsto



## [2022-06-24 15:26:16](https://github.com/leanprover-community/mathlib/commit/475cf37)
refactor(data/polynomial): extract/add lemmas and golf ([#14888](https://github.com/leanprover-community/mathlib/pull/14888))
+ Extract lemmas `roots_multiset_prod_X_sub_C`, `nat_degree_multiset_prod_X_sub_C_eq_card`, `monic_prod_multiset_X_sub_C` from the proof of `C_leading_coeff_mul_prod_multiset_X_sub_C` in *ring_division.lean*.
+ Add the lemma `exists_prod_multiset_X_sub_C_mul` in *ring_division.lean* and `roots_ne_zero_of_splits` in *splitting_field.lean* and use them to golf `nat_degree_eq_card_roots` The proof of the latter originally depends on `eq_prod_roots_of_splits`, but now the dependency reversed, with `nat_degree_eq_card_roots` now used to golf `eq_prod_roots_of_splits` (and `roots_map` as well).
+ Move `prod_multiset_root_eq_finset_root` and `prod_multiset_X_sub_C_dvd` from *field_division.lean* to *ring_division.lean* and golf the proof of the latter, generalizing `field` to `is_domain`.
+ Remove redundant imports and the lemma `exists_multiset_of_splits`, because it is just one direction of `splits_iff_exists_multiset`, and it follows trivially from `eq_prod_roots_of_splits`. It couldn't be removed before this PR because `roots_map` and `eq_prod_roots_of_splits` depended on it.
+ Golf `splits_of_exists_multiset` (independent of other changes).
#### Estimated changes
Modified src/data/polynomial/field_division.lean
- \- *lemma* polynomial.prod_multiset_X_sub_C_dvd
- \- *lemma* polynomial.prod_multiset_root_eq_finset_root

Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* polynomial.count_map_roots
- \+ *lemma* polynomial.exists_prod_multiset_X_sub_C_mul
- \+ *lemma* polynomial.monic_prod_multiset_X_sub_C
- \+ *lemma* polynomial.nat_degree_multiset_prod_X_sub_C_eq_card
- \+ *lemma* polynomial.prod_multiset_X_sub_C_dvd
- \+ *lemma* polynomial.prod_multiset_root_eq_finset_root
- \+ *lemma* polynomial.roots_multiset_prod_X_sub_C

Modified src/field_theory/abel_ruffini.lean


Modified src/field_theory/separable.lean


Modified src/field_theory/splitting_field.lean
- \+/\- *lemma* polynomial.eq_prod_roots_of_splits
- \- *lemma* polynomial.exists_multiset_of_splits
- \+ *lemma* polynomial.roots_ne_zero_of_splits



## [2022-06-24 15:26:15](https://github.com/leanprover-community/mathlib/commit/dabb0c6)
feat(probability/independence): equivalent ways to check indep_fun ([#14814](https://github.com/leanprover-community/mathlib/pull/14814))
Prove:
- `indep_fun f g μ ↔ ∀ s t, measurable_set s → measurable_set t → μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t)`,
- `indep_fun f g μ ↔ ∀ s t, measurable_set s → measurable_set t → indep_set (f ⁻¹' s) (g ⁻¹' t) μ`.
#### Estimated changes
Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_space.comap_eq_generate_from

Modified src/probability/independence.lean
- \+ *lemma* probability_theory.indep_fun_iff_indep_set_preimage
- \+ *lemma* probability_theory.indep_fun_iff_measure_inter_preimage_eq_mul



## [2022-06-24 15:26:14](https://github.com/leanprover-community/mathlib/commit/7c2ad75)
feat(field_theory.intermediate_field):  intermediate_field.inclusion ([#12596](https://github.com/leanprover-community/mathlib/pull/12596))
#### Estimated changes
Modified src/field_theory/intermediate_field.lean
- \+ *lemma* intermediate_field.coe_inclusion
- \+ *def* intermediate_field.inclusion
- \+ *lemma* intermediate_field.inclusion_inclusion
- \+ *lemma* intermediate_field.inclusion_injective
- \+ *lemma* intermediate_field.inclusion_self



## [2022-06-24 13:23:16](https://github.com/leanprover-community/mathlib/commit/e420232)
feat(data/int/basic): add a better `has_reflect int` instance ([#14906](https://github.com/leanprover-community/mathlib/pull/14906))
This closes a todo comment in `number_theory.lucas_lehmer`.
This also merges `rat.has_reflect` with `rat.reflect` to match `nat.reflect`.
#### Estimated changes
Modified src/data/int/basic.lean


Modified src/data/rat/meta_defs.lean


Modified src/number_theory/lucas_lehmer.lean


Modified test/rat.lean




## [2022-06-24 13:23:15](https://github.com/leanprover-community/mathlib/commit/f05c49f)
feat(meta/univs): Add a reflect_name tactic, make reflected instances universe polymorphic ([#14766](https://github.com/leanprover-community/mathlib/pull/14766))
The existing `list.reflect` instance only works for `Type 0`, this version works for `Type u` providing `u` is known.
#### Estimated changes
Modified src/data/fin/vec_notation.lean


Modified src/data/vector/basic.lean


Added src/meta/univs.lean


Modified test/vec_notation.lean




## [2022-06-24 11:15:40](https://github.com/leanprover-community/mathlib/commit/8187142)
feat(data/finset/pointwise): `s • t` is the union of the `a • t` ([#14696](https://github.com/leanprover-community/mathlib/pull/14696))
and a few other results leading to it. Also tag `set.coe_bUnion` with `norm_cast` and rename `finset.image_mul_prod`/`finset.add_image_prod` to `finset.image_mul_product`/`finset.image_add_product`
#### Estimated changes
Modified src/data/finset/basic.lean
- \+/\- *lemma* finset.coe_bUnion

Modified src/data/finset/n_ary.lean
- \+ *lemma* finset.bUnion_image_left
- \+ *lemma* finset.bUnion_image_right

Modified src/data/finset/pointwise.lean
- \+ *lemma* finset.bUnion_smul_finset
- \- *lemma* finset.image_mul_prod
- \+ *lemma* finset.image_mul_product
- \+ *lemma* finset.pairwise_disjoint_smul_iff

Modified src/data/set/lattice.lean
- \+ *lemma* set.prod_eq_bUnion_left
- \+ *lemma* set.prod_eq_bUnion_right

Modified src/data/set/pairwise.lean
- \+ *lemma* set.pairwise_disjoint_image_left_iff
- \+ *lemma* set.pairwise_disjoint_image_right_iff

Modified src/data/set/pointwise.lean
- \+ *lemma* set.bUnion_smul_set
- \+ *lemma* set.pairwise_disjoint_smul_iff

Modified src/data/set/prod.lean
- \+ *lemma* set.image2_mk_eq_prod



## [2022-06-24 11:15:39](https://github.com/leanprover-community/mathlib/commit/6d00cc2)
feat(ring_theory/trace): Add `trace_eq_sum_automorphisms`, `norm_eq_prod_automorphisms`, `normal.alg_hom_equiv_aut` ([#14523](https://github.com/leanprover-community/mathlib/pull/14523))
#### Estimated changes
Modified src/field_theory/normal.lean
- \+ *def* normal.alg_hom_equiv_aut

Modified src/ring_theory/norm.lean
- \+ *lemma* algebra.norm_eq_prod_automorphisms

Modified src/ring_theory/trace.lean
- \+ *lemma* trace_eq_sum_automorphisms



## [2022-06-24 09:56:29](https://github.com/leanprover-community/mathlib/commit/efe794c)
chore(order/filter): turn `tendsto_id'` into an `iff` lemma ([#14791](https://github.com/leanprover-community/mathlib/pull/14791))
#### Estimated changes
Modified src/dynamics/omega_limit.lean


Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.tendsto_id'
- \+/\- *lemma* filter.tendsto_id

Modified src/topology/instances/ennreal.lean


Modified src/topology/order.lean
- \+ *lemma* continuous_id_iff_le

Modified src/topology/separation.lean




## [2022-06-24 09:16:09](https://github.com/leanprover-community/mathlib/commit/6cefaf4)
feat(measure_theory/function/conditional_expectation): conditional expectation w.r.t. the restriction of a measure to a set ([#14751](https://github.com/leanprover-community/mathlib/pull/14751))
We prove `(μ.restrict s)[f | m] =ᵐ[μ.restrict s] μ[f | m]`.
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean
- \+/\- *lemma* measure_theory.condexp_indicator_aux
- \+ *lemma* measure_theory.condexp_of_ae_strongly_measurable'
- \+ *lemma* measure_theory.condexp_restrict_ae_eq_restrict



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
Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.inv_three_add_inv_three
- \+ *def* ennreal.order_iso_Iic_coe
- \+ *lemma* ennreal.order_iso_Iic_coe_symm_apply_coe
- \+ *def* ennreal.order_iso_Iic_one_birational
- \+ *lemma* ennreal.order_iso_Iic_one_birational_symm_apply
- \+ *def* ennreal.order_iso_unit_interval_birational
- \+ *lemma* ennreal.order_iso_unit_interval_birational_apply_coe

Modified src/data/real/nnreal.lean
- \+ *def* nnreal.order_iso_Icc_zero_coe
- \+ *lemma* nnreal.order_iso_Icc_zero_coe_symm_apply_coe

Modified src/logic/equiv/basic.lean
- \+/\- *def* equiv.subtype_subtype_equiv_subtype
- \- *lemma* equiv.subtype_subtype_equiv_subtype_apply
- \- *lemma* equiv.subtype_subtype_equiv_subtype_exists_apply
- \+/\- *def* equiv.subtype_subtype_equiv_subtype_inter
- \- *lemma* equiv.subtype_subtype_equiv_subtype_inter_apply

Modified src/topology/instances/ennreal.lean




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
Modified src/order/complete_lattice.lean
- \+/\- *theorem* Inf_eq_of_forall_ge_of_forall_gt_exists_lt
- \+ *lemma* Inf_eq_top
- \- *theorem* Inf_eq_top
- \+/\- *theorem* Inf_image
- \+/\- *lemma* Sup_apply
- \+/\- *lemma* Sup_eq_bot
- \+/\- *theorem* Sup_eq_of_forall_le_of_forall_lt_exists_gt
- \+/\- *lemma* Sup_eq_top
- \+/\- *theorem* Sup_image
- \+ *lemma* binary_relation_Inf_iff
- \+/\- *lemma* eq_singleton_top_of_Inf_eq_top_of_nonempty
- \+/\- *lemma* inf_infi
- \+/\- *lemma* infi_and
- \+/\- *theorem* infi_const
- \+/\- *theorem* infi_emptyset
- \+/\- *lemma* infi_eq_bot
- \+/\- *theorem* infi_eq_of_forall_ge_of_forall_gt_exists_lt
- \+/\- *lemma* infi_exists
- \+ *lemma* infi_extend_top
- \+/\- *lemma* infi_image
- \+/\- *lemma* infi_inf
- \+/\- *theorem* infi_inf_eq
- \+ *lemma* infi_le_infi_of_subset
- \- *theorem* infi_le_infi_of_subset
- \+/\- *theorem* infi_option
- \+/\- *theorem* infi_prod
- \+/\- *lemma* infi_range
- \+/\- *theorem* infi_sigma
- \+/\- *lemma* infi_split
- \+/\- *lemma* infi_split_single
- \+/\- *lemma* infi_subtype''
- \+/\- *theorem* infi_subtype
- \+/\- *theorem* infi_sum
- \+ *lemma* infi_supr_ge_nat_add
- \+/\- *lemma* infi_top
- \+/\- *theorem* infi_union
- \+/\- *theorem* infi_univ
- \+/\- *lemma* le_infi_const
- \+/\- *lemma* sup_supr
- \+/\- *lemma* supr_and
- \+/\- *lemma* supr_bot
- \+/\- *theorem* supr_const
- \+/\- *lemma* supr_const_le
- \+/\- *theorem* supr_emptyset
- \+/\- *lemma* supr_eq_top
- \+/\- *lemma* supr_exists
- \+ *lemma* supr_le_supr_of_subset
- \- *theorem* supr_le_supr_of_subset
- \+/\- *theorem* supr_option
- \+/\- *theorem* supr_prod
- \+/\- *theorem* supr_sigma
- \+/\- *lemma* supr_split_single
- \+/\- *lemma* supr_subtype''
- \+/\- *lemma* supr_subtype'
- \+/\- *theorem* supr_subtype
- \+/\- *theorem* supr_sum
- \+/\- *lemma* supr_sup
- \+/\- *theorem* supr_sup_eq
- \+/\- *theorem* supr_univ
- \+ *lemma* unary_relation_Inf_iff



## [2022-06-24 01:29:09](https://github.com/leanprover-community/mathlib/commit/649ca66)
chore(*): Disparate generalizations to division monoids ([#14686](https://github.com/leanprover-community/mathlib/pull/14686))
The leftover changes from the introduction of `division_monoid`.
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean


Modified src/algebra/group/commute.lean
- \+ *lemma* commute.inv_inv
- \- *theorem* commute.inv_inv
- \+ *lemma* commute.inv_inv_iff
- \- *theorem* commute.inv_inv_iff

Modified src/algebra/group/conj.lean


Modified src/algebra/group/prod.lean
- \+/\- *def* div_monoid_hom

Modified src/algebra/group/semiconj.lean
- \+/\- *lemma* semiconj_by.inv_inv_symm
- \+/\- *lemma* semiconj_by.inv_inv_symm_iff

Modified src/algebra/group_with_zero/basic.lean
- \- *theorem* commute.inv_inv₀
- \- *lemma* units.coe_inv'

Modified src/algebra/group_with_zero/power.lean
- \- *lemma* units.coe_zpow₀

Modified src/algebra/order/group.lean


Modified src/analysis/normed_space/spectrum.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/nnreal.lean


Modified src/group_theory/group_action/group.lean
- \+/\- *def* arrow_action

Modified src/group_theory/submonoid/pointwise.lean


Modified src/group_theory/subsemigroup/center.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/ring_theory/dedekind_domain/adic_valuation.lean


Modified src/ring_theory/localization/as_subring.lean


Modified src/topology/algebra/field.lean




## [2022-06-23 23:27:42](https://github.com/leanprover-community/mathlib/commit/56185bd)
feat(data/finset): add some lemmas about `finset.disj_union` ([#14910](https://github.com/leanprover-community/mathlib/pull/14910))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_disj_union

Modified src/data/finset/basic.lean
- \+ *lemma* finset.forall_mem_map
- \+ *theorem* finset.map_disj_union'
- \+ *theorem* finset.map_disj_union
- \+ *theorem* finset.map_disj_union_aux

Modified src/data/finset/fold.lean
- \+ *theorem* finset.fold_disj_union



## [2022-06-23 20:16:37](https://github.com/leanprover-community/mathlib/commit/198cb64)
refactor(ring_theory): generalize basic API of `ring_hom` to `ring_hom_class` ([#14756](https://github.com/leanprover-community/mathlib/pull/14756))
This PR generalizes part of the basic API of ring homs to `ring_hom_class`. This notably includes things like `ring_hom.ker`, `ideal.map` and `ideal.comap`. I left the namespaces unchanged, for example `ring_hom.ker` remains the same even though it is now defined for any `ring_hom_class` morphism; this way dot notation still (mostly) works for actual ring homs.
#### Estimated changes
Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/ideal/local_ring.lean


Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* ideal.apply_coe_mem_map
- \+/\- *lemma* ideal.comap_le_map_of_inv_on
- \+/\- *lemma* ideal.comap_le_map_of_inverse
- \+/\- *lemma* ideal.ker_le_comap
- \+/\- *lemma* ideal.map_Inf
- \+/\- *lemma* ideal.map_eq_bot_iff_le_ker
- \+/\- *theorem* ideal.map_is_prime_of_equiv
- \+/\- *theorem* ideal.map_is_prime_of_surjective
- \+/\- *lemma* ideal.map_le_comap_of_inv_on
- \+/\- *lemma* ideal.map_le_comap_of_inverse
- \+/\- *lemma* ideal.map_span
- \+/\- *theorem* ideal.mem_map_of_mem
- \+/\- *lemma* ring_hom.comap_ker
- \+/\- *lemma* ring_hom.ker_coe_equiv
- \+/\- *lemma* ring_hom.ker_eq_comap_bot
- \+ *lemma* ring_hom.ker_equiv
- \+/\- *lemma* ring_hom.ker_is_maximal_of_surjective
- \+/\- *lemma* ring_hom.ker_is_prime
- \+/\- *lemma* ring_hom.ker_ne_top
- \+/\- *lemma* ring_hom.not_one_mem_ker

Modified src/ring_theory/ideal/over.lean


Modified src/ring_theory/ideal/prod.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/jacobson_ideal.lean


Modified src/ring_theory/localization/localization_localization.lean


Modified src/ring_theory/polynomial/basic.lean
- \+/\- *lemma* mv_polynomial.ker_map



## [2022-06-23 16:23:10](https://github.com/leanprover-community/mathlib/commit/44d3fc0)
chore(data/nat,int): move field-specific lemmas about cast ([#14890](https://github.com/leanprover-community/mathlib/pull/14890))
I want to refer to the rational numbers in the definition of a field, meaning we can't have `algebra.field.basic` in the transitive imports of `data.rat.basic`.
This is a step in rearranging those imports: remove the definition of a field from the dependencies of the casts `ℕ → α` and `ℤ → α`, where `α` is a (semi)ring.
#### Estimated changes
Modified src/algebra/big_operators/ring.lean


Modified src/algebra/char_zero.lean


Modified src/algebra/order/field.lean
- \+ *theorem* nat.cast_le_pow_div_sub
- \+ *theorem* nat.cast_le_pow_sub_div_sub
- \+ *lemma* pow_minus_two_nonneg

Deleted src/algebra/order/field_pow.lean
- \- *theorem* nat.cast_le_pow_div_sub
- \- *theorem* nat.cast_le_pow_sub_div_sub
- \- *lemma* pow_minus_two_nonneg

Modified src/algebra/order/smul.lean


Modified src/analysis/special_functions/bernstein.lean


Modified src/analysis/specific_limits/normed.lean


Modified src/data/int/cast.lean
- \- *theorem* int.cast_div

Added src/data/int/cast_field.lean
- \+ *theorem* int.cast_div

Modified src/data/int/char_zero.lean


Modified src/data/nat/cast.lean
- \- *theorem* nat.cast_div
- \- *lemma* nat.cast_div_le
- \- *lemma* nat.inv_pos_of_nat
- \- *lemma* nat.one_div_le_one_div
- \- *lemma* nat.one_div_lt_one_div
- \- *lemma* nat.one_div_pos_of_nat

Added src/data/nat/cast_field.lean
- \+ *theorem* nat.cast_div
- \+ *lemma* nat.cast_div_le
- \+ *lemma* nat.inv_pos_of_nat
- \+ *lemma* nat.one_div_le_one_div
- \+ *lemma* nat.one_div_lt_one_div
- \+ *lemma* nat.one_div_pos_of_nat

Modified src/data/nat/choose/bounds.lean


Modified src/data/rat/order.lean


Modified src/order/filter/at_top_bot.lean




## [2022-06-23 16:23:08](https://github.com/leanprover-community/mathlib/commit/c3e3d1a)
feat(data/set): replace `set_coe.can_lift` by `subtype.can_lift` ([#14792](https://github.com/leanprover-community/mathlib/pull/14792))
#### Estimated changes
Modified src/data/set/basic.lean


Modified src/tactic/lift.lean




## [2022-06-23 16:23:07](https://github.com/leanprover-community/mathlib/commit/4de20c5)
feat(analysis/../log): log_nat_eq_sum_factorization ([#14782](https://github.com/leanprover-community/mathlib/pull/14782))
#### Estimated changes
Modified src/analysis/special_functions/log/basic.lean
- \+ *lemma* real.log_nat_eq_sum_factorization



## [2022-06-23 16:23:06](https://github.com/leanprover-community/mathlib/commit/c2fcf9f)
feat(data/polynomial/erase_lead): Characterizations of polynomials of small support ([#14500](https://github.com/leanprover-community/mathlib/pull/14500))
This PR adds iff-lemmas `card_support_eq_one`, `card_support_eq_two`, and `card_support_eq_three`. These will be useful for irreducibility of x^n-x-1.
#### Estimated changes
Modified src/data/polynomial/erase_lead.lean
- \+ *lemma* polynomial.card_support_eq_one
- \+ *lemma* polynomial.card_support_eq_three
- \+ *lemma* polynomial.card_support_eq_two



## [2022-06-23 14:10:06](https://github.com/leanprover-community/mathlib/commit/ef24ace)
feat(order/hom/basic): some lemmas about order homs and equivs  ([#14872](https://github.com/leanprover-community/mathlib/pull/14872))
A few lemmas from [#11053](https://github.com/leanprover-community/mathlib/pull/11053), which I have seperated from the original PR following @riccardobrasca's suggestion.
#### Estimated changes
Modified src/order/hom/basic.lean
- \+ *lemma* order_hom.coe_eq
- \+ *def* order_iso.of_hom_inv



## [2022-06-23 14:10:05](https://github.com/leanprover-community/mathlib/commit/dd2e7ad)
feat(analysis/convex/strict_convex_space): isometries of strictly convex spaces are affine ([#14837](https://github.com/leanprover-community/mathlib/pull/14837))
Add the result that isometries of (affine spaces for) real normed
spaces with strictly convex codomain are affine isometries.  In
particular, this applies to isometries of Euclidean spaces (we already
have the instance that real inner product spaces are uniformly convex
and thus strictly convex).  Strict convexity means the surjectivity
requirement of Mazur-Ulam can be avoided.
#### Estimated changes
Modified src/analysis/convex/strict_convex_space.lean
- \+ *lemma* eq_line_map_of_dist_eq_mul_of_dist_eq_mul
- \+ *lemma* eq_midpoint_of_dist_eq_half
- \+ *lemma* isometry.affine_isometry_of_strict_convex_space_apply
- \+ *lemma* isometry.coe_affine_isometry_of_strict_convex_space

Modified src/analysis/normed/group/add_torsor.lean
- \+ *lemma* dist_eq_norm_vsub'



## [2022-06-23 14:10:04](https://github.com/leanprover-community/mathlib/commit/966bb24)
feat(group_theory/finite_abelian): Structure of finite abelian groups ([#14736](https://github.com/leanprover-community/mathlib/pull/14736))
Any finitely generated abelian group is the product of a power of `ℤ` and a direct sum of some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`.
Any finite abelian group is a direct sum of some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`.
(TODO : prove uniqueness of this decomposition)
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/algebra/group/prod.lean
- \+ *def* mul_equiv.prod_congr
- \+ *def* mul_equiv.prod_unique
- \+ *def* mul_equiv.unique_prod

Modified src/data/zmod/basic.lean
- \+ *def* zmod.ring_equiv_congr

Added src/group_theory/finite_abelian.lean
- \+ *theorem* add_comm_group.equiv_direct_sum_zmod_of_fintype
- \+ *theorem* add_comm_group.equiv_free_prod_direct_sum_zmod

Modified src/group_theory/finiteness.lean


Modified src/linear_algebra/prod.lean


Modified src/logic/equiv/basic.lean
- \+ *def* equiv.prod_unique
- \+ *def* equiv.unique_prod



## [2022-06-23 14:10:03](https://github.com/leanprover-community/mathlib/commit/cff439d)
feat(analysis/seminorm): add add_group_seminorm ([#14336](https://github.com/leanprover-community/mathlib/pull/14336))
We introduce `add_group_seminorm` and refactor `seminorm` to extend this new definition. This new `add_group_seminorm` structure will also be used in [#14115](https://github.com/leanprover-community/mathlib/pull/14115) to define `ring_seminorm`.
#### Estimated changes
Modified counterexamples/seminorm_lattice_not_distrib.lean


Modified src/analysis/convex/gauge.lean


Modified src/analysis/seminorm.lean
- \+ *lemma* add_group_seminorm.add_apply
- \+ *lemma* add_group_seminorm.add_comp
- \+ *lemma* add_group_seminorm.coe_add
- \+ *lemma* add_group_seminorm.coe_comp
- \+ *lemma* add_group_seminorm.coe_smul
- \+ *lemma* add_group_seminorm.coe_sup
- \+ *lemma* add_group_seminorm.coe_zero
- \+ *def* add_group_seminorm.comp
- \+ *lemma* add_group_seminorm.comp_add_le
- \+ *lemma* add_group_seminorm.comp_apply
- \+ *lemma* add_group_seminorm.comp_comp
- \+ *lemma* add_group_seminorm.comp_id
- \+ *lemma* add_group_seminorm.comp_mono
- \+ *lemma* add_group_seminorm.comp_zero
- \+ *lemma* add_group_seminorm.ext
- \+ *lemma* add_group_seminorm.inf_apply
- \+ *lemma* add_group_seminorm.le_def
- \+ *lemma* add_group_seminorm.le_insert'
- \+ *lemma* add_group_seminorm.le_insert
- \+ *lemma* add_group_seminorm.lt_def
- \+ *lemma* add_group_seminorm.smul_apply
- \+ *lemma* add_group_seminorm.smul_sup
- \+ *lemma* add_group_seminorm.sub_rev
- \+ *lemma* add_group_seminorm.sup_apply
- \+ *lemma* add_group_seminorm.zero_apply
- \+ *lemma* add_group_seminorm.zero_comp
- \+ *structure* add_group_seminorm
- \+ *lemma* coe_norm_add_group_seminorm
- \+ *def* norm_add_group_seminorm
- \+/\- *def* norm_seminorm
- \+/\- *lemma* seminorm.ball_bot
- \+/\- *lemma* seminorm.ball_finset_sup
- \+ *lemma* seminorm.comp_add_le
- \- *lemma* seminorm.comp_triangle
- \- *lemma* seminorm.nonneg
- \+ *def* seminorm.of
- \+/\- *structure* seminorm



## [2022-06-23 14:10:01](https://github.com/leanprover-community/mathlib/commit/585a1bf)
feat(number_theory): define ramification index and inertia degree ([#14332](https://github.com/leanprover-community/mathlib/pull/14332))
We define ramification index `ramification_idx` and inertia degree `inertia_deg` for `P : ideal S` over `p : ideal R` given a ring extension `f : R →+* S`. The literature generally assumes `p` is included in `P`, both are maximal, `R` is the ring of integers of a number field `K` and `S` is the integral closure of `R` in `L`, a finite separable extension of `K`; we relax these assumptions as much as is practical.
#### Estimated changes
Added src/number_theory/ramification_inertia.lean
- \+ *lemma* ideal.inertia_deg_algebra_map
- \+ *lemma* ideal.inertia_deg_of_subsingleton
- \+ *lemma* ideal.is_dedekind_domain.ramification_idx_eq_factors_count
- \+ *lemma* ideal.is_dedekind_domain.ramification_idx_eq_normalized_factors_count
- \+ *lemma* ideal.is_dedekind_domain.ramification_idx_ne_zero
- \+ *lemma* ideal.le_pow_of_le_ramification_idx
- \+ *lemma* ideal.le_pow_ramification_idx
- \+ *lemma* ideal.ramification_idx_bot
- \+ *lemma* ideal.ramification_idx_eq_find
- \+ *lemma* ideal.ramification_idx_eq_zero
- \+ *lemma* ideal.ramification_idx_lt
- \+ *lemma* ideal.ramification_idx_ne_zero
- \+ *lemma* ideal.ramification_idx_of_not_le
- \+ *lemma* ideal.ramification_idx_spec



## [2022-06-23 11:58:10](https://github.com/leanprover-community/mathlib/commit/cc4b8e5)
feat(data/sigma,data/ulift,logic/equiv): add missing lemmas ([#14903](https://github.com/leanprover-community/mathlib/pull/14903))
Add lemmas and `equiv`s about `plift`, `psigma`, and `pprod`.
#### Estimated changes
Modified src/data/sigma/basic.lean
- \+ *theorem* psigma.«exists»
- \+ *theorem* psigma.«forall»

Modified src/data/ulift.lean
- \+ *lemma* plift.down_bijective
- \+ *lemma* plift.down_surjective
- \+ *lemma* plift.up_bijective
- \+ *lemma* plift.up_inj
- \+ *lemma* plift.up_injective
- \+ *lemma* plift.up_surjective
- \+ *lemma* ulift.down_bijective
- \+ *lemma* ulift.down_surjective
- \+ *lemma* ulift.up_bijective
- \+ *lemma* ulift.up_inj
- \+ *lemma* ulift.up_injective
- \+ *lemma* ulift.up_surjective

Modified src/logic/equiv/basic.lean
- \+ *def* equiv.pprod_equiv_prod_plift
- \+ *def* equiv.psigma_equiv_sigma_plift

Modified src/set_theory/cardinal/cofinality.lean




## [2022-06-23 10:25:45](https://github.com/leanprover-community/mathlib/commit/cf23199)
chore(number_theory/lucas_lehmer): remove `has_to_pexpr` instances ([#14905](https://github.com/leanprover-community/mathlib/pull/14905))
These instances are sort of out-of-place, and aren't really needed anyway.
We already use the more verbose ``%%`(n)`` notation elsewhere in mathlib, which as an operation makes more conceptual sense.
Until [#14901](https://github.com/leanprover-community/mathlib/pull/14901) these two instances were just special cases of `has_reflect.has_to_pexpr`. While unlike that instance these two instances are not diamond-forming, they're unecessary special cases that make antiquoting harder to understand.
#### Estimated changes
Modified src/number_theory/lucas_lehmer.lean




## [2022-06-22 23:55:53](https://github.com/leanprover-community/mathlib/commit/416edbd)
chore(ring_theory/polynomial/symmetric): golf proofs ([#14866](https://github.com/leanprover-community/mathlib/pull/14866))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* equiv.finset_congr_to_embedding

Modified src/data/finset/powerset.lean
- \+ *theorem* finset.powerset_len_map

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.map_univ_equiv
- \+ *lemma* finset.map_univ_of_surjective

Modified src/ring_theory/polynomial/symmetric.lean




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
Modified src/meta/expr.lean


Modified src/tactic/core.lean


Modified src/tactic/transform_decl.lean


Modified test/norm_swap.lean




## [2022-06-22 18:31:24](https://github.com/leanprover-community/mathlib/commit/2a732ed)
chore(analysis/special_functions/log/basic): golf a proof ([#14898](https://github.com/leanprover-community/mathlib/pull/14898))
#### Estimated changes
Modified src/analysis/special_functions/log/basic.lean




## [2022-06-22 18:31:23](https://github.com/leanprover-community/mathlib/commit/23918a5)
feat(order/filter/basic): add some lemmas about `eventually_le` ([#14891](https://github.com/leanprover-community/mathlib/pull/14891))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_le.mul_le_mul
- \+ *lemma* filter.eventually_le.mul_nonneg
- \+ *lemma* filter.eventually_sub_nonneg



## [2022-06-22 18:31:21](https://github.com/leanprover-community/mathlib/commit/12e5f2e)
refactor(data/set/countable): make `set.countable` protected ([#14886](https://github.com/leanprover-community/mathlib/pull/14886))
I'm going to add `_root_.countable` typeclass, a data-free version of `encodable`.
#### Estimated changes
Modified counterexamples/phillips.lean
- \+/\- *lemma* phillips_1940.bounded_additive_measure.apply_countable
- \+/\- *lemma* phillips_1940.countable_compl_spf
- \+/\- *lemma* phillips_1940.countable_spf_mem

Modified src/analysis/box_integral/divergence_theorem.lean


Modified src/analysis/complex/cauchy_integral.lean


Modified src/analysis/special_functions/complex/log.lean
- \+/\- *lemma* complex.countable_preimage_exp

Modified src/data/complex/cardinality.lean
- \+/\- *lemma* not_countable_complex

Modified src/data/real/cardinality.lean
- \+/\- *lemma* cardinal.not_countable_real

Modified src/data/set/countable.lean
- \+/\- *lemma* set.countable.exists_surjective
- \+/\- *lemma* set.countable.image2
- \+/\- *lemma* set.countable.image
- \+/\- *lemma* set.countable.insert
- \+/\- *lemma* set.countable.mono
- \+/\- *lemma* set.countable.preimage_of_inj_on
- \+/\- *lemma* set.countable.sUnion
- \+/\- *def* set.countable.to_encodable
- \- *def* set.countable
- \+/\- *lemma* set.countable_Union
- \+/\- *lemma* set.countable_Union_Prop
- \+/\- *lemma* set.countable_empty
- \+/\- *lemma* set.countable_encodable'
- \+/\- *lemma* set.countable_encodable
- \+/\- *lemma* set.countable_insert
- \+/\- *lemma* set.countable_is_bot
- \+/\- *lemma* set.countable_is_top
- \+/\- *lemma* set.countable_pi
- \+/\- *lemma* set.countable_range
- \+/\- *lemma* set.countable_set_of_finite_subset
- \+/\- *lemma* set.countable_singleton
- \+/\- *lemma* set.countable_union
- \+/\- *def* set.enumerate_countable
- \+/\- *lemma* set.finite.countable
- \+/\- *lemma* set.subset_range_enumerate
- \+/\- *lemma* set.subsingleton.countable

Modified src/geometry/manifold/charted_space.lean


Modified src/measure_theory/constructions/borel_space.lean
- \+/\- *lemma* ae_measurable_binfi
- \+/\- *lemma* ae_measurable_bsupr
- \+/\- *lemma* measurable_binfi
- \+/\- *lemma* measurable_bsupr

Modified src/measure_theory/constructions/polish.lean


Modified src/measure_theory/covering/besicovitch.lean


Modified src/measure_theory/covering/differentiation.lean


Modified src/measure_theory/covering/vitali.lean


Modified src/measure_theory/covering/vitali_family.lean
- \+/\- *lemma* vitali_family.fine_subfamily_on.index_countable

Modified src/measure_theory/function/ae_measurable_order.lean


Modified src/measure_theory/function/jacobian.lean


Modified src/measure_theory/integral/circle_integral.lean


Modified src/measure_theory/integral/divergence_theorem.lean


Modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* measure_theory.lintegral_bUnion
- \+/\- *lemma* measure_theory.lintegral_bUnion₀

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable_set.pi
- \+/\- *lemma* measurable_set_pi

Modified src/measure_theory/measurable_space_def.lean
- \+/\- *lemma* measurable_set.bInter
- \+/\- *lemma* measurable_set.bUnion
- \+/\- *lemma* measurable_set.sInter
- \+/\- *lemma* measurable_set.sUnion
- \+/\- *lemma* set.countable.measurable_set

Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.bsupr_measure_Iic
- \+/\- *lemma* measure_theory.measure.ext_iff_of_bUnion_eq_univ
- \+/\- *lemma* measure_theory.measure.ext_iff_of_sUnion_eq_univ
- \+/\- *lemma* measure_theory.measure.restrict_bUnion_congr
- \+/\- *lemma* measure_theory.measure.restrict_sUnion_congr
- \+/\- *lemma* measure_theory.measure.sigma_finite_of_countable
- \+/\- *lemma* measure_theory.measure_bUnion
- \+/\- *lemma* measure_theory.measure_bUnion_eq_supr
- \+/\- *lemma* measure_theory.measure_bUnion_to_measurable
- \+/\- *lemma* measure_theory.measure_bUnion₀
- \+/\- *lemma* measure_theory.measure_sUnion
- \+/\- *lemma* measure_theory.measure_sUnion₀
- \+/\- *lemma* measure_theory.tsum_measure_preimage_singleton

Modified src/measure_theory/measure/measure_space_def.lean
- \+/\- *lemma* measure_theory.ae_ball_iff
- \+/\- *lemma* measure_theory.measure_bUnion_le
- \+/\- *lemma* measure_theory.measure_bUnion_null_iff
- \+/\- *lemma* measure_theory.measure_sUnion_null_iff

Modified src/measure_theory/measure/null_measurable.lean


Modified src/measure_theory/measure/outer_measure.lean
- \+/\- *lemma* measure_theory.outer_measure.bUnion_null_iff
- \+/\- *lemma* measure_theory.outer_measure.sUnion_null_iff

Modified src/order/filter/bases.lean
- \+/\- *lemma* filter.countable_binfi_eq_infi_seq'
- \+/\- *lemma* filter.countable_binfi_eq_infi_seq
- \+/\- *lemma* filter.countable_binfi_principal_eq_seq_infi
- \+/\- *lemma* filter.is_countably_generated_binfi_principal

Modified src/order/filter/countable_Inter.lean
- \+/\- *lemma* countable_bInter_mem
- \+/\- *lemma* countable_sInter_mem
- \+/\- *lemma* eventually_countable_ball
- \+/\- *lemma* eventually_eq.countable_bInter
- \+/\- *lemma* eventually_eq.countable_bUnion
- \+/\- *lemma* eventually_le.countable_bInter
- \+/\- *lemma* eventually_le.countable_bUnion

Modified src/set_theory/cardinal/basic.lean
- \+/\- *lemma* cardinal.mk_set_le_aleph_0
- \+/\- *lemma* cardinal.mk_subtype_le_aleph_0

Modified src/set_theory/cardinal/ordinal.lean
- \+/\- *lemma* cardinal.countable_iff_lt_aleph_one

Modified src/topology/G_delta.lean
- \+/\- *lemma* is_Gδ_bInter
- \+/\- *lemma* is_Gδ_bInter_of_open
- \+/\- *lemma* is_Gδ_sInter
- \+/\- *lemma* set.countable.is_Gδ_compl

Modified src/topology/algebra/order/basic.lean


Modified src/topology/bases.lean
- \+/\- *lemma* set.countable.is_separable
- \+/\- *lemma* topological_space.countable_countable_basis

Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/baire.lean
- \+/\- *theorem* dense_sInter_of_Gδ
- \+/\- *theorem* dense_sInter_of_open

Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/hausdorff_dimension.lean
- \+/\- *lemma* dimH_bUnion
- \+/\- *lemma* dimH_countable
- \+/\- *lemma* dimH_sUnion

Modified src/topology/metric_space/kuratowski.lean


Modified src/topology/subset_properties.lean
- \+/\- *lemma* sigma_compact_space.of_countable



## [2022-06-22 18:31:20](https://github.com/leanprover-community/mathlib/commit/d8fc588)
refactor(data/finite/card): split from `basic` ([#14885](https://github.com/leanprover-community/mathlib/pull/14885))
#### Estimated changes
Modified src/data/finite/basic.lean
- \- *lemma* finite.card_eq
- \- *lemma* finite.card_eq_zero_iff
- \- *lemma* finite.card_le_of_embedding
- \- *lemma* finite.card_le_of_injective
- \- *lemma* finite.card_le_of_surjective
- \- *lemma* finite.card_le_one_iff_subsingleton
- \- *lemma* finite.card_option
- \- *lemma* finite.card_pos_iff
- \- *theorem* finite.card_subtype_le
- \- *theorem* finite.card_subtype_lt
- \- *lemma* finite.card_sum
- \- *def* finite.equiv_fin
- \- *def* finite.equiv_fin_of_card_eq
- \- *lemma* finite.one_lt_card
- \- *lemma* finite.one_lt_card_iff_nontrivial
- \- *lemma* nat.card_eq

Added src/data/finite/card.lean
- \+ *lemma* finite.card_eq
- \+ *lemma* finite.card_eq_zero_iff
- \+ *lemma* finite.card_le_of_embedding
- \+ *lemma* finite.card_le_of_injective
- \+ *lemma* finite.card_le_of_surjective
- \+ *lemma* finite.card_le_one_iff_subsingleton
- \+ *lemma* finite.card_option
- \+ *lemma* finite.card_pos_iff
- \+ *theorem* finite.card_subtype_le
- \+ *theorem* finite.card_subtype_lt
- \+ *lemma* finite.card_sum
- \+ *def* finite.equiv_fin
- \+ *def* finite.equiv_fin_of_card_eq
- \+ *lemma* finite.one_lt_card
- \+ *lemma* finite.one_lt_card_iff_nontrivial
- \+ *lemma* nat.card_eq



## [2022-06-22 18:31:18](https://github.com/leanprover-community/mathlib/commit/c2719ad)
feat(topology/basic): `sum.elim` of locally finite set families is locally finite ([#14826](https://github.com/leanprover-community/mathlib/pull/14826))
#### Estimated changes
Modified src/order/filter/small_sets.lean
- \+ *lemma* filter.frequently_small_sets
- \+ *lemma* filter.frequently_small_sets_mem

Modified src/topology/basic.lean
- \+ *lemma* locally_finite.eventually_finite
- \+ *lemma* locally_finite.preimage_continuous
- \+ *lemma* locally_finite.sum_elim



## [2022-06-22 18:31:17](https://github.com/leanprover-community/mathlib/commit/44bb35e)
feat({algebra/big_operators/basic,data/rat/cast}): Missing cast lemmas ([#14824](https://github.com/leanprover-community/mathlib/pull/14824))
`rat.cast_sum`, `rat.cast_prod` and `nat`, `int` lemmas about `multiset` and `list` big operators.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* int.cast_list_prod
- \+ *lemma* int.cast_list_sum
- \+ *lemma* int.cast_multiset_prod
- \+ *lemma* int.cast_multiset_sum
- \+/\- *lemma* int.cast_prod
- \+/\- *lemma* int.cast_sum
- \+ *lemma* nat.cast_list_prod
- \+ *lemma* nat.cast_list_sum
- \+ *lemma* nat.cast_multiset_prod
- \+ *lemma* nat.cast_multiset_sum
- \+/\- *lemma* nat.cast_prod
- \+/\- *lemma* nat.cast_sum

Modified src/data/finsupp/basic.lean
- \+ *lemma* rat.cast_finsupp_prod
- \+ *lemma* rat.cast_finsupp_sum

Modified src/data/rat/cast.lean
- \+/\- *theorem* rat.cast_div
- \+/\- *def* rat.cast_hom
- \+/\- *theorem* rat.cast_inv
- \+ *lemma* rat.cast_list_prod
- \+ *lemma* rat.cast_list_sum
- \+/\- *theorem* rat.cast_mk
- \+ *lemma* rat.cast_multiset_prod
- \+ *lemma* rat.cast_multiset_sum
- \+/\- *theorem* rat.cast_pow
- \+ *lemma* rat.cast_prod
- \+ *lemma* rat.cast_sum
- \+/\- *lemma* rat.coe_cast_hom



## [2022-06-22 16:29:05](https://github.com/leanprover-community/mathlib/commit/38642ef)
chore(data/rat): rename `data.rat.basic` to `data.rat.defs` ([#14895](https://github.com/leanprover-community/mathlib/pull/14895))
This is a preparatory step for PR [#14893](https://github.com/leanprover-community/mathlib/pull/14893) that moves only the `field ℚ` instance (and its small set of dependencies) back to `data.rat.basic`; doing this in two moves should produce a neater set of diffs.
#### Estimated changes
Modified archive/imo/imo1988_q6.lean


Modified archive/imo/imo2013_q5.lean


Modified src/algebraic_geometry/EllipticCurve.lean


Renamed src/data/rat/basic.lean to src/data/rat/defs.lean


Modified src/data/rat/meta_defs.lean


Modified src/data/rat/order.lean


Modified test/rewrite_search/rewrite_search.lean




## [2022-06-22 16:29:04](https://github.com/leanprover-community/mathlib/commit/f57c0cd)
chore(algebra/{group_power,order}): split off field lemmas ([#14849](https://github.com/leanprover-community/mathlib/pull/14849))
I want to refer to the rational numbers in the definition of a field, meaning we can't have `algebra.field.basic` in the transitive imports of `data.rat.basic`.
This is half of rearranging those imports: remove the definition of a field from the dependencies of basic lemmas about `nsmul`, `npow`, `zsmul` and `zpow`.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \- *theorem* nat.cast_le_pow_div_sub
- \- *theorem* nat.cast_le_pow_sub_div_sub

Modified src/algebra/group_with_zero/power.lean
- \- *lemma* pow_minus_two_nonneg

Added src/algebra/order/field_pow.lean
- \+ *theorem* nat.cast_le_pow_div_sub
- \+ *theorem* nat.cast_le_pow_sub_div_sub
- \+ *lemma* pow_minus_two_nonneg

Modified src/analysis/special_functions/bernstein.lean


Modified src/analysis/specific_limits/normed.lean




## [2022-06-22 13:46:51](https://github.com/leanprover-community/mathlib/commit/d939b0e)
feat(topology/vector_bundle/hom): define the vector bundle of continuous linear maps ([#14541](https://github.com/leanprover-community/mathlib/pull/14541))
* The changes in `topology/fiber_bundle` are not necessary for this PR, but perhaps nice additions
* Co-authored by: Heather Macbeth <25316162+hrmacbeth@users.noreply.github.com>
* Co-authored by: Patrick Massot <patrick.massot@u-psud.fr>
#### Estimated changes
Modified src/topology/fiber_bundle.lean
- \+ *lemma* topological_fiber_bundle.pretrivialization.symm_apply_apply
- \+ *lemma* topological_fiber_bundle.pretrivialization.target_inter_preimage_symm_source_eq
- \+ *lemma* topological_fiber_bundle.pretrivialization.trans_source
- \+ *lemma* topological_fiber_bundle.trivialization.continuous_at_of_comp_left
- \+ *lemma* topological_fiber_bundle.trivialization.continuous_at_of_comp_right
- \+ *lemma* topological_fiber_prebundle.continuous_on_of_comp_right

Modified src/topology/vector_bundle/basic.lean


Added src/topology/vector_bundle/hom.lean
- \+ *def* bundle.continuous_linear_map.topological_vector_prebundle
- \+ *def* bundle.continuous_linear_map
- \+ *def* topological_vector_bundle.pretrivialization.continuous_linear_map
- \+ *lemma* topological_vector_bundle.pretrivialization.continuous_linear_map_apply
- \+ *def* topological_vector_bundle.pretrivialization.continuous_linear_map_coord_change
- \+ *lemma* topological_vector_bundle.pretrivialization.continuous_linear_map_coord_change_apply
- \+ *lemma* topological_vector_bundle.pretrivialization.continuous_linear_map_symm_apply'
- \+ *lemma* topological_vector_bundle.pretrivialization.continuous_linear_map_symm_apply
- \+ *lemma* topological_vector_bundle.pretrivialization.continuous_on_continuous_linear_map_coord_change
- \+ *lemma* topological_vector_bundle.trivialization.base_set_continuous_linear_map
- \+ *def* topological_vector_bundle.trivialization.continuous_linear_map
- \+ *lemma* topological_vector_bundle.trivialization.continuous_linear_map_apply



## [2022-06-22 08:58:26](https://github.com/leanprover-community/mathlib/commit/ad49768)
feat(set_theory/surreal/basic): define map `surreal →+o game` ([#14783](https://github.com/leanprover-community/mathlib/pull/14783))
#### Estimated changes
Modified src/set_theory/surreal/basic.lean
- \+ *theorem* surreal.nat_to_game
- \+ *theorem* surreal.one_to_game
- \+ *def* surreal.to_game
- \+ *theorem* surreal.zero_to_game



## [2022-06-22 04:11:06](https://github.com/leanprover-community/mathlib/commit/61b837f)
feat(combinatorics/simple_graph/connectivity): Connectivity is a graph property ([#14865](https://github.com/leanprover-community/mathlib/pull/14865))
`simple_graph.preconnected` and `simple_graph.connected` are preserved under graph isomorphisms.
#### Estimated changes
Modified src/combinatorics/simple_graph/connectivity.lean
- \+ *lemma* simple_graph.connected.map
- \+ *lemma* simple_graph.iso.connected_iff
- \+ *lemma* simple_graph.iso.preconnected_iff
- \+ *lemma* simple_graph.preconnected.map



## [2022-06-22 02:09:00](https://github.com/leanprover-community/mathlib/commit/f3cd150)
fix(tactic/apply_fun.lean): instantiate mvars in apply_fun ([#14882](https://github.com/leanprover-community/mathlib/pull/14882))
Fixes leanprover-community/lean[#733](https://github.com/leanprover-community/mathlib/pull/733)
#### Estimated changes
Modified src/tactic/apply_fun.lean


Modified test/apply_fun.lean




## [2022-06-21 16:31:41](https://github.com/leanprover-community/mathlib/commit/3b6552e)
chore(linear_algebra/alternating): more lemmas about `curry_left` ([#14844](https://github.com/leanprover-community/mathlib/pull/14844))
This follows on from [#14802](https://github.com/leanprover-community/mathlib/pull/14802)
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *lemma* alternating_map.curry_left_add
- \+ *lemma* alternating_map.curry_left_comp_alternating_map
- \+ *lemma* alternating_map.curry_left_comp_linear_map
- \+ *lemma* alternating_map.curry_left_smul
- \+ *lemma* alternating_map.curry_left_zero

Modified src/linear_algebra/exterior_algebra/basic.lean
- \+ *lemma* exterior_algebra.ι_multi_succ_apply
- \+ *lemma* exterior_algebra.ι_multi_succ_curry_left
- \+ *lemma* exterior_algebra.ι_multi_zero_apply



## [2022-06-21 16:31:40](https://github.com/leanprover-community/mathlib/commit/d953773)
feat(data/finsupp/basic): make `prod_add_index_of_disjoint` to_additive ([#14786](https://github.com/leanprover-community/mathlib/pull/14786))
Adds lemma `sum_add_index_of_disjoint (h : disjoint f1.support f2.support) (g : α → M → β) : (f1 + f2).sum g = f1.sum g + f2.sum g`
#### Estimated changes
Modified src/data/finsupp/basic.lean




## [2022-06-21 16:31:39](https://github.com/leanprover-community/mathlib/commit/3e66afe)
feat(data/sigma): add reflected instance ([#14764](https://github.com/leanprover-community/mathlib/pull/14764))
#### Estimated changes
Modified src/data/sigma/basic.lean




## [2022-06-21 16:31:38](https://github.com/leanprover-community/mathlib/commit/b779513)
feat(order/conditionally_complete_lattice): add `cInf_le_cInf'` ([#14719](https://github.com/leanprover-community/mathlib/pull/14719))
A version of `cInf_le_cInf` for `conditionally_complete_linear_order_bot`
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* cInf_le_cInf'



## [2022-06-21 14:57:41](https://github.com/leanprover-community/mathlib/commit/2d70b94)
golf(data/polynomial): factorization into linear factors when #roots=degree  ([#14862](https://github.com/leanprover-community/mathlib/pull/14862))
+ Golf the proofs of `prod_multiset_X_sub_C_of_monic_of_roots_card_eq` and `C_leading_coeff_mul_prod_multiset_X_sub_C` and move them from *splitting_field.lean* to *ring_division.lean*; instead of using the former to deduce the latter as is currently done in mathlib, we prove the latter first and deduce the former easily. Remove the less general auxiliary, `private` `_of_field` versions.
+ Move `pairwise_coprime_X_sub` from *field_division.lean* to *ring_division.lean*. Rename it to `pairwise_coprime_X_sub_C` to conform with existing convention. Golf its proof using the more general new lemma `is_coprime_X_sub_C_of_is_unit_sub`.
+ Golf `monic.irreducible_of_irreducible_map`, but it's essentially the same proof.
#### Estimated changes
Modified src/data/polynomial/field_division.lean
- \- *theorem* polynomial.pairwise_coprime_X_sub

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.C_leading_coeff_mul_prod_multiset_X_sub_C
- \+ *lemma* polynomial.is_coprime_X_sub_C_of_is_unit_sub
- \+ *theorem* polynomial.pairwise_coprime_X_sub_C
- \+ *lemma* polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq

Modified src/field_theory/fixed.lean


Modified src/field_theory/separable.lean


Modified src/field_theory/splitting_field.lean
- \- *lemma* polynomial.C_leading_coeff_mul_prod_multiset_X_sub_C
- \- *lemma* polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq



## [2022-06-21 14:57:40](https://github.com/leanprover-community/mathlib/commit/ee12362)
feat(topology/metric_space/basic): Add `ball_comm` lemmas ([#14858](https://github.com/leanprover-community/mathlib/pull/14858))
This adds `closed_ball` and `sphere` comm lemmas to go with the existing `mem_ball_comm`.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* metric.mem_ball'
- \+/\- *theorem* metric.mem_closed_ball'
- \+ *theorem* metric.mem_closed_ball_comm
- \+ *theorem* metric.mem_sphere'
- \+ *theorem* metric.mem_sphere_comm

Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* emetric.mem_ball'
- \+ *theorem* emetric.mem_closed_ball'
- \+ *theorem* emetric.mem_closed_ball_comm



## [2022-06-21 13:23:46](https://github.com/leanprover-community/mathlib/commit/2b5a577)
doc(data/polynomial/div): fix runaway code block ([#14864](https://github.com/leanprover-community/mathlib/pull/14864))
Also use a fully-qualilfied name for linking
#### Estimated changes
Modified src/data/polynomial/div.lean




## [2022-06-21 13:23:45](https://github.com/leanprover-community/mathlib/commit/65031ca)
feat(ring_theory/dedekind_domain/ideal): drop an unneeded assumption ([#14444](https://github.com/leanprover-community/mathlib/pull/14444))
#### Estimated changes
Modified src/ring_theory/dedekind_domain/ideal.lean
- \+/\- *lemma* ideal.count_normalized_factors_eq
- \+ *theorem* ideal.is_prime_iff_bot_or_prime

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* unique_factorization_monoid.count_normalized_factors_eq'



## [2022-06-21 11:26:39](https://github.com/leanprover-community/mathlib/commit/273986a)
fix(topology/algebra/group_completion): add lemmas about nsmul and zsmul and fix diamonds ([#14846](https://github.com/leanprover-community/mathlib/pull/14846))
This prevents a diamond forming between `uniform_space.completion.has_scalar` and the default `add_monoid.nsmul` and `sub_neg_monoid.zsmul` fields; by manually defining the latter to match the former.
To do this, we add two new instances of `has_uniform_continuous_smul` for nat- and int- actions.
To use the existing scalar actions, we had to shuffle the imports around a bit.
#### Estimated changes
Modified src/analysis/normed_space/completion.lean


Modified src/topology/algebra/group_completion.lean


Modified src/topology/algebra/uniform_group.lean
- \+ *lemma* uniform_continuous.pow_const
- \+ *lemma* uniform_continuous.zpow_const
- \+ *lemma* uniform_continuous_pow_const
- \+ *lemma* uniform_continuous_zpow_const

Modified src/topology/algebra/uniform_mul_action.lean




## [2022-06-21 11:26:38](https://github.com/leanprover-community/mathlib/commit/2a7bde0)
feat(data{finset,set}/pointwise): Pointwise monoids are domains ([#14687](https://github.com/leanprover-community/mathlib/pull/14687))
`no_zero_divisors`/`no_zero_smul_divisors` instances for `set` and `finset`.
#### Estimated changes
Modified src/algebra/module/basic.lean


Modified src/data/finset/pointwise.lean


Modified src/data/set/pointwise.lean




## [2022-06-21 09:14:05](https://github.com/leanprover-community/mathlib/commit/481f991)
refactor(algebra/{hom/equiv, ring/equiv}): rename `equiv_of_unique_of_unique` to `equiv_of_unique` ([#14861](https://github.com/leanprover-community/mathlib/pull/14861))
This matches [`equiv.equiv_of_unique`](https://leanprover-community.github.io/mathlib_docs/logic/equiv/basic.html#equiv.equiv_of_unique).
#### Estimated changes
Modified src/algebra/hom/equiv.lean
- \+ *def* mul_equiv.mul_equiv_of_unique
- \- *def* mul_equiv.mul_equiv_of_unique_of_unique

Modified src/algebra/ring/equiv.lean
- \+ *def* ring_equiv.ring_equiv_of_unique
- \- *def* ring_equiv.ring_equiv_of_unique_of_unique



## [2022-06-21 07:18:59](https://github.com/leanprover-community/mathlib/commit/e1d7cc7)
chore(set_theory/game/*): create `pgame` and `natural_ops` locales ([#14856](https://github.com/leanprover-community/mathlib/pull/14856))
#### Estimated changes
Modified src/set_theory/game/basic.lean


Modified src/set_theory/game/birthday.lean


Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/ordinal.lean


Modified src/set_theory/game/pgame.lean


Modified src/set_theory/game/short.lean


Modified src/set_theory/ordinal/natural_ops.lean




## [2022-06-21 07:18:57](https://github.com/leanprover-community/mathlib/commit/67e026c)
fix(tactic/norm_num): fix bad proof / bad test ([#14852](https://github.com/leanprover-community/mathlib/pull/14852))
This is a bug in master but it was first noticed in [#14683](https://github.com/leanprover-community/mathlib/pull/14683).
#### Estimated changes
Modified src/tactic/norm_num.lean


Modified test/norm_num.lean




## [2022-06-21 05:57:01](https://github.com/leanprover-community/mathlib/commit/8ac19d3)
chore(data/finsupp/fin): fix spacing ([#14860](https://github.com/leanprover-community/mathlib/pull/14860))
#### Estimated changes
Modified src/data/finsupp/fin.lean




## [2022-06-21 04:38:57](https://github.com/leanprover-community/mathlib/commit/326465d)
chore(set_theory/ordinal/natural_ops): use derive ([#14859](https://github.com/leanprover-community/mathlib/pull/14859))
#### Estimated changes
Modified src/set_theory/ordinal/natural_ops.lean




## [2022-06-21 01:37:43](https://github.com/leanprover-community/mathlib/commit/3b5441c)
feat(data/fintype/basic): equivalence between `finset α` and `set α` for `fintype α` ([#14840](https://github.com/leanprover-community/mathlib/pull/14840))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* finset.to_finset_coe
- \+ *lemma* fintype.finset_equiv_set_apply
- \+ *lemma* fintype.finset_equiv_set_symm_apply



## [2022-06-21 00:01:30](https://github.com/leanprover-community/mathlib/commit/87f4758)
feat(polynomial/ring_division): strengthen/generalize various lemmas ([#14839](https://github.com/leanprover-community/mathlib/pull/14839))
+ Generalize the assumption `function.injective f` in `le_root_multiplicity_map` to `map f p ≠ 0`. Strictly speaking this is not a generalization because the trivial case `p = 0` is excluded. If one do want to apply the lemma without assuming `p ≠ 0`, they can use the newly introduced `eq_root_multiplicity_map`, which is a strengthening of the original lemma (with the same hypothesis `function.injective f`).
+ Extract some common `variables` from four lemmas.
+ Generalize `eq_of_monic_of_dvd_of_nat_degree_le` to `eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le`: if a polynomial `q` is divisible by a monic polynomial `p` and has degree no greater than `p`, then `q = p`. Also remove the `is_domain` hypothesis and golf the proof.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/multiplicity.20of.20root.20in.20extension.20field/near/286736361)
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* polynomial.count_map_roots
- \+ *lemma* polynomial.eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le
- \+/\- *lemma* polynomial.eq_of_monic_of_dvd_of_nat_degree_le
- \+ *lemma* polynomial.eq_root_multiplicity_map
- \+/\- *lemma* polynomial.le_root_multiplicity_map
- \+/\- *lemma* polynomial.roots_map_of_injective_card_eq_total_degree



## [2022-06-20 22:02:23](https://github.com/leanprover-community/mathlib/commit/125055b)
refactor(data/sym/basic): change notation for sym.cons ([#14853](https://github.com/leanprover-community/mathlib/pull/14853))
Switch from `::` to `::ₛ` for `sym.cons` so that it no longer conflicts with `list.cons`. This (finally) puts it in line with other notations, like `::ₘ` for `multiset.cons`.
#### Estimated changes
Modified src/data/sym/basic.lean
- \+/\- *lemma* sym.coe_cons
- \+/\- *lemma* sym.cons_inj_left
- \+/\- *lemma* sym.cons_inj_right
- \+/\- *lemma* sym.cons_of_coe_eq
- \+/\- *lemma* sym.cons_swap
- \+/\- *lemma* sym.exists_eq_cons_of_succ
- \+/\- *lemma* sym.mem_cons
- \+/\- *lemma* sym.mem_cons_of_mem
- \+/\- *lemma* sym.mem_cons_self
- \+/\- *lemma* sym.repeat_succ



## [2022-06-20 16:13:29](https://github.com/leanprover-community/mathlib/commit/9df2762)
chore(data/nat/totient): golf a proof ([#14851](https://github.com/leanprover-community/mathlib/pull/14851))
#### Estimated changes
Modified src/data/nat/totient.lean
- \+/\- *lemma* zmod.card_units_eq_totient



## [2022-06-20 13:49:56](https://github.com/leanprover-community/mathlib/commit/f855a4b)
feat(order/monotone): Monotonicity of `prod.map` ([#14843](https://github.com/leanprover-community/mathlib/pull/14843))
If `f` and `g` are monotone/antitone, then `prod.map f g` is as well.
#### Estimated changes
Modified src/order/monotone.lean
- \+ *lemma* antitone.imp
- \+ *lemma* antitone.prod_map
- \+ *lemma* monotone.imp
- \+ *lemma* monotone.prod_map
- \+/\- *lemma* monotone_fst
- \+/\- *lemma* monotone_snd
- \+ *lemma* strict_anti.imp
- \+ *lemma* strict_anti.prod_map
- \+ *lemma* strict_mono.imp
- \+ *lemma* strict_mono.prod_map



## [2022-06-20 13:49:55](https://github.com/leanprover-community/mathlib/commit/66d3f89)
feat(logic/unique): functions from a `unique` type is `const` ([#14823](https://github.com/leanprover-community/mathlib/pull/14823))
+ A function `f` from a `unique` type is equal to the constant function with value `f default`, and the analogous heq version for dependent functions.
+ Also changes `Π a : α, Sort v` in the file to `α → Sort v`.
Inspired by https://github.com/leanprover-community/mathlib/pull/14724#discussion_r900542203
#### Estimated changes
Modified src/logic/unique.lean
- \+ *lemma* eq_const_of_unique
- \+ *lemma* heq_const_of_unique
- \+/\- *lemma* pi.default_apply
- \+/\- *lemma* pi.default_def



## [2022-06-20 13:49:54](https://github.com/leanprover-community/mathlib/commit/0b806ba)
docs(linear_algebra): refer to `pi.basis_fun` in `pi.basis` ([#14505](https://github.com/leanprover-community/mathlib/pull/14505))
This is a common question so the more ways we can point to the standard basis, the better!
See also Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Standard.20basis
#### Estimated changes
Modified src/linear_algebra/std_basis.lean




## [2022-06-20 11:25:39](https://github.com/leanprover-community/mathlib/commit/c781c0e)
feat(data/prod/basic): Involutivity of `prod.map` ([#14845](https://github.com/leanprover-community/mathlib/pull/14845))
If `f` and `g` are involutive, then so is `prod.map f g`.
#### Estimated changes
Modified src/data/prod/basic.lean
- \+ *lemma* function.bijective.prod_map
- \+/\- *lemma* function.injective.prod_map
- \+ *lemma* function.involutive.prod_map
- \+ *lemma* function.left_inverse.prod_map
- \+ *lemma* function.right_inverse.prod_map
- \+/\- *lemma* function.surjective.prod_map



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
Modified src/linear_algebra/clifford_algebra/basic.lean
- \- *def* clifford_algebra.as_exterior

Modified src/linear_algebra/exterior_algebra/basic.lean
- \- *inductive* exterior_algebra.rel
- \+/\- *def* exterior_algebra.ι
- \+/\- *def* exterior_algebra

Modified src/linear_algebra/exterior_algebra/grading.lean


Modified test/free_algebra.lean




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
Modified src/data/dfinsupp/basic.lean
- \+ *lemma* dfinsupp.comap_domain'_single
- \+ *lemma* dfinsupp.comap_domain_single
- \+ *lemma* dfinsupp.extend_with_single_zero
- \+ *lemma* dfinsupp.extend_with_zero
- \+ *lemma* dfinsupp.sigma_curry_single
- \+ *lemma* dfinsupp.sigma_uncurry_single



## [2022-06-20 11:25:36](https://github.com/leanprover-community/mathlib/commit/c5e13ba)
feat(algebra/order/pointwise): Supremum of pointwise operations ([#13669](https://github.com/leanprover-community/mathlib/pull/13669))
Pointwise operations of sets distribute over the (conditional) supremum/infimum.
#### Estimated changes
Modified src/algebra/order/pointwise.lean
- \+ *lemma* Inf_div
- \+ *lemma* Inf_inv
- \+ *lemma* Inf_mul
- \+ *lemma* Inf_one
- \+ *lemma* Sup_div
- \+ *lemma* Sup_inv
- \+ *lemma* Sup_mul
- \+ *lemma* Sup_one
- \+ *lemma* cInf_div
- \+ *lemma* cInf_inv
- \+ *lemma* cInf_mul
- \+ *lemma* cInf_one
- \+ *lemma* cSup_div
- \+ *lemma* cSup_inv
- \+ *lemma* cSup_mul
- \+ *lemma* cSup_one



## [2022-06-20 09:15:57](https://github.com/leanprover-community/mathlib/commit/f9c339e)
feat(group_theory/group_action/sigma): Scalar action on a sigma type ([#14825](https://github.com/leanprover-community/mathlib/pull/14825))
`(Π i, has_scalar α (β i)) → has_scalar α (Σ i, β i)` and similar.
#### Estimated changes
Modified src/group_theory/group_action/pi.lean


Modified src/group_theory/group_action/prod.lean


Added src/group_theory/group_action/sigma.lean
- \+ *lemma* sigma.smul_def
- \+ *lemma* sigma.smul_mk

Modified src/group_theory/group_action/sum.lean




## [2022-06-20 09:15:55](https://github.com/leanprover-community/mathlib/commit/ff40b2c)
chore(algebra/group/basic): lemmas about `bit0`, `bit1`, and addition ([#14798](https://github.com/leanprover-community/mathlib/pull/14798))
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* bit0_add
- \+ *lemma* bit0_sub
- \+ *lemma* bit1_add'
- \+ *lemma* bit1_add
- \+ *lemma* bit1_sub

Modified src/data/nat/basic.lean
- \+ *theorem* nat.bit_add'
- \+ *theorem* nat.bit_add



## [2022-06-20 09:15:53](https://github.com/leanprover-community/mathlib/commit/df50b88)
feat(order/filter/bases): basis for directed (b)infi of filters ([#14775](https://github.com/leanprover-community/mathlib/pull/14775))
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis_binfi_of_directed'
- \+ *lemma* filter.has_basis_binfi_of_directed
- \+ *lemma* filter.has_basis_infi_of_directed'
- \+ *lemma* filter.has_basis_infi_of_directed



## [2022-06-20 09:15:51](https://github.com/leanprover-community/mathlib/commit/2604c04)
feat(number_theory/number_field): add definitions and results about embeddings  ([#14749](https://github.com/leanprover-community/mathlib/pull/14749))
We consider the embeddings of a number field into an algebraic closed field (of char. 0) and prove some results about those. 
We also prove the ```number_field``` instance  for ```adjoint_root``` of an irreducible polynomial of `ℚ[X]`. 
From flt-regular
#### Estimated changes
Modified src/number_theory/number_field.lean
- \+ *lemma* number_field.embeddings.card
- \+ *lemma* number_field.embeddings.eq_roots



## [2022-06-20 09:15:48](https://github.com/leanprover-community/mathlib/commit/8263a4b)
refactor(analysis/complex/upper_half_plane): move topology to a new file ([#14748](https://github.com/leanprover-community/mathlib/pull/14748))
Also add some instances and lemmas about topology on the upper half plane.
#### Estimated changes
Modified src/analysis/complex/upper_half_plane/basic.lean


Added src/analysis/complex/upper_half_plane/topology.lean
- \+ *lemma* upper_half_plane.continuous_coe
- \+ *lemma* upper_half_plane.continuous_im
- \+ *lemma* upper_half_plane.continuous_re
- \+ *lemma* upper_half_plane.embedding_coe
- \+ *lemma* upper_half_plane.open_embedding_coe



## [2022-06-20 09:15:46](https://github.com/leanprover-community/mathlib/commit/804afcb)
feat(geometry/manifold/diffeomorph): some additions needed for smooth vector bundles ([#14738](https://github.com/leanprover-community/mathlib/pull/14738))
* Define `diffeomorph.prod_comm`, `diffeomorph.prod_congr`, `diffeomorph.prod_assoc`
* Prove `cont_mdiff_on.comp_cont_mdiff`
* In `fiber_bundle`, define some lemmas for `local_triv_at` that were already there for `local_triv`
* Yes, this PR does a couple different things, but it is still very small
* This is part of [#14412](https://github.com/leanprover-community/mathlib/pull/14412)
#### Estimated changes
Modified src/geometry/manifold/cont_mdiff.lean
- \+ *lemma* cont_mdiff_on.comp_cont_mdiff
- \+ *lemma* smooth_on.comp_smooth

Modified src/geometry/manifold/diffeomorph.lean
- \+ *lemma* diffeomorph.coe_prod_comm
- \+ *lemma* diffeomorph.coe_prod_congr
- \+ *def* diffeomorph.prod_assoc
- \+ *def* diffeomorph.prod_comm
- \+ *lemma* diffeomorph.prod_comm_symm
- \+ *def* diffeomorph.prod_congr
- \+ *lemma* diffeomorph.prod_congr_symm

Modified src/topology/fiber_bundle.lean
- \+/\- *lemma* topological_fiber_bundle_core.local_triv_at_apply
- \+ *lemma* topological_fiber_bundle_core.local_triv_at_apply_mk
- \+ *lemma* topological_fiber_bundle_core.local_triv_symm_apply
- \- *lemma* topological_fiber_bundle_core.local_triv_symm_fst
- \+ *lemma* topological_fiber_bundle_core.mem_local_triv_at_source
- \+ *lemma* topological_fiber_bundle_core.mem_local_triv_at_target

Modified src/topology/vector_bundle/basic.lean
- \+/\- *lemma* topological_vector_bundle_core.local_triv_at_apply
- \+ *lemma* topological_vector_bundle_core.local_triv_at_apply_mk
- \+ *def* topological_vector_bundle_core.to_topological_fiber_bundle_core
- \- *def* topological_vector_bundle_core.to_topological_vector_bundle_core



## [2022-06-20 09:15:45](https://github.com/leanprover-community/mathlib/commit/04f4505)
feat(analysis/convex/join): Join of sets ([#14676](https://github.com/leanprover-community/mathlib/pull/14676))
Define the join of two sets as the union of all segments between them.
#### Estimated changes
Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/hull.lean
- \+ *lemma* convex_hull_convex_hull_union_left
- \+ *lemma* convex_hull_convex_hull_union_right
- \+ *lemma* convex_hull_pair
- \+/\- *lemma* convex_hull_singleton
- \+ *lemma* segment_subset_convex_hull

Added src/analysis/convex/join.lean
- \+ *lemma* convex_hull_insert
- \+ *lemma* convex_hull_union
- \+ *def* convex_join
- \+ *lemma* convex_join_Union_left
- \+ *lemma* convex_join_Union_right
- \+ *lemma* convex_join_assoc
- \+ *lemma* convex_join_assoc_aux
- \+ *lemma* convex_join_comm
- \+ *lemma* convex_join_convex_join_convex_join_comm
- \+ *lemma* convex_join_empty_left
- \+ *lemma* convex_join_empty_right
- \+ *lemma* convex_join_left_comm
- \+ *lemma* convex_join_mono
- \+ *lemma* convex_join_mono_left
- \+ *lemma* convex_join_mono_right
- \+ *lemma* convex_join_right_comm
- \+ *lemma* convex_join_segment_singleton
- \+ *lemma* convex_join_segments
- \+ *lemma* convex_join_singleton_left
- \+ *lemma* convex_join_singleton_right
- \+ *lemma* convex_join_singleton_segment
- \+ *lemma* convex_join_singletons
- \+ *lemma* convex_join_subset
- \+ *lemma* convex_join_subset_convex_hull
- \+ *lemma* convex_join_union_left
- \+ *lemma* convex_join_union_right
- \+ *lemma* mem_convex_join
- \+ *lemma* segment_subset_convex_join
- \+ *lemma* subset_convex_join_left
- \+ *lemma* subset_convex_join_right



## [2022-06-20 07:16:13](https://github.com/leanprover-community/mathlib/commit/2903674)
refactor(order/conditionally_complete_lattice): tweak `well_founded.conditionally_complete_linear_order_with_bot` ([#14706](https://github.com/leanprover-community/mathlib/pull/14706))
We change the `well_founded` assumption on `well_founded.conditionally_complete_linear_order_bot` to an equivalent but more convenient `is_well_order` typeclass assumption. As such, we place it in the `is_well_order` namespace.
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean


Modified src/order/well_founded.lean


Modified src/set_theory/cardinal/basic.lean


Modified src/set_theory/ordinal/basic.lean




## [2022-06-20 04:10:04](https://github.com/leanprover-community/mathlib/commit/ae5b695)
refactor(number_theory/cyclotomic/*): refactor the definition of is_cyclotomic_extension ([#14463](https://github.com/leanprover-community/mathlib/pull/14463))
We modify the definition of `is_cyclotomic_extension`, requiring the existence of a primitive root of unity rather than a root of the cyclotomic polynomial. This removes almost all the `ne_zero` assumptions.
#### Estimated changes
Modified src/algebra/char_p/basic.lean
- \+ *lemma* char_p.pow_prime_pow_mul_eq_one_iff

Modified src/algebra/ne_zero.lean
- \+ *lemma* ne_zero.nat_of_ne_zero

Modified src/number_theory/cyclotomic/basic.lean
- \+/\- *lemma* is_alg_closed.is_cyclotomic_extension
- \+/\- *lemma* is_cyclotomic_extension.adjoin_primitive_root_eq_top
- \+/\- *lemma* is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic
- \+ *lemma* is_cyclotomic_extension.ne_zero'
- \+ *lemma* is_cyclotomic_extension.ne_zero
- \+ *lemma* is_cyclotomic_extension.subsingleton_iff
- \+/\- *lemma* is_cyclotomic_extension.trans
- \+/\- *lemma* is_primitive_root.adjoin_is_cyclotomic_extension

Modified src/number_theory/cyclotomic/discriminant.lean


Modified src/number_theory/cyclotomic/gal.lean
- \+/\- *lemma* is_cyclotomic_extension.from_zeta_aut_spec

Modified src/number_theory/cyclotomic/primitive_roots.lean
- \+ *lemma* is_cyclotomic_extension.aeval_zeta
- \+/\- *lemma* is_cyclotomic_extension.finrank
- \+/\- *lemma* is_cyclotomic_extension.prime_ne_two_norm_zeta_sub_one
- \+/\- *lemma* is_cyclotomic_extension.prime_ne_two_pow_norm_zeta_pow_sub_one
- \+/\- *lemma* is_cyclotomic_extension.prime_ne_two_pow_norm_zeta_sub_one
- \+/\- *lemma* is_cyclotomic_extension.two_pow_norm_zeta_sub_one
- \+ *lemma* is_cyclotomic_extension.zeta_is_root
- \- *lemma* is_cyclotomic_extension.zeta_primitive_root
- \- *lemma* is_cyclotomic_extension.zeta_spec'
- \+/\- *lemma* is_cyclotomic_extension.zeta_spec
- \+/\- *lemma* is_primitive_root.minpoly_sub_one_eq_cyclotomic_comp
- \+/\- *lemma* is_primitive_root.pow_sub_one_norm_prime_ne_two
- \+/\- *lemma* is_primitive_root.pow_sub_one_norm_prime_pow_ne_two
- \+/\- *lemma* is_primitive_root.pow_sub_one_norm_prime_pow_of_one_le
- \+/\- *lemma* is_primitive_root.pow_sub_one_norm_two
- \+/\- *lemma* is_primitive_root.sub_one_norm_prime
- \+/\- *lemma* is_primitive_root.sub_one_norm_prime_ne_two
- \+/\- *lemma* is_primitive_root.sub_one_norm_two

Modified src/number_theory/cyclotomic/rat.lean


Modified src/ring_theory/polynomial/cyclotomic/eval.lean
- \+/\- *lemma* polynomial.eval_one_cyclotomic_not_prime_pow

Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* is_primitive_root.ne_zero'
- \+ *lemma* mem_roots_of_unity'
- \+ *lemma* mem_roots_of_unity_prime_pow_mul_iff



## [2022-06-20 00:03:55](https://github.com/leanprover-community/mathlib/commit/10a5275)
feat(analysis/normed/group/basic): `isometry.norm_map_of_map_zero` ([#14836](https://github.com/leanprover-community/mathlib/pull/14836))
Add the lemma that an isometry of `semi_normed_group`s that preserves
0 preserves the norm.
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *lemma* isometry.norm_map_of_map_zero



## [2022-06-19 23:24:05](https://github.com/leanprover-community/mathlib/commit/cf118ee)
feat(analysis/complex/upper_half_plane): add `upper_half_plane.mk` ([#14795](https://github.com/leanprover-community/mathlib/pull/14795))
#### Estimated changes
Modified src/analysis/complex/upper_half_plane/basic.lean
- \+ *lemma* upper_half_plane.coe_mk
- \+ *def* upper_half_plane.mk
- \+ *lemma* upper_half_plane.mk_coe
- \+ *lemma* upper_half_plane.mk_im
- \+ *lemma* upper_half_plane.mk_re
- \+ *lemma* upper_half_plane.re_add_im



## [2022-06-19 17:24:08](https://github.com/leanprover-community/mathlib/commit/26279c5)
chore(algebraic_geometry/function_field): fix timeout in `function_field.algebra` ([#14830](https://github.com/leanprover-community/mathlib/pull/14830))
Reduces `elaboration of function_field.algebra` from ~29.3s to ~0.4s.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/deterministic.20timeout/near/286714162)
#### Estimated changes
Modified src/algebraic_geometry/function_field.lean




## [2022-06-19 16:13:12](https://github.com/leanprover-community/mathlib/commit/65c9ffb)
feat(topology/algebra/infinite_sum) Sums over Z vs sums over N ([#14667](https://github.com/leanprover-community/mathlib/pull/14667))
This PR adds some functions for handling infinite sums indexed by the integers, relating them to sums over the naturals.
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum.int_rec
- \+ *lemma* has_sum.nonneg_add_neg
- \+ *lemma* has_sum.pos_add_zero_add_neg
- \+ *lemma* has_sum.sum_nat_of_sum_int



## [2022-06-19 12:34:38](https://github.com/leanprover-community/mathlib/commit/f460576)
feat(group_theory/group_action/sum): Scalar action on a sum of types ([#14818](https://github.com/leanprover-community/mathlib/pull/14818))
`has_scalar α β → has_scalar α γ → has_scalar α (β ⊕ γ)` and similar.
#### Estimated changes
Added src/group_theory/group_action/sum.lean
- \+ *lemma* sum.smul_def
- \+ *lemma* sum.smul_inl
- \+ *lemma* sum.smul_inr
- \+ *lemma* sum.smul_swap



## [2022-06-19 09:55:31](https://github.com/leanprover-community/mathlib/commit/5dabef8)
feat(set_theory/game/basic): Basic lemmas on `inv` ([#13840](https://github.com/leanprover-community/mathlib/pull/13840))
Note that we've redefined `inv` so that `inv x = 0` when `x ≈ 0`. This is because, in order to lift it to an operation on surreals, we need to prove that equivalent numeric games give equivalent numeric values, and this isn't the case otherwise.
#### Estimated changes
Modified src/set_theory/game/basic.lean
- \+ *def* pgame.inv'_one
- \+ *theorem* pgame.inv'_one_equiv
- \+ *def* pgame.inv'_zero
- \+ *theorem* pgame.inv'_zero_equiv
- \+ *theorem* pgame.inv_eq_of_equiv_zero
- \+ *theorem* pgame.inv_eq_of_lf_zero
- \+ *theorem* pgame.inv_eq_of_pos
- \+ *def* pgame.inv_one
- \+ *theorem* pgame.inv_one_equiv
- \+ *theorem* pgame.inv_val_is_empty
- \+ *theorem* pgame.inv_zero
- \+ *theorem* pgame.zero_lf_inv'



## [2022-06-19 09:12:48](https://github.com/leanprover-community/mathlib/commit/69686e7)
feat(algebra/category/Module): Tannaka duality for rings ([#14352](https://github.com/leanprover-community/mathlib/pull/14352))
Obviously this is not the most interesting statement that one might label "Tannaka duality", but perhaps it can get the ball rolling. :-)
#### Estimated changes
Modified src/algebra/category/Module/basic.lean


Added src/algebra/category/Module/tannaka.lean
- \+ *def* ring_equiv_End_forget₂



## [2022-06-19 07:01:49](https://github.com/leanprover-community/mathlib/commit/7f358d0)
feat(category_theory/preadditive/eilenberg_moore): (Co)algebras over a (co)monad are preadditive ([#14811](https://github.com/leanprover-community/mathlib/pull/14811))
The category of algebras over an additive monad on a preadditive category is preadditive (and the dual result).
#### Estimated changes
Added src/category_theory/preadditive/eilenberg_moore.lean




## [2022-06-18 19:10:48](https://github.com/leanprover-community/mathlib/commit/0a5b9eb)
feat(set_theory/game/pgame): tweak lemmas ([#14810](https://github.com/leanprover-community/mathlib/pull/14810))
This PR does the following:
- uncurry `le_of_forall_lf` and `le_of_forall_lt`.
- remove `lf_of_exists_le`, as it's made redundant by `lf_of_move_right_le` and `lf_of_le_move_left`.
- golfing.
#### Estimated changes
Modified src/set_theory/game/ordinal.lean


Modified src/set_theory/game/pgame.lean
- \+/\- *theorem* pgame.le_of_forall_lf
- \+/\- *theorem* pgame.le_of_forall_lt
- \+/\- *theorem* pgame.lf_move_right_of_le
- \- *theorem* pgame.lf_of_exists_le
- \+/\- *theorem* pgame.lf_of_le_move_left
- \+/\- *theorem* pgame.lf_of_move_right_le
- \+/\- *theorem* pgame.move_left_lf_of_le

Modified src/set_theory/surreal/dyadic.lean




## [2022-06-18 16:59:43](https://github.com/leanprover-community/mathlib/commit/4264220)
feat(analysis/asymptotics): add several lemmas ([#14805](https://github.com/leanprover-community/mathlib/pull/14805))
Also make `𝕜` explicit in `asymptotics.is_O_with_const_one` and `asymptotics.is_O_const_one`.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotic_equivalent.lean
- \+ *lemma* asymptotics.is_o.add_is_equivalent

Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/asymptotics/theta.lean
- \+ *lemma* asymptotics.is_Theta.div
- \+ *lemma* asymptotics.is_Theta.trans_eventually_eq
- \+ *lemma* asymptotics.is_Theta_norm_left
- \+ *lemma* asymptotics.is_Theta_norm_right
- \+ *lemma* asymptotics.is_Theta_of_norm_eventually_eq'
- \+ *lemma* asymptotics.is_Theta_of_norm_eventually_eq
- \+/\- *lemma* asymptotics.is_Theta_refl
- \+ *lemma* asymptotics.is_Theta_rfl
- \+ *lemma* filter.eventually_eq.trans_is_Theta



## [2022-06-18 16:59:42](https://github.com/leanprover-community/mathlib/commit/100975e)
feat(geometry/euclidean/inversion) new file ([#14692](https://github.com/leanprover-community/mathlib/pull/14692))
* Define `euclidean_geometry.inversion`.
* Prove Ptolemy's inequality.
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* dist_div_norm_sq_smul

Added src/geometry/euclidean/inversion.lean
- \+ *lemma* euclidean_geometry.dist_center_inversion
- \+ *lemma* euclidean_geometry.dist_inversion_center
- \+ *lemma* euclidean_geometry.dist_inversion_inversion
- \+ *def* euclidean_geometry.inversion
- \+ *lemma* euclidean_geometry.inversion_bijective
- \+ *lemma* euclidean_geometry.inversion_dist_center
- \+ *lemma* euclidean_geometry.inversion_injective
- \+ *lemma* euclidean_geometry.inversion_inversion
- \+ *lemma* euclidean_geometry.inversion_involutive
- \+ *lemma* euclidean_geometry.inversion_of_mem_sphere
- \+ *lemma* euclidean_geometry.inversion_self
- \+ *lemma* euclidean_geometry.inversion_surjective
- \+ *lemma* euclidean_geometry.inversion_vsub_center
- \+ *lemma* euclidean_geometry.mul_dist_le_mul_dist_add_mul_dist



## [2022-06-18 16:59:41](https://github.com/leanprover-community/mathlib/commit/92d5fdf)
feat(topology/metric_space/baire): generalize some lemmas ([#14633](https://github.com/leanprover-community/mathlib/pull/14633))
Add `is_Gδ.dense_{s,b,}Union_interior_of_closed`.
#### Estimated changes
Modified src/topology/metric_space/baire.lean
- \+ *lemma* is_Gδ.dense_Union_interior_of_closed
- \+ *lemma* is_Gδ.dense_bUnion_interior_of_closed
- \+ *lemma* is_Gδ.dense_sUnion_interior_of_closed



## [2022-06-18 16:59:40](https://github.com/leanprover-community/mathlib/commit/f1b0402)
feat(tactic/core + test/list_summands): a function extracting a list of summands from an expression ([#14617](https://github.com/leanprover-community/mathlib/pull/14617))
This meta def is used in [#13483](https://github.com/leanprover-community/mathlib/pull/13483), where `move_add` is defined.
A big reason for splitting these 5 lines off the main PR is that they are not in a leaf of the import hierarchy: this hopefully saves lots of CI time, when doing trivial changes to the main PR.
#### Estimated changes
Modified src/tactic/core.lean


Added test/list_summands.lean




## [2022-06-18 15:26:18](https://github.com/leanprover-community/mathlib/commit/3a8e0a1)
feat(group_theory/torsion): define the p-primary component of a group ([#14312](https://github.com/leanprover-community/mathlib/pull/14312))
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* exists_order_of_eq_prime_pow_iff

Modified src/group_theory/torsion.lean
- \+ *lemma* comm_group.primary_component.is_p_group
- \+ *def* comm_group.primary_component
- \+ *def* comm_group.torsion
- \+ *lemma* comm_group.torsion_eq_torsion_submonoid
- \+ *lemma* comm_monoid.primary_component.disjoint
- \+ *lemma* comm_monoid.primary_component.exists_order_of_eq_prime_pow
- \+ *def* comm_monoid.primary_component
- \+/\- *lemma* is_torsion_free.quotient_torsion
- \- *def* torsion
- \- *lemma* torsion_eq_torsion_submonoid



## [2022-06-18 12:50:23](https://github.com/leanprover-community/mathlib/commit/3abee05)
chore(order/pfilter): more `principal` API ([#14759](https://github.com/leanprover-community/mathlib/pull/14759))
`principal` and `Inf` form a Galois coinsertion.
#### Estimated changes
Modified src/order/pfilter.lean
- \+ *lemma* order.pfilter.Inf_gc
- \+ *def* order.pfilter.Inf_gi
- \+ *lemma* order.pfilter.antitone_principal
- \+ *lemma* order.pfilter.mem_def
- \+ *lemma* order.pfilter.mem_principal
- \+ *lemma* order.pfilter.principal_le_principal_iff



## [2022-06-18 09:28:02](https://github.com/leanprover-community/mathlib/commit/39986ae)
chore(data/nat/lattice): add `nat.infi_of_empty` to match `_root_.infi_of_empty` ([#14797](https://github.com/leanprover-community/mathlib/pull/14797))
#### Estimated changes
Modified src/data/nat/lattice.lean
- \+ *lemma* nat.infi_of_empty



## [2022-06-18 08:28:16](https://github.com/leanprover-community/mathlib/commit/7fb5ed2)
feat(data/complex/basic): add `complex.abs_le_sqrt_two_mul_max` ([#14804](https://github.com/leanprover-community/mathlib/pull/14804))
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *lemma* complex.abs_le_sqrt_two_mul_max



## [2022-06-17 23:41:50](https://github.com/leanprover-community/mathlib/commit/bd6b98b)
feat(linear_algebra/alternating): add more compositional API ([#14802](https://github.com/leanprover-community/mathlib/pull/14802))
These will be helpful in relating `alternating_map`s to the `exterior_algebra`.
This adds:
* `alternating_map.curry_left`
* `alternating_map.const_linear_equiv_of_is_empty`
* `alternating_map.dom_dom_congr`
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+/\- *lemma* alternating_map.coe_dom_dom_congr
- \+ *def* alternating_map.const_linear_equiv_of_is_empty
- \+ *def* alternating_map.const_of_is_empty
- \+ *def* alternating_map.curry_left
- \+ *def* alternating_map.curry_left_linear_map
- \+ *lemma* alternating_map.curry_left_same
- \+ *def* alternating_map.dom_dom_congr
- \+ *lemma* alternating_map.dom_dom_congr_add
- \+ *lemma* alternating_map.dom_dom_congr_eq_iff
- \+ *lemma* alternating_map.dom_dom_congr_eq_zero_iff
- \+ *def* alternating_map.dom_dom_congr_equiv
- \+ *lemma* alternating_map.dom_dom_congr_perm
- \+ *lemma* alternating_map.dom_dom_congr_refl
- \+ *lemma* alternating_map.dom_dom_congr_trans
- \+ *lemma* alternating_map.dom_dom_congr_zero
- \+ *lemma* alternating_map.map_vec_cons_add
- \+ *lemma* alternating_map.map_vec_cons_smul
- \+/\- *def* alternating_map.of_subsingleton



## [2022-06-17 23:41:49](https://github.com/leanprover-community/mathlib/commit/0c47657)
chore(order/symm_diff): add lemma about `bxor` ([#14801](https://github.com/leanprover-community/mathlib/pull/14801))
#### Estimated changes
Modified src/order/boolean_algebra.lean
- \+ *lemma* bool.compl_eq_bnot
- \+ *lemma* bool.inf_eq_band
- \+ *lemma* bool.sup_eq_bor

Modified src/order/symm_diff.lean
- \+ *lemma* bool.symm_diff_eq_bxor



## [2022-06-17 22:43:38](https://github.com/leanprover-community/mathlib/commit/4ff9e93)
feat(analysis/complex/basic): add a few lemmas about `dist` on `complex` ([#14796](https://github.com/leanprover-community/mathlib/pull/14796))
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* complex.dist_eq_re_im
- \+ *lemma* complex.dist_mk
- \+ *lemma* complex.dist_of_im_eq
- \+ *lemma* complex.dist_of_re_eq
- \+ *lemma* complex.edist_of_im_eq
- \+ *lemma* complex.edist_of_re_eq
- \+ *lemma* complex.nndist_conj_self
- \+ *lemma* complex.nndist_of_im_eq
- \+ *lemma* complex.nndist_of_re_eq
- \+ *lemma* complex.nndist_self_conj



## [2022-06-17 20:37:43](https://github.com/leanprover-community/mathlib/commit/d2369bc)
feat(data/set/intervals): add two `ssubset` lemmas ([#14793](https://github.com/leanprover-community/mathlib/pull/14793))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Iio_ssubset_Iic_self
- \+ *lemma* set.Ioi_ssubset_Ici_self



## [2022-06-17 18:57:26](https://github.com/leanprover-community/mathlib/commit/e23de85)
feat(algebra/algebra/basic) : add ring_hom.equiv_rat_alg_hom ([#14772](https://github.com/leanprover-community/mathlib/pull/14772))
Proves the equivalence between `ring_hom` and `rat_alg_hom`.
From flt-regular
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_hom.to_ring_hom_to_rat_alg_hom
- \+ *def* ring_hom.equiv_rat_alg_hom
- \+ *lemma* ring_hom.to_rat_alg_hom_to_ring_hom



## [2022-06-17 17:39:07](https://github.com/leanprover-community/mathlib/commit/260d472)
feat(order/topology/**/uniform*): Lemmas about uniform convergence ([#14587](https://github.com/leanprover-community/mathlib/pull/14587))
To prove facts about uniform convergence, it is often useful to manipulate the various functions without dealing with the ε's and δ's. To do so, you need auxiliary lemmas about adding/muliplying/etc Cauchy sequences.
This commit adds several such lemmas. It supports [#14090](https://github.com/leanprover-community/mathlib/pull/14090), which we're slowly transforming to use these lemmas instead of doing direct ε/δ manipulation.
#### Estimated changes
Modified src/order/filter/bases.lean
- \- *lemma* filter.prod_assoc

Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually.diag_of_prod
- \+ *lemma* filter.map_swap4_eq_comap
- \+ *lemma* filter.map_swap4_prod
- \+ *lemma* filter.prod_assoc
- \+ *theorem* filter.prod_assoc_symm
- \+ *lemma* filter.tendsto_diag
- \+ *lemma* filter.tendsto_prod_assoc
- \+ *lemma* filter.tendsto_prod_assoc_symm
- \+ *lemma* filter.tendsto_prod_swap
- \+ *lemma* filter.tendsto_swap4_prod

Modified src/topology/algebra/uniform_group.lean
- \+ *lemma* tendsto_uniformly_on.div
- \+ *lemma* tendsto_uniformly_on.mul
- \+ *lemma* uniform_cauchy_seq_on.div
- \+ *lemma* uniform_cauchy_seq_on.mul

Modified src/topology/continuous_function/algebra.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* filter.tendsto.tendsto_uniformly_on_const
- \+ *lemma* tendsto_prod_principal_iff
- \- *lemma* tendsto_uniformly.comp'
- \- *lemma* tendsto_uniformly_on.comp'
- \+ *lemma* tendsto_uniformly_on.congr
- \+ *lemma* tendsto_uniformly_on_empty
- \+ *lemma* tendsto_uniformly_on_singleton_iff_tendsto
- \+ *lemma* uniform_cauchy_seq_on.comp
- \+ *lemma* uniform_cauchy_seq_on.mono
- \+ *lemma* uniform_cauchy_seq_on.prod'
- \+ *lemma* uniform_cauchy_seq_on.prod
- \+ *lemma* uniform_cauchy_seq_on.prod_map
- \+ *lemma* uniform_continuous.comp_tendsto_uniformly
- \+ *lemma* uniform_continuous.comp_tendsto_uniformly_on
- \+ *lemma* uniform_continuous.comp_uniform_cauchy_seq_on



## [2022-06-17 16:27:29](https://github.com/leanprover-community/mathlib/commit/545f0fb)
feat(category_theory/monad/kleisli): dualise kleisli of monad to cokleisli of comonad ([#14799](https://github.com/leanprover-community/mathlib/pull/14799))
This PR defines the (co)Kleisli category of a comonad, defines the corresponding adjunction, and proves that it gives rise to the original comonad.
#### Estimated changes
Modified src/category_theory/monad/kleisli.lean
- \+ *def* category_theory.cokleisli.adjunction.adj
- \+ *def* category_theory.cokleisli.adjunction.from_cokleisli
- \+ *def* category_theory.cokleisli.adjunction.to_cokleisli
- \+ *def* category_theory.cokleisli.adjunction.to_cokleisli_comp_from_cokleisli_iso_self
- \+ *def* category_theory.cokleisli



## [2022-06-17 15:08:42](https://github.com/leanprover-community/mathlib/commit/ade72ab)
refactor(linear_algebra/quadratic_form/basic): generalize to semiring ([#14303](https://github.com/leanprover-community/mathlib/pull/14303))
This uses a slightly nicer strategy than the one suggested by @adamtopaz [on Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Exterior.20algebras.20over.20semiring/near/282808284).
The main motivation here is to be able to talk about `0 : quadratic_form R M` even when there is no negation available, as that will let us merge `clifford_algebra`  (which currently requires negation) and `exterior_algebra` (which does not).
It's likely this generalization is broadly not very useful, so this adds a `quadratic_form.of_polar` constructor to preserve the old more convenient API.
Note the `.bib` file changed slightly as I ran the autoformatting tool.
#### Estimated changes
Modified docs/references.bib


Modified src/linear_algebra/quadratic_form/basic.lean
- \+/\- *lemma* quadratic_form.add_lin_mul_lin
- \+/\- *lemma* quadratic_form.basis_repr_eq_of_is_Ortho
- \+ *lemma* quadratic_form.exists_companion
- \+/\- *def* quadratic_form.lin_mul_lin
- \+/\- *lemma* quadratic_form.lin_mul_lin_add
- \+/\- *lemma* quadratic_form.lin_mul_lin_apply
- \+/\- *lemma* quadratic_form.lin_mul_lin_comp
- \+ *lemma* quadratic_form.map_add_add_add_map
- \+/\- *lemma* quadratic_form.map_smul_of_tower
- \+ *def* quadratic_form.of_polar
- \+ *lemma* quadratic_form.polar_add_left_iff
- \+ *def* quadratic_form.polar_bilin
- \+/\- *def* quadratic_form.proj
- \+/\- *lemma* quadratic_form.proj_apply
- \+ *lemma* quadratic_form.some_exists_companion
- \+/\- *def* quadratic_form.sq
- \+/\- *lemma* quadratic_form.to_fun_eq_coe
- \+/\- *def* quadratic_form.weighted_sum_squares
- \+/\- *structure* quadratic_form

Modified src/linear_algebra/quadratic_form/isometry.lean


Modified src/linear_algebra/quadratic_form/prod.lean




## [2022-06-17 13:35:37](https://github.com/leanprover-community/mathlib/commit/9c2b890)
feat(group_theory/sylow): API lemmas for smul and subtype  ([#14521](https://github.com/leanprover-community/mathlib/pull/14521))
This PR adds some API lemmas for smul and subtype.
#### Estimated changes
Modified src/group_theory/subgroup/pointwise.lean
- \+ *lemma* subgroup.conj_smul_le_of_le
- \+ *lemma* subgroup.conj_smul_subgroup_of

Modified src/group_theory/sylow.lean
- \+ *lemma* sylow.smul_le
- \+ *lemma* sylow.smul_subtype



## [2022-06-17 11:03:20](https://github.com/leanprover-community/mathlib/commit/0be36f6)
feat(data/list/of_fn): Add `list.of_fn_add` and `list.of_fn_mul` ([#14370](https://github.com/leanprover-community/mathlib/pull/14370))
This adds some lemmas to split up lists generated over `fin (n + m)` and `fin (n * m)` into their constituent parts.
It also adds a congr lemma to allow `list.of_fn (λ i : fin n, _)` to be rewritten into `list.of_fn (λ i : fin m, _)` by `simp` when `h : n = m` is available.
I'll need these eventually to prove some things about products of tensor powers.
#### Estimated changes
Modified src/data/list/join.lean
- \+ *lemma* list.join_concat

Modified src/data/list/of_fn.lean
- \+ *theorem* list.of_fn_add
- \+ *theorem* list.of_fn_congr
- \+ *theorem* list.of_fn_mul'
- \+ *theorem* list.of_fn_mul
- \+ *theorem* list.of_fn_succ'



## [2022-06-17 08:38:50](https://github.com/leanprover-community/mathlib/commit/e427a0e)
feat(set/basic, order/boolean_algebra): generalized `compl_comp_compl` ([#14784](https://github.com/leanprover-community/mathlib/pull/14784))
This PR generalizes `compl_comp_compl` to apply whenever there is a `boolean_algebra` instance. We also make the set parameter of `compl_compl_image` explicit.
#### Estimated changes
Modified src/data/set/basic.lean
- \- *theorem* set.compl_comp_compl
- \+/\- *theorem* set.compl_compl_image

Modified src/order/boolean_algebra.lean
- \+ *theorem* compl_comp_compl



## [2022-06-17 01:10:15](https://github.com/leanprover-community/mathlib/commit/d21469e)
feat(set_theory/ordinal/basic): improve docs on `lift`, add `simp` lemmas ([#14599](https://github.com/leanprover-community/mathlib/pull/14599))
This is pretty much the same thing as [#14596](https://github.com/leanprover-community/mathlib/pull/14596), just on `ordinal.lift` instead of `cardinal.lift`.
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean
- \+/\- *theorem* ordinal.lift_id'
- \+/\- *theorem* ordinal.lift_lift
- \+ *theorem* ordinal.lift_umax'
- \+/\- *theorem* ordinal.lift_umax
- \+ *theorem* ordinal.lift_uzero



## [2022-06-16 22:34:16](https://github.com/leanprover-community/mathlib/commit/d0b93fa)
feat(set_theory/{pgame, basic}): Notation for `relabelling`, golfing ([#14155](https://github.com/leanprover-community/mathlib/pull/14155))
We introduce the notation `≡r` for relabellings between two pre-games. We also golf many theorems on relabellings.
#### Estimated changes
Modified src/set_theory/game/basic.lean
- \+/\- *theorem* pgame.mul_zero_equiv
- \+/\- *def* pgame.mul_zero_relabelling
- \+/\- *theorem* pgame.zero_mul_equiv
- \+/\- *def* pgame.zero_mul_relabelling

Modified src/set_theory/game/birthday.lean
- \+/\- *theorem* pgame.relabelling.birthday_congr

Modified src/set_theory/game/impartial.lean
- \+/\- *theorem* pgame.impartial.impartial_congr

Modified src/set_theory/game/nim.lean
- \+/\- *def* pgame.nim.nim_zero_relabelling

Modified src/set_theory/game/pgame.lean
- \+/\- *def* pgame.add_assoc_relabelling
- \+/\- *def* pgame.add_comm_relabelling
- \+/\- *def* pgame.add_zero_relabelling
- \+/\- *theorem* pgame.equiv.is_empty
- \+/\- *def* pgame.neg_add_relabelling
- \+/\- *def* pgame.relabel
- \+/\- *def* pgame.relabelling.add_congr
- \+/\- *theorem* pgame.relabelling.equiv
- \+ *theorem* pgame.relabelling.ge
- \+/\- *def* pgame.relabelling.is_empty
- \+/\- *theorem* pgame.relabelling.le
- \+/\- *def* pgame.relabelling.neg_congr
- \+/\- *def* pgame.relabelling.refl
- \+/\- *def* pgame.relabelling.restricted
- \+/\- *def* pgame.relabelling.sub_congr
- \+/\- *def* pgame.relabelling.symm
- \+/\- *def* pgame.relabelling.trans
- \+ *def* pgame.restricted.trans
- \+/\- *def* pgame.zero_add_relabelling



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
Modified counterexamples/homogeneous_prime_not_prime.lean


Added src/algebra/direct_sum/decomposition.lean
- \+ *def* direct_sum.decompose
- \+ *lemma* direct_sum.decompose_add
- \+ *def* direct_sum.decompose_add_equiv
- \+ *lemma* direct_sum.decompose_coe
- \+ *def* direct_sum.decompose_linear_equiv
- \+ *lemma* direct_sum.decompose_neg
- \+ *lemma* direct_sum.decompose_of_mem
- \+ *lemma* direct_sum.decompose_of_mem_ne
- \+ *lemma* direct_sum.decompose_of_mem_same
- \+ *lemma* direct_sum.decompose_smul
- \+ *lemma* direct_sum.decompose_sub
- \+ *lemma* direct_sum.decompose_sum
- \+ *lemma* direct_sum.decompose_symm_add
- \+ *lemma* direct_sum.decompose_symm_neg
- \+ *lemma* direct_sum.decompose_symm_of
- \+ *lemma* direct_sum.decompose_symm_sub
- \+ *lemma* direct_sum.decompose_symm_sum
- \+ *lemma* direct_sum.decompose_symm_zero
- \+ *lemma* direct_sum.decompose_zero
- \+ *lemma* direct_sum.decomposition.decompose'_eq
- \+ *lemma* direct_sum.sum_support_decompose

Modified src/algebra/monoid_algebra/grading.lean


Modified src/algebraic_geometry/projective_spectrum/topology.lean


Modified src/ring_theory/graded_algebra/basic.lean
- \+ *def* direct_sum.decompose_alg_equiv
- \+ *lemma* direct_sum.decompose_mul
- \+ *lemma* direct_sum.decompose_one
- \+ *lemma* direct_sum.decompose_symm_mul
- \+ *lemma* direct_sum.decompose_symm_one
- \- *lemma* graded_algebra.decompose'_def
- \- *def* graded_algebra.decompose
- \- *lemma* graded_algebra.decompose_coe
- \- *lemma* graded_algebra.decompose_of_mem
- \- *lemma* graded_algebra.decompose_of_mem_ne
- \- *lemma* graded_algebra.decompose_of_mem_same
- \- *lemma* graded_algebra.decompose_symm_of
- \+/\- *lemma* graded_algebra.mem_support_iff
- \- *lemma* graded_algebra.sum_support_decompose
- \- *def* graded_algebra.support

Modified src/ring_theory/graded_algebra/homogeneous_ideal.lean


Modified src/ring_theory/graded_algebra/radical.lean




## [2022-06-16 19:20:24](https://github.com/leanprover-community/mathlib/commit/67da272)
feat(analysis/inner_product_space): Gram-Schmidt Basis ([#14514](https://github.com/leanprover-community/mathlib/pull/14514))
When the Gram-Schmidt procedure is given a basis, it produces a basis.
This pull request also refactors the lemma `gram_schmidt_span`. The new versions of the lemmas cover the span of `Iio`, the span of `Iic` and the span of the complete set of input vectors. I was also able to remove some type classes in the process.
#### Estimated changes
Modified src/analysis/inner_product_space/gram_schmidt_ortho.lean
- \+ *lemma* coe_gram_schmidt_basis
- \+ *lemma* gram_schmidt_linear_independent
- \+ *lemma* gram_schmidt_mem_span
- \+/\- *lemma* gram_schmidt_ne_zero
- \+/\- *lemma* gram_schmidt_ne_zero_coe
- \+/\- *lemma* gram_schmidt_normed_unit_length
- \+/\- *lemma* gram_schmidt_normed_unit_length_coe
- \+/\- *theorem* gram_schmidt_orthonormal
- \+ *lemma* gram_schmidt_triangular
- \+/\- *lemma* gram_schmidt_zero
- \+ *lemma* mem_span_gram_schmidt
- \+/\- *lemma* span_gram_schmidt
- \+ *lemma* span_gram_schmidt_Iic
- \+ *lemma* span_gram_schmidt_Iio
- \+ *lemma* span_gram_schmidt_normed
- \+ *lemma* span_gram_schmidt_normed_range

Modified src/linear_algebra/span.lean
- \+ *lemma* submodule.span_eq_span



## [2022-06-16 15:46:22](https://github.com/leanprover-community/mathlib/commit/988f160)
fix(data/rat/basic): Remove incorrect simp attribute ([#14765](https://github.com/leanprover-community/mathlib/pull/14765))
Remove simp attribute that breaks `field_simp`.
#### Estimated changes
Modified src/data/rat/basic.lean
- \+/\- *lemma* rat.coe_int_div_eq_mk



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
Modified src/linear_algebra/clifford_algebra/basic.lean


Added src/linear_algebra/clifford_algebra/fold.lean
- \+ *def* clifford_algebra.foldl
- \+ *lemma* clifford_algebra.foldl_algebra_map
- \+ *lemma* clifford_algebra.foldl_mul
- \+ *lemma* clifford_algebra.foldl_one
- \+ *lemma* clifford_algebra.foldl_prod_map_ι
- \+ *lemma* clifford_algebra.foldl_reverse
- \+ *lemma* clifford_algebra.foldl_ι
- \+ *def* clifford_algebra.foldr
- \+ *lemma* clifford_algebra.foldr_algebra_map
- \+ *lemma* clifford_algebra.foldr_mul
- \+ *lemma* clifford_algebra.foldr_one
- \+ *lemma* clifford_algebra.foldr_prod_map_ι
- \+ *lemma* clifford_algebra.foldr_reverse
- \+ *lemma* clifford_algebra.foldr_ι
- \+ *lemma* clifford_algebra.left_induction
- \+ *lemma* clifford_algebra.right_induction



## [2022-06-16 15:46:18](https://github.com/leanprover-community/mathlib/commit/7584a10)
feat(set_theory/game/ordinal): addition of ordinals on games matches natural addition ([#14298](https://github.com/leanprover-community/mathlib/pull/14298))
#### Estimated changes
Modified src/set_theory/game/birthday.lean


Modified src/set_theory/game/ordinal.lean
- \+ *theorem* ordinal.to_pgame_add
- \+ *theorem* ordinal.to_pgame_add_mk



## [2022-06-16 12:52:06](https://github.com/leanprover-community/mathlib/commit/b05d845)
feat(data/nat/basic): add a few lemmas ([#14718](https://github.com/leanprover-community/mathlib/pull/14718))
Add a few lemmas about sub and mod.
#### Estimated changes
Modified src/algebra/order/sub.lean
- \+ *lemma* tsub_lt_of_lt

Modified src/data/nat/basic.lean
- \+ *lemma* nat.mul_add_mod
- \+ *lemma* nat.mul_add_mod_of_lt
- \+ *lemma* nat.pred_eq_self_iff



## [2022-06-16 11:52:28](https://github.com/leanprover-community/mathlib/commit/3feb151)
feat(algebra/homology,category_theory/abelian): exact_comp_mono_iff ([#14410](https://github.com/leanprover-community/mathlib/pull/14410))
From LTE.
#### Estimated changes
Modified src/algebra/homology/exact.lean
- \+ *lemma* category_theory.exact_comp_mono_iff

Modified src/category_theory/abelian/exact.lean
- \+ *lemma* category_theory.abelian.exact_epi_comp_iff



## [2022-06-16 02:53:25](https://github.com/leanprover-community/mathlib/commit/6834a24)
feat(analysis/asymptotics): define `is_Theta` ([#14567](https://github.com/leanprover-community/mathlib/pull/14567))
* define `f =Θ[l] g` and prove basic properties;
* add `is_O.const_smul_left`, `is_o.const_smul_left`;
* rename `is_O_const_smul_left_iff` and `is_o_const_smul_left_iff` to
  `is_O_const_smul_left` and `is_o_const_smul_left`.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+ *lemma* asymptotics.is_O.const_smul_left
- \+ *theorem* asymptotics.is_O_const_smul_left
- \- *theorem* asymptotics.is_O_const_smul_left_iff
- \+ *lemma* asymptotics.is_o.const_smul_left
- \+/\- *theorem* asymptotics.is_o_const_smul_left
- \- *theorem* asymptotics.is_o_const_smul_left_iff

Added src/analysis/asymptotics/theta.lean
- \+ *lemma* asymptotics.is_O.antisymm
- \+ *lemma* asymptotics.is_O.trans_is_Theta
- \+ *lemma* asymptotics.is_Theta.eq_zero_iff
- \+ *lemma* asymptotics.is_Theta.inv
- \+ *lemma* asymptotics.is_Theta.is_O_congr_left
- \+ *lemma* asymptotics.is_Theta.is_O_congr_right
- \+ *lemma* asymptotics.is_Theta.is_bounded_under_le_iff
- \+ *lemma* asymptotics.is_Theta.is_o_congr_left
- \+ *lemma* asymptotics.is_Theta.is_o_congr_right
- \+ *lemma* asymptotics.is_Theta.mono
- \+ *lemma* asymptotics.is_Theta.mul
- \+ *lemma* asymptotics.is_Theta.pow
- \+ *lemma* asymptotics.is_Theta.smul
- \+ *lemma* asymptotics.is_Theta.sup
- \+ *lemma* asymptotics.is_Theta.symm
- \+ *lemma* asymptotics.is_Theta.tendsto_norm_at_top_iff
- \+ *lemma* asymptotics.is_Theta.tendsto_zero_iff
- \+ *lemma* asymptotics.is_Theta.trans
- \+ *lemma* asymptotics.is_Theta.trans_is_O
- \+ *lemma* asymptotics.is_Theta.trans_is_o
- \+ *lemma* asymptotics.is_Theta.zpow
- \+ *def* asymptotics.is_Theta
- \+ *lemma* asymptotics.is_Theta_comm
- \+ *lemma* asymptotics.is_Theta_const_const
- \+ *lemma* asymptotics.is_Theta_const_const_iff
- \+ *lemma* asymptotics.is_Theta_const_mul_left
- \+ *lemma* asymptotics.is_Theta_const_mul_right
- \+ *lemma* asymptotics.is_Theta_const_smul_left
- \+ *lemma* asymptotics.is_Theta_const_smul_right
- \+ *lemma* asymptotics.is_Theta_inv
- \+ *lemma* asymptotics.is_Theta_refl
- \+ *lemma* asymptotics.is_Theta_sup
- \+ *lemma* asymptotics.is_Theta_zero_left
- \+ *lemma* asymptotics.is_Theta_zero_right
- \+ *lemma* asymptotics.is_o.trans_is_Theta



## [2022-06-16 02:00:04](https://github.com/leanprover-community/mathlib/commit/0053e3c)
feat(analysis/special_functions/arsinh): add lemmas, review API ([#14668](https://github.com/leanprover-community/mathlib/pull/14668))
#### Estimated changes
Modified src/analysis/calculus/cont_diff.lean
- \+ *theorem* homeomorph.cont_diff_symm
- \+ *theorem* homeomorph.cont_diff_symm_deriv

Modified src/analysis/special_functions/arsinh.lean
- \+ *lemma* cont_diff.arsinh
- \+ *lemma* cont_diff_at.arsinh
- \+ *lemma* cont_diff_on.arsinh
- \+ *lemma* cont_diff_within_at.arsinh
- \+ *lemma* continuous.arsinh
- \+ *lemma* continuous_at.arsinh
- \+ *lemma* continuous_on.arsinh
- \+ *lemma* continuous_within_at.arsinh
- \+ *lemma* differentiable.arsinh
- \+ *lemma* differentiable_at.arsinh
- \+ *lemma* differentiable_on.arsinh
- \+ *lemma* differentiable_within_at.arsinh
- \+ *lemma* filter.tendsto.arsinh
- \+ *lemma* has_deriv_at.arsinh
- \+ *lemma* has_deriv_within_at.arsinh
- \+ *lemma* has_fderiv_at.arsinh
- \+ *lemma* has_fderiv_within_at.arsinh
- \+ *lemma* has_strict_deriv_at.arsinh
- \+ *lemma* has_strict_fderiv_at.arsinh
- \+ *lemma* real.arsinh_bijective
- \+ *lemma* real.arsinh_eq_zero_iff
- \+ *lemma* real.arsinh_inj
- \+ *lemma* real.arsinh_injective
- \+ *lemma* real.arsinh_le_arsinh
- \+ *lemma* real.arsinh_lt_arsinh
- \+ *lemma* real.arsinh_neg
- \+ *lemma* real.arsinh_neg_iff
- \+ *lemma* real.arsinh_nonneg_iff
- \+ *lemma* real.arsinh_nonpos_iff
- \+ *lemma* real.arsinh_pos_iff
- \+/\- *lemma* real.arsinh_sinh
- \+ *lemma* real.arsinh_strict_mono
- \+ *lemma* real.arsinh_surjective
- \+ *lemma* real.arsinh_zero
- \+ *lemma* real.cont_diff_arsinh
- \+ *lemma* real.continuous_arsinh
- \+ *lemma* real.cosh_arsinh
- \+ *lemma* real.differentiable_arsinh
- \+ *lemma* real.exp_arsinh
- \+ *lemma* real.has_deriv_at_arsinh
- \+ *lemma* real.has_strict_deriv_at_arsinh
- \+/\- *lemma* real.sinh_arsinh
- \+/\- *lemma* real.sinh_bijective
- \+ *def* real.sinh_equiv
- \+ *def* real.sinh_homeomorph
- \+ *def* real.sinh_order_iso
- \+/\- *lemma* real.sinh_surjective
- \- *lemma* real.sqrt_one_add_sinh_sq



## [2022-06-16 02:00:03](https://github.com/leanprover-community/mathlib/commit/22f3255)
refactor(set_theory/game/*): Delete `winner.lean` ([#14271](https://github.com/leanprover-community/mathlib/pull/14271))
The file `winner.lean` currently consists of one-line definitions and theorems, including aliases for basic inequalities. This PR removes the file, inlines all previous definitions and theorems, and golfs various proofs in the process.
#### Estimated changes
Modified src/set_theory/game/impartial.lean
- \+/\- *lemma* pgame.impartial.add_self
- \+ *lemma* pgame.impartial.equiv_iff_add_equiv_zero'
- \+ *lemma* pgame.impartial.equiv_iff_add_equiv_zero
- \- *lemma* pgame.impartial.equiv_iff_sum_first_loses
- \+ *lemma* pgame.impartial.equiv_or_fuzzy_zero
- \+ *lemma* pgame.impartial.equiv_zero_iff_ge
- \+ *lemma* pgame.impartial.equiv_zero_iff_le:
- \+ *lemma* pgame.impartial.exists_left_move_equiv_iff_fuzzy_zero
- \+ *lemma* pgame.impartial.exists_right_move_equiv_iff_fuzzy_zero
- \- *lemma* pgame.impartial.first_loses_symm'
- \- *lemma* pgame.impartial.first_loses_symm
- \- *lemma* pgame.impartial.first_wins_symm'
- \- *lemma* pgame.impartial.first_wins_symm
- \+ *lemma* pgame.impartial.forall_left_moves_fuzzy_iff_equiv_zero
- \+ *lemma* pgame.impartial.forall_right_moves_fuzzy_iff_equiv_zero
- \+ *lemma* pgame.impartial.fuzzy_zero_iff_gf
- \+ *lemma* pgame.impartial.fuzzy_zero_iff_lf
- \- *lemma* pgame.impartial.good_left_move_iff_first_wins
- \- *lemma* pgame.impartial.good_right_move_iff_first_wins
- \+ *lemma* pgame.impartial.mk_add_self
- \+ *lemma* pgame.impartial.mk_neg_equiv_self
- \- *lemma* pgame.impartial.no_good_left_moves_iff_first_loses
- \- *lemma* pgame.impartial.no_good_right_moves_iff_first_loses
- \+/\- *lemma* pgame.impartial.nonneg
- \+/\- *lemma* pgame.impartial.nonpos
- \+ *lemma* pgame.impartial.not_equiv_zero_iff
- \- *lemma* pgame.impartial.not_first_loses
- \- *lemma* pgame.impartial.not_first_wins
- \+ *lemma* pgame.impartial.not_fuzzy_zero_iff
- \- *lemma* pgame.impartial.winner_cases

Modified src/set_theory/game/nim.lean
- \+ *lemma* pgame.nim.add_equiv_zero_iff_eq
- \+ *lemma* pgame.nim.add_fuzzy_zero_iff_ne
- \+/\- *lemma* pgame.nim.non_zero_first_wins
- \- *lemma* pgame.nim.sum_first_loses_iff_eq
- \- *lemma* pgame.nim.sum_first_wins_iff_neq
- \- *lemma* pgame.nim.zero_first_loses

Deleted src/set_theory/game/winner.lean
- \- *def* pgame.first_loses
- \- *lemma* pgame.first_loses_is_zero
- \- *lemma* pgame.first_loses_of_equiv
- \- *lemma* pgame.first_loses_of_equiv_iff
- \- *def* pgame.first_wins
- \- *lemma* pgame.first_wins_of_equiv
- \- *lemma* pgame.first_wins_of_equiv_iff
- \- *def* pgame.left_wins
- \- *lemma* pgame.left_wins_of_equiv
- \- *lemma* pgame.left_wins_of_equiv_iff
- \- *lemma* pgame.not_first_loses_of_first_wins
- \- *lemma* pgame.not_first_wins_of_first_loses
- \- *theorem* pgame.one_left_wins
- \- *def* pgame.right_wins
- \- *lemma* pgame.right_wins_of_equiv
- \- *lemma* pgame.right_wins_of_equiv_iff
- \- *theorem* pgame.star_first_wins
- \- *lemma* pgame.winner_cases
- \- *theorem* pgame.zero_first_loses



## [2022-06-15 23:36:05](https://github.com/leanprover-community/mathlib/commit/f991b4d)
chore(*): Bump to Lean 3.43.0 ([#14684](https://github.com/leanprover-community/mathlib/pull/14684))
Most of the changes in this upgrade are a consequence of https://github.com/leanprover-community/lean/pull/675, which removed almost all of `init/data/set.lean` from lean core so it could be migrated to mathlib. Other relevant core changes are https://github.com/leanprover-community/lean/pull/714, which removed a few order decidability instances, and https://github.com/leanprover-community/lean/pull/711, which caused a docstring to be rejected.
#### Estimated changes
Modified leanpkg.toml


Modified src/algebra/lie/free.lean


Modified src/algebra/lie/ideal_operations.lean


Modified src/analysis/inner_product_space/projection.lean


Modified src/analysis/normed/group/quotient.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/combinatorics/set_family/compression/uv.lean


Modified src/data/bool/basic.lean


Modified src/data/set/basic.lean
- \- *lemma* set.compl_eq_compl
- \+ *def* set.image
- \+/\- *theorem* set.mem_powerset
- \+/\- *theorem* set.mem_powerset_iff
- \- *theorem* set.mem_set_of_eq
- \+ *def* set.powerset
- \+/\- *theorem* set.subset_of_mem_powerset

Modified src/data/set/functor.lean


Modified src/data/set/lattice.lean
- \+/\- *theorem* set.mem_sUnion
- \+ *def* set.sUnion

Modified src/field_theory/adjoin.lean


Modified src/field_theory/primitive_element.lean


Modified src/group_theory/nielsen_schreier.lean
- \+/\- *def* is_free_groupoid.spanning_tree.End_is_free

Modified src/group_theory/order_of_element.lean


Modified src/logic/equiv/set.lean


Modified src/measure_theory/constructions/borel_space.lean
- \+/\- *def* measurable_equiv.ereal_equiv_real

Modified src/measure_theory/covering/vitali.lean


Modified src/measure_theory/function/conditional_expectation.lean


Modified src/measure_theory/function/strongly_measurable.lean


Modified src/measure_theory/measure/ae_measurable.lean


Modified src/model_theory/semantics.lean
- \+ *lemma* first_order.language.mem_complete_theory

Modified src/model_theory/syntax.lean


Modified src/order/filter/basic.lean
- \+ *lemma* has_subset.subset.eventually_le
- \- *lemma* set.subset.eventually_le

Modified src/order/succ_pred/basic.lean


Modified src/ring_theory/local_properties.lean


Modified src/set_theory/zfc.lean


Modified src/tactic/core.lean


Modified src/tactic/localized.lean


Modified src/topology/basic.lean


Modified src/topology/omega_complete_partial_order.lean
- \+/\- *theorem* Scott.is_open_univ

Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/compact_convergence.lean


Modified test/back_chaining.lean


Modified test/rcases.lean




## [2022-06-15 21:34:32](https://github.com/leanprover-community/mathlib/commit/c81c6c9)
feat(data/polynomial/erase_lead): `lt_nat_degree_of_mem_erase_lead_support` ([#14745](https://github.com/leanprover-community/mathlib/pull/14745))
This PR adds a lemma `lt_nat_degree_of_mem_erase_lead_support` and adds term-mode proofs of a couple related lemmas.
#### Estimated changes
Modified src/data/polynomial/erase_lead.lean
- \+ *lemma* polynomial.lt_nat_degree_of_mem_erase_lead_support
- \+/\- *lemma* polynomial.nat_degree_not_mem_erase_lead_support



## [2022-06-15 21:34:31](https://github.com/leanprover-community/mathlib/commit/ea2dbcb)
feat(analysis/special_functions/integrals): Add integral_cpow ([#14491](https://github.com/leanprover-community/mathlib/pull/14491))
Also adds various helper lemmas.
The purpose of this commit is to provide a computed integral for the `cpow` function. The proof is functionally identical to that of `integral_rpow`, but places a different set of constraints on the various parameters due to different continuity constraints of the cpow function.
Some notes on future improvments:
  * The range of valid integration can be expanded using ae_covers a la [#14147](https://github.com/leanprover-community/mathlib/pull/14147)
  * We currently only contemplate a real argument. However, this should essentially work for any continuous path in the complex plane that avoids the negative real axis. That would require a lot more machinery, not currently in mathlib.
Despite these restrictions, why is this important? This, Abel summation, [#13500](https://github.com/leanprover-community/mathlib/pull/13500), and [#14090](https://github.com/leanprover-community/mathlib/pull/14090) are the key ingredients to bootstrapping Dirichlet series.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *theorem* has_strict_deriv_at.smul_const

Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* integral_cpow
- \+ *lemma* interval_integral.interval_integrable_cpow

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* continuous_on.cpow_const



## [2022-06-15 21:34:27](https://github.com/leanprover-community/mathlib/commit/7145043)
feat(algebra/group/pi): Technical casework lemma for when two binomials are equal to each other ([#14400](https://github.com/leanprover-community/mathlib/pull/14400))
This PR adds a technical casework lemma for when two binomials are equal to each other. It will be useful for irreducibility of x^n-x-1. If anyone can see how to golf the proof further, that would be appreciated!
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+ *lemma* pi.mul_single_mul_mul_single_eq_mul_single_mul_mul_single

Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.single_add_single_eq_single_add_single

Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.binomial_eq_binomial
- \+/\- *lemma* polynomial.monomial_left_inj
- \+/\- *lemma* polynomial.nat_cast_mul



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
Modified src/data/nat/factorization/basic.lean
- \- *lemma* nat.div_factorization_pos
- \- *lemma* nat.ne_dvd_factorization_div



## [2022-06-15 18:51:16](https://github.com/leanprover-community/mathlib/commit/a583244)
feat(representation_theory/Action): a few lemmas about the rigid structure of Action ([#14620](https://github.com/leanprover-community/mathlib/pull/14620))
#### Estimated changes
Modified src/representation_theory/Action.lean
- \+ *lemma* Action.left_dual_V
- \+ *lemma* Action.left_dual_ρ
- \+ *lemma* Action.right_dual_V
- \+ *lemma* Action.right_dual_ρ



## [2022-06-15 18:51:15](https://github.com/leanprover-community/mathlib/commit/c4ef20e)
feat(order/rel_classes): an irreflexive order on a subsingleton type is a well order ([#14601](https://github.com/leanprover-community/mathlib/pull/14601))
This generalizes a previously existing lemma that the empty relation on a subsingleton type is a well order.
#### Estimated changes
Modified src/order/rel_classes.lean
- \+ *lemma* empty_relation_apply
- \+ *lemma* eq_empty_relation
- \+ *lemma* not_rel
- \+ *theorem* subsingleton.is_well_order



## [2022-06-15 17:10:38](https://github.com/leanprover-community/mathlib/commit/94fa33b)
fix(tactic/congrm): support multiple binders ([#14753](https://github.com/leanprover-community/mathlib/pull/14753))
#### Estimated changes
Modified src/tactic/congrm.lean


Modified test/congrm.lean




## [2022-06-15 17:10:37](https://github.com/leanprover-community/mathlib/commit/430da94)
chore(analysis/normed): move `normed.normed_field` to `normed.field.basic` ([#14747](https://github.com/leanprover-community/mathlib/pull/14747))
#### Estimated changes
Modified src/analysis/locally_convex/polar.lean


Modified src/analysis/locally_convex/weak_dual.lean


Renamed src/analysis/normed/normed_field.lean to src/analysis/normed/field/basic.lean


Modified src/analysis/normed_space/basic.lean




## [2022-06-15 17:10:36](https://github.com/leanprover-community/mathlib/commit/6a0f967)
feat(data/finite/set): `finite` instances for set constructions ([#14673](https://github.com/leanprover-community/mathlib/pull/14673))
#### Estimated changes
Modified src/data/finite/basic.lean


Added src/data/finite/default.lean


Added src/data/finite/set.lean
- \+ *lemma* finite.of_finite_univ
- \+ *lemma* finite.set.finite_bUnion
- \+ *lemma* finite.set.finite_of_finite_image
- \+ *lemma* set.finite_iff_finite
- \+ *theorem* set.finite_of_finite
- \+ *lemma* set.finite_univ_iff



## [2022-06-15 17:10:35](https://github.com/leanprover-community/mathlib/commit/8eaeec2)
chore(a few random files): golfing using the new tactic `congrm` ([#14593](https://github.com/leanprover-community/mathlib/pull/14593))
This PR is simply intended to showcase some possible applications of the new tactic `congrm`, introduced in [#14153](https://github.com/leanprover-community/mathlib/pull/14153).
#### Estimated changes
Modified archive/100-theorems-list/45_partition.lean


Modified src/analysis/analytic/inverse.lean


Modified src/analysis/calculus/cont_diff.lean


Modified src/analysis/convex/gauge.lean




## [2022-06-15 14:55:51](https://github.com/leanprover-community/mathlib/commit/34ce784)
refactor(algebra/group_with_zero/basic): Golf using division monoid lemmas ([#14213](https://github.com/leanprover-community/mathlib/pull/14213))
Make all eligible `group_with_zero` lemmas one-liners from `division_monoid` ones and group them within the file.
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* div_div_cancel'
- \+/\- *lemma* div_eq_iff
- \+/\- *lemma* div_eq_iff_mul_eq
- \+/\- *lemma* div_eq_of_eq_mul
- \+/\- *lemma* div_eq_one_iff_eq
- \+/\- *lemma* div_helper
- \+/\- *lemma* div_left_inj'
- \+/\- *lemma* div_mul_cancel
- \+/\- *lemma* div_mul_left
- \+/\- *lemma* div_mul_right
- \+/\- *lemma* div_self
- \+/\- *lemma* eq_div_iff
- \+/\- *lemma* eq_div_iff_mul_eq
- \+/\- *lemma* eq_div_of_mul_eq
- \+/\- *lemma* inv_mul_eq_one₀
- \+/\- *lemma* is_unit_iff_ne_zero
- \+/\- *lemma* mul_div_cancel'
- \+/\- *lemma* mul_div_cancel
- \+/\- *lemma* mul_div_cancel_left
- \+/\- *lemma* mul_div_mul_left
- \+/\- *lemma* mul_div_mul_right
- \+/\- *lemma* mul_eq_one_iff_eq_inv₀
- \+/\- *lemma* mul_eq_one_iff_inv_eq₀
- \+/\- *lemma* mul_inv_eq_one₀
- \+/\- *lemma* mul_left_inj'
- \+/\- *lemma* mul_mul_div
- \+/\- *lemma* mul_one_div_cancel
- \+/\- *lemma* mul_right_inj'
- \+/\- *lemma* one_div_mul_cancel

Modified src/data/real/pi/leibniz.lean




## [2022-06-15 14:55:50](https://github.com/leanprover-community/mathlib/commit/bbca289)
feat(dynamics/periodic_pts): `chain.pairwise` on orbit ([#12991](https://github.com/leanprover-community/mathlib/pull/12991))
We prove that a relation holds pairwise on an orbit iff it does for `f^[n] x` and `f^[n+1] x` for any `n`.
#### Estimated changes
Modified src/data/list/cycle.lean
- \+ *theorem* cycle.chain_range_succ

Modified src/dynamics/periodic_pts.lean
- \+ *theorem* function.periodic_orbit_chain'
- \+ *theorem* function.periodic_orbit_chain



## [2022-06-15 13:13:12](https://github.com/leanprover-community/mathlib/commit/4661473)
chore(analysis/normed/normed_field): golf 2 proofs ([#14746](https://github.com/leanprover-community/mathlib/pull/14746))
#### Estimated changes
Modified src/analysis/normed/normed_field.lean




## [2022-06-15 13:13:11](https://github.com/leanprover-community/mathlib/commit/dccdef6)
chore(set_theory/ordinal/basic): golf ordinal addition definition ([#14744](https://github.com/leanprover-community/mathlib/pull/14744))
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean




## [2022-06-15 13:13:10](https://github.com/leanprover-community/mathlib/commit/d2bfb32)
feat(analysis/normed_space): range of `norm` ([#14740](https://github.com/leanprover-community/mathlib/pull/14740))
* Add `exists_norm_eq`, `range_norm`, `range_nnnorm`, and `nnnorm_surjective`.
* Open `set` namespace.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* exists_norm_eq
- \+ *lemma* nnnorm_surjective
- \+ *lemma* range_nnnorm
- \+ *lemma* range_norm



## [2022-06-15 13:13:09](https://github.com/leanprover-community/mathlib/commit/2aa3fd9)
feat(analysis/convex): a convex set is contractible ([#14732](https://github.com/leanprover-community/mathlib/pull/14732))
#### Estimated changes
Added src/analysis/convex/contractible.lean




## [2022-06-15 13:13:08](https://github.com/leanprover-community/mathlib/commit/7430d2d)
feat(data/complex/exponential): more `simp` lemmas ([#14731](https://github.com/leanprover-community/mathlib/pull/14731))
Add `simp` attrs and `simp` lemmas.
#### Estimated changes
Modified src/data/complex/exponential.lean
- \+/\- *lemma* complex.cosh_add_sinh
- \+/\- *lemma* complex.cosh_of_real_re
- \+/\- *lemma* complex.cosh_sq_sub_sinh_sq
- \+/\- *lemma* complex.cosh_sub_sinh
- \+ *lemma* complex.exp_sub_cosh
- \+ *lemma* complex.exp_sub_sinh
- \+/\- *lemma* complex.of_real_cosh_of_real_re
- \+/\- *lemma* complex.sinh_add_cosh
- \+ *lemma* complex.sinh_sub_cosh
- \+/\- *lemma* real.cosh_add_sinh
- \+/\- *lemma* real.cosh_neg
- \+ *lemma* real.cosh_sq'
- \+/\- *lemma* real.cosh_sq_sub_sinh_sq
- \+ *lemma* real.cosh_sub_sinh
- \+ *lemma* real.exp_sub_cosh
- \+ *lemma* real.exp_sub_sinh
- \+/\- *lemma* real.sinh_add_cosh
- \+ *lemma* real.sinh_lt_cosh
- \+ *lemma* real.sinh_sub_cosh



## [2022-06-15 13:13:07](https://github.com/leanprover-community/mathlib/commit/fee91d7)
feat(data/fin/vec_notation): add has_reflect instance and tests ([#14670](https://github.com/leanprover-community/mathlib/pull/14670))
#### Estimated changes
Modified src/data/fin/vec_notation.lean


Added test/vec_notation.lean




## [2022-06-15 13:13:06](https://github.com/leanprover-community/mathlib/commit/764d7a9)
feat(probability/stopping): first hitting time ([#14630](https://github.com/leanprover-community/mathlib/pull/14630))
This PR adds the first hitting time (before some time) and proves that it is a stopping time in the discrete case.
#### Estimated changes
Added src/probability/hitting_time.lean
- \+ *lemma* measure_theory.hitting_bot_le_iff
- \+ *lemma* measure_theory.hitting_eq_Inf
- \+ *lemma* measure_theory.hitting_is_stopping_time
- \+ *lemma* measure_theory.hitting_le
- \+ *lemma* measure_theory.hitting_le_iff_of_exists
- \+ *lemma* measure_theory.hitting_le_iff_of_lt
- \+ *lemma* measure_theory.hitting_le_of_mem
- \+ *lemma* measure_theory.hitting_lt_iff
- \+ *lemma* measure_theory.hitting_mem_Icc
- \+ *lemma* measure_theory.hitting_mem_set
- \+ *lemma* measure_theory.hitting_of_lt
- \+ *lemma* measure_theory.le_hitting
- \+ *lemma* measure_theory.le_hitting_of_exists



## [2022-06-15 13:13:04](https://github.com/leanprover-community/mathlib/commit/947c3c6)
refactor(order/locally_finite): Allow `finset.Iix`/`finset.Ixi` on empty types ([#14430](https://github.com/leanprover-community/mathlib/pull/14430))
Define `locally_finite_order_top` and `locally_finite_order_bot` are redefine `Ici`, `Ioi`, `iic`, `Iio` using them. Those new typeclasses are the same as `locally_finite_order` + `order_top`/`order_bot`, except that they allow the empty type, which is a surprisingly useful feature.
#### Estimated changes
Modified src/analysis/inner_product_space/gram_schmidt_ortho.lean
- \+/\- *lemma* gram_schmidt_zero

Modified src/combinatorics/set_family/lym.lean


Modified src/data/fin/interval.lean
- \+/\- *lemma* fin.Ici_eq_finset_subtype
- \+/\- *lemma* fin.Iic_eq_finset_subtype
- \+/\- *lemma* fin.Iio_eq_finset_subtype
- \+/\- *lemma* fin.Ioi_eq_finset_subtype
- \+/\- *lemma* fin.card_Ici
- \+/\- *lemma* fin.card_Ioi
- \+/\- *lemma* fin.card_filter_ge
- \+/\- *lemma* fin.card_filter_gt
- \+/\- *lemma* fin.card_filter_le
- \+/\- *lemma* fin.card_filter_lt_lt
- \+/\- *lemma* fin.card_fintype_Ici
- \+/\- *lemma* fin.card_fintype_Ioi
- \+/\- *lemma* fin.map_subtype_embedding_Icc
- \+/\- *lemma* fin.map_subtype_embedding_Ici
- \+/\- *lemma* fin.map_subtype_embedding_Ico
- \+/\- *lemma* fin.map_subtype_embedding_Iic
- \+/\- *lemma* fin.map_subtype_embedding_Iio
- \+/\- *lemma* fin.map_subtype_embedding_Ioc
- \+/\- *lemma* fin.map_subtype_embedding_Ioi
- \+/\- *lemma* fin.map_subtype_embedding_Ioo

Modified src/data/finset/locally_finite.lean
- \+/\- *lemma* finset.Icc_subset_Ici_self
- \+/\- *lemma* finset.Icc_subset_Iic_self
- \+/\- *lemma* finset.Ico_subset_Ici_self
- \+/\- *lemma* finset.Ico_subset_Iio_self
- \+/\- *lemma* finset.Iio_subset_Iic_self
- \+/\- *lemma* finset.Ioc_subset_Iic_self
- \+/\- *lemma* finset.Ioc_subset_Ioi_self
- \+/\- *lemma* finset.Ioi_subset_Ici_self
- \+/\- *lemma* finset.Ioo_subset_Ici_self
- \+/\- *lemma* finset.Ioo_subset_Iic_self
- \+/\- *lemma* finset.Ioo_subset_Iio_self
- \+/\- *lemma* finset.Ioo_subset_Ioi_self
- \+/\- *lemma* finset.filter_ge_eq_Iic
- \+/\- *lemma* finset.filter_gt_eq_Iio
- \+/\- *lemma* finset.filter_le_eq_Ici
- \+/\- *lemma* finset.filter_lt_eq_Ioi

Modified src/data/nat/interval.lean
- \+/\- *lemma* nat.card_Iic
- \+/\- *lemma* nat.card_Iio

Modified src/order/locally_finite.lean
- \+ *lemma* Icc_of_dual
- \+ *lemma* Ici_of_dual
- \+ *lemma* Ici_to_dual
- \+ *lemma* Ico_of_dual
- \+ *lemma* Iic_of_dual
- \+ *lemma* Iic_to_dual
- \+ *lemma* Iio_of_dual
- \+ *lemma* Iio_to_dual
- \+ *lemma* Ioc_of_dual
- \+ *lemma* Ioi_of_dual
- \+ *lemma* Ioi_to_dual
- \+ *lemma* Ioo_of_dual
- \+/\- *def* finset.Ici
- \+/\- *def* finset.Iic
- \+/\- *def* finset.Iio
- \+/\- *def* finset.Ioi
- \+/\- *lemma* finset.coe_Ici
- \+/\- *lemma* finset.coe_Iic
- \+/\- *lemma* finset.coe_Iio
- \+/\- *lemma* finset.coe_Ioi
- \+/\- *lemma* finset.map_subtype_embedding_Icc
- \+ *lemma* finset.map_subtype_embedding_Ici
- \+/\- *lemma* finset.map_subtype_embedding_Ico
- \+ *lemma* finset.map_subtype_embedding_Iic
- \+ *lemma* finset.map_subtype_embedding_Iio
- \+/\- *lemma* finset.map_subtype_embedding_Ioc
- \+ *lemma* finset.map_subtype_embedding_Ioi
- \+/\- *lemma* finset.map_subtype_embedding_Ioo
- \+/\- *lemma* finset.mem_Ici
- \+/\- *lemma* finset.mem_Iic
- \+/\- *lemma* finset.mem_Iio
- \+/\- *lemma* finset.mem_Ioi
- \+ *lemma* finset.subtype_Ici_eq
- \+ *lemma* finset.subtype_Iic_eq
- \+ *lemma* finset.subtype_Iio_eq
- \+ *lemma* finset.subtype_Ioi_eq
- \+ *def* locally_finite_order_bot.of_Iic'
- \+ *def* locally_finite_order_top.of_Ici'
- \+ *def* locally_finite_order_top.of_Ici
- \+ *def* locally_finite_order_top.of_Iic



## [2022-06-15 11:13:37](https://github.com/leanprover-community/mathlib/commit/114f543)
feat(model_theory/semantics, elementary_maps): Defines elementary equivalence ([#14723](https://github.com/leanprover-community/mathlib/pull/14723))
Defines elementary equivalence of structures
Shows that the domain and codomain of an elementary map are elementarily equivalent.
#### Estimated changes
Modified src/model_theory/elementary_maps.lean
- \+ *lemma* first_order.language.elementary_embedding.elementarily_equivalent
- \+ *lemma* first_order.language.elementary_substructure.elementarily_equivalent

Modified src/model_theory/semantics.lean
- \+ *def* first_order.language.elementarily_equivalent
- \+ *lemma* first_order.language.elementarily_equivalent_iff



## [2022-06-15 11:13:36](https://github.com/leanprover-community/mathlib/commit/9c40f30)
refactor(set_theory/game/*): fix theorem names ([#14685](https://github.com/leanprover-community/mathlib/pull/14685))
Some theorems about `exists` had `forall` in the name, other theorems about swapped `≤` or `⧏` used `le` and `lf` instead of `ge` and `gf`.
We also golf `le_of_forall_lt`.
#### Estimated changes
Modified src/set_theory/game/basic.lean


Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/nim.lean


Modified src/set_theory/game/pgame.lean
- \+ *theorem* has_le.le.not_gf
- \- *theorem* has_le.le.not_lf
- \+ *theorem* pgame.le_of_forall_lt
- \+/\- *theorem* pgame.lf.not_equiv'
- \+/\- *theorem* pgame.lf.not_equiv
- \+ *theorem* pgame.lf.not_ge
- \+ *theorem* pgame.lf.not_gt
- \- *theorem* pgame.lf.not_le
- \- *theorem* pgame.lf.not_lt
- \+ *theorem* pgame.lf_iff_exists_le
- \- *theorem* pgame.lf_iff_forall_le
- \+/\- *theorem* pgame.lf_irrefl
- \+ *theorem* pgame.lf_of_exists_le
- \- *theorem* pgame.lf_of_forall_le

Modified src/set_theory/surreal/basic.lean
- \- *theorem* pgame.le_of_forall_lt
- \+ *theorem* pgame.lt_iff_exists_le
- \- *theorem* pgame.lt_iff_forall_le
- \+ *theorem* pgame.lt_of_exists_le
- \- *theorem* pgame.lt_of_forall_le

Modified src/set_theory/surreal/dyadic.lean




## [2022-06-15 11:13:35](https://github.com/leanprover-community/mathlib/commit/c667723)
feat(model_theory/syntax, semantics): Mapping formulas given maps on terms and relations ([#14466](https://github.com/leanprover-community/mathlib/pull/14466))
Defines `first_order.language.bounded_formula.map_term_rel`, which maps formulas given maps on terms and maps on relations.
#### Estimated changes
Modified src/data/fin/basic.lean
- \+ *lemma* fin.cast_le_cast_le
- \+ *lemma* fin.cast_le_comp_cast_le
- \+ *lemma* fin.nat_add_cast_succ
- \+ *lemma* fin.nat_add_last

Modified src/data/fin/tuple/basic.lean
- \+ *lemma* fin.snoc_cast_add
- \+ *lemma* fin.snoc_comp_cast_add
- \+ *lemma* fin.snoc_comp_nat_add

Modified src/model_theory/semantics.lean
- \+ *lemma* first_order.language.bounded_formula.realize_map_term_rel_add_cast_le
- \+ *lemma* first_order.language.bounded_formula.realize_map_term_rel_id
- \- *lemma* first_order.language.bounded_formula.realize_subst_aux

Modified src/model_theory/syntax.lean
- \+ *lemma* first_order.language.bounded_formula.cast_le_cast_le
- \+ *lemma* first_order.language.bounded_formula.cast_le_comp_cast_le
- \+ *lemma* first_order.language.bounded_formula.cast_le_rfl
- \+/\- *def* first_order.language.bounded_formula.lift_at
- \+ *def* first_order.language.bounded_formula.map_term_rel
- \+ *def* first_order.language.bounded_formula.map_term_rel_equiv
- \+ *lemma* first_order.language.bounded_formula.map_term_rel_id_id_id
- \+ *lemma* first_order.language.bounded_formula.map_term_rel_map_term_rel
- \+/\- *def* first_order.language.bounded_formula.relabel
- \+ *lemma* first_order.language.bounded_formula.relabel_all
- \+ *lemma* first_order.language.bounded_formula.relabel_bot
- \+ *lemma* first_order.language.bounded_formula.relabel_ex
- \+ *lemma* first_order.language.bounded_formula.relabel_falsum
- \+ *lemma* first_order.language.bounded_formula.relabel_imp
- \+ *lemma* first_order.language.bounded_formula.relabel_not
- \+/\- *def* first_order.language.bounded_formula.subst
- \+ *lemma* first_order.language.term.relabel_comp_relabel
- \+/\- *lemma* first_order.language.term.relabel_id
- \+ *lemma* first_order.language.term.relabel_id_eq_id



## [2022-06-15 11:13:33](https://github.com/leanprover-community/mathlib/commit/ea97606)
feat(tactic/ring): recursive ring_nf ([#14429](https://github.com/leanprover-community/mathlib/pull/14429))
As [reported on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60ring_nf.60.20not.20consistently.20normalizing.3F). This allows `ring_nf` to rewrite inside the atoms of a ring expression, meaning that things like `f (a + b) + c` can simplify in both `+` expressions.
#### Estimated changes
Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/ring_theory/trace.lean


Modified src/tactic/ring.lean
- \+ *structure* tactic.ring.ring_nf_cfg

Modified test/ring.lean




## [2022-06-15 10:32:10](https://github.com/leanprover-community/mathlib/commit/6e0e270)
feat(linear_algebra/matrix): positive definite ([#14531](https://github.com/leanprover-community/mathlib/pull/14531))
Define positive definite matrices and connect them to positive definiteness of quadratic forms.
#### Estimated changes
Modified src/linear_algebra/matrix/hermitian.lean


Added src/linear_algebra/matrix/pos_def.lean
- \+ *def* matrix.pos_def
- \+ *lemma* matrix.pos_def_of_to_quadratic_form'
- \+ *lemma* matrix.pos_def_to_quadratic_form'
- \+ *lemma* quadratic_form.pos_def_of_to_matrix'
- \+ *lemma* quadratic_form.pos_def_to_matrix'

Modified src/linear_algebra/quadratic_form/basic.lean
- \+ *lemma* quadratic_form.is_symm_to_matrix'



## [2022-06-15 09:13:28](https://github.com/leanprover-community/mathlib/commit/784c703)
docs(topology/basic): Fix typo in library note ([#14743](https://github.com/leanprover-community/mathlib/pull/14743))
#### Estimated changes
Modified src/topology/basic.lean




## [2022-06-15 08:32:58](https://github.com/leanprover-community/mathlib/commit/1fbe118)
golf(set_theory/game/pgame): golf `neg_le_neg_iff` ([#14726](https://github.com/leanprover-community/mathlib/pull/14726))
Also in this PR:
+ slightly golf `subsequent.trans`
+ replace `->` by `→`
+ replace a nonterminal `simp` by `dsimp`
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+/\- *lemma* pgame.left_moves_add_cases
- \+/\- *theorem* pgame.neg_le_neg_iff
- \+/\- *theorem* pgame.neg_lf_neg_iff
- \+/\- *lemma* pgame.right_moves_add_cases
- \+/\- *theorem* pgame.subsequent.trans



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
Modified src/analysis/convex/extreme.lean




## [2022-06-15 07:00:25](https://github.com/leanprover-community/mathlib/commit/6b4f3f2)
feat(data/nat/prime): prime.even_iff ([#14688](https://github.com/leanprover-community/mathlib/pull/14688))
Adds a lemma saying that the only even prime is two.
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.prime.even_iff



## [2022-06-15 04:54:47](https://github.com/leanprover-community/mathlib/commit/e86ab0b)
refactor(src/algebra/order/monoid): make bot_eq_zero a simp lemma only when the order is linear ([#14553](https://github.com/leanprover-community/mathlib/pull/14553))
#### Estimated changes
Modified src/algebra/lie/subalgebra.lean
- \- *def* lie_subalgebra.canonically_ordered_add_monoid

Modified src/algebra/module/submodule/pointwise.lean
- \- *def* submodule.canonically_ordered_add_monoid

Modified src/algebra/order/monoid.lean
- \+ *lemma* bot_eq_one'
- \+/\- *lemma* bot_eq_one

Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.bot_eq_zero



## [2022-06-15 04:54:45](https://github.com/leanprover-community/mathlib/commit/b4b816c)
feat(number_theory/cyclotomic/primitive_roots): generalize finrank lemma  ([#14550](https://github.com/leanprover-community/mathlib/pull/14550))
We generalize certain results from fields to domains.
#### Estimated changes
Modified src/number_theory/cyclotomic/discriminant.lean


Modified src/number_theory/cyclotomic/gal.lean


Modified src/number_theory/cyclotomic/primitive_roots.lean




## [2022-06-15 03:13:18](https://github.com/leanprover-community/mathlib/commit/38ad656)
chore(field_theory/intermediate_field): fix timeout ([#14725](https://github.com/leanprover-community/mathlib/pull/14725))
+ Remove `@[simps]` from `intermediate_field_map` to reduce `decl post-processing of intermediate_field_map` from 18.3s to 46.4ms (on my machine).
+ Manually provide the two `simp` lemmas previously auto-generated by `@[simps]`. Mathlib compiles even without the two simp lemmas (see commit 1f5a7f1), but I am inclined to keep them in case some other branches/projects are using them.
[Zulip reports](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/deterministic.20timeout/near/285792556) about `intermediate_field_map` causing timeout in two separate branches
#### Estimated changes
Modified src/field_theory/intermediate_field.lean
- \+/\- *def* intermediate_field.intermediate_field_map
- \+ *lemma* intermediate_field.intermediate_field_map_apply_coe
- \+ *lemma* intermediate_field.intermediate_field_map_symm_apply_coe



## [2022-06-15 03:13:17](https://github.com/leanprover-community/mathlib/commit/dd4d8e6)
feat(logic/hydra): basic lemmas on `cut_expand` ([#14408](https://github.com/leanprover-community/mathlib/pull/14408))
#### Estimated changes
Modified src/logic/hydra.lean
- \+/\- *def* relation.cut_expand
- \+ *theorem* relation.cut_expand_add_left
- \+/\- *lemma* relation.cut_expand_fibration
- \+/\- *lemma* relation.cut_expand_iff
- \+ *theorem* relation.cut_expand_singleton
- \+ *theorem* relation.cut_expand_singleton_singleton
- \+ *theorem* relation.not_cut_expand_zero



## [2022-06-15 03:13:16](https://github.com/leanprover-community/mathlib/commit/a16f1cf)
feat(set_theory/game/basic): cast inequalities on `pgame` to `game` ([#14405](https://github.com/leanprover-community/mathlib/pull/14405))
#### Estimated changes
Modified src/set_theory/game/basic.lean
- \+ *theorem* pgame.equiv_iff_game_eq
- \+ *theorem* pgame.fuzzy_iff_game_fuzzy
- \+ *theorem* pgame.le_iff_game_le
- \+ *theorem* pgame.lf_iff_game_lf
- \+ *theorem* pgame.lt_iff_game_lt



## [2022-06-15 00:05:51](https://github.com/leanprover-community/mathlib/commit/bf2edb5)
feat(data/vector/basic): reflected instance for vectors ([#14669](https://github.com/leanprover-community/mathlib/pull/14669))
This means that a `vector` from a tactic block can be used in an expression.
#### Estimated changes
Modified src/data/vector/basic.lean




## [2022-06-15 00:05:50](https://github.com/leanprover-community/mathlib/commit/b134b2f)
refactor(set_theory/game/state): rename `pgame.of` to `pgame.of_state` ([#14658](https://github.com/leanprover-community/mathlib/pull/14658))
This is so that we can redefine `pgame.of x y = {x | y}` in [#14659](https://github.com/leanprover-community/mathlib/pull/14659). Further, this is just a much clearer name.
#### Estimated changes
Modified src/set_theory/game/domineering.lean
- \+/\- *def* pgame.domineering

Modified src/set_theory/game/state.lean
- \- *def* game.of
- \+ *def* game.of_state
- \- *def* pgame.left_moves_of
- \- *def* pgame.left_moves_of_aux
- \+ *def* pgame.left_moves_of_state
- \+ *def* pgame.left_moves_of_state_aux
- \- *def* pgame.of
- \- *def* pgame.of_aux
- \- *def* pgame.of_aux_relabelling
- \+ *def* pgame.of_state
- \+ *def* pgame.of_state_aux
- \+ *def* pgame.of_state_aux_relabelling
- \+/\- *def* pgame.relabelling_move_left
- \+/\- *def* pgame.relabelling_move_right
- \- *def* pgame.right_moves_of
- \- *def* pgame.right_moves_of_aux
- \+ *def* pgame.right_moves_of_state
- \+ *def* pgame.right_moves_of_state_aux



## [2022-06-15 00:05:49](https://github.com/leanprover-community/mathlib/commit/7b2970f)
feat(set_theory/cardinal/basic): improve docs on `lift`, add `simp` lemmas ([#14596](https://github.com/leanprover-community/mathlib/pull/14596))
We add some much needed documentation to the `cardinal.lift` API.  We also mark a few extra lemmas with `simp`.
#### Estimated changes
Modified src/set_theory/cardinal/basic.lean
- \+/\- *theorem* cardinal.lift_id'
- \+/\- *theorem* cardinal.lift_umax'
- \+/\- *theorem* cardinal.lift_umax



## [2022-06-15 00:05:48](https://github.com/leanprover-community/mathlib/commit/2e2d515)
feat(data/nat/factorization): add lemma `coprime_of_div_pow_factorization` ([#14576](https://github.com/leanprover-community/mathlib/pull/14576))
Add lemma `coprime_of_div_pow_factorization (hp : prime p) (hn : n ≠ 0) : coprime p (n / p ^ n.factorization p)`
Prompted by [this Zulip question](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/div.20by.20p_adic_val_nat.20is.20coprime).
#### Estimated changes
Modified src/data/nat/factorization/basic.lean
- \+ *lemma* nat.coprime_of_div_pow_factorization



## [2022-06-14 18:25:05](https://github.com/leanprover-community/mathlib/commit/16728b3)
feat(topology/homotopy/contractible): a few convenience lemmas ([#14710](https://github.com/leanprover-community/mathlib/pull/14710))
If `X` and `Y` are homotopy equivalent spaces, then one is
contractible if and only if the other one is contractible.
#### Estimated changes
Modified src/topology/homotopy/contractible.lean
- \+/\- *lemma* id_nullhomotopic



## [2022-06-14 18:25:02](https://github.com/leanprover-community/mathlib/commit/05aa960)
feat(analysis/special_functions/trigonometric/deriv): compare `sinh x` with `x` ([#14702](https://github.com/leanprover-community/mathlib/pull/14702))
#### Estimated changes
Modified src/analysis/special_functions/arsinh.lean
- \- *lemma* real.sinh_injective

Modified src/analysis/special_functions/log/basic.lean
- \+ *lemma* real.cosh_log
- \+ *lemma* real.sinh_log

Modified src/analysis/special_functions/trigonometric/deriv.lean
- \+ *lemma* real.cosh_le_cosh
- \+ *lemma* real.cosh_lt_cosh
- \+ *lemma* real.cosh_strict_mono_on
- \+ *lemma* real.one_le_cosh
- \+ *lemma* real.one_lt_cosh
- \+ *lemma* real.self_le_sinh_iff
- \+ *lemma* real.self_lt_sinh_iff
- \+ *lemma* real.sinh_inj
- \+ *lemma* real.sinh_injective
- \+ *lemma* real.sinh_le_self_iff
- \+ *lemma* real.sinh_le_sinh
- \+ *lemma* real.sinh_lt_self_iff
- \+ *lemma* real.sinh_lt_sinh
- \+ *lemma* real.sinh_neg_iff
- \+ *lemma* real.sinh_nonneg_iff
- \+ *lemma* real.sinh_nonpos_iff
- \+ *lemma* real.sinh_pos_iff
- \+ *lemma* real.sinh_sub_id_strict_mono

Modified src/data/complex/exponential.lean
- \+ *lemma* real.cosh_abs



## [2022-06-14 18:24:59](https://github.com/leanprover-community/mathlib/commit/d5c7260)
feat(order/monotone): add lemmas about `cmp` ([#14689](https://github.com/leanprover-community/mathlib/pull/14689))
Also replace `order_dual.cmp_le_flip` with lemmas about `to_dual` and `of_dual`.
#### Estimated changes
Modified src/data/ordmap/ordset.lean


Modified src/order/compare.lean
- \+ *lemma* cmp_le_of_dual
- \+ *lemma* cmp_le_to_dual
- \+ *lemma* cmp_of_dual
- \+ *lemma* cmp_to_dual
- \+ *lemma* eq_iff_eq_of_cmp_eq_cmp
- \- *lemma* order_dual.cmp_le_flip
- \+ *lemma* ordering.compares.cmp_eq

Modified src/order/monotone.lean
- \+ *lemma* strict_anti.cmp_map_eq
- \+ *lemma* strict_anti_on.cmp_map_eq
- \+ *lemma* strict_mono.cmp_map_eq
- \+ *lemma* strict_mono_on.cmp_map_eq



## [2022-06-14 17:04:56](https://github.com/leanprover-community/mathlib/commit/6cdc30d)
golf(set_theory/ordinal/basic): golf theorems on `cardinal.ord` and `ordinal.card`  ([#14709](https://github.com/leanprover-community/mathlib/pull/14709))
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean
- \+/\- *lemma* cardinal.mk_ord_out



## [2022-06-14 15:42:17](https://github.com/leanprover-community/mathlib/commit/ed033f3)
feat(linear_algebra/vandermonde): add lemmas about det equals zero ([#14695](https://github.com/leanprover-community/mathlib/pull/14695))
Adding two lemmas about when the determinant is zero.
I shortened the first with the help of some code I found in `ring_theory/trace.lean`, lemma `det_trace_matrix_ne_zero'`.
#### Estimated changes
Modified src/linear_algebra/vandermonde.lean
- \+ *lemma* matrix.det_vandermonde_eq_zero_iff
- \+ *lemma* matrix.det_vandermonde_ne_zero_iff



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
Added src/tactic/congrm.lean


Added test/congrm.lean




## [2022-06-14 13:35:08](https://github.com/leanprover-community/mathlib/commit/32d8fc4)
feat(topology/homeomorph): add `homeomorph.set.univ` ([#14730](https://github.com/leanprover-community/mathlib/pull/14730))
#### Estimated changes
Modified src/topology/homeomorph.lean
- \+/\- *def* homeomorph.image
- \+ *def* homeomorph.set.univ



## [2022-06-14 13:35:07](https://github.com/leanprover-community/mathlib/commit/1c8f995)
feat(analysis/special_functions/exp): add `real.exp_half` ([#14729](https://github.com/leanprover-community/mathlib/pull/14729))
#### Estimated changes
Modified src/analysis/special_functions/exp.lean
- \+ *lemma* real.exp_half



## [2022-06-14 13:35:06](https://github.com/leanprover-community/mathlib/commit/da5a737)
feat(data/complex/basic): ranges of `re`, `im`, `norm_sq`, and `abs` ([#14727](https://github.com/leanprover-community/mathlib/pull/14727))
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *theorem* complex.im_surjective
- \+ *lemma* complex.range_abs
- \+ *theorem* complex.range_im
- \+ *lemma* complex.range_norm_sq
- \+ *theorem* complex.range_re
- \+ *theorem* complex.re_surjective



## [2022-06-14 13:35:05](https://github.com/leanprover-community/mathlib/commit/b11f8e7)
refactor(algebra/order/group): unify instances ([#14705](https://github.com/leanprover-community/mathlib/pull/14705))
Drop `group.covariant_class_le.to_contravariant_class_le` etc in favor
of `group.covconv` (now an instance) and a new similar instance
`group.covconv_swap`.
#### Estimated changes
Modified src/algebra/covariant_and_contravariant.lean
- \+ *lemma* group.covariant_swap_iff_contravariant_swap
- \- *lemma* group.covconv

Modified src/algebra/order/group.lean




## [2022-06-14 13:35:03](https://github.com/leanprover-community/mathlib/commit/2b46992)
feat(algebra/algebra/basic): define `alg_hom_class` and `non_unital_alg_hom_class` ([#14679](https://github.com/leanprover-community/mathlib/pull/14679))
This PR defines `alg_hom_class` and `non_unital_alg_hom_class` as part of the morphism refactor.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *lemma* alg_hom.map_add
- \- *lemma* alg_hom.map_bit0
- \- *lemma* alg_hom.map_bit1
- \- *lemma* alg_hom.map_finsupp_prod
- \- *lemma* alg_hom.map_finsupp_sum
- \- *lemma* alg_hom.map_mul
- \- *lemma* alg_hom.map_multiset_prod
- \- *lemma* alg_hom.map_neg
- \- *lemma* alg_hom.map_one
- \- *lemma* alg_hom.map_pow
- \- *lemma* alg_hom.map_prod
- \- *lemma* alg_hom.map_smul
- \- *lemma* alg_hom.map_sub
- \- *lemma* alg_hom.map_sum
- \- *lemma* alg_hom.map_zero

Modified src/algebra/hom/non_unital_alg.lean
- \- *lemma* non_unital_alg_hom.map_add
- \- *lemma* non_unital_alg_hom.map_mul
- \- *lemma* non_unital_alg_hom.map_smul
- \- *lemma* non_unital_alg_hom.map_zero



## [2022-06-14 13:35:02](https://github.com/leanprover-community/mathlib/commit/5d18a72)
feat(order/{conditionally_complete_lattice,galois_connection): Supremum of `set.image2` ([#14307](https://github.com/leanprover-community/mathlib/pull/14307))
`Sup` and `Inf` distribute over `set.image2` in the presence of appropriate Galois connections.
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+ *lemma* Inf_image2
- \+ *lemma* Sup_image2
- \+ *lemma* binfi_prod
- \+ *lemma* bsupr_prod
- \+/\- *theorem* infi_prod
- \+/\- *theorem* supr_prod

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* cInf_image2_eq_cInf_cInf
- \+ *lemma* cInf_image2_eq_cInf_cSup
- \+ *lemma* cInf_image2_eq_cSup_cInf
- \+ *lemma* cInf_image2_eq_cSup_cSup
- \+ *lemma* cSup_image2_eq_cInf_cInf
- \+ *lemma* cSup_image2_eq_cInf_cSup
- \+ *lemma* cSup_image2_eq_cSup_cInf
- \+ *lemma* cSup_image2_eq_cSup_cSup
- \+ *lemma* csupr_le_iff
- \+ *lemma* csupr_set_le_iff
- \+ *lemma* le_cinfi_iff
- \+ *lemma* le_cinfi_set_iff

Modified src/order/galois_connection.lean
- \+ *lemma* Inf_image2_eq_Inf_Inf
- \+ *lemma* Inf_image2_eq_Inf_Sup
- \+ *lemma* Inf_image2_eq_Sup_Inf
- \+ *lemma* Inf_image2_eq_Sup_Sup
- \+ *lemma* Sup_image2_eq_Inf_Inf
- \+ *lemma* Sup_image2_eq_Inf_Sup
- \+ *lemma* Sup_image2_eq_Sup_Inf
- \+ *lemma* Sup_image2_eq_Sup_Sup



## [2022-06-14 13:35:01](https://github.com/leanprover-community/mathlib/commit/300c439)
feat(algebra/lie/weights): the zero root space is the Cartan subalgebra for a Noetherian Lie algebra ([#14174](https://github.com/leanprover-community/mathlib/pull/14174))
#### Estimated changes
Modified src/algebra/lie/cartan_subalgebra.lean
- \+ *lemma* lie_subalgebra.centralizer_eq_self_of_is_cartan_subalgebra

Modified src/algebra/lie/of_associative.lean
- \+/\- *lemma* lie_submodule.coe_map_to_endomorphism_le
- \+ *lemma* lie_submodule.to_endomorphism_comp_subtype_mem
- \+ *lemma* lie_submodule.to_endomorphism_restrict_eq_to_endomorphism

Modified src/algebra/lie/weights.lean
- \+ *lemma* lie_algebra.is_cartan_of_zero_root_subalgebra_eq
- \+ *lemma* lie_algebra.zero_root_subalgebra_eq_iff_is_cartan
- \+ *lemma* lie_algebra.zero_root_subalgebra_eq_of_is_cartan
- \- *lemma* lie_algebra.zero_root_subalgebra_is_cartan_of_eq
- \+ *lemma* lie_module.exists_pre_weight_space_zero_le_ker_of_is_noetherian
- \+ *lemma* lie_module.is_nilpotent_to_endomorphism_weight_space_zero

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.pow_apply_mem_of_forall_mem
- \+ *lemma* linear_map.pow_restrict

Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* module.End.eigenspace_zero
- \+ *lemma* module.End.generalized_eigenspace_zero



## [2022-06-14 11:24:09](https://github.com/leanprover-community/mathlib/commit/67dfb57)
feat(set_theory/cardinal/cofinality): lemma on subsets of strong limit cardinal ([#14442](https://github.com/leanprover-community/mathlib/pull/14442))
#### Estimated changes
Modified src/order/rel_classes.lean
- \+ *lemma* set.unbounded_of_is_empty

Modified src/set_theory/cardinal/cofinality.lean
- \+ *theorem* cardinal.mk_bounded_subset
- \+ *theorem* cardinal.mk_subset_mk_lt_cof

Modified src/set_theory/ordinal/arithmetic.lean
- \+ *lemma* ordinal.bounded_singleton



## [2022-06-14 01:31:50](https://github.com/leanprover-community/mathlib/commit/7fee0f1)
fix(data/list/nodup): change `Type` to `Type u` ([#14721](https://github.com/leanprover-community/mathlib/pull/14721))
Change `Type` to `Type u` in `nodup_iff_nth_ne_nth` and two other lemmas added in [#14371](https://github.com/leanprover-community/mathlib/pull/14371).
#### Estimated changes
Modified src/data/list/basic.lean
- \+/\- *lemma* list.nth_le_eq_iff
- \+/\- *lemma* list.some_nth_le_eq

Modified src/data/list/nodup.lean
- \+/\- *theorem* list.nodup.nth_le_inj_iff
- \+/\- *lemma* list.nodup_iff_nth_ne_nth



## [2022-06-14 01:31:49](https://github.com/leanprover-community/mathlib/commit/659983c)
feat(logic/equiv/basic): add `Pi_comm` aka `function.swap` as an `equiv` ([#14561](https://github.com/leanprover-community/mathlib/pull/14561))
#### Estimated changes
Modified src/logic/equiv/basic.lean
- \+ *def* equiv.Pi_comm
- \+ *lemma* equiv.Pi_comm_symm



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
Modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean
- \+ *lemma* ex_L.exists_add_of_le
- \- *lemma* ex_L.le_iff_exists_add
- \+ *lemma* ex_L.le_self_add

Modified src/algebra/associated.lean


Modified src/algebra/lie/subalgebra.lean


Modified src/algebra/module/submodule/pointwise.lean


Modified src/algebra/order/monoid.lean
- \+/\- *lemma* le_iff_exists_mul'
- \+/\- *lemma* le_iff_exists_mul
- \+/\- *lemma* le_mul_self
- \+/\- *lemma* le_self_mul
- \+/\- *lemma* self_le_mul_left
- \+/\- *lemma* self_le_mul_right

Modified src/algebra/order/nonneg.lean


Modified src/algebra/order/pi.lean


Modified src/algebra/punit_instances.lean


Modified src/data/dfinsupp/order.lean


Modified src/data/finsupp/order.lean


Modified src/data/multiset/basic.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/enat.lean


Modified src/data/set/semiring.lean


Modified src/set_theory/cardinal/basic.lean




## [2022-06-13 23:08:36](https://github.com/leanprover-community/mathlib/commit/2967fae)
refactor(data/option/defs): Swap arguments to `option.elim` ([#14681](https://github.com/leanprover-community/mathlib/pull/14681))
Make `option.elim` a non-dependent version of `option.rec` rather than a non-dependent version of `option.rec_on`. Same for `option.melim`.
This replaces `option.cons`, and brings `option.elim` in line with `nat.elim`, `sum.elim`, and `iff.elim`.
It addresses the TODO comment added in 22c4291217925c6957c0f5a44551c9917b56c7cf.
#### Estimated changes
Modified src/algebra/big_operators/option.lean


Modified src/analysis/box_integral/partition/basic.lean


Modified src/analysis/calculus/lagrange_multipliers.lean


Modified src/category_theory/category/PartialFun.lean
- \+/\- *def* Pointed_to_PartialFun

Modified src/computability/tm_to_partrec.lean


Modified src/data/finset/basic.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/data/option/basic.lean
- \- *def* option.cons
- \- *lemma* option.cons_none_some
- \+ *lemma* option.elim_none_some

Modified src/data/option/defs.lean
- \+/\- *def* option.melim

Modified src/logic/embedding.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/number_theory/dioph.lean


Modified src/tactic/linarith/frontend.lean


Modified src/topology/paracompact.lean




## [2022-06-13 21:43:10](https://github.com/leanprover-community/mathlib/commit/425dfe7)
feat(set_theory/game/ordinal): golf `to_pgame_birthday` ([#14662](https://github.com/leanprover-community/mathlib/pull/14662))
#### Estimated changes
Modified src/set_theory/game/birthday.lean




## [2022-06-13 19:21:13](https://github.com/leanprover-community/mathlib/commit/3afafe6)
doc(ring_theory/algebraic): clarify docstring ([#14715](https://github.com/leanprover-community/mathlib/pull/14715))
#### Estimated changes
Modified src/ring_theory/algebraic.lean




## [2022-06-13 19:21:12](https://github.com/leanprover-community/mathlib/commit/b44e742)
feat(category_theory/limits): realise products as pullbacks ([#14322](https://github.com/leanprover-community/mathlib/pull/14322))
This was mostly done in [#10581](https://github.com/leanprover-community/mathlib/pull/10581), this just adds the isomorphisms between the objects produced by the `has_limit` API.
#### Estimated changes
Modified src/category_theory/limits/constructions/binary_products.lean
- \+ *def* coprod_iso_pushout
- \+ *def* prod_iso_pullback



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
Modified docs/overview.yaml


Modified src/algebra/big_operators/associated.lean
- \+ *theorem* associates.finset_prod_mk

Modified src/algebra/direct_sum/module.lean


Added src/algebra/module/dedekind_domain.lean
- \+ *theorem* submodule.is_internal_prime_power_torsion
- \+ *lemma* submodule.is_internal_prime_power_torsion_of_is_torsion_by_ideal

Added src/algebra/module/pid.lean
- \+ *lemma* ideal.torsion_of_eq_span_pow_p_order
- \+ *theorem* module.equiv_direct_sum_of_is_torsion
- \+ *theorem* module.equiv_free_prod_direct_sum
- \+ *lemma* module.exists_smul_eq_zero_and_mk_eq
- \+ *lemma* module.p_pow_smul_lift
- \+ *theorem* module.torsion_by_prime_power_decomposition
- \+ *theorem* submodule.is_internal_prime_power_torsion_of_pid

Modified src/algebra/module/torsion.lean
- \- *lemma* ideal.sup_eq_top_iff_is_coprime

Modified src/data/multiset/bind.lean
- \+ *lemma* multiset.le_bind

Modified src/data/set/basic.lean
- \+ *lemma* set.insert_image_compl_eq_range

Modified src/linear_algebra/quotient.lean
- \+ *def* submodule.liftq_span_singleton
- \+ *lemma* submodule.liftq_span_singleton_apply
- \+ *lemma* submodule.mkq_surjective

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.sup_eq_top_iff_is_coprime



## [2022-06-13 17:42:16](https://github.com/leanprover-community/mathlib/commit/3225926)
feat(category_theory/monoidal): monoidal functors `Type ⥤  C` acting on powers ([#14330](https://github.com/leanprover-community/mathlib/pull/14330))
#### Estimated changes
Modified src/category_theory/monoidal/types.lean
- \+ *def* category_theory.monoidal_functor.map_pi

Modified src/logic/equiv/fin.lean
- \+ *def* equiv.pi_fin_succ



## [2022-06-13 16:22:21](https://github.com/leanprover-community/mathlib/commit/6ad2799)
chore(analysis/locally_convex/weak_dual): golf using `seminorm.comp` ([#14699](https://github.com/leanprover-community/mathlib/pull/14699))
#### Estimated changes
Modified src/analysis/locally_convex/weak_dual.lean




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
Modified src/data/zmod/basic.lean


Modified test/instance_diamonds.lean




## [2022-06-13 14:24:16](https://github.com/leanprover-community/mathlib/commit/aed7f9a)
feat(topology/uniform_space/basic): add three easy lemmas about `uniform_space.comap` ([#14678](https://github.com/leanprover-community/mathlib/pull/14678))
These are uniform spaces versions of `filter.comap_inf`, `filter.comap_infi` and `filter.comap_mono`. I split them from [#14534](https://github.com/leanprover-community/mathlib/pull/14534) which is already a quite big PR.
#### Estimated changes
Modified src/topology/algebra/uniform_field.lean


Modified src/topology/uniform_space/basic.lean
- \+ *lemma* uniform_space.comap_inf
- \+ *lemma* uniform_space.comap_infi
- \+ *lemma* uniform_space.comap_mono



## [2022-06-13 13:01:51](https://github.com/leanprover-community/mathlib/commit/b7b371e)
doc(field_theory/finite/trace): fix module docstring ([#14711](https://github.com/leanprover-community/mathlib/pull/14711))
This PR just fixes the docstring in `field_theory/finite/trace.lean`. It was still mentioning a definition that was removed.
#### Estimated changes
Modified src/field_theory/finite/trace.lean




## [2022-06-13 13:01:50](https://github.com/leanprover-community/mathlib/commit/46ac3cb)
chore(analysis/complex/upper_half_plane): move to a subdirectory ([#14704](https://github.com/leanprover-community/mathlib/pull/14704))
I'm going to add more files to `analysis/complex/upper_half_plane/` soon.
#### Estimated changes
Renamed src/analysis/complex/upper_half_plane.lean to src/analysis/complex/upper_half_plane/basic.lean


Modified src/number_theory/modular.lean




## [2022-06-13 11:39:13](https://github.com/leanprover-community/mathlib/commit/04019de)
chore(algebra/big_operators/associated,ring_theory/unique_factorization_domain): golf ([#14671](https://github.com/leanprover-community/mathlib/pull/14671))
#### Estimated changes
Modified src/algebra/big_operators/associated.lean


Modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *lemma* unique_factorization_monoid.factors_unique
- \+/\- *theorem* unique_factorization_monoid.prime_of_factor



## [2022-06-13 09:39:39](https://github.com/leanprover-community/mathlib/commit/b100037)
refactor(order/conditionally_complete_lattice): use `order_bot` ([#14568](https://github.com/leanprover-community/mathlib/pull/14568))
Use `order_bot` instead of an explicit `c = ⊥` argument in
`well_founded.conditionally_complete_linear_order_with_bot`. Also
reuse `linear_order.to_lattice` and add `well_founded.min_le`.
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean


Modified src/order/well_founded.lean
- \+ *theorem* well_founded.min_le

Modified src/set_theory/cardinal/basic.lean


Modified src/set_theory/ordinal/basic.lean




## [2022-06-13 09:39:38](https://github.com/leanprover-community/mathlib/commit/4b67645)
chore(algebra/ring_quot): provide an explicit npow field ([#14349](https://github.com/leanprover-community/mathlib/pull/14349))
While this probably shouldn't matter since `ring_quot` is irreducible, this matches what we do for `nsmul` and `zsmul`.
#### Estimated changes
Modified src/algebra/ring_quot.lean
- \+ *lemma* ring_quot.pow_quot



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
Modified src/set_theory/game/birthday.lean
- \- *theorem* pgame.birthday_half

Modified src/set_theory/game/pgame.lean
- \- *def* pgame.half
- \- *theorem* pgame.half_add_half_equiv_one
- \- *theorem* pgame.half_left_moves
- \- *theorem* pgame.half_lt_one
- \- *lemma* pgame.half_move_left
- \- *lemma* pgame.half_move_right
- \- *theorem* pgame.half_right_moves

Modified src/set_theory/surreal/basic.lean
- \- *theorem* pgame.numeric_half

Modified src/set_theory/surreal/dyadic.lean
- \+/\- *theorem* pgame.add_pow_half_succ_self_eq_pow_half
- \+ *theorem* pgame.birthday_half
- \+ *theorem* pgame.half_add_half_equiv_one
- \+/\- *theorem* pgame.numeric_pow_half
- \+ *theorem* pgame.pow_half_le_one
- \+/\- *lemma* pgame.pow_half_left_moves
- \- *lemma* pgame.pow_half_move_left'
- \+/\- *lemma* pgame.pow_half_move_left
- \- *lemma* pgame.pow_half_move_right'
- \- *lemma* pgame.pow_half_move_right
- \+ *theorem* pgame.pow_half_pos
- \- *lemma* pgame.pow_half_right_moves
- \+/\- *theorem* pgame.pow_half_succ_le_pow_half
- \+ *theorem* pgame.pow_half_succ_lt_one
- \+/\- *theorem* pgame.pow_half_succ_lt_pow_half
- \+ *lemma* pgame.pow_half_succ_move_right
- \+ *lemma* pgame.pow_half_succ_right_moves
- \+ *lemma* pgame.pow_half_zero
- \+ *lemma* pgame.pow_half_zero_right_moves
- \+/\- *theorem* pgame.zero_le_pow_half
- \- *theorem* pgame.zero_lt_pow_half
- \- *theorem* surreal.add_half_self_eq_one
- \+/\- *lemma* surreal.double_pow_half_succ_eq_pow_half
- \- *def* surreal.half
- \+/\- *lemma* surreal.nsmul_pow_two_pow_half'
- \+/\- *lemma* surreal.nsmul_pow_two_pow_half
- \+/\- *def* surreal.pow_half
- \- *lemma* surreal.pow_half_one



## [2022-06-13 03:45:17](https://github.com/leanprover-community/mathlib/commit/dc9eab6)
feat(tactic/lift): generalize pi.can_lift to Sort ([#14700](https://github.com/leanprover-community/mathlib/pull/14700))
#### Estimated changes
Modified src/tactic/lift.lean




## [2022-06-12 20:34:14](https://github.com/leanprover-community/mathlib/commit/8fb92bf)
feat(measure_theory/integral/circle_integral): add lemma `circle_map_nmem_ball` ([#14643](https://github.com/leanprover-community/mathlib/pull/14643))
The lemma `set.ne_of_mem_nmem` is unrelated except that both of these should be helpful for:
https://github.com/leanprover-community/mathlib/pull/13885
#### Estimated changes
Modified src/measure_theory/integral/circle_integral.lean
- \+ *lemma* circle_map_ne_mem_ball
- \+ *lemma* circle_map_not_mem_ball



## [2022-06-12 16:53:57](https://github.com/leanprover-community/mathlib/commit/d6eb634)
feat(number_theory/legendre_symbol/auxiliary, *): add/move lemmas in/to various files, delete `auxiliary.lean` ([#14572](https://github.com/leanprover-community/mathlib/pull/14572))
This is the first PR in a series that will culminate in providing the proof of Quadratic Reciprocity using Gauss sums.
Here we just add some lemmas to the file `auxiliary.lean` that will be used in new code later.
We also generalize the lemmas `neg_one_ne_one_of_char_ne_two` and `neg_ne_self_of_char_ne_two` from finite fields to more general rings.
See [this Zulipt topic](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Quadratic.20Hilbert.20symbol.20over.20.E2.84.9A/near/285053214) for more information.
**CHANGE OF PLAN:** Following the discussion on Zulip linked to above, the lemmas in `auxiliary.lean` are supposed to be moved to there proper places. I have added suggestions to each lemma or group of lemmas (or definitions) what the proper place could be (in some cases, there are alternatives). Please comment if you do not agree or to support one of the alternatives.
#### Estimated changes
Modified src/algebra/char_p/basic.lean
- \+ *lemma* int.cast_inj_on_of_ring_char_ne_two
- \+ *lemma* is_square_of_char_two'
- \+ *lemma* ring.eq_self_iff_eq_zero_of_char_ne_two
- \+ *lemma* ring.neg_one_ne_one_of_char_ne_two
- \+ *lemma* ring.two_ne_zero

Added src/algebra/char_p/char_and_card.lean
- \+ *lemma* is_unit_iff_not_dvd_char
- \+ *lemma* not_is_unit_prime_of_dvd_card
- \+ *lemma* prime_dvd_char_iff_dvd_card

Modified src/algebra/group_power/basic.lean
- \+ *lemma* coe_pow_monoid_with_zero_hom
- \+ *lemma* pow_eq_pow_mod
- \+ *def* pow_monoid_with_zero_hom
- \+ *lemma* pow_monoid_with_zero_hom_apply

Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* monoid_with_zero.coe_inverse
- \+ *def* monoid_with_zero.inverse
- \+ *lemma* monoid_with_zero.inverse_apply

Modified src/data/nat/modeq.lean
- \+ *lemma* nat.odd_mod_four_iff

Modified src/field_theory/finite/basic.lean
- \+ *lemma* finite_field.even_card_iff_char_two
- \+ *lemma* finite_field.even_card_of_char_two
- \+ *lemma* finite_field.exists_nonsquare
- \+ *lemma* finite_field.is_square_iff
- \+ *lemma* finite_field.is_square_of_char_two
- \+ *lemma* finite_field.odd_card_of_char_ne_two
- \+ *lemma* finite_field.pow_dichotomy
- \+ *lemma* finite_field.unit_is_square_iff

Added src/field_theory/finite/trace.lean
- \+ *lemma* finite_field.trace_to_zmod_nondegenerate

Deleted src/number_theory/legendre_symbol/auxiliary.lean
- \- *lemma* finite_field.even_card_iff_char_two
- \- *lemma* finite_field.even_card_of_char_two
- \- *lemma* finite_field.exists_nonsquare
- \- *lemma* finite_field.is_square_iff
- \- *lemma* finite_field.is_square_of_char_two
- \- *lemma* finite_field.neg_ne_self_of_char_ne_two
- \- *lemma* finite_field.neg_one_ne_one_of_char_ne_two
- \- *lemma* finite_field.odd_card_of_char_ne_two
- \- *lemma* finite_field.pow_dichotomy
- \- *lemma* finite_field.unit_is_square_iff
- \- *lemma* is_square_of_char_two'
- \- *lemma* nat.odd_mod_four_iff

Modified src/number_theory/legendre_symbol/quadratic_char.lean


Modified src/number_theory/legendre_symbol/quadratic_reciprocity.lean


Modified src/number_theory/legendre_symbol/zmod_char.lean




## [2022-06-12 16:03:11](https://github.com/leanprover-community/mathlib/commit/97c9ef8)
chore(measure_theory): use notation `measurable_set[m]` ([#14690](https://github.com/leanprover-community/mathlib/pull/14690))
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measurable_space_def.lean


Modified src/measure_theory/measure/content.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/measure_theory/measure/stieltjes.lean


Modified src/measure_theory/pi_system.lean


Modified src/probability/independence.lean


Modified src/probability/integration.lean




## [2022-06-12 11:53:19](https://github.com/leanprover-community/mathlib/commit/8cad81a)
feat(data/{finset,set}/basic): More `insert` and `erase` lemmas ([#14675](https://github.com/leanprover-community/mathlib/pull/14675))
Also turn `finset.disjoint_iff_disjoint_coe` around and change `set.finite.to_finset_insert` take `(insert a s).finite` instead of `s.finite`.
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean


Modified src/data/finset/basic.lean
- \+ *lemma* finset.disjoint_coe
- \- *lemma* finset.disjoint_iff_disjoint_coe
- \+ *lemma* finset.erase_cons
- \+ *lemma* finset.erase_image_subset_image_erase
- \+ *lemma* finset.erase_inj_on'
- \+ *lemma* finset.erase_ssubset_insert
- \+ *lemma* finset.erase_subset_iff_of_mem
- \+ *lemma* finset.filter_inter_distrib
- \+/\- *lemma* finset.image_inter
- \+ *lemma* finset.image_inter_of_inj_on
- \+ *theorem* finset.pair_eq_singleton
- \- *theorem* finset.pair_self_eq
- \+ *lemma* finset.pairwise_disjoint_coe
- \+ *lemma* finset.subset_insert_iff_of_not_mem

Modified src/data/finset/pointwise.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* finset.coe_eq_univ
- \+/\- *lemma* finset.eq_univ_iff_forall
- \+ *lemma* finset.eq_univ_of_forall
- \+ *lemma* finset.image_univ_of_surjective

Modified src/data/set/basic.lean
- \+ *lemma* set.insert_idem

Modified src/data/set/finite.lean
- \+ *lemma* set.finite.to_finset_insert'
- \+/\- *lemma* set.finite.to_finset_insert
- \+ *lemma* set.finite.to_finset_singleton

Modified src/data/set/lattice.lean
- \+ *lemma* set.Inter_comm
- \- *theorem* set.Inter_comm
- \+ *lemma* set.Inter₂_comm
- \+ *lemma* set.Union_comm
- \- *theorem* set.Union_comm
- \+ *lemma* set.Union₂_comm

Modified src/group_theory/perm/cycle/basic.lean


Modified src/group_theory/perm/support.lean


Modified src/logic/basic.lean
- \+ *lemma* exists₂_comm

Modified src/order/complete_lattice.lean
- \+ *lemma* infi₂_comm
- \+ *lemma* supr₂_comm



## [2022-06-12 11:13:54](https://github.com/leanprover-community/mathlib/commit/579d6f9)
feat(data/polynomial/laurent): Laurent polynomials are a localization of polynomials ([#14489](https://github.com/leanprover-community/mathlib/pull/14489))
This PR proves the lemma `is_localization (submonoid.closure ({X} : set R[X])) R[T;T⁻¹]`.
#### Estimated changes
Modified src/data/polynomial/laurent.lean
- \+ *lemma* laurent_polynomial.algebra_map_X_pow
- \+ *lemma* laurent_polynomial.algebra_map_eq_to_laurent
- \+ *lemma* laurent_polynomial.is_localization



## [2022-06-12 08:43:37](https://github.com/leanprover-community/mathlib/commit/4a3b22e)
feat(number_theory/bernoulli_polynomials): Derivative of Bernoulli polynomial ([#14625](https://github.com/leanprover-community/mathlib/pull/14625))
Add the statement that the derivative of `bernoulli k x` is `k * bernoulli (k-1) x`. This will be used in a subsequent PR to evaluate the even positive integer values of the Riemann zeta function.
#### Estimated changes
Modified src/number_theory/bernoulli_polynomials.lean
- \+ *lemma* polynomial.derivative_bernoulli
- \+ *lemma* polynomial.derivative_bernoulli_add_one



## [2022-06-12 05:48:33](https://github.com/leanprover-community/mathlib/commit/0926f07)
feat(data/polynomial/eval): add some lemmas for `comp` ([#14346](https://github.com/leanprover-community/mathlib/pull/14346))
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.coe_comp_ring_hom
- \+ *lemma* polynomial.coe_comp_ring_hom_apply
- \+ *lemma* polynomial.list_prod_comp
- \+ *lemma* polynomial.multiset_prod_comp
- \+/\- *lemma* polynomial.prod_comp

Modified src/field_theory/abel_ruffini.lean




## [2022-06-12 05:09:43](https://github.com/leanprover-community/mathlib/commit/eb063e7)
feat(category_theory/Fintype): equiv_equiv_iso ([#13984](https://github.com/leanprover-community/mathlib/pull/13984))
From LTE.
#### Estimated changes
Modified src/category_theory/Fintype.lean
- \+ *def* Fintype.equiv_equiv_iso



## [2022-06-11 15:30:23](https://github.com/leanprover-community/mathlib/commit/053a03d)
feat(algebra/char_p): `char_p` of a local ring is zero or prime power ([#14461](https://github.com/leanprover-community/mathlib/pull/14461))
For a local commutative ring the characteristics is either zero or a prime power.
#### Estimated changes
Added src/algebra/char_p/local_ring.lean
- \+ *theorem* char_p_zero_or_prime_power

Modified src/data/nat/factorization/basic.lean
- \+ *lemma* nat.div_factorization_pos
- \+ *lemma* nat.ne_dvd_factorization_div



## [2022-06-11 14:33:12](https://github.com/leanprover-community/mathlib/commit/2e3a0a6)
feat(analysis/special_functions/log): add `real.log_sqrt` ([#14663](https://github.com/leanprover-community/mathlib/pull/14663))
#### Estimated changes
Modified src/analysis/special_functions/log/basic.lean
- \+ *lemma* real.log_sqrt



## [2022-06-11 11:06:30](https://github.com/leanprover-community/mathlib/commit/d1a6dd2)
feat(topology/algebra/module/locally_convex): local convexity is preserved by `Inf` and `induced` ([#12118](https://github.com/leanprover-community/mathlib/pull/12118))
I also generalized slightly `locally_convex_space.of_bases` and changed a `Sort*` to `Type*` in `filter.has_basis_infi` to correctly reflect the universe constraints.
#### Estimated changes
Modified src/order/filter/bases.lean
- \+/\- *lemma* filter.has_basis_infi

Modified src/topology/algebra/module/locally_convex.lean
- \+/\- *lemma* locally_convex_space.of_bases
- \+ *lemma* locally_convex_space_Inf
- \+ *lemma* locally_convex_space_induced
- \+ *lemma* locally_convex_space_inf
- \+ *lemma* locally_convex_space_infi



## [2022-06-11 08:59:36](https://github.com/leanprover-community/mathlib/commit/13b999c)
feat(algebra/{group,hom}/units): Units in division monoids ([#14212](https://github.com/leanprover-community/mathlib/pull/14212))
Copy over `group_with_zero` lemmas to the more general setting of `division_monoid`.
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* is_unit.mul_left_inj
- \- *theorem* is_unit.mul_left_inj
- \+ *lemma* is_unit.mul_right_inj
- \- *theorem* is_unit.mul_right_inj
- \- *lemma* units.eq_iff_inv_mul
- \- *lemma* units.inv_eq_of_mul_eq_one_right
- \+ *lemma* units.inv_mul_eq_one
- \+/\- *lemma* units.inv_mul_of_eq
- \+ *lemma* units.mul_eq_one_iff_eq_inv
- \+ *lemma* units.mul_eq_one_iff_inv_eq
- \+ *lemma* units.mul_inv_eq_one
- \+/\- *lemma* units.mul_inv_of_eq

Modified src/algebra/group_with_zero/basic.lean
- \- *theorem* divp_eq_div

Modified src/algebra/hom/units.lean
- \+ *lemma* divp_eq_div
- \+/\- *lemma* is_unit.coe_lift_right
- \+ *lemma* is_unit.div
- \+ *lemma* is_unit.inv
- \+/\- *lemma* is_unit.lift_right_inv_mul
- \+/\- *lemma* is_unit.map
- \+/\- *lemma* is_unit.mul_lift_right_inv
- \+ *def* is_unit.unit'

Modified src/ring_theory/ideal/local_ring.lean




## [2022-06-11 02:10:15](https://github.com/leanprover-community/mathlib/commit/050404a)
feat(group_theory/sylow): Sylow subgroups are Hall subgroups ([#14624](https://github.com/leanprover-community/mathlib/pull/14624))
This PR adds a lemma stating that Sylow subgroups are Hall subgroups (cardinality is coprime to index).
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *lemma* sylow.card_coprime_index



## [2022-06-10 14:50:29](https://github.com/leanprover-community/mathlib/commit/18936e5)
feat(topology/uniform_space/equiv): define uniform isomorphisms ([#14537](https://github.com/leanprover-community/mathlib/pull/14537))
This adds a new file, mostly copy-pasted from `topology/homeomorph`, to analogously define uniform isomorphisms
#### Estimated changes
Modified src/data/prod/basic.lean
- \+/\- *lemma* prod.id_prod
- \+ *lemma* prod.map_id

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* uniform_continuous_subtype_coe

Added src/topology/uniform_space/equiv.lean
- \+ *def* equiv.to_uniform_equiv_of_uniform_inducing
- \+ *lemma* uniform_equiv.apply_symm_apply
- \+ *def* uniform_equiv.change_inv
- \+ *lemma* uniform_equiv.coe_prod_comm
- \+ *lemma* uniform_equiv.coe_prod_congr
- \+ *lemma* uniform_equiv.coe_punit_prod
- \+ *lemma* uniform_equiv.coe_symm_to_equiv
- \+ *lemma* uniform_equiv.coe_to_equiv
- \+ *lemma* uniform_equiv.comap_eq
- \+ *lemma* uniform_equiv.ext
- \+ *def* uniform_equiv.fin_two_arrow
- \+ *def* uniform_equiv.fun_unique
- \+ *def* uniform_equiv.image
- \+ *lemma* uniform_equiv.image_preimage
- \+ *lemma* uniform_equiv.image_symm
- \+ *lemma* uniform_equiv.preimage_image
- \+ *lemma* uniform_equiv.preimage_symm
- \+ *def* uniform_equiv.prod_assoc
- \+ *def* uniform_equiv.prod_comm
- \+ *lemma* uniform_equiv.prod_comm_symm
- \+ *def* uniform_equiv.prod_congr
- \+ *lemma* uniform_equiv.prod_congr_symm
- \+ *def* uniform_equiv.prod_punit
- \+ *def* uniform_equiv.punit_prod
- \+ *lemma* uniform_equiv.range_coe
- \+ *lemma* uniform_equiv.refl_symm
- \+ *lemma* uniform_equiv.self_comp_symm
- \+ *def* uniform_equiv.set_congr
- \+ *def* uniform_equiv.simps.apply
- \+ *def* uniform_equiv.simps.symm_apply
- \+ *lemma* uniform_equiv.symm_apply_apply
- \+ *lemma* uniform_equiv.symm_comp_self
- \+ *lemma* uniform_equiv.to_equiv_injective
- \+ *lemma* uniform_equiv.trans_apply
- \+ *lemma* uniform_equiv.uniform_equiv_mk_coe
- \+ *lemma* uniform_equiv.uniform_equiv_mk_coe_symm
- \+ *def* uniform_equiv.{u}
- \+ *structure* uniform_equiv

Modified src/topology/uniform_space/uniform_embedding.lean
- \+ *lemma* uniform_inducing_id
- \+ *lemma* uniform_inducing_of_compose



## [2022-06-10 12:55:31](https://github.com/leanprover-community/mathlib/commit/8c812fd)
feat(topology/algebra/order): `coe : ℚ → 𝕜` has dense range ([#14635](https://github.com/leanprover-community/mathlib/pull/14635))
* add `rat.dense_range_cast`, use it in `rat.dense_embedding_coe_real`;
* rename `dense_iff_forall_lt_exists_mem` to `dense_iff_exists_between`;
* add `dense_of_exists_between`, use it in `dense_iff_exists_between`.
#### Estimated changes
Added src/topology/algebra/order/archimedean.lean
- \+ *lemma* rat.dense_range_cast

Modified src/topology/algebra/order/basic.lean
- \+ *lemma* dense_iff_exists_between
- \- *lemma* dense_iff_forall_lt_exists_mem
- \+ *lemma* dense_of_exists_between

Modified src/topology/basic.lean


Modified src/topology/instances/rat.lean




## [2022-06-10 12:55:30](https://github.com/leanprover-community/mathlib/commit/0f5a1f2)
feat(data/rat): Add some lemmas to work with num/denom ([#14456](https://github.com/leanprover-community/mathlib/pull/14456))
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *lemma* rat.add_num_denom'
- \+ *lemma* rat.coe_int_div_eq_mk
- \+ *lemma* rat.mk_div_mk_cancel_left
- \+ *lemma* rat.mk_div_mk_cancel_right
- \+ *lemma* rat.mk_mul_mk_cancel
- \+ *lemma* rat.mul_num_denom'
- \+ *lemma* rat.substr_num_denom'



## [2022-06-10 10:43:10](https://github.com/leanprover-community/mathlib/commit/95da649)
feat(analysis/inner_product_space): Generalize Gram-Schmidt ([#14379](https://github.com/leanprover-community/mathlib/pull/14379))
The generalisation is to allow a family of vectors indexed by a general indexing set `ι` (carrying appropriate order typeclasses) rather than just `ℕ`.
#### Estimated changes
Modified src/analysis/box_integral/partition/basic.lean


Modified src/analysis/box_integral/partition/tagged.lean


Modified src/analysis/inner_product_space/gram_schmidt_ortho.lean
- \+/\- *lemma* gram_schmidt_def'
- \+/\- *lemma* gram_schmidt_def
- \- *lemma* gram_schmidt_ne_zero'
- \+/\- *lemma* gram_schmidt_ne_zero
- \+ *lemma* gram_schmidt_ne_zero_coe
- \- *lemma* gram_schmidt_normed_unit_length'
- \+/\- *lemma* gram_schmidt_normed_unit_length
- \+ *lemma* gram_schmidt_normed_unit_length_coe
- \+/\- *theorem* gram_schmidt_orthogonal
- \+/\- *theorem* gram_schmidt_orthonormal
- \+/\- *theorem* gram_schmidt_pairwise_orthogonal
- \+/\- *lemma* gram_schmidt_zero
- \+/\- *lemma* span_gram_schmidt

Modified src/data/finset/lattice.lean
- \- *lemma* finset.sup_le_iff

Modified src/data/finset/powerset.lean


Modified src/order/rel_classes.lean
- \+ *def* is_well_order.to_has_well_founded

Modified src/order/succ_pred/basic.lean
- \+ *lemma* order.Ioi_pred_eq_insert_of_not_is_min



## [2022-06-10 10:04:50](https://github.com/leanprover-community/mathlib/commit/391d178)
feat(set_theory/game/ordinal): golf `to_pgame_injective` ([#14661](https://github.com/leanprover-community/mathlib/pull/14661))
We also add the `eq_iff` version and remove an outdated todo comment.
#### Estimated changes
Modified src/set_theory/game/ordinal.lean
- \+ *theorem* ordinal.to_pgame_eq_iff

Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.equiv_of_eq



## [2022-06-10 10:04:49](https://github.com/leanprover-community/mathlib/commit/68dc07f)
refactor(set_theory/game/pgame): rename and add theorems like `-y ≤ -x ↔ x ≤ y` ([#14653](https://github.com/leanprover-community/mathlib/pull/14653))
For `*` in `le`, `lf`, `lt`, we rename `neg_*_iff : -y * -x ↔ x * y` to `neg_*_neg_iff`, and add the theorems `neg_*_iff : -y * x ↔ x * -y`.
We further add many missing corresponding theorems for equivalence and fuzziness.
#### Estimated changes
Modified src/set_theory/game/basic.lean


Modified src/set_theory/game/birthday.lean


Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.le_neg_iff
- \+ *theorem* pgame.lf_neg_iff
- \+ *theorem* pgame.lt_neg_iff
- \- *theorem* pgame.neg_congr
- \+ *theorem* pgame.neg_equiv_iff
- \+ *theorem* pgame.neg_equiv_neg_iff
- \+ *theorem* pgame.neg_equiv_zero_iff
- \+ *theorem* pgame.neg_fuzzy_iff
- \+ *theorem* pgame.neg_fuzzy_neg_iff
- \+ *theorem* pgame.neg_fuzzy_zero_iff
- \+/\- *theorem* pgame.neg_le_iff
- \+ *theorem* pgame.neg_le_neg_iff
- \+/\- *theorem* pgame.neg_lf_iff
- \+ *theorem* pgame.neg_lf_neg_iff
- \+/\- *theorem* pgame.neg_lt_iff
- \+ *theorem* pgame.neg_lt_neg_iff
- \+ *theorem* pgame.zero_equiv_neg_iff
- \+ *theorem* pgame.zero_fuzzy_neg_iff

Modified src/set_theory/surreal/basic.lean




## [2022-06-10 07:36:57](https://github.com/leanprover-community/mathlib/commit/a912392)
feat(data/fintype/basic): add `card_subtype_mono` ([#14645](https://github.com/leanprover-community/mathlib/pull/14645))
This lemma naturally forms a counterpart to existing lemmas.
I've also renamed a lemma it uses that didn't seem to fit the existing naming pattern.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *theorem* card_subtype_mono



## [2022-06-10 07:36:56](https://github.com/leanprover-community/mathlib/commit/771f2b7)
chore(topology/metric_space/basic): add `metric_space.replace_bornology` ([#14638](https://github.com/leanprover-community/mathlib/pull/14638))
We have the `pseudo_metric_space` version from [#13927](https://github.com/leanprover-community/mathlib/pull/13927), but not the `metric_space` version.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *def* metric_space.replace_bornology
- \+ *lemma* metric_space.replace_bornology_eq



## [2022-06-10 07:36:55](https://github.com/leanprover-community/mathlib/commit/5bccb51)
refactor(logic/equiv/basic): tweak lemmas on equivalences between `unique` types ([#14605](https://github.com/leanprover-community/mathlib/pull/14605))
This PR does various simple and highly related things:
- Rename `equiv_of_unique_of_unique` to `equiv_of_unique` and make its arguments explicit, in order to match the lemma `equiv_of_empty` added in [#14604](https://github.com/leanprover-community/mathlib/pull/14604).  
- Rename `equiv_punit_of_unique` to `equiv_punit` and make its argument explicit to match `equiv_pempty`.
- Fix their docstrings (which talked about a `subsingleton` type instead of a `unique` one).
- Move them much earlier in the file, together with the lemmas on empty types.
- Golf `prop_equiv_punit`.
#### Estimated changes
Modified src/algebra/hom/equiv.lean


Modified src/group_theory/perm/cycle/type.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/logic/equiv/basic.lean
- \+ *def* equiv.equiv_of_unique
- \+ *def* equiv.equiv_punit
- \- *def* equiv.true_equiv_punit
- \- *def* equiv_of_unique_of_unique
- \- *def* equiv_punit_of_unique

Modified src/logic/equiv/fin.lean


Modified src/measure_theory/measurable_space.lean


Modified src/set_theory/cardinal/basic.lean


Modified src/set_theory/game/nim.lean




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
Modified src/data/polynomial/derivative.lean
- \+/\- *lemma* polynomial.degree_derivative_eq
- \+/\- *theorem* polynomial.derivative_map
- \+/\- *theorem* polynomial.iterate_derivative_map
- \+/\- *lemma* polynomial.mem_support_derivative



## [2022-06-10 07:36:52](https://github.com/leanprover-community/mathlib/commit/39184f4)
feat(dynamics/periodic_pts): Orbit under periodic function ([#12976](https://github.com/leanprover-community/mathlib/pull/12976))
#### Estimated changes
Modified src/dynamics/periodic_pts.lean
- \+ *lemma* function.eq_iff_lt_minimal_period_of_iterate_eq
- \+ *lemma* function.eq_of_lt_minimal_period_of_iterate_eq
- \+/\- *lemma* function.is_periodic_pt.minimal_period_dvd
- \+/\- *lemma* function.is_periodic_pt_iff_minimal_period_dvd
- \+/\- *lemma* function.is_periodic_pt_minimal_period
- \+ *lemma* function.iterate_add_minimal_period_eq
- \- *lemma* function.iterate_eq_mod_minimal_period
- \- *lemma* function.iterate_injective_of_lt_minimal_period
- \+ *lemma* function.iterate_mem_periodic_orbit
- \+/\- *lemma* function.iterate_minimal_period
- \+ *lemma* function.iterate_mod_minimal_period_eq
- \+ *lemma* function.le_of_lt_minimal_period_of_iterate_eq
- \+ *lemma* function.mem_periodic_orbit_iff
- \+ *lemma* function.minimal_period_apply
- \+ *lemma* function.minimal_period_apply_iterate
- \+ *lemma* function.minimal_period_eq_zero_iff_nmem_periodic_pts
- \+ *lemma* function.minimal_period_eq_zero_of_nmem_periodic_pts
- \+ *lemma* function.nodup_periodic_orbit
- \+ *def* function.periodic_orbit
- \+ *lemma* function.periodic_orbit_apply_eq
- \+ *lemma* function.periodic_orbit_apply_iterate_eq
- \+ *lemma* function.periodic_orbit_def
- \+ *lemma* function.periodic_orbit_eq_cycle_map
- \+ *lemma* function.periodic_orbit_eq_nil_iff_not_periodic_pt
- \+ *lemma* function.periodic_orbit_eq_nil_of_not_periodic_pt
- \+ *lemma* function.periodic_orbit_length
- \+ *lemma* function.self_mem_periodic_orbit

Modified src/group_theory/order_of_element.lean




## [2022-06-10 05:26:20](https://github.com/leanprover-community/mathlib/commit/e3dade3)
feat(data/finite/basic): `finite` predicate ([#14373](https://github.com/leanprover-community/mathlib/pull/14373))
Introduces a `Prop`-valued finiteness predicate on types and adapts some subset of the `fintype` API to get started. Uses `nat.card` as the primary cardinality function.
#### Estimated changes
Added src/data/finite/basic.lean
- \+ *lemma* equiv.finite_iff
- \+ *lemma* finite.card_eq
- \+ *lemma* finite.card_eq_zero_iff
- \+ *lemma* finite.card_le_of_embedding
- \+ *lemma* finite.card_le_of_injective
- \+ *lemma* finite.card_le_of_surjective
- \+ *lemma* finite.card_le_one_iff_subsingleton
- \+ *lemma* finite.card_option
- \+ *lemma* finite.card_pos_iff
- \+ *theorem* finite.card_subtype_le
- \+ *theorem* finite.card_subtype_lt
- \+ *lemma* finite.card_sum
- \+ *def* finite.equiv_fin
- \+ *def* finite.equiv_fin_of_card_eq
- \+ *lemma* finite.exists_equiv_fin
- \+ *lemma* finite.exists_max
- \+ *lemma* finite.exists_min
- \+ *lemma* finite.of_bijective
- \+ *lemma* finite.of_equiv
- \+ *lemma* finite.of_fintype
- \+ *lemma* finite.of_injective
- \+ *lemma* finite.of_not_infinite
- \+ *lemma* finite.of_surjective
- \+ *lemma* finite.one_lt_card
- \+ *lemma* finite.one_lt_card_iff_nontrivial
- \+ *lemma* finite.prod_left
- \+ *lemma* finite.prod_right
- \+ *lemma* finite.sum_left
- \+ *lemma* finite.sum_right
- \+ *lemma* finite_iff_nonempty_fintype
- \+ *lemma* finite_or_infinite
- \+ *def* fintype.of_finite
- \+ *lemma* infinite.of_not_finite
- \+ *lemma* nat.card_eq
- \+ *lemma* not_finite
- \+ *lemma* not_finite_iff_infinite
- \+ *lemma* not_infinite_iff_finite
- \+ *lemma* of_subsingleton

Modified src/data/nat/totient.lean


Modified src/logic/unique.lean
- \+ *lemma* unique_iff_subsingleton_and_nonempty

Modified src/set_theory/cardinal/finite.lean
- \+ *lemma* nat.card_congr
- \+ *lemma* nat.card_eq_of_bijective
- \+ *lemma* nat.card_eq_of_equiv_fin
- \+ *lemma* nat.card_eq_one_iff_unique
- \+ *theorem* nat.card_of_is_empty
- \+ *lemma* nat.card_of_subsingleton
- \+ *lemma* nat.card_plift
- \+ *lemma* nat.card_prod
- \+ *lemma* nat.card_ulift
- \+ *lemma* nat.card_unique
- \+ *def* nat.equiv_fin_of_card_pos



## [2022-06-10 04:32:43](https://github.com/leanprover-community/mathlib/commit/e9d2564)
chore(measure_theory): golf ([#14657](https://github.com/leanprover-community/mathlib/pull/14657))
Also use `@measurable_set α m s` instead of `m.measurable_set' s` in the definition of the partial order on `measurable_space`. This way we can use dot notation lemmas about measurable sets in a proof of `m₁ ≤ m₂`.
#### Estimated changes
Modified src/measure_theory/measurable_space_def.lean


Modified src/measure_theory/measure/measure_space_def.lean




## [2022-06-10 02:04:07](https://github.com/leanprover-community/mathlib/commit/ed2cfce)
feat(set_theory/ordinal/basic): tweak theorems on order type of empty relation ([#14650](https://github.com/leanprover-community/mathlib/pull/14650))
We move the theorems on the order type of an empty relation much earlier, and golf them. We also remove other redundant theorems.
`zero_eq_type_empty` is made redundant by `type_eq_zero_of_empty`, while `zero_eq_lift_type_empty`  is made redundant by the former lemma and `lift_zero`.
#### Estimated changes
Modified src/order/rel_iso.lean
- \+ *def* rel_iso.rel_iso_of_is_empty

Modified src/set_theory/ordinal/arithmetic.lean
- \- *theorem* ordinal.type_eq_zero_iff_is_empty
- \- *theorem* ordinal.type_eq_zero_of_empty
- \- *theorem* ordinal.type_ne_zero_iff_nonempty

Modified src/set_theory/ordinal/basic.lean
- \+ *theorem* ordinal.type_eq_zero_iff_is_empty
- \+ *theorem* ordinal.type_eq_zero_of_empty
- \+ *theorem* ordinal.type_ne_zero_iff_nonempty
- \+ *theorem* ordinal.type_ne_zero_of_nonempty
- \- *theorem* ordinal.zero_eq_lift_type_empty
- \- *theorem* ordinal.zero_eq_type_empty



## [2022-06-09 23:59:52](https://github.com/leanprover-community/mathlib/commit/2cf4746)
chore(analysis/special_functions/gamma): tidy some proofs ([#14615](https://github.com/leanprover-community/mathlib/pull/14615))
#### Estimated changes
Modified src/analysis/special_functions/gamma.lean




## [2022-06-09 23:59:51](https://github.com/leanprover-community/mathlib/commit/3afb1fa)
feat(ci): Add support for "notice"-level messages ([#14443](https://github.com/leanprover-community/mathlib/pull/14443))
It looks like support for this was added recently, it's now documented at the same link already in our source code.
#### Estimated changes
Modified scripts/detect_errors.py




## [2022-06-09 22:24:53](https://github.com/leanprover-community/mathlib/commit/6e13617)
feat(set_theory/ordinal/basic): better definitions for `0` and `1` ([#14651](https://github.com/leanprover-community/mathlib/pull/14651))
We define the `0` and `1` ordinals as the order types of the empty relation on `pempty` and `punit`, respectively. These definitions are definitionally equal to the previous ones, yet much clearer, for two reasons:
- They don't make use of the auxiliary `Well_order` type. 
- Much of the basic API for these ordinals uses this def-eq anyways.
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean




## [2022-06-09 22:24:52](https://github.com/leanprover-community/mathlib/commit/c89d319)
feat(set_theory/cardinal): add `cardinal.aleph_0_le_mul_iff'` ([#14648](https://github.com/leanprover-community/mathlib/pull/14648))
This version provides a more useful `iff.mpr`. Also review 2 proofs.
#### Estimated changes
Modified src/set_theory/cardinal/basic.lean
- \+ *lemma* cardinal.aleph_0_le_mul_iff'



## [2022-06-09 22:24:51](https://github.com/leanprover-community/mathlib/commit/405be36)
feat(data/matrix): Lemmas about `vec_mul`, `mul_vec`, `dot_product`, `inv` ([#14644](https://github.com/leanprover-community/mathlib/pull/14644))
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *lemma* matrix.dot_product_assoc
- \+ *lemma* matrix.mul_vec_vec_mul
- \+ *lemma* matrix.sub_mul_vec
- \+ *lemma* matrix.sum_elim_dot_product_sum_elim
- \+ *lemma* matrix.vec_mul_mul_vec
- \+ *lemma* matrix.vec_mul_sub

Modified src/data/matrix/block.lean
- \+ *lemma* matrix.from_blocks_mul_vec
- \+ *lemma* matrix.vec_mul_from_blocks

Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* matrix.inv_mul_cancel_left_of_invertible
- \+ *lemma* matrix.inv_mul_cancel_right_of_invertible
- \+ *lemma* matrix.mul_inv_cancel_left_of_invertible
- \+ *lemma* matrix.mul_inv_cancel_right_of_invertible
- \+ *lemma* matrix.mul_nonsing_inv_cancel_left
- \+ *lemma* matrix.mul_nonsing_inv_cancel_right
- \+ *lemma* matrix.nonsing_inv_mul_cancel_left
- \+ *lemma* matrix.nonsing_inv_mul_cancel_right



## [2022-06-09 22:24:50](https://github.com/leanprover-community/mathlib/commit/3e458e2)
chore(topology/sequences): rename variables ([#14631](https://github.com/leanprover-community/mathlib/pull/14631))
* types `X`, `Y`;
* sequence `x : ℕ → X`;
* a point `a : X`;
* sets `s`, `t`.
#### Estimated changes
Modified src/topology/sequences.lean
- \+/\- *lemma* compact_space.tendsto_subseq
- \+/\- *lemma* continuous_iff_seq_continuous
- \+/\- *lemma* is_closed.is_seq_closed
- \+/\- *lemma* is_compact.is_seq_compact
- \+/\- *lemma* is_compact.tendsto_subseq'
- \+/\- *lemma* is_compact.tendsto_subseq
- \+/\- *lemma* is_seq_closed.mem_of_tendsto
- \+/\- *def* is_seq_closed
- \+/\- *lemma* is_seq_closed_iff_is_closed
- \+/\- *lemma* is_seq_closed_of_def
- \+/\- *lemma* is_seq_compact.subseq_of_frequently_in
- \+/\- *def* is_seq_compact
- \+/\- *lemma* lebesgue_number_lemma_seq
- \+/\- *lemma* mem_closure_iff_seq_limit
- \+/\- *def* seq_closure
- \+/\- *lemma* seq_closure_subset_closure
- \+/\- *lemma* seq_compact.lebesgue_number_lemma_of_metric
- \+/\- *lemma* seq_compact_space.tendsto_subseq
- \+/\- *def* seq_continuous
- \+/\- *lemma* subset_seq_closure
- \+/\- *lemma* tendsto_subseq_of_bounded
- \+/\- *lemma* uniform_space.compact_space_iff_seq_compact_space



## [2022-06-09 19:45:28](https://github.com/leanprover-community/mathlib/commit/81ab992)
chore(set_theory/cardinal/basic): tidy lt_wf proof ([#14574](https://github.com/leanprover-community/mathlib/pull/14574))
#### Estimated changes
Modified src/set_theory/cardinal/basic.lean




## [2022-06-09 19:45:27](https://github.com/leanprover-community/mathlib/commit/34a9d0d)
feat(algebra/order/ring): Binary rearrangement inequality ([#14478](https://github.com/leanprover-community/mathlib/pull/14478))
Extract the binary case of the rearrangement inequality (`a * d + b * c ≤ a * c + b * d` if `a ≤ b` and `c ≤ d`) from the general one.
#### Estimated changes
Modified src/algebra/order/module.lean
- \+ *lemma* smul_add_smul_le_smul_add_smul'
- \+ *lemma* smul_add_smul_le_smul_add_smul
- \+ *lemma* smul_add_smul_lt_smul_add_smul'
- \+ *lemma* smul_add_smul_lt_smul_add_smul

Modified src/algebra/order/rearrangement.lean


Modified src/algebra/order/ring.lean
- \+ *lemma* mul_add_mul_le_mul_add_mul'
- \+ *lemma* mul_add_mul_le_mul_add_mul
- \+ *lemma* mul_add_mul_lt_mul_add_mul'
- \+ *lemma* mul_add_mul_lt_mul_add_mul



## [2022-06-09 19:45:25](https://github.com/leanprover-community/mathlib/commit/7fbff0f)
feat(data/nat/choose/central): arity of primes in central binomial coefficients ([#14017](https://github.com/leanprover-community/mathlib/pull/14017))
Spun off of [#8002](https://github.com/leanprover-community/mathlib/pull/8002). Lemmas about the arity of primes in central binomial coefficients.
#### Estimated changes
Modified docs/references.bib


Modified src/data/nat/choose/central.lean
- \- *lemma* nat.padic_val_nat_central_binom_le
- \- *lemma* nat.padic_val_nat_central_binom_of_large_eq_zero
- \- *lemma* nat.padic_val_nat_central_binom_of_large_le_one

Added src/data/nat/choose/factorization.lean
- \+ *lemma* nat.factorization_central_binom_eq_zero_of_two_mul_lt
- \+ *lemma* nat.factorization_central_binom_of_two_mul_self_lt_three_mul
- \+ *lemma* nat.factorization_choose_eq_zero_of_lt
- \+ *lemma* nat.factorization_choose_le_log
- \+ *lemma* nat.factorization_choose_le_one
- \+ *lemma* nat.factorization_choose_of_lt_three_mul
- \+ *lemma* nat.factorization_factorial_eq_zero_of_lt
- \+ *lemma* nat.le_two_mul_of_factorization_central_binom_pos
- \+ *lemma* nat.pow_factorization_choose_le

Modified src/data/nat/factorization/basic.lean
- \+ *lemma* nat.factorization_eq_zero_of_lt



## [2022-06-09 18:12:47](https://github.com/leanprover-community/mathlib/commit/4d4de43)
chore(ring_theory/unique_factorization_domain): drop simp annotation for factors_pow ([#14646](https://github.com/leanprover-community/mathlib/pull/14646))
Followup to https://github.com/leanprover-community/mathlib/pull/14555.
#### Estimated changes
Modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *lemma* unique_factorization_monoid.factors_pow



## [2022-06-09 18:12:46](https://github.com/leanprover-community/mathlib/commit/7b4680f)
feat(analysis/inner_product_space/pi_L2): Distance formula in the euclidean space ([#14642](https://github.com/leanprover-community/mathlib/pull/14642))
A few missing results about `pi_Lp 2` and `euclidean_space`.
#### Estimated changes
Modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* euclidean_space.dist_eq
- \+ *lemma* euclidean_space.edist_eq
- \+ *lemma* euclidean_space.nndist_eq

Modified src/analysis/normed_space/pi_Lp.lean
- \+ *lemma* pi_Lp.dist_eq_of_L2
- \+ *lemma* pi_Lp.edist_eq_of_L2
- \+ *lemma* pi_Lp.nndist_eq_of_L2



## [2022-06-09 18:12:45](https://github.com/leanprover-community/mathlib/commit/ac0ce64)
feat(special_functions/integrals): exponential of complex multiple of x ([#14623](https://github.com/leanprover-community/mathlib/pull/14623))
We add an integral for `exp (c * x)` for `c` complex (so this cannot be reduced to integration of `exp x` on the real line). This is useful for Fourier series.
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* integral_exp_mul_complex



## [2022-06-09 15:38:27](https://github.com/leanprover-community/mathlib/commit/abee649)
feat(data/set/intervals): add lemmas about unions of intervals ([#14636](https://github.com/leanprover-community/mathlib/pull/14636))
#### Estimated changes
Modified src/data/set/intervals/disjoint.lean
- \+ *lemma* set.Union_Icc_left
- \+ *lemma* set.Union_Icc_right
- \+ *lemma* set.Union_Ici
- \+ *lemma* set.Union_Ico_left
- \+ *lemma* set.Union_Ico_right
- \+ *lemma* set.Union_Iic
- \+ *lemma* set.Union_Iio
- \+ *lemma* set.Union_Ioc_left
- \+ *lemma* set.Union_Ioc_right
- \+ *lemma* set.Union_Ioi
- \+ *lemma* set.Union_Ioo_left
- \+ *lemma* set.Union_Ioo_right

Modified src/data/set/lattice.lean
- \+ *theorem* set.Inter_union



## [2022-06-09 15:38:26](https://github.com/leanprover-community/mathlib/commit/e0f3ea3)
feat(topology/constructions): add `subtype.dense_iff` ([#14632](https://github.com/leanprover-community/mathlib/pull/14632))
Also add `inducing.dense_iff`.
#### Estimated changes
Modified src/topology/constructions.lean
- \+ *lemma* subtype.dense_iff

Modified src/topology/maps.lean
- \+ *lemma* inducing.dense_iff



## [2022-06-09 15:38:25](https://github.com/leanprover-community/mathlib/commit/48f557d)
chore(analysis/convex/integral): use `variables` ([#14592](https://github.com/leanprover-community/mathlib/pull/14592))
* Move some implicit arguments to `variables`.
* Move `ae_eq_const_or_exists_average_ne_compl` to the root namespace.
* Add `ae_eq_const_or_norm_set_integral_lt_of_norm_le_const`.
#### Estimated changes
Modified src/analysis/convex/integral.lean
- \+ *lemma* ae_eq_const_or_exists_average_ne_compl
- \+ *lemma* ae_eq_const_or_norm_set_integral_lt_of_norm_le_const
- \+/\- *lemma* concave_on.average_mem_hypograph
- \+/\- *lemma* concave_on.le_map_average
- \+/\- *lemma* concave_on.le_map_integral
- \+/\- *lemma* concave_on.le_map_set_average
- \+/\- *lemma* concave_on.set_average_mem_hypograph
- \+/\- *lemma* convex.average_mem
- \+/\- *lemma* convex.average_mem_interior_of_set
- \+/\- *lemma* convex.integral_mem
- \+/\- *lemma* convex.set_average_mem
- \+/\- *lemma* convex.set_average_mem_closure
- \+/\- *lemma* convex_on.average_mem_epigraph
- \+/\- *lemma* convex_on.map_average_le
- \+/\- *lemma* convex_on.map_integral_le
- \+/\- *lemma* convex_on.map_set_average_le
- \+/\- *lemma* convex_on.set_average_mem_epigraph
- \- *lemma* measure_theory.integrable.ae_eq_const_or_exists_average_ne_compl
- \+/\- *lemma* strict_concave_on.ae_eq_const_or_lt_map_average
- \+/\- *lemma* strict_convex.ae_eq_const_or_average_mem_interior
- \+/\- *lemma* strict_convex_on.ae_eq_const_or_map_average_lt



## [2022-06-09 13:27:25](https://github.com/leanprover-community/mathlib/commit/c0b3ed7)
feat(number_theory/padics/padic_val): add `padic_val_nat_def'` and generalise `pow_padic_val_nat_dvd` ([#14637](https://github.com/leanprover-community/mathlib/pull/14637))
add `padic_val_nat_def' (hn : 0 < n) (hp : p ≠ 1) : ↑(padic_val_nat p n) = multiplicity p n`
`pow_padic_val_nat_dvd : p ^ (padic_val_nat p n) ∣ n` holds without the assumption that `p` is prime.
#### Estimated changes
Modified src/number_theory/padics/padic_val.lean
- \+ *lemma* padic_val_nat_def'
- \+/\- *lemma* pow_padic_val_nat_dvd
- \+/\- *lemma* range_pow_padic_val_nat_subset_divisors



## [2022-06-09 13:27:23](https://github.com/leanprover-community/mathlib/commit/dc766dd)
refactor(group_theory/sylow): Golf proof of `pow_dvd_card_of_pow_dvd_card` ([#14622](https://github.com/leanprover-community/mathlib/pull/14622))
This PR golfs the proof of `pow_dvd_card_of_pow_dvd_card`.
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+/\- *lemma* sylow.pow_dvd_card_of_pow_dvd_card



## [2022-06-09 13:27:22](https://github.com/leanprover-community/mathlib/commit/cde6e63)
feat(analysis/seminorm): removed unnecessary `norm_one_class` arguments ([#14614](https://github.com/leanprover-community/mathlib/pull/14614))
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+/\- *lemma* balanced_ball_zero
- \+/\- *lemma* seminorm.le_insert'
- \+/\- *lemma* seminorm.le_insert
- \+/\- *lemma* seminorm.nonneg
- \+/\- *lemma* seminorm.sub_rev



## [2022-06-09 13:27:21](https://github.com/leanprover-community/mathlib/commit/d997baa)
refactor(logic/equiv/basic): remove `fin_equiv_subtype` ([#14603](https://github.com/leanprover-community/mathlib/pull/14603))
The types `fin n` and `{m // m < n}` are definitionally equal, so it doesn't make sense to have a dedicated equivalence between them (other than `equiv.refl`). We remove this equivalence and golf the places where it was used.
#### Estimated changes
Modified src/computability/primrec.lean


Modified src/data/fintype/card.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/logic/encodable/basic.lean


Modified src/logic/equiv/basic.lean
- \- *def* equiv.fin_equiv_subtype



## [2022-06-09 13:27:20](https://github.com/leanprover-community/mathlib/commit/c2bb59e)
feat(algebra/module/torsion.lean): various lemmas about torsion modules ([#14573](https://github.com/leanprover-community/mathlib/pull/14573))
An intermediate PR for various lemmas about torsion modules needed at [#13524](https://github.com/leanprover-community/mathlib/pull/13524)
#### Estimated changes
Modified src/algebra/module/torsion.lean
- \+ *lemma* ideal.mem_torsion_of_iff
- \+ *lemma* ideal.quot_torsion_of_equiv_span_singleton_apply_mk
- \+ *lemma* ideal.sup_eq_top_iff_is_coprime
- \+ *def* ideal.torsion_of
- \- *lemma* mem_torsion_of_iff
- \+ *lemma* module.is_torsion_by_iff_torsion_by_eq_top
- \+ *lemma* module.is_torsion_by_set_iff_is_torsion_by_span
- \+ *lemma* module.is_torsion_by_set_iff_torsion_by_set_eq_top
- \+ *lemma* module.is_torsion_by_singleton_iff
- \+ *lemma* module.is_torsion_by_span_singleton_iff
- \- *lemma* quot_torsion_of_equiv_span_singleton_apply_mk
- \+ *lemma* submodule.exists_is_torsion_by
- \+ *lemma* submodule.is_torsion_by_ideal_of_finite_of_is_torsion
- \- *lemma* submodule.is_torsion_by_iff_torsion_by_eq_top
- \- *lemma* submodule.is_torsion_by_set_iff_is_torsion_by_span
- \- *lemma* submodule.is_torsion_by_set_iff_torsion_by_set_eq_top
- \- *lemma* submodule.is_torsion_by_singleton_iff
- \- *lemma* submodule.is_torsion_by_span_singleton_iff
- \+ *def* submodule.p_order
- \+ *lemma* submodule.pow_p_order_smul
- \+ *lemma* submodule.sup_indep_torsion_by
- \+ *lemma* submodule.sup_indep_torsion_by_ideal
- \+ *lemma* submodule.supr_torsion_by_ideal_eq_torsion_by_infi
- \- *lemma* submodule.torsion_by_independent
- \+ *lemma* submodule.torsion_by_is_internal
- \+ *lemma* submodule.torsion_by_set_is_internal
- \+ *lemma* submodule.torsion_gc
- \- *lemma* submodule.torsion_is_internal
- \- *def* torsion_of

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.prod_mem_prod



## [2022-06-09 13:27:19](https://github.com/leanprover-community/mathlib/commit/dfc54a3)
feat(combinatorics/ballot): the Ballot problem ([#13592](https://github.com/leanprover-community/mathlib/pull/13592))
#### Estimated changes
Added archive/100-theorems-list/30_ballot_problem.lean
- \+ *lemma* ballot.ballot_edge
- \+ *lemma* ballot.ballot_neg
- \+ *lemma* ballot.ballot_pos
- \+ *theorem* ballot.ballot_problem'
- \+ *theorem* ballot.ballot_problem
- \+ *lemma* ballot.ballot_same
- \+ *lemma* ballot.count_counted_sequence
- \+ *lemma* ballot.counted_left_zero
- \+ *lemma* ballot.counted_ne_nil_left
- \+ *lemma* ballot.counted_ne_nil_right
- \+ *lemma* ballot.counted_right_zero
- \+ *def* ballot.counted_sequence
- \+ *lemma* ballot.counted_sequence_finite
- \+ *lemma* ballot.counted_sequence_int_neg_counted_succ_succ
- \+ *lemma* ballot.counted_sequence_int_pos_counted_succ_succ
- \+ *lemma* ballot.counted_sequence_nonempty
- \+ *lemma* ballot.counted_succ_succ
- \+ *lemma* ballot.disjoint_bits
- \+ *lemma* ballot.first_vote_neg
- \+ *lemma* ballot.first_vote_pos
- \+ *lemma* ballot.head_mem_of_nonempty
- \+ *lemma* ballot.length_of_mem_counted_sequence
- \+ *lemma* ballot.mem_of_mem_counted_sequence
- \+ *def* ballot.stays_positive
- \+ *lemma* ballot.stays_positive_cons_pos
- \+ *lemma* ballot.stays_positive_nil
- \+ *lemma* ballot.sum_of_mem_counted_sequence

Modified docs/100.yaml


Modified src/data/list/infix.lean
- \+ *lemma* list.mem_of_mem_suffix

Modified src/data/nat/basic.lean
- \+ *lemma* nat.diag_induction

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.div_eq_div_iff
- \+ *lemma* ennreal.eq_div_iff

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measure.count_injective_image

Modified src/probability/cond_count.lean
- \+/\- *lemma* probability_theory.cond_count_add_compl_eq
- \+/\- *lemma* probability_theory.cond_count_compl



## [2022-06-09 11:44:36](https://github.com/leanprover-community/mathlib/commit/d51aacb)
feat(ring_theory/unique_factorization_domain): add some lemmas about … ([#14555](https://github.com/leanprover-community/mathlib/pull/14555))
#### Estimated changes
Modified src/algebra/associated.lean


Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* unique_factorization_monoid.factors_mul
- \+ *lemma* unique_factorization_monoid.factors_one
- \+ *lemma* unique_factorization_monoid.factors_pow
- \+ *lemma* unique_factorization_monoid.factors_zero



## [2022-06-09 09:58:31](https://github.com/leanprover-community/mathlib/commit/dc2f6bb)
chore(topology/metric_space): remove instances that duplicate lemmas ([#14639](https://github.com/leanprover-community/mathlib/pull/14639))
We can use the structure projections directly as instances, rather than duplicating them with primed names. This removes;
* `metric_space.to_uniform_space'` (was misnamed, now `pseudo_metric_space.to_uniform_space`)
* `pseudo_metric_space.to_bornology'` (now `pseudo_metric_space.to_bornology`)
* `pseudo_emetric_space.to_uniform_space'` (now `pseudo_metric_space.to_uniform_space`)
* `emetric_space.to_uniform_space'` (redundant)
Follows up from review comments in [#13927](https://github.com/leanprover-community/mathlib/pull/13927)
#### Estimated changes
Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/uniform_space/compare_reals.lean




## [2022-06-09 09:58:30](https://github.com/leanprover-community/mathlib/commit/bc7b342)
feat(topology/metric_space/basic): add lemma `exists_lt_mem_ball_of_mem_ball` ([#14627](https://github.com/leanprover-community/mathlib/pull/14627))
This is apparently necessary in https://github.com/leanprover-community/mathlib/pull/13885
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.exists_lt_mem_ball_of_mem_ball



## [2022-06-09 09:58:29](https://github.com/leanprover-community/mathlib/commit/6a1ce4e)
feat(analysis/seminorm): add a `zero_hom_class` instance and remove `seminorm.zero` ([#14613](https://github.com/leanprover-community/mathlib/pull/14613))
#### Estimated changes
Modified src/analysis/locally_convex/with_seminorms.lean


Modified src/analysis/seminorm.lean




## [2022-06-09 09:58:28](https://github.com/leanprover-community/mathlib/commit/6826bf0)
doc(data/vector3): improve wording ([#14610](https://github.com/leanprover-community/mathlib/pull/14610))
#### Estimated changes
Modified src/data/vector3.lean




## [2022-06-09 09:58:27](https://github.com/leanprover-community/mathlib/commit/ab64f63)
refactor(algebra/sub{monoid,group,ring,semiring,field}): merge together the `restrict` and `cod_restrict` helpers ([#14548](https://github.com/leanprover-community/mathlib/pull/14548))
This uses the new subobject typeclasses to merge together:
* `monoid_hom.mrestrict`, `monoid_hom.restrict`
* `monoid_hom.cod_mrestrict`, `monoid_hom.cod_restrict`
* `ring_hom.srestrict`, `ring_hom.restrict`, `ring_hom.restrict_field`
* `ring_hom.cod_srestrict`, `ring_hom.cod_restrict`, `ring_hom.cod_restrict_field`
For consistency, this also removes the `m` prefix from `mul_hom.mrestrict`
#### Estimated changes
Modified src/algebra/algebra/subalgebra/basic.lean


Modified src/algebra/category/Ring/constructions.lean


Modified src/field_theory/subfield.lean
- \- *def* ring_hom.cod_restrict_field
- \- *def* ring_hom.restrict_field
- \- *lemma* ring_hom.restrict_field_apply

Modified src/group_theory/free_product.lean


Modified src/group_theory/monoid_localization.lean


Modified src/group_theory/subgroup/basic.lean
- \- *def* monoid_hom.cod_restrict
- \- *lemma* monoid_hom.cod_restrict_apply
- \- *def* monoid_hom.restrict
- \- *lemma* monoid_hom.restrict_apply

Modified src/group_theory/submonoid/operations.lean
- \- *def* monoid_hom.cod_mrestrict
- \+ *def* monoid_hom.cod_restrict
- \- *def* monoid_hom.mrestrict
- \- *lemma* monoid_hom.mrestrict_apply
- \+ *def* monoid_hom.restrict
- \+ *lemma* monoid_hom.restrict_apply

Modified src/group_theory/subsemigroup/operations.lean
- \+ *def* mul_hom.cod_restrict
- \- *def* mul_hom.cod_srestrict
- \+ *def* mul_hom.restrict
- \+ *lemma* mul_hom.restrict_apply
- \- *def* mul_hom.srestrict
- \- *lemma* mul_hom.srestrict_apply

Modified src/ring_theory/localization/basic.lean


Modified src/ring_theory/subring/basic.lean
- \- *def* ring_hom.cod_restrict'
- \- *def* ring_hom.restrict
- \- *lemma* ring_hom.restrict_apply

Modified src/ring_theory/subsemiring/basic.lean
- \+ *def* ring_hom.cod_restrict
- \- *def* ring_hom.cod_srestrict
- \+ *def* ring_hom.restrict
- \+ *lemma* ring_hom.restrict_apply
- \- *def* ring_hom.srestrict
- \- *lemma* ring_hom.srestrict_apply



## [2022-06-09 09:58:26](https://github.com/leanprover-community/mathlib/commit/732b79f)
feat(order/compactly_generated): an independent subset of a well-founded complete lattice is finite ([#14215](https://github.com/leanprover-community/mathlib/pull/14215))
#### Estimated changes
Modified src/order/compactly_generated.lean
- \+ *lemma* complete_lattice.well_founded.finite_of_set_independent



## [2022-06-09 07:52:18](https://github.com/leanprover-community/mathlib/commit/3a95d1d)
feat(algebra/order/monoid): `zero_le_one_class` instances for `with_top` and `with_bot` ([#14640](https://github.com/leanprover-community/mathlib/pull/14640))
#### Estimated changes
Modified src/algebra/order/monoid.lean




## [2022-06-09 05:43:16](https://github.com/leanprover-community/mathlib/commit/971a9b0)
feat(logic/equiv/basic): two empty types are equivalent; remove various redundant lemmas ([#14604](https://github.com/leanprover-community/mathlib/pull/14604))
We prove `equiv_of_is_empty`, which states two empty types are equivalent. This allows us to remove various redundant lemmas.
We keep `empty_equiv_empty` and `empty_equiv_pempty` as these specific instantiations of that lemma are widely used.
#### Estimated changes
Modified src/logic/equiv/basic.lean
- \- *def* equiv.empty_equiv_pempty
- \+ *def* equiv.equiv_of_is_empty
- \+ *def* equiv.equiv_pempty
- \- *def* equiv.false_equiv_empty
- \- *def* equiv.false_equiv_pempty
- \- *def* equiv.pempty_equiv_pempty
- \- *def* equiv.{u'

Modified src/set_theory/ordinal/basic.lean




## [2022-06-09 04:07:37](https://github.com/leanprover-community/mathlib/commit/9f19686)
feat(logic/small): generalize + golf ([#14584](https://github.com/leanprover-community/mathlib/pull/14584))
This PR does the following:
- add a lemma `small_lift`
- generalize the lemma `small_ulift`
- golf `small_self` and `small_max`
#### Estimated changes
Modified src/logic/small.lean
- \+ *theorem* small_lift



## [2022-06-09 01:54:18](https://github.com/leanprover-community/mathlib/commit/b392bb2)
feat(data/nat/factorization/basic): two trivial simp lemmas about factorizations ([#14634](https://github.com/leanprover-community/mathlib/pull/14634))
For any `n : ℕ`, `n.factorization 0 = 0` and `n.factorization 1 = 0`
#### Estimated changes
Modified src/data/nat/factorization/basic.lean
- \+ *lemma* nat.factorization_one_right
- \+ *lemma* nat.factorization_zero_right



## [2022-06-09 01:54:16](https://github.com/leanprover-community/mathlib/commit/4fc3539)
refactor(data/finset/nat_antidiagonal): state lemmas with cons instead of insert ([#14533](https://github.com/leanprover-community/mathlib/pull/14533))
This puts less of a burden on the caller rewriting in the forward direction, as they don't have to prove obvious things about membership when evaluating sums.
Since this adds the missing `finset.map_cons`, a number of uses of `multiset.map_cons` now need qualified names.
#### Estimated changes
Modified src/algebra/big_operators/nat_antidiagonal.lean


Modified src/algebra/polynomial/big_operators.lean


Modified src/data/finset/basic.lean
- \+ *lemma* finset.map_cons

Modified src/data/finset/fold.lean


Modified src/data/finset/nat_antidiagonal.lean
- \+/\- *lemma* finset.nat.antidiagonal_succ'
- \+/\- *lemma* finset.nat.antidiagonal_succ



## [2022-06-08 23:44:35](https://github.com/leanprover-community/mathlib/commit/0c08bd4)
chore(data/set/basic): minor style fixes ([#14628](https://github.com/leanprover-community/mathlib/pull/14628))
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *lemma* set.set_of_app_iff
- \+/\- *theorem* set_coe_cast



## [2022-06-08 20:36:43](https://github.com/leanprover-community/mathlib/commit/c1faa2e)
feat(linear_algebra/affine_space/affine_subspace/pointwise): Translations are an action on affine subspaces ([#14230](https://github.com/leanprover-community/mathlib/pull/14230))
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_equiv.lean
- \+ *lemma* affine_equiv.coe_refl_to_affine_map

Modified src/linear_algebra/affine_space/affine_subspace.lean
- \+/\- *lemma* affine_equiv.span_eq_top_iff

Added src/linear_algebra/affine_space/pointwise.lean
- \+ *lemma* affine_subspace.coe_pointwise_vadd
- \+ *lemma* affine_subspace.map_pointwise_vadd
- \+ *lemma* affine_subspace.pointwise_vadd_bot
- \+ *lemma* affine_subspace.pointwise_vadd_direction
- \+ *lemma* affine_subspace.pointwise_vadd_span
- \+ *lemma* affine_subspace.vadd_mem_pointwise_vadd_iff



## [2022-06-08 20:36:42](https://github.com/leanprover-community/mathlib/commit/84a1bd6)
refactor(topology/metric_space/basic): add `pseudo_metric_space.to_bornology'` ([#13927](https://github.com/leanprover-community/mathlib/pull/13927))
* add `pseudo_metric_space.to_bornology'` and `pseudo_metric_space.replace_bornology`;
* add `metric.is_bounded_iff` and a few similar lemmas;
* fix instances for `subtype`, `prod`, `pi`, and `pi_Lp` to use the correct bornology`;
* add `lipschitz_with.to_locally_bounded_map` and `lipschitz_with.comap_cobounded_le`;
* add `antilipschitz_with.tendsto_cobounded`.
#### Estimated changes
Modified src/analysis/normed_space/enorm.lean
- \+/\- *def* enorm.emetric_space

Modified src/analysis/normed_space/pi_Lp.lean
- \+ *lemma* pi_Lp.aux_cobounded_eq
- \+ *def* pi_Lp.pseudo_metric_aux

Modified src/topology/metric_space/antilipschitz.lean
- \+ *lemma* antilipschitz_with.tendsto_cobounded

Modified src/topology/metric_space/basic.lean
- \+ *theorem* metric.is_bounded_iff
- \+ *theorem* metric.is_bounded_iff_eventually
- \+ *theorem* metric.is_bounded_iff_exists_ge
- \+ *theorem* metric.is_bounded_iff_nndist
- \+ *def* pseudo_metric_space.replace_bornology
- \+ *lemma* pseudo_metric_space.replace_bornology_eq

Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* lipschitz_with.coe_to_locally_bounded_map
- \+ *lemma* lipschitz_with.comap_cobounded_le
- \+ *def* lipschitz_with.to_locally_bounded_map



## [2022-06-08 18:51:48](https://github.com/leanprover-community/mathlib/commit/61df9c6)
feat(set_theory/ordinal/basic): tweak `type_def` + golf `type_lt` ([#14611](https://github.com/leanprover-community/mathlib/pull/14611))
We replace the original, redundant `type_def'` with a new more general lemma. We keep `type_def` as it enables `dsimp`, unlike `type_def'`. We golf `type_lt` using this new lemma.
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean
- \+/\- *theorem* ordinal.type_def'
- \+/\- *theorem* ordinal.type_def



## [2022-06-08 18:51:32](https://github.com/leanprover-community/mathlib/commit/9c4a3d1)
feat(ring_theory/valuation/valuation_subring): define unit group of valuation subring and provide basic API ([#14540](https://github.com/leanprover-community/mathlib/pull/14540))
This PR defines the unit group of a valuation subring as a multiplicative subgroup of the units of the field. We show two valuation subrings are equivalent iff they have the same unit group. We show the map sending a valuation to its unit group is an order embedding.
#### Estimated changes
Modified src/ring_theory/valuation/basic.lean
- \+ *lemma* valuation.map_one_add_of_lt
- \+ *lemma* valuation.map_one_sub_of_lt

Modified src/ring_theory/valuation/valuation_subring.lean
- \+ *lemma* valuation_subring.coe_unit_group_mul_equiv_apply
- \+ *lemma* valuation_subring.coe_unit_group_mul_equiv_symm_apply
- \+ *lemma* valuation_subring.eq_iff_unit_group
- \+ *lemma* valuation_subring.mem_unit_group_iff
- \+ *def* valuation_subring.unit_group
- \+ *lemma* valuation_subring.unit_group_injective
- \+ *lemma* valuation_subring.unit_group_le_unit_group
- \+ *def* valuation_subring.unit_group_mul_equiv
- \+ *def* valuation_subring.unit_group_order_embedding
- \+ *lemma* valuation_subring.unit_group_strict_mono



## [2022-06-08 18:10:02](https://github.com/leanprover-community/mathlib/commit/d315666)
feat(model_theory/substructures): tweak universes for `lift_card_closure_le` ([#14597](https://github.com/leanprover-community/mathlib/pull/14597))
Since `cardinal.lift.{(max u v) u} = cardinal.lift.{v u}`, the latter form should be preferred.
#### Estimated changes
Modified src/model_theory/substructures.lean
- \+/\- *theorem* first_order.language.substructure.lift_card_closure_le



## [2022-06-08 15:58:47](https://github.com/leanprover-community/mathlib/commit/8934884)
feat(set_theory/ordinal/basic): `rel_iso.ordinal_type_eq` ([#14602](https://github.com/leanprover-community/mathlib/pull/14602))
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean
- \+ *theorem* rel_iso.ordinal_type_eq



## [2022-06-08 15:58:46](https://github.com/leanprover-community/mathlib/commit/09df85f)
feat(order/rel_classes): any relation on an empty type is a well-order ([#14600](https://github.com/leanprover-community/mathlib/pull/14600))
#### Estimated changes
Modified src/logic/is_empty.lean
- \+ *lemma* well_founded_of_empty

Modified src/order/rel_classes.lean




## [2022-06-08 15:58:45](https://github.com/leanprover-community/mathlib/commit/201a3f4)
chore(*): remove extra parentheses in universe annotations ([#14595](https://github.com/leanprover-community/mathlib/pull/14595))
We change `f.{(max u v)}` to `f.{max u v}` throughout, and similarly for `imax`. This is for consistency with the rest of the code.
Note that `max` and `imax` take an arbitrary number of parameters, so if anyone wants to add a second universe parameter, they'll have to add the parentheses again.
#### Estimated changes
Modified src/algebra/category/Module/projective.lean


Modified src/category_theory/category/ulift.lean


Modified src/category_theory/graded_object.lean


Modified src/linear_algebra/dimension.lean


Modified src/set_theory/cardinal/basic.lean


Modified src/set_theory/cardinal/cofinality.lean


Modified src/set_theory/cardinal/ordinal.lean


Modified src/set_theory/ordinal/basic.lean
- \+/\- *theorem* ordinal.lift_lift

Modified src/testing/slim_check/functions.lean




## [2022-06-08 15:58:43](https://github.com/leanprover-community/mathlib/commit/3e4d6aa)
feat(algebra/algebra/basic): add instances `char_zero.no_zero_smul_divisors_int`, `char_zero.no_zero_smul_divisors_nat` ([#14395](https://github.com/leanprover-community/mathlib/pull/14395))
The proofs are taken from [#14338](https://github.com/leanprover-community/mathlib/pull/14338) where a specific need for these arose
Aside from the new instances, nothing else has changed; I moved the
`no_zero_smul_divisors` section lower down in the file since the new
instances need the `algebra ℤ R` structure carried by a ring `R`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean




## [2022-06-08 13:42:41](https://github.com/leanprover-community/mathlib/commit/bfb8ec8)
feat(logic/basic): add lemma `pi_congr` ([#14616](https://github.com/leanprover-community/mathlib/pull/14616))
This lemma is used in [#14153](https://github.com/leanprover-community/mathlib/pull/14153), where `congrm` is defined.
A big reason for splitting these 3 lines off the main PR is that they are the only ones that are not in a leaf of the import hierarchy: this hopefully saves lots of CI time, when doing trivial changes to the main PR.
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* pi_congr



## [2022-06-08 13:42:38](https://github.com/leanprover-community/mathlib/commit/700181a)
refactor(algebra/is_prime_pow): move lemmas using `factorization` to new file ([#14598](https://github.com/leanprover-community/mathlib/pull/14598))
As discussed in [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/squarefree.2C.20is_prime_pow.2C.20and.20factorization/near/285144241).
#### Estimated changes
Modified src/algebra/is_prime_pow.lean
- \- *lemma* is_prime_pow.min_fac_pow_factorization_eq
- \- *lemma* is_prime_pow_iff_card_support_factorization_eq_one
- \- *lemma* is_prime_pow_iff_factorization_eq_single
- \- *lemma* is_prime_pow_iff_min_fac_pow_factorization_eq
- \- *lemma* is_prime_pow_iff_unique_prime_dvd
- \- *lemma* is_prime_pow_of_min_fac_pow_factorization_eq
- \- *lemma* is_prime_pow_pow_iff
- \- *lemma* nat.coprime.is_prime_pow_dvd_mul
- \- *lemma* nat.mul_divisors_filter_prime_pow

Renamed src/data/nat/factorization.lean to src/data/nat/factorization/basic.lean


Added src/data/nat/factorization/prime_pow.lean
- \+ *lemma* is_prime_pow.min_fac_pow_factorization_eq
- \+ *lemma* is_prime_pow_iff_card_support_factorization_eq_one
- \+ *lemma* is_prime_pow_iff_factorization_eq_single
- \+ *lemma* is_prime_pow_iff_min_fac_pow_factorization_eq
- \+ *lemma* is_prime_pow_iff_unique_prime_dvd
- \+ *lemma* is_prime_pow_of_min_fac_pow_factorization_eq
- \+ *lemma* is_prime_pow_pow_iff
- \+ *lemma* nat.coprime.is_prime_pow_dvd_mul
- \+ *lemma* nat.mul_divisors_filter_prime_pow

Modified src/data/nat/squarefree.lean


Modified src/field_theory/cardinality.lean


Modified src/group_theory/nilpotent.lean


Modified src/group_theory/sylow.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/number_theory/padics/padic_val.lean


Modified src/ring_theory/multiplicity.lean




## [2022-06-08 12:10:16](https://github.com/leanprover-community/mathlib/commit/db4531f)
doc(data/qpf/multivariate/constructions/cofix): fix doc typos ([#14609](https://github.com/leanprover-community/mathlib/pull/14609))
#### Estimated changes
Modified src/data/qpf/multivariate/constructions/cofix.lean




## [2022-06-08 12:10:15](https://github.com/leanprover-community/mathlib/commit/0add876)
chore(set_theory/cardinal/basic): remove unused universe + fix spacing ([#14606](https://github.com/leanprover-community/mathlib/pull/14606))
#### Estimated changes
Modified src/set_theory/cardinal/basic.lean
- \+/\- *lemma* cardinal.mk_subtype_mono



## [2022-06-08 12:10:14](https://github.com/leanprover-community/mathlib/commit/65fba4c)
feat(algebra/lie/centralizer): define the centralizer of a Lie submodule and the upper central series ([#14173](https://github.com/leanprover-community/mathlib/pull/14173))
#### Estimated changes
Modified src/algebra/lie/cartan_subalgebra.lean
- \- *lemma* lie_subalgebra.exists_nested_lie_ideal_of_le_normalizer
- \- *lemma* lie_subalgebra.ideal_in_normalizer
- \- *lemma* lie_subalgebra.le_normalizer
- \- *lemma* lie_subalgebra.le_normalizer_of_ideal
- \- *lemma* lie_subalgebra.lie_mem_sup_of_mem_normalizer
- \- *lemma* lie_subalgebra.mem_normalizer_iff'
- \- *lemma* lie_subalgebra.mem_normalizer_iff
- \- *def* lie_subalgebra.normalizer
- \- *lemma* lie_subalgebra.normalizer_eq_self_iff

Added src/algebra/lie/centralizer.lean
- \+ *lemma* lie_subalgebra.coe_centralizer_eq_normalizer
- \+ *lemma* lie_subalgebra.exists_nested_lie_ideal_of_le_normalizer
- \+ *lemma* lie_subalgebra.ideal_in_normalizer
- \+ *lemma* lie_subalgebra.le_normalizer
- \+ *lemma* lie_subalgebra.lie_mem_sup_of_mem_normalizer
- \+ *lemma* lie_subalgebra.mem_normalizer_iff'
- \+ *lemma* lie_subalgebra.mem_normalizer_iff
- \+ *def* lie_subalgebra.normalizer
- \+ *lemma* lie_subalgebra.normalizer_eq_self_iff
- \+ *def* lie_submodule.centralizer
- \+ *lemma* lie_submodule.centralizer_bot_eq_max_triv_submodule
- \+ *lemma* lie_submodule.centralizer_inf
- \+ *lemma* lie_submodule.comap_centralizer
- \+ *lemma* lie_submodule.gc_top_lie_centralizer
- \+ *lemma* lie_submodule.le_centralizer
- \+ *lemma* lie_submodule.mem_centralizer
- \+ *lemma* lie_submodule.monotone_centalizer
- \+ *lemma* lie_submodule.top_lie_le_iff_le_centralizer

Modified src/algebra/lie/engel.lean


Modified src/algebra/lie/ideal_operations.lean
- \+ *lemma* lie_submodule.lie_le_iff

Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* lie_module.is_nilpotent_iff
- \+ *lemma* lie_module.is_nilpotent_iff_exists_ucs_eq_top
- \+ *lemma* lie_submodule.gc_lcs_ucs
- \+ *lemma* lie_submodule.is_nilpotent_iff_exists_self_le_ucs
- \+ *lemma* lie_submodule.lcs_add_le_iff
- \+ *lemma* lie_submodule.lcs_le_iff
- \+ *def* lie_submodule.ucs
- \+ *lemma* lie_submodule.ucs_comap_incl
- \+ *lemma* lie_submodule.ucs_eq_self_of_centralizer_eq_self
- \+ *lemma* lie_submodule.ucs_eq_top_iff
- \+ *lemma* lie_submodule.ucs_le_of_centralizer_eq_self
- \+ *lemma* lie_submodule.ucs_mono
- \+ *lemma* lie_submodule.ucs_succ
- \+ *lemma* lie_submodule.ucs_zero

Modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_submodule.comap_incl_eq_top



## [2022-06-08 09:31:34](https://github.com/leanprover-community/mathlib/commit/ffad43d)
golf(*): `λ _, default` → `default` ([#14608](https://github.com/leanprover-community/mathlib/pull/14608))
#### Estimated changes
Modified src/computability/turing_machine.lean


Modified src/data/array/lemmas.lean


Modified src/data/finset/basic.lean


Modified src/data/holor.lean
- \+/\- *def* holor
- \+/\- *def* holor_index

Modified src/data/pfunctor/multivariate/basic.lean


Modified src/data/pfunctor/univariate/M.lean


Modified src/data/pfunctor/univariate/basic.lean


Modified src/data/prod/tprod.lean


Modified src/data/qpf/multivariate/constructions/sigma.lean


Modified src/data/setoid/partition.lean


Modified src/data/vector/basic.lean


Modified src/group_theory/sylow.lean


Modified src/logic/basic.lean


Modified src/logic/embedding.lean


Modified src/logic/equiv/basic.lean


Modified src/logic/unique.lean


Modified src/measure_theory/covering/besicovitch.lean


Modified src/order/jordan_holder.lean


Modified src/order/omega_complete_partial_order.lean


Modified src/topology/continuous_function/basic.lean


Modified src/topology/vector_bundle/basic.lean


Modified test/lint_coe_t.lean
- \+/\- *def* int_to_a



## [2022-06-08 09:31:33](https://github.com/leanprover-community/mathlib/commit/60454dd)
feat(algebra/order/monoid): `zero_le_one'` lemma with explicit type argument ([#14594](https://github.com/leanprover-community/mathlib/pull/14594))
#### Estimated changes
Modified src/algebra/geom_sum.lean


Modified src/algebra/order/monoid.lean
- \+ *lemma* zero_le_one'
- \+/\- *lemma* zero_le_one

Modified src/analysis/specific_limits/basic.lean


Modified src/data/int/basic.lean


Modified src/topology/algebra/order/floor.lean


Modified src/topology/homotopy/basic.lean


Modified src/topology/path_connected.lean




## [2022-06-08 09:31:32](https://github.com/leanprover-community/mathlib/commit/f40cd3c)
feat(topology/algebra/order/basic): in a second-countable linear order, only countably many points are isolated to the right ([#14564](https://github.com/leanprover-community/mathlib/pull/14564))
This makes it possible to remove a useless `densely_ordered` assumption in a lemma in `borel_space`.
#### Estimated changes
Modified src/data/set/basic.lean
- \- *def* set.unique_empty

Modified src/data/set/countable.lean
- \+ *lemma* set.countable.of_subsingleton

Modified src/data/set/finite.lean
- \+ *lemma* set.finite.of_subsingleton

Modified src/measure_theory/constructions/borel_space.lean
- \+/\- *lemma* measurable_set_of_mem_nhds_within_Ioi
- \+/\- *lemma* measurable_set_of_mem_nhds_within_Ioi_aux

Modified src/measure_theory/integral/set_to_l1.lean


Modified src/topology/algebra/order/basic.lean
- \+ *lemma* countable_of_isolated_left
- \+ *lemma* countable_of_isolated_right
- \+ *lemma* set.pairwise_disjoint.countable_of_Ioo

Modified src/topology/separation.lean
- \+ *lemma* topological_space.is_topological_basis.exists_mem_of_ne



## [2022-06-08 09:31:31](https://github.com/leanprover-community/mathlib/commit/a20032a)
feat(group_theory/sylow): The index of a sylow subgroup is indivisible by the prime ([#14518](https://github.com/leanprover-community/mathlib/pull/14518))
This PR adds a lemma stating that the index of a sylow subgroup is indivisible by the prime.
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *lemma* not_dvd_index_sylow'
- \+ *lemma* not_dvd_index_sylow
- \+/\- *def* sylow.comap_of_injective
- \+/\- *lemma* sylow.stabilizer_eq_normalizer



## [2022-06-08 09:31:30](https://github.com/leanprover-community/mathlib/commit/54236f5)
feat(topology/continuous_function/compact): `cstar_ring` instance on `C(α, β)` when `α` is compact ([#14437](https://github.com/leanprover-community/mathlib/pull/14437))
We define the star operation on `C(α, β)` by applying `β`'s star operation pointwise. In the case when `α` is compact, then `C(α, β)` has a norm, and we show that it is a `cstar_ring`.
#### Estimated changes
Modified src/topology/algebra/star.lean
- \+ *def* star_continuous_map

Modified src/topology/continuous_function/algebra.lean
- \+ *lemma* continuous_map.coe_star
- \+ *lemma* continuous_map.star_apply

Modified src/topology/continuous_function/compact.lean
- \+ *lemma* bounded_continuous_function.mk_of_compact_star



## [2022-06-08 07:33:27](https://github.com/leanprover-community/mathlib/commit/e39af18)
chore(data/finset): remove duplicated lemma ([#14607](https://github.com/leanprover-community/mathlib/pull/14607))
The lemma `ssubset_iff_exists_insert_subset` was added in [#11248](https://github.com/leanprover-community/mathlib/pull/11248) but is just a duplicate of the `ssubset_iff` lemma a few lines earlier in the file. It's only used once.
#### Estimated changes
Modified src/combinatorics/set_family/lym.lean


Modified src/data/finset/basic.lean
- \- *lemma* finset.ssubset_iff_exists_insert_subset



## [2022-06-08 00:23:16](https://github.com/leanprover-community/mathlib/commit/9d04844)
feat(data/int/basic): Sum of units casework lemma ([#14557](https://github.com/leanprover-community/mathlib/pull/14557))
This PR adds a casework lemma for when the sum of two units equals the sum of two units. I needed this lemma for irreducibility of x^n-x-1.
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.is_unit_add_is_unit_eq_is_unit_add_is_unit



## [2022-06-07 22:31:45](https://github.com/leanprover-community/mathlib/commit/759516c)
chore(ring_theory/dedekind_domain/ideal): speed up a proof ([#14590](https://github.com/leanprover-community/mathlib/pull/14590))
... which causes recurring timeout at irrelevant places, see https://github.com/leanprover-community/mathlib/pull/14585#issuecomment-1148222373 and referenced Zulip discussion.
Feel free to push golfs that remains fast (1-2s)!
#### Estimated changes
Modified src/ring_theory/dedekind_domain/ideal.lean




## [2022-06-07 21:09:01](https://github.com/leanprover-community/mathlib/commit/905374c)
feat(special_functions/gamma): better convergence bounds ([#14496](https://github.com/leanprover-community/mathlib/pull/14496))
Use the stronger form of FTC-2 added [#14147](https://github.com/leanprover-community/mathlib/pull/14147) to strengthen some results about the gamma function.
#### Estimated changes
Modified src/analysis/special_functions/gamma.lean
- \+/\- *def* complex.Gamma
- \+/\- *lemma* complex.Gamma_aux_recurrence1
- \+/\- *lemma* complex.Gamma_aux_recurrence2
- \+/\- *lemma* complex.Gamma_eq_Gamma_aux
- \+/\- *theorem* complex.Gamma_eq_integral
- \+/\- *theorem* complex.Gamma_integral_add_one
- \+/\- *lemma* complex.Gamma_integral_convergent
- \+/\- *lemma* complex.partial_Gamma_add_one
- \+/\- *lemma* complex.tendsto_partial_Gamma
- \+/\- *lemma* real.Gamma_integral_convergent



## [2022-06-07 17:43:24](https://github.com/leanprover-community/mathlib/commit/cfa447e)
chore(logic/hydra): tweak docs + minor golf ([#14579](https://github.com/leanprover-community/mathlib/pull/14579))
#### Estimated changes
Modified src/logic/hydra.lean




## [2022-06-07 13:32:20](https://github.com/leanprover-community/mathlib/commit/43f1af9)
refactor(topology/continuous_function/basic): rename `map_specialization` ([#14565](https://github.com/leanprover-community/mathlib/pull/14565))
Rename `continuous_map.map_specialization` to `continuous_map.map_specializes` to align with the name of the relation.
#### Estimated changes
Modified src/algebraic_geometry/stalks.lean


Modified src/topology/continuous_function/basic.lean
- \- *lemma* continuous_map.map_specialization
- \+ *lemma* continuous_map.map_specializes

Modified src/topology/sheaves/stalks.lean




## [2022-06-07 12:37:21](https://github.com/leanprover-community/mathlib/commit/544fdc0)
chore(ring_theory/integral_closure): fix dot notation ([#14589](https://github.com/leanprover-community/mathlib/pull/14589))
#### Estimated changes
Modified src/number_theory/function_field.lean


Modified src/number_theory/number_field.lean


Modified src/ring_theory/integral_closure.lean
- \+ *lemma* algebra.is_integral.is_field_iff_is_field
- \- *lemma* is_integral.is_field_iff_is_field



## [2022-06-07 11:40:32](https://github.com/leanprover-community/mathlib/commit/6906627)
refactor(algebra/squarefree): split out `nat` part to new file `data/nat/squarefree` ([#14577](https://github.com/leanprover-community/mathlib/pull/14577))
As discussed in this Zulip [thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/squarefree.2C.20is_prime_pow.2C.20and.20factorization)
#### Estimated changes
Modified archive/100-theorems-list/81_sum_of_prime_reciprocals_diverges.lean


Modified src/algebra/squarefree.lean
- \- *lemma* nat.divisors_filter_squarefree
- \- *def* nat.min_sq_fac
- \- *def* nat.min_sq_fac_aux
- \- *theorem* nat.min_sq_fac_aux_has_prop
- \- *theorem* nat.min_sq_fac_dvd
- \- *theorem* nat.min_sq_fac_has_prop
- \- *theorem* nat.min_sq_fac_le_of_dvd
- \- *theorem* nat.min_sq_fac_prime
- \- *def* nat.min_sq_fac_prop
- \- *theorem* nat.min_sq_fac_prop_div
- \- *lemma* nat.sq_mul_squarefree
- \- *lemma* nat.sq_mul_squarefree_of_pos'
- \- *lemma* nat.sq_mul_squarefree_of_pos
- \- *lemma* nat.squarefree.ext_iff
- \- *lemma* nat.squarefree.factorization_le_one
- \- *lemma* nat.squarefree_and_prime_pow_iff_prime
- \- *lemma* nat.squarefree_iff_factorization_le_one
- \- *lemma* nat.squarefree_iff_min_sq_fac
- \- *lemma* nat.squarefree_iff_nodup_factors
- \- *theorem* nat.squarefree_iff_prime_squarefree
- \- *lemma* nat.squarefree_mul
- \- *lemma* nat.squarefree_of_factorization_le_one
- \- *lemma* nat.squarefree_pow_iff
- \- *theorem* nat.squarefree_two
- \- *lemma* nat.sum_divisors_filter_squarefree
- \- *lemma* tactic.norm_num.not_squarefree_mul
- \- *lemma* tactic.norm_num.squarefree_bit10
- \- *lemma* tactic.norm_num.squarefree_bit1
- \- *def* tactic.norm_num.squarefree_helper
- \- *lemma* tactic.norm_num.squarefree_helper_0
- \- *lemma* tactic.norm_num.squarefree_helper_1
- \- *lemma* tactic.norm_num.squarefree_helper_2
- \- *lemma* tactic.norm_num.squarefree_helper_3
- \- *lemma* tactic.norm_num.squarefree_helper_4

Added src/data/nat/squarefree.lean
- \+ *lemma* nat.divisors_filter_squarefree
- \+ *def* nat.min_sq_fac
- \+ *def* nat.min_sq_fac_aux
- \+ *theorem* nat.min_sq_fac_aux_has_prop
- \+ *theorem* nat.min_sq_fac_dvd
- \+ *theorem* nat.min_sq_fac_has_prop
- \+ *theorem* nat.min_sq_fac_le_of_dvd
- \+ *theorem* nat.min_sq_fac_prime
- \+ *def* nat.min_sq_fac_prop
- \+ *theorem* nat.min_sq_fac_prop_div
- \+ *lemma* nat.sq_mul_squarefree
- \+ *lemma* nat.sq_mul_squarefree_of_pos'
- \+ *lemma* nat.sq_mul_squarefree_of_pos
- \+ *lemma* nat.squarefree.ext_iff
- \+ *lemma* nat.squarefree.factorization_le_one
- \+ *lemma* nat.squarefree_and_prime_pow_iff_prime
- \+ *lemma* nat.squarefree_iff_factorization_le_one
- \+ *lemma* nat.squarefree_iff_min_sq_fac
- \+ *lemma* nat.squarefree_iff_nodup_factors
- \+ *theorem* nat.squarefree_iff_prime_squarefree
- \+ *lemma* nat.squarefree_mul
- \+ *lemma* nat.squarefree_of_factorization_le_one
- \+ *lemma* nat.squarefree_pow_iff
- \+ *theorem* nat.squarefree_two
- \+ *lemma* nat.sum_divisors_filter_squarefree
- \+ *lemma* tactic.norm_num.not_squarefree_mul
- \+ *lemma* tactic.norm_num.squarefree_bit10
- \+ *lemma* tactic.norm_num.squarefree_bit1
- \+ *def* tactic.norm_num.squarefree_helper
- \+ *lemma* tactic.norm_num.squarefree_helper_0
- \+ *lemma* tactic.norm_num.squarefree_helper_1
- \+ *lemma* tactic.norm_num.squarefree_helper_2
- \+ *lemma* tactic.norm_num.squarefree_helper_3
- \+ *lemma* tactic.norm_num.squarefree_helper_4

Modified src/number_theory/arithmetic_function.lean


Modified test/norm_num_ext.lean




## [2022-06-07 07:06:14](https://github.com/leanprover-community/mathlib/commit/4a4cd6d)
feat(topology/metric_space/metrizable): assume `regular_space` ([#14586](https://github.com/leanprover-community/mathlib/pull/14586))
#### Estimated changes
Modified src/topology/metric_space/metrizable.lean
- \- *lemma* topological_space.metrizable_space_of_normal_second_countable
- \+ *lemma* topological_space.metrizable_space_of_regular_second_countable



## [2022-06-07 01:29:01](https://github.com/leanprover-community/mathlib/commit/de648fd)
chore(set_theory/game/basic): spacing tweaks + fix docstring typo ([#14580](https://github.com/leanprover-community/mathlib/pull/14580))
#### Estimated changes
Modified src/set_theory/game/basic.lean
- \+/\- *def* pgame.to_left_moves_mul
- \+/\- *def* pgame.to_right_moves_mul



## [2022-06-06 22:44:27](https://github.com/leanprover-community/mathlib/commit/6ad1a55)
feat(set_theory/game/pgame): induction on left/right moves of add/mul ([#14345](https://github.com/leanprover-community/mathlib/pull/14345))
#### Estimated changes
Modified src/set_theory/game/basic.lean
- \+/\- *lemma* pgame.left_moves_mul_cases
- \+/\- *lemma* pgame.right_moves_mul_cases

Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/nim.lean


Modified src/set_theory/game/pgame.lean
- \+/\- *lemma* pgame.left_moves_add_cases
- \+/\- *lemma* pgame.right_moves_add_cases



## [2022-06-06 20:46:31](https://github.com/leanprover-community/mathlib/commit/c7a1319)
feat(measure_theory/measure/measure_space): add `interval_oc_ae_eq_interval` ([#14566](https://github.com/leanprover-community/mathlib/pull/14566))
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.interval_oc_ae_eq_interval



## [2022-06-06 20:46:30](https://github.com/leanprover-community/mathlib/commit/2c89306)
chore(geometry/manifold/charted_space): make `M` an explicit argument ([#14562](https://github.com/leanprover-community/mathlib/pull/14562))
#### Estimated changes
Modified src/geometry/manifold/charted_space.lean


Modified src/geometry/manifold/partition_of_unity.lean




## [2022-06-06 20:46:29](https://github.com/leanprover-community/mathlib/commit/d0b7ecc)
refactor(analysis/asymptotics): rename `is_O.join` to `is_O.sup` ([#14558](https://github.com/leanprover-community/mathlib/pull/14558))
* rename `is_*.join` to `is_*.sup`;
* add `iff` versions.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \- *theorem* asymptotics.is_O.join
- \+ *theorem* asymptotics.is_O.sup
- \+ *lemma* asymptotics.is_O_sup
- \- *theorem* asymptotics.is_O_with.join'
- \- *theorem* asymptotics.is_O_with.join
- \+ *theorem* asymptotics.is_O_with.sup'
- \+ *theorem* asymptotics.is_O_with.sup
- \- *theorem* asymptotics.is_o.join
- \+ *theorem* asymptotics.is_o.sup
- \+ *lemma* asymptotics.is_o_sup

Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/complex/phragmen_lindelof.lean




## [2022-06-06 20:46:28](https://github.com/leanprover-community/mathlib/commit/2b7e72b)
feat(order/liminf_limsup): add a few lemmas ([#14554](https://github.com/leanprover-community/mathlib/pull/14554))
* add `is_bounded_under.mono_le`, `is_bounded_under.mono_ge`;
* add `order_iso.is_bounded_under_le_comp`, `order_iso.is_bounded_under_ge_comp`;
* add `is_bounded_under_le_inv`, `is_bounded_under_le_inv`, and additive versions;
* rename `is_bounded_under_sup` and `is_bounded_under_inf` to `is_bounded_under.sup` and `is_bounded_under.inf`;
* add `iff` versions under names `is_bounded_under_le_sup` and `is_bounded_under_ge_inf`;
* add `is_bounded_under_le_abs`.
#### Estimated changes
Modified src/order/liminf_limsup.lean
- \+ *lemma* filter.is_bounded_under.inf
- \+ *lemma* filter.is_bounded_under.mono_ge
- \+ *lemma* filter.is_bounded_under.mono_le
- \+ *lemma* filter.is_bounded_under.sup
- \+ *lemma* filter.is_bounded_under_ge_inf
- \+ *lemma* filter.is_bounded_under_ge_inv
- \- *lemma* filter.is_bounded_under_inf
- \+ *lemma* filter.is_bounded_under_le_abs
- \+ *lemma* filter.is_bounded_under_le_inv
- \+ *lemma* filter.is_bounded_under_le_sup
- \- *lemma* filter.is_bounded_under_sup
- \+ *lemma* order_iso.is_bounded_under_ge_comp
- \+ *lemma* order_iso.is_bounded_under_le_comp



## [2022-06-06 20:46:27](https://github.com/leanprover-community/mathlib/commit/029a955)
refactor(../metric_space/baire): add baire_space class and instances ([#14547](https://github.com/leanprover-community/mathlib/pull/14547))
* Add a `baire_space` class containing the Baire property (a countable intersection of open dense sets is dense).
* The Baire category theorem for complete metric spaces becomes an instance of `baire_space`.
* Previous consequences of the Baire property use `baire_space` as an hypothesis, instead of `pseudo_emetric_space` `complete_space`.
* Add an instance of `baire_space` for locally compact t2 spaces, in effect extending all the consequences of the Baire property to locally compact spaces.
#### Estimated changes
Modified src/topology/metric_space/baire.lean
- \+/\- *theorem* dense_Inter_of_open_nat
- \+/\- *lemma* dense_of_mem_residual
- \+/\- *lemma* mem_residual

Modified src/topology/sets/compacts.lean
- \+ *lemma* exists_positive_compacts_subset



## [2022-06-06 20:46:26](https://github.com/leanprover-community/mathlib/commit/d28aa2c)
feat(analysis/normed_space/banach): closed graph theorem ([#14265](https://github.com/leanprover-community/mathlib/pull/14265))
#### Estimated changes
Modified src/analysis/normed_space/banach.lean
- \+ *lemma* continuous_linear_map.coe_fn_of_is_closed_graph
- \+ *lemma* continuous_linear_map.coe_fn_of_seq_closed_graph
- \+ *lemma* continuous_linear_map.coe_of_is_closed_graph
- \+ *lemma* continuous_linear_map.coe_of_seq_closed_graph
- \+ *def* continuous_linear_map.of_is_closed_graph
- \+ *def* continuous_linear_map.of_seq_closed_graph
- \+ *theorem* linear_map.continuous_of_is_closed_graph
- \+ *theorem* linear_map.continuous_of_seq_closed_graph



## [2022-06-06 18:41:09](https://github.com/leanprover-community/mathlib/commit/7b7da89)
feat(algebra/order/*): typeclass for `0 ≤ 1` ([#14510](https://github.com/leanprover-community/mathlib/pull/14510))
With this new typeclass, lemmas such as `zero_le_two` and `one_le_two` can be generalized to require just a few typeclasses for notation, `zero_add_class`, and some `covariant` class.
#### Estimated changes
Modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean
- \- *lemma* Nxzmod_2.zero_le_one

Modified src/algebra/geom_sum.lean


Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/order/monoid.lean
- \+ *lemma* one_le_two'
- \+ *lemma* one_le_two
- \+ *lemma* zero_le_one
- \+ *lemma* zero_le_two

Modified src/algebra/order/ring.lean
- \- *lemma* one_le_two
- \- *lemma* zero_le_one
- \- *lemma* zero_le_two

Modified src/algebra/order/with_zero.lean
- \- *lemma* zero_le_one'

Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/trigonometric/inverse.lean


Modified src/analysis/specific_limits/basic.lean


Modified src/category_theory/preadditive/schur.lean


Modified src/data/int/basic.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/probability/strong_law.lean


Modified src/ring_theory/valuation/integers.lean


Modified src/set_theory/game/pgame.lean
- \- *theorem* pgame.zero_le_one

Modified src/set_theory/ordinal/arithmetic.lean
- \- *theorem* ordinal.zero_le_one

Modified src/topology/algebra/order/floor.lean


Modified src/topology/homotopy/basic.lean


Modified src/topology/path_connected.lean




## [2022-06-06 14:27:28](https://github.com/leanprover-community/mathlib/commit/abbc7f6)
feat(measure_theory/measure/finite_measure_weak_convergence): Prove one implication of portmanteau theorem, convergence implies a limsup condition for measures of closed sets. ([#14116](https://github.com/leanprover-community/mathlib/pull/14116))
This PR contains the proof of one implication of portmanteau theorem characterizing weak convergence: it is shown that weak convergence implies that for any closed set the limsup of measures is at most the limit measure.
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.lintegral_const_lt_top
- \+ *lemma* measure_theory.set_lintegral_const_lt_top

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_le_lintegral_thickened_indicator
- \+ *lemma* measure_le_lintegral_thickened_indicator_aux

Modified src/measure_theory/measure/finite_measure_weak_convergence.lean
- \+ *lemma* measure_theory.finite_measure.limsup_measure_closed_le_of_tendsto
- \+ *lemma* measure_theory.finite_measure.tendsto_lintegral_nn_filter_of_le_const
- \+ *lemma* measure_theory.finite_measure.tendsto_lintegral_nn_of_le_const
- \+ *lemma* measure_theory.finite_measure.tendsto_test_against_nn_filter_of_le_const
- \+ *lemma* measure_theory.finite_measure.tendsto_test_against_nn_of_le_const
- \+ *lemma* measure_theory.measure_of_cont_bdd_of_tendsto_filter_indicator
- \+ *lemma* measure_theory.measure_of_cont_bdd_of_tendsto_indicator
- \+ *lemma* measure_theory.tendsto_lintegral_thickened_indicator_of_is_closed

Modified src/topology/metric_space/thickened_indicator.lean
- \+ *lemma* indicator_le_thickened_indicator
- \+ *lemma* indicator_le_thickened_indicator_aux



## [2022-06-06 13:48:54](https://github.com/leanprover-community/mathlib/commit/d6477a8)
feat(analysis/convex/krein_milman): The Krein-Milman theorem ([#8112](https://github.com/leanprover-community/mathlib/pull/8112))
This PR proves the Krein-Milman lemma and the Krein-Milman theorem.
#### Estimated changes
Modified src/analysis/convex/exposed.lean


Added src/analysis/convex/krein_milman.lean
- \+ *lemma* closure_convex_hull_extreme_points
- \+ *lemma* is_compact.has_extreme_point



## [2022-06-06 12:19:21](https://github.com/leanprover-community/mathlib/commit/d490ad1)
move(set_theory/ordinal/cantor_normal_form): move `CNF` to a new file ([#14563](https://github.com/leanprover-community/mathlib/pull/14563))
We move the API for the Cantor Normal Form to a new file, in preparation for an API expansion.
#### Estimated changes
Modified src/set_theory/ordinal/arithmetic.lean
- \- *def* ordinal.CNF
- \- *theorem* ordinal.CNF_foldr
- \- *theorem* ordinal.CNF_fst_le
- \- *theorem* ordinal.CNF_fst_le_log
- \- *theorem* ordinal.CNF_lt_snd
- \- *theorem* ordinal.CNF_ne_zero
- \- *theorem* ordinal.CNF_pairwise
- \- *theorem* ordinal.CNF_rec_ne_zero
- \- *theorem* ordinal.CNF_rec_zero
- \- *theorem* ordinal.CNF_snd_lt
- \- *theorem* ordinal.CNF_sorted
- \- *theorem* ordinal.CNF_zero
- \- *theorem* ordinal.one_CNF
- \- *theorem* ordinal.zero_CNF

Added src/set_theory/ordinal/cantor_normal_form.lean
- \+ *def* ordinal.CNF
- \+ *theorem* ordinal.CNF_foldr
- \+ *theorem* ordinal.CNF_fst_le
- \+ *theorem* ordinal.CNF_fst_le_log
- \+ *theorem* ordinal.CNF_lt_snd
- \+ *theorem* ordinal.CNF_ne_zero
- \+ *theorem* ordinal.CNF_pairwise
- \+ *theorem* ordinal.CNF_rec_ne_zero
- \+ *theorem* ordinal.CNF_rec_zero
- \+ *theorem* ordinal.CNF_snd_lt
- \+ *theorem* ordinal.CNF_sorted
- \+ *theorem* ordinal.CNF_zero
- \+ *theorem* ordinal.one_CNF
- \+ *theorem* ordinal.zero_CNF



## [2022-06-06 10:35:42](https://github.com/leanprover-community/mathlib/commit/0f5ea39)
feat(order/antichain, order/minimal): some antichain lemmas ([#14507](https://github.com/leanprover-community/mathlib/pull/14507))
This PR adds a few lemmas about antichains, including their images under complementation and order isomorphisms.
#### Estimated changes
Modified src/order/antichain.lean
- \+ *lemma* is_antichain.image_compl
- \+ *lemma* is_antichain.image_embedding
- \+ *lemma* is_antichain.image_embedding_iff
- \+ *lemma* is_antichain.image_iso
- \+ *lemma* is_antichain.image_iso_iff
- \+ *lemma* is_antichain.image_rel_embedding
- \+ *lemma* is_antichain.image_rel_embedding_iff
- \+ *lemma* is_antichain.image_rel_iso
- \+ *lemma* is_antichain.image_rel_iso_iff
- \+ *lemma* is_antichain.preimage_compl
- \+ *lemma* is_antichain.preimage_embedding
- \+ *lemma* is_antichain.preimage_iso
- \+ *lemma* is_antichain.preimage_iso_iff
- \+ *lemma* is_antichain.preimage_rel_embedding
- \+ *lemma* is_antichain.preimage_rel_iso
- \+ *lemma* is_antichain.to_dual
- \+ *lemma* is_antichain.to_dual_iff

Modified src/order/minimal.lean
- \+ *lemma* is_antichain.max_lower_set_of
- \+ *lemma* is_antichain.min_upper_set_of



## [2022-06-06 09:16:32](https://github.com/leanprover-community/mathlib/commit/d88ecd5)
chore(linear_algebra/std_basis): minor golfs ([#14552](https://github.com/leanprover-community/mathlib/pull/14552))
#### Estimated changes
Modified src/linear_algebra/std_basis.lean




## [2022-06-06 07:26:33](https://github.com/leanprover-community/mathlib/commit/789af09)
feat(algebra/char_p): add two helper lemmas about the cast of the characteristics being zero ([#14464](https://github.com/leanprover-community/mathlib/pull/14464))
- `(ring_char R : R) = 0` and
- If there exists a positive `n` lifting to zero, then the characteristics is positive.
#### Estimated changes
Modified src/algebra/char_p/basic.lean
- \+ *lemma* ring_char.nat.cast_ring_char



## [2022-06-05 20:50:27](https://github.com/leanprover-community/mathlib/commit/769a934)
feat(set_theory/*) `cardinal.min` → `Inf` ([#13410](https://github.com/leanprover-community/mathlib/pull/13410))
We discard `cardinal.min` in favor of `Inf` (the original definition is really just `infi`). 
Note: `lift_min'` is renamed to `lift_min`, as the name clash no longer exists. For consistency, `lift_max'` is renamed to `lift_max` and `lift_max` is renamed to `lift_umax_eq`.
#### Estimated changes
Modified src/linear_algebra/dimension.lean


Modified src/model_theory/encoding.lean


Modified src/model_theory/skolem.lean


Modified src/set_theory/cardinal/basic.lean
- \+ *theorem* cardinal.Inf_empty
- \- *theorem* cardinal.le_min
- \+ *theorem* cardinal.lift_Inf
- \- *theorem* cardinal.lift_max'
- \+/\- *theorem* cardinal.lift_max
- \- *theorem* cardinal.lift_min'
- \+/\- *theorem* cardinal.lift_min
- \+ *theorem* cardinal.lift_monotone
- \+ *theorem* cardinal.lift_strict_mono
- \+ *theorem* cardinal.lift_umax_eq
- \- *theorem* cardinal.min_eq
- \- *theorem* cardinal.min_le
- \+/\- *theorem* cardinal.sup_eq_zero

Modified src/set_theory/cardinal/cofinality.lean
- \+/\- *def* order.cof
- \+/\- *lemma* order.cof_le
- \+ *theorem* order.cof_nonempty
- \+/\- *theorem* ordinal.lift_cof
- \- *theorem* rel_iso.cof.aux
- \- *theorem* rel_iso.cof
- \+ *theorem* rel_iso.cof_eq
- \+ *theorem* rel_iso.cof_eq_lift
- \+ *theorem* rel_iso.cof_le
- \+ *theorem* rel_iso.cof_le_lift
- \+/\- *def* strict_order.cof
- \+ *theorem* strict_order.cof_nonempty

Modified src/set_theory/cardinal/schroeder_bernstein.lean
- \+/\- *theorem* function.embedding.min_injective
- \+/\- *theorem* function.embedding.total

Modified src/set_theory/ordinal/basic.lean




## [2022-06-05 19:28:46](https://github.com/leanprover-community/mathlib/commit/736b4e5)
feat(data/nat/factorization): Lemma on zero-ness of factorization ([#14560](https://github.com/leanprover-community/mathlib/pull/14560))
Sad naming is sad.
[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/from-referrer/)
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+ *lemma* nat.factorization_eq_zero_iff'



## [2022-06-05 14:52:20](https://github.com/leanprover-community/mathlib/commit/043fa29)
feat(src/analysis/normed_space): various improvements for continuous bilinear maps ([#14539](https://github.com/leanprover-community/mathlib/pull/14539))
* Add `simps` to `arrow_congrSL`
* `continuous_linear_map.flip (compSL F E H σ₂₁ σ₁₄)` takes almost 5 seconds to elaborate, but when giving the argument `(F →SL[σ₂₄] H)` for `G` explicitly, this goes down to 1 second.
* Reorder arguments of `is_bounded_bilinear_map_comp`
* Use `continuous_linear_map` results to prove `is_bounded_bilinear_map` results.
* Make arguments to `comp_continuous_multilinear_mapL` explicit
* Add `continuous[_on].clm_comp`, `cont_diff[_on].clm_comp` and `cont_diff.comp_cont_diff_on(₂|₃)`
#### Estimated changes
Modified src/analysis/calculus/cont_diff.lean
- \+ *lemma* cont_diff.clm_comp
- \+ *lemma* cont_diff.comp_cont_diff_on₂
- \+ *lemma* cont_diff.comp_cont_diff_on₃
- \+/\- *lemma* cont_diff_at.continuous_linear_map_comp
- \+ *lemma* cont_diff_on.clm_comp
- \+/\- *lemma* cont_diff_on.continuous_linear_map_comp

Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* continuous.clm_comp
- \+ *lemma* continuous_on.clm_comp

Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous.clm_comp_const
- \+ *lemma* continuous.const_clm_comp



## [2022-06-05 12:08:46](https://github.com/leanprover-community/mathlib/commit/d9e72ff)
feat(analysis/normed_space/hahn-banach/separation): Eidelheit's theorem ([#14460](https://github.com/leanprover-community/mathlib/pull/14460))
Prove Eidelheit's theorem as a corollary to the geometric Hahn-Banach.
#### Estimated changes
Modified src/analysis/normed_space/hahn_banach/separation.lean
- \+ *lemma* Inter_halfspaces_eq



## [2022-06-05 07:36:59](https://github.com/leanprover-community/mathlib/commit/b6395b3)
refactor(set_theory/*): change `omega` to `aleph_0` + golf ([#14467](https://github.com/leanprover-community/mathlib/pull/14467))
This PR does two things:
- we change `cardinal.omega` to `cardinal.aleph_0` and introduce the notation `ℵ₀`.
- we golf many proofs throughout
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified src/algebra/algebraic_card.lean
- \+ *theorem* algebraic.aleph_0_le_cardinal_mk_of_char_zero
- \+/\- *theorem* algebraic.cardinal_mk_le_max
- \+/\- *theorem* algebraic.cardinal_mk_le_mul
- \- *theorem* algebraic.omega_le_cardinal_mk_of_char_zero

Modified src/algebra/quaternion.lean


Modified src/analysis/complex/cauchy_integral.lean


Modified src/computability/encoding.lean
- \+ *lemma* computability.encoding.card_le_aleph_0
- \- *lemma* computability.encoding.card_le_omega
- \+ *lemma* computability.fin_encoding.card_le_aleph_0
- \- *lemma* computability.fin_encoding.card_le_omega

Modified src/data/W/cardinal.lean
- \+ *lemma* W_type.cardinal_mk_le_max_aleph_0_of_fintype
- \- *lemma* W_type.cardinal_mk_le_max_omega_of_fintype

Modified src/data/complex/cardinality.lean


Modified src/data/mv_polynomial/cardinal.lean


Modified src/data/polynomial/cardinal.lean
- \+/\- *lemma* polynomial.cardinal_mk_le_max

Modified src/data/rat/denumerable.lean
- \+/\- *lemma* cardinal.mk_rat

Modified src/data/real/cardinality.lean


Modified src/field_theory/cardinality.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/field_theory/finiteness.lean
- \+ *lemma* is_noetherian.dim_lt_aleph_0
- \- *lemma* is_noetherian.dim_lt_omega
- \+ *lemma* is_noetherian.iff_dim_lt_aleph_0
- \- *lemma* is_noetherian.iff_dim_lt_omega

Modified src/field_theory/fixed.lean


Modified src/field_theory/is_alg_closed/classification.lean
- \+/\- *lemma* algebra.is_algebraic.cardinal_mk_le_max
- \+ *lemma* is_alg_closed.cardinal_eq_cardinal_transcendence_basis_of_aleph_0_lt
- \- *lemma* is_alg_closed.cardinal_eq_cardinal_transcendence_basis_of_omega_lt

Modified src/group_theory/index.lean


Modified src/group_theory/schur_zassenhaus.lean


Modified src/linear_algebra/dimension.lean
- \+ *lemma* basis.finite_index_of_dim_lt_aleph_0
- \- *lemma* basis.finite_index_of_dim_lt_omega
- \+ *lemma* basis.finite_of_vector_space_index_of_dim_lt_aleph_0
- \- *lemma* basis.finite_of_vector_space_index_of_dim_lt_omega
- \+ *lemma* basis.nonempty_fintype_index_of_dim_lt_aleph_0
- \- *lemma* basis.nonempty_fintype_index_of_dim_lt_omega

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.lt_aleph_0_of_linear_independent
- \- *lemma* finite_dimensional.lt_omega_of_linear_independent

Modified src/linear_algebra/finsupp_vector_space.lean
- \+ *lemma* cardinal_lt_aleph_0_of_finite_dimensional
- \- *lemma* cardinal_lt_omega_of_finite_dimensional

Modified src/linear_algebra/free_module/finite/rank.lean
- \+ *lemma* module.free.rank_lt_aleph_0
- \- *lemma* module.free.rank_lt_omega

Modified src/measure_theory/card_measurable_space.lean


Modified src/model_theory/basic.lean
- \+ *lemma* first_order.language.card_functions_le_aleph_0
- \- *lemma* first_order.language.card_functions_le_omega
- \+ *lemma* first_order.language.card_le_aleph_0
- \- *lemma* first_order.language.card_le_omega
- \+/\- *lemma* first_order.language.encodable.countable
- \+/\- *lemma* first_order.language.encodable.countable_functions

Modified src/model_theory/encoding.lean
- \+/\- *theorem* first_order.language.term.card_le
- \+ *lemma* first_order.language.term.card_le_aleph_0
- \- *lemma* first_order.language.term.card_le_omega
- \+/\- *theorem* first_order.language.term.card_sigma

Modified src/model_theory/satisfiability.lean


Modified src/model_theory/semantics.lean


Modified src/model_theory/skolem.lean


Modified src/model_theory/substructures.lean


Modified src/ring_theory/localization/cardinality.lean


Modified src/set_theory/cardinal/basic.lean
- \+ *lemma* cardinal.add_le_aleph_0
- \- *lemma* cardinal.add_le_omega
- \+ *theorem* cardinal.add_lt_aleph_0
- \+ *lemma* cardinal.add_lt_aleph_0_iff
- \- *theorem* cardinal.add_lt_omega
- \- *lemma* cardinal.add_lt_omega_iff
- \+ *def* cardinal.aleph_0
- \+ *lemma* cardinal.aleph_0_add_aleph_0
- \+ *theorem* cardinal.aleph_0_le
- \+ *lemma* cardinal.aleph_0_le_add_iff
- \+ *theorem* cardinal.aleph_0_le_lift
- \+ *lemma* cardinal.aleph_0_le_mk
- \+ *lemma* cardinal.aleph_0_le_mul_iff
- \+ *lemma* cardinal.aleph_0_mul_aleph_0
- \+ *theorem* cardinal.aleph_0_ne_zero
- \+ *theorem* cardinal.aleph_0_pos
- \+/\- *theorem* cardinal.card_le_of
- \+/\- *theorem* cardinal.card_le_of_finset
- \+ *lemma* cardinal.cast_to_nat_of_aleph_0_le
- \+ *lemma* cardinal.cast_to_nat_of_lt_aleph_0
- \- *lemma* cardinal.cast_to_nat_of_lt_omega
- \- *lemma* cardinal.cast_to_nat_of_omega_le
- \+/\- *lemma* cardinal.denumerable_iff
- \+/\- *lemma* cardinal.encodable_iff
- \+ *lemma* cardinal.finset_card_lt_aleph_0
- \- *lemma* cardinal.finset_card_lt_omega
- \+/\- *theorem* cardinal.infinite_iff
- \+ *theorem* cardinal.lift_aleph_0
- \+ *theorem* cardinal.lift_le_aleph_0
- \- *theorem* cardinal.lift_le_omega
- \- *theorem* cardinal.lift_omega
- \+ *theorem* cardinal.lt_aleph_0
- \+ *theorem* cardinal.lt_aleph_0_iff_finite
- \+ *theorem* cardinal.lt_aleph_0_iff_fintype
- \+ *theorem* cardinal.lt_aleph_0_of_fintype
- \- *theorem* cardinal.lt_omega
- \- *theorem* cardinal.lt_omega_iff_finite
- \- *theorem* cardinal.lt_omega_iff_fintype
- \- *theorem* cardinal.lt_omega_of_fintype
- \+/\- *lemma* cardinal.mk_denumerable
- \+/\- *lemma* cardinal.mk_int
- \+ *lemma* cardinal.mk_le_aleph_0
- \- *lemma* cardinal.mk_le_omega
- \+/\- *lemma* cardinal.mk_nat
- \+/\- *lemma* cardinal.mk_pnat
- \+ *lemma* cardinal.mk_set_le_aleph_0
- \- *lemma* cardinal.mk_set_le_omega
- \+ *lemma* cardinal.mk_subtype_le_aleph_0
- \- *lemma* cardinal.mk_subtype_le_omega
- \+/\- *lemma* cardinal.mk_to_enat_of_infinite
- \+/\- *lemma* cardinal.mk_to_nat_of_infinite
- \+ *lemma* cardinal.mk_union_le_aleph_0
- \- *lemma* cardinal.mk_union_le_omega
- \+ *theorem* cardinal.mul_lt_aleph_0
- \+ *lemma* cardinal.mul_lt_aleph_0_iff
- \+ *lemma* cardinal.mul_lt_aleph_0_iff_of_ne_zero
- \- *theorem* cardinal.mul_lt_omega
- \- *lemma* cardinal.mul_lt_omega_iff
- \- *lemma* cardinal.mul_lt_omega_iff_of_ne_zero
- \+ *theorem* cardinal.nat_lt_aleph_0
- \- *theorem* cardinal.nat_lt_omega
- \+ *lemma* cardinal.nsmul_lt_aleph_0_iff
- \+ *lemma* cardinal.nsmul_lt_aleph_0_iff_of_ne_zero
- \- *lemma* cardinal.nsmul_lt_omega_iff
- \- *lemma* cardinal.nsmul_lt_omega_iff_of_ne_zero
- \- *def* cardinal.omega
- \- *lemma* cardinal.omega_add_omega
- \- *theorem* cardinal.omega_le
- \- *lemma* cardinal.omega_le_add_iff
- \- *theorem* cardinal.omega_le_lift
- \- *lemma* cardinal.omega_le_mk
- \- *lemma* cardinal.omega_le_mul_iff
- \- *lemma* cardinal.omega_mul_omega
- \- *theorem* cardinal.omega_ne_zero
- \- *theorem* cardinal.omega_pos
- \+ *theorem* cardinal.one_le_aleph_0
- \+ *theorem* cardinal.one_lt_aleph_0
- \- *theorem* cardinal.one_lt_omega
- \+/\- *lemma* cardinal.one_to_nat
- \+ *theorem* cardinal.power_lt_aleph_0
- \- *theorem* cardinal.power_lt_omega
- \+ *lemma* cardinal.to_enat_apply_of_aleph_0_le
- \+ *lemma* cardinal.to_enat_apply_of_lt_aleph_0
- \- *lemma* cardinal.to_enat_apply_of_lt_omega
- \- *lemma* cardinal.to_enat_apply_of_omega_le
- \+/\- *lemma* cardinal.to_enat_cast
- \+ *lemma* cardinal.to_nat_add_of_lt_aleph_0
- \- *lemma* cardinal.to_nat_add_of_lt_omega
- \+ *lemma* cardinal.to_nat_apply_of_aleph_0_le
- \+ *lemma* cardinal.to_nat_apply_of_lt_aleph_0
- \- *lemma* cardinal.to_nat_apply_of_lt_omega
- \- *lemma* cardinal.to_nat_apply_of_omega_le
- \+/\- *lemma* cardinal.to_nat_cast
- \+ *lemma* cardinal.to_nat_le_iff_le_of_lt_aleph_0
- \- *lemma* cardinal.to_nat_le_iff_le_of_lt_omega
- \+ *lemma* cardinal.to_nat_le_of_le_of_lt_aleph_0
- \- *lemma* cardinal.to_nat_le_of_le_of_lt_omega
- \+ *lemma* cardinal.to_nat_lt_iff_lt_of_lt_aleph_0
- \- *lemma* cardinal.to_nat_lt_iff_lt_of_lt_omega
- \+ *lemma* cardinal.to_nat_lt_of_lt_of_lt_aleph_0
- \- *lemma* cardinal.to_nat_lt_of_lt_of_lt_omega
- \+/\- *lemma* cardinal.zero_to_nat

Modified src/set_theory/cardinal/cofinality.lean
- \+/\- *theorem* cardinal.deriv_lt_ord
- \+/\- *theorem* cardinal.is_inaccessible.mk
- \+ *theorem* cardinal.is_limit.aleph_0_le
- \- *theorem* cardinal.is_limit.omega_le
- \+ *theorem* cardinal.is_limit_aleph_0
- \- *theorem* cardinal.is_limit_omega
- \+ *lemma* cardinal.is_regular.aleph_0_le
- \- *lemma* cardinal.is_regular.omega_le
- \+/\- *theorem* cardinal.is_regular_aleph'_succ
- \+ *theorem* cardinal.is_regular_aleph_0
- \- *theorem* cardinal.is_regular_omega
- \+/\- *theorem* cardinal.is_regular_succ
- \+ *theorem* cardinal.is_strong_limit_aleph_0
- \- *theorem* cardinal.is_strong_limit_omega
- \+/\- *theorem* cardinal.lt_cof_power
- \+/\- *theorem* cardinal.lt_power_cof
- \+/\- *theorem* cardinal.nfp_lt_ord_of_is_regular
- \+ *theorem* ordinal.aleph_0_le_cof
- \+/\- *theorem* ordinal.cof_omega
- \+/\- *theorem* ordinal.infinite_pigeonhole
- \+/\- *theorem* ordinal.nfp_bfamily_lt_ord
- \+/\- *theorem* ordinal.nfp_bfamily_lt_ord_lift
- \+/\- *theorem* ordinal.nfp_family_lt_ord
- \+/\- *theorem* ordinal.nfp_family_lt_ord_lift
- \+/\- *theorem* ordinal.nfp_lt_ord
- \- *theorem* ordinal.omega_le_cof

Modified src/set_theory/cardinal/continuum.lean
- \+ *lemma* cardinal.aleph_0_add_continuum
- \+ *lemma* cardinal.aleph_0_le_continuum
- \+ *lemma* cardinal.aleph_0_lt_continuum
- \+ *lemma* cardinal.aleph_0_mul_continuum
- \+ *lemma* cardinal.aleph_0_power_aleph_0
- \+/\- *def* cardinal.continuum
- \+ *lemma* cardinal.continuum_add_aleph_0
- \- *lemma* cardinal.continuum_add_omega
- \+ *lemma* cardinal.continuum_mul_aleph_0
- \+/\- *lemma* cardinal.continuum_mul_nat
- \- *lemma* cardinal.continuum_mul_omega
- \+ *lemma* cardinal.continuum_power_aleph_0
- \- *lemma* cardinal.continuum_power_omega
- \+/\- *lemma* cardinal.lift_continuum
- \+/\- *lemma* cardinal.nat_lt_continuum
- \+/\- *lemma* cardinal.nat_mul_continuum
- \+ *lemma* cardinal.nat_power_aleph_0
- \- *lemma* cardinal.nat_power_omega
- \- *lemma* cardinal.omega_add_continuum
- \- *lemma* cardinal.omega_le_continuum
- \- *lemma* cardinal.omega_lt_continuum
- \- *lemma* cardinal.omega_mul_continuum
- \- *lemma* cardinal.omega_power_omega
- \+ *lemma* cardinal.two_power_aleph_0
- \- *lemma* cardinal.two_power_omega

Modified src/set_theory/cardinal/divisibility.lean
- \+ *lemma* cardinal.dvd_of_le_of_aleph_0_le
- \- *lemma* cardinal.dvd_of_le_of_omega_le
- \+/\- *lemma* cardinal.is_prime_iff
- \+/\- *lemma* cardinal.is_prime_pow_iff
- \+ *lemma* cardinal.not_irreducible_of_aleph_0_le
- \- *lemma* cardinal.not_irreducible_of_omega_le
- \+ *lemma* cardinal.prime_of_aleph_0_le
- \- *lemma* cardinal.prime_of_omega_le

Modified src/set_theory/cardinal/ordinal.lean
- \+/\- *lemma* cardinal.add_eq_left
- \+/\- *lemma* cardinal.add_eq_left_iff
- \+/\- *theorem* cardinal.add_eq_max'
- \+/\- *theorem* cardinal.add_eq_max
- \+/\- *lemma* cardinal.add_eq_right
- \+/\- *lemma* cardinal.add_eq_right_iff
- \+/\- *theorem* cardinal.add_eq_self
- \+/\- *theorem* cardinal.add_le_max
- \+/\- *theorem* cardinal.add_le_of_le
- \+/\- *theorem* cardinal.add_lt_of_lt
- \+/\- *lemma* cardinal.add_one_eq
- \+/\- *theorem* cardinal.aleph'_aleph_idx
- \+/\- *theorem* cardinal.aleph'_le
- \+/\- *theorem* cardinal.aleph'_le_of_limit
- \+/\- *theorem* cardinal.aleph'_lt
- \+/\- *theorem* cardinal.aleph'_omega
- \+/\- *theorem* cardinal.aleph'_succ
- \+/\- *def* cardinal.aleph
- \+ *theorem* cardinal.aleph_0_le_aleph'
- \+ *theorem* cardinal.aleph_0_le_aleph
- \+ *theorem* cardinal.aleph_0_le_bit0
- \+ *theorem* cardinal.aleph_0_le_bit1
- \+ *lemma* cardinal.aleph_0_lt_aleph_one
- \+ *theorem* cardinal.aleph_0_mul_aleph
- \+ *theorem* cardinal.aleph_0_mul_eq
- \+ *theorem* cardinal.aleph_0_mul_mk_eq
- \+/\- *theorem* cardinal.aleph_idx_aleph'
- \+/\- *theorem* cardinal.aleph_le
- \+/\- *theorem* cardinal.aleph_lt
- \+ *theorem* cardinal.aleph_mul_aleph_0
- \- *theorem* cardinal.aleph_mul_omega
- \+/\- *theorem* cardinal.aleph_succ
- \+/\- *theorem* cardinal.aleph_zero
- \+/\- *theorem* cardinal.bit0_eq_self
- \+ *theorem* cardinal.bit0_lt_aleph_0
- \+/\- *lemma* cardinal.bit0_lt_bit1
- \- *theorem* cardinal.bit0_lt_omega
- \+/\- *theorem* cardinal.bit1_eq_self_iff
- \+/\- *lemma* cardinal.bit1_le_bit0
- \+ *theorem* cardinal.bit1_lt_aleph_0
- \- *theorem* cardinal.bit1_lt_omega
- \+/\- *theorem* cardinal.eq_aleph_of_eq_card_ord
- \+ *lemma* cardinal.eq_of_add_eq_of_aleph_0_le
- \- *lemma* cardinal.eq_of_add_eq_of_omega_le
- \+/\- *theorem* cardinal.exists_aleph
- \+ *theorem* cardinal.mk_list_eq_aleph_0
- \+ *theorem* cardinal.mk_list_eq_max_mk_aleph_0
- \- *theorem* cardinal.mk_list_eq_max_mk_omega
- \- *theorem* cardinal.mk_list_eq_omega
- \+/\- *theorem* cardinal.mk_list_le_max
- \+ *theorem* cardinal.mk_mul_aleph_0_eq
- \- *theorem* cardinal.mk_mul_omega_eq
- \+ *theorem* cardinal.mul_aleph_0_eq
- \+/\- *lemma* cardinal.mul_eq_left
- \+/\- *lemma* cardinal.mul_eq_left_iff
- \+/\- *lemma* cardinal.mul_eq_max'
- \+/\- *theorem* cardinal.mul_eq_max
- \+ *lemma* cardinal.mul_eq_max_of_aleph_0_le_left
- \+ *lemma* cardinal.mul_eq_max_of_aleph_0_le_right
- \- *lemma* cardinal.mul_eq_max_of_omega_le_left
- \- *lemma* cardinal.mul_eq_max_of_omega_le_right
- \+/\- *lemma* cardinal.mul_eq_right
- \+/\- *theorem* cardinal.mul_eq_self
- \+/\- *theorem* cardinal.mul_le_max
- \+ *lemma* cardinal.mul_le_max_of_aleph_0_le_left
- \- *lemma* cardinal.mul_le_max_of_omega_le_left
- \+/\- *theorem* cardinal.mul_lt_of_lt
- \- *theorem* cardinal.mul_omega_eq
- \+/\- *lemma* cardinal.nat_power_eq
- \- *theorem* cardinal.omega_le_aleph'
- \- *theorem* cardinal.omega_le_aleph
- \- *theorem* cardinal.omega_le_bit0
- \- *theorem* cardinal.omega_le_bit1
- \- *lemma* cardinal.omega_lt_aleph_one
- \- *theorem* cardinal.omega_mul_aleph
- \- *theorem* cardinal.omega_mul_eq
- \- *theorem* cardinal.omega_mul_mk_eq
- \- *lemma* cardinal.one_le_one
- \+/\- *theorem* cardinal.ord_card_unbounded'
- \+/\- *theorem* cardinal.ord_is_limit
- \+/\- *theorem* cardinal.pow_eq
- \+/\- *theorem* cardinal.pow_le
- \+/\- *lemma* cardinal.power_eq_two_power
- \+/\- *lemma* cardinal.power_nat_eq
- \+/\- *lemma* cardinal.power_nat_le
- \+/\- *lemma* cardinal.power_nat_le_max
- \+/\- *lemma* cardinal.power_self_eq
- \+ *lemma* cardinal.powerlt_aleph_0
- \+ *lemma* cardinal.powerlt_aleph_0_le
- \- *lemma* cardinal.powerlt_omega
- \- *lemma* cardinal.powerlt_omega_le
- \+/\- *theorem* cardinal.principal_add_ord
- \+ *theorem* cardinal.succ_aleph_0
- \- *theorem* cardinal.succ_omega
- \+/\- *theorem* cardinal.type_cardinal

Modified src/set_theory/game/short.lean


Modified src/set_theory/ordinal/arithmetic.lean
- \+ *theorem* cardinal.add_one_of_aleph_0_le
- \- *theorem* cardinal.add_one_of_omega_le
- \+ *theorem* cardinal.ord_aleph_0
- \- *theorem* cardinal.ord_omega
- \+/\- *theorem* ordinal.add_le_of_limit
- \+/\- *theorem* ordinal.div_nonempty
- \+/\- *theorem* ordinal.is_limit_iff_omega_dvd
- \+/\- *theorem* ordinal.lt_mul_of_limit
- \+/\- *theorem* ordinal.lt_omega
- \+/\- *theorem* ordinal.mul_le_of_limit
- \+/\- *theorem* ordinal.nat_lt_limit
- \+/\- *theorem* ordinal.nat_lt_omega
- \+/\- *theorem* ordinal.omega_is_limit
- \+/\- *theorem* ordinal.omega_le
- \+/\- *theorem* ordinal.omega_le_of_is_limit
- \+/\- *theorem* ordinal.omega_ne_zero
- \+/\- *theorem* ordinal.omega_pos
- \+/\- *theorem* ordinal.one_add_of_omega_le
- \+/\- *theorem* ordinal.one_add_omega
- \+/\- *theorem* ordinal.one_lt_omega
- \+/\- *def* ordinal.pred
- \+/\- *theorem* ordinal.sub_nonempty
- \+/\- *theorem* ordinal.sup_add_nat
- \+/\- *theorem* ordinal.sup_mul_nat
- \+/\- *theorem* ordinal.sup_nat_cast
- \+/\- *theorem* ordinal.sup_opow_nat

Modified src/set_theory/ordinal/basic.lean
- \+/\- *theorem* cardinal.mk_ordinal_out
- \+/\- *theorem* ordinal.card_omega
- \+/\- *theorem* ordinal.lift_omega
- \+/\- *def* ordinal.univ
- \+/\- *theorem* ordinal.univ_id

Modified src/set_theory/ordinal/notation.lean
- \+/\- *theorem* onote.repr_opow_aux₁

Modified src/topology/metric_space/gromov_hausdorff.lean




## [2022-06-05 04:57:10](https://github.com/leanprover-community/mathlib/commit/8651b70)
chore(set_theory/cardinal/cofinality): golf + fix spacing ([#14509](https://github.com/leanprover-community/mathlib/pull/14509))
#### Estimated changes
Modified src/set_theory/cardinal/cofinality.lean




## [2022-06-05 02:47:09](https://github.com/leanprover-community/mathlib/commit/10f4572)
refactor(group_theory/group_action/defs): rename has_faithful_scalar ([#14515](https://github.com/leanprover-community/mathlib/pull/14515))
This is the first scalar -> smul renaming transition.
Discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/scalar.20smul.20naming.20discrepancy
#### Estimated changes
Modified scripts/nolints.txt


Modified src/algebra/algebra/basic.lean
- \+/\- *theorem* mul_semiring_action.to_alg_equiv_injective
- \+/\- *theorem* mul_semiring_action.to_alg_hom_injective

Modified src/algebra/algebra/subalgebra/basic.lean


Modified src/algebra/group_ring_action.lean
- \+/\- *theorem* to_ring_hom_injective

Modified src/algebra/hom/aut.lean


Modified src/algebra/module/basic.lean


Modified src/algebra/module/equiv.lean


Modified src/algebra/module/linear_map.lean


Modified src/algebra/monoid_algebra/basic.lean


Modified src/analysis/normed_space/M_structure.lean
- \+/\- *lemma* is_Lprojection.coe_bot
- \+/\- *lemma* is_Lprojection.coe_inf
- \+/\- *lemma* is_Lprojection.coe_sdiff
- \+/\- *lemma* is_Lprojection.coe_sup
- \+/\- *lemma* is_Lprojection.coe_top
- \+/\- *lemma* is_Lprojection.commute
- \+/\- *lemma* is_Lprojection.distrib_lattice_lemma
- \+/\- *lemma* is_Lprojection.join
- \+/\- *lemma* is_Lprojection.le_def
- \+/\- *lemma* is_Lprojection.mul

Modified src/data/finsupp/basic.lean


Modified src/data/mv_polynomial/basic.lean


Modified src/data/polynomial/basic.lean


Modified src/field_theory/fixed.lean


Modified src/group_theory/group_action/defs.lean
- \+/\- *lemma* smul_left_injective'

Modified src/group_theory/group_action/group.lean
- \+/\- *lemma* mul_action.to_perm_injective

Modified src/group_theory/group_action/opposite.lean


Modified src/group_theory/group_action/pi.lean
- \- *lemma* pi.has_faithful_scalar_at
- \+ *lemma* pi.has_faithful_smul_at

Modified src/group_theory/group_action/prod.lean


Modified src/group_theory/group_action/units.lean


Modified src/group_theory/perm/subgroup.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/group_theory/submonoid/operations.lean


Modified src/ring_theory/subring/basic.lean


Modified src/ring_theory/subsemiring/basic.lean


Modified src/topology/algebra/module/basic.lean




## [2022-06-05 01:29:35](https://github.com/leanprover-community/mathlib/commit/157013d)
feat(set_theory/cardinal/cofinality): weaker definition for regular cardinals ([#14433](https://github.com/leanprover-community/mathlib/pull/14433))
We weaken `c.ord.cof = c` to `c ≤ c.ord.cof` in the definition of regular cardinals, in order to slightly simplify proofs. The lemma `is_regular.cof_eq` shows that this leads to an equivalent definition.
#### Estimated changes
Modified src/measure_theory/card_measurable_space.lean


Modified src/set_theory/cardinal/cofinality.lean
- \+/\- *theorem* cardinal.is_inaccessible.mk
- \+/\- *theorem* ordinal.cof_ord_le



## [2022-06-04 21:21:39](https://github.com/leanprover-community/mathlib/commit/741f4de)
feat(data/fin/tuple/monotone): new file ([#14483](https://github.com/leanprover-community/mathlib/pull/14483))
#### Estimated changes
Added src/data/fin/tuple/monotone.lean
- \+ *lemma* antitone.vec_cons
- \+ *lemma* antitone_vec_cons
- \+ *lemma* lift_fun_vec_cons
- \+ *lemma* monotone.vec_cons
- \+ *lemma* monotone_vec_cons
- \+ *lemma* strict_anti.vec_cons
- \+ *lemma* strict_anti_vec_cons
- \+ *lemma* strict_mono.vec_cons
- \+ *lemma* strict_mono_vec_cons



## [2022-06-04 21:21:38](https://github.com/leanprover-community/mathlib/commit/f65b160)
feat(set_theory/cardinal/cofinality): basic lemmas on limit cardinals ([#14439](https://github.com/leanprover-community/mathlib/pull/14439))
#### Estimated changes
Modified src/set_theory/cardinal/cofinality.lean
- \+ *theorem* cardinal.is_limit.ne_zero
- \+ *theorem* cardinal.is_limit.succ_lt
- \+ *theorem* cardinal.is_strong_limit.ne_zero
- \+ *theorem* cardinal.is_strong_limit.two_power_lt



## [2022-06-04 19:44:08](https://github.com/leanprover-community/mathlib/commit/d136cd5)
chore(data/pi/lex): turn `pi.lex.linear_order` into an instance ([#14389](https://github.com/leanprover-community/mathlib/pull/14389))
* Use `[is_well_order ι (<)]` instead of `(wf : well_founded ((<) : ι → ι → Prop))`. This way `pi.lex.linear_order` can be an instance.
* Add `pi.lex.order_bot`/`pi.lex.order_top`/`pi.lex.bounded_order`.
#### Estimated changes
Modified src/data/pi/lex.lean
- \+ *lemma* pi.is_trichotomous_lex
- \+/\- *lemma* pi.lex.le_of_forall_le
- \+ *lemma* pi.lex.le_of_of_lex_le
- \+ *lemma* pi.to_lex_monotone



## [2022-06-04 19:44:07](https://github.com/leanprover-community/mathlib/commit/9749297)
feat(measure_theory/integral/interval_integral): integrability of nonnegative derivatives on open intervals ([#14147](https://github.com/leanprover-community/mathlib/pull/14147))
Shows that derivatives of continuous functions are integrable when nonnegative.
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+/\- *lemma* integral_rpow
- \+ *lemma* interval_integral.interval_integrable_rpow'

Modified src/measure_theory/integral/integral_eq_improper.lean
- \+ *lemma* measure_theory.integrable_on_Ioc_of_interval_integral_norm_bounded
- \+ *lemma* measure_theory.integrable_on_Ioc_of_interval_integral_norm_bounded_left
- \+ *lemma* measure_theory.integrable_on_Ioc_of_interval_integral_norm_bounded_right

Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* integrable_on_Icc_iff_integrable_on_Ioc'
- \+ *lemma* integrable_on_Icc_iff_integrable_on_Ioc
- \+ *lemma* integrable_on_Icc_iff_integrable_on_Ioo
- \+ *lemma* integrable_on_Ioc_iff_integrable_on_Ioo'
- \+ *lemma* integrable_on_Ioc_iff_integrable_on_Ioo
- \+ *lemma* interval_integrable.comp_mul_left
- \+ *lemma* interval_integrable.iff_comp_neg
- \+ *lemma* interval_integrable_iff'
- \+ *lemma* interval_integrable_iff_integrable_Icc_of_le
- \- *lemma* interval_integral.integrable_on_Icc_iff_integrable_on_Ioc'
- \- *lemma* interval_integral.integrable_on_Icc_iff_integrable_on_Ioc
- \+ *lemma* interval_integral.integrable_on_deriv_of_nonneg
- \+ *lemma* interval_integral.integrable_on_deriv_right_of_nonneg
- \- *lemma* interval_integral.integral_eq_sub_of_has_deriv_right_of_le_real'
- \+ *theorem* interval_integral.interval_integrable_deriv_of_nonneg
- \- *lemma* interval_integral.interval_integrable_iff_integrable_Icc_of_le
- \+/\- *lemma* interval_integral.sub_le_integral_of_has_deriv_right_of_le
- \+ *lemma* interval_integral.sub_le_integral_of_has_deriv_right_of_le_Ico



## [2022-06-04 17:34:23](https://github.com/leanprover-community/mathlib/commit/93fb534)
refactor(topology/vector_bundle): split file ([#14535](https://github.com/leanprover-community/mathlib/pull/14535))
Also:
* Rename `pullback` -> `topological_vector_bundle.pullback`
* Use `delta_instance` instead of `local attribute [reducible]`
* Change module doc
* Remove transitive import
#### Estimated changes
Modified src/geometry/manifold/tangent_bundle.lean


Renamed src/topology/vector_bundle.lean to src/topology/vector_bundle/basic.lean
- \- *lemma* inducing_pullback_total_space_embedding
- \- *lemma* pullback.continuous_lift
- \- *lemma* pullback.continuous_proj
- \- *lemma* pullback.continuous_total_space_mk
- \- *def* pullback_topology
- \- *lemma* topological_vector_bundle.prod.inducing_diag
- \- *lemma* topological_vector_bundle.trivialization.base_set_prod
- \- *lemma* topological_vector_bundle.trivialization.continuous_linear_equiv_at_prod
- \- *lemma* topological_vector_bundle.trivialization.prod.continuous_inv_fun
- \- *lemma* topological_vector_bundle.trivialization.prod.continuous_to_fun
- \- *def* topological_vector_bundle.trivialization.prod.inv_fun'
- \- *lemma* topological_vector_bundle.trivialization.prod.left_inv
- \- *lemma* topological_vector_bundle.trivialization.prod.right_inv
- \- *def* topological_vector_bundle.trivialization.prod.to_fun'
- \- *def* topological_vector_bundle.trivialization.prod
- \- *lemma* topological_vector_bundle.trivialization.prod_apply
- \- *lemma* topological_vector_bundle.trivialization.prod_symm_apply
- \- *def* topological_vector_bundle.trivialization.pullback

Added src/topology/vector_bundle/prod.lean
- \+ *lemma* topological_vector_bundle.prod.inducing_diag
- \+ *lemma* topological_vector_bundle.trivialization.base_set_prod
- \+ *lemma* topological_vector_bundle.trivialization.continuous_linear_equiv_at_prod
- \+ *lemma* topological_vector_bundle.trivialization.prod.continuous_inv_fun
- \+ *lemma* topological_vector_bundle.trivialization.prod.continuous_to_fun
- \+ *def* topological_vector_bundle.trivialization.prod.inv_fun'
- \+ *lemma* topological_vector_bundle.trivialization.prod.left_inv
- \+ *lemma* topological_vector_bundle.trivialization.prod.right_inv
- \+ *def* topological_vector_bundle.trivialization.prod.to_fun'
- \+ *def* topological_vector_bundle.trivialization.prod
- \+ *lemma* topological_vector_bundle.trivialization.prod_apply
- \+ *lemma* topological_vector_bundle.trivialization.prod_symm_apply

Added src/topology/vector_bundle/pullback.lean
- \+ *lemma* inducing_pullback_total_space_embedding
- \+ *lemma* pullback.continuous_lift
- \+ *lemma* pullback.continuous_proj
- \+ *lemma* pullback.continuous_total_space_mk
- \+ *def* pullback_topology
- \+ *def* topological_vector_bundle.trivialization.pullback



## [2022-06-04 17:34:22](https://github.com/leanprover-community/mathlib/commit/3103a89)
feat(analysis/special_functions/exp): a lemma about `exp (f x) =O[l] const _ _` ([#14524](https://github.com/leanprover-community/mathlib/pull/14524))
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+ *lemma* asymptotics.is_O_const_left_iff_pos_le_norm

Modified src/analysis/special_functions/exp.lean
- \+ *lemma* real.is_O_one_exp_comp



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
Modified src/algebra/order/lattice_group.lean


Modified src/data/nat/prime.lean


Modified src/tactic/interactive.lean


Modified test/set.lean
- \+ *inductive* foo



## [2022-06-04 17:34:20](https://github.com/leanprover-community/mathlib/commit/a869df9)
feat(analysis/asymptotics/asymptotics): generalize `is_*.inv_rev` ([#14486](https://github.com/leanprover-community/mathlib/pull/14486))
Use weaker assumption `∀ᶠ x in l, f x = 0 → g x = 0` instead of `∀ᶠ x in l, f x ≠ 0`.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean


Modified src/measure_theory/integral/circle_integral.lean




## [2022-06-04 17:34:19](https://github.com/leanprover-community/mathlib/commit/8a6a793)
refactor(data/fin/basic): reformulate `fin.strict_mono_iff_lt_succ` ([#14482](https://github.com/leanprover-community/mathlib/pull/14482))
Use `fin.succ_cast` and `fin.succ`. This way we lose the case `n = 0`
but the statement looks more natural in other cases. Also add versions
for `monotone`, `antitone`, and `strict_anti`.
#### Estimated changes
Modified src/combinatorics/composition.lean


Modified src/data/fin/basic.lean
- \+ *lemma* fin.antitone_iff_succ_le
- \+ *lemma* fin.lift_fun_iff_succ
- \+ *lemma* fin.monotone_iff_le_succ
- \+ *lemma* fin.strict_anti_iff_succ_lt
- \+/\- *lemma* fin.strict_mono_iff_lt_succ

Modified src/order/jordan_holder.lean




## [2022-06-04 17:34:18](https://github.com/leanprover-community/mathlib/commit/cab5a45)
refactor(order/directed): use `(≥)` instead of `swap (≤)` ([#14474](https://github.com/leanprover-community/mathlib/pull/14474))
#### Estimated changes
Modified src/analysis/convex/quasiconvex.lean
- \+/\- *lemma* quasiconcave_on.convex

Modified src/category_theory/filtered.lean


Modified src/order/directed.lean
- \+/\- *lemma* exists_le_le
- \+/\- *theorem* exists_lt_of_directed_ge
- \+/\- *lemma* is_bot_iff_is_min
- \+/\- *lemma* is_bot_or_exists_lt

Modified src/order/ideal.lean
- \+/\- *lemma* order.ideal.inter_nonempty



## [2022-06-04 17:34:17](https://github.com/leanprover-community/mathlib/commit/b5973ba)
feat(measure_theory/measure/measure_space): there exists a ball of positive measure ([#14449](https://github.com/leanprover-community/mathlib/pull/14449))
Motivated by [#12933](https://github.com/leanprover-community/mathlib/pull/12933)
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.exists_pos_ball
- \+ *lemma* measure_theory.exists_pos_measure_of_cover
- \+ *lemma* measure_theory.exists_pos_preimage_ball



## [2022-06-04 15:25:58](https://github.com/leanprover-community/mathlib/commit/cfcc3a1)
chore(data/finsupp/basic): make arguments explicit ([#14551](https://github.com/leanprover-community/mathlib/pull/14551))
This follow the pattern that arguments to an `=` lemma should be explicit if they're not implied by other arguments.
#### Estimated changes
Modified src/algebra/monoid_algebra/grading.lean


Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.single_add
- \+/\- *lemma* finsupp.single_eq_pi_single
- \+/\- *lemma* finsupp.single_eq_update
- \+/\- *lemma* finsupp.single_neg
- \+/\- *lemma* finsupp.single_sub
- \+/\- *lemma* finsupp.single_zero
- \+/\- *lemma* finsupp.support_single_ne_zero

Modified src/data/finsupp/multiset.lean


Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* mv_polynomial.C_add

Modified src/data/mv_polynomial/variables.lean


Modified src/data/polynomial/basic.lean


Modified src/group_theory/free_abelian_group_finsupp.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/std_basis.lean


Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/polynomial/homogeneous.lean


Modified src/ring_theory/polynomial/symmetric.lean




## [2022-06-04 15:25:56](https://github.com/leanprover-community/mathlib/commit/b949240)
feat(algebra/{lie/subalgebra,module/submodule/pointwise}): submodules and lie subalgebras form canonically ordered additive monoids under addition ([#14529](https://github.com/leanprover-community/mathlib/pull/14529))
We can't actually make these instances because they result in loops for `simp`.
The `le_iff_exists_sup` lemma is probably not very useful for much beyond these new instances, but it matches `le_iff_exists_add`.
#### Estimated changes
Modified src/algebra/lie/subalgebra.lean
- \+ *def* lie_subalgebra.canonically_ordered_add_monoid

Modified src/algebra/module/submodule/pointwise.lean
- \+ *def* submodule.canonically_ordered_add_monoid

Modified src/order/lattice.lean
- \+ *theorem* le_iff_exists_sup

Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/nilpotent.lean




## [2022-06-04 15:25:56](https://github.com/leanprover-community/mathlib/commit/83c1cd8)
feat(set_theory/cardinal/cofinality): `ω` is a strong limit cardinal ([#14436](https://github.com/leanprover-community/mathlib/pull/14436))
#### Estimated changes
Modified src/set_theory/cardinal/cofinality.lean
- \+ *theorem* cardinal.is_limit_omega
- \+ *theorem* cardinal.is_strong_limit_omega



## [2022-06-04 15:25:55](https://github.com/leanprover-community/mathlib/commit/0746194)
feat(set_theory/cardinal/cofinality): limit cardinal is at least `ω` ([#14432](https://github.com/leanprover-community/mathlib/pull/14432))
#### Estimated changes
Modified src/set_theory/cardinal/cofinality.lean
- \+ *theorem* cardinal.is_limit.omega_le



## [2022-06-04 15:25:54](https://github.com/leanprover-community/mathlib/commit/15726ee)
move(set_theory/{schroeder_bernstein → cardinal/schroeder_bernstein}): move file ([#14426](https://github.com/leanprover-community/mathlib/pull/14426))
Schroeder-Bernstein is ultimately the statement that cardinals are a total order, so it should go in that folder.
#### Estimated changes
Modified src/set_theory/cardinal/basic.lean


Renamed src/set_theory/schroeder_bernstein.lean to src/set_theory/cardinal/schroeder_bernstein.lean




## [2022-06-04 15:25:53](https://github.com/leanprover-community/mathlib/commit/1f196cb)
feat(data/list/nodup): Add `list.nodup_iff` ([#14371](https://github.com/leanprover-community/mathlib/pull/14371))
Add `list.nodup_iff` and two helper lemmas `list.nth_le_eq_iff` and `list.some_nth_le_eq`
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.nth_le_eq_iff
- \+ *lemma* list.some_nth_le_eq

Modified src/data/list/nodup.lean
- \+ *lemma* list.nodup_iff_nth_ne_nth



## [2022-06-04 13:17:06](https://github.com/leanprover-community/mathlib/commit/aa7d90b)
doc(set_theory/ordinal/natural_ops): mention alternate names ([#14546](https://github.com/leanprover-community/mathlib/pull/14546))
#### Estimated changes
Modified src/set_theory/ordinal/natural_ops.lean




## [2022-06-04 13:17:05](https://github.com/leanprover-community/mathlib/commit/8ef2c02)
chore(order/bounded_order): move `order_dual` instances up, use them to golf lemmas ([#14544](https://github.com/leanprover-community/mathlib/pull/14544))
I only golf lemmas and `Prop`-valued instances to be sure that I don't add `order_dual`s to the statements.
#### Estimated changes
Modified src/order/bounded_order.lean
- \+/\- *lemma* not_is_max_bot
- \- *lemma* of_dual_bot
- \- *lemma* of_dual_top
- \+ *lemma* order_dual.of_dual_bot
- \+ *lemma* order_dual.of_dual_top
- \+ *lemma* order_dual.to_dual_bot
- \+ *lemma* order_dual.to_dual_top
- \- *lemma* to_dual_bot
- \- *lemma* to_dual_top
- \+/\- *lemma* with_top.not_top_le_coe



## [2022-06-04 13:17:04](https://github.com/leanprover-community/mathlib/commit/5002452)
refactor(topology): move code around ([#14525](https://github.com/leanprover-community/mathlib/pull/14525))
Create a new file `topology/inseparable` and more the definitions of `specializes` and `inseparable` to this file. This is a preparation to a larger refactor of these definitions.
#### Estimated changes
Modified src/topology/continuous_function/basic.lean
- \+ *lemma* continuous_map.map_specialization

Added src/topology/inseparable.lean
- \+ *lemma* inseparable.map
- \+ *def* inseparable
- \+ *lemma* inseparable_iff_closed
- \+ *lemma* inseparable_iff_closure
- \+ *lemma* inseparable_iff_nhds_eq
- \+ *lemma* inseparable_iff_specializes_and
- \+ *lemma* specialization_order.monotone_of_continuous
- \+ *def* specialization_preorder
- \+ *lemma* specializes.map
- \+ *lemma* specializes.trans
- \+ *def* specializes
- \+ *lemma* specializes_def
- \+ *lemma* specializes_iff_closure_subset
- \+ *lemma* specializes_iff_forall_closed
- \+ *lemma* specializes_iff_forall_open
- \+ *lemma* specializes_refl
- \+ *lemma* specializes_rfl
- \+ *lemma* subtype_inseparable_iff

Modified src/topology/separation.lean
- \- *lemma* inseparable.map
- \- *def* inseparable
- \- *lemma* inseparable_iff_closed
- \- *lemma* inseparable_iff_closure
- \- *lemma* inseparable_iff_nhds_eq
- \+ *def* specialization_order
- \+ *lemma* specializes.eq
- \+ *lemma* specializes_antisymm
- \+ *lemma* specializes_iff_eq
- \- *lemma* subtype_inseparable_iff

Modified src/topology/sober.lean
- \- *lemma* continuous_map.map_specialization
- \- *lemma* inseparable_iff_specializes_and
- \- *lemma* specialization_order.monotone_of_continuous
- \- *def* specialization_order
- \- *def* specialization_preorder
- \- *lemma* specializes.eq
- \- *lemma* specializes.map
- \- *lemma* specializes.trans
- \- *def* specializes
- \- *lemma* specializes_antisymm
- \- *lemma* specializes_def
- \- *lemma* specializes_iff_closure_subset
- \- *lemma* specializes_iff_eq
- \- *lemma* specializes_iff_forall_closed
- \- *lemma* specializes_iff_forall_open
- \- *lemma* specializes_refl
- \- *lemma* specializes_rfl



## [2022-06-04 13:17:03](https://github.com/leanprover-community/mathlib/commit/66b618d)
perf(measure_theory/probability_mass_function/monad): speed up proof ([#14519](https://github.com/leanprover-community/mathlib/pull/14519))
This causes a deterministic timeout in another PR.
#### Estimated changes
Modified src/measure_theory/probability_mass_function/monad.lean




## [2022-06-04 13:17:02](https://github.com/leanprover-community/mathlib/commit/3f26dfe)
feat(data/int/basic): Units are either equal or negatives of each other ([#14517](https://github.com/leanprover-community/mathlib/pull/14517))
This PR adds a lemma stating that units in the integers are either equal or negatives of each other. I have found this lemma to be useful for casework.
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.is_unit_eq_or_eq_neg



## [2022-06-04 13:17:01](https://github.com/leanprover-community/mathlib/commit/b332507)
feat(data/int/basic): Forward direction of `is_unit_iff_nat_abs_eq` ([#14516](https://github.com/leanprover-community/mathlib/pull/14516))
This PR adds the forward direction of `is_unit_iff_nat_abs_eq` as a separate lemma. This is useful since you often have `is_unit n` as a hypothesis, and `is_unit_iff_nat_abs_eq.mp hn` is a bit of a mouthful.
#### Estimated changes
Modified src/data/int/basic.lean




## [2022-06-04 13:17:00](https://github.com/leanprover-community/mathlib/commit/2a9be5b)
feat(analysis/special_functions): lemmas about filter `map`/`comap` ([#14513](https://github.com/leanprover-community/mathlib/pull/14513))
* add `comap_inf_principal_range` and `comap_nhds_within_range`;
* add `@[simp]` to `real.comap_exp_nhds_within_Ioi_zero`;
* add `real.comap_exp_nhds_zero`, `complex.comap_exp_comap_abs_at_top`, `complex.comap_exp_nhds_zero`, `complex.comap_exp_nhds_within_zero`, and `complex.tendsto_exp_nhds_zero_iff`;
* add `complex.map_exp_comap_re_at_bot` and `complex.map_exp_comap_re_at_top`;
* add `comap_norm_nhds_zero` and `complex.comap_abs_nhds_zero`.
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* complex.comap_abs_nhds_zero

Modified src/analysis/normed/group/basic.lean
- \+ *lemma* comap_norm_nhds_zero

Modified src/analysis/special_functions/complex/log.lean
- \+ *lemma* complex.map_exp_comap_re_at_bot
- \+ *lemma* complex.map_exp_comap_re_at_top

Modified src/analysis/special_functions/exp.lean
- \+ *lemma* complex.comap_exp_comap_abs_at_top
- \+ *lemma* complex.comap_exp_nhds_within_zero
- \+ *lemma* complex.comap_exp_nhds_zero
- \+ *lemma* complex.tendsto_exp_nhds_zero_iff
- \+/\- *lemma* real.comap_exp_nhds_within_Ioi_zero
- \+ *lemma* real.comap_exp_nhds_zero

Modified src/order/filter/basic.lean
- \+ *lemma* filter.comap_inf_principal_range

Modified src/topology/continuous_on.lean
- \+ *lemma* comap_nhds_within_range



## [2022-06-04 13:16:59](https://github.com/leanprover-community/mathlib/commit/0e943b1)
feat(order/boolean_algebra, set/basic): some compl lemmas ([#14508](https://github.com/leanprover-community/mathlib/pull/14508))
Added a few lemmas about complementation, and rephrased `compl_compl` and `mem_compl_image` to apply in `boolean_algebra` rather than `set (set _ ))`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *theorem* set.compl_compl_image
- \+/\- *theorem* set.mem_compl_image
- \+ *lemma* set.preimage_compl_eq_image_compl

Modified src/order/boolean_algebra.lean
- \+ *theorem* compl_eq_comm
- \+ *theorem* disjoint_iff_le_compl_left
- \+ *theorem* disjoint_iff_le_compl_right
- \+ *theorem* eq_compl_comm



## [2022-06-04 13:16:58](https://github.com/leanprover-community/mathlib/commit/27c4241)
feat(set_theory/ordinal/arithmetic): `has_exists_add_of_le` instance for `ordinal` ([#14499](https://github.com/leanprover-community/mathlib/pull/14499))
#### Estimated changes
Modified src/set_theory/ordinal/arithmetic.lean




## [2022-06-04 11:12:53](https://github.com/leanprover-community/mathlib/commit/7c57af9)
feat(order/bounds): Bounds on `set.image2` ([#14306](https://github.com/leanprover-community/mathlib/pull/14306))
`set.image2` analogues to the `set.image` lemmas.
#### Estimated changes
Modified src/order/bounds.lean
- \+ *lemma* bdd_above.bdd_above_image2_of_bdd_below
- \+ *lemma* bdd_above.bdd_below_image2_of_bdd_above
- \+ *lemma* bdd_above.image2
- \+ *lemma* bdd_above.image2_bdd_below
- \+ *lemma* bdd_below.bdd_above_image2_of_bdd_above
- \+ *lemma* bdd_below.bdd_below_image2_of_bdd_above
- \+ *lemma* bdd_below.image2
- \+ *lemma* bdd_below.image2_bdd_above
- \+ *lemma* image2_lower_bounds_lower_bounds_subset
- \+ *lemma* image2_lower_bounds_lower_bounds_subset_lower_bounds_image2
- \+ *lemma* image2_lower_bounds_upper_bounds_subset_lower_bounds_image2
- \+ *lemma* image2_lower_bounds_upper_bounds_subset_upper_bounds_image2
- \+ *lemma* image2_upper_bounds_lower_bounds_subset_lower_bounds_image2
- \+ *lemma* image2_upper_bounds_lower_bounds_subset_upper_bounds_image2
- \+ *lemma* image2_upper_bounds_upper_bounds_subset
- \+ *lemma* image2_upper_bounds_upper_bounds_subset_upper_bounds_image2
- \+ *lemma* is_greatest.image2
- \+ *lemma* is_greatest.is_greatest_image2_of_is_least
- \+ *lemma* is_greatest.is_least_image2
- \+ *lemma* is_greatest.is_least_image2_of_is_least
- \+ *lemma* is_least.image2
- \+ *lemma* is_least.is_greatest_image2
- \+ *lemma* is_least.is_greatest_image2_of_is_greatest
- \+ *lemma* is_least.is_least_image2_of_is_greatest
- \+ *lemma* mem_lower_bounds_image2
- \+ *lemma* mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_lower_bounds
- \+ *lemma* mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_upper_bounds
- \+ *lemma* mem_lower_bounds_image2_of_mem_upper_bounds
- \+ *lemma* mem_upper_bounds_image2
- \+ *lemma* mem_upper_bounds_image2_of_mem_lower_bounds
- \+ *lemma* mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_lower_bounds
- \+ *lemma* mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_upper_bounds



## [2022-06-04 08:30:21](https://github.com/leanprover-community/mathlib/commit/85fffda)
feat(order/conditionally_complete_lattice,data/real/nnreal): add 2 lemmas ([#14545](https://github.com/leanprover-community/mathlib/pull/14545))
Add `cInf_univ` and `nnreal.Inf_empty`.
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.Inf_empty

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* cInf_univ



## [2022-06-04 06:32:56](https://github.com/leanprover-community/mathlib/commit/72ac40e)
feat(data/multiset/basic): add some lemmas ([#14421](https://github.com/leanprover-community/mathlib/pull/14421))
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.countp_nsmul
- \+ *lemma* multiset.map_eq_cons
- \+ *lemma* multiset.map_surjective_of_surjective
- \+ *lemma* multiset.rel.countp_eq
- \+ *lemma* multiset.rel.trans



## [2022-06-04 04:55:08](https://github.com/leanprover-community/mathlib/commit/a418945)
chore(set_theory/surreal/basic): golf ([#14168](https://github.com/leanprover-community/mathlib/pull/14168))
We also add some basic lemmas for simplifying the definition of `numeric` when either a game's left or right moves are empty.
#### Estimated changes
Modified src/set_theory/surreal/basic.lean
- \+ *theorem* pgame.numeric_of_is_empty
- \+ *theorem* pgame.numeric_of_is_empty_left_moves
- \+ *theorem* pgame.numeric_of_is_empty_right_moves
- \+/\- *theorem* pgame.numeric_one
- \+/\- *theorem* pgame.numeric_zero
- \+/\- *def* surreal.mk



## [2022-06-04 04:16:45](https://github.com/leanprover-community/mathlib/commit/e1b3351)
feat(set_theory/game/pgame): Add dot notation on many lemmas ([#14149](https://github.com/leanprover-community/mathlib/pull/14149))
#### Estimated changes
Modified src/set_theory/game/basic.lean


Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/nim.lean
- \+/\- *lemma* pgame.grundy_value_star
- \+/\- *lemma* pgame.grundy_value_zero

Modified src/set_theory/game/pgame.lean
- \+ *theorem* has_le.le.not_lf
- \+ *theorem* pgame.equiv.ge
- \+ *theorem* pgame.equiv.le
- \+/\- *theorem* pgame.equiv_refl
- \+/\- *theorem* pgame.equiv_rfl
- \- *theorem* pgame.equiv_symm
- \- *theorem* pgame.equiv_trans
- \+ *theorem* pgame.lf.not_equiv'
- \+ *theorem* pgame.lf.not_equiv
- \+ *theorem* pgame.lf.not_le
- \+ *theorem* pgame.lf.not_lt
- \+/\- *theorem* pgame.lf_irrefl
- \+/\- *theorem* pgame.lf_of_fuzzy
- \+/\- *theorem* pgame.lf_of_lt

Modified src/set_theory/game/winner.lean


Modified src/set_theory/surreal/basic.lean
- \+/\- *theorem* pgame.le_of_lf
- \+/\- *theorem* pgame.lt_of_lf
- \+ *theorem* pgame.lt_or_equiv_or_gt



## [2022-06-03 22:33:16](https://github.com/leanprover-community/mathlib/commit/0098286)
feat(set_theory/ordinal/natural_ops): define natural addition ([#14291](https://github.com/leanprover-community/mathlib/pull/14291))
We define the natural addition operation on ordinals. We prove the basic properties, like commutativity, associativity, and cancellativity. We also provide the type synonym `nat_ordinal` for ordinals with natural operations, which allows us to take full advantage of this rich algebraic structure.
#### Estimated changes
Added src/set_theory/ordinal/natural_ops.lean
- \+ *theorem* nat_ordinal.add_one_eq_succ
- \+ *theorem* nat_ordinal.induction
- \+ *theorem* nat_ordinal.lt_wf
- \+ *theorem* nat_ordinal.succ_def
- \+ *def* nat_ordinal.to_ordinal
- \+ *theorem* nat_ordinal.to_ordinal_cast_nat
- \+ *theorem* nat_ordinal.to_ordinal_eq_one
- \+ *theorem* nat_ordinal.to_ordinal_eq_zero
- \+ *theorem* nat_ordinal.to_ordinal_max
- \+ *theorem* nat_ordinal.to_ordinal_min
- \+ *theorem* nat_ordinal.to_ordinal_one
- \+ *theorem* nat_ordinal.to_ordinal_symm_eq
- \+ *theorem* nat_ordinal.to_ordinal_to_nat_ordinal
- \+ *theorem* nat_ordinal.to_ordinal_zero
- \+ *def* nat_ordinal
- \+ *theorem* ordinal.add_le_nadd
- \+ *theorem* ordinal.blsub_nadd_of_mono
- \+ *theorem* ordinal.le_of_nadd_le_nadd_left
- \+ *theorem* ordinal.le_of_nadd_le_nadd_right
- \+ *theorem* ordinal.lt_nadd_iff
- \+ *theorem* ordinal.lt_of_nadd_lt_nadd_left
- \+ *theorem* ordinal.lt_of_nadd_lt_nadd_right
- \+ *theorem* ordinal.nadd_assoc
- \+ *theorem* ordinal.nadd_comm
- \+ *theorem* ordinal.nadd_def
- \+ *theorem* ordinal.nadd_le_iff
- \+ *theorem* ordinal.nadd_le_nadd_iff_left
- \+ *theorem* ordinal.nadd_le_nadd_iff_right
- \+ *theorem* ordinal.nadd_le_nadd_left
- \+ *theorem* ordinal.nadd_le_nadd_right
- \+ *theorem* ordinal.nadd_left_cancel
- \+ *theorem* ordinal.nadd_left_cancel_iff
- \+ *theorem* ordinal.nadd_lt_nadd_iff_left
- \+ *theorem* ordinal.nadd_lt_nadd_iff_right
- \+ *theorem* ordinal.nadd_lt_nadd_left
- \+ *theorem* ordinal.nadd_lt_nadd_right
- \+ *theorem* ordinal.nadd_nat
- \+ *theorem* ordinal.nadd_one
- \+ *theorem* ordinal.nadd_right_cancel
- \+ *theorem* ordinal.nadd_right_cancel_iff
- \+ *theorem* ordinal.nadd_succ
- \+ *theorem* ordinal.nadd_zero
- \+ *theorem* ordinal.nat_nadd
- \+ *theorem* ordinal.one_nadd
- \+ *theorem* ordinal.succ_nadd
- \+ *def* ordinal.to_nat_ordinal
- \+ *theorem* ordinal.to_nat_ordinal_cast_nat
- \+ *theorem* ordinal.to_nat_ordinal_eq_one
- \+ *theorem* ordinal.to_nat_ordinal_eq_zero
- \+ *theorem* ordinal.to_nat_ordinal_max
- \+ *theorem* ordinal.to_nat_ordinal_min
- \+ *theorem* ordinal.to_nat_ordinal_one
- \+ *theorem* ordinal.to_nat_ordinal_symm_eq
- \+ *theorem* ordinal.to_nat_ordinal_to_ordinal
- \+ *theorem* ordinal.to_nat_ordinal_zero
- \+ *theorem* ordinal.zero_nadd



## [2022-06-03 16:16:11](https://github.com/leanprover-community/mathlib/commit/d63246c)
feat(analysis/calculus/fderiv_measurable): the right derivative is measurable ([#14527](https://github.com/leanprover-community/mathlib/pull/14527))
We already know that the full Fréchet derivative is measurable. In this PR, we follow the same proof to show that the right derivative of a function defined on the real line is also measurable (the target space may be any complete vector space).
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_mem_iff
- \+ *lemma* deriv_within_Ioi_eq_Ici
- \+ *lemma* deriv_within_mem_iff
- \+ *lemma* differentiable_within_at_Ioi_iff_Ici
- \+ *theorem* has_deriv_at_filter_iff_is_o
- \+ *theorem* has_deriv_at_iff_is_o
- \+ *theorem* has_deriv_within_at_iff_is_o

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* fderiv_within_mem_iff

Modified src/analysis/calculus/fderiv_measurable.lean
- \+ *lemma* ae_measurable_deriv_within_Ici
- \+ *lemma* ae_measurable_deriv_within_Ioi
- \+ *lemma* ae_strongly_measurable_deriv_within_Ici
- \+ *lemma* ae_strongly_measurable_deriv_within_Ioi
- \+ *lemma* measurable_deriv_within_Ici
- \+ *lemma* measurable_deriv_within_Ioi
- \+ *theorem* measurable_set_of_differentiable_within_at_Ici
- \+ *theorem* measurable_set_of_differentiable_within_at_Ici_of_is_complete
- \+ *theorem* measurable_set_of_differentiable_within_at_Ioi
- \+ *def* right_deriv_measurable_aux.A
- \+ *lemma* right_deriv_measurable_aux.A_mem_nhds_within_Ioi
- \+ *lemma* right_deriv_measurable_aux.A_mono
- \+ *def* right_deriv_measurable_aux.B
- \+ *lemma* right_deriv_measurable_aux.B_mem_nhds_within_Ioi
- \+ *def* right_deriv_measurable_aux.D
- \+ *lemma* right_deriv_measurable_aux.D_subset_differentiable_set
- \+ *theorem* right_deriv_measurable_aux.differentiable_set_eq_D
- \+ *lemma* right_deriv_measurable_aux.differentiable_set_subset_D
- \+ *lemma* right_deriv_measurable_aux.le_of_mem_A
- \+ *lemma* right_deriv_measurable_aux.measurable_set_B
- \+ *lemma* right_deriv_measurable_aux.mem_A_of_differentiable
- \+ *lemma* right_deriv_measurable_aux.norm_sub_le_of_mem_A
- \+ *lemma* strongly_measurable_deriv_within_Ici
- \+ *lemma* strongly_measurable_deriv_within_Ioi

Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* measurable_set_of_mem_nhds_within_Ioi
- \+ *lemma* measurable_set_of_mem_nhds_within_Ioi_aux



## [2022-06-03 16:16:10](https://github.com/leanprover-community/mathlib/commit/2a21a86)
refactor(algebra/order/ring): turn `sq_le_sq` into an `iff` ([#14511](https://github.com/leanprover-community/mathlib/pull/14511))
* `sq_le_sq` and `sq_lt_sq` are now `iff` lemmas;
* drop `abs_le_abs_of_sq_le_sq` and `abs_lt_abs_of_sq_lt_sq`.
#### Estimated changes
Modified src/algebra/group_power/order.lean
- \- *theorem* abs_le_abs_of_sq_le_sq
- \- *theorem* abs_lt_abs_of_sq_lt_sq
- \+/\- *theorem* sq_le_sq
- \+/\- *theorem* sq_lt_sq

Modified src/analysis/inner_product_space/basic.lean


Modified src/analysis/special_functions/bernstein.lean
- \+ *lemma* bernstein_approximation.δ_pos

Modified src/number_theory/modular.lean




## [2022-06-03 14:08:37](https://github.com/leanprover-community/mathlib/commit/fa22603)
docs(order/boolean_algebra): typo in generalized boolean algebra doc ([#14536](https://github.com/leanprover-community/mathlib/pull/14536))
#### Estimated changes
Modified src/order/boolean_algebra.lean




## [2022-06-03 12:27:32](https://github.com/leanprover-community/mathlib/commit/6ca5910)
feat(measure_theory/integral/lebesgue): approximate a function by a finite integral function in a sigma-finite measure space. ([#14528](https://github.com/leanprover-community/mathlib/pull/14528))
If `L < ∫⁻ x, f x ∂μ`, then there exists a measurable function `g ≤ f` (even a simple function) with finite integral and `L < ∫⁻ x, g x ∂μ`, if the measure is sigma-finite.
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.exists_lt_lintegral_simple_func_of_lt_lintegral
- \+ *lemma* measure_theory.simple_func.exists_lt_lintegral_simple_func_of_lt_lintegral

Modified src/measure_theory/measure/regular.lean


Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.exists_lt_add_of_lt_add



## [2022-06-03 10:31:17](https://github.com/leanprover-community/mathlib/commit/bec8b65)
feat(analysis/calculus/tangent_cone): unique differentiability of open interval at endpoint ([#14530](https://github.com/leanprover-community/mathlib/pull/14530))
We show that, if a point belongs to the closure of a convex set with nonempty interior, then it is a point of unique differentiability. We apply this to the specific situation of `Ioi` and `Iio`.
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean
- \+ *lemma* mem_tangent_cone_of_open_segment_subset
- \+ *lemma* unique_diff_within_at_Iio
- \+ *lemma* unique_diff_within_at_Ioi
- \+ *theorem* unique_diff_within_at_convex



## [2022-06-03 10:31:16](https://github.com/leanprover-community/mathlib/commit/705160e)
feat(algebra/char_zero): add a lemma `ring_hom.injective_nat` ([#14414](https://github.com/leanprover-community/mathlib/pull/14414))
Note that there is a lemma `ring_hom.injective_int`.
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+ *lemma* ring_hom.injective_nat



## [2022-06-03 10:31:15](https://github.com/leanprover-community/mathlib/commit/d2dcb74)
feat(data/polynomial/eval): reduce assumptions, add a lemma ([#14391](https://github.com/leanprover-community/mathlib/pull/14391))
Note that there is a lemma `mv_polynomial.support_map_of_injective`.
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.support_map_of_injective
- \+/\- *lemma* polynomial.support_map_subset



## [2022-06-03 10:31:14](https://github.com/leanprover-community/mathlib/commit/c9d69a4)
feat(topology/algebra/module/finite_dimension): all linear maps from a finite dimensional T2 TVS are continuous ([#13460](https://github.com/leanprover-community/mathlib/pull/13460))
Summary of the changes :
- generalize a bunch of results from `analysis/normed_space/finite_dimension` (main ones are : `continuous_equiv_fun_basis`, `linear_map.continuous_of_finite_dimensional`, and related constructions like `linear_map.to_continuous_linear_map`) to arbitrary TVSs, and move them to a new file `topology/algebra/module/finite_dimension`
- generalize `linear_map.continuous_iff_is_closed_ker` to arbitrary TVSs, and move it from `analysis/normed_space/operator_norm` to the new file
- as needed by the generalizations, add lemma `unique_topology_of_t2` : if `𝕜` is a nondiscrete normed field, any T2 topology on `𝕜` which makes it a topological vector space over itself (with the norm topology) is *equal* to the norm topology
- finally, change `pi_eq_sum_univ` to take any `decidable_eq` instance (not just the classical ones), and fix later uses
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean
- \- *lemma* continuous_equiv_fun_basis
- \- *lemma* continuous_linear_map.coe_to_continuous_linear_equiv_of_det_ne_zero
- \- *def* continuous_linear_map.to_continuous_linear_equiv_of_det_ne_zero
- \- *lemma* continuous_linear_map.to_continuous_linear_equiv_of_det_ne_zero_apply
- \- *lemma* linear_equiv.coe_to_continuous_linear_equiv'
- \- *lemma* linear_equiv.coe_to_continuous_linear_equiv
- \- *lemma* linear_equiv.coe_to_continuous_linear_equiv_symm'
- \- *lemma* linear_equiv.coe_to_continuous_linear_equiv_symm
- \- *def* linear_equiv.to_continuous_linear_equiv
- \- *lemma* linear_equiv.to_linear_equiv_to_continuous_linear_equiv
- \- *lemma* linear_equiv.to_linear_equiv_to_continuous_linear_equiv_symm
- \- *lemma* linear_map.coe_to_continuous_linear_map'
- \- *lemma* linear_map.coe_to_continuous_linear_map
- \- *lemma* linear_map.coe_to_continuous_linear_map_symm
- \- *theorem* linear_map.continuous_of_finite_dimensional
- \- *lemma* linear_map.continuous_on_pi
- \- *def* linear_map.to_continuous_linear_map

Modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* linear_map.continuous_iff_is_closed_ker

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* linear_map.pi_apply_eq_sum_univ
- \+/\- *lemma* pi_eq_sum_univ

Modified src/linear_algebra/matrix/adjugate.lean


Modified src/ring_theory/ideal/quotient.lean


Added src/topology/algebra/module/finite_dimension.lean
- \+ *theorem* continuous_equiv_fun_basis
- \+ *lemma* continuous_linear_map.coe_to_continuous_linear_equiv_of_det_ne_zero
- \+ *def* continuous_linear_map.to_continuous_linear_equiv_of_det_ne_zero
- \+ *lemma* continuous_linear_map.to_continuous_linear_equiv_of_det_ne_zero_apply
- \+ *lemma* linear_equiv.coe_to_continuous_linear_equiv'
- \+ *lemma* linear_equiv.coe_to_continuous_linear_equiv
- \+ *lemma* linear_equiv.coe_to_continuous_linear_equiv_symm'
- \+ *lemma* linear_equiv.coe_to_continuous_linear_equiv_symm
- \+ *def* linear_equiv.to_continuous_linear_equiv
- \+ *lemma* linear_equiv.to_linear_equiv_to_continuous_linear_equiv
- \+ *lemma* linear_equiv.to_linear_equiv_to_continuous_linear_equiv_symm
- \+ *lemma* linear_map.coe_to_continuous_linear_map'
- \+ *lemma* linear_map.coe_to_continuous_linear_map
- \+ *lemma* linear_map.coe_to_continuous_linear_map_symm
- \+ *lemma* linear_map.continuous_iff_is_closed_ker
- \+ *theorem* linear_map.continuous_of_finite_dimensional
- \+ *lemma* linear_map.continuous_of_is_closed_ker
- \+ *lemma* linear_map.continuous_on_pi
- \+ *def* linear_map.to_continuous_linear_map
- \+ *lemma* unique_topology_of_t2



## [2022-06-03 08:57:19](https://github.com/leanprover-community/mathlib/commit/31cbfbb)
feat(linear_algebra/basis): repr_support_of_mem_span ([#14504](https://github.com/leanprover-community/mathlib/pull/14504))
This lemma states that if a vector is in the span of a subset of the basis vectors, only this subset of basis vectors will be used in its `repr` representation.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *lemma* basis.repr_support_subset_of_mem_span



## [2022-06-03 07:58:59](https://github.com/leanprover-community/mathlib/commit/2b69bb4)
feat(analysis/complex/upper_half_plane): extend action on upper half plane to GL_pos ([#12415](https://github.com/leanprover-community/mathlib/pull/12415))
This extends the action on the upper half plane from `SL_2` to `GL_pos`,
#### Estimated changes
Modified src/analysis/complex/upper_half_plane.lean
- \+ *lemma* upper_half_plane.SL_neg_smul
- \+ *lemma* upper_half_plane.SL_on_GL_pos_smul_apply
- \+/\- *lemma* upper_half_plane.coe_smul
- \+/\- *def* upper_half_plane.denom
- \+ *lemma* upper_half_plane.denom_apply
- \+/\- *lemma* upper_half_plane.denom_cocycle
- \+/\- *lemma* upper_half_plane.denom_ne_zero
- \+/\- *lemma* upper_half_plane.im_smul
- \+/\- *lemma* upper_half_plane.im_smul_eq_div_norm_sq
- \+/\- *lemma* upper_half_plane.mul_smul'
- \+/\- *lemma* upper_half_plane.neg_smul
- \+/\- *lemma* upper_half_plane.norm_sq_denom_ne_zero
- \+/\- *lemma* upper_half_plane.norm_sq_denom_pos
- \+/\- *def* upper_half_plane.num
- \+/\- *lemma* upper_half_plane.re_smul
- \+ *lemma* upper_half_plane.sl_moeb
- \+/\- *def* upper_half_plane.smul_aux'
- \+/\- *lemma* upper_half_plane.smul_aux'_im
- \+/\- *def* upper_half_plane.smul_aux
- \+ *lemma* upper_half_plane.special_linear_group.im_smul_eq_div_norm_sq
- \+ *lemma* upper_half_plane.subgroup_moeb
- \+ *lemma* upper_half_plane.subgroup_on_GL_pos_smul_apply
- \+ *lemma* upper_half_plane.subgroup_on_SL_apply
- \+ *lemma* upper_half_plane.subgroup_to_sl_moeb

Modified src/number_theory/modular.lean
- \+/\- *lemma* modular_group.coe_T_zpow_smul_eq
- \- *lemma* modular_group.coe_smul
- \- *lemma* modular_group.denom_apply
- \- *lemma* modular_group.im_smul
- \- *lemma* modular_group.im_smul_eq_div_norm_sq
- \- *lemma* modular_group.neg_smul
- \- *lemma* modular_group.re_smul
- \- *lemma* modular_group.smul_coe



## [2022-06-02 21:38:24](https://github.com/leanprover-community/mathlib/commit/1a1895c)
feat(data/nat/basic): add lemmas about `nat.bit_cases_on` ([#14481](https://github.com/leanprover-community/mathlib/pull/14481))
Also drop `nat.bit_cases` (was the same definition with a different
order of arguments).
#### Estimated changes
Modified src/data/nat/basic.lean
- \- *def* nat.bit_cases
- \+ *lemma* nat.bit_cases_on_bit0
- \+ *lemma* nat.bit_cases_on_bit1
- \+ *lemma* nat.bit_cases_on_bit
- \+ *lemma* nat.bit_cases_on_inj
- \+ *lemma* nat.bit_cases_on_injective



## [2022-06-02 19:38:29](https://github.com/leanprover-community/mathlib/commit/ade30c3)
feat(data/int/basic): Lemmas for when a square equals 1 ([#14501](https://github.com/leanprover-community/mathlib/pull/14501))
This PR adds two lemmas for when a square equals one. The `lt` lemma will be useful for irreducibility of x^n-x-1.
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.sq_eq_one_of_sq_le_three
- \+ *lemma* int.sq_eq_one_of_sq_lt_four



## [2022-06-02 19:38:28](https://github.com/leanprover-community/mathlib/commit/e443331)
refactor(field_theory/normal): generalize `lift_normal` and `restrict_normal` ([#14450](https://github.com/leanprover-community/mathlib/pull/14450))
This generalization seems useful. The example I have in mind is restricting a map `ϕ : E →ₐ[F] (algebraic_closure E)` to a map `ϕ : E →ₐ[F] E` when E/F is normal.
Coauthored by @mariainesdff
#### Estimated changes
Modified src/field_theory/normal.lean
- \+/\- *lemma* alg_equiv.lift_normal_commutes
- \+/\- *lemma* alg_equiv.restrict_lift_normal
- \+/\- *def* alg_equiv.restrict_normal_hom
- \+/\- *lemma* alg_equiv.restrict_normal_hom_surjective
- \+/\- *lemma* alg_hom.lift_normal_commutes
- \+/\- *lemma* alg_hom.restrict_lift_normal
- \+ *def* alg_hom.restrict_normal'
- \+/\- *lemma* is_solvable_of_is_scalar_tower



## [2022-06-02 17:31:51](https://github.com/leanprover-community/mathlib/commit/ae02583)
refactor(data/set/finite): protect `set.finite` ([#14344](https://github.com/leanprover-community/mathlib/pull/14344))
This change will make it so that it does not conflict with a top-level `finite` that will be added to complement `infinite`.
#### Estimated changes
Modified roadmap/topology/shrinking_lemma.lean


Modified src/algebra/big_operators/finprod.lean
- \+/\- *lemma* mul_finprod_cond_ne

Modified src/algebra/star/pointwise.lean
- \+/\- *lemma* set.finite.star

Modified src/analysis/convex/combination.lean
- \+/\- *lemma* set.finite.convex_hull_eq
- \+/\- *lemma* set.finite.convex_hull_eq_image

Modified src/analysis/convex/topology.lean
- \+/\- *lemma* set.finite.compact_convex_hull
- \+/\- *lemma* set.finite.is_closed_convex_hull

Modified src/data/polynomial/ring_division.lean


Modified src/data/set/countable.lean
- \+/\- *lemma* set.finite.countable

Modified src/data/set/finite.lean
- \+/\- *lemma* set.exists_max_image
- \+/\- *lemma* set.exists_min_image
- \+/\- *lemma* set.finite.bdd_above_bUnion
- \+/\- *lemma* set.finite.bdd_below_bUnion
- \+/\- *lemma* set.finite.fin_embedding
- \+/\- *lemma* set.finite.finite_subsets
- \+/\- *theorem* set.finite.inf_of_left
- \+/\- *theorem* set.finite.inf_of_right
- \+/\- *theorem* set.finite.map
- \+/\- *theorem* set.finite.of_diff
- \+/\- *theorem* set.finite.sUnion
- \+/\- *lemma* set.finite.sup
- \+/\- *inductive* set.finite
- \+/\- *lemma* set.finite_is_bot
- \+/\- *lemma* set.finite_is_top
- \+/\- *lemma* set.finite_le_nat
- \+/\- *lemma* set.finite_lt_nat
- \+/\- *theorem* set.finite_mem_finset
- \+/\- *lemma* set.finite_option
- \+/\- *lemma* set.finite_range_const
- \+/\- *lemma* set.finite_range_ite
- \+/\- *lemma* set.finite_subset_Union
- \+/\- *lemma* set.subsingleton.finite

Modified src/data/set/pointwise.lean
- \+/\- *lemma* set.finite.inv
- \+/\- *lemma* set.finite.mul
- \+/\- *lemma* set.finite.smul
- \+/\- *lemma* set.finite.smul_set
- \+/\- *lemma* set.finite.vsub

Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* finrank_span_le_card
- \+/\- *lemma* finrank_span_set_eq_card

Modified src/linear_algebra/linear_independent.lean


Modified src/measure_theory/integral/integrable_on.lean
- \+/\- *lemma* measure_theory.integrable_on_finite_Union

Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measurable_space_def.lean
- \+/\- *lemma* set.finite.measurable_set
- \+/\- *lemma* set.finite.measurable_set_bInter
- \+/\- *lemma* set.finite.measurable_set_bUnion
- \+/\- *lemma* set.finite.measurable_set_sInter
- \+/\- *lemma* set.finite.measurable_set_sUnion

Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.measure.count_apply_finite

Modified src/measure_theory/measure/measure_space_def.lean
- \+/\- *lemma* measure_theory.measure_bUnion_lt_top

Modified src/measure_theory/measure/null_measurable.lean
- \+/\- *lemma* set.finite.null_measurable_set_bInter
- \+/\- *lemma* set.finite.null_measurable_set_bUnion
- \+/\- *lemma* set.finite.null_measurable_set_sInter
- \+/\- *lemma* set.finite.null_measurable_set_sUnion

Modified src/model_theory/finitely_generated.lean
- \+/\- *theorem* first_order.language.substructure.fg_closure

Modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* set.finite.cSup_lt_iff
- \+/\- *lemma* set.finite.lt_cInf_iff
- \+/\- *lemma* set.nonempty.cInf_mem
- \+/\- *lemma* set.nonempty.cSup_mem

Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.bInter_mem
- \+/\- *lemma* filter.infi_principal_finite
- \+/\- *lemma* filter.mem_infi_of_Inter
- \+/\- *lemma* filter.sInter_mem

Modified src/order/filter/cofinite.lean
- \+/\- *lemma* filter.mem_cofinite

Modified src/order/filter/pi.lean
- \+/\- *lemma* filter.pi_mem_pi
- \+/\- *lemma* filter.pi_mem_pi_iff

Modified src/order/filter/ultrafilter.lean
- \+/\- *lemma* ultrafilter.finite_bUnion_mem_iff
- \+/\- *lemma* ultrafilter.finite_sUnion_mem_iff

Modified src/order/locally_finite.lean
- \+/\- *lemma* set.finite_Icc
- \+/\- *lemma* set.finite_Ici
- \+/\- *lemma* set.finite_Ico
- \+/\- *lemma* set.finite_Iic
- \+/\- *lemma* set.finite_Iio
- \+/\- *lemma* set.finite_Ioc
- \+/\- *lemma* set.finite_Ioi
- \+/\- *lemma* set.finite_Ioo

Modified src/ring_theory/algebraic_independent.lean


Modified src/ring_theory/artinian.lean


Modified src/ring_theory/noetherian.lean
- \+/\- *theorem* submodule.fg_span

Modified src/set_theory/cardinal/basic.lean
- \+/\- *theorem* cardinal.lt_omega_iff_finite

Modified src/topology/G_delta.lean
- \+/\- *lemma* set.finite.is_Gδ
- \+/\- *lemma* set.finite.is_Gδ_compl

Modified src/topology/bases.lean
- \+/\- *lemma* set.finite.is_separable

Modified src/topology/basic.lean
- \+/\- *lemma* is_closed_bUnion
- \+/\- *lemma* is_open_bInter
- \+/\- *lemma* is_open_sInter

Modified src/topology/bornology/basic.lean
- \+/\- *lemma* bornology.is_bounded_bUnion
- \+/\- *lemma* bornology.is_bounded_sUnion
- \+/\- *lemma* bornology.is_cobounded_bInter
- \+/\- *lemma* bornology.is_cobounded_sInter

Modified src/topology/constructions.lean


Modified src/topology/continuous_on.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* metric.bounded_bUnion
- \+/\- *lemma* metric.bounded_of_finite

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/hausdorff_dimension.lean
- \+/\- *lemma* dimH_finite

Modified src/topology/metric_space/metric_separated.lean
- \+/\- *lemma* is_metric_separated.finite_Union_left_iff
- \+/\- *lemma* is_metric_separated.finite_Union_right_iff

Modified src/topology/metric_space/metrizable.lean


Modified src/topology/metric_space/shrinking_lemma.lean
- \+/\- *lemma* exists_Union_ball_eq_radius_lt

Modified src/topology/partition_of_unity.lean


Modified src/topology/separation.lean


Modified src/topology/sequences.lean


Modified src/topology/shrinking_lemma.lean
- \+/\- *lemma* exists_Union_eq_closed_subset
- \+/\- *lemma* exists_Union_eq_closure_subset

Modified src/topology/subset_properties.lean
- \+/\- *lemma* set.finite.compact_bUnion
- \+/\- *lemma* set.finite.is_compact

Modified src/topology/uniform_space/cauchy.lean




## [2022-06-02 17:31:49](https://github.com/leanprover-community/mathlib/commit/28031a8)
feat(number_theory/factorization): evaluating arithmetic functions at prime powers ([#13817](https://github.com/leanprover-community/mathlib/pull/13817))
#### Estimated changes
Modified archive/100-theorems-list/70_perfect_numbers.lean


Modified src/data/int/cast.lean
- \+ *theorem* int.cast_ite

Modified src/data/list/dedup.lean
- \+ *lemma* list.repeat_dedup

Modified src/number_theory/arithmetic_function.lean
- \+ *lemma* nat.arithmetic_function.card_distinct_factors_apply_prime
- \+ *lemma* nat.arithmetic_function.card_distinct_factors_apply_prime_pow
- \+ *lemma* nat.arithmetic_function.card_distinct_factors_one
- \+ *lemma* nat.arithmetic_function.card_factors_apply_prime
- \+ *lemma* nat.arithmetic_function.card_factors_apply_prime_pow
- \+/\- *lemma* nat.arithmetic_function.coe_zeta_mul_coe_moebius
- \+ *lemma* nat.arithmetic_function.int_coe_mul
- \+ *lemma* nat.arithmetic_function.int_coe_one
- \+ *lemma* nat.arithmetic_function.is_multiplicative_one
- \+ *lemma* nat.arithmetic_function.moebius_apply_is_prime_pow_not_prime
- \+/\- *lemma* nat.arithmetic_function.moebius_apply_of_squarefree
- \+ *lemma* nat.arithmetic_function.moebius_apply_one
- \+ *lemma* nat.arithmetic_function.moebius_apply_prime
- \+ *lemma* nat.arithmetic_function.moebius_apply_prime_pow
- \+/\- *lemma* nat.arithmetic_function.moebius_eq_zero_of_not_squarefree
- \+ *lemma* nat.arithmetic_function.mul_apply_one
- \+ *lemma* nat.arithmetic_function.nat_coe_mul
- \+ *lemma* nat.arithmetic_function.nat_coe_one
- \+ *lemma* nat.arithmetic_function.one_apply
- \+/\- *lemma* nat.arithmetic_function.one_apply_ne
- \+/\- *lemma* nat.arithmetic_function.one_one
- \+ *lemma* nat.arithmetic_function.pow_zero_eq_zeta
- \+/\- *lemma* nat.arithmetic_function.sigma_one_apply
- \+ *lemma* nat.arithmetic_function.sigma_zero_apply
- \+ *lemma* nat.arithmetic_function.sigma_zero_apply_prime_pow



## [2022-06-02 15:58:16](https://github.com/leanprover-community/mathlib/commit/0575db0)
feat(topology/vector_bundle): define some useful linear maps globally ([#14484](https://github.com/leanprover-community/mathlib/pull/14484))
* Define `pretrivialization.symmₗ`, `pretrivialization.linear_map_at`, `trivialization.symmL`, `trivialization.continuous_linear_map_at`
* These are globally-defined (continuous) linear maps. They are linear equivalences on `e.base_set`, but it is useful to define these globally. They are defined as `0` outside `e.base_set`
* These are convenient to define the vector bundle of continuous linear maps.
#### Estimated changes
Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_if_const

Modified src/topology/vector_bundle.lean
- \+ *lemma* topological_vector_bundle.pretrivialization.coe_linear_map_at
- \+ *lemma* topological_vector_bundle.pretrivialization.coe_linear_map_at_of_mem
- \+ *lemma* topological_vector_bundle.pretrivialization.coe_symm_of_not_mem
- \+ *lemma* topological_vector_bundle.pretrivialization.linear_map_at_apply
- \+ *lemma* topological_vector_bundle.pretrivialization.linear_map_at_def_of_mem
- \+ *lemma* topological_vector_bundle.pretrivialization.linear_map_at_def_of_not_mem
- \+ *lemma* topological_vector_bundle.pretrivialization.linear_map_at_eq_zero
- \+ *lemma* topological_vector_bundle.pretrivialization.linear_map_at_symmₗ
- \+ *lemma* topological_vector_bundle.pretrivialization.symmₗ_linear_map_at
- \+ *lemma* topological_vector_bundle.trivialization.coe_continuous_linear_equiv_at_eq
- \+ *lemma* topological_vector_bundle.trivialization.coe_linear_map_at
- \+ *lemma* topological_vector_bundle.trivialization.coe_linear_map_at_of_mem
- \+ *lemma* topological_vector_bundle.trivialization.coe_symmₗ
- \+/\- *def* topological_vector_bundle.trivialization.continuous_linear_equiv_at
- \+ *def* topological_vector_bundle.trivialization.continuous_linear_map_at
- \+ *lemma* topological_vector_bundle.trivialization.continuous_linear_map_at_symmL
- \+ *lemma* topological_vector_bundle.trivialization.linear_equiv_at_apply
- \+ *lemma* topological_vector_bundle.trivialization.linear_equiv_at_symm_apply
- \+ *lemma* topological_vector_bundle.trivialization.linear_map_at_apply
- \+ *lemma* topological_vector_bundle.trivialization.linear_map_at_def_of_mem
- \+ *lemma* topological_vector_bundle.trivialization.linear_map_at_def_of_not_mem
- \+ *lemma* topological_vector_bundle.trivialization.linear_map_at_symmₗ
- \+ *def* topological_vector_bundle.trivialization.symmL
- \+ *lemma* topological_vector_bundle.trivialization.symmL_continuous_linear_map_at
- \+ *lemma* topological_vector_bundle.trivialization.symm_continuous_linear_equiv_at_eq
- \+ *lemma* topological_vector_bundle.trivialization.symmₗ_linear_map_at



## [2022-06-02 15:58:15](https://github.com/leanprover-community/mathlib/commit/c5f8d78)
doc(set_theory/cardinal/cofinality): add myself as author ([#14469](https://github.com/leanprover-community/mathlib/pull/14469))
#### Estimated changes
Modified src/set_theory/cardinal/cofinality.lean




## [2022-06-02 15:58:14](https://github.com/leanprover-community/mathlib/commit/4bd8c85)
feat(category_theory/limits): is_kernel_of_comp ([#14409](https://github.com/leanprover-community/mathlib/pull/14409))
From LTE.
Also rename `lift_comp_ι` to `lift_ι` for consistency with the general `has_limit` versions.
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \- *lemma* category_theory.limits.cofork.is_colimit.π_comp_desc
- \+ *lemma* category_theory.limits.cofork.is_colimit.π_desc
- \- *lemma* category_theory.limits.fork.is_limit.lift_comp_ι
- \+ *lemma* category_theory.limits.fork.is_limit.lift_ι

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.is_cokernel_of_comp
- \+ *def* category_theory.limits.is_kernel_of_comp

Modified src/category_theory/monad/monadicity.lean




## [2022-06-02 15:58:13](https://github.com/leanprover-community/mathlib/commit/2941590)
feat(linear_algebra/matrix): Spectral theorem for matrices ([#14231](https://github.com/leanprover-community/mathlib/pull/14231))
#### Estimated changes
Modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* euclidean_space.inner_eq_star_dot_product

Modified src/analysis/normed_space/pi_Lp.lean
- \+ *lemma* pi_Lp.equiv_apply'
- \+/\- *lemma* pi_Lp.equiv_apply
- \+ *lemma* pi_Lp.equiv_symm_apply'
- \+/\- *lemma* pi_Lp.equiv_symm_apply

Modified src/linear_algebra/matrix/basis.lean
- \+ *lemma* basis_to_matrix_basis_fun_mul
- \+ *lemma* basis_to_matrix_mul
- \+ *lemma* mul_basis_to_matrix

Added src/linear_algebra/matrix/hermitian.lean
- \+ *lemma* matrix.conj_transpose_map
- \+ *lemma* matrix.is_hermitian.add
- \+ *lemma* matrix.is_hermitian.apply
- \+ *lemma* matrix.is_hermitian.conj_transpose
- \+ *lemma* matrix.is_hermitian.eq
- \+ *lemma* matrix.is_hermitian.ext
- \+ *lemma* matrix.is_hermitian.ext_iff
- \+ *lemma* matrix.is_hermitian.from_blocks
- \+ *lemma* matrix.is_hermitian.map
- \+ *lemma* matrix.is_hermitian.minor
- \+ *lemma* matrix.is_hermitian.neg
- \+ *lemma* matrix.is_hermitian.sub
- \+ *lemma* matrix.is_hermitian.transpose
- \+ *def* matrix.is_hermitian
- \+ *lemma* matrix.is_hermitian_add_transpose_self
- \+ *lemma* matrix.is_hermitian_diagonal
- \+ *lemma* matrix.is_hermitian_from_blocks_iff
- \+ *lemma* matrix.is_hermitian_iff_is_self_adjoint
- \+ *lemma* matrix.is_hermitian_mul_conj_transpose_self
- \+ *lemma* matrix.is_hermitian_one
- \+ *lemma* matrix.is_hermitian_transpose_add_self
- \+ *lemma* matrix.is_hermitian_transpose_mul_self
- \+ *lemma* matrix.is_hermitian_zero

Added src/linear_algebra/matrix/spectrum.lean
- \+ *lemma* matrix.is_hermitian.eigenvector_matrix_mul_inv
- \+ *theorem* matrix.is_hermitian.spectral_theorem

Modified src/linear_algebra/matrix/to_lin.lean
- \+/\- *lemma* matrix.mul_vec_std_basis
- \+ *lemma* matrix.mul_vec_std_basis_apply



## [2022-06-02 13:48:11](https://github.com/leanprover-community/mathlib/commit/4e1eeeb)
feat(tactic/linear_combination): allow combinations of arbitrary proofs ([#14229](https://github.com/leanprover-community/mathlib/pull/14229))
This changes the syntax of `linear_combination` so that the combination is expressed using arithmetic operation. Credit to @digama0 for the parser. See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2313979.20arbitrary.20proof.20terms.20in.20.60linear_combination.60) for more details.
#### Estimated changes
Modified archive/100-theorems-list/37_solution_of_cubic.lean


Modified archive/imo/imo2001_q6.lean


Modified archive/imo/imo2008_q3.lean


Modified archive/imo/imo2008_q4.lean


Modified src/algebra/quadratic_discriminant.lean


Modified src/data/polynomial/identities.lean


Modified src/meta/expr.lean


Modified src/number_theory/fermat4.lean


Modified src/ring_theory/polynomial/chebyshev.lean


Modified src/ring_theory/witt_vector/discrete_valuation_ring.lean


Modified src/ring_theory/witt_vector/isocrystal.lean


Modified src/tactic/linear_combination.lean


Modified test/linear_combination.lean




## [2022-06-02 09:08:42](https://github.com/leanprover-community/mathlib/commit/57885b4)
feat(topological_space/vector_bundle): reformulate linearity condition ([#14485](https://github.com/leanprover-community/mathlib/pull/14485))
* Reformulate the linearity condition on (pre)trivializations of vector bundles using `total_space_mk`. Note: it is definitionally equal to the previous definition, but without using the coercion.
* Make one argument of `e.linear` implicit
* Simplify the proof of linearity of the product of vector bundles
#### Estimated changes
Modified src/topology/vector_bundle.lean
- \- *lemma* topological_vector_bundle.pretrivialization.linear



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
Modified archive/imo/imo2008_q4.lean


Modified src/algebra/quadratic_discriminant.lean


Modified src/number_theory/fermat4.lean


Modified src/tactic/linear_combination.lean


Modified test/linear_combination.lean




## [2022-06-01 20:32:56](https://github.com/leanprover-community/mathlib/commit/12ad63e)
feat(order/conditionally_complete_lattice): Map `Inf` by monotone function ([#14118](https://github.com/leanprover-community/mathlib/pull/14118))
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* monotone.map_Inf
- \+ *lemma* monotone_on.map_Inf



## [2022-06-01 17:27:02](https://github.com/leanprover-community/mathlib/commit/9600f4f)
feat(order/filter/bases): view a filter as a *bundled* filter basis ([#14506](https://github.com/leanprover-community/mathlib/pull/14506))
We already have `filter.basis_sets` which says that the elements of a filter are a basis of itself (in the `has_basis` sense), but we don't have the fact that they form a filter basis (in the `filter_basis` sense), and `x ∈ f.basis_sets.is_basis.filter_basis` is not defeq to `x ∈ f`
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *def* filter.as_basis
- \+ *lemma* filter.as_basis_filter



## [2022-06-01 17:27:01](https://github.com/leanprover-community/mathlib/commit/0950ba3)
refactor(topology/separation): rename `indistinguishable` to `inseparable` ([#14401](https://github.com/leanprover-community/mathlib/pull/14401))
* Replace `indistinguishable` by `inseparable` in the definition and lemma names. The word "indistinguishable" is too generic.
* Rename `t0_space_iff_distinguishable` to `t0_space_iff_not_inseparable` because the name `t0_space_iff_separable` is misleading, slightly golf the proof.
* Add `t0_space_iff_nhds_injective`, `nhds_injective`, reorder lemmas around these two.
#### Estimated changes
Modified src/algebraic_geometry/properties.lean


Modified src/topology/maps.lean


Modified src/topology/metric_space/basic.lean
- \- *lemma* metric.indistinguishable_iff
- \+ *lemma* metric.inseparable_iff

Modified src/topology/metric_space/emetric_space.lean
- \- *theorem* emetric.indistinguishable_iff
- \+ *theorem* emetric.inseparable_iff

Modified src/topology/separation.lean
- \- *lemma* indistinguishable.eq
- \- *lemma* indistinguishable.map
- \- *def* indistinguishable
- \- *lemma* indistinguishable_iff_closed
- \- *lemma* indistinguishable_iff_closure
- \- *lemma* indistinguishable_iff_nhds_eq
- \+ *lemma* inseparable.eq
- \+ *lemma* inseparable.map
- \+ *def* inseparable
- \+ *lemma* inseparable_iff_closed
- \+ *lemma* inseparable_iff_closure
- \+ *lemma* inseparable_iff_nhds_eq
- \+ *lemma* nhds_injective
- \- *lemma* subtype_indistinguishable_iff
- \+ *lemma* subtype_inseparable_iff
- \- *lemma* t0_space_iff_distinguishable
- \- *lemma* t0_space_iff_indistinguishable
- \+ *lemma* t0_space_iff_inseparable
- \+ *lemma* t0_space_iff_nhds_injective
- \+ *lemma* t0_space_iff_not_inseparable

Modified src/topology/sets/opens.lean


Modified src/topology/sober.lean
- \- *lemma* indistinguishable_iff_specializes_and
- \+ *lemma* inseparable_iff_specializes_and



## [2022-06-01 17:27:00](https://github.com/leanprover-community/mathlib/commit/9b3ea03)
feat(data/bundle): make arguments to proj and total_space_mk implicit ([#14359](https://github.com/leanprover-community/mathlib/pull/14359))
I will wait for a later PR to (maybe) fix the reducibility/simp of these declarations.
#### Estimated changes
Modified src/data/bundle.lean
- \- *def* bundle.proj
- \+/\- *lemma* bundle.sigma_mk_eq_total_space_mk
- \+/\- *lemma* bundle.to_total_space_coe
- \+/\- *lemma* bundle.total_space.eta
- \+ *def* bundle.total_space.proj
- \+/\- *lemma* bundle.total_space.proj_mk
- \+/\- *def* bundle.total_space_mk

Modified src/geometry/manifold/cont_mdiff.lean


Modified src/topology/fiber_bundle.lean
- \+/\- *lemma* topological_fiber_bundle_core.continuous_total_space_mk
- \+/\- *def* topological_fiber_bundle_core.proj

Modified src/topology/vector_bundle.lean
- \+/\- *lemma* topological_vector_bundle.continuous_proj
- \+/\- *lemma* topological_vector_bundle.continuous_total_space_mk
- \+/\- *lemma* topological_vector_bundle.pretrivialization.coe_fst'
- \+/\- *lemma* topological_vector_bundle.pretrivialization.coe_fst
- \+/\- *lemma* topological_vector_bundle.pretrivialization.mem_source
- \+/\- *lemma* topological_vector_bundle.pretrivialization.mk_proj_snd'
- \+/\- *lemma* topological_vector_bundle.pretrivialization.mk_proj_snd
- \+/\- *lemma* topological_vector_bundle.pretrivialization.proj_symm_apply
- \- *lemma* topological_vector_bundle.pretrivialization.symm_coe_fst'
- \+ *lemma* topological_vector_bundle.pretrivialization.symm_coe_proj
- \+/\- *lemma* topological_vector_bundle.trivialization.apply_symm_apply'
- \+/\- *lemma* topological_vector_bundle.trivialization.coe_fst'
- \+/\- *lemma* topological_vector_bundle.trivialization.coe_fst
- \+/\- *lemma* topological_vector_bundle.trivialization.mem_source
- \+/\- *lemma* topological_vector_bundle.trivialization.mk_proj_snd'
- \+/\- *lemma* topological_vector_bundle.trivialization.mk_proj_snd
- \+/\- *lemma* topological_vector_bundle.trivialization.prod.continuous_to_fun
- \+/\- *lemma* topological_vector_bundle.trivialization.proj_symm_apply'
- \- *lemma* topological_vector_bundle.trivialization.symm_coe_fst'
- \+ *lemma* topological_vector_bundle.trivialization.symm_coe_proj
- \+/\- *def* topological_vector_bundle_core.proj



## [2022-06-01 15:09:46](https://github.com/leanprover-community/mathlib/commit/dba797a)
feat(order/liminf_limsup): composition `g ∘ f` is bounded iff `f` is bounded ([#14479](https://github.com/leanprover-community/mathlib/pull/14479))
* If `g` is a monotone function that tends to infinity at infinity, then a filter is bounded from above under `g ∘ f` iff it is bounded under `f`, similarly for antitone functions and/or filter bounded from below.
* A filter is bounded from above under `real.exp ∘ f` iff it is is bounded from above under `f`.
* Use `monotone` in `real.exp_monotone`.
* Add `@[mono]` to `real.exp_strict_mono`.
#### Estimated changes
Modified src/analysis/special_functions/exp.lean
- \+ *lemma* real.is_bounded_under_ge_exp_comp
- \+ *lemma* real.is_bounded_under_le_exp_comp

Modified src/data/complex/exponential.lean
- \+/\- *lemma* real.exp_eq_one_iff
- \+/\- *lemma* real.exp_monotone
- \+/\- *lemma* real.exp_strict_mono

Modified src/order/liminf_limsup.lean
- \+ *lemma* antitone.is_bounded_under_ge_comp
- \+ *lemma* antitone.is_bounded_under_le_comp
- \+/\- *lemma* galois_connection.l_limsup_le
- \+ *lemma* monotone.is_bounded_under_ge_comp
- \+ *lemma* monotone.is_bounded_under_le_comp



## [2022-06-01 15:09:45](https://github.com/leanprover-community/mathlib/commit/047db39)
feat(algebra/char_p/basic): add lemma `ring_char.char_ne_zero_of_finite` ([#14454](https://github.com/leanprover-community/mathlib/pull/14454))
This adds the fact that a finite (not necessarily associative) ring cannot have characteristic zero.
See [this topic on Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Statements.20about.20finite.20rings).
#### Estimated changes
Modified src/algebra/char_p/basic.lean
- \+ *lemma* char_p.ring_char_ne_zero_of_fintype
- \+/\- *lemma* char_p_of_prime_pow_injective



## [2022-06-01 15:09:44](https://github.com/leanprover-community/mathlib/commit/df057e3)
feat(measure_theory/integral/lebesgue): integral over finite and countable sets ([#14447](https://github.com/leanprover-community/mathlib/pull/14447))
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.lintegral_countable
- \+/\- *lemma* measure_theory.lintegral_encodable
- \+ *lemma* measure_theory.lintegral_finset
- \+ *lemma* measure_theory.lintegral_fintype
- \+ *lemma* measure_theory.lintegral_insert
- \+ *lemma* measure_theory.lintegral_singleton'
- \+ *lemma* measure_theory.lintegral_singleton
- \+ *lemma* measure_theory.lintegral_unique



## [2022-06-01 15:09:43](https://github.com/leanprover-community/mathlib/commit/f0216ff)
refactor(combinatorics/simple_graph/basic): rename induced embedding on complete graphs ([#14404](https://github.com/leanprover-community/mathlib/pull/14404))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \- *def* simple_graph.embedding.complete_graph.of_embedding

Modified src/combinatorics/simple_graph/coloring.lean




## [2022-06-01 15:09:42](https://github.com/leanprover-community/mathlib/commit/0a0a60c)
feat(data/set/finite,order/*): generalize some lemmas from sets to (co)frames ([#14394](https://github.com/leanprover-community/mathlib/pull/14394))
* generalize `set.Union_inter_of_monotone` to an `order.frame`;
* add dual versions, both for `(co)frame`s and sets;
* same for `set.Union_Inter_of_monotone`.
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* infi_supr_of_antitone
- \+ *lemma* infi_supr_of_monotone
- \+ *lemma* set.Inter_Union_of_antitone
- \+ *lemma* set.Inter_Union_of_monotone
- \+ *lemma* set.Union_Inter_of_antitone
- \+/\- *lemma* set.Union_Inter_of_monotone
- \+ *lemma* set.finite.infi_bsupr_of_antitone
- \+ *lemma* set.finite.infi_bsupr_of_monotone
- \+ *lemma* set.finite.supr_binfi_of_antitone
- \+ *lemma* set.finite.supr_binfi_of_monotone
- \+ *lemma* supr_infi_of_antitone
- \+ *lemma* supr_infi_of_monotone

Modified src/data/set/lattice.lean
- \+ *lemma* set.Inter_union_of_antitone
- \+ *lemma* set.Inter_union_of_monotone
- \+ *lemma* set.Union_inter_of_antitone
- \+/\- *lemma* set.Union_inter_of_monotone

Modified src/order/complete_boolean_algebra.lean
- \+ *lemma* infi_sup_of_antitone
- \+ *lemma* infi_sup_of_monotone
- \+ *lemma* supr_inf_of_antitone
- \+ *lemma* supr_inf_of_monotone

Modified src/order/complete_lattice.lean
- \+ *lemma* infi_sup_infi_le
- \+ *lemma* le_supr_inf_supr
- \+ *lemma* supr_infi_le_infi_supr



## [2022-06-01 15:09:41](https://github.com/leanprover-community/mathlib/commit/892f889)
feat(data/matrix/basic): lemmas about mul_vec and single ([#13835](https://github.com/leanprover-community/mathlib/pull/13835))
We seem to be proving variants of the same statement over and over again; this introduces a new lemma that we can use to prove all these variants trivially in term mode. The new lemmas are:
* `matrix.mul_vec_single`
* `matrix.single_vec_mul`
* `matrix.diagonal_mul_vec_single`
* `matrix.single_vec_mul_diagonal`
A lot of the proofs got shorter by avoiding `ext` which invokes a more powerful lemma than we actually need.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.diagonal_mul_vec_single
- \+ *lemma* matrix.mul_vec_single
- \+ *lemma* matrix.single_vec_mul
- \+ *lemma* matrix.single_vec_mul_diagonal

Modified src/linear_algebra/matrix/diagonal.lean


Modified src/linear_algebra/matrix/to_lin.lean


Modified src/linear_algebra/std_basis.lean




## [2022-06-01 13:00:47](https://github.com/leanprover-community/mathlib/commit/f359d55)
feat(analysis/asymptotics/asymptotics): generalize `is_O.smul` etc ([#14487](https://github.com/leanprover-community/mathlib/pull/14487))
Allow `(k₁ : α → 𝕜) (k₂ : α → 𝕜')` instead of `(k₁ k₂ : α → 𝕜)`.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+/\- *theorem* asymptotics.is_O.smul
- \+/\- *theorem* asymptotics.is_O.smul_is_o
- \+/\- *theorem* asymptotics.is_O_with.smul
- \+/\- *theorem* asymptotics.is_o.smul
- \+/\- *theorem* asymptotics.is_o.smul_is_O



## [2022-06-01 13:00:46](https://github.com/leanprover-community/mathlib/commit/4f1c8cf)
feat(algebra/order/group): helper lemma `0 ≤ a + |a|` ([#14457](https://github.com/leanprover-community/mathlib/pull/14457))
Helper lemma for integers and absolute values.
#### Estimated changes
Modified src/algebra/order/group.lean
- \+ *lemma* add_abs_nonneg



## [2022-06-01 12:13:54](https://github.com/leanprover-community/mathlib/commit/f4fe790)
feat(topology/vector_bundle): redefine continuous coordinate change ([#14462](https://github.com/leanprover-community/mathlib/pull/14462))
* For any two trivializations, we define the coordinate change between the two trivializations: continous linear automorphism of `F`, defined by composing one trivialization with the inverse of the other. This is defined for any point in the intersection of their base sets, and we define it to be the identity function outside this set.
* Redefine `topological_vector_bundle`: we now require that this coordinate change between any two trivializations is continuous on the intersection of their base sets.
* Redefine `topological_vector_prebundle` with the existence of a continuous linear coordinate change function.
* Simplify the proofs that the coordinate change function is continuous for constructions on vector bundles.
#### Estimated changes
Modified src/topology/vector_bundle.lean
- \- *lemma* topological_vector_bundle.continuous_on_coord_change
- \- *def* topological_vector_bundle.coord_change
- \- *lemma* topological_vector_bundle.mem_source_trivialization_at
- \+/\- *def* topological_vector_bundle.pretrivialization.linear_equiv_at
- \- *lemma* topological_vector_bundle.trans_eq_coord_change
- \+ *lemma* topological_vector_bundle.trivial_topological_vector_bundle.trivialization.coord_change
- \+/\- *def* topological_vector_bundle.trivial_topological_vector_bundle.trivialization
- \+/\- *lemma* topological_vector_bundle.trivial_topological_vector_bundle.trivialization_source
- \+/\- *lemma* topological_vector_bundle.trivial_topological_vector_bundle.trivialization_target
- \+ *lemma* topological_vector_bundle.trivialization.coe_coord_change
- \+/\- *lemma* topological_vector_bundle.trivialization.comp_continuous_linear_equiv_at_eq_coord_change
- \+ *def* topological_vector_bundle.trivialization.coord_change
- \+ *lemma* topological_vector_bundle.trivialization.coord_change_apply'
- \+ *lemma* topological_vector_bundle.trivialization.coord_change_apply
- \+ *lemma* topological_vector_bundle.trivialization.coord_change_symm_apply
- \+ *def* topological_vector_bundle.trivialization.linear_equiv_at
- \+ *lemma* topological_vector_bundle.trivialization.mk_coord_change
- \+ *lemma* topological_vector_bundle_core.local_triv_coord_change_eq
- \+ *lemma* topological_vector_bundle_core.local_triv_symm_apply
- \+ *lemma* topological_vector_prebundle.continuous_on_coord_change
- \+ *def* topological_vector_prebundle.coord_change
- \+ *lemma* topological_vector_prebundle.coord_change_apply
- \+ *lemma* topological_vector_prebundle.mk_coord_change



## [2022-06-01 09:59:02](https://github.com/leanprover-community/mathlib/commit/60371b8)
refactor(topology/metric_space/lipschitz): use `function.End` ([#14502](https://github.com/leanprover-community/mathlib/pull/14502))
This way we avoid dependency on `category_theory`.
#### Estimated changes
Modified src/topology/metric_space/lipschitz.lean




## [2022-06-01 09:59:01](https://github.com/leanprover-community/mathlib/commit/7d71343)
chore(topology/algebra/uniform_field): Wrap in namespace ([#14498](https://github.com/leanprover-community/mathlib/pull/14498))
Put everything in `topology.algebra.uniform_field` in the `uniform_space.completion` namespace.
#### Estimated changes
Modified src/number_theory/function_field.lean


Modified src/ring_theory/dedekind_domain/adic_valuation.lean


Modified src/topology/algebra/uniform_field.lean
- \- *lemma* coe_inv
- \- *lemma* continuous_hat_inv
- \- *def* hat_inv
- \- *lemma* hat_inv_extends
- \- *lemma* mul_hat_inv_cancel
- \+ *lemma* uniform_space.completion.coe_inv
- \+ *lemma* uniform_space.completion.continuous_hat_inv
- \+ *def* uniform_space.completion.hat_inv
- \+ *lemma* uniform_space.completion.hat_inv_extends
- \+ *lemma* uniform_space.completion.mul_hat_inv_cancel



## [2022-06-01 09:18:43](https://github.com/leanprover-community/mathlib/commit/2a0f474)
feat(analysis/normed_space/star/character_space): compactness of the character space of a normed algebra ([#14135](https://github.com/leanprover-community/mathlib/pull/14135))
This PR puts a `compact_space` instance on `character_space 𝕜 A` for a normed algebra `A` using the Banach-Alaoglu theorem. This is a key step in developing the continuous functional calculus.
#### Estimated changes
Added src/analysis/normed_space/algebra.lean
- \+ *lemma* weak_dual.character_space.norm_one

Modified src/analysis/normed_space/weak_dual.lean
- \+ *lemma* weak_dual.to_normed_dual_apply

Modified src/topology/algebra/module/character_space.lean
- \+ *lemma* weak_dual.character_space.eq_set_map_one_map_mul
- \+ *lemma* weak_dual.character_space.is_closed



## [2022-06-01 01:59:39](https://github.com/leanprover-community/mathlib/commit/6b18362)
feat(data/zmod/quotient): More API for `orbit_zpowers_equiv` ([#14181](https://github.com/leanprover-community/mathlib/pull/14181))
This PR adds another `symm_apply` API lemma for `orbit_zpowers_equiv`, taking `(k : ℤ)` rather than `(k : zmod (minimal_period ((•) a) b))`.
#### Estimated changes
Modified src/data/zmod/quotient.lean
- \+ *lemma* add_action.orbit_zmultiples_equiv_symm_apply'
- \+ *lemma* mul_action.orbit_zpowers_equiv_symm_apply'
- \+/\- *lemma* mul_action.orbit_zpowers_equiv_symm_apply

Modified src/dynamics/periodic_pts.lean
- \+ *lemma* mul_action.pow_smul_mod_minimal_period
- \+ *lemma* mul_action.zpow_smul_mod_minimal_period

