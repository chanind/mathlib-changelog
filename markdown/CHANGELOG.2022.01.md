## [2022-01-31 22:22:23](https://github.com/leanprover-community/mathlib/commit/731d93b)
feat(group_theory/sylow): the normalizer is self-normalizing ([#11638](https://github.com/leanprover-community/mathlib/pull/11638))
with hat tip to Thomas Browning for a proof on Zuplip.
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *lemma* sylow.normal_of_normalizer_condition
- \+ *lemma* sylow.normal_of_normalizer_normal
- \+ *lemma* sylow.normalizer_normalizer



## [2022-01-31 22:22:22](https://github.com/leanprover-community/mathlib/commit/5964343)
feat(data/equiv): define `mul_equiv_class` ([#10760](https://github.com/leanprover-community/mathlib/pull/10760))
This PR defines a class of types of multiplicative (additive) equivalences, along the lines of [#9888](https://github.com/leanprover-community/mathlib/pull/9888).
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \- *lemma* add_equiv.map_sub
- \+/\- *lemma* mul_equiv.ext
- \+/\- *lemma* mul_equiv.ext_iff
- \- *lemma* mul_equiv.map_eq_one_iff
- \- *lemma* mul_equiv.map_inv
- \- *lemma* mul_equiv.map_mul
- \- *lemma* mul_equiv.map_one
- \+ *lemma* mul_equiv_class.map_eq_one_iff
- \+ *lemma* mul_equiv_class.map_ne_one_iff

Modified src/data/fun_like/basic.lean
- \+ *lemma* fun_like.coe_eq_coe_fn



## [2022-01-31 20:42:48](https://github.com/leanprover-community/mathlib/commit/a0bb6ea)
feat(algebraic_geometry): Open covers of the fibred product. ([#11733](https://github.com/leanprover-community/mathlib/pull/11733))
#### Estimated changes
Modified src/algebraic_geometry/open_immersion.lean
- \+ *def* algebraic_geometry.Scheme.open_cover.copy
- \+ *def* algebraic_geometry.Scheme.open_cover.pushforward_iso
- \+ *def* algebraic_geometry.Scheme.open_cover_of_is_iso

Modified src/algebraic_geometry/pullbacks.lean
- \+ *def* algebraic_geometry.Scheme.pullback.open_cover_of_base'
- \+ *def* algebraic_geometry.Scheme.pullback.open_cover_of_base
- \+ *def* algebraic_geometry.Scheme.pullback.open_cover_of_left
- \+ *def* algebraic_geometry.Scheme.pullback.open_cover_of_right



## [2022-01-31 20:42:46](https://github.com/leanprover-community/mathlib/commit/6130e57)
feat(topology/metric_space/basic): add some lemmas about spheres ([#11719](https://github.com/leanprover-community/mathlib/pull/11719))
#### Estimated changes
Modified src/analysis/normed_space/is_R_or_C.lean
- \+ *lemma* normed_space.sphere_nonempty_is_R_or_C

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.bounded_sphere
- \+ *theorem* metric.sphere_eq_empty_of_subsingleton
- \+ *theorem* metric.sphere_is_empty_of_subsingleton



## [2022-01-31 20:42:45](https://github.com/leanprover-community/mathlib/commit/ca17a18)
feat(algebra/pointwise): introduce `canonically_ordered_comm_semiring` on `set_semiring` ... ([#11580](https://github.com/leanprover-community/mathlib/pull/11580))
... assuming multiplication is commutative (there is no `canonically_ordered_`~~comm~~`_semiring` structure).
Also prove the relevant `no_zero_divisors` and `covariant_class` properties of addition and multiplication.
#### Estimated changes
Modified src/algebra/pointwise.lean




## [2022-01-31 20:42:43](https://github.com/leanprover-community/mathlib/commit/719b7b0)
feat(set_theory/ordinal_arithmetic, set_theory/cardinal_ordinal): `deriv` and `aleph` are enumerators ([#10987](https://github.com/leanprover-community/mathlib/pull/10987))
We prove `deriv_eq_enum_fp`, `ord_aleph'_eq_enum_card`, and `ord_aleph_eq_enum_card`.
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* cardinal.eq_aleph'_of_eq_card_ord
- \+ *theorem* cardinal.eq_aleph_of_eq_card_ord
- \+ *theorem* cardinal.ord_aleph'_eq_enum_card
- \+ *theorem* cardinal.ord_aleph_eq_enum_card
- \+ *theorem* cardinal.ord_card_unbounded'
- \+ *theorem* cardinal.ord_card_unbounded

Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.deriv_eq_enum_fp
- \+/\- *theorem* ordinal.deriv_limit
- \+ *theorem* ordinal.is_normal.fp_iff_deriv'
- \+/\- *theorem* ordinal.is_normal.fp_iff_deriv
- \+/\- *theorem* ordinal.is_normal.le_nfp
- \+/\- *theorem* ordinal.is_normal.lt_nfp
- \+ *theorem* ordinal.is_normal.nfp_unbounded



## [2022-01-31 19:55:53](https://github.com/leanprover-community/mathlib/commit/750f53c)
feat(analysis/seminorm): define the topology induced by a family of seminorms ([#11604](https://github.com/leanprover-community/mathlib/pull/11604))
Define the topology induced by a single seminorm and by a family of seminorms and show that boundedness of linear maps implies continuity.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+/\- *lemma* seminorm.ball_finset_sup
- \+/\- *lemma* seminorm.ball_finset_sup_eq_Inter
- \+ *lemma* seminorm.ball_smul
- \+ *lemma* seminorm.const_is_bounded
- \+ *lemma* seminorm.cont_normed_space_to_with_seminorms
- \+ *lemma* seminorm.cont_with_seminorms_normed_space
- \+ *lemma* seminorm.continuous_from_bounded
- \+ *lemma* seminorm.finset_sup_le_sum
- \+ *def* seminorm.is_bounded
- \+ *lemma* seminorm.is_bounded_const
- \+ *lemma* seminorm.is_bounded_sup
- \+ *def* seminorm.pullback
- \+ *def* seminorm.seminorm_add_group_filter_basis
- \+ *def* seminorm.seminorm_basis_zero
- \+ *lemma* seminorm.seminorm_basis_zero_add
- \+ *lemma* seminorm.seminorm_basis_zero_iff
- \+ *lemma* seminorm.seminorm_basis_zero_intersect
- \+ *lemma* seminorm.seminorm_basis_zero_mem
- \+ *lemma* seminorm.seminorm_basis_zero_neg
- \+ *lemma* seminorm.seminorm_basis_zero_nonempty
- \+ *lemma* seminorm.seminorm_basis_zero_singleton_mem
- \+ *lemma* seminorm.seminorm_basis_zero_smul
- \+ *lemma* seminorm.seminorm_basis_zero_smul_left
- \+ *lemma* seminorm.seminorm_basis_zero_smul_right
- \+ *lemma* seminorm.seminorm_basis_zero_zero
- \+ *def* seminorm.seminorm_module_filter_basis
- \+ *lemma* seminorm.smul_le_smul
- \+ *lemma* seminorm.with_seminorms_eq



## [2022-01-31 15:42:13](https://github.com/leanprover-community/mathlib/commit/ccbb848)
feat(set_theory/ordinal_arithmetic): `lt_add_of_limit` ([#11748](https://github.com/leanprover-community/mathlib/pull/11748))
Both `lt_mul_of_limit` and `lt_opow_of_limit` already existed, so this exclusion is odd to say the least.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.lt_add_of_limit



## [2022-01-31 15:42:12](https://github.com/leanprover-community/mathlib/commit/c0be8dc)
feat(model_theory/basic): define quotient structures ([#11747](https://github.com/leanprover-community/mathlib/pull/11747))
Defines prestructures and quotient structures
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *lemma* first_order.language.fun_map_quotient_mk
- \+ *lemma* first_order.language.realize_term_quotient_mk



## [2022-01-31 15:42:10](https://github.com/leanprover-community/mathlib/commit/792d3e5)
feat(group_theory/order_of_element): pow_eq_pow_iff_modeq ([#11737](https://github.com/leanprover-community/mathlib/pull/11737))
From flt-regular.
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* pow_eq_one_iff_modeq
- \+ *lemma* pow_eq_pow_iff_modeq



## [2022-01-31 15:42:09](https://github.com/leanprover-community/mathlib/commit/76b2a0e)
feat(group_theory/nilpotent): abelian iff nilpotency class ≤ 1 ([#11718](https://github.com/leanprover-community/mathlib/pull/11718))
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* comm_group.nilpotency_class_le_one
- \+ *def* comm_group_of_nilpotency_class

Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* comm_group.center_eq_top
- \+ *def* group.comm_group_of_center_eq_top



## [2022-01-31 15:42:08](https://github.com/leanprover-community/mathlib/commit/ff02774)
feat(algebra/squarefree): norm_num extension for squarefree ([#11666](https://github.com/leanprover-community/mathlib/pull/11666))
Adds two methods for computing `squarefree`: an improved algorithm for VM computation of squarefreedom via the `min_sq_fac` function, and a proof procedure which follows the same evaluation strategy as a `norm_num` extension.
#### Estimated changes
Modified src/algebra/squarefree.lean
- \+ *def* nat.min_sq_fac
- \+ *def* nat.min_sq_fac_aux
- \+ *theorem* nat.min_sq_fac_aux_has_prop
- \+ *theorem* nat.min_sq_fac_dvd
- \+ *theorem* nat.min_sq_fac_has_prop
- \+ *theorem* nat.min_sq_fac_le_of_dvd
- \+ *theorem* nat.min_sq_fac_prime
- \+ *def* nat.min_sq_fac_prop
- \+ *theorem* nat.min_sq_fac_prop_div
- \+ *lemma* nat.squarefree_iff_min_sq_fac
- \+ *theorem* nat.squarefree_iff_prime_squarefree
- \+ *theorem* nat.squarefree_two
- \+ *lemma* tactic.norm_num.not_squarefree_mul
- \+ *lemma* tactic.norm_num.squarefree_bit10
- \+ *lemma* tactic.norm_num.squarefree_bit1
- \+ *def* tactic.norm_num.squarefree_helper
- \+ *lemma* tactic.norm_num.squarefree_helper_0
- \+ *lemma* tactic.norm_num.squarefree_helper_1
- \+ *lemma* tactic.norm_num.squarefree_helper_2
- \+ *lemma* tactic.norm_num.squarefree_helper_3
- \+ *lemma* tactic.norm_num.squarefree_helper_4

Modified src/data/nat/prime.lean
- \+/\- *theorem* nat.min_fac_aux_has_prop
- \+ *lemma* nat.min_fac_lemma

Modified test/norm_num_ext.lean




## [2022-01-31 15:42:06](https://github.com/leanprover-community/mathlib/commit/c04daaf)
feat(measure_theory): typeclass for measures positive on nonempty opens ([#11652](https://github.com/leanprover-community/mathlib/pull/11652))
Add a typeclass for measures positive on nonempty opens, migrate `is(_add?)_haar_measure` to this API.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* continuous.is_open_pos_measure_map

Modified src/measure_theory/covering/besicovitch_vector_space.lean


Modified src/measure_theory/group/basic.lean
- \- *lemma* is_open.haar_pos
- \+ *lemma* measure_theory.is_open_pos_measure_of_mul_left_invariant_of_compact
- \+ *lemma* measure_theory.is_open_pos_measure_of_mul_left_invariant_of_regular
- \- *lemma* measure_theory.measure.haar_pos_of_nonempty_interior
- \- *lemma* measure_theory.measure_pos_of_is_open_of_is_mul_left_invariant
- \- *lemma* measure_theory.null_iff_empty_of_is_mul_left_invariant

Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/measure/haar.lean


Modified src/measure_theory/measure/haar_lebesgue.lean
- \- *lemma* measure_theory.measure.add_haar_ball_pos
- \- *lemma* measure_theory.measure.add_haar_closed_ball_pos

Added src/measure_theory/measure/open_pos.lean
- \+ *lemma* continuous.ae_eq_iff_eq
- \+ *lemma* emetric.measure_ball_pos
- \+ *lemma* emetric.measure_closed_ball_pos
- \+ *lemma* has_le.le.is_open_pos_measure
- \+ *lemma* is_open.eq_empty_of_measure_zero
- \+ *lemma* is_open.measure_eq_zero_iff
- \+ *lemma* is_open.measure_ne_zero
- \+ *lemma* is_open.measure_pos
- \+ *lemma* is_open.measure_pos_iff
- \+ *lemma* measure_theory.measure.eq_of_ae_eq
- \+ *lemma* measure_theory.measure.eq_on_Icc_of_ae_eq
- \+ *lemma* measure_theory.measure.eq_on_Ico_of_ae_eq
- \+ *lemma* measure_theory.measure.eq_on_Ioc_of_ae_eq
- \+ *lemma* measure_theory.measure.eq_on_Ioo_of_ae_eq
- \+ *lemma* measure_theory.measure.eq_on_of_ae_eq
- \+ *lemma* measure_theory.measure.eq_on_open_of_ae_eq
- \+ *lemma* measure_theory.measure.interior_eq_empty_of_null
- \+ *lemma* measure_theory.measure.is_open_pos_measure_smul
- \+ *lemma* measure_theory.measure.measure_Iio_pos
- \+ *lemma* measure_theory.measure.measure_Ioi_pos
- \+ *lemma* measure_theory.measure.measure_Ioo_eq_zero
- \+ *lemma* measure_theory.measure.measure_Ioo_pos
- \+ *lemma* measure_theory.measure.measure_pos_of_mem_nhds
- \+ *lemma* measure_theory.measure.measure_pos_of_nonempty_interior
- \+ *lemma* metric.measure_ball_pos
- \+ *lemma* metric.measure_closed_ball_pos

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* Ico_subset_closure_interior
- \+ *lemma* Ioc_subset_closure_interior
- \+ *lemma* Ioo_subset_closure_interior
- \+ *lemma* closure_interior_Icc

Modified src/topology/separation.lean
- \+ *lemma* set.eq_on.of_subset_closure



## [2022-01-31 15:42:05](https://github.com/leanprover-community/mathlib/commit/d6440a8)
feat(group_theory/nilpotent): add lemmas about `G / center G` ([#11592](https://github.com/leanprover-community/mathlib/pull/11592))
in particular its nilpotency class and an induction principle based on
that.
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* comap_upper_central_series_quotient_center
- \+ *lemma* nilpotency_class_eq_quotient_center_plus_one
- \+ *lemma* nilpotency_class_quotient_center
- \+ *lemma* nilpotency_class_zero_iff_subsingleton
- \+ *lemma* nilpotent_center_quotient_ind

Modified src/group_theory/quotient_group.lean
- \+ *lemma* quotient_group.comap_comap_center



## [2022-01-31 15:42:04](https://github.com/leanprover-community/mathlib/commit/06bb5b6)
feat(topology/nhds_set): define neighborhoods of a set ([#11520](https://github.com/leanprover-community/mathlib/pull/11520))
* Co-authored by @PatrickMassot
* From the sphere eversion project
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* interior_eq_univ
- \+ *lemma* is_open.mem_nhds_iff
- \+ *lemma* subset_interior_iff

Added src/topology/nhds_set.lean
- \+ *lemma* is_open.mem_nhds_set
- \+ *lemma* mem_nhds_set_empty
- \+ *lemma* mem_nhds_set_iff_exists
- \+ *lemma* mem_nhds_set_iff_forall
- \+ *lemma* mem_nhds_set_interior
- \+ *lemma* monotone_nhds_set
- \+ *def* nhds_set
- \+ *lemma* nhds_set_empty
- \+ *lemma* nhds_set_singleton
- \+ *lemma* nhds_set_univ
- \+ *lemma* subset_interior_iff_mem_nhds_set
- \+ *lemma* union_mem_nhds_set

Modified src/topology/separation.lean
- \+ *lemma* compl_singleton_mem_nhds_iff
- \+ *lemma* compl_singleton_mem_nhds_set_iff
- \+ *lemma* injective_nhds_set
- \+ *lemma* nhds_le_nhds_set
- \+ *lemma* nhds_set_inj_iff
- \+ *lemma* nhds_set_le_iff
- \+ *lemma* strict_mono_nhds_set



## [2022-01-31 15:42:02](https://github.com/leanprover-community/mathlib/commit/366d13e)
feat(scripts/lint_style): Add a check for unfreeze_local_instances ([#11509](https://github.com/leanprover-community/mathlib/pull/11509))
#### Estimated changes
Modified scripts/lint-style.py


Modified src/tactic/choose.lean




## [2022-01-31 14:14:34](https://github.com/leanprover-community/mathlib/commit/ada43f0)
feat(order/hom/complete_lattice): Complete lattice homomorphisms ([#11741](https://github.com/leanprover-community/mathlib/pull/11741))
Define frame homs and complete lattice homs using the `fun_like` along with weaker homomorphisms that only preserve `Sup`, `Inf`.
#### Estimated changes
Added src/order/hom/complete_lattice.lean
- \+ *lemma* Inf_hom.cancel_left
- \+ *lemma* Inf_hom.cancel_right
- \+ *lemma* Inf_hom.coe_comp
- \+ *lemma* Inf_hom.coe_id
- \+ *lemma* Inf_hom.coe_top
- \+ *def* Inf_hom.comp
- \+ *lemma* Inf_hom.comp_apply
- \+ *lemma* Inf_hom.comp_assoc
- \+ *lemma* Inf_hom.comp_id
- \+ *lemma* Inf_hom.ext
- \+ *lemma* Inf_hom.id_apply
- \+ *lemma* Inf_hom.id_comp
- \+ *lemma* Inf_hom.to_fun_eq_coe
- \+ *lemma* Inf_hom.top_apply
- \+ *structure* Inf_hom
- \+ *lemma* Sup_hom.bot_apply
- \+ *lemma* Sup_hom.cancel_left
- \+ *lemma* Sup_hom.cancel_right
- \+ *lemma* Sup_hom.coe_bot
- \+ *lemma* Sup_hom.coe_comp
- \+ *lemma* Sup_hom.coe_id
- \+ *def* Sup_hom.comp
- \+ *lemma* Sup_hom.comp_apply
- \+ *lemma* Sup_hom.comp_assoc
- \+ *lemma* Sup_hom.comp_id
- \+ *lemma* Sup_hom.ext
- \+ *lemma* Sup_hom.id_apply
- \+ *lemma* Sup_hom.id_comp
- \+ *lemma* Sup_hom.to_fun_eq_coe
- \+ *structure* Sup_hom
- \+ *lemma* complete_lattice_hom.cancel_left
- \+ *lemma* complete_lattice_hom.cancel_right
- \+ *lemma* complete_lattice_hom.coe_comp
- \+ *lemma* complete_lattice_hom.coe_id
- \+ *def* complete_lattice_hom.comp
- \+ *lemma* complete_lattice_hom.comp_apply
- \+ *lemma* complete_lattice_hom.comp_assoc
- \+ *lemma* complete_lattice_hom.comp_id
- \+ *lemma* complete_lattice_hom.ext
- \+ *lemma* complete_lattice_hom.id_apply
- \+ *lemma* complete_lattice_hom.id_comp
- \+ *def* complete_lattice_hom.to_Inf_hom
- \+ *lemma* complete_lattice_hom.to_fun_eq_coe
- \+ *structure* complete_lattice_hom
- \+ *lemma* frame_hom.bot_apply
- \+ *lemma* frame_hom.cancel_left
- \+ *lemma* frame_hom.cancel_right
- \+ *lemma* frame_hom.coe_bot
- \+ *lemma* frame_hom.coe_comp
- \+ *lemma* frame_hom.coe_id
- \+ *def* frame_hom.comp
- \+ *lemma* frame_hom.comp_apply
- \+ *lemma* frame_hom.comp_assoc
- \+ *lemma* frame_hom.comp_id
- \+ *lemma* frame_hom.ext
- \+ *lemma* frame_hom.id_apply
- \+ *lemma* frame_hom.id_comp
- \+ *lemma* frame_hom.to_fun_eq_coe
- \+ *def* frame_hom.to_lattice_hom
- \+ *structure* frame_hom
- \+ *lemma* map_infi
- \+ *lemma* map_infi₂
- \+ *lemma* map_supr
- \+ *lemma* map_supr₂



## [2022-01-31 14:14:32](https://github.com/leanprover-community/mathlib/commit/08fed82)
feat(category_theory/preadditive): the Yoneda embedding for preadditive categories ([#11740](https://github.com/leanprover-community/mathlib/pull/11740))
#### Estimated changes
Modified src/category_theory/endomorphism.lean
- \+ *lemma* category_theory.End.smul_left
- \+ *lemma* category_theory.End.smul_right

Modified src/category_theory/preadditive/default.lean


Modified src/category_theory/preadditive/opposite.lean


Added src/category_theory/preadditive/yoneda.lean
- \+ *def* category_theory.preadditive_coyoneda
- \+ *def* category_theory.preadditive_coyoneda_obj
- \+ *def* category_theory.preadditive_yoneda
- \+ *def* category_theory.preadditive_yoneda_obj
- \+ *lemma* category_theory.whiskering_preadditive_coyoneda
- \+ *lemma* category_theory.whiskering_preadditive_yoneda



## [2022-01-31 14:14:30](https://github.com/leanprover-community/mathlib/commit/323287e)
feat(data/polynomial/reverse): lemmas about evaluating reversed polynomials ([#11705](https://github.com/leanprover-community/mathlib/pull/11705))
#### Estimated changes
Modified src/data/polynomial/reverse.lean
- \+ *lemma* polynomial.eval₂_reflect_eq_zero_iff
- \+ *lemma* polynomial.eval₂_reflect_mul_pow
- \+ *lemma* polynomial.eval₂_reverse_eq_zero_iff
- \+ *lemma* polynomial.eval₂_reverse_mul_pow
- \+ *lemma* polynomial.reflect_C
- \+ *lemma* polynomial.rev_at_zero



## [2022-01-31 14:14:27](https://github.com/leanprover-community/mathlib/commit/bb2b58e)
feat(data/{nat,int}/parity): add division lemmas ([#11570](https://github.com/leanprover-community/mathlib/pull/11570))
Add lemmas of the form `even n → n / 2 * 2 = n` and `odd n → n / 2 * 2 + 1 = n`
#### Estimated changes
Modified src/data/int/parity.lean
- \+ *lemma* int.add_one_div_two_mul_two_of_odd
- \+ *lemma* int.div_two_mul_two_add_one_of_odd
- \+ *lemma* int.div_two_mul_two_of_even
- \+ *lemma* int.two_mul_div_two_add_one_of_odd
- \+ *lemma* int.two_mul_div_two_of_even
- \+ *lemma* int.two_mul_div_two_of_odd

Modified src/data/nat/parity.lean
- \+ *lemma* nat.div_two_mul_two_add_one_of_odd
- \+ *lemma* nat.div_two_mul_two_of_even
- \+ *lemma* nat.one_add_div_two_mul_two_of_odd
- \+ *lemma* nat.two_mul_div_two_add_one_of_odd
- \+ *lemma* nat.two_mul_div_two_of_even



## [2022-01-31 14:14:26](https://github.com/leanprover-community/mathlib/commit/6e016d2)
feat(linear_algebra/{tensor,exterior,clifford}_algebra): these algebras are graded by powers of the submodules of their generators ([#11542](https://github.com/leanprover-community/mathlib/pull/11542))
This shows that:
* The tensor and exterior algebras are `nat`-graded algebras, with each grade `n` corresponding to the submodule `(ι R).range ^ n`
* The clifford algebra is a superalgebra (`zmod 2`-graded algebra), with even and odd grades corresponding to even and odd powers of the submodule `(ι Q).range`
Eventually we'll also want to show that the tensor algebra is also graded with pieces in `pi_tensor_prod`, but that's a job for another time.
#### Estimated changes
Modified src/algebra/algebra/operations.lean


Modified src/algebra/direct_sum/internal.lean
- \+ *lemma* submodule.supr_eq_to_submodule_range

Added src/linear_algebra/clifford_algebra/grading.lean
- \+ *def* clifford_algebra.even_odd
- \+ *lemma* clifford_algebra.even_odd_mul_le
- \+ *def* clifford_algebra.graded_algebra.ι
- \+ *lemma* clifford_algebra.graded_algebra.ι_apply
- \+ *lemma* clifford_algebra.graded_algebra.ι_sq_scalar
- \+ *lemma* clifford_algebra.one_le_even_odd_zero
- \+ *lemma* clifford_algebra.range_ι_le_even_odd_one
- \+ *lemma* clifford_algebra.supr_ι_range_eq_top

Added src/linear_algebra/exterior_algebra/grading.lean
- \+ *def* exterior_algebra.graded_algebra.ι
- \+ *lemma* exterior_algebra.graded_algebra.ι_apply
- \+ *lemma* exterior_algebra.graded_algebra.ι_sq_zero

Added src/linear_algebra/tensor_algebra/grading.lean
- \+ *def* tensor_algebra.graded_algebra.ι
- \+ *lemma* tensor_algebra.graded_algebra.ι_apply



## [2022-01-31 12:36:17](https://github.com/leanprover-community/mathlib/commit/45cfb25)
refactor(order/bounded_order): Use `is_min`/`is_max` ([#11408](https://github.com/leanprover-community/mathlib/pull/11408))
Golf `order.bounded_order` and `data.set.basic` using `is_min`/`is_max`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *lemma* set.subsingleton_is_bot
- \+/\- *lemma* set.subsingleton_is_top

Modified src/data/set/intervals/basic.lean
- \- *lemma* is_bot.Iic_eq
- \- *lemma* is_bot.Iio_eq
- \+ *lemma* is_max.Ici_eq
- \+ *lemma* is_max.Ioi_eq
- \+ *lemma* is_min.Iic_eq
- \+ *lemma* is_min.Iio_eq
- \- *lemma* is_top.Ici_eq
- \- *lemma* is_top.Ioi_eq
- \+/\- *lemma* set.Ici_top
- \+/\- *lemma* set.Iic_bot
- \+/\- *lemma* set.Iio_bot
- \+/\- *lemma* set.Ioi_top

Modified src/order/atoms.lean
- \+ *lemma* is_simple_order.eq_bot_of_lt
- \+ *lemma* is_simple_order.eq_top_of_lt

Modified src/order/basic.lean
- \+ *lemma* eq_or_gt_of_le

Modified src/order/bounded_order.lean
- \+ *lemma* bot_le
- \- *theorem* bot_le
- \+ *lemma* bot_lt_top
- \+/\- *lemma* eq_bot_or_bot_lt
- \+/\- *lemma* is_bot_bot
- \+ *lemma* is_bot_iff_eq_bot
- \- *theorem* is_bot_iff_eq_bot
- \+ *lemma* is_max_iff_eq_top
- \+ *lemma* is_max_top
- \+ *lemma* is_min_bot
- \+ *lemma* is_min_iff_eq_bot
- \+ *lemma* is_top_iff_eq_top
- \- *theorem* is_top_iff_eq_top
- \+ *lemma* is_top_top
- \- *theorem* is_top_top
- \+ *lemma* le_top
- \- *theorem* le_top
- \+ *lemma* not_lt_bot
- \- *theorem* not_lt_bot
- \+ *lemma* not_top_lt
- \- *theorem* not_top_lt
- \+/\- *lemma* top_ne_bot

Modified src/order/max.lean
- \- *lemma* is_bot.unique
- \- *lemma* is_top.unique



## [2022-01-31 11:21:34](https://github.com/leanprover-community/mathlib/commit/2e1d8d6)
feat(ring_theory/roots_of_unity): `fun_like` support ([#11735](https://github.com/leanprover-community/mathlib/pull/11735))
- feat(ring_theory/roots_of_unity): ring_hom_class
- oops these could've been monoid homs from the start
#### Estimated changes
Modified src/field_theory/abel_ruffini.lean


Modified src/ring_theory/roots_of_unity.lean
- \+/\- *lemma* is_primitive_root.map_iff_of_injective
- \+/\- *lemma* is_primitive_root.map_of_injective
- \+/\- *lemma* is_primitive_root.of_map_of_injective
- \+ *lemma* map_root_of_unity_eq_pow_self
- \+ *def* restrict_roots_of_unity
- \+ *lemma* restrict_roots_of_unity_coe_apply
- \- *lemma* ring_hom.map_root_of_unity_eq_pow_self
- \- *def* ring_hom.restrict_roots_of_unity
- \- *lemma* ring_hom.restrict_roots_of_unity_coe_apply



## [2022-01-31 11:21:33](https://github.com/leanprover-community/mathlib/commit/406719e)
feat(order/hom/lattice): Composition of lattice homs ([#11676](https://github.com/leanprover-community/mathlib/pull/11676))
Define `top_hom.comp`, `bot_hom.comp`, `sup_hom.comp`, `inf_hom.comp`, `lattice_hom.comp`, `bounded_lattice_hom.comp`, `order_hom.to_lattice_hom`.
#### Estimated changes
Modified src/order/hom/lattice.lean
- \+ *lemma* bot_hom.cancel_left
- \+ *lemma* bot_hom.cancel_right
- \+ *lemma* bot_hom.coe_comp
- \+ *def* bot_hom.comp
- \+ *lemma* bot_hom.comp_apply
- \+ *lemma* bot_hom.comp_assoc
- \+ *lemma* bot_hom.comp_id
- \+ *lemma* bot_hom.id_comp
- \+ *lemma* bounded_lattice_hom.cancel_left
- \+ *lemma* bounded_lattice_hom.cancel_right
- \+ *lemma* bounded_lattice_hom.coe_comp
- \+ *lemma* bounded_lattice_hom.coe_comp_inf_hom
- \+ *lemma* bounded_lattice_hom.coe_comp_lattice_hom
- \+ *lemma* bounded_lattice_hom.coe_comp_sup_hom
- \+ *def* bounded_lattice_hom.comp
- \+ *lemma* bounded_lattice_hom.comp_apply
- \+ *lemma* bounded_lattice_hom.comp_assoc
- \+ *lemma* bounded_lattice_hom.comp_id
- \+ *lemma* bounded_lattice_hom.id_comp
- \+ *lemma* inf_hom.cancel_left
- \+ *lemma* inf_hom.cancel_right
- \+ *lemma* inf_hom.coe_comp
- \+ *def* inf_hom.comp
- \+ *lemma* inf_hom.comp_apply
- \+ *lemma* inf_hom.comp_assoc
- \+ *lemma* inf_hom.comp_id
- \+ *lemma* inf_hom.id_comp
- \+ *lemma* lattice_hom.cancel_left
- \+ *lemma* lattice_hom.cancel_right
- \+ *lemma* lattice_hom.coe_comp
- \+ *lemma* lattice_hom.coe_comp_inf_hom
- \+ *lemma* lattice_hom.coe_comp_sup_hom
- \+ *def* lattice_hom.comp
- \+ *lemma* lattice_hom.comp_apply
- \+ *lemma* lattice_hom.comp_assoc
- \+ *lemma* lattice_hom.comp_id
- \+ *lemma* lattice_hom.id_comp
- \+ *lemma* order_hom_class.coe_to_lattice_hom
- \+ *def* order_hom_class.to_lattice_hom
- \+ *lemma* order_hom_class.to_lattice_hom_apply
- \+ *def* order_hom_class.to_lattice_hom_class
- \+ *lemma* sup_hom.cancel_left
- \+ *lemma* sup_hom.cancel_right
- \+ *lemma* sup_hom.coe_comp
- \+ *def* sup_hom.comp
- \+ *lemma* sup_hom.comp_apply
- \+ *lemma* sup_hom.comp_assoc
- \+ *lemma* sup_hom.comp_id
- \+ *lemma* sup_hom.id_comp
- \+ *lemma* top_hom.cancel_left
- \+ *lemma* top_hom.cancel_right
- \+ *lemma* top_hom.coe_comp
- \+ *def* top_hom.comp
- \+ *lemma* top_hom.comp_apply
- \+ *lemma* top_hom.comp_assoc
- \+ *lemma* top_hom.comp_id
- \+ *lemma* top_hom.id_comp



## [2022-01-31 09:46:30](https://github.com/leanprover-community/mathlib/commit/16274f6)
chore(analysis/inner_product_space/lax_milgram): docs fixes ([#11745](https://github.com/leanprover-community/mathlib/pull/11745))
A couple of corrections, and a couple of additions of namespaces to docstrings so that they get hyperlinks when docgen is run.
#### Estimated changes
Modified src/analysis/inner_product_space/dual.lean


Modified src/analysis/inner_product_space/lax_milgram.lean




## [2022-01-31 09:46:29](https://github.com/leanprover-community/mathlib/commit/4388743)
feat(algebra/algebra/basic): add 1-related lemmas for `aut` ([#11738](https://github.com/leanprover-community/mathlib/pull/11738))
from flt-regular
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_equiv.one_apply
- \+/\- *def* alg_equiv.refl



## [2022-01-31 09:46:28](https://github.com/leanprover-community/mathlib/commit/7468d8d)
feat(measure_theory/integral/lebesgue): weaken assumptions for with_density lemmas ([#11711](https://github.com/leanprover-community/mathlib/pull/11711))
We state more precise versions of some lemmas about the measure `μ.with_density f`, making it possible to remove some assumptions down the road. For instance, the lemma
```lean
  integrable g (μ.with_density f) ↔ integrable (λ x, g x * (f x).to_real) μ
```
currently requires the measurability of `g`, while we can completely remove it with the new lemmas.
We also make `lintegral` irreducible.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* ae_measurable_of_unif_approx

Modified src/measure_theory/function/ae_eq_of_integral.lean


Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.coe_to_nnreal_ae_eq
- \+ *lemma* measure_theory.integrable_with_density_iff_integrable_smul'
- \+ *lemma* measure_theory.integrable_with_density_iff_integrable_smul

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.ae_measurable_with_density_ennreal_iff
- \+ *lemma* measure_theory.ae_measurable_with_density_iff
- \+ *lemma* measure_theory.ae_with_density_iff
- \+ *lemma* measure_theory.ae_with_density_iff_ae_restrict
- \+/\- *def* measure_theory.lintegral
- \+/\- *lemma* measure_theory.lintegral_map'
- \+/\- *lemma* measure_theory.lintegral_map
- \+ *lemma* measure_theory.lintegral_map_le
- \+ *lemma* measure_theory.lintegral_with_density_eq_lintegral_mul_non_measurable
- \+ *lemma* measure_theory.lintegral_with_density_eq_lintegral_mul_non_measurable₀
- \+ *lemma* measure_theory.lintegral_with_density_eq_lintegral_mul₀'
- \+ *lemma* measure_theory.lintegral_with_density_eq_lintegral_mul₀
- \+ *lemma* measure_theory.lintegral_with_density_le_lintegral_mul
- \+ *lemma* measure_theory.set_lintegral_with_density_eq_set_lintegral_mul_non_measurable
- \+ *lemma* measure_theory.set_lintegral_with_density_eq_set_lintegral_mul_non_measurable₀
- \+ *lemma* measure_theory.supr_lintegral_measurable_le_eq_lintegral
- \+ *lemma* measure_theory.with_density_apply_eq_zero
- \+ *lemma* measure_theory.with_density_congr_ae

Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.ae_of_ae_restrict_of_ae_restrict_compl

Modified src/probability_theory/density.lean




## [2022-01-31 09:46:27](https://github.com/leanprover-community/mathlib/commit/0c0ab69)
feat(topology/algebra/continuous_monoid_hom): Add `topological_group` instance ([#11707](https://github.com/leanprover-community/mathlib/pull/11707))
This PR proves that continuous monoid homs form a topological group.
#### Estimated changes
Modified src/topology/algebra/continuous_monoid_hom.lean
- \+ *lemma* continuous_monoid_hom.is_embedding
- \+ *lemma* continuous_monoid_hom.is_inducing



## [2022-01-31 09:46:26](https://github.com/leanprover-community/mathlib/commit/b3ad3f2)
feat(data/set/lattice): review ([#11672](https://github.com/leanprover-community/mathlib/pull/11672))
* generalize `set.Union_coe_set` and `set.Inter_coe_set` to dependent functions;
* add `bInter_Union`, `sUnion_Union`;
* drop `sUnion_bUnion`, `sInter_bUnion`.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+/\- *lemma* set.Inter_coe_set
- \+/\- *lemma* set.Union_coe_set
- \+ *lemma* set.bInter_Union
- \- *lemma* set.sInter_bUnion
- \+ *lemma* set.sUnion_Union
- \- *lemma* set.sUnion_bUnion

Modified src/order/filter/basic.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/paracompact.lean




## [2022-01-31 09:17:53](https://github.com/leanprover-community/mathlib/commit/6319a23)
feat(number_theory/cyclotomic): simplify `ne_zero`s ([#11715](https://github.com/leanprover-community/mathlib/pull/11715))
For flt-regular.
#### Estimated changes
Modified src/algebra/ne_zero.lean
- \+/\- *lemma* ne_zero.of_no_zero_smul_divisors
- \+ *lemma* ne_zero.trans

Modified src/number_theory/cyclotomic/basic.lean


Modified src/number_theory/cyclotomic/zeta.lean




## [2022-01-31 07:25:05](https://github.com/leanprover-community/mathlib/commit/8a67cf5)
feat(ring_theory/roots_of_unity): turn `is_primitive_root` into a member of `roots_of_unity` ([#11739](https://github.com/leanprover-community/mathlib/pull/11739))
from flt-regular
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+ *def* is_primitive_root.to_roots_of_unity



## [2022-01-31 00:40:09](https://github.com/leanprover-community/mathlib/commit/50cdb95)
fix(tactic/suggest): make `library_search` aware of definition of `ne` ([#11742](https://github.com/leanprover-community/mathlib/pull/11742))
`library_search` wasn't including results like `¬ a = b` to solve goals like `a ≠ b` and vice-versa.
Closes [#3428](https://github.com/leanprover-community/mathlib/pull/3428)
#### Estimated changes
Modified src/tactic/suggest.lean


Modified test/library_search/basic.lean




## [2022-01-30 23:01:38](https://github.com/leanprover-community/mathlib/commit/07735b8)
fix(tactic/squeeze_simp): "match failed" when `simp` works ([#11659](https://github.com/leanprover-community/mathlib/pull/11659))
Closes [#11196](https://github.com/leanprover-community/mathlib/pull/11196).
#### Estimated changes
Modified src/tactic/squeeze.lean


Modified test/squeeze.lean
- \+ *lemma* asda
- \+ *lemma* pnat.asda



## [2022-01-30 18:57:22](https://github.com/leanprover-community/mathlib/commit/b0fc10a)
chore(ring_theory/polynomial/chebyshev): simplify argument using new `linear_combination` tactic ([#11736](https://github.com/leanprover-community/mathlib/pull/11736))
cc @agoldb10 @robertylewis
#### Estimated changes
Modified src/ring_theory/polynomial/chebyshev.lean




## [2022-01-30 15:41:10](https://github.com/leanprover-community/mathlib/commit/97f61df)
feat(group_theory/sylow): preimages of sylow groups ([#11722](https://github.com/leanprover-community/mathlib/pull/11722))
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *lemma* sylow.coe_comap_of_injective
- \+ *lemma* sylow.coe_comap_of_ker_is_p_group
- \+ *lemma* sylow.coe_subtype
- \+ *def* sylow.comap_of_injective
- \+ *def* sylow.comap_of_ker_is_p_group
- \+ *def* sylow.subtype



## [2022-01-30 14:09:00](https://github.com/leanprover-community/mathlib/commit/02c720e)
chore(*): Rename `prod_dvd_prod` ([#11734](https://github.com/leanprover-community/mathlib/pull/11734))
In [#11693](https://github.com/leanprover-community/mathlib/pull/11693) I introduced the counterpart for `multiset` of `finset.prod_dvd_prod`.  It makes sense for these to have the same name, but there's already a different lemma called `multiset.prod_dvd_prod`, so the new lemma was named `multiset.prod_dvd_prod_of_dvd` instead.  As discussed with @riccardobrasca and @ericrbg at [#11693](https://github.com/leanprover-community/mathlib/pull/11693), this PR brings the names of the two counterpart lemmas into alignment, and also renames `multiset.prod_dvd_prod` to something more informative.
Renaming as follows:
`multiset.prod_dvd_prod` to `multiset.prod_dvd_prod_of_le`
`finset.prod_dvd_prod` to `finset.prod_dvd_prod_of_dvd`
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \- *lemma* finset.prod_dvd_prod
- \+ *lemma* finset.prod_dvd_prod_of_dvd

Modified src/algebra/big_operators/multiset.lean
- \- *lemma* multiset.prod_dvd_prod
- \+ *lemma* multiset.prod_dvd_prod_of_le

Modified src/algebra/squarefree.lean


Modified src/ring_theory/unique_factorization_domain.lean




## [2022-01-30 11:14:54](https://github.com/leanprover-community/mathlib/commit/a248bef)
feat(data/pnat/basic): 0 < n as a fact ([#11729](https://github.com/leanprover-community/mathlib/pull/11729))
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *lemma* pnat.fact_pos



## [2022-01-30 10:31:37](https://github.com/leanprover-community/mathlib/commit/dde904e)
chore(ring_theory/localization) weaken hypothesis from field to comm_ring ([#11713](https://github.com/leanprover-community/mathlib/pull/11713))
also making `B` an explicit argument
#### Estimated changes
Modified src/number_theory/class_number/finite.lean


Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/localization.lean
- \+/\- *lemma* is_fraction_ring.comap_is_algebraic_iff
- \+/\- *lemma* is_fraction_ring.is_algebraic_iff



## [2022-01-30 09:39:36](https://github.com/leanprover-community/mathlib/commit/1ea49d0)
feat(tactic/linear_combination): add tactic for combining equations ([#11646](https://github.com/leanprover-community/mathlib/pull/11646))
This new tactic attempts to prove a target equation by creating a linear combination of a list of equalities.  The name of this tactic is currently `linear_combination`, but I am open to other possible names.
An example of how to use this tactic is shown below:
```
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
by linear_combination (h1, 1) (h2, -2)
```
#### Estimated changes
Added src/tactic/linear_combination.lean
- \+ *lemma* linear_combo.all_on_left_equiv
- \+ *lemma* linear_combo.left_minus_right
- \+ *lemma* linear_combo.left_mul_both_sides
- \+ *lemma* linear_combo.replace_eq_expr
- \+ *lemma* linear_combo.sum_two_equations

Added test/linear_combination.lean




## [2022-01-30 07:28:22](https://github.com/leanprover-community/mathlib/commit/73e45c6)
chore(analysis/normed_space/star): create new folder for normed star rings ([#11732](https://github.com/leanprover-community/mathlib/pull/11732))
This PR moves the file `analysis/normed_space/star.lean` to the new folder `analysis/normed_space/star` (where it of course becomes `basic.lean`).
I expect a lot of material about C*-algebras to land in this folder in the (hopefully) near future.
#### Estimated changes
Modified src/analysis/inner_product_space/dual.lean


Renamed src/analysis/normed_space/star.lean to src/analysis/normed_space/star/basic.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/topology/continuous_function/bounded.lean




## [2022-01-30 05:38:03](https://github.com/leanprover-community/mathlib/commit/09d4f48)
chore(measure_theory/function/conditional_expectation): fix typo ([#11731](https://github.com/leanprover-community/mathlib/pull/11731))
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean




## [2022-01-30 00:12:37](https://github.com/leanprover-community/mathlib/commit/af1290c)
feat(field_theory/ratfunc): rational functions as Laurent series ([#11276](https://github.com/leanprover-community/mathlib/pull/11276))
#### Estimated changes
Modified src/field_theory/ratfunc.lean
- \+ *lemma* ratfunc.algebra_map_apply
- \+ *lemma* ratfunc.algebra_map_apply_div
- \+ *lemma* ratfunc.coe_C
- \+ *lemma* ratfunc.coe_X
- \+ *lemma* ratfunc.coe_add
- \+ *def* ratfunc.coe_alg_hom
- \+ *lemma* ratfunc.coe_apply
- \+ *lemma* ratfunc.coe_def
- \+ *lemma* ratfunc.coe_div
- \+ *lemma* ratfunc.coe_injective
- \+ *lemma* ratfunc.coe_mul
- \+ *lemma* ratfunc.coe_num_denom
- \+ *lemma* ratfunc.coe_one
- \+ *lemma* ratfunc.coe_smul
- \+ *lemma* ratfunc.coe_zero
- \+ *lemma* ratfunc.div_smul
- \+ *def* ratfunc.lift_alg_hom
- \+ *lemma* ratfunc.lift_alg_hom_apply
- \+ *lemma* ratfunc.lift_alg_hom_apply_div
- \+ *lemma* ratfunc.lift_alg_hom_apply_of_fraction_ring_mk
- \+ *lemma* ratfunc.lift_alg_hom_injective
- \+ *def* ratfunc.lift_monoid_with_zero_hom
- \+ *lemma* ratfunc.lift_monoid_with_zero_hom_apply
- \+ *lemma* ratfunc.lift_monoid_with_zero_hom_apply_div
- \+ *lemma* ratfunc.lift_monoid_with_zero_hom_apply_of_fraction_ring_mk
- \+ *lemma* ratfunc.lift_monoid_with_zero_hom_injective
- \+ *def* ratfunc.lift_ring_hom
- \+ *lemma* ratfunc.lift_ring_hom_apply
- \+ *lemma* ratfunc.lift_ring_hom_apply_div
- \+ *lemma* ratfunc.lift_ring_hom_apply_of_fraction_ring_mk
- \+ *lemma* ratfunc.lift_ring_hom_injective
- \+ *lemma* ratfunc.map_denom_ne_zero
- \+ *lemma* ratfunc.smul_eq_C_mul
- \+ *lemma* ratfunc.smul_eq_C_smul

Modified src/ring_theory/euclidean_domain.lean
- \+ *lemma* gcd_ne_zero_of_left
- \+ *lemma* gcd_ne_zero_of_right

Modified src/ring_theory/hahn_series.lean
- \+ *lemma* hahn_series.algebra_map_apply'
- \+ *lemma* polynomial.algebra_map_hahn_series_apply
- \+ *lemma* polynomial.algebra_map_hahn_series_injective

Modified src/ring_theory/localization.lean


Modified src/ring_theory/power_series/basic.lean




## [2022-01-29 21:10:10](https://github.com/leanprover-community/mathlib/commit/ff35218)
feat(analysis/convex/topology): add lemmas ([#11615](https://github.com/leanprover-community/mathlib/pull/11615))
#### Estimated changes
Modified src/analysis/convex/topology.lean
- \+ *lemma* convex.combo_interior_self_subset_interior
- \+ *lemma* convex.combo_mem_interior_left
- \+ *lemma* convex.combo_mem_interior_right
- \+ *lemma* convex.combo_self_interior_subset_interior
- \+ *lemma* convex.open_segment_subset_interior_left
- \+ *lemma* convex.open_segment_subset_interior_right

Modified src/topology/algebra/group.lean
- \+/\- *lemma* is_open.mul_left

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* is_closed.epigraph
- \+ *lemma* is_closed.hypograph



## [2022-01-29 20:28:18](https://github.com/leanprover-community/mathlib/commit/4085363)
feat(number_theory/prime_counting): The prime counting function ([#9080](https://github.com/leanprover-community/mathlib/pull/9080))
With an eye to implementing [this proof](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.238002/near/251178921), I am adding a file to define the prime counting function and prove a simple upper bound on it.
#### Estimated changes
Modified src/data/nat/totient.lean
- \+ *lemma* nat.Ico_filter_coprime_le
- \+ *lemma* nat.filter_coprime_Ico_eq_totient
- \+/\- *def* nat.totient
- \+/\- *lemma* nat.totient_eq_card_coprime

Added src/number_theory/prime_counting.lean
- \+ *lemma* nat.monotone_prime_counting'
- \+ *lemma* nat.monotone_prime_counting
- \+ *def* nat.prime_counting'
- \+ *lemma* nat.prime_counting'_add_le
- \+ *def* nat.prime_counting

Modified src/set_theory/fincard.lean
- \- *def* nat.card
- \+/\- *lemma* nat.card_eq_fintype_card
- \+/\- *lemma* nat.card_eq_zero_of_infinite



## [2022-01-29 19:47:13](https://github.com/leanprover-community/mathlib/commit/74250a0)
chore(representation_theory/maschke): remove recover ([#11721](https://github.com/leanprover-community/mathlib/pull/11721))
#### Estimated changes
Modified src/representation_theory/maschke.lean




## [2022-01-29 14:01:52](https://github.com/leanprover-community/mathlib/commit/49b8b91)
feat(data/fintype/order): `bool` is a boolean algebra ([#11694](https://github.com/leanprover-community/mathlib/pull/11694))
Provide the `boolean_algebra` instance for `bool` and use the machinery from `data.fintype.order` to deduce `complete_boolean_algebra bool` and `complete_linear_order bool`.
#### Estimated changes
Modified src/data/bool/basic.lean
- \+ *lemma* bool.band_bnot_self
- \+ *lemma* bool.bnot_band_self
- \+ *lemma* bool.bnot_bor_self
- \+ *lemma* bool.bor_bnot_self

Modified src/data/fintype/order.lean


Modified src/order/boolean_algebra.lean


Modified src/order/lattice.lean




## [2022-01-29 03:47:21](https://github.com/leanprover-community/mathlib/commit/fc4e471)
feat(measure_theory/group/basic): make is_[add|mul]_[left|right]_invariant classes ([#11655](https://github.com/leanprover-community/mathlib/pull/11655))
* Simplify the definitions of these classes
* Generalize many results about topological groups to measurable groups (still to do in `group/prod`)
* Simplify some proofs
* Make function argument of `integral_mul_[left|right]_eq_self` explicit (otherwise it is hard to apply this lemma in case the function is not a variable)
#### Estimated changes
Modified src/analysis/fourier.lean


Modified src/measure_theory/group/basic.lean
- \+ *lemma* measure_theory.forall_measure_preimage_mul_iff
- \+ *lemma* measure_theory.forall_measure_preimage_mul_right_iff
- \- *lemma* measure_theory.is_mul_left_invariant.inv
- \- *lemma* measure_theory.is_mul_left_invariant.measure_lt_top_of_is_compact'
- \- *lemma* measure_theory.is_mul_left_invariant.measure_lt_top_of_is_compact
- \- *lemma* measure_theory.is_mul_left_invariant.measure_ne_zero_iff_nonempty
- \- *lemma* measure_theory.is_mul_left_invariant.measure_pos_iff_nonempty
- \- *lemma* measure_theory.is_mul_left_invariant.measure_pos_of_is_open
- \- *lemma* measure_theory.is_mul_left_invariant.measure_preimage_mul
- \- *lemma* measure_theory.is_mul_left_invariant.null_iff
- \- *lemma* measure_theory.is_mul_left_invariant.null_iff_empty
- \- *lemma* measure_theory.is_mul_left_invariant.smul
- \- *def* measure_theory.is_mul_left_invariant
- \- *lemma* measure_theory.is_mul_left_invariant_inv
- \- *lemma* measure_theory.is_mul_right_invariant.inv
- \- *lemma* measure_theory.is_mul_right_invariant.smul
- \- *def* measure_theory.is_mul_right_invariant
- \- *lemma* measure_theory.is_mul_right_invariant_inv
- \+/\- *lemma* measure_theory.lintegral_eq_zero_of_is_mul_left_invariant
- \+/\- *lemma* measure_theory.lintegral_mul_left_eq_self
- \+/\- *lemma* measure_theory.lintegral_mul_right_eq_self
- \+ *lemma* measure_theory.map_mul_left_eq_self
- \+ *lemma* measure_theory.map_mul_right_eq_self
- \- *lemma* measure_theory.measure.haar_preimage_mul
- \- *lemma* measure_theory.measure.haar_preimage_mul_right
- \+/\- *lemma* measure_theory.measure.inv_apply
- \- *lemma* measure_theory.measure.is_mul_left_invariant_haar
- \- *lemma* measure_theory.measure.map_mul_left_eq_self
- \- *lemma* measure_theory.measure.map_mul_right_eq_self
- \+ *lemma* measure_theory.measure_lt_top_of_is_compact_of_is_mul_left_invariant'
- \+ *lemma* measure_theory.measure_lt_top_of_is_compact_of_is_mul_left_invariant
- \+ *lemma* measure_theory.measure_ne_zero_iff_nonempty_of_is_mul_left_invariant
- \+ *lemma* measure_theory.measure_pos_iff_nonempty_of_is_mul_left_invariant
- \+ *lemma* measure_theory.measure_pos_of_is_open_of_is_mul_left_invariant
- \+ *lemma* measure_theory.measure_preimage_mul
- \+ *lemma* measure_theory.measure_preimage_mul_right
- \+ *lemma* measure_theory.null_iff_empty_of_is_mul_left_invariant
- \+ *lemma* measure_theory.null_iff_of_is_mul_left_invariant
- \+/\- *lemma* measure_theory.regular_inv_iff

Modified src/measure_theory/group/prod.lean
- \+/\- *lemma* measure_theory.lintegral_lintegral_mul_inv
- \+/\- *lemma* measure_theory.map_prod_inv_mul_eq
- \+/\- *lemma* measure_theory.map_prod_inv_mul_eq_swap
- \+/\- *lemma* measure_theory.map_prod_mul_eq
- \+/\- *lemma* measure_theory.map_prod_mul_eq_swap
- \+/\- *lemma* measure_theory.map_prod_mul_inv_eq
- \+/\- *lemma* measure_theory.measure_inv_null
- \+/\- *lemma* measure_theory.measure_lintegral_div_measure
- \+/\- *lemma* measure_theory.measure_mul_measure_eq
- \+/\- *lemma* measure_theory.measure_mul_right_ne_zero
- \+/\- *lemma* measure_theory.measure_mul_right_null
- \+/\- *lemma* measure_theory.quasi_measure_preserving_inv

Modified src/measure_theory/integral/bochner.lean
- \+/\- *lemma* measure_theory.integral_mul_left_eq_self
- \+/\- *lemma* measure_theory.integral_mul_right_eq_self
- \+/\- *lemma* measure_theory.integral_zero_of_mul_left_eq_neg
- \+/\- *lemma* measure_theory.integral_zero_of_mul_right_eq_neg

Modified src/measure_theory/measure/haar.lean
- \+/\- *theorem* measure_theory.measure.haar_measure_unique
- \- *lemma* measure_theory.measure.is_mul_left_invariant_haar_measure
- \+/\- *theorem* measure_theory.measure.regular_of_is_mul_left_invariant

Modified src/measure_theory/measure/haar_lebesgue.lean
- \- *lemma* measure_theory.is_add_left_invariant_real_volume
- \- *lemma* measure_theory.is_add_left_invariant_real_volume_pi



## [2022-01-29 01:17:00](https://github.com/leanprover-community/mathlib/commit/44105f8)
feat(analysis/inner_product_space): proof of the Lax Milgram theorem ([#11491](https://github.com/leanprover-community/mathlib/pull/11491))
My work on the Lax Milgram theorem, as suggested by @hrmacbeth. Done following the [slides from Peter Howard (Texas A&M University)](https://www.math.tamu.edu/~phoward/m612/s20/elliptic2.pdf).
Closes [#10213](https://github.com/leanprover-community/mathlib/pull/10213).
#### Estimated changes
Modified docs/references.bib


Modified docs/undergrad.yaml


Modified src/analysis/inner_product_space/dual.lean
- \+ *def* inner_product_space.continuous_linear_map_of_bilin
- \+ *lemma* inner_product_space.continuous_linear_map_of_bilin_apply
- \+ *lemma* inner_product_space.unique_continuous_linear_map_of_bilin

Added src/analysis/inner_product_space/lax_milgram.lean
- \+ *lemma* is_coercive.antilipschitz
- \+ *lemma* is_coercive.bounded_below
- \+ *lemma* is_coercive.closed_range
- \+ *def* is_coercive.continuous_linear_equiv_of_bilin
- \+ *lemma* is_coercive.continuous_linear_equiv_of_bilin_apply
- \+ *lemma* is_coercive.ker_eq_bot
- \+ *lemma* is_coercive.range_eq_top
- \+ *lemma* is_coercive.unique_continuous_linear_equiv_of_bilin

Modified src/analysis/normed_space/operator_norm.lean
- \+ *def* is_coercive



## [2022-01-29 00:33:42](https://github.com/leanprover-community/mathlib/commit/f51d6bf)
chore(ring_theory/polynomial/tower): weaken comm_semiring hypothesis to semiring ([#11712](https://github.com/leanprover-community/mathlib/pull/11712))
…to semiring
#### Estimated changes
Modified src/ring_theory/polynomial/tower.lean




## [2022-01-29 00:04:55](https://github.com/leanprover-community/mathlib/commit/601ea91)
feat(data/nat/mul_ind): generalise rec_on_prime to assume positivity ([#11714](https://github.com/leanprover-community/mathlib/pull/11714))
This makes the multiplicative induction principles slightly stronger, as the coprimality part can assume the given values are positive.
#### Estimated changes
Modified src/data/nat/factorization.lean


Modified src/data/nat/mul_ind.lean




## [2022-01-28 16:51:38](https://github.com/leanprover-community/mathlib/commit/d58ce5a)
feat(number_theory/cyclotomic/zeta): add is_cyclotomic_extension.zeta ([#11695](https://github.com/leanprover-community/mathlib/pull/11695))
We add `is_cyclotomic_extension.zeta n A B`: any primitive `n`-th root of unity in a cyclotomic extension.
From flt-regular.
#### Estimated changes
Modified src/number_theory/cyclotomic/basic.lean


Added src/number_theory/cyclotomic/zeta.lean
- \+ *def* is_cyclotomic_extension.zeta.embeddings_equiv_primitive_roots
- \+ *def* is_cyclotomic_extension.zeta.power_basis
- \+ *lemma* is_cyclotomic_extension.zeta.power_basis_gen_minpoly
- \+ *def* is_cyclotomic_extension.zeta
- \+ *lemma* is_cyclotomic_extension.zeta_minpoly
- \+ *lemma* is_cyclotomic_extension.zeta_primitive_root
- \+ *lemma* is_cyclotomic_extension.zeta_spec'
- \+ *lemma* is_cyclotomic_extension.zeta_spec



## [2022-01-28 16:51:36](https://github.com/leanprover-community/mathlib/commit/02c3146)
feat(analysis/complex): removable singularity theorem ([#11686](https://github.com/leanprover-community/mathlib/pull/11686))
#### Estimated changes
Added src/analysis/complex/removable_singularity.lean
- \+ *lemma* complex.analytic_at_of_differentiable_on_punctured_nhds_of_continuous_at
- \+ *lemma* complex.differentiable_on_compl_singleton_and_continuous_at_iff
- \+ *lemma* complex.differentiable_on_dslope
- \+ *lemma* complex.differentiable_on_update_lim_insert_of_is_o
- \+ *lemma* complex.differentiable_on_update_lim_of_bdd_above
- \+ *lemma* complex.differentiable_on_update_lim_of_is_o
- \+ *lemma* complex.tendsto_lim_of_differentiable_on_punctured_nhds_of_bounded_under
- \+ *lemma* complex.tendsto_lim_of_differentiable_on_punctured_nhds_of_is_o



## [2022-01-28 16:51:34](https://github.com/leanprover-community/mathlib/commit/7e8cb75)
refactor(algebra/linear_ordered_comm_group_with_zero, *): mostly take advantage of the new classes for `linear_ordered_comm_group_with_zero` ([#7645](https://github.com/leanprover-community/mathlib/pull/7645))
This PR continues the refactor of the `ordered` hierarchy, begun in [#7371](https://github.com/leanprover-community/mathlib/pull/7371).
In this iteration, I weakened the assumptions of the lemmas in `ordered_group`.  The bulk of the changes are in the two files
* `algebra/ordered_monoid_lemmas`
* `algebra/ordered_group`
while the remaining files have been edited mostly to accommodate for name/assumption changes.
I have tried to be careful to maintain the **exact** assumptions of each one of the `norm_num` and `linarith` lemmas.  For this reason, some lemmas have a proof that is simply an application of a lemma with weaker assumptions.  The end result is that no lemma whose proof involved a call to `norm_num` or `linarith` broke.
#### Estimated changes
Modified src/algebra/order/monoid.lean
- \+ *lemma* has_mul.to_covariant_class_left
- \+ *lemma* has_mul.to_covariant_class_right

Modified src/algebra/order/with_zero.lean
- \+ *lemma* left.one_le_pow_of_le
- \+ *lemma* left.pow_lt_one_iff
- \+ *lemma* left.pow_lt_one_of_lt
- \+ *lemma* pow_le_pow_of_le
- \+ *lemma* right.one_le_pow_of_le
- \+ *lemma* right.pow_le_one_of_le
- \+ *lemma* right.pow_lt_one_iff
- \+ *lemma* right.pow_lt_one_of_lt

Modified src/data/nat/cast.lean


Modified src/data/real/ereal.lean




## [2022-01-28 15:19:21](https://github.com/leanprover-community/mathlib/commit/dddf6eb)
feat(data/fintype/order): More and better instances ([#11702](https://github.com/leanprover-community/mathlib/pull/11702))
In a fintype, this allows to promote 
* `distrib_lattice` to `complete_distrib_lattice`
* `boolean_algebra` to `complete_boolean_algebra`
Also strengthen
* `fintype.to_order_bot`
* `fintype.to_order_top`
* `fintype.to_bounded_order`
* `complete_linear_order.to_conditionally_complete_linear_order_bot`
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.inf_sup_distrib_left
- \+ *lemma* finset.inf_sup_distrib_right
- \+ *lemma* finset.sup_inf_distrib_left
- \+ *lemma* finset.sup_inf_distrib_right

Modified src/data/fintype/order.lean
- \+/\- *def* fintype.to_bounded_order
- \+/\- *def* fintype.to_order_bot
- \+/\- *def* fintype.to_order_top

Modified src/order/conditionally_complete_lattice.lean




## [2022-01-28 15:19:20](https://github.com/leanprover-community/mathlib/commit/6ca08e8)
feat(algebra/ne_zero): add `coe_trans` instance ([#11700](https://github.com/leanprover-community/mathlib/pull/11700))
This is super-useful for `flt_regular`, meaning we don't have to write all of our lemmata as `ne_zero ((n : ℕ) : R)`.
#### Estimated changes



## [2022-01-28 15:19:19](https://github.com/leanprover-community/mathlib/commit/de27bfc)
feat(algebra/big_operators/{basic,multiset}): two `multiset.prod` lemmas ([#11693](https://github.com/leanprover-community/mathlib/pull/11693))
Two lemmas suggested by Riccardo Brasca on [#11572](https://github.com/leanprover-community/mathlib/pull/11572):
`to_finset_prod_dvd_prod`: `S.to_finset.prod id ∣ S.prod`
`prod_dvd_prod_of_dvd`: For any `S : multiset α`, if `∀ a ∈ S, g1 a ∣ g2 a` then `S.prod g1 ∣ S.prod g2` (a counterpart to `finset.prod_dvd_prod`)
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* multiset.to_finset_prod_dvd_prod

Modified src/algebra/big_operators/multiset.lean
- \+ *lemma* multiset.prod_dvd_prod_of_dvd



## [2022-01-28 15:19:17](https://github.com/leanprover-community/mathlib/commit/c50a60d)
feat(analysis/convex/specific_functions): sin is strictly concave ([#11688](https://github.com/leanprover-community/mathlib/pull/11688))
#### Estimated changes
Modified src/analysis/convex/specific_functions.lean
- \+ *lemma* strict_concave_on_cos_Icc
- \+ *lemma* strict_concave_on_sin_Icc



## [2022-01-28 15:19:16](https://github.com/leanprover-community/mathlib/commit/92c64c4)
feat(group_theory/nilpotent): add upper_central_series_eq_top_iff_nilpotency_class_le ([#11670](https://github.com/leanprover-community/mathlib/pull/11670))
and the analogue for the lower central series.
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* lower_central_series_eq_bot_iff_nilpotency_class_le
- \+ *lemma* upper_central_series_eq_top_iff_nilpotency_class_le



## [2022-01-28 15:19:15](https://github.com/leanprover-community/mathlib/commit/7a485b1)
feat(topology/continuous_function/algebra): `C(α, β)` is a topological group ([#11665](https://github.com/leanprover-community/mathlib/pull/11665))
This PR proves that `C(α, β)` is a topological group. I had to borrow the fix from [#11229](https://github.com/leanprover-community/mathlib/pull/11229) to avoid a diamond.
#### Estimated changes
Modified src/topology/continuous_function/algebra.lean


Modified src/topology/continuous_function/compact.lean
- \+ *lemma* continuous_map.uniform_embedding_equiv_bounded_of_compact
- \+ *lemma* continuous_map.uniform_inducing_equiv_bounded_of_compact



## [2022-01-28 15:19:14](https://github.com/leanprover-community/mathlib/commit/113ab32)
feat(ring_theory/power_series/basic): API about inv ([#11617](https://github.com/leanprover-community/mathlib/pull/11617))
Also rename protected lemmas
`mul_inv`  to `mul_inv_cancel`
`inv_mul` to `inv_mul_cancel`
#### Estimated changes
Modified src/number_theory/bernoulli.lean


Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* mv_power_series.C_inv
- \+ *lemma* mv_power_series.X_inv
- \+ *lemma* mv_power_series.one_inv
- \+ *lemma* mv_power_series.smul_eq_C_mul
- \+ *lemma* mv_power_series.smul_inv
- \+ *lemma* mv_power_series.zero_inv
- \+ *lemma* polynomial.constant_coeff_coe
- \+ *lemma* power_series.C_inv
- \+ *lemma* power_series.X_inv
- \+ *lemma* power_series.one_inv
- \+ *lemma* power_series.smul_eq_C_mul
- \+ *lemma* power_series.smul_inv
- \+ *lemma* power_series.zero_inv



## [2022-01-28 15:19:13](https://github.com/leanprover-community/mathlib/commit/36dd6a6)
feat(algebra/squarefree): squarefree iff no square irreducible divisors ([#11544](https://github.com/leanprover-community/mathlib/pull/11544))
#### Estimated changes
Modified src/algebra/squarefree.lean
- \+ *lemma* irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree
- \+ *lemma* nat.squarefree_iff_prime_sq_not_dvd
- \+ *lemma* squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible
- \+ *lemma* squarefree_iff_irreducible_sq_not_dvd_of_ne_zero



## [2022-01-28 15:19:11](https://github.com/leanprover-community/mathlib/commit/fb9c5d3)
feat(cyclotomic/basic): diverse roots of unity lemmas ([#11473](https://github.com/leanprover-community/mathlib/pull/11473))
From flt-regular.
#### Estimated changes
Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* polynomial.cyclotomic.roots_eq_primitive_roots_val
- \+ *lemma* polynomial.cyclotomic.roots_to_finset_eq_primitive_roots
- \+/\- *lemma* polynomial.is_root_cyclotomic
- \+/\- *lemma* polynomial.is_root_cyclotomic_iff
- \+ *lemma* polynomial.is_root_of_unity_of_root_cyclotomic
- \+ *lemma* polynomial.roots_cyclotomic_nodup



## [2022-01-28 15:19:10](https://github.com/leanprover-community/mathlib/commit/91a1afb)
feat(algebraic_geometry): The function field is the fraction field of stalks ([#11129](https://github.com/leanprover-community/mathlib/pull/11129))
#### Estimated changes
Modified src/algebraic_geometry/function_field.lean
- \+ *lemma* algebraic_geometry.function_field_is_fraction_ring_of_is_affine_open
- \+ *lemma* algebraic_geometry.generic_point_eq_bot_of_affine
- \+ *lemma* algebraic_geometry.generic_point_eq_of_is_open_immersion
- \+ *lemma* algebraic_geometry.is_affine_open.prime_ideal_of_generic_point



## [2022-01-28 15:19:08](https://github.com/leanprover-community/mathlib/commit/0b6330d)
feat(data/finsupp/interval): Finitely supported functions to a locally finite order are locally finite ([#10930](https://github.com/leanprover-community/mathlib/pull/10930))
... when the codomain itself is locally finite.
This allows getting rid of `finsupp.Iic_finset`.
#### Estimated changes
Modified src/data/finsupp/antidiagonal.lean
- \- *def* finsupp.Iic_finset
- \- *lemma* finsupp.coe_Iic_finset
- \- *lemma* finsupp.finite_le_nat
- \- *lemma* finsupp.finite_lt_nat
- \- *lemma* finsupp.mem_Iic_finset

Added src/data/finsupp/interval.lean
- \+ *lemma* finsupp.card_Icc
- \+ *lemma* finsupp.card_Ico
- \+ *lemma* finsupp.card_Ioc
- \+ *lemma* finsupp.card_Ioo
- \+ *lemma* finsupp.mem_range_Icc_apply_iff
- \+ *lemma* finsupp.mem_range_singleton_apply_iff
- \+ *def* finsupp.range_Icc
- \+ *def* finsupp.range_singleton

Modified src/ring_theory/power_series/basic.lean




## [2022-01-28 13:31:09](https://github.com/leanprover-community/mathlib/commit/445be96)
fix(tactic/squeeze): `squeeze_simp` providing invalid suggestions ([#11696](https://github.com/leanprover-community/mathlib/pull/11696))
`squeeze_simp` was previously permuting the lemmas passed to `simp`, which caused failures in cases where the lemma order mattered. The fix is to ensure that `squeeze_simp` does not change the order of passed lemmas.
Closes [#3097](https://github.com/leanprover-community/mathlib/pull/3097)
#### Estimated changes
Modified src/meta/expr.lean


Modified src/tactic/squeeze.lean


Modified test/squeeze.lean
- \+ *def* a
- \+ *def* b
- \+ *def* c
- \+ *def* f
- \+ *lemma* k
- \+ *lemma* l



## [2022-01-28 13:31:08](https://github.com/leanprover-community/mathlib/commit/3837abc)
feat(data/list/*): subperm_singleton_iff ([#11680](https://github.com/leanprover-community/mathlib/pull/11680))
#### Estimated changes
Modified src/data/list/count.lean
- \+/\- *lemma* list.count_pos
- \+ *lemma* list.one_le_count_iff_mem

Modified src/data/list/perm.lean
- \+ *lemma* list.subperm_singleton_iff



## [2022-01-28 13:31:06](https://github.com/leanprover-community/mathlib/commit/1e44add)
feat(order/filter/countable_Inter): review ([#11673](https://github.com/leanprover-community/mathlib/pull/11673))
- drop `_sets` in more names;
- add `filter.of_countable_Inter` and instances for
  `filter.map`/`filter.comap`;
- add docs.
#### Estimated changes
Modified src/order/filter/countable_Inter.lean
- \+ *lemma* countable_Inter_mem
- \- *lemma* countable_Inter_mem_sets
- \+ *lemma* countable_sInter_mem
- \- *lemma* countable_sInter_mem_sets
- \+ *lemma* filter.mem_of_countable_Inter
- \+ *def* filter.of_countable_Inter



## [2022-01-28 13:31:05](https://github.com/leanprover-community/mathlib/commit/680733c)
feat(order/hom/basic): `compl` as a dual order isomorphism ([#11630](https://github.com/leanprover-community/mathlib/pull/11630))
#### Estimated changes
Modified src/order/hom/basic.lean
- \+ *theorem* compl_antitone
- \+ *theorem* compl_strict_anti
- \+ *def* order_iso.compl



## [2022-01-28 13:31:04](https://github.com/leanprover-community/mathlib/commit/ff241e1)
feat(order/max): Predicate for minimal/maximal elements, typeclass for orders without bottoms ([#11618](https://github.com/leanprover-community/mathlib/pull/11618))
This defines
* `is_min`: Predicate for a minimal element
* `is_max`: Predicate for a maximal element
* `no_bot_order`: Predicate for an order without bottoms
* `no_top_order`: Predicate for an order without tops
#### Estimated changes
Modified src/order/directed.lean
- \+ *lemma* is_bot_iff_is_min
- \+ *lemma* is_top_iff_is_max

Modified src/order/max.lean
- \+ *lemma* is_bot.mono
- \- *lemma* is_bot.to_dual
- \+ *lemma* is_bot_of_dual_iff
- \+ *lemma* is_bot_to_dual_iff
- \+ *lemma* is_max.mono
- \+ *lemma* is_max.not_lt
- \+ *def* is_max
- \+ *lemma* is_max_iff_forall_not_lt
- \+ *lemma* is_max_of_dual_iff
- \+ *lemma* is_max_to_dual_iff
- \+ *lemma* is_min.mono
- \+ *lemma* is_min.not_lt
- \+ *def* is_min
- \+ *lemma* is_min_iff_forall_not_lt
- \+ *lemma* is_min_of_dual_iff
- \+ *lemma* is_min_to_dual_iff
- \+ *lemma* is_top.mono
- \- *lemma* is_top.to_dual
- \+/\- *lemma* is_top.unique
- \+ *lemma* is_top_of_dual_iff
- \+ *lemma* is_top_to_dual_iff
- \+/\- *lemma* not_is_bot
- \+ *lemma* not_is_max
- \+ *lemma* not_is_max_iff
- \+ *lemma* not_is_min
- \+ *lemma* not_is_min_iff
- \+/\- *lemma* not_is_top

Modified src/order/order_dual.lean




## [2022-01-28 13:31:02](https://github.com/leanprover-community/mathlib/commit/2fa5977)
feat(category_theory/bicategory/natural_transformation): define oplax natural transformations ([#11404](https://github.com/leanprover-community/mathlib/pull/11404))
This PR define oplax natural transformations between oplax functors.
We give a composition and a category structure on oplax natural transformations.
#### Estimated changes
Added src/category_theory/bicategory/natural_transformation.lean
- \+ *def* category_theory.oplax_nat_trans.id
- \+ *def* category_theory.oplax_nat_trans.modification.id
- \+ *def* category_theory.oplax_nat_trans.modification.vcomp
- \+ *lemma* category_theory.oplax_nat_trans.modification.whisker_left_naturality
- \+ *lemma* category_theory.oplax_nat_trans.modification.whisker_right_naturality
- \+ *structure* category_theory.oplax_nat_trans.modification
- \+ *def* category_theory.oplax_nat_trans.modification_iso.of_components
- \+ *def* category_theory.oplax_nat_trans.vcomp
- \+ *lemma* category_theory.oplax_nat_trans.whisker_left_naturality_comp
- \+ *lemma* category_theory.oplax_nat_trans.whisker_left_naturality_id
- \+ *lemma* category_theory.oplax_nat_trans.whisker_left_naturality_naturality
- \+ *lemma* category_theory.oplax_nat_trans.whisker_right_naturality_comp
- \+ *lemma* category_theory.oplax_nat_trans.whisker_right_naturality_id
- \+ *lemma* category_theory.oplax_nat_trans.whisker_right_naturality_naturality
- \+ *structure* category_theory.oplax_nat_trans



## [2022-01-28 13:31:00](https://github.com/leanprover-community/mathlib/commit/b9db169)
chore(order/locally_finite): fill in finset interval API ([#11338](https://github.com/leanprover-community/mathlib/pull/11338))
A bunch of statements about finset intervals, mimicking the set interval API and mostly proved using it. `simp` attributes are  chosen as they were for sets. Also some golf.
#### Estimated changes
Modified src/data/finset/locally_finite.lean
- \+ *lemma* finset.Icc_diff_Ico_self
- \+ *lemma* finset.Icc_diff_Ioc_self
- \+ *lemma* finset.Icc_diff_Ioo_self
- \+ *lemma* finset.Icc_diff_both
- \+ *lemma* finset.Icc_eq_cons_Ico
- \+ *lemma* finset.Icc_eq_cons_Ioc
- \+/\- *lemma* finset.Icc_erase_left
- \+/\- *lemma* finset.Icc_erase_right
- \+ *lemma* finset.Icc_ssubset_Icc_left
- \+ *lemma* finset.Icc_ssubset_Icc_right
- \+ *lemma* finset.Icc_subset_Icc
- \+ *lemma* finset.Icc_subset_Icc_iff
- \+ *lemma* finset.Icc_subset_Icc_left
- \+ *lemma* finset.Icc_subset_Icc_right
- \+ *lemma* finset.Icc_subset_Ici_self
- \+ *lemma* finset.Icc_subset_Ico_iff
- \+ *lemma* finset.Icc_subset_Ico_right
- \+ *lemma* finset.Icc_subset_Iic_self
- \+ *lemma* finset.Icc_subset_Ioc_iff
- \+ *lemma* finset.Icc_subset_Ioo_iff
- \+ *lemma* finset.Ici_eq_cons_Ioi
- \+ *lemma* finset.Ici_erase
- \+ *lemma* finset.Ico_diff_Ioo_self
- \+ *lemma* finset.Ico_erase_left
- \+/\- *lemma* finset.Ico_filter_le_of_right_le
- \+/\- *lemma* finset.Ico_filter_lt_of_le_left
- \+/\- *lemma* finset.Ico_filter_lt_of_le_right
- \+/\- *lemma* finset.Ico_filter_lt_of_right_le
- \+/\- *lemma* finset.Ico_insert_right
- \+/\- *lemma* finset.Ico_self
- \+ *lemma* finset.Ico_subset_Icc_self
- \+ *lemma* finset.Ico_subset_Ici_self
- \+ *lemma* finset.Ico_subset_Ico
- \+ *lemma* finset.Ico_subset_Ico_left
- \+ *lemma* finset.Ico_subset_Ico_right
- \+ *lemma* finset.Ico_subset_Iic_self
- \+ *lemma* finset.Ico_subset_Iio_self
- \+ *lemma* finset.Ico_subset_Ioo_left
- \+ *lemma* finset.Iic_eq_cons_Iio
- \+ *lemma* finset.Iic_erase
- \+ *lemma* finset.Iio_insert
- \+ *lemma* finset.Iio_subset_Iic_self
- \+ *lemma* finset.Ioc_diff_Ioo_self
- \+ *lemma* finset.Ioc_erase_right
- \+ *lemma* finset.Ioc_insert_left
- \+/\- *lemma* finset.Ioc_self
- \+ *lemma* finset.Ioc_subset_Icc_self
- \+ *lemma* finset.Ioc_subset_Ici_self
- \+ *lemma* finset.Ioc_subset_Iic_self
- \+ *lemma* finset.Ioc_subset_Ioc
- \+ *lemma* finset.Ioc_subset_Ioc_left
- \+ *lemma* finset.Ioc_subset_Ioc_right
- \+ *lemma* finset.Ioc_subset_Ioi_self
- \+ *lemma* finset.Ioc_subset_Ioo_right
- \+ *lemma* finset.Ioi_insert
- \+ *lemma* finset.Ioi_subset_Ici_self
- \+/\- *lemma* finset.Ioo_insert_left
- \+ *lemma* finset.Ioo_insert_right
- \+/\- *lemma* finset.Ioo_self
- \+ *lemma* finset.Ioo_subset_Icc_self
- \+ *lemma* finset.Ioo_subset_Ici_self
- \+ *lemma* finset.Ioo_subset_Ico_self
- \+ *lemma* finset.Ioo_subset_Iic_self
- \+ *lemma* finset.Ioo_subset_Iio_self
- \+ *lemma* finset.Ioo_subset_Ioc_self
- \+ *lemma* finset.Ioo_subset_Ioi_self
- \+ *lemma* finset.Ioo_subset_Ioo
- \+ *lemma* finset.Ioo_subset_Ioo_left
- \+ *lemma* finset.Ioo_subset_Ioo_right
- \+ *lemma* finset.card_Ioo_eq_card_Ioc_sub_one
- \+/\- *lemma* finset.filter_ge_eq_Iic
- \+/\- *lemma* finset.filter_gt_eq_Iio
- \+/\- *lemma* finset.filter_le_eq_Ici
- \+/\- *lemma* finset.filter_le_le_eq_Icc
- \+/\- *lemma* finset.filter_le_lt_eq_Ico
- \+/\- *lemma* finset.filter_lt_eq_Ioi
- \+/\- *lemma* finset.filter_lt_le_eq_Ioc
- \+/\- *lemma* finset.filter_lt_lt_eq_Ioo
- \+/\- *lemma* finset.image_add_right_Icc
- \+/\- *lemma* finset.image_add_right_Ico
- \+/\- *lemma* finset.image_add_right_Ioc
- \+/\- *lemma* finset.image_add_right_Ioo
- \+/\- *lemma* finset.left_mem_Icc
- \+/\- *lemma* finset.left_mem_Ico
- \+/\- *lemma* finset.right_mem_Icc
- \+/\- *lemma* finset.right_mem_Ioc
- \+/\- *def* set.fintype_of_mem_bounds

Modified src/order/locally_finite.lean
- \- *theorem* finset.Ico_subset_Ico
- \+/\- *lemma* finset.coe_Icc
- \+/\- *lemma* finset.coe_Ico
- \+/\- *lemma* finset.coe_Ioc
- \+/\- *lemma* finset.coe_Ioo
- \+/\- *lemma* finset.mem_Icc
- \+/\- *lemma* finset.mem_Ici
- \+/\- *lemma* finset.mem_Ico
- \+/\- *lemma* finset.mem_Iic
- \+/\- *lemma* finset.mem_Iio
- \+/\- *lemma* finset.mem_Ioc
- \+/\- *lemma* finset.mem_Ioi
- \+/\- *lemma* finset.mem_Ioo



## [2022-01-28 13:03:39](https://github.com/leanprover-community/mathlib/commit/924aab1)
feat(ring_theory/polynomial/eisenstein): add miscellaneous results about Eisenstein polynomials ([#11697](https://github.com/leanprover-community/mathlib/pull/11697))
Miscellaneous results about Eisenstein polynomials
From flt-regular.
#### Estimated changes
Added src/ring_theory/polynomial/eisenstein.lean
- \+ *lemma* polynomial.is_eisenstein_at.coeff_mem
- \+ *lemma* polynomial.is_eisenstein_at.irreducible
- \+ *lemma* polynomial.is_eisenstein_at.is_weakly_eisenstein_at
- \+ *structure* polynomial.is_eisenstein_at
- \+ *lemma* polynomial.is_weakly_eisenstein_at.exists_mem_adjoin_mul_eq_pow_nat_degree
- \+ *lemma* polynomial.is_weakly_eisenstein_at.exists_mem_adjoin_mul_eq_pow_nat_degree_le
- \+ *lemma* polynomial.is_weakly_eisenstein_at.map
- \+ *lemma* polynomial.is_weakly_eisenstein_at.pow_nat_degree_le_of_aeval_zero_of_monic_mem_map
- \+ *lemma* polynomial.is_weakly_eisenstein_at.pow_nat_degree_le_of_root_of_monic_mem
- \+ *structure* polynomial.is_weakly_eisenstein_at



## [2022-01-28 11:11:22](https://github.com/leanprover-community/mathlib/commit/e290b29)
feat(data/quot): add subsingleton instances ([#11668](https://github.com/leanprover-community/mathlib/pull/11668))
#### Estimated changes
Modified src/data/quot.lean




## [2022-01-28 08:38:09](https://github.com/leanprover-community/mathlib/commit/bf347f9)
feat(algebraic_geometry): Fiber products of schemes ([#10605](https://github.com/leanprover-community/mathlib/pull/10605))
#### Estimated changes
Modified src/algebraic_geometry/gluing.lean
- \+ *lemma* algebraic_geometry.Scheme.open_cover.hom_ext

Modified src/algebraic_geometry/pullbacks.lean
- \+ *lemma* algebraic_geometry.Scheme.pullback.affine_affine_has_pullback
- \+ *def* algebraic_geometry.Scheme.pullback.glued_is_limit
- \+ *lemma* algebraic_geometry.Scheme.pullback.has_pullback_of_cover
- \+ *lemma* algebraic_geometry.Scheme.pullback.lift_comp_ι
- \+ *def* algebraic_geometry.Scheme.pullback.pullback_fst_ι_to_V
- \+ *lemma* algebraic_geometry.Scheme.pullback.pullback_fst_ι_to_V_fst
- \+ *lemma* algebraic_geometry.Scheme.pullback.pullback_fst_ι_to_V_snd
- \+ *def* algebraic_geometry.Scheme.pullback.pullback_p1_iso
- \+ *lemma* algebraic_geometry.Scheme.pullback.pullback_p1_iso_hom_fst
- \+ *lemma* algebraic_geometry.Scheme.pullback.pullback_p1_iso_hom_snd
- \+ *lemma* algebraic_geometry.Scheme.pullback.pullback_p1_iso_hom_ι
- \+ *lemma* algebraic_geometry.Scheme.pullback.pullback_p1_iso_inv_fst
- \+ *lemma* algebraic_geometry.Scheme.pullback.pullback_p1_iso_inv_snd



## [2022-01-28 07:26:07](https://github.com/leanprover-community/mathlib/commit/67dcdef)
feat(data/mv_polynomial/derivation): derivations of `mv_polynomial`s ([#9145](https://github.com/leanprover-community/mathlib/pull/9145))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean


Added src/data/mv_polynomial/derivation.lean
- \+ *lemma* mv_polynomial.derivation_C
- \+ *lemma* mv_polynomial.derivation_C_mul
- \+ *lemma* mv_polynomial.derivation_eq_of_forall_mem_vars
- \+ *lemma* mv_polynomial.derivation_eq_on_supported
- \+ *lemma* mv_polynomial.derivation_eq_zero_of_forall_mem_vars
- \+ *lemma* mv_polynomial.derivation_ext
- \+ *lemma* mv_polynomial.leibniz_iff_X
- \+ *def* mv_polynomial.mk_derivation
- \+ *lemma* mv_polynomial.mk_derivation_X
- \+ *def* mv_polynomial.mk_derivation_equiv
- \+ *lemma* mv_polynomial.mk_derivation_monomial
- \+ *def* mv_polynomial.mk_derivationₗ
- \+ *lemma* mv_polynomial.mk_derivationₗ_C
- \+ *lemma* mv_polynomial.mk_derivationₗ_X
- \+ *lemma* mv_polynomial.mk_derivationₗ_monomial

Modified src/data/mv_polynomial/pderiv.lean
- \+/\- *def* mv_polynomial.pderiv
- \+/\- *lemma* mv_polynomial.pderiv_C
- \+/\- *lemma* mv_polynomial.pderiv_C_mul
- \+/\- *lemma* mv_polynomial.pderiv_X
- \+ *lemma* mv_polynomial.pderiv_X_of_ne
- \+/\- *lemma* mv_polynomial.pderiv_X_self
- \+/\- *lemma* mv_polynomial.pderiv_monomial
- \- *lemma* mv_polynomial.pderiv_monomial_mul
- \- *lemma* mv_polynomial.pderiv_nat_cast
- \- *lemma* mv_polynomial.pderiv_pow

Modified src/ring_theory/derivation.lean
- \+ *lemma* derivation.map_sum

Modified src/ring_theory/polynomial/bernstein.lean




## [2022-01-28 06:58:36](https://github.com/leanprover-community/mathlib/commit/6687cf1)
feat(group_theory/sylow): `fintype (sylow p H)` from `fintype (sylow p G)` ([#11664](https://github.com/leanprover-community/mathlib/pull/11664))
If the number of Sylow `p`-subgroups of `G` is finite, then the number of Sylow `p`-subgroups of `H` is finite.
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+ *lemma* is_p_group.ker_is_p_group_of_injective

Modified src/group_theory/sylow.lean
- \+ *lemma* sylow.exists_comap_eq_of_injective
- \+ *lemma* sylow.exists_comap_eq_of_ker_is_p_group
- \+ *lemma* sylow.exists_comap_subtype_eq



## [2022-01-28 03:07:32](https://github.com/leanprover-community/mathlib/commit/f5d63f9)
feat(topology/category/Compactum): forget creates limits ([#11690](https://github.com/leanprover-community/mathlib/pull/11690))
Will likely be used in LTE.
#### Estimated changes
Modified src/topology/category/Compactum.lean
- \+ *def* Compactum_to_CompHaus_comp_forget



## [2022-01-28 00:40:24](https://github.com/leanprover-community/mathlib/commit/24cfb88)
chore(set_theory/ordinal_arithmetic): Golf some instances of `lt_irrefl _ h` down to `h.false` ([#11699](https://github.com/leanprover-community/mathlib/pull/11699))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean




## [2022-01-28 00:40:23](https://github.com/leanprover-community/mathlib/commit/bac0f55)
chore(order/conditionally_complete_lattice): move code to a new file ([#11698](https://github.com/leanprover-community/mathlib/pull/11698))
This is the first step towards adding a `complete_lattice` instance for `Icc`/`interval`.
#### Estimated changes
Modified src/algebra/order/nonneg.lean


Added src/order/complete_lattice_intervals.lean
- \+ *lemma* Inf_within_of_ord_connected
- \+ *lemma* Sup_within_of_ord_connected
- \+ *lemma* subset_Inf_def
- \+ *lemma* subset_Inf_of_within
- \+ *lemma* subset_Sup_def
- \+ *lemma* subset_Sup_of_within

Modified src/order/conditionally_complete_lattice.lean
- \- *lemma* Inf_within_of_ord_connected
- \- *lemma* Sup_within_of_ord_connected
- \- *lemma* subset_Inf_def
- \- *lemma* subset_Inf_of_within
- \- *lemma* subset_Sup_def
- \- *lemma* subset_Sup_of_within

Modified src/topology/algebra/ordered/intermediate_value.lean




## [2022-01-27 23:05:41](https://github.com/leanprover-community/mathlib/commit/21cea47)
feat(analysis/special_functions/log): log of natural power ([#11685](https://github.com/leanprover-community/mathlib/pull/11685))
The rpow versions are already present, but the natural/integer versions can also be very helpful (eg for squares).
#### Estimated changes
Modified src/analysis/special_functions/log.lean
- \+ *lemma* real.log_pow
- \+ *lemma* real.log_zpow



## [2022-01-27 23:05:40](https://github.com/leanprover-community/mathlib/commit/79e6cb0)
feat(order/succ_pred/relation): `succ`/`pred` inductions on relations ([#11518](https://github.com/leanprover-community/mathlib/pull/11518))
* Rename file `order.succ_pred` -> `order.succ_pred.basic`
* Generalize induction principles `succ.rec` and `pred.rec`, make the argument order more "induction-like" and add the attribute `@[elab_as_eliminator]`
* Proof properties about `refl_trans_gen` and `trans_gen` in a `is_succ_archimedean` order.
* Proof some monotonicity properties of closure operations.
#### Estimated changes
Modified src/data/int/succ_pred.lean


Modified src/data/nat/succ_pred.lean


Modified src/logic/relation.lean
- \+ *lemma* relation.refl_gen.mono
- \+/\- *lemma* relation.refl_gen.to_refl_trans_gen
- \+ *lemma* relation.refl_trans_gen.swap
- \+ *lemma* relation.refl_trans_gen_swap
- \+ *lemma* relation.trans_gen.mono
- \+ *lemma* relation.trans_gen.swap
- \+ *lemma* relation.trans_gen_swap

Renamed src/order/succ_pred.lean to src/order/succ_pred/basic.lean
- \+/\- *lemma* pred.rec
- \+/\- *lemma* succ.rec

Added src/order/succ_pred/relation.lean
- \+ *lemma* refl_trans_gen_of_pred
- \+ *lemma* refl_trans_gen_of_pred_of_ge
- \+ *lemma* refl_trans_gen_of_pred_of_le
- \+ *lemma* refl_trans_gen_of_succ
- \+ *lemma* refl_trans_gen_of_succ_of_ge
- \+ *lemma* refl_trans_gen_of_succ_of_le
- \+ *lemma* trans_gen_of_pred_of_gt
- \+ *lemma* trans_gen_of_pred_of_lt
- \+ *lemma* trans_gen_of_pred_of_ne
- \+ *lemma* trans_gen_of_pred_of_reflexive
- \+ *lemma* trans_gen_of_succ_of_gt
- \+ *lemma* trans_gen_of_succ_of_lt
- \+ *lemma* trans_gen_of_succ_of_ne
- \+ *lemma* trans_gen_of_succ_of_reflexive

Modified src/set_theory/ordinal.lean




## [2022-01-27 23:05:38](https://github.com/leanprover-community/mathlib/commit/0a721cc)
feat(data/nat): a predicate for prime powers ([#11313](https://github.com/leanprover-community/mathlib/pull/11313))
Adds a predicate for prime powers, in preparation for defining the von Mangoldt function.
cc @stuart-presnell since you might be needing this material soon, and @jcommelin if you have thoughts about generalising this to rings/UFDs?
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* associated.of_pow_associated_of_prime'
- \+ *lemma* associated.of_pow_associated_of_prime

Added src/algebra/is_prime_pow.lean
- \+ *lemma* eq_of_prime_pow_eq'
- \+ *lemma* eq_of_prime_pow_eq
- \+ *lemma* is_prime_pow.dvd
- \+ *lemma* is_prime_pow.min_fac_pow_factorization_eq
- \+ *lemma* is_prime_pow.ne_one
- \+ *theorem* is_prime_pow.ne_zero
- \+ *theorem* is_prime_pow.one_lt
- \+ *theorem* is_prime_pow.pos
- \+ *lemma* is_prime_pow.pow
- \+ *lemma* is_prime_pow.two_le
- \+ *def* is_prime_pow
- \+ *lemma* is_prime_pow_def
- \+ *lemma* is_prime_pow_iff_min_fac_pow_factorization_eq
- \+ *lemma* is_prime_pow_iff_pow_succ
- \+ *lemma* is_prime_pow_iff_unique_prime_dvd
- \+ *lemma* is_prime_pow_nat_iff
- \+ *lemma* is_prime_pow_nat_iff_bounded
- \+ *lemma* is_prime_pow_of_min_fac_pow_factorization_eq
- \+ *lemma* not_is_prime_pow_one
- \+ *lemma* not_is_prime_pow_zero
- \+ *lemma* prime.is_prime_pow

Modified src/algebra/ne_zero.lean


Modified src/number_theory/cyclotomic/basic.lean




## [2022-01-27 22:03:42](https://github.com/leanprover-community/mathlib/commit/7458476)
chore(set_theory/ordinal_arithmetic): golf proof into term mode ([#11691](https://github.com/leanprover-community/mathlib/pull/11691))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean




## [2022-01-27 20:16:32](https://github.com/leanprover-community/mathlib/commit/02c08d9)
doc(polynomial/eval): why map_ring_hom can't replace map ([#11537](https://github.com/leanprover-community/mathlib/pull/11537))
#### Estimated changes
Modified src/data/polynomial/eval.lean




## [2022-01-27 10:01:14](https://github.com/leanprover-community/mathlib/commit/05e1845)
feat(archive/100-theorems-list): add proof of the solution of the cubic ([#11635](https://github.com/leanprover-community/mathlib/pull/11635))
Gives solution to the cubic equation, based on the cardano's formula. The base field should have cube root of unity and characteristic neither 2 nor 3.
#### Estimated changes
Added archive/100-theorems-list/37_solution_of_cubic.lean
- \+ *lemma* cube_root_of_unity_sum
- \+ *lemma* cubic_basic_eq_zero_iff
- \+ *theorem* cubic_eq_zero_iff
- \+ *lemma* cubic_eq_zero_iff_of_p_eq_zero
- \+ *lemma* cubic_monic_eq_zero_iff

Modified docs/100.yaml




## [2022-01-27 05:30:47](https://github.com/leanprover-community/mathlib/commit/0844597)
feat(set_theory/ordinal_arithmetic): Update header ([#11681](https://github.com/leanprover-community/mathlib/pull/11681))
Added definitions from my previous PRs, and made myself an author.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean




## [2022-01-27 01:40:11](https://github.com/leanprover-community/mathlib/commit/a6ace8c)
feat(set_theory/ordinal_arithmetic): Proved `sup_eq_lsub_iff_lt_sup` ([#11660](https://github.com/leanprover-community/mathlib/pull/11660))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* ordinal.bsup_eq_blsub
- \+ *theorem* ordinal.bsup_eq_blsub_iff_lt_bsup
- \+ *theorem* ordinal.bsup_eq_blsub_iff_succ
- \- *theorem* ordinal.sup_eq_lsub
- \+ *theorem* ordinal.sup_eq_lsub_iff_lt_sup
- \+ *theorem* ordinal.sup_eq_lsub_iff_succ



## [2022-01-26 23:35:18](https://github.com/leanprover-community/mathlib/commit/92ee748)
chore(analysis/complex/cauchy_integral): use `dslope` to golf a proof ([#11675](https://github.com/leanprover-community/mathlib/pull/11675))
#### Estimated changes
Modified src/analysis/complex/cauchy_integral.lean




## [2022-01-26 23:35:16](https://github.com/leanprover-community/mathlib/commit/a1e1ffd)
feat(order/filter): +1 version of `mem_inf_principal` ([#11674](https://github.com/leanprover-community/mathlib/pull/11674))
#### Estimated changes
Modified src/order/bounded_order.lean
- \+ *lemma* disjoint_assoc

Modified src/order/filter/basic.lean
- \+ *theorem* filter.mem_inf_principal'



## [2022-01-26 23:35:15](https://github.com/leanprover-community/mathlib/commit/52e9fd5)
chore(*): don't use tactic internal lemmas in proofs ([#11641](https://github.com/leanprover-community/mathlib/pull/11641))
Some lemmas that are intended as internals to a tactic get picked up by library search and end up in proofs.
We replace a few of these tactic lemma uses with actual library lemmas which should be more maintainable, de-coupling tactic internals from the actual library.
#### Estimated changes
Modified src/analysis/mean_inequalities.lean


Modified src/analysis/special_functions/trigonometric/basic.lean


Modified src/data/nat/totient.lean


Modified src/data/real/pi/leibniz.lean


Modified src/data/set/lattice.lean


Modified src/field_theory/splitting_field.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/integral/set_to_l1.lean


Modified test/induction.lean




## [2022-01-26 22:45:31](https://github.com/leanprover-community/mathlib/commit/577e3a2)
chore(topology/algebra/uniform_group): Remove newline after docstring ([#11671](https://github.com/leanprover-community/mathlib/pull/11671))
Yael pointed out that [#11662](https://github.com/leanprover-community/mathlib/pull/11662) added an erroneous newline after a docstring. This PR removes that newline.
#### Estimated changes
Modified src/topology/algebra/uniform_group.lean




## [2022-01-26 20:52:57](https://github.com/leanprover-community/mathlib/commit/946454a)
feat(data/nat/factorization): various theorems on factorization and division ([#11663](https://github.com/leanprover-community/mathlib/pull/11663))
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+ *lemma* nat.div_factorization_eq_tsub_of_dvd
- \+ *lemma* nat.dvd_iff_div_factorization_eq_tsub
- \+ *lemma* nat.dvd_iff_prime_pow_dvd_dvd
- \+ *lemma* nat.exists_factorization_lt_of_lt
- \+ *lemma* nat.factorization_eq_zero_of_non_prime
- \+ *lemma* nat.pow_factorization_dvd
- \+ *lemma* nat.prime_pow_dvd_iff_le_factorization



## [2022-01-26 20:14:54](https://github.com/leanprover-community/mathlib/commit/97e01cd)
feat(group_theory/free_abelian_group_finsupp): various equiv.of_free_*_group lemmas ([#11469](https://github.com/leanprover-community/mathlib/pull/11469))
Namely `equiv.of_free_abelian_group_linear_equiv`,
`equiv.of_free_abelian_group_equiv` and `equiv.of_free_group_equiv`
#### Estimated changes
Modified src/group_theory/free_abelian_group_finsupp.lean
- \+ *def* free_abelian_group.equiv.of_free_abelian_group_equiv
- \+ *def* free_abelian_group.equiv.of_free_abelian_group_linear_equiv
- \+ *def* free_abelian_group.equiv.of_free_group_equiv
- \+ *def* free_abelian_group.equiv.of_is_free_group_equiv

Modified src/group_theory/free_group.lean




## [2022-01-26 17:10:48](https://github.com/leanprover-community/mathlib/commit/8fbc009)
feat(data/{dfinsupp,finsupp}/basic): `fun_like` instances for `Π₀ i, α i` and `ι →₀ α` ([#11667](https://github.com/leanprover-community/mathlib/pull/11667))
This provides the `fun_like` instances for `finsupp` and `dfinsupp` and deprecates the lemmas that are now provided by the `fun_like` API.
#### Estimated changes
Modified src/data/dfinsupp/basic.lean
- \+/\- *lemma* dfinsupp.coe_fn_injective
- \+/\- *lemma* dfinsupp.ext
- \+/\- *lemma* dfinsupp.ext_iff

Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.coe_fn_inj
- \+/\- *lemma* finsupp.coe_fn_injective
- \+/\- *lemma* finsupp.congr_fun
- \+/\- *lemma* finsupp.ext
- \+/\- *lemma* finsupp.ext_iff



## [2022-01-26 17:10:46](https://github.com/leanprover-community/mathlib/commit/c447a31)
feat(algebraic_geometry): Stalk is localization of affine open.  ([#11640](https://github.com/leanprover-community/mathlib/pull/11640))
#### Estimated changes
Modified src/algebra/category/CommRing/basic.lean
- \+ *lemma* category_theory.iso.CommRing_iso_to_ring_equiv_symm_to_ring_hom
- \+ *lemma* category_theory.iso.CommRing_iso_to_ring_equiv_to_ring_hom

Modified src/algebraic_geometry/AffineScheme.lean
- \+ *lemma* algebraic_geometry.is_affine_open.from_Spec_prime_ideal_of
- \+ *lemma* algebraic_geometry.is_affine_open.is_localization_stalk
- \+ *lemma* algebraic_geometry.is_affine_open.is_localization_stalk_aux
- \+ *def* algebraic_geometry.is_affine_open.prime_ideal_of

Modified src/algebraic_geometry/Scheme.lean
- \+ *lemma* algebraic_geometry.Scheme.app_eq
- \+ *lemma* algebraic_geometry.Scheme.id_app
- \+ *lemma* algebraic_geometry.Scheme.id_coe_base
- \+ *lemma* algebraic_geometry.Scheme.id_val_base
- \+ *lemma* algebraic_geometry.Scheme.inv_val_c_app

Modified src/algebraic_geometry/Spec.lean


Modified src/algebraic_geometry/properties.lean
- \+ *lemma* algebraic_geometry.is_integral_of_is_affine_is_domain
- \+ *lemma* algebraic_geometry.is_reduced_of_is_affine_is_reduced
- \+ *lemma* algebraic_geometry.reduce_to_affine_nbhd

Modified src/ring_theory/localization.lean
- \+ *lemma* is_fraction_ring.is_fraction_ring_of_is_domain_of_is_localization
- \+ *lemma* is_fraction_ring.is_fraction_ring_of_is_localization
- \+ *lemma* is_fraction_ring.nontrivial
- \+ *lemma* is_localization.map_non_zero_divisors_le
- \+ *lemma* is_localization.mk'_eq_zero_iff
- \+ *lemma* is_localization.non_zero_divisors_le_comap

Modified src/topology/category/Top/opens.lean
- \+ *lemma* topological_space.opens.adjunction_counit_app_self

Modified src/topology/sheaves/stalks.lean
- \+ *lemma* Top.presheaf.stalk_open_algebra_map



## [2022-01-26 15:22:43](https://github.com/leanprover-community/mathlib/commit/b8fcac5)
feat(data/nat/basic): three small `dvd_iff...` lemmas ([#11669](https://github.com/leanprover-community/mathlib/pull/11669))
Three biconditionals for proving `d ∣ n`
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.dvd_iff_div_mul_eq
- \+ *lemma* nat.dvd_iff_dvd_dvd
- \+ *lemma* nat.dvd_iff_le_div_mul



## [2022-01-26 13:30:01](https://github.com/leanprover-community/mathlib/commit/c5a8a81)
refactor(topology/algebra/uniform_group): Use `to_additive`. ([#11662](https://github.com/leanprover-community/mathlib/pull/11662))
This PR refactors `topology/algebra/uniform_group` to use `to_additive`.
#### Estimated changes
Modified src/topology/algebra/group_completion.lean


Modified src/topology/algebra/uniform_group.lean
- \- *lemma* add_monoid_hom.uniform_continuous_of_continuous_at_zero
- \- *lemma* cauchy_seq.add
- \+ *lemma* cauchy_seq.mul
- \+/\- *lemma* group_separation_rel
- \+ *lemma* monoid_hom.uniform_continuous_of_continuous_at_one
- \+ *lemma* tendsto_div_comap_self
- \- *lemma* tendsto_sub_comap_self
- \- *lemma* to_uniform_space_eq
- \- *lemma* topological_add_group.separated_iff_zero_closed
- \- *lemma* topological_add_group.separated_of_zero_sep
- \- *lemma* topological_add_group_is_uniform
- \+ *lemma* topological_group.separated_iff_one_closed
- \+ *lemma* topological_group.separated_of_one_sep
- \+ *lemma* topological_group_is_uniform
- \- *theorem* uniform_add_group.mk'
- \- *lemma* uniform_continuous.add
- \+ *lemma* uniform_continuous.div
- \+ *lemma* uniform_continuous.inv
- \+ *lemma* uniform_continuous.mul
- \- *lemma* uniform_continuous.neg
- \- *lemma* uniform_continuous.sub
- \- *lemma* uniform_continuous_add
- \+ *lemma* uniform_continuous_div
- \+ *lemma* uniform_continuous_inv
- \+ *lemma* uniform_continuous_monoid_hom_of_continuous
- \+ *lemma* uniform_continuous_mul
- \- *lemma* uniform_continuous_neg
- \- *lemma* uniform_continuous_of_continuous
- \+ *lemma* uniform_continuous_of_tendsto_one
- \- *lemma* uniform_continuous_of_tendsto_zero
- \- *lemma* uniform_continuous_sub
- \- *lemma* uniform_embedding_translate
- \+ *lemma* uniform_embedding_translate_mul
- \+ *theorem* uniform_group.mk'
- \+ *lemma* uniform_group.to_uniform_space_eq
- \+ *lemma* uniformity_eq_comap_nhds_one'
- \+ *lemma* uniformity_eq_comap_nhds_one
- \- *lemma* uniformity_eq_comap_nhds_zero'
- \- *lemma* uniformity_eq_comap_nhds_zero
- \- *lemma* uniformity_translate
- \+ *lemma* uniformity_translate_mul

Modified src/topology/algebra/uniform_ring.lean




## [2022-01-26 13:30:00](https://github.com/leanprover-community/mathlib/commit/5472f0a)
feat(group_theory/subgroup/basic): add lemmas related to map, comap, normalizer ([#11637](https://github.com/leanprover-community/mathlib/pull/11637))
which are useful when `H < K < G` and one needs to move from `subgroup
G` to `subgroup K`
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+ *lemma* is_p_group.comap_subtype

Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.comap_normalizer_eq_of_injective_of_le_range
- \+ *lemma* subgroup.comap_subtype_normalizer_eq
- \+ *lemma* subgroup.comap_subtype_self_eq_top



## [2022-01-26 13:29:59](https://github.com/leanprover-community/mathlib/commit/2b25723)
feat(group_theory/sylow): add characteristic_of_normal ([#11636](https://github.com/leanprover-community/mathlib/pull/11636))
A normal sylow subgroup is characteristic.
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *lemma* sylow.characteristic_of_normal
- \+ *lemma* sylow.smul_eq_of_normal
- \+ *lemma* sylow.subsingleton_of_normal



## [2022-01-26 13:29:58](https://github.com/leanprover-community/mathlib/commit/1a72f88)
feat(analysis/inner_product_space/basic): isometries and orthonormal families ([#11631](https://github.com/leanprover-community/mathlib/pull/11631))
Add various lemmas and definitions about the action of isometries on
orthonormal families of vectors.  An isometry preserves the property
of being orthonormal; a linear map sending an orthonormal basis to an
orthonormal family is a linear isometry, and a linear equiv sending an
orthonormal basis to an orthonormal family is a linear isometry equiv.
A definition `orthonormal.equiv` is provided that uses `basis.equiv`
to provide a linear isometry equiv mapping a given orthonormal basis
to another given orthonormal basis, and lemmas are provided analogous
to those for `basis.equiv` (`orthonormal.map_equiv` isn't a `simp`
lemma because `simp` can prove it).
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* linear_equiv.coe_isometry_of_orthonormal
- \+ *def* linear_equiv.isometry_of_orthonormal
- \+ *lemma* linear_equiv.isometry_of_orthonormal_to_linear_equiv
- \+ *lemma* linear_map.coe_isometry_of_orthonormal
- \+ *def* linear_map.isometry_of_orthonormal
- \+ *lemma* linear_map.isometry_of_orthonormal_to_linear_map
- \+ *lemma* orthonormal.comp_linear_isometry
- \+ *lemma* orthonormal.comp_linear_isometry_equiv
- \+ *def* orthonormal.equiv
- \+ *lemma* orthonormal.equiv_apply
- \+ *lemma* orthonormal.equiv_refl
- \+ *lemma* orthonormal.equiv_symm
- \+ *lemma* orthonormal.equiv_to_linear_equiv
- \+ *lemma* orthonormal.equiv_trans
- \+ *lemma* orthonormal.map_equiv



## [2022-01-26 13:29:57](https://github.com/leanprover-community/mathlib/commit/631f339)
feat(measure_theory/measure/haar_lebesgue): a density point for closed balls is a density point for rescalings of arbitrary sets ([#11620](https://github.com/leanprover-community/mathlib/pull/11620))
Consider a point `x` in a finite-dimensional real vector space with a Haar measure, at which a set `s` has density one, with respect to closed balls (i.e., a Lebesgue density point of `s`). Then `s` has also density one at `x` with respect to any measurable set `t`: the proportion of points in `s` belonging to a rescaled copy `{x} + r • t` of `t` tends to one as `r` tends to zero. In particular, `s ∩ ({x} + r • t)` is nonempty for small enough `r`.
#### Estimated changes
Modified src/measure_theory/measure/haar_lebesgue.lean
- \+ *lemma* measure_theory.measure.add_haar_ball_mul
- \+ *lemma* measure_theory.measure.add_haar_ball_mul_of_pos
- \+ *lemma* measure_theory.measure.add_haar_closed_ball_mul
- \+ *lemma* measure_theory.measure.add_haar_closed_ball_mul_of_pos
- \+ *lemma* measure_theory.measure.add_haar_singleton_add_smul_div_singleton_add_smul
- \+ *lemma* measure_theory.measure.eventually_nonempty_inter_smul_of_density_one
- \+ *lemma* measure_theory.measure.tendsto_add_haar_inter_smul_one_of_density_one
- \+ *lemma* measure_theory.measure.tendsto_add_haar_inter_smul_one_of_density_one_aux
- \+ *lemma* measure_theory.measure.tendsto_add_haar_inter_smul_zero_of_density_zero
- \+ *lemma* measure_theory.measure.tendsto_add_haar_inter_smul_zero_of_density_zero_aux1
- \+ *lemma* measure_theory.measure.tendsto_add_haar_inter_smul_zero_of_density_zero_aux2

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.Union_inter_closed_ball_nat



## [2022-01-26 13:29:54](https://github.com/leanprover-community/mathlib/commit/590b5eb)
feat(analysis/seminorm): The norm as a seminorm, balanced and absorbent lemmas ([#11487](https://github.com/leanprover-community/mathlib/pull/11487))
This
* defines `norm_seminorm`, the norm as a seminorm. This is useful to translate seminorm lemmas to norm lemmas
* proves many lemmas about `balanced`, `absorbs`, `absorbent`
* generalizes many lemmas about the aforementioned predicates. In particular, `one_le_gauge_of_not_mem` now takes `(star_convex ℝ 0 s) (absorbs ℝ s {x})` instead of `(convex ℝ s) ((0 : E) ∈ s) (is_open s)`. The new `star_convex` lemmas justify that it's a generalization.
* proves `star_convex_zero_iff`
* proves `ne_zero_of_norm_ne_zero` and friends
* makes `x` implicit in `convex.star_convex`
* renames `balanced.univ` to `balanced_univ`
#### Estimated changes
Modified src/algebra/smul_with_zero.lean
- \+ *lemma* smul_inv₀

Modified src/analysis/complex/circle.lean
- \+ *lemma* ne_zero_of_mem_circle
- \- *lemma* nonzero_of_mem_circle

Modified src/analysis/convex/star.lean
- \+ *lemma* convex.star_convex
- \+ *lemma* star_convex_zero_iff

Modified src/analysis/fourier.lean


Modified src/analysis/inner_product_space/rayleigh.lean


Modified src/analysis/normed/group/basic.lean
- \+ *lemma* ne_zero_of_mem_sphere
- \+ *lemma* ne_zero_of_mem_unit_sphere
- \+ *lemma* ne_zero_of_nnnorm_ne_zero
- \+ *lemma* ne_zero_of_norm_ne_zero
- \- *lemma* ne_zero_of_norm_pos
- \+ *lemma* nnnorm_ne_zero_iff
- \- *lemma* nonzero_of_mem_sphere
- \- *lemma* nonzero_of_mem_unit_sphere
- \+ *lemma* norm_ne_zero_iff

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* ne_neg_of_mem_sphere

Modified src/analysis/normed_space/spectrum.lean


Modified src/analysis/seminorm.lean
- \+ *lemma* absorbent.absorbs
- \+ *lemma* absorbent.zero_mem
- \+ *lemma* absorbent_ball
- \+ *lemma* absorbent_ball_zero
- \+ *lemma* absorbent_univ
- \+ *lemma* absorbs.inter
- \+ *lemma* absorbs.mono
- \+ *lemma* absorbs.mono_left
- \+ *lemma* absorbs.mono_right
- \+ *lemma* absorbs.union
- \+ *lemma* absorbs_inter
- \+ *lemma* absorbs_union
- \+ *lemma* absorbs_zero_iff
- \+ *lemma* balanced.smul_mono
- \+ *lemma* balanced.star_convex
- \- *lemma* balanced.univ
- \+ *lemma* balanced_ball_zero
- \+ *lemma* balanced_univ
- \+/\- *lemma* balanced_zero_union_interior
- \+ *lemma* ball_norm_seminorm
- \+ *lemma* coe_norm_seminorm
- \+ *lemma* convex.gauge_le
- \- *lemma* convex.gauge_le_one
- \+/\- *lemma* exists_lt_of_gauge_lt
- \+ *lemma* gauge_ball
- \+ *lemma* gauge_empty
- \+ *lemma* gauge_le_eq
- \+/\- *lemma* gauge_le_of_mem
- \- *lemma* gauge_le_one_eq'
- \- *lemma* gauge_le_one_eq
- \+ *lemma* gauge_lt_eq'
- \+ *lemma* gauge_lt_eq
- \+ *lemma* gauge_lt_of_mem_smul
- \- *lemma* gauge_lt_one_eq'
- \- *lemma* gauge_lt_one_eq
- \+/\- *lemma* gauge_lt_one_eq_self_of_open
- \+/\- *lemma* gauge_lt_one_of_mem_of_open
- \+ *lemma* gauge_mono
- \+ *lemma* gauge_of_subset_zero
- \+/\- *def* gauge_seminorm
- \+ *lemma* gauge_seminorm_lt_one_of_open
- \+ *lemma* gauge_smul_left
- \+ *lemma* gauge_smul_left_of_nonneg
- \+ *lemma* gauge_unit_ball
- \+ *lemma* gauge_zero'
- \+ *lemma* le_gauge_of_not_mem
- \+ *lemma* mul_gauge_le_norm
- \+ *def* norm_seminorm
- \+/\- *lemma* one_le_gauge_of_not_mem
- \- *lemma* seminorm.absorbent_ball
- \- *lemma* seminorm.absorbent_ball_zero
- \+/\- *lemma* seminorm.balanced_ball_zero
- \- *lemma* seminorm.gauge_ball
- \+/\- *lemma* seminorm.mem_ball
- \+ *lemma* smul_unit_ball

Modified src/geometry/manifold/instances/sphere.lean




## [2022-01-26 13:29:53](https://github.com/leanprover-community/mathlib/commit/573ca83)
feat(analysis/seminorm): add some lemmas for seminorm balls ([#11471](https://github.com/leanprover-community/mathlib/pull/11471))
Add some lemmas for seminorm balls.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* seminorm.ball_add_ball_subset
- \+ *lemma* seminorm.ball_antitone
- \+ *lemma* seminorm.ball_mono
- \+ *lemma* seminorm.ball_smul_ball
- \+ *lemma* seminorm.neg_ball
- \+ *lemma* seminorm.smul_ball_preimage



## [2022-01-26 13:29:52](https://github.com/leanprover-community/mathlib/commit/07d8ca6)
feat(combinatorics/configuration): Formula for cardinality of a projective plane ([#11462](https://github.com/leanprover-community/mathlib/pull/11462))
This PR proves the formula for the cardinality of a projective plane in terms of the order.
#### Estimated changes
Modified src/combinatorics/configuration.lean
- \+ *lemma* configuration.projective_plane.card_lines
- \+ *lemma* configuration.projective_plane.card_points



## [2022-01-26 11:53:03](https://github.com/leanprover-community/mathlib/commit/7f0f3f1)
feat(algebra/order/hom/monoid): Ordered monoid/group homomorphisms ([#11633](https://github.com/leanprover-community/mathlib/pull/11633))
Define
* `order_add_monoid_hom` with notation `→+o`
* `order_monoid_hom` with notation `→*o`
* `order_monoid_with_zero_hom` with notation `→*₀o`
and their corresponding hom classes.
Also add a few missing API lemmas in `algebra.group.hom` and `order.hom.basic`.
#### Estimated changes
Modified src/algebra/group/hom.lean


Added src/algebra/order/hom/monoid.lean
- \+ *structure* order_add_monoid_hom
- \+ *lemma* order_monoid_hom.cancel_left
- \+ *lemma* order_monoid_hom.cancel_right
- \+ *lemma* order_monoid_hom.coe_comp
- \+ *lemma* order_monoid_hom.coe_comp_monoid_hom
- \+ *lemma* order_monoid_hom.coe_comp_order_hom
- \+ *lemma* order_monoid_hom.coe_id
- \+ *lemma* order_monoid_hom.coe_mk
- \+ *lemma* order_monoid_hom.coe_monoid_hom
- \+ *lemma* order_monoid_hom.coe_mul
- \+ *lemma* order_monoid_hom.coe_one
- \+ *lemma* order_monoid_hom.coe_order_hom
- \+ *def* order_monoid_hom.comp
- \+ *lemma* order_monoid_hom.comp_apply
- \+ *lemma* order_monoid_hom.comp_assoc
- \+ *lemma* order_monoid_hom.comp_id
- \+ *lemma* order_monoid_hom.comp_mul
- \+ *lemma* order_monoid_hom.comp_one
- \+ *lemma* order_monoid_hom.ext
- \+ *lemma* order_monoid_hom.id_comp
- \+ *def* order_monoid_hom.mk'
- \+ *lemma* order_monoid_hom.mk_coe
- \+ *lemma* order_monoid_hom.mul_apply
- \+ *lemma* order_monoid_hom.mul_comp
- \+ *lemma* order_monoid_hom.one_apply
- \+ *lemma* order_monoid_hom.one_comp
- \+ *lemma* order_monoid_hom.to_fun_eq_coe
- \+ *lemma* order_monoid_hom.to_monoid_hom_eq_coe
- \+ *lemma* order_monoid_hom.to_monoid_hom_injective
- \+ *def* order_monoid_hom.to_order_hom
- \+ *lemma* order_monoid_hom.to_order_hom_eq_coe
- \+ *lemma* order_monoid_hom.to_order_hom_injective
- \+ *structure* order_monoid_hom
- \+ *lemma* order_monoid_with_zero_hom.cancel_left
- \+ *lemma* order_monoid_with_zero_hom.cancel_right
- \+ *lemma* order_monoid_with_zero_hom.coe_comp
- \+ *lemma* order_monoid_with_zero_hom.coe_comp_monoid_with_zero_hom
- \+ *lemma* order_monoid_with_zero_hom.coe_comp_order_monoid_hom
- \+ *lemma* order_monoid_with_zero_hom.coe_id
- \+ *lemma* order_monoid_with_zero_hom.coe_mk
- \+ *lemma* order_monoid_with_zero_hom.coe_monoid_with_zero_hom
- \+ *lemma* order_monoid_with_zero_hom.coe_mul
- \+ *lemma* order_monoid_with_zero_hom.coe_order_monoid_hom
- \+ *def* order_monoid_with_zero_hom.comp
- \+ *lemma* order_monoid_with_zero_hom.comp_apply
- \+ *lemma* order_monoid_with_zero_hom.comp_assoc
- \+ *lemma* order_monoid_with_zero_hom.comp_id
- \+ *lemma* order_monoid_with_zero_hom.comp_mul
- \+ *lemma* order_monoid_with_zero_hom.ext
- \+ *lemma* order_monoid_with_zero_hom.id_comp
- \+ *lemma* order_monoid_with_zero_hom.mk_coe
- \+ *lemma* order_monoid_with_zero_hom.mul_apply
- \+ *lemma* order_monoid_with_zero_hom.mul_comp
- \+ *lemma* order_monoid_with_zero_hom.to_fun_eq_coe
- \+ *lemma* order_monoid_with_zero_hom.to_monoid_with_zero_hom_eq_coe
- \+ *lemma* order_monoid_with_zero_hom.to_monoid_with_zero_hom_injective
- \+ *def* order_monoid_with_zero_hom.to_order_monoid_hom
- \+ *lemma* order_monoid_with_zero_hom.to_order_monoid_hom_eq_coe
- \+ *lemma* order_monoid_with_zero_hom.to_order_monoid_hom_injective
- \+ *structure* order_monoid_with_zero_hom

Modified src/order/hom/basic.lean




## [2022-01-26 11:25:56](https://github.com/leanprover-community/mathlib/commit/20aae83)
feat(order/hom/lattice): Lattice homomorphisms ([#11610](https://github.com/leanprover-community/mathlib/pull/11610))
This defines (bounded) lattice homomorphisms using the `fun_like` along with weaker homomorphisms that only preserve `sup`, `inf`, `top`, `bot`.
#### Estimated changes
Added src/order/hom/lattice.lean
- \+ *lemma* bot_hom.bot_apply
- \+ *lemma* bot_hom.coe_bot
- \+ *lemma* bot_hom.coe_id
- \+ *lemma* bot_hom.coe_inf
- \+ *lemma* bot_hom.coe_sup
- \+ *lemma* bot_hom.ext
- \+ *lemma* bot_hom.id_apply
- \+ *lemma* bot_hom.inf_apply
- \+ *lemma* bot_hom.sup_apply
- \+ *lemma* bot_hom.to_fun_eq_coe
- \+ *structure* bot_hom
- \+ *lemma* bounded_lattice_hom.coe_id
- \+ *lemma* bounded_lattice_hom.ext
- \+ *lemma* bounded_lattice_hom.id_apply
- \+ *def* bounded_lattice_hom.to_bot_hom
- \+ *lemma* bounded_lattice_hom.to_fun_eq_coe
- \+ *def* bounded_lattice_hom.to_top_hom
- \+ *structure* bounded_lattice_hom
- \+ *lemma* inf_hom.coe_const
- \+ *lemma* inf_hom.coe_id
- \+ *lemma* inf_hom.coe_inf
- \+ *def* inf_hom.const
- \+ *lemma* inf_hom.const_apply
- \+ *lemma* inf_hom.ext
- \+ *lemma* inf_hom.id_apply
- \+ *lemma* inf_hom.inf_apply
- \+ *lemma* inf_hom.to_fun_eq_coe
- \+ *structure* inf_hom
- \+ *lemma* lattice_hom.coe_id
- \+ *lemma* lattice_hom.ext
- \+ *lemma* lattice_hom.id_apply
- \+ *lemma* lattice_hom.to_fun_eq_coe
- \+ *def* lattice_hom.to_inf_hom
- \+ *structure* lattice_hom
- \+ *lemma* sup_hom.coe_const
- \+ *lemma* sup_hom.coe_id
- \+ *lemma* sup_hom.coe_sup
- \+ *def* sup_hom.const
- \+ *lemma* sup_hom.const_apply
- \+ *lemma* sup_hom.ext
- \+ *lemma* sup_hom.id_apply
- \+ *lemma* sup_hom.sup_apply
- \+ *lemma* sup_hom.to_fun_eq_coe
- \+ *structure* sup_hom
- \+ *lemma* top_hom.coe_id
- \+ *lemma* top_hom.coe_inf
- \+ *lemma* top_hom.coe_sup
- \+ *lemma* top_hom.coe_top
- \+ *lemma* top_hom.ext
- \+ *lemma* top_hom.id_apply
- \+ *lemma* top_hom.inf_apply
- \+ *lemma* top_hom.sup_apply
- \+ *lemma* top_hom.to_fun_eq_coe
- \+ *lemma* top_hom.top_apply
- \+ *structure* top_hom



## [2022-01-26 10:04:22](https://github.com/leanprover-community/mathlib/commit/09c6ce8)
feat(group_theory/subgroup/basic): add normalizer_condition definition ([#11587](https://github.com/leanprover-community/mathlib/pull/11587))
and an equivalent formula that is a bit easier to work with.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *def* normalizer_condition
- \+ *lemma* normalizer_condition_iff_only_full_group_self_normalizing



## [2022-01-26 09:10:25](https://github.com/leanprover-community/mathlib/commit/c294e4b)
feat(topology/*): replace some `a < b` assumptions with `a ≠ b` ([#11650](https://github.com/leanprover-community/mathlib/pull/11650))
#### Estimated changes
Modified src/analysis/box_integral/box/basic.lean
- \+ *lemma* box_integral.box.lower_ne_upper

Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/special_functions/trigonometric/basic.lean


Modified src/measure_theory/integral/interval_integral.lean


Modified src/topology/algebra/ordered/basic.lean
- \+/\- *lemma* closure_Ico
- \+/\- *lemma* closure_Ioc
- \+/\- *lemma* closure_Ioo

Modified src/topology/algebra/ordered/extend_from.lean




## [2022-01-25 23:46:56](https://github.com/leanprover-community/mathlib/commit/20a461f)
feat(algebra/big_operators/order): The size of a finset of disjoint finsets is less than the size of its union ([#11654](https://github.com/leanprover-community/mathlib/pull/11654))
Prove `card_le_card_bUnion`, its corollary `card_le_card_bUnion_add_card_fiber` where we drop the nonemptiness condition in exchange of a `+` card of the fiber of `∅` on the RHS, and its useful special case `card_le_card_bUnion_add_one`.
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+ *lemma* finset.card_le_card_bUnion
- \+ *lemma* finset.card_le_card_bUnion_add_card_fiber
- \+ *lemma* finset.card_le_card_bUnion_add_one



## [2022-01-25 22:24:52](https://github.com/leanprover-community/mathlib/commit/b237af5)
refactor(set_theory/ordinal_arithmetic): Rename `lsub_le_iff_lt` to `lsub_le` ([#11661](https://github.com/leanprover-community/mathlib/pull/11661))
This way, it directly corresponds to `sup_le`. Ditto for `blsub_le_iff_lt`.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.blsub_le
- \- *theorem* ordinal.blsub_le_iff_lt
- \+ *theorem* ordinal.lsub_le
- \- *theorem* ordinal.lsub_le_iff_lt



## [2022-01-25 22:24:51](https://github.com/leanprover-community/mathlib/commit/b0a1812)
chore(data/buffer/parser/numeral): fix backticks ([#11658](https://github.com/leanprover-community/mathlib/pull/11658))
#### Estimated changes
Modified src/data/buffer/parser/numeral.lean




## [2022-01-25 22:24:50](https://github.com/leanprover-community/mathlib/commit/033dd3c)
feat(analysis/special_functions/complex/circle): `real.angle.exp_map_circle` ([#11627](https://github.com/leanprover-community/mathlib/pull/11627))
Add a version of `exp_map_circle` that applies to a `real.angle`
argument.
#### Estimated changes
Modified src/analysis/special_functions/complex/circle.lean
- \+ *lemma* real.angle.exp_map_circle_coe



## [2022-01-25 22:24:49](https://github.com/leanprover-community/mathlib/commit/f5b11ad)
feat(algebra/lie/{nilpotent,of_associative}): a representation of an associative algebra gives a representation of a Lie algebra ([#11558](https://github.com/leanprover-community/mathlib/pull/11558))
The lemma `lie_algebra.non_trivial_center_of_is_nilpotent` is unrelated.
#### Estimated changes
Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* lie_algebra.non_trivial_center_of_is_nilpotent

Modified src/algebra/lie/of_associative.lean
- \+ *lemma* lie_eq_smul
- \+ *def* lie_module.of_associative_module
- \+ *lemma* lie_module.to_endomorphism_module_End
- \+ *def* lie_ring_module.of_associative_module

Modified src/algebra/module/linear_map.lean




## [2022-01-25 20:59:08](https://github.com/leanprover-community/mathlib/commit/99608cc)
feat(group_theory/sub{monoid,group}, linear_algebra/basic): add `supr_induction` for `submonoid`, `add_submonoid`, `subgroup`, `add_subgroup`, and `submodule` ([#11556](https://github.com/leanprover-community/mathlib/pull/11556))
This also adds dependent versions, which match the style of the dependent versions of `submodule.span_induction` and `submonoid.closure_induction` in [#11555](https://github.com/leanprover-community/mathlib/pull/11555).
Primarily it's the group and module versions that are useful here, as they remove the inv and smul obligations that would appear if using `closure_induction` or `span_induction`.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+/\- *lemma* subgroup.mem_supr_of_mem
- \+ *lemma* subgroup.supr_eq_closure
- \+ *lemma* subgroup.supr_induction'
- \+ *lemma* subgroup.supr_induction

Modified src/group_theory/submonoid/membership.lean
- \+/\- *lemma* submonoid.mem_supr_of_mem
- \+ *lemma* submonoid.supr_induction'
- \+ *lemma* submonoid.supr_induction

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.supr_induction'
- \+ *lemma* submodule.supr_induction



## [2022-01-25 20:59:07](https://github.com/leanprover-community/mathlib/commit/25d1341)
feat(group_theory/sub{monoid,group}, linear_algebra/basic): remove specialization to subtypes from dependent recursors ([#11555](https://github.com/leanprover-community/mathlib/pull/11555))
The following recursors (the first of which was added in [#4984](https://github.com/leanprover-community/mathlib/pull/4984)) are more generally applicable than to subtypes alone:
* `submonoid.closure_induction'`
* `add_submonoid.closure_induction'`
* `subgroup.closure_induction'`
* `add_subgroup.closure_induction'`
* `submodule.span_induction'`
Now that these live right next to their non-dependent version, there is little need to repeat the docstring.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+/\- *lemma* subgroup.closure_induction'

Modified src/group_theory/submonoid/basic.lean
- \+ *lemma* submonoid.closure_induction'

Modified src/group_theory/submonoid/operations.lean
- \- *lemma* submonoid.closure_induction'

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* submodule.span_induction'

Modified src/model_theory/basic.lean
- \+/\- *lemma* first_order.language.substructure.closure_induction'



## [2022-01-25 20:59:06](https://github.com/leanprover-community/mathlib/commit/7e09827)
feat(analysis/inner_product_space/adjoint): matrix and linear map adjoints agree ([#11551](https://github.com/leanprover-community/mathlib/pull/11551))
#### Estimated changes
Modified src/analysis/inner_product_space/adjoint.lean
- \+ *lemma* matrix.conj_transpose_eq_adjoint



## [2022-01-25 20:59:04](https://github.com/leanprover-community/mathlib/commit/84f2e93)
feat(group_theory/free_abelian_group): add free_abelian_group.basis ([#11465](https://github.com/leanprover-community/mathlib/pull/11465))
Although a statement about `free_abelian_group`, it lives in
`free_abelian_group_finsupp` because it uses the isomorphism between
`free_abelian_group X` and `X →₀ ℤ`
#### Estimated changes
Modified src/group_theory/free_abelian_group_finsupp.lean




## [2022-01-25 19:51:28](https://github.com/leanprover-community/mathlib/commit/009cec0)
feat(set_theory/cardinal_ordinal): Aleph is positive ([#11657](https://github.com/leanprover-community/mathlib/pull/11657))
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* cardinal.aleph'_pos
- \+ *theorem* cardinal.aleph_pos



## [2022-01-25 17:30:28](https://github.com/leanprover-community/mathlib/commit/6184db1)
feat(topology/algebra/mul_action2): quotient by a properly discontinuous group action is t2 ([#10465](https://github.com/leanprover-community/mathlib/pull/10465))
We prove that the quotient of a Hausdorff (t2) locally compact space by a properly discontinuous group action is itself Hausdorff.
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \+ *lemma* mul_action.image_inter_image_iff
- \+ *lemma* mul_action.quotient_preimage_image_eq_union_mul

Modified src/topology/algebra/mul_action.lean


Added src/topology/algebra/mul_action2.lean
- \+ *def* homeomorph.smul
- \+ *def* homeomorph.vadd
- \+ *lemma* is_open_map_quotient_mk_mul

Modified src/topology/separation.lean
- \+ *lemma* t2_separation_compact_nhds
- \+ *lemma* t2_separation_nhds
- \+ *lemma* t2_space_iff_nhds

Modified src/topology/subset_properties.lean
- \+ *lemma* local_compact_nhds



## [2022-01-25 13:19:58](https://github.com/leanprover-community/mathlib/commit/4d761f4)
feat(algebra/group/hom): Notation for `monoid_with_zero_hom` ([#11632](https://github.com/leanprover-community/mathlib/pull/11632))
Introduce notation `→*₀` for `monoid_with_zero_hom` and use it everywhere.
#### Estimated changes
Modified src/algebra/gcd_monoid/basic.lean
- \+/\- *def* normalize

Modified src/algebra/group/hom.lean
- \+/\- *lemma* monoid_with_zero_hom.cancel_left
- \+/\- *lemma* monoid_with_zero_hom.cancel_right
- \+/\- *lemma* monoid_with_zero_hom.comp_apply
- \+/\- *theorem* monoid_with_zero_hom.congr_arg
- \+/\- *theorem* monoid_with_zero_hom.congr_fun
- \+/\- *lemma* monoid_with_zero_hom.ext
- \+/\- *lemma* monoid_with_zero_hom.ext_iff
- \+/\- *def* monoid_with_zero_hom.id
- \+/\- *lemma* monoid_with_zero_hom.mk_coe

Modified src/algebra/group/prod.lean
- \+/\- *def* div_monoid_with_zero_hom
- \+/\- *def* mul_monoid_with_zero_hom

Modified src/algebra/group_with_zero/basic.lean
- \+/\- *def* inv_monoid_with_zero_hom

Modified src/algebra/group_with_zero/power.lean


Modified src/algebra/order/absolute_value.lean
- \+/\- *def* absolute_value.to_monoid_with_zero_hom
- \+/\- *def* is_absolute_value.abv_hom

Modified src/algebra/order/field.lean
- \+/\- *lemma* abs_div
- \+/\- *lemma* abs_inv

Modified src/algebra/order/ring.lean
- \+/\- *def* abs_hom

Modified src/algebra/quaternion.lean
- \+/\- *def* quaternion.norm_sq

Modified src/algebra/ring/basic.lean


Modified src/algebra/smul_with_zero.lean
- \+/\- *def* mul_action_with_zero.comp_hom

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* normed_field.nnnorm_div
- \+/\- *def* normed_field.nnnorm_hom
- \+/\- *lemma* normed_field.norm_div
- \+/\- *def* normed_field.norm_hom
- \+/\- *lemma* normed_field.norm_inv
- \+/\- *lemma* normed_field.norm_zpow

Modified src/data/complex/basic.lean
- \+/\- *def* complex.norm_sq

Modified src/data/complex/is_R_or_C.lean
- \+/\- *def* is_R_or_C.norm_sq

Modified src/data/fintype/basic.lean


Modified src/data/int/cast.lean
- \+ *lemma* monoid_with_zero_hom.ext_int'
- \- *theorem* monoid_with_zero_hom.ext_int'
- \+ *lemma* monoid_with_zero_hom.ext_int
- \- *theorem* monoid_with_zero_hom.ext_int

Modified src/data/nat/cast.lean


Modified src/data/rat/cast.lean
- \+/\- *theorem* monoid_with_zero_hom.ext_rat
- \+/\- *theorem* monoid_with_zero_hom.ext_rat_on_pnat

Modified src/data/real/nnreal.lean


Modified src/data/real/sqrt.lean


Modified src/ring_theory/non_zero_divisors.lean
- \+/\- *lemma* monoid_with_zero_hom.map_le_non_zero_divisors_of_injective
- \+/\- *lemma* monoid_with_zero_hom.map_ne_zero_of_mem_non_zero_divisors

Modified src/ring_theory/valuation/basic.lean
- \+/\- *lemma* valuation.coe_coe
- \+/\- *lemma* valuation.is_equiv.map
- \+/\- *def* valuation.map
- \+/\- *structure* valuation



## [2022-01-25 12:25:39](https://github.com/leanprover-community/mathlib/commit/1b3da83)
feat(combinatorics/simple_graph/coloring): add inequalities from embeddings ([#11548](https://github.com/leanprover-community/mathlib/pull/11548))
Also add a lemma that the chromatic number of an infinite complete graph is zero (i.e., it needs infinitely many colors), as suggested by @arthurpaulino.
#### Estimated changes
Modified src/combinatorics/simple_graph/coloring.lean
- \- *lemma* simple_graph.chromatic_number_complete_graph
- \- *lemma* simple_graph.chromatic_number_le_of_forall_imp
- \- *lemma* simple_graph.chromatic_number_le_of_le_colorable
- \+ *lemma* simple_graph.chromatic_number_pos
- \+ *lemma* simple_graph.chromatic_number_top
- \+ *lemma* simple_graph.chromatic_number_top_eq_zero_of_infinite
- \+ *lemma* simple_graph.colorable.chromatic_number_le_of_forall_imp
- \+ *lemma* simple_graph.colorable.chromatic_number_mono
- \+ *lemma* simple_graph.colorable.chromatic_number_mono_of_embedding
- \+ *lemma* simple_graph.colorable.mono
- \+ *lemma* simple_graph.colorable.mono_left
- \+ *lemma* simple_graph.colorable.of_embedding
- \- *lemma* simple_graph.colorable.of_le
- \+ *lemma* simple_graph.colorable_of_chromatic_number_pos
- \- *lemma* simple_graph.colorable_of_le_colorable
- \- *lemma* simple_graph.zero_lt_chromatic_number

Modified src/combinatorics/simple_graph/partition.lean




## [2022-01-25 12:25:38](https://github.com/leanprover-community/mathlib/commit/158c0ea)
feat(group_theory/abelianization): add abelianization_of_comm_group ([#11467](https://github.com/leanprover-community/mathlib/pull/11467))
#### Estimated changes
Modified src/group_theory/abelianization.lean
- \+ *def* abelianization.equiv_of_comm



## [2022-01-25 10:49:34](https://github.com/leanprover-community/mathlib/commit/494f719)
feat(data/fun_like): define `embedding_like` and `equiv_like` ([#10759](https://github.com/leanprover-community/mathlib/pull/10759))
These extend `fun_like` with a proof of injectivity resp. an inverse.
The number of new generic lemmas is quite low at the moment, so their use is more in defining derived classes such as `mul_equiv_class`.
#### Estimated changes
Modified src/algebra/group/freiman.lean


Modified src/algebra/group/hom.lean


Modified src/data/equiv/basic.lean
- \+/\- *theorem* equiv.apply_eq_iff_eq
- \+/\- *lemma* equiv.bijective_comp
- \+/\- *theorem* equiv.coe_fn_injective
- \+/\- *lemma* equiv.comp_bijective
- \+/\- *lemma* equiv.comp_injective
- \+/\- *lemma* equiv.comp_surjective
- \+/\- *lemma* equiv.ext
- \+/\- *lemma* equiv.ext_iff
- \+/\- *lemma* equiv.injective_comp
- \+/\- *lemma* equiv.surjective_comp

Renamed src/data/fun_like.lean to src/data/fun_like/basic.lean


Added src/data/fun_like/embedding.lean
- \+ *structure* cooler_embedding
- \+ *lemma* do_something
- \+ *lemma* embedding_like.apply_eq_iff_eq
- \+ *lemma* embedding_like.comp_injective
- \+ *lemma* map_cool
- \+ *lemma* map_op

Added src/data/fun_like/equiv.lean
- \+ *structure* cooler_iso
- \+ *lemma* do_something
- \+ *theorem* equiv_like.apply_eq_iff_eq
- \+ *lemma* equiv_like.bijective_comp
- \+ *lemma* equiv_like.comp_bijective
- \+ *lemma* equiv_like.comp_injective
- \+ *lemma* equiv_like.comp_surjective
- \+ *lemma* equiv_like.injective_comp
- \+ *lemma* equiv_like.inv_injective
- \+ *lemma* equiv_like.surjective_comp
- \+ *lemma* map_cool

Modified src/logic/embedding.lean
- \+/\- *lemma* function.embedding.apply_eq_iff_eq
- \+/\- *lemma* function.embedding.coe_injective
- \+/\- *lemma* function.embedding.ext
- \+/\- *lemma* function.embedding.ext_iff

Modified src/order/rel_iso.lean




## [2022-01-25 10:04:17](https://github.com/leanprover-community/mathlib/commit/6b32241)
feat(model_theory/basic): Terms, formulas, and definable sets ([#11067](https://github.com/leanprover-community/mathlib/pull/11067))
Defines first-order terms, formulas, sentences and theories
Defines the boolean algebra of definable sets
(Several of these definitions are based on those from the flypitch project.)
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *def* first_order.language.bd_not
- \+ *inductive* first_order.language.bounded_formula
- \+ *lemma* first_order.language.definable_set.coe_bot
- \+ *lemma* first_order.language.definable_set.coe_compl
- \+ *lemma* first_order.language.definable_set.coe_inf
- \+ *lemma* first_order.language.definable_set.coe_sup
- \+ *lemma* first_order.language.definable_set.coe_top
- \+ *lemma* first_order.language.definable_set.le_iff
- \+ *lemma* first_order.language.definable_set.mem_compl
- \+ *lemma* first_order.language.definable_set.mem_inf
- \+ *lemma* first_order.language.definable_set.mem_sup
- \+ *lemma* first_order.language.definable_set.mem_top
- \+ *lemma* first_order.language.definable_set.not_mem_bot
- \+ *def* first_order.language.definable_set
- \+ *def* first_order.language.formula
- \+ *lemma* first_order.language.is_definable.compl
- \+ *lemma* first_order.language.is_definable.inter
- \+ *lemma* first_order.language.is_definable.sdiff
- \+ *lemma* first_order.language.is_definable.union
- \+ *structure* first_order.language.is_definable
- \+ *lemma* first_order.language.is_definable_empty
- \+ *lemma* first_order.language.is_definable_univ
- \+ *def* first_order.language.realize_bounded_formula
- \+ *def* first_order.language.realize_formula
- \+ *lemma* first_order.language.realize_not
- \+ *def* first_order.language.realize_sentence
- \+ *def* first_order.language.realize_term
- \+ *def* first_order.language.sentence
- \+ *inductive* first_order.language.term
- \+ *def* first_order.language.theory



## [2022-01-25 08:35:58](https://github.com/leanprover-community/mathlib/commit/4883d11)
feat(README.md): add Kyle Miller as new maintainer ([#11653](https://github.com/leanprover-community/mathlib/pull/11653))
#### Estimated changes
Modified README.md




## [2022-01-25 07:42:56](https://github.com/leanprover-community/mathlib/commit/bf71feb)
feat(number_theory/quadratic_reciprocity): generalise legendre_sym to allow integer first argument ([#11573](https://github.com/leanprover-community/mathlib/pull/11573))
Talking about the legendre symbol of -1 mod p is quite natural, so we generalize to include this case.
So far in a minimal way without changing any existing lemmas
#### Estimated changes
Modified src/number_theory/quadratic_reciprocity.lean
- \+/\- *def* zmod.legendre_sym



## [2022-01-25 07:15:51](https://github.com/leanprover-community/mathlib/commit/f7a597a)
feat(group_theory/nilpotent): add nilpotency_class inequalities ([#11585](https://github.com/leanprover-community/mathlib/pull/11585))
Every theorem that proves `nilpotency G'` (e.g. for subgroups, images,
preimages) should be accompanied by a lemma relating their
`nilpotency_class`, so add thse lmmeas for subgroups and preimages.
Also add nilpotency lemmas for surjective homomorphisms and quotions,
including nilpotency_class lemmas.
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+/\- *lemma* is_nilpotent_of_ker_le_center
- \+ *lemma* lower_central_series_nilpotency_class
- \+ *lemma* nilpotency_class_le_of_ker_le_center
- \+ *lemma* nilpotency_class_le_of_surjective
- \+ *lemma* nilpotency_class_quotient_le
- \+ *lemma* nilpotent_of_surjective
- \+ *lemma* subgroup.nilpotency_class_le
- \+ *lemma* upper_central_series_nilpotency_class



## [2022-01-25 06:08:03](https://github.com/leanprover-community/mathlib/commit/f278663)
feat(README.md): add Frédéric Dupuis as new maintainer ([#11651](https://github.com/leanprover-community/mathlib/pull/11651))
#### Estimated changes
Modified README.md




## [2022-01-25 05:11:24](https://github.com/leanprover-community/mathlib/commit/b3cd0e6)
chore(order/filter, *): enhancing `filter_upwards` tactic ([#11624](https://github.com/leanprover-community/mathlib/pull/11624))
#### Estimated changes
Modified src/analysis/ODE/picard_lindelof.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/inverse.lean


Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/box_integral/divergence_theorem.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/fderiv_symmetric.lean


Modified src/analysis/calculus/parametric_integral.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/complex/cauchy_integral.lean


Modified src/analysis/convex/integral.lean


Modified src/analysis/fourier.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/exponential.lean


Modified src/analysis/normed_space/pointwise.lean


Modified src/analysis/special_functions/bernstein.lean


Modified src/analysis/special_functions/complex/arg.lean


Modified src/analysis/special_functions/exponential.lean


Modified src/analysis/special_functions/non_integrable.lean


Modified src/analysis/special_functions/trigonometric/basic.lean


Modified src/analysis/special_functions/trigonometric/inverse_deriv.lean


Modified src/analysis/specific_limits.lean


Modified src/analysis/subadditive.lean


Modified src/dynamics/ergodic/conservative.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/constructions/prod.lean


Modified src/measure_theory/covering/besicovitch.lean


Modified src/measure_theory/covering/differentiation.lean


Modified src/measure_theory/covering/vitali_family.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/function/ae_eq_fun.lean


Modified src/measure_theory/function/ae_eq_of_integral.lean


Modified src/measure_theory/function/ae_measurable_order.lean


Modified src/measure_theory/function/l1_space.lean


Modified src/measure_theory/function/l2_space.lean


Modified src/measure_theory/function/lp_order.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/function/simple_func_dense.lean


Modified src/measure_theory/function/uniform_integrable.lean


Modified src/measure_theory/integral/bochner.lean


Modified src/measure_theory/integral/integrable_on.lean


Modified src/measure_theory/integral/integral_eq_improper.lean


Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/integral/set_integral.lean


Modified src/measure_theory/integral/set_to_l1.lean


Modified src/measure_theory/integral/vitali_caratheodory.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/stieltjes.lean


Modified src/order/filter/archimedean.lean


Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/basic.lean


Modified src/order/filter/pi.lean


Modified src/order/liminf_limsup.lean


Modified src/probability_theory/martingale.lean


Modified src/topology/G_delta.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/algebra/ordered/monotone_continuity.lean


Modified src/topology/basic.lean


Modified src/topology/category/Compactum.lean


Modified src/topology/dense_embedding.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/partition_of_unity.lean


Modified src/topology/semicontinuous.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/urysohns_lemma.lean




## [2022-01-25 03:33:34](https://github.com/leanprover-community/mathlib/commit/8cc2ff4)
refactor(order/{bounded, rel_classes}): Moved `bounded` into the `set` namespace ([#11594](https://github.com/leanprover-community/mathlib/pull/11594))
As per the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/bounded.2Emono). Closes [#11589](https://github.com/leanprover-community/mathlib/pull/11589).
#### Estimated changes
Modified src/order/bounded.lean
- \- *theorem* bounded.mono
- \- *lemma* bounded.rel_mono
- \- *theorem* bounded_ge_Icc
- \- *theorem* bounded_ge_Ici
- \- *theorem* bounded_ge_Ico
- \- *theorem* bounded_ge_Ioc
- \- *theorem* bounded_ge_Ioi
- \- *theorem* bounded_ge_Ioo
- \- *lemma* bounded_ge_iff_bounded_gt
- \- *theorem* bounded_ge_inter_ge
- \- *theorem* bounded_ge_inter_gt
- \- *theorem* bounded_ge_inter_not_ge
- \- *lemma* bounded_ge_of_bounded_gt
- \- *theorem* bounded_gt_Icc
- \- *theorem* bounded_gt_Ici
- \- *theorem* bounded_gt_Ico
- \- *theorem* bounded_gt_Ioc
- \- *theorem* bounded_gt_Ioi
- \- *theorem* bounded_gt_Ioo
- \- *theorem* bounded_gt_inter_ge
- \- *theorem* bounded_gt_inter_gt
- \- *theorem* bounded_gt_inter_not_gt
- \- *theorem* bounded_inter_not
- \- *theorem* bounded_le_Icc
- \- *theorem* bounded_le_Ico
- \- *theorem* bounded_le_Iic
- \- *theorem* bounded_le_Iio
- \- *theorem* bounded_le_Ioc
- \- *theorem* bounded_le_Ioo
- \- *lemma* bounded_le_iff_bounded_lt
- \- *theorem* bounded_le_inter_le
- \- *theorem* bounded_le_inter_lt
- \- *theorem* bounded_le_inter_not_le
- \- *lemma* bounded_le_of_bounded_lt
- \- *theorem* bounded_lt_Icc
- \- *theorem* bounded_lt_Ico
- \- *theorem* bounded_lt_Iic
- \- *theorem* bounded_lt_Iio
- \- *theorem* bounded_lt_Ioc
- \- *theorem* bounded_lt_Ioo
- \- *theorem* bounded_lt_inter_le
- \- *theorem* bounded_lt_inter_lt
- \- *theorem* bounded_lt_inter_not_lt
- \- *theorem* bounded_self
- \+ *theorem* set.bounded.mono
- \+ *lemma* set.bounded.rel_mono
- \+ *theorem* set.bounded_ge_Icc
- \+ *theorem* set.bounded_ge_Ici
- \+ *theorem* set.bounded_ge_Ico
- \+ *theorem* set.bounded_ge_Ioc
- \+ *theorem* set.bounded_ge_Ioi
- \+ *theorem* set.bounded_ge_Ioo
- \+ *lemma* set.bounded_ge_iff_bounded_gt
- \+ *theorem* set.bounded_ge_inter_ge
- \+ *theorem* set.bounded_ge_inter_gt
- \+ *theorem* set.bounded_ge_inter_not_ge
- \+ *lemma* set.bounded_ge_of_bounded_gt
- \+ *theorem* set.bounded_gt_Icc
- \+ *theorem* set.bounded_gt_Ici
- \+ *theorem* set.bounded_gt_Ico
- \+ *theorem* set.bounded_gt_Ioc
- \+ *theorem* set.bounded_gt_Ioi
- \+ *theorem* set.bounded_gt_Ioo
- \+ *theorem* set.bounded_gt_inter_ge
- \+ *theorem* set.bounded_gt_inter_gt
- \+ *theorem* set.bounded_gt_inter_not_gt
- \+ *theorem* set.bounded_inter_not
- \+ *theorem* set.bounded_le_Icc
- \+ *theorem* set.bounded_le_Ico
- \+ *theorem* set.bounded_le_Iic
- \+ *theorem* set.bounded_le_Iio
- \+ *theorem* set.bounded_le_Ioc
- \+ *theorem* set.bounded_le_Ioo
- \+ *lemma* set.bounded_le_iff_bounded_lt
- \+ *theorem* set.bounded_le_inter_le
- \+ *theorem* set.bounded_le_inter_lt
- \+ *theorem* set.bounded_le_inter_not_le
- \+ *lemma* set.bounded_le_of_bounded_lt
- \+ *theorem* set.bounded_lt_Icc
- \+ *theorem* set.bounded_lt_Ico
- \+ *theorem* set.bounded_lt_Iic
- \+ *theorem* set.bounded_lt_Iio
- \+ *theorem* set.bounded_lt_Ioc
- \+ *theorem* set.bounded_lt_Ioo
- \+ *theorem* set.bounded_lt_inter_le
- \+ *theorem* set.bounded_lt_inter_lt
- \+ *theorem* set.bounded_lt_inter_not_lt
- \+ *theorem* set.bounded_self
- \+ *theorem* set.unbounded.mono
- \+ *lemma* set.unbounded.rel_mono
- \+ *lemma* set.unbounded_ge_iff
- \+ *theorem* set.unbounded_ge_iff_unbounded_inter_ge
- \+ *theorem* set.unbounded_ge_inter_gt
- \+ *theorem* set.unbounded_ge_inter_not_ge
- \+ *lemma* set.unbounded_ge_of_forall_exists_gt
- \+ *lemma* set.unbounded_gt_iff
- \+ *lemma* set.unbounded_gt_iff_unbounded_ge
- \+ *theorem* set.unbounded_gt_inter_gt
- \+ *theorem* set.unbounded_gt_inter_not_gt
- \+ *lemma* set.unbounded_gt_of_forall_exists_ge
- \+ *lemma* set.unbounded_gt_of_unbounded_ge
- \+ *theorem* set.unbounded_inter_ge
- \+ *theorem* set.unbounded_inter_not
- \+ *theorem* set.unbounded_le_Ici
- \+ *theorem* set.unbounded_le_Ioi
- \+ *lemma* set.unbounded_le_iff
- \+ *theorem* set.unbounded_le_inter_le
- \+ *theorem* set.unbounded_le_inter_lt
- \+ *theorem* set.unbounded_le_inter_not_le
- \+ *lemma* set.unbounded_le_of_forall_exists_lt
- \+ *theorem* set.unbounded_lt_Ici
- \+ *theorem* set.unbounded_lt_Ioi
- \+ *lemma* set.unbounded_lt_iff
- \+ *lemma* set.unbounded_lt_iff_unbounded_le
- \+ *theorem* set.unbounded_lt_inter_le
- \+ *theorem* set.unbounded_lt_inter_lt
- \+ *theorem* set.unbounded_lt_inter_not_lt
- \+ *lemma* set.unbounded_lt_of_forall_exists_le
- \+ *lemma* set.unbounded_lt_of_unbounded_le
- \- *theorem* unbounded.mono
- \- *lemma* unbounded.rel_mono
- \- *lemma* unbounded_ge_iff
- \- *theorem* unbounded_ge_iff_unbounded_inter_ge
- \- *theorem* unbounded_ge_inter_gt
- \- *theorem* unbounded_ge_inter_not_ge
- \- *lemma* unbounded_ge_of_forall_exists_gt
- \- *lemma* unbounded_gt_iff
- \- *lemma* unbounded_gt_iff_unbounded_ge
- \- *theorem* unbounded_gt_inter_gt
- \- *theorem* unbounded_gt_inter_not_gt
- \- *lemma* unbounded_gt_of_forall_exists_ge
- \- *lemma* unbounded_gt_of_unbounded_ge
- \- *theorem* unbounded_inter_ge
- \- *theorem* unbounded_inter_not
- \- *theorem* unbounded_le_Ici
- \- *theorem* unbounded_le_Ioi
- \- *lemma* unbounded_le_iff
- \- *theorem* unbounded_le_inter_le
- \- *theorem* unbounded_le_inter_lt
- \- *theorem* unbounded_le_inter_not_le
- \- *lemma* unbounded_le_of_forall_exists_lt
- \- *theorem* unbounded_lt_Ici
- \- *theorem* unbounded_lt_Ioi
- \- *lemma* unbounded_lt_iff
- \- *lemma* unbounded_lt_iff_unbounded_le
- \- *theorem* unbounded_lt_inter_le
- \- *theorem* unbounded_lt_inter_lt
- \- *theorem* unbounded_lt_inter_not_lt
- \- *lemma* unbounded_lt_of_forall_exists_le
- \- *lemma* unbounded_lt_of_unbounded_le

Modified src/order/rel_classes.lean
- \- *def* bounded
- \- *lemma* not_bounded_iff
- \- *lemma* not_unbounded_iff
- \+ *def* set.bounded
- \+ *lemma* set.not_bounded_iff
- \+ *lemma* set.not_unbounded_iff
- \+ *def* set.unbounded
- \- *def* unbounded



## [2022-01-25 03:33:32](https://github.com/leanprover-community/mathlib/commit/b834415)
chore(topology/metric_space/gromov_hausdorff): Golf some theorems ([#11591](https://github.com/leanprover-community/mathlib/pull/11591))
#### Estimated changes
Modified src/topology/metric_space/gromov_hausdorff.lean




## [2022-01-25 03:33:31](https://github.com/leanprover-community/mathlib/commit/88479be)
feat(algebra/big_operators/basic): add lemma `finset.prod_dvd_prod` ([#11521](https://github.com/leanprover-community/mathlib/pull/11521))
For any `S : finset α`, if `∀ a ∈ S, g1 a ∣ g2 a` then `S.prod g1 ∣ S.prod g2`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_dvd_prod



## [2022-01-25 01:56:07](https://github.com/leanprover-community/mathlib/commit/4f5d6ac)
refactor(tactic/interactive): rename tactic.interactive.triv to tactic.interactive.trivial' ([#11643](https://github.com/leanprover-community/mathlib/pull/11643))
The difference between `tactic.interactive.trivial` and `tactic.interactive.triv` is that the latter expands only reducible constants; the first uses `tactic.triv` and the latter uses `tactic.triv'`. This name change is to improve consistency.
Also (slipping in a new feature) add `tactic.interactive.triv`, which is the old `tactic.interactive.triv` but does not run `contradiction`. This is useful for teaching.
#### Estimated changes
Modified src/algebraic_geometry/Gamma_Spec_adjunction.lean


Modified src/data/qpf/multivariate/constructions/fix.lean


Modified src/tactic/interactive.lean




## [2022-01-24 22:53:51](https://github.com/leanprover-community/mathlib/commit/0d172ba)
feat(README.md): add Riccardo Brasca as new maintainer ([#11647](https://github.com/leanprover-community/mathlib/pull/11647))
Add myself as new maintainer and test my superpowers :)
#### Estimated changes
Modified README.md




## [2022-01-24 22:53:50](https://github.com/leanprover-community/mathlib/commit/12fde09)
feat(data/finset/finsupp): Finitely supported product of finsets ([#11639](https://github.com/leanprover-community/mathlib/pull/11639))
Define
* `finsupp.indicator`: Similar to `finsupp.on_finset` except that it only requires a partially defined function. This is more compatible with `finset.pi`.
* `finset.finsupp : finset ι → (ι → finset α) → finset (ι →₀ α)`: Finitely supported product of finsets.
* `finsupp.pi : (ι →₀ finset α) → finset (ι →₀ α)`: The set of finitely supported functions whose `i`-th value lies in the `i`-th of a given `finset`-valued `finsupp`.
#### Estimated changes
Added src/data/finset/finsupp.lean
- \+ *lemma* finset.card_finsupp
- \+ *lemma* finset.mem_finsupp_iff
- \+ *lemma* finset.mem_finsupp_iff_of_support_subset
- \+ *lemma* finsupp.card_pi
- \+ *lemma* finsupp.mem_pi
- \+ *def* finsupp.pi

Modified src/data/finsupp/basic.lean
- \+/\- *def* finsupp.emb_domain.add_monoid_hom
- \+/\- *def* finsupp.map_domain_embedding
- \+/\- *def* finsupp.zip_with

Added src/data/finsupp/indicator.lean
- \+ *def* finsupp.indicator
- \+ *lemma* finsupp.indicator_apply
- \+ *lemma* finsupp.indicator_injective
- \+ *lemma* finsupp.indicator_of_mem
- \+ *lemma* finsupp.indicator_of_not_mem
- \+ *lemma* finsupp.support_indicator_subset



## [2022-01-24 21:01:29](https://github.com/leanprover-community/mathlib/commit/32052b8)
chore(ci): remove working directory on self-hosted ([#11645](https://github.com/leanprover-community/mathlib/pull/11645))
Mathlib now takes several gigabytes to build.  This addresses some of the space issues on the CI machines.
#### Estimated changes
Modified .github/workflows/bors.yml


Modified .github/workflows/build.yml


Modified .github/workflows/build.yml.in


Modified .github/workflows/build_fork.yml




## [2022-01-24 21:01:26](https://github.com/leanprover-community/mathlib/commit/511aa35)
feat(algebra/pointwise): add partial order to `set_semiring` ([#11567](https://github.com/leanprover-community/mathlib/pull/11567))
This PR introduces the natural inclusion order on sets on `set_semiring`.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Ordered.20semirings)
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* set.down_ssubset_down
- \+ *lemma* set.down_subset_down
- \- *def* set.set_semiring
- \+ *lemma* set.up_le_up
- \+ *lemma* set.up_lt_up



## [2022-01-24 21:01:25](https://github.com/leanprover-community/mathlib/commit/9e799a0)
feat(algebra/pointwise): Scalar multiplication lemmas ([#11486](https://github.com/leanprover-community/mathlib/pull/11486))
This proves a bunch of lemmas about pointwise scalar multiplication of sets, moves `has_vsub` to `algebra.group.defs` and pointwise `vsub` lemmas to `algebra.pointwise`.
I'm also adding a few sections because having `{s t : set α}` is nice for multiplication but not for scalar multiplication.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \- *lemma* set.empty_vsub
- \- *lemma* set.finite.vadd
- \- *lemma* set.finite.vsub
- \- *lemma* set.mem_vsub
- \- *lemma* set.set_vadd_singleton
- \- *lemma* set.singleton_vsub
- \- *lemma* set.vadd_subset_vadd
- \- *lemma* set.vsub_empty
- \- *lemma* set.vsub_mem_vsub
- \- *lemma* set.vsub_self_mono
- \- *lemma* set.vsub_singleton
- \- *lemma* set.vsub_subset_iff
- \- *lemma* set.vsub_subset_vsub

Modified src/algebra/group/defs.lean


Modified src/algebra/pointwise.lean
- \+/\- *lemma* mem_inv_smul_set_iff₀
- \+/\- *lemma* mem_smul_set_iff_inv_smul_mem₀
- \+/\- *lemma* preimage_smul_inv₀
- \+/\- *lemma* preimage_smul₀
- \+ *lemma* set.Inter_mul_subset
- \+ *lemma* set.Inter_smul_subset
- \+ *lemma* set.Inter_vsub_subset
- \+ *lemma* set.Inter₂_mul_subset
- \+ *lemma* set.Inter₂_smul_subset
- \+ *lemma* set.Inter₂_vsub_subset
- \+/\- *lemma* set.Union_mul
- \+/\- *lemma* set.Union_mul_left_image
- \+/\- *lemma* set.Union_mul_right_image
- \+ *lemma* set.Union_smul
- \+ *lemma* set.Union_smul_left_image
- \+ *lemma* set.Union_smul_right_image
- \+ *lemma* set.Union_vsub
- \+ *lemma* set.Union_vsub_left_image
- \+ *lemma* set.Union_vsub_right_image
- \+ *lemma* set.Union₂_mul
- \+ *lemma* set.Union₂_smul
- \+ *lemma* set.Union₂_vsub
- \+/\- *lemma* set.empty_mul
- \+ *lemma* set.empty_smul
- \+ *lemma* set.empty_vsub
- \+ *lemma* set.finite.smul_set
- \+ *lemma* set.finite.vsub
- \+/\- *lemma* set.image2_mul
- \+/\- *lemma* set.image2_smul
- \+ *lemma* set.image2_vsub
- \+/\- *lemma* set.image_mul_left
- \+/\- *lemma* set.image_mul_prod
- \+/\- *lemma* set.image_mul_right'
- \+/\- *lemma* set.image_mul_right
- \+ *lemma* set.image_one
- \- *theorem* set.image_one
- \+/\- *lemma* set.image_smul
- \+/\- *lemma* set.image_smul_prod
- \+ *lemma* set.image_vsub_prod
- \+ *lemma* set.inter_mul_subset
- \+ *lemma* set.inter_smul_subset
- \+ *lemma* set.inter_vsub_subset
- \+/\- *lemma* set.mem_mul
- \+/\- *lemma* set.mem_one
- \+/\- *lemma* set.mem_smul
- \+/\- *lemma* set.mem_smul_of_mem
- \+/\- *lemma* set.mem_smul_set
- \+ *lemma* set.mem_vsub
- \+ *lemma* set.mul_Inter_subset
- \+ *lemma* set.mul_Inter₂_subset
- \+/\- *lemma* set.mul_Union
- \+ *lemma* set.mul_Union₂
- \+/\- *lemma* set.mul_empty
- \+ *lemma* set.mul_inter_subset
- \+/\- *lemma* set.mul_mem_mul
- \+/\- *lemma* set.mul_singleton
- \+/\- *lemma* set.mul_subset_mul
- \+/\- *lemma* set.mul_subset_mul_left
- \+/\- *lemma* set.mul_subset_mul_right
- \+/\- *lemma* set.mul_union
- \+ *lemma* set.mul_univ
- \+ *lemma* set.neg_smul_set
- \+/\- *lemma* set.one_mem_one
- \+ *lemma* set.one_nonempty
- \- *theorem* set.one_nonempty
- \+ *lemma* set.one_subset
- \- *theorem* set.one_subset
- \+/\- *lemma* set.preimage_mul_left_one
- \+/\- *lemma* set.preimage_mul_right_one'
- \+/\- *lemma* set.preimage_mul_right_one
- \+/\- *theorem* set.range_smul_range
- \+/\- *lemma* set.singleton_mul
- \+/\- *def* set.singleton_mul_hom
- \+/\- *lemma* set.singleton_mul_singleton
- \+/\- *lemma* set.singleton_one
- \+/\- *lemma* set.singleton_smul
- \+ *lemma* set.singleton_smul_singleton
- \+ *lemma* set.singleton_vsub
- \+ *lemma* set.singleton_vsub_singleton
- \+ *lemma* set.smul_Inter_subset
- \+ *lemma* set.smul_Inter₂_subset
- \+ *lemma* set.smul_Union
- \+ *lemma* set.smul_Union₂
- \+ *lemma* set.smul_empty
- \+ *lemma* set.smul_inter_subset
- \+ *lemma* set.smul_mem_smul
- \+/\- *lemma* set.smul_mem_smul_set
- \+ *lemma* set.smul_set_Inter_subset
- \+ *lemma* set.smul_set_Inter₂_subset
- \+ *lemma* set.smul_set_Union
- \+ *lemma* set.smul_set_Union₂
- \+/\- *lemma* set.smul_set_empty
- \+/\- *lemma* set.smul_set_inter_subset
- \+/\- *lemma* set.smul_set_mono
- \+ *lemma* set.smul_set_neg
- \+ *lemma* set.smul_set_singleton
- \+/\- *lemma* set.smul_set_union
- \+ *lemma* set.smul_set_univ
- \+/\- *lemma* set.smul_singleton
- \+ *lemma* set.smul_subset_iff
- \+ *lemma* set.smul_subset_smul
- \+ *lemma* set.smul_subset_smul_left
- \+ *lemma* set.smul_subset_smul_right
- \+ *lemma* set.smul_union
- \+ *lemma* set.smul_univ
- \+ *lemma* set.subset_mul_left
- \+ *lemma* set.subset_mul_right
- \+/\- *lemma* set.union_mul
- \+ *lemma* set.union_smul
- \+ *lemma* set.union_vsub
- \+ *lemma* set.univ_mul
- \+ *lemma* set.vsub_Inter_subset
- \+ *lemma* set.vsub_Inter₂_subset
- \+ *lemma* set.vsub_Union
- \+ *lemma* set.vsub_Union₂
- \+ *lemma* set.vsub_empty
- \+ *lemma* set.vsub_inter_subset
- \+ *lemma* set.vsub_mem_vsub
- \+ *lemma* set.vsub_self_mono
- \+ *lemma* set.vsub_singleton
- \+ *lemma* set.vsub_subset_iff
- \+ *lemma* set.vsub_subset_vsub
- \+ *lemma* set.vsub_subset_vsub_left
- \+ *lemma* set.vsub_subset_vsub_right
- \+ *lemma* set.vsub_union
- \+/\- *lemma* set_smul_subset_iff₀
- \+/\- *lemma* set_smul_subset_set_smul_iff₀
- \+/\- *lemma* smul_mem_smul_set_iff₀
- \+ *lemma* smul_set_univ₀
- \+ *lemma* smul_univ₀
- \+/\- *lemma* subset_set_smul_iff₀
- \+/\- *lemma* subsingleton_zero_smul_set
- \+ *lemma* zero_mem_smul_iff
- \+ *lemma* zero_mem_smul_set
- \+ *lemma* zero_mem_smul_set_iff
- \+/\- *lemma* zero_smul_set
- \+/\- *lemma* zero_smul_subset

Modified src/analysis/convex/star.lean




## [2022-01-24 20:18:07](https://github.com/leanprover-community/mathlib/commit/6aea8ac)
chore(probability_theory/stopping): fix names in documentation ([#11644](https://github.com/leanprover-community/mathlib/pull/11644))
#### Estimated changes
Modified src/probability_theory/stopping.lean




## [2022-01-24 18:04:16](https://github.com/leanprover-community/mathlib/commit/1bbed96)
doc(tactic/interactive): mention triv uses contradiction ([#11502](https://github.com/leanprover-community/mathlib/pull/11502))
Adding the fact that `triv` tries `contradiction` to the docstring for `triv`.
#### Estimated changes
Modified src/tactic/interactive.lean




## [2022-01-24 16:03:59](https://github.com/leanprover-community/mathlib/commit/eccd8dd)
feat(algebra/lie/nilpotent): generalise lower central series to start with given Lie submodule ([#11625](https://github.com/leanprover-community/mathlib/pull/11625))
The advantage of this approach is that we can regard the terms of the lower central series of a Lie submodule as Lie submodules of the enclosing Lie module.
In particular, this is useful when considering the lower central series of a Lie ideal.
#### Estimated changes
Modified src/algebra/lie/ideal_operations.lean
- \+ *lemma* lie_submodule.comap_bracket_eq
- \+ *lemma* lie_submodule.comap_map_eq
- \+ *lemma* lie_submodule.le_comap_map
- \+/\- *lemma* lie_submodule.map_bracket_eq
- \+ *lemma* lie_submodule.map_comap_eq
- \+ *lemma* lie_submodule.map_comap_incl
- \+ *lemma* lie_submodule.map_comap_le

Modified src/algebra/lie/nilpotent.lean
- \+/\- *def* lie_module.lower_central_series
- \+/\- *lemma* lie_module.lower_central_series_succ
- \+ *def* lie_submodule.lcs
- \+ *lemma* lie_submodule.lcs_le_self
- \+ *lemma* lie_submodule.lcs_succ
- \+ *lemma* lie_submodule.lcs_zero
- \+ *lemma* lie_submodule.lower_central_series_eq_lcs_comap
- \+ *lemma* lie_submodule.lower_central_series_map_eq_lcs

Modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_module_hom.ker_coe_submodule
- \+ *lemma* lie_module_hom.ker_eq_bot
- \+ *lemma* lie_submodule.coe_submodule_comap
- \+ *lemma* lie_submodule.comap_incl_self
- \+ *lemma* lie_submodule.incl_coe
- \+ *lemma* lie_submodule.ker_incl
- \+ *lemma* lie_submodule.range_incl



## [2022-01-24 16:03:56](https://github.com/leanprover-community/mathlib/commit/a631839)
feat(analysis/special_functions/pow): add nnreal variant of rpow_pos ([#11619](https://github.com/leanprover-community/mathlib/pull/11619))
This matches the lemma for ennreal.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* nnreal.rpow_pos



## [2022-01-24 16:03:55](https://github.com/leanprover-community/mathlib/commit/155c330)
feat(analysis/convex/{basic,function}): add lemmas, golf ([#11608](https://github.com/leanprover-community/mathlib/pull/11608))
* add `segment_subset_iff`, `open_segment_subset_iff`, use them to golf some proofs;
* add `mem_segment_iff_div`, `mem_open_segment_iff_div`, use the
  former in the proof of `convex_iff_div`;
* move the proof of `mpr` in `convex_on_iff_convex_epigraph` to a new
  lemma;
* prove that the strict epigraph of a convex function include the open
  segment provided that one of the endpoints is in the strong epigraph
  and the other is in the epigraph; use it in the proof of
  `convex_on.convex_strict_epigraph`.
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex.linear_image
- \+ *lemma* mem_open_segment_iff_div
- \+ *lemma* mem_segment_iff_div
- \+ *lemma* open_segment_subset_iff
- \+ *lemma* segment_subset_iff

Modified src/analysis/convex/function.lean
- \+ *lemma* concave_on.open_segment_subset_strict_hypograph
- \+ *lemma* concave_on_of_convex_hypograph
- \+ *lemma* convex_on.open_segment_subset_strict_epigraph
- \+ *lemma* convex_on_of_convex_epigraph

Modified src/analysis/convex/strict.lean




## [2022-01-24 16:03:53](https://github.com/leanprover-community/mathlib/commit/a52ce83)
feat(combinatorics/configuration): The order of a projective plane is at least 2 ([#11550](https://github.com/leanprover-community/mathlib/pull/11550))
This PR proves that the order of a projective plane is strictly larger than 1.
#### Estimated changes
Modified src/combinatorics/configuration.lean
- \+ *lemma* configuration.projective_plane.one_lt_order
- \+ *lemma* configuration.projective_plane.two_lt_line_count
- \+ *lemma* configuration.projective_plane.two_lt_point_count



## [2022-01-24 16:03:52](https://github.com/leanprover-community/mathlib/commit/9150268)
feat (algebraic_geometry): Constructions of fibred products of schemes ([#11450](https://github.com/leanprover-community/mathlib/pull/11450))
This is the first half of the PRs about constructing fibred products of schemes, where we
construct all the relevant schemes and morphisms but yet to show that they are actually
fibred products.
#### Estimated changes
Added src/algebraic_geometry/pullbacks.lean
- \+ *def* algebraic_geometry.Scheme.pullback.V
- \+ *lemma* algebraic_geometry.Scheme.pullback.cocycle
- \+ *lemma* algebraic_geometry.Scheme.pullback.cocycle_fst_fst_fst
- \+ *lemma* algebraic_geometry.Scheme.pullback.cocycle_fst_fst_snd
- \+ *lemma* algebraic_geometry.Scheme.pullback.cocycle_fst_snd
- \+ *lemma* algebraic_geometry.Scheme.pullback.cocycle_snd_fst_fst
- \+ *lemma* algebraic_geometry.Scheme.pullback.cocycle_snd_fst_snd
- \+ *lemma* algebraic_geometry.Scheme.pullback.cocycle_snd_snd
- \+ *abbreviation* algebraic_geometry.Scheme.pullback.fV
- \+ *def* algebraic_geometry.Scheme.pullback.glued_lift
- \+ *lemma* algebraic_geometry.Scheme.pullback.glued_lift_p1
- \+ *lemma* algebraic_geometry.Scheme.pullback.glued_lift_p2
- \+ *def* algebraic_geometry.Scheme.pullback.glued_lift_pullback_map
- \+ *lemma* algebraic_geometry.Scheme.pullback.glued_lift_pullback_map_fst
- \+ *lemma* algebraic_geometry.Scheme.pullback.glued_lift_pullback_map_snd
- \+ *def* algebraic_geometry.Scheme.pullback.gluing
- \+ *def* algebraic_geometry.Scheme.pullback.p1
- \+ *def* algebraic_geometry.Scheme.pullback.p2
- \+ *lemma* algebraic_geometry.Scheme.pullback.p_comm
- \+ *def* algebraic_geometry.Scheme.pullback.t'
- \+ *lemma* algebraic_geometry.Scheme.pullback.t'_fst_fst_fst
- \+ *lemma* algebraic_geometry.Scheme.pullback.t'_fst_fst_snd
- \+ *lemma* algebraic_geometry.Scheme.pullback.t'_fst_snd
- \+ *lemma* algebraic_geometry.Scheme.pullback.t'_snd_fst_fst
- \+ *lemma* algebraic_geometry.Scheme.pullback.t'_snd_fst_snd
- \+ *lemma* algebraic_geometry.Scheme.pullback.t'_snd_snd
- \+ *def* algebraic_geometry.Scheme.pullback.t
- \+ *lemma* algebraic_geometry.Scheme.pullback.t_fst_fst
- \+ *lemma* algebraic_geometry.Scheme.pullback.t_fst_snd
- \+ *lemma* algebraic_geometry.Scheme.pullback.t_id
- \+ *lemma* algebraic_geometry.Scheme.pullback.t_snd



## [2022-01-24 14:20:36](https://github.com/leanprover-community/mathlib/commit/4a6709b)
feat(data/{int,nat}/gcd): add `nat.gcd_greatest` ([#11611](https://github.com/leanprover-community/mathlib/pull/11611))
Add lemma characterising `gcd` in `ℕ`, counterpart of `int.gcd_greatest`.  Also add shorter proof of `int.gcd_greatest`.
#### Estimated changes
Modified src/data/int/gcd.lean


Modified src/data/nat/gcd.lean
- \+ *theorem* nat.gcd_greatest



## [2022-01-24 14:20:33](https://github.com/leanprover-community/mathlib/commit/bc2f73f)
feat(topology/uniform_space/uniform_convergence): Product of `tendsto_uniformly` ([#11562](https://github.com/leanprover-community/mathlib/pull/11562))
This PR adds lemmas `tendsto_uniformly_on.prod` and `tendsto_uniformly.prod`.
#### Estimated changes
Modified src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* tendsto_uniformly.prod
- \+ *lemma* tendsto_uniformly.prod_map
- \+ *lemma* tendsto_uniformly_on.prod
- \+ *lemma* tendsto_uniformly_on.prod_map



## [2022-01-24 12:47:20](https://github.com/leanprover-community/mathlib/commit/f99af7d)
chore(data/set/lattice): Generalize more `⋃`/`⋂` lemmas to dependent families ([#11516](https://github.com/leanprover-community/mathlib/pull/11516))
The "bounded union" and "bounded intersection" are both instances of nested `⋃`/`⋂`. But they only apply when the inner one runs over a predicate `p : ι → Prop`, and the resulting set couldn't depend on `p`. This generalizes to `κ : ι → Sort*` and allows dependence on `κ i`.
The lemmas are renamed from `bUnion`/`bInter` to `Union₂`/`Inter₂` to show that they are more general. Some generalizations lead to unification problems, so I've kept the `b` version around.
Some lemmas were missing between `⋃` and `⋂` or between `⋃`/`⋂` and nested `⋃`/`⋂`, so I'm adding them as well.
Renames
#### Estimated changes
Modified src/algebra/module/submodule_lattice.lean


Modified src/analysis/box_integral/partition/basic.lean
- \+/\- *lemma* box_integral.prepartition.Union_subset

Modified src/analysis/box_integral/partition/tagged.lean
- \+/\- *lemma* box_integral.tagged_prepartition.Union_subset

Modified src/analysis/convex/simplicial_complex/basic.lean


Modified src/analysis/normed_space/weak_dual.lean


Modified src/analysis/seminorm.lean


Modified src/data/set/accumulate.lean


Modified src/data/set/intervals/disjoint.lean


Modified src/data/set/lattice.lean
- \+/\- *lemma* set.Inter_congr
- \+ *lemma* set.Inter_congr_of_surjective
- \+ *lemma* set.Inter_mono'
- \+ *lemma* set.Inter_mono
- \- *lemma* set.Inter_subset_Inter2
- \- *lemma* set.Inter_subset_Inter
- \+ *lemma* set.Inter_subset_Inter₂
- \+/\- *lemma* set.Inter_subset_of_subset
- \+ *lemma* set.Inter₂_congr
- \+ *lemma* set.Inter₂_eq_empty_iff
- \+ *lemma* set.Inter₂_mono'
- \+ *lemma* set.Inter₂_mono
- \+ *lemma* set.Inter₂_subset
- \+/\- *lemma* set.Union_Inter_subset
- \+/\- *lemma* set.Union_congr
- \+ *lemma* set.Union_congr_of_surjective
- \+ *lemma* set.Union_mono'
- \+ *lemma* set.Union_mono
- \+/\- *lemma* set.Union_prod_const
- \+/\- *lemma* set.Union_range_eq_Union
- \+ *lemma* set.Union_set_of
- \+ *lemma* set.Union_subset
- \- *theorem* set.Union_subset
- \- *lemma* set.Union_subset_Union2
- \- *lemma* set.Union_subset_Union
- \+ *lemma* set.Union_subset_iff
- \- *theorem* set.Union_subset_iff
- \+ *lemma* set.Union₂_congr
- \+ *lemma* set.Union₂_eq_univ_iff
- \+ *lemma* set.Union₂_inter
- \+ *lemma* set.Union₂_mono'
- \+ *lemma* set.Union₂_mono
- \+ *lemma* set.Union₂_prod_const
- \+ *lemma* set.Union₂_subset
- \+ *lemma* set.Union₂_subset_Union
- \+ *lemma* set.Union₂_subset_iff
- \- *lemma* set.bInter_congr
- \- *lemma* set.bInter_eq_empty_iff
- \- *theorem* set.bInter_mono'
- \+ *lemma* set.bInter_mono
- \- *theorem* set.bInter_mono
- \- *lemma* set.bUnion_congr
- \- *lemma* set.bUnion_eq_univ_iff
- \- *theorem* set.bUnion_inter
- \+ *lemma* set.bUnion_mono
- \- *theorem* set.bUnion_mono
- \- *lemma* set.bUnion_prod_const
- \- *theorem* set.bUnion_subset
- \- *theorem* set.bUnion_subset_Union
- \- *theorem* set.bUnion_subset_bUnion
- \+ *lemma* set.compl_Inter₂
- \+ *lemma* set.compl_Union₂
- \- *theorem* set.compl_bInter
- \- *theorem* set.compl_bUnion
- \+ *lemma* set.image2_Inter_subset_left
- \+ *lemma* set.image2_Inter_subset_right
- \+ *lemma* set.image2_Inter₂_subset_left
- \+ *lemma* set.image2_Inter₂_subset_right
- \+ *lemma* set.image2_Union₂_left
- \+ *lemma* set.image2_Union₂_right
- \+ *lemma* set.image_Inter₂_subset
- \+ *lemma* set.image_Union₂
- \- *lemma* set.image_bInter_subset
- \- *lemma* set.image_bUnion
- \+ *lemma* set.inter_Union₂
- \- *theorem* set.inter_bUnion
- \+ *lemma* set.maps_to_Inter₂
- \+ *lemma* set.maps_to_Inter₂_Inter₂
- \+ *lemma* set.maps_to_Union₂
- \+ *lemma* set.maps_to_Union₂_Union₂
- \- *lemma* set.maps_to_bInter
- \- *lemma* set.maps_to_bInter_bInter
- \- *lemma* set.maps_to_bUnion
- \- *lemma* set.maps_to_bUnion_bUnion
- \+ *lemma* set.mem_Inter
- \- *theorem* set.mem_Inter
- \+ *lemma* set.mem_Inter_of_mem
- \- *theorem* set.mem_Inter_of_mem
- \+ *lemma* set.mem_Inter₂
- \- *theorem* set.mem_Inter₂
- \+ *lemma* set.mem_Inter₂_of_mem
- \+ *lemma* set.mem_Union
- \- *theorem* set.mem_Union
- \+ *lemma* set.mem_Union_of_mem
- \+ *lemma* set.mem_Union₂
- \- *theorem* set.mem_Union₂
- \+ *lemma* set.mem_Union₂_of_mem
- \+ *lemma* set.nonempty_Inter₂
- \- *theorem* set.nonempty_bInter
- \+/\- *lemma* set.preimage_Inter
- \+ *lemma* set.preimage_Inter₂
- \+ *lemma* set.preimage_Union
- \- *theorem* set.preimage_Union
- \+ *lemma* set.preimage_Union₂
- \- *lemma* set.preimage_bInter
- \- *theorem* set.preimage_bUnion
- \+/\- *lemma* set.prod_Union
- \+ *lemma* set.prod_Union₂
- \- *lemma* set.prod_bUnion
- \+ *lemma* set.subset_Inter_iff
- \- *theorem* set.subset_Inter_iff
- \+ *lemma* set.subset_Inter₂
- \+ *lemma* set.subset_Inter₂_iff
- \+ *lemma* set.subset_Union_of_subset
- \+ *lemma* set.subset_Union₂
- \- *theorem* set.subset_bInter
- \- *theorem* set.subset_subset_Union
- \+ *lemma* set.surj_on_Union₂
- \+ *lemma* set.surj_on_Union₂_Union₂
- \- *lemma* set.surj_on_bUnion
- \- *lemma* set.surj_on_bUnion_bUnion
- \+/\- *lemma* set.union_distrib_Inter_left
- \+/\- *lemma* set.union_distrib_Inter_right
- \+ *lemma* set.union_distrib_Inter₂_left
- \+ *lemma* set.union_distrib_Inter₂_right
- \- *lemma* set.union_distrib_bInter_left
- \- *lemma* set.union_distrib_bInter_right

Modified src/data/set/pairwise.lean


Modified src/deprecated/subgroup.lean


Modified src/dynamics/ergodic/conservative.lean


Modified src/dynamics/omega_limit.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/linear_algebra/affine_space/affine_subspace.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/covering/besicovitch.lean


Modified src/measure_theory/covering/besicovitch_vector_space.lean


Modified src/measure_theory/covering/vitali.lean


Modified src/measure_theory/function/uniform_integrable.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measurable_space_def.lean


Modified src/measure_theory/measure/haar.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/measure_theory/measure/regular.lean


Modified src/measure_theory/measure/stieltjes.lean


Modified src/number_theory/liouville/residual.lean


Modified src/order/compactly_generated.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean


Modified src/order/filter/pi.lean


Modified src/ring_theory/algebraic_independent.lean


Modified src/ring_theory/hahn_series.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/tactic/monotonicity/lemmas.lean


Modified src/topology/G_delta.lean


Modified src/topology/algebra/group.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean
- \+ *lemma* interior_Inter₂_subset
- \- *lemma* interior_bInter_subset

Modified src/topology/connected.lean


Modified src/topology/continuous_on.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/hausdorff_dimension.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/shrinking_lemma.lean


Modified src/topology/separation.lean


Modified src/topology/sequences.lean


Modified src/topology/shrinking_lemma.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/compact_convergence.lean




## [2022-01-24 12:18:54](https://github.com/leanprover-community/mathlib/commit/ee36571)
feat(algebra/lie/cartan_subalgebra): add self-normalizing characterisation for Lie subalgebra ([#11598](https://github.com/leanprover-community/mathlib/pull/11598))
#### Estimated changes
Modified src/algebra/lie/cartan_subalgebra.lean
- \+ *lemma* lie_subalgebra.mem_normalizer_iff'
- \+ *lemma* lie_subalgebra.normalizer_eq_self_iff

Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* lie_subalgebra.neg_mem_iff

Modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_submodule.mk_eq_zero
- \+ *lemma* lie_submodule.to_submodule_eq_coe



## [2022-01-24 11:34:45](https://github.com/leanprover-community/mathlib/commit/dac4f40)
feat(analysis/normed_space/linear_isometry): `to_linear_equiv_trans` ([#11628](https://github.com/leanprover-community/mathlib/pull/11628))
Add a lemma relating `trans` for `linear_isometry_equiv` and
`linear_equiv`.
#### Estimated changes
Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry_equiv.to_linear_equiv_trans



## [2022-01-24 11:34:44](https://github.com/leanprover-community/mathlib/commit/ed90301)
feat(group_theory/commuting_probability): Commuting probability inequalities ([#11564](https://github.com/leanprover-community/mathlib/pull/11564))
This PR adds some inequalities for the commuting probability.
#### Estimated changes
Modified src/group_theory/commuting_probability.lean
- \+ *lemma* inv_card_commutator_le_comm_prob
- \+ *lemma* subgroup.comm_prob_quotient_le
- \+ *lemma* subgroup.comm_prob_subgroup_le



## [2022-01-24 10:02:38](https://github.com/leanprover-community/mathlib/commit/9ef7f6b)
feat(linear_algebra/orientation): `eq_neg_iff_eq_neg` ([#11629](https://github.com/leanprover-community/mathlib/pull/11629))
Add two more `module.ray` lemmas about negation.
#### Estimated changes
Modified src/linear_algebra/orientation.lean
- \+ *lemma* module.ray.neg_involutive



## [2022-01-24 10:02:37](https://github.com/leanprover-community/mathlib/commit/7ddb9a3)
refactor(order/ideal): Generalize definition and lemmas ([#11421](https://github.com/leanprover-community/mathlib/pull/11421))
* Generalize the `order_top` instance to `[nonempty P] [is_directed P (≤)]`.
* Delete `order.ideal.ideal_inter_nonempty` in favor of the equivalent condition `is_directed P (swap (≤))`.
* Delete `order.ideal.sup`/`order.ideal.inf` in favor of a direct instance declaration.
* Generalize defs/lemmas from `preorder` to `has_le` or `partial_order` to `preorder`.
* Two more `is_directed` lemmas and instances for `order_bot` and `order_top`.
#### Estimated changes
Modified src/order/atoms.lean
- \+/\- *def* is_atom
- \+/\- *def* is_coatom

Modified src/order/directed.lean
- \+ *lemma* directed_id_iff
- \- *lemma* directed_id_iff_is_directed
- \+ *lemma* directed_on_univ
- \+ *lemma* directed_on_univ_iff

Modified src/order/ideal.lean
- \+/\- *lemma* is_coatom.is_maximal
- \+/\- *lemma* is_coatom.is_proper
- \+/\- *lemma* order.ideal.bot_mem
- \+ *lemma* order.ideal.coe_inj
- \+ *lemma* order.ideal.coe_injective
- \+/\- *lemma* order.ideal.coe_top
- \+/\- *lemma* order.ideal.eq_sup_of_le_sup
- \- *lemma* order.ideal.ext'_iff
- \+/\- *lemma* order.ideal.ext
- \+ *lemma* order.ideal.ext_iff
- \- *lemma* order.ideal.ext_set_eq
- \- *def* order.ideal.inf
- \+/\- *lemma* order.ideal.inter_nonempty
- \- *lemma* order.ideal.is_ideal
- \+/\- *lemma* order.ideal.is_maximal.is_coatom'
- \+/\- *lemma* order.ideal.is_maximal.is_coatom
- \+/\- *lemma* order.ideal.is_maximal_iff_is_coatom
- \+/\- *lemma* order.ideal.is_proper.ne_top
- \+/\- *lemma* order.ideal.is_proper.top_not_mem
- \+/\- *lemma* order.ideal.is_proper_iff_ne_top
- \+/\- *lemma* order.ideal.is_proper_of_ne_top
- \+/\- *lemma* order.ideal.mem_inf
- \+/\- *lemma* order.ideal.mem_principal
- \+/\- *lemma* order.ideal.mem_sup
- \- *def* order.ideal.sup
- \- *lemma* order.ideal.sup_le
- \- *lemma* order.ideal.top_of_mem_top
- \+ *lemma* order.ideal.top_of_top_mem
- \+/\- *structure* order.ideal
- \+/\- *def* order.is_ideal.to_ideal
- \+/\- *structure* order.is_ideal
- \+/\- *lemma* order.mem_ideal_of_cofinals



## [2022-01-24 10:02:36](https://github.com/leanprover-community/mathlib/commit/9becbc7)
feat(algebra/order/rearrangement) : Rearrangement Inequality ([#10861](https://github.com/leanprover-community/mathlib/pull/10861))
A range of variants of the rearrangement inequality.
This is stated with scalar multiplication of a linear ring over an additive linear group, rather than having everything be in a linear ring. We couldn't find general statements of the rearrangement inequality in the literature, but this very much seems like an improvement.
#### Estimated changes
Added src/algebra/order/rearrangement.lean
- \+ *lemma* antivary.sum_mul_le_sum_comp_perm_mul
- \+ *lemma* antivary.sum_mul_le_sum_mul_comp_perm
- \+ *lemma* antivary.sum_smul_le_sum_comp_perm_smul
- \+ *lemma* antivary.sum_smul_le_sum_smul_comp_perm
- \+ *lemma* antivary_on.sum_mul_le_sum_comp_perm_mul
- \+ *lemma* antivary_on.sum_mul_le_sum_mul_comp_perm
- \+ *lemma* antivary_on.sum_smul_le_sum_comp_perm_smul
- \+ *lemma* antivary_on.sum_smul_le_sum_smul_comp_perm
- \+ *lemma* monovary.sum_comp_perm_mul_le_sum_mul
- \+ *lemma* monovary.sum_comp_perm_smul_le_sum_smul
- \+ *lemma* monovary.sum_mul_comp_perm_le_sum_mul
- \+ *lemma* monovary.sum_smul_comp_perm_le_sum_smul
- \+ *lemma* monovary_on.sum_comp_perm_mul_le_sum_mul
- \+ *lemma* monovary_on.sum_comp_perm_smul_le_sum_smul
- \+ *lemma* monovary_on.sum_mul_comp_perm_le_sum_mul
- \+ *lemma* monovary_on.sum_smul_comp_perm_le_sum_smul

Modified src/order/monovary.lean




## [2022-01-24 07:24:57](https://github.com/leanprover-community/mathlib/commit/8c64be0)
chore(category_theory/abelian): Moved more stuff into `pseudoelement` locale ([#11621](https://github.com/leanprover-community/mathlib/pull/11621))
The `ext` lemma triggers unwantedly in lots of places.
#### Estimated changes
Modified src/category_theory/abelian/diagram_lemmas/four.lean


Modified src/category_theory/abelian/pseudoelements.lean
- \+/\- *theorem* category_theory.abelian.pseudoelement.zero_morphism_ext'
- \+/\- *theorem* category_theory.abelian.pseudoelement.zero_morphism_ext



## [2022-01-24 05:54:29](https://github.com/leanprover-community/mathlib/commit/8f73b07)
feat(set_theory/surreal/dyadic): define add_monoid_hom structure on dyadic map ([#11052](https://github.com/leanprover-community/mathlib/pull/11052))
The proof is mechanical and mostly requires unraveling definitions.
The above map cannot be extended to ring morphism as so far there's not multiplication structure on surreal numbers.
#### Estimated changes
Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* submonoid.log_mul
- \+/\- *theorem* submonoid.log_pow_eq_self
- \+ *lemma* submonoid.pow_apply

Modified src/ring_theory/localization.lean
- \+ *lemma* localization.lift_on_zero

Modified src/set_theory/surreal/dyadic.lean
- \+/\- *def* surreal.dyadic_map
- \+ *lemma* surreal.dyadic_map_apply
- \+ *lemma* surreal.dyadic_map_apply_pow



## [2022-01-24 03:52:26](https://github.com/leanprover-community/mathlib/commit/32cd278)
feat(analysis/asymptotics): add a few lemmas ([#11623](https://github.com/leanprover-community/mathlib/pull/11623))
* rename `is_o.tendsto_0` to `is_o.tendsto_div_nhds_zero`, add `is_o.tendsto_inv_smul_nhds_zero`;
* add `is_o_const_left` and `filter.is_bounded_under.is_o_sub_self_inv`.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotic_equivalent.lean


Modified src/analysis/asymptotics/asymptotics.lean
- \- *theorem* asymptotics.is_o.tendsto_0
- \+ *theorem* asymptotics.is_o.tendsto_div_nhds_zero
- \+ *theorem* asymptotics.is_o.tendsto_inv_smul_nhds_zero
- \+ *lemma* asymptotics.is_o_const_left
- \+ *lemma* asymptotics.is_o_const_left_of_ne
- \+/\- *theorem* filter.is_bounded_under.is_O_const

Modified src/analysis/asymptotics/specific_asymptotics.lean
- \+ *lemma* filter.is_bounded_under.is_o_sub_self_inv

Modified src/analysis/normed/group/basic.lean
- \+ *lemma* tendsto_norm_sub_self_punctured_nhds

Modified src/analysis/normed_space/units.lean


Modified src/analysis/specific_limits.lean




## [2022-01-24 02:18:18](https://github.com/leanprover-community/mathlib/commit/095c46c)
feat(linear_algebra/basis): `reindex_refl` ([#11626](https://github.com/leanprover-community/mathlib/pull/11626))
Add a `simp` lemma about applying `basis.reindex` with `equiv.refl`.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *lemma* basis.reindex_refl



## [2022-01-23 15:43:45](https://github.com/leanprover-community/mathlib/commit/5449ffa)
feat(data/nat/prime): factors of non-prime powers ([#11546](https://github.com/leanprover-community/mathlib/pull/11546))
Adds the result `pow_factors_to_finset`, fills in `factors_mul_to_finset_of_coprime` for the sake of completion, and adjusts statements to take `ne_zero` rather than pos assumptions.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* list.to_finset.ext
- \+ *lemma* list.to_finset.ext_iff

Modified src/data/nat/factorization.lean
- \+ *lemma* nat.factorization_mul_support
- \- *lemma* nat.factorization_mul_support_of_pos

Modified src/data/nat/prime.lean
- \+/\- *lemma* nat.coprime_factors_disjoint
- \- *lemma* nat.factors_mul_of_coprime
- \- *lemma* nat.factors_mul_of_pos
- \+ *lemma* nat.factors_mul_to_finset
- \+ *lemma* nat.factors_mul_to_finset_of_coprime
- \+/\- *lemma* nat.mem_factors
- \+ *lemma* nat.mem_factors_mul
- \+ *lemma* nat.mem_factors_mul_of_coprime
- \- *lemma* nat.mem_factors_mul_of_pos
- \+ *lemma* nat.pow_factors_to_finset
- \+ *lemma* nat.pow_succ_factors_to_finset
- \+/\- *lemma* nat.prime_pow_prime_divisor

Modified src/group_theory/p_group.lean




## [2022-01-23 13:55:13](https://github.com/leanprover-community/mathlib/commit/59ef8ce)
feat(measure_theory/measure): assorted lemmas ([#11612](https://github.com/leanprover-community/mathlib/pull/11612))
* add `ae_disjoint_compl_left/right`;
* deduce `restrict_to_measurable` and `restrict_to_measurable_of_sigma_finite` from @sgouezel 's lemmas about measures of intersections;
* add `ae_restrict_mem₀`;
* add `ae_eq_univ`.
#### Estimated changes
Modified src/measure_theory/measure/ae_disjoint.lean
- \+ *lemma* measure_theory.ae_disjoint_compl_left
- \+ *lemma* measure_theory.ae_disjoint_compl_right

Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.ae_restrict_iff'
- \+/\- *lemma* measure_theory.ae_restrict_mem
- \+ *lemma* measure_theory.ae_restrict_mem₀
- \+ *lemma* measure_theory.measure.restrict_to_measurable
- \+ *lemma* measure_theory.measure.restrict_to_measurable_of_sigma_finite

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* measure_theory.ae_eq_univ



## [2022-01-23 10:59:21](https://github.com/leanprover-community/mathlib/commit/d0f392e)
feat(analysis/calculus/inverse): a map which approximates a linear map on a set admits a nice global extension ([#11568](https://github.com/leanprover-community/mathlib/pull/11568))
And several other results on maps that are well approximated by linear maps on some subset of the space (not necessarily open).
#### Estimated changes
Modified src/analysis/calculus/inverse.lean
- \+ *lemma* approximates_linear_on.approximates_linear_on_iff_lipschitz_on_with
- \+ *lemma* approximates_linear_on.exists_homeomorph_extension
- \+/\- *lemma* approximates_linear_on.open_image
- \+ *def* approximates_linear_on.to_homeomorph
- \+ *lemma* approximates_linear_on.to_inv
- \+ *lemma* approximates_linear_on_empty

Modified src/analysis/normed_space/operator_norm.lean
- \+ *theorem* continuous_linear_map.antilipschitz_of_bound
- \+ *lemma* continuous_linear_map.bound_of_antilipschitz

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.Ici_mem_at_top

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.forall_of_forall_mem_ball
- \+ *lemma* metric.forall_of_forall_mem_closed_ball



## [2022-01-23 07:44:41](https://github.com/leanprover-community/mathlib/commit/b1ad301)
feat(number_theory/cyclotomic/basic): add missing lemmas ([#11451](https://github.com/leanprover-community/mathlib/pull/11451))
We add some missing lemmas about cyclotomic extensions.
From flt-regular.
#### Estimated changes
Modified src/number_theory/cyclotomic/basic.lean
- \+ *lemma* cyclotomic_ring.eq_adjoin_primitive_root
- \+ *lemma* is_cyclotomic_extension.adjoin_primitive_root_eq_top
- \+ *lemma* is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic



## [2022-01-23 03:26:11](https://github.com/leanprover-community/mathlib/commit/9a517cf)
chore(analysis/normed/group/completion): fix attribution ([#11614](https://github.com/leanprover-community/mathlib/pull/11614))
This code was written by @jcommelin in [#6189](https://github.com/leanprover-community/mathlib/pull/6189) but somehow acquired my name during a refactor ([#10055](https://github.com/leanprover-community/mathlib/pull/10055)).  I don't think I've ever touched it!
#### Estimated changes
Modified src/analysis/normed/group/completion.lean




## [2022-01-23 02:45:45](https://github.com/leanprover-community/mathlib/commit/2babfeb)
chore(data/complex/is_R_or_C): squeeze simps ([#11251](https://github.com/leanprover-community/mathlib/pull/11251))
This PR squeezes most of the simps in `is_R_or_C`, and updates the module docstring.
#### Estimated changes
Modified src/analysis/normed_space/is_R_or_C.lean
- \+/\- *lemma* is_R_or_C.norm_coe_norm

Modified src/data/complex/is_R_or_C.lean
- \+/\- *lemma* is_R_or_C.I_im'
- \+/\- *lemma* is_R_or_C.I_im
- \+/\- *lemma* is_R_or_C.I_mul_re
- \+/\- *lemma* is_R_or_C.I_re
- \+/\- *lemma* is_R_or_C.I_to_real
- \+/\- *lemma* is_R_or_C.abs_abs
- \+/\- *lemma* is_R_or_C.abs_cast_nat
- \+/\- *lemma* is_R_or_C.abs_conj
- \+/\- *theorem* is_R_or_C.abs_div
- \+/\- *lemma* is_R_or_C.abs_eq_zero
- \+/\- *theorem* is_R_or_C.abs_inv
- \+/\- *lemma* is_R_or_C.abs_mul
- \+/\- *lemma* is_R_or_C.abs_neg
- \+/\- *lemma* is_R_or_C.abs_one
- \+/\- *lemma* is_R_or_C.abs_pos
- \+/\- *lemma* is_R_or_C.abs_to_real
- \+/\- *lemma* is_R_or_C.abs_two
- \+/\- *lemma* is_R_or_C.abs_zero
- \+/\- *lemma* is_R_or_C.bit0_im
- \+/\- *lemma* is_R_or_C.bit0_re
- \+/\- *lemma* is_R_or_C.bit1_im
- \+/\- *lemma* is_R_or_C.bit1_re
- \+/\- *lemma* is_R_or_C.conj_I
- \+/\- *lemma* is_R_or_C.conj_ae_coe
- \+/\- *lemma* is_R_or_C.conj_bit0
- \+/\- *lemma* is_R_or_C.conj_bit1
- \+/\- *lemma* is_R_or_C.conj_cle_apply
- \+/\- *lemma* is_R_or_C.conj_cle_coe
- \+/\- *lemma* is_R_or_C.conj_cle_norm
- \+/\- *lemma* is_R_or_C.conj_eq_re_sub_im
- \+/\- *lemma* is_R_or_C.conj_im
- \+/\- *lemma* is_R_or_C.conj_lie_apply
- \+/\- *lemma* is_R_or_C.conj_neg_I
- \+/\- *lemma* is_R_or_C.conj_of_real
- \+/\- *lemma* is_R_or_C.conj_re
- \+/\- *lemma* is_R_or_C.conj_smul
- \+/\- *lemma* is_R_or_C.conj_to_real
- \+/\- *lemma* is_R_or_C.div_I
- \+/\- *lemma* is_R_or_C.im_clm_apply
- \+/\- *lemma* is_R_or_C.im_clm_coe
- \+/\- *lemma* is_R_or_C.im_lm_coe
- \+/\- *lemma* is_R_or_C.im_to_real
- \+/\- *lemma* is_R_or_C.int_cast_im
- \+/\- *lemma* is_R_or_C.int_cast_re
- \+/\- *lemma* is_R_or_C.inv_I
- \+/\- *lemma* is_R_or_C.inv_im
- \+/\- *lemma* is_R_or_C.inv_re
- \+/\- *lemma* is_R_or_C.mul_im
- \+/\- *lemma* is_R_or_C.mul_re
- \+/\- *lemma* is_R_or_C.nat_cast_im
- \+/\- *lemma* is_R_or_C.nat_cast_re
- \+/\- *lemma* is_R_or_C.norm_conj
- \+/\- *lemma* is_R_or_C.norm_eq_abs
- \+/\- *lemma* is_R_or_C.norm_sq_conj
- \+/\- *lemma* is_R_or_C.norm_sq_div
- \+/\- *lemma* is_R_or_C.norm_sq_eq_zero
- \+/\- *lemma* is_R_or_C.norm_sq_inv
- \+/\- *lemma* is_R_or_C.norm_sq_mul
- \+/\- *lemma* is_R_or_C.norm_sq_neg
- \+/\- *lemma* is_R_or_C.norm_sq_of_real
- \+/\- *lemma* is_R_or_C.norm_sq_one
- \+/\- *lemma* is_R_or_C.norm_sq_pos
- \+/\- *lemma* is_R_or_C.norm_sq_sub
- \+/\- *lemma* is_R_or_C.norm_sq_to_real
- \+/\- *lemma* is_R_or_C.norm_sq_zero
- \+/\- *lemma* is_R_or_C.of_real_add
- \+/\- *lemma* is_R_or_C.of_real_am_coe
- \+/\- *lemma* is_R_or_C.of_real_bit0
- \+/\- *lemma* is_R_or_C.of_real_bit1
- \+/\- *lemma* is_R_or_C.of_real_clm_apply
- \+/\- *lemma* is_R_or_C.of_real_clm_coe
- \+/\- *lemma* is_R_or_C.of_real_clm_norm
- \+/\- *lemma* is_R_or_C.of_real_div
- \+/\- *theorem* is_R_or_C.of_real_eq_zero
- \+/\- *lemma* is_R_or_C.of_real_finsupp_prod
- \+/\- *lemma* is_R_or_C.of_real_finsupp_sum
- \+/\- *lemma* is_R_or_C.of_real_im
- \+/\- *theorem* is_R_or_C.of_real_int_cast
- \+/\- *lemma* is_R_or_C.of_real_inv
- \+/\- *lemma* is_R_or_C.of_real_li_apply
- \+/\- *lemma* is_R_or_C.of_real_mul
- \+/\- *lemma* is_R_or_C.of_real_mul_im
- \+/\- *lemma* is_R_or_C.of_real_mul_re
- \+/\- *theorem* is_R_or_C.of_real_nat_cast
- \+/\- *lemma* is_R_or_C.of_real_neg
- \+/\- *lemma* is_R_or_C.of_real_one
- \+/\- *lemma* is_R_or_C.of_real_pow
- \+/\- *lemma* is_R_or_C.of_real_prod
- \+/\- *theorem* is_R_or_C.of_real_rat_cast
- \+/\- *lemma* is_R_or_C.of_real_re
- \+/\- *lemma* is_R_or_C.of_real_smul
- \+/\- *lemma* is_R_or_C.of_real_sub
- \+/\- *lemma* is_R_or_C.of_real_sum
- \+/\- *lemma* is_R_or_C.of_real_zero
- \+/\- *lemma* is_R_or_C.of_real_zpow
- \+/\- *lemma* is_R_or_C.one_im
- \+/\- *lemma* is_R_or_C.one_re
- \+/\- *lemma* is_R_or_C.rat_cast_im
- \+/\- *lemma* is_R_or_C.rat_cast_re
- \+/\- *lemma* is_R_or_C.re_add_im
- \+/\- *lemma* is_R_or_C.re_clm_apply
- \+/\- *lemma* is_R_or_C.re_clm_coe
- \+/\- *lemma* is_R_or_C.re_clm_norm
- \+/\- *lemma* is_R_or_C.re_lm_coe
- \+/\- *lemma* is_R_or_C.re_to_real
- \+/\- *lemma* is_R_or_C.smul_im
- \+/\- *lemma* is_R_or_C.smul_re
- \+/\- *lemma* is_R_or_C.zero_re'



## [2022-01-22 23:39:48](https://github.com/leanprover-community/mathlib/commit/84dbe7b)
feat(measure_theory/covering): Lebesgue density points ([#11554](https://github.com/leanprover-community/mathlib/pull/11554))
We show in the general context of differentiation of measures that `μ (s ∩ a) / μ a` converges, when `a` shrinks towards a point `x`, to `1` for almost every `x` in `s`, and to `0` for almost every point outside of `s`. In other words, almost every point of `s` is a Lebesgue density points of `s`. Of course, this requires assumptions on allowed sets `a`. We state this in the general context of Vitali families. We also give easier to use versions in spaces with the Besicovitch property (e.g., final dimensional real vector spaces), where one can take for `a` the closed balls centered at `x`.
#### Estimated changes
Modified src/measure_theory/covering/besicovitch.lean
- \+ *lemma* besicovitch.ae_tendsto_measure_inter_div
- \+ *lemma* besicovitch.ae_tendsto_measure_inter_div_of_measurable_set
- \+ *lemma* besicovitch.ae_tendsto_rn_deriv
- \+/\- *theorem* besicovitch.exists_disjoint_closed_ball_covering_ae
- \+/\- *theorem* besicovitch.exists_disjoint_closed_ball_covering_ae_aux
- \+ *lemma* besicovitch.tendsto_filter_at

Modified src/measure_theory/covering/differentiation.lean
- \+ *lemma* vitali_family.ae_tendsto_measure_inter_div
- \+ *lemma* vitali_family.ae_tendsto_measure_inter_div_of_measurable_set

Modified src/measure_theory/covering/vitali_family.lean
- \+ *lemma* vitali_family.eventually_filter_at_measurable_set

Modified src/measure_theory/decomposition/lebesgue.lean
- \+ *theorem* measure_theory.measure.rn_deriv_restrict

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.with_density_indicator_one



## [2022-01-22 22:28:56](https://github.com/leanprover-community/mathlib/commit/a196f9b)
chore(measure_theory/probability_mass_function): Move pmf monad operations into a seperate file ([#11579](https://github.com/leanprover-community/mathlib/pull/11579))
This PR moves the `pure`, `bind`, and `bind_on_support` operations on `pmf` into a new `probability_mass_function/monad.lean` file.
#### Estimated changes
Modified src/measure_theory/probability_mass_function/basic.lean
- \- *def* pmf.bind
- \- *lemma* pmf.bind_apply
- \- *lemma* pmf.bind_bind
- \- *lemma* pmf.bind_comm
- \- *lemma* pmf.bind_pure
- \- *lemma* pmf.coe_bind_apply
- \- *lemma* pmf.mem_support_bind_iff
- \- *lemma* pmf.mem_support_pure_iff:
- \- *def* pmf.pure
- \- *lemma* pmf.pure_apply
- \- *lemma* pmf.pure_bind
- \- *lemma* pmf.support_bind
- \- *lemma* pmf.support_pure

Modified src/measure_theory/probability_mass_function/constructions.lean
- \- *def* pmf.bind_on_support
- \- *lemma* pmf.bind_on_support_apply
- \- *lemma* pmf.bind_on_support_bind_on_support
- \- *lemma* pmf.bind_on_support_comm
- \- *lemma* pmf.bind_on_support_eq_bind
- \- *lemma* pmf.bind_on_support_eq_zero_iff
- \- *lemma* pmf.bind_on_support_pure
- \- *lemma* pmf.coe_bind_on_support_apply
- \- *lemma* pmf.mem_support_bind_on_support_iff
- \- *lemma* pmf.pure_bind_on_support
- \- *lemma* pmf.support_bind_on_support

Added src/measure_theory/probability_mass_function/monad.lean
- \+ *def* pmf.bind
- \+ *lemma* pmf.bind_apply
- \+ *lemma* pmf.bind_bind
- \+ *lemma* pmf.bind_comm
- \+ *def* pmf.bind_on_support
- \+ *lemma* pmf.bind_on_support_apply
- \+ *lemma* pmf.bind_on_support_bind_on_support
- \+ *lemma* pmf.bind_on_support_comm
- \+ *lemma* pmf.bind_on_support_eq_bind
- \+ *lemma* pmf.bind_on_support_eq_zero_iff
- \+ *lemma* pmf.bind_on_support_pure
- \+ *lemma* pmf.bind_pure
- \+ *lemma* pmf.coe_bind_apply
- \+ *lemma* pmf.coe_bind_on_support_apply
- \+ *lemma* pmf.mem_support_bind_iff
- \+ *lemma* pmf.mem_support_bind_on_support_iff
- \+ *lemma* pmf.mem_support_pure_iff:
- \+ *def* pmf.pure
- \+ *lemma* pmf.pure_apply
- \+ *lemma* pmf.pure_bind
- \+ *lemma* pmf.pure_bind_on_support
- \+ *lemma* pmf.support_bind
- \+ *lemma* pmf.support_bind_on_support
- \+ *lemma* pmf.support_pure



## [2022-01-22 22:28:55](https://github.com/leanprover-community/mathlib/commit/31db25b)
feat(topology/instances/ennreal): continuity of subtraction on ennreal ([#11527](https://github.com/leanprover-community/mathlib/pull/11527))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.mul_inv

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.inv_lt_inv
- \+ *lemma* nnreal.inv_lt_inv_iff

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.tendsto_sub



## [2022-01-22 20:53:55](https://github.com/leanprover-community/mathlib/commit/159d9ac)
split(order/max): Split off `order.basic` ([#11603](https://github.com/leanprover-community/mathlib/pull/11603))
This moves `is_bot`, `is_top`, `no_min_order`, `no_max_order` to a new file `order.max`.
#### Estimated changes
Modified src/order/basic.lean
- \- *lemma* exists_gt
- \- *lemma* exists_lt
- \- *lemma* is_bot.unique
- \- *def* is_bot
- \- *lemma* is_bot_or_exists_lt
- \- *lemma* is_top.unique
- \- *def* is_top
- \- *lemma* is_top_or_exists_gt
- \- *lemma* not_is_bot
- \- *lemma* not_is_top

Modified src/order/bounded_order.lean


Added src/order/max.lean
- \+ *lemma* is_bot.to_dual
- \+ *lemma* is_bot.unique
- \+ *def* is_bot
- \+ *lemma* is_bot_or_exists_lt
- \+ *lemma* is_top.to_dual
- \+ *lemma* is_top.unique
- \+ *def* is_top
- \+ *lemma* is_top_or_exists_gt
- \+ *lemma* not_is_bot
- \+ *lemma* not_is_top

Modified src/order/order_dual.lean
- \- *lemma* is_bot.to_dual
- \- *lemma* is_top.to_dual



## [2022-01-22 20:00:08](https://github.com/leanprover-community/mathlib/commit/5080d64)
feat(topology): add a few lemmas ([#11607](https://github.com/leanprover-community/mathlib/pull/11607))
* add `homeomorph.preimage_interior`, `homeomorph.image_interior`,
  reorder lemmas;
* add `is_open.smul₀` and `interior_smul₀`.
#### Estimated changes
Modified src/topology/algebra/mul_action.lean
- \+ *lemma* interior_smul₀
- \+ *lemma* is_open.smul₀

Modified src/topology/homeomorph.lean
- \+ *lemma* homeomorph.image_interior
- \+ *lemma* homeomorph.preimage_interior



## [2022-01-22 18:38:06](https://github.com/leanprover-community/mathlib/commit/bd3b892)
move(order/hom/order): Move from `order.hom.lattice` ([#11601](https://github.com/leanprover-community/mathlib/pull/11601))
Rename `order.hom.lattice` into `order.hom.order` to make space for lattice homomorphisms, as opposed to the lattice of order homomorphisms.
#### Estimated changes
Modified src/order/fixed_points.lean


Renamed src/order/hom/lattice.lean to src/order/hom/order.lean


Modified src/order/omega_complete_partial_order.lean




## [2022-01-22 18:38:05](https://github.com/leanprover-community/mathlib/commit/206b56e)
doc(group_theory.quotient_group): Fix typos in main statement list ([#11581](https://github.com/leanprover-community/mathlib/pull/11581))
This now matches the docstring for the declaration in question.
#### Estimated changes
Modified src/group_theory/quotient_group.lean




## [2022-01-22 18:38:03](https://github.com/leanprover-community/mathlib/commit/155cf1d)
feat(group_theory/abelianization): add mul_equiv.abelianization_congr ([#11466](https://github.com/leanprover-community/mathlib/pull/11466))
#### Estimated changes
Modified src/group_theory/abelianization.lean
- \+ *lemma* abelianization.lift_of
- \+ *def* abelianization.map
- \+ *lemma* abelianization.map_comp
- \+ *lemma* abelianization.map_id
- \+ *lemma* abelianization.map_map_apply
- \+ *lemma* abelianization.map_of
- \+ *lemma* abelianization.mk_eq_of
- \+ *lemma* abelianization_congr_of
- \+ *lemma* abelianization_congr_refl
- \+ *lemma* abelianization_congr_symm
- \+ *lemma* abelianization_congr_trans
- \+ *def* mul_equiv.abelianization_congr



## [2022-01-22 18:05:24](https://github.com/leanprover-community/mathlib/commit/7ba08d3)
fix(category_theory/triangulated): Fix definition of pretriangulated ([#11596](https://github.com/leanprover-community/mathlib/pull/11596))
The original definition unfolds to `(T₁ : triangle C) (T₁ ∈ distinguished_triangles) (T₂ : triangle C) (T₁ : triangle C) (e : T₁ ≅ T₂)`, where the two `T₁` are referring to different triangles.
#### Estimated changes
Modified src/category_theory/triangulated/pretriangulated.lean




## [2022-01-22 17:00:41](https://github.com/leanprover-community/mathlib/commit/d1b5165)
chore(group_theory/nilpotent): golf some proofs ([#11599](https://github.com/leanprover-community/mathlib/pull/11599))
#### Estimated changes
Modified src/group_theory/nilpotent.lean




## [2022-01-22 16:18:02](https://github.com/leanprover-community/mathlib/commit/fbf3c64)
chore(analysis/normed_space/star): golf some lemmas ([#11600](https://github.com/leanprover-community/mathlib/pull/11600))
#### Estimated changes
Modified src/analysis/normed_space/star.lean




## [2022-01-22 13:06:18](https://github.com/leanprover-community/mathlib/commit/504e1f6)
feat(group_theory.nilpotent): add *_central_series_one G 1 = … simp lemmas ([#11584](https://github.com/leanprover-community/mathlib/pull/11584))
analogously to the existing `_zero` lemmas
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* lower_central_series_one
- \+ *lemma* upper_central_series_one



## [2022-01-22 13:06:17](https://github.com/leanprover-community/mathlib/commit/b630b8c)
feat(order/antichain): Strong antichains ([#11400](https://github.com/leanprover-community/mathlib/pull/11400))
This introduces a predicate `is_strong_antichain` to state that a set is a strong antichain with respect to a relation.
`s` is a strong (upward) antichain wrt `r` if for all `a ≠ b` in `s` there is some `c` such that `¬ r a c` or `¬ r b c`. A strong downward antichain of the swapped relation.
#### Estimated changes
Modified src/data/set/pairwise.lean


Modified src/order/antichain.lean
- \- *lemma* is_antichain.eq_of_related'
- \- *lemma* is_antichain.eq_of_related
- \+ *lemma* is_strong_antichain.eq
- \+ *lemma* is_strong_antichain.image
- \+ *lemma* is_strong_antichain.mono
- \+ *lemma* is_strong_antichain.preimage
- \+ *lemma* is_strong_antichain.swap
- \+ *def* is_strong_antichain
- \+ *lemma* is_strong_antichain_insert
- \+ *lemma* set.subsingleton.is_strong_antichain

Modified src/order/minimal.lean


Modified src/order/well_founded_set.lean




## [2022-01-22 12:01:38](https://github.com/leanprover-community/mathlib/commit/0ca7795)
feat(algebra/algebra/operations): remove two hypotheses from `submodule.mul_induction_on` ([#11533](https://github.com/leanprover-community/mathlib/pull/11533))
`h0 : C 0` followed trivially from `hm 0 _ 0 _`.
`hs : ∀ (r : R) x, C x → C (r • x)` follows nontrivially from an analogy to the `add_submonoid` case.
This also adds:
* a `pow_induction` variant.
* primed variants for when the motive depends on the proof term (such as the proof field in a subtype)
#### Estimated changes
Modified src/algebra/algebra/operations.lean
- \+ *lemma* submodule.mul_to_add_submonoid

Modified src/ring_theory/fractional_ideal.lean




## [2022-01-21 23:07:46](https://github.com/leanprover-community/mathlib/commit/5e9c0a5)
feat(group_theory/subgroup/basic): add center_le_normalizer ([#11590](https://github.com/leanprover-community/mathlib/pull/11590))
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.center_le_normalizer



## [2022-01-21 22:19:47](https://github.com/leanprover-community/mathlib/commit/d99f2fd)
chore(analysis/normed/group/basic): merge `norm` and `semi_norm` lemmas on `prod` and `pi` ([#11492](https://github.com/leanprover-community/mathlib/pull/11492))
`norm` and `semi_norm` are the same operator, so there is no need to have two sets of lemmas.
As a result the elaborator needs a few hints for some applications of the `pi` lemmas, but this is par for the course for pi typeclass instances anyway.
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/analysis/normed/group/basic.lean
- \+/\- *lemma* norm_le_pi_norm
- \- *lemma* pi_nnsemi_norm_const
- \+/\- *lemma* pi_norm_le_iff
- \+/\- *lemma* pi_norm_lt_iff
- \- *lemma* pi_semi_norm_const
- \- *lemma* pi_semi_norm_le_iff
- \- *lemma* pi_semi_norm_lt_iff
- \- *lemma* prod.nnsemi_norm_def
- \- *lemma* prod.semi_norm_def
- \- *lemma* semi_norm_fst_le
- \- *lemma* semi_norm_le_pi_norm
- \- *lemma* semi_norm_prod_le_iff
- \- *lemma* semi_norm_snd_le

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_matrix_le_iff
- \- *lemma* semi_norm_matrix_le_iff

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/linear_isometry.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean




## [2022-01-21 21:34:00](https://github.com/leanprover-community/mathlib/commit/0653975)
chore(category_theory/sites): Generalize universes for the comparison lemma. ([#11588](https://github.com/leanprover-community/mathlib/pull/11588))
#### Estimated changes
Modified src/category_theory/limits/kan_extension.lean


Modified src/category_theory/sites/cover_lifting.lean


Modified src/category_theory/sites/dense_subsite.lean




## [2022-01-21 19:30:19](https://github.com/leanprover-community/mathlib/commit/049d2ac)
feat(analysis/fourier): Fourier series for functions in L2; Parseval's identity ([#11320](https://github.com/leanprover-community/mathlib/pull/11320))
#### Estimated changes
Modified docs/100.yaml


Modified docs/undergrad.yaml


Modified src/analysis/fourier.lean
- \+ *lemma* coe_fn_fourier_Lp
- \+ *lemma* coe_fourier_series
- \+ *def* fourier_series
- \+ *lemma* fourier_series_repr
- \+ *lemma* has_sum_fourier_series
- \+ *lemma* tsum_sq_fourier_series_repr



## [2022-01-21 15:40:51](https://github.com/leanprover-community/mathlib/commit/9c39019)
refactor(src/order/bounded): Invert iff direction ([#11582](https://github.com/leanprover-community/mathlib/pull/11582))
That way, `unbounded_gt_iff_unbounded_ge` corresponds to `unbounded_lt_iff_unbounded_le`.
#### Estimated changes
Modified src/order/bounded.lean
- \- *lemma* unbounded_ge_iff_unbounded_gt
- \+ *lemma* unbounded_gt_iff_unbounded_ge



## [2022-01-21 10:54:30](https://github.com/leanprover-community/mathlib/commit/ca79513)
feat(order/bounded): Proved many lemmas about bounded and unbounded sets ([#11179](https://github.com/leanprover-community/mathlib/pull/11179))
These include more convenient characterizations of unboundedness in preorders and linear orders, and many results about bounded intervals and initial segments.
#### Estimated changes
Added src/order/bounded.lean
- \+ *theorem* bounded.mono
- \+ *lemma* bounded.rel_mono
- \+ *theorem* bounded_ge_Icc
- \+ *theorem* bounded_ge_Ici
- \+ *theorem* bounded_ge_Ico
- \+ *theorem* bounded_ge_Ioc
- \+ *theorem* bounded_ge_Ioi
- \+ *theorem* bounded_ge_Ioo
- \+ *lemma* bounded_ge_iff_bounded_gt
- \+ *theorem* bounded_ge_inter_ge
- \+ *theorem* bounded_ge_inter_gt
- \+ *theorem* bounded_ge_inter_not_ge
- \+ *lemma* bounded_ge_of_bounded_gt
- \+ *theorem* bounded_gt_Icc
- \+ *theorem* bounded_gt_Ici
- \+ *theorem* bounded_gt_Ico
- \+ *theorem* bounded_gt_Ioc
- \+ *theorem* bounded_gt_Ioi
- \+ *theorem* bounded_gt_Ioo
- \+ *theorem* bounded_gt_inter_ge
- \+ *theorem* bounded_gt_inter_gt
- \+ *theorem* bounded_gt_inter_not_gt
- \+ *theorem* bounded_inter_not
- \+ *theorem* bounded_le_Icc
- \+ *theorem* bounded_le_Ico
- \+ *theorem* bounded_le_Iic
- \+ *theorem* bounded_le_Iio
- \+ *theorem* bounded_le_Ioc
- \+ *theorem* bounded_le_Ioo
- \+ *lemma* bounded_le_iff_bounded_lt
- \+ *theorem* bounded_le_inter_le
- \+ *theorem* bounded_le_inter_lt
- \+ *theorem* bounded_le_inter_not_le
- \+ *lemma* bounded_le_of_bounded_lt
- \+ *theorem* bounded_lt_Icc
- \+ *theorem* bounded_lt_Ico
- \+ *theorem* bounded_lt_Iic
- \+ *theorem* bounded_lt_Iio
- \+ *theorem* bounded_lt_Ioc
- \+ *theorem* bounded_lt_Ioo
- \+ *theorem* bounded_lt_inter_le
- \+ *theorem* bounded_lt_inter_lt
- \+ *theorem* bounded_lt_inter_not_lt
- \+ *theorem* bounded_self
- \+ *theorem* unbounded.mono
- \+ *lemma* unbounded.rel_mono
- \+ *lemma* unbounded_ge_iff
- \+ *lemma* unbounded_ge_iff_unbounded_gt
- \+ *theorem* unbounded_ge_iff_unbounded_inter_ge
- \+ *theorem* unbounded_ge_inter_gt
- \+ *theorem* unbounded_ge_inter_not_ge
- \+ *lemma* unbounded_ge_of_forall_exists_gt
- \+ *lemma* unbounded_gt_iff
- \+ *theorem* unbounded_gt_inter_gt
- \+ *theorem* unbounded_gt_inter_not_gt
- \+ *lemma* unbounded_gt_of_forall_exists_ge
- \+ *lemma* unbounded_gt_of_unbounded_ge
- \+ *theorem* unbounded_inter_ge
- \+ *theorem* unbounded_inter_not
- \+ *theorem* unbounded_le_Ici
- \+ *theorem* unbounded_le_Ioi
- \+ *lemma* unbounded_le_iff
- \+ *theorem* unbounded_le_inter_le
- \+ *theorem* unbounded_le_inter_lt
- \+ *theorem* unbounded_le_inter_not_le
- \+ *lemma* unbounded_le_of_forall_exists_lt
- \+ *theorem* unbounded_lt_Ici
- \+ *theorem* unbounded_lt_Ioi
- \+ *lemma* unbounded_lt_iff
- \+ *lemma* unbounded_lt_iff_unbounded_le
- \+ *theorem* unbounded_lt_inter_le
- \+ *theorem* unbounded_lt_inter_lt
- \+ *theorem* unbounded_lt_inter_not_lt
- \+ *lemma* unbounded_lt_of_forall_exists_le
- \+ *lemma* unbounded_lt_of_unbounded_le

Modified src/order/lattice.lean
- \+ *theorem* inf_lt_of_left_lt
- \+ *theorem* inf_lt_of_right_lt
- \+ *theorem* lt_sup_of_lt_left
- \+ *theorem* lt_sup_of_lt_right

Modified src/order/rel_classes.lean
- \+/\- *def* bounded



## [2022-01-21 04:46:35](https://github.com/leanprover-community/mathlib/commit/884d813)
chore(analysis/inner_product_space/dual): remove unneeded `complete_space` assumption in four lemmas ([#11578](https://github.com/leanprover-community/mathlib/pull/11578))
We remove the `[complete_space E]` assumption in four lemmas.
#### Estimated changes
Modified src/analysis/inner_product_space/dual.lean




## [2022-01-21 03:07:37](https://github.com/leanprover-community/mathlib/commit/80e072e)
feat(data/finset/basic): random golf ([#11576](https://github.com/leanprover-community/mathlib/pull/11576))
#### Estimated changes
Modified src/data/finset/basic.lean




## [2022-01-21 00:16:10](https://github.com/leanprover-community/mathlib/commit/d71cab9)
feat(analysis/seminorm): add composition with linear maps ([#11477](https://github.com/leanprover-community/mathlib/pull/11477))
This PR defines the composition of seminorms with linear maps and shows that composition is monotone and calculates the seminorm ball of the composition.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* seminorm.add_comp
- \+ *lemma* seminorm.ball_comp
- \+ *lemma* seminorm.coe_comp
- \+ *def* seminorm.comp
- \+ *lemma* seminorm.comp_apply
- \+ *lemma* seminorm.comp_comp
- \+ *lemma* seminorm.comp_id
- \+ *lemma* seminorm.comp_mono
- \+ *lemma* seminorm.comp_smul
- \+ *lemma* seminorm.comp_smul_apply
- \+ *lemma* seminorm.comp_triangle
- \+ *lemma* seminorm.comp_zero
- \+ *lemma* seminorm.smul_comp
- \+ *lemma* seminorm.zero_apply
- \+ *lemma* seminorm.zero_comp



## [2022-01-20 22:45:37](https://github.com/leanprover-community/mathlib/commit/6c97821)
feat(group_theory/submonoid/pointwise): add pointwise multiplication to `add_submonoid`s ([#11522](https://github.com/leanprover-community/mathlib/pull/11522))
#### Estimated changes
Modified src/group_theory/submonoid/pointwise.lean
- \+ *theorem* add_submonoid.bot_mul
- \+ *theorem* add_submonoid.closure_mul_closure
- \+ *theorem* add_submonoid.mul_bot
- \+ *theorem* add_submonoid.mul_le
- \+ *theorem* add_submonoid.mul_le_mul
- \+ *theorem* add_submonoid.mul_le_mul_left
- \+ *theorem* add_submonoid.mul_le_mul_right
- \+ *theorem* add_submonoid.mul_mem_mul
- \+ *lemma* add_submonoid.mul_subset_mul



## [2022-01-20 19:35:50](https://github.com/leanprover-community/mathlib/commit/adadd4a)
feat(measure_theory/function/lp_space): some variations of Markov's inequality formulated using `snorm` ([#11478](https://github.com/leanprover-community/mathlib/pull/11478))
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/measure_theory/function/lp_space.lean
- \+ *lemma* measure_theory.Lp.meas_ge_le_mul_pow_norm
- \+ *lemma* measure_theory.Lp.mul_meas_ge_le_pow_norm'
- \+ *lemma* measure_theory.Lp.mul_meas_ge_le_pow_norm
- \+ *lemma* measure_theory.Lp.pow_mul_meas_ge_le_norm
- \+ *lemma* measure_theory.meas_ge_le_mul_pow_snorm
- \+ *lemma* measure_theory.mul_meas_ge_le_pow_snorm'
- \+ *lemma* measure_theory.mul_meas_ge_le_pow_snorm
- \+ *lemma* measure_theory.pow_mul_meas_ge_le_snorm



## [2022-01-20 18:13:27](https://github.com/leanprover-community/mathlib/commit/8c9074f)
chore(*): Remove tactic.unfreeze_local_instances ([#11507](https://github.com/leanprover-community/mathlib/pull/11507))
#### Estimated changes
Modified src/algebra/associated.lean


Modified src/algebra/lie/nilpotent.lean


Modified src/algebra/lie/semisimple.lean


Modified src/algebra/lie/solvable.lean


Modified src/algebraic_geometry/properties.lean


Modified src/analysis/normed_space/lp_space.lean


Modified src/combinatorics/hall/finite.lean


Modified src/data/real/ennreal.lean


Modified src/group_theory/solvable.lean


Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/matrix/block.lean


Modified src/linear_algebra/multilinear/basic.lean


Modified src/linear_algebra/quadratic_form/basic.lean


Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/local_properties.lean


Modified src/topology/category/Top/limits.lean




## [2022-01-20 17:46:05](https://github.com/leanprover-community/mathlib/commit/dfca2b0)
feat(data/sym/sym2): add lemma that eq from distinct common members ([#11563](https://github.com/leanprover-community/mathlib/pull/11563))
Two terms of type `sym2 a` are equal if one can find two distinct elements of type `a` that are members of both.
#### Estimated changes
Modified src/data/sym/sym2.lean
- \+ *lemma* sym2.eq_of_ne_mem



## [2022-01-20 16:52:21](https://github.com/leanprover-community/mathlib/commit/b87449a)
feat(group_theory/nilpotent): Add equality theorems for nilpotency class ([#11540](https://github.com/leanprover-community/mathlib/pull/11540))
the nilpotency class can be defined as the length of the
upper central series, the lower central series, or as the shortest
length across all ascending or descending series.
In order to use the equivalence proofs between the various definition
of nilpotency in these lemmas, I had to reorder them to put the `∃n` in
front.
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* is_ascending_rev_series_of_is_descending
- \+ *lemma* is_decending_rev_series_of_is_ascending
- \+ *lemma* least_ascending_central_series_length_eq_nilpotency_class
- \+ *lemma* least_descending_central_series_length_eq_nilpotency_class
- \+ *lemma* lower_central_series_length_eq_nilpotency_class



## [2022-01-20 16:01:23](https://github.com/leanprover-community/mathlib/commit/b5e542d)
feat(measure_theory/measurable_space): defining a measurable function on countably many pieces ([#11532](https://github.com/leanprover-community/mathlib/pull/11532))
Also, remove `open_locale classical` in this file and add decidability assumptions where needed. And add a few isolated useful lemmas.
#### Estimated changes
Modified src/measure_theory/group/basic.lean


Modified src/measure_theory/measurable_space.lean
- \+ *lemma* exists_measurable_piecewise_nat
- \+ *lemma* measurable.find
- \+ *def* measurable_equiv.pi_measurable_equiv_tprod
- \+/\- *lemma* measurable_find
- \+/\- *lemma* measurable_find_greatest'
- \+/\- *lemma* measurable_find_greatest
- \+/\- *lemma* measurable_from_prod_encodable
- \+/\- *lemma* measurable_set_pi_of_nonempty
- \+/\- *lemma* measurable_tprod_elim'
- \+/\- *lemma* measurable_tprod_elim
- \+/\- *lemma* measurable_update

Modified src/measure_theory/measure/haar.lean




## [2022-01-20 15:29:30](https://github.com/leanprover-community/mathlib/commit/1d762c7)
feat(ring_theory/{norm.lean, trace.lean}): improve two statements. ([#11569](https://github.com/leanprover-community/mathlib/pull/11569))
These statement are more precise.
From flt-regular.
#### Estimated changes
Modified src/ring_theory/norm.lean


Modified src/ring_theory/trace.lean




## [2022-01-20 11:33:03](https://github.com/leanprover-community/mathlib/commit/447928c)
feat(topology/uniform_space/uniform_convergence): Composition on the left ([#11560](https://github.com/leanprover-community/mathlib/pull/11560))
Composing on the left by a uniformly continuous function preserves uniform convergence.
#### Estimated changes
Modified src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* tendsto_uniformly.comp'
- \+ *lemma* tendsto_uniformly_on.comp'



## [2022-01-20 10:32:33](https://github.com/leanprover-community/mathlib/commit/5a40c33)
feat(analysis/inner_product_space/l2): a Hilbert space is isometrically isomorphic to `ℓ²` ([#11255](https://github.com/leanprover-community/mathlib/pull/11255))
Define `orthogonal_family.linear_isometry_equiv`: the isometric isomorphism of a Hilbert space `E` with a Hilbert sum of a family of Hilbert spaces `G i`, induced by individual isometries of each `G i` into `E` whose images are orthogonal and span a dense subset of `E`.
Define a Hilbert basis of `E` to be an isometric isomorphism of `E` with `ℓ²(ι, 𝕜)`, the Hilbert sum of `ι` copies of `𝕜`.  Prove that an orthonormal family of vectors in `E` whose span is dense in `E` has an associated Hilbert basis.
Prove that every Hilbert space admit a Hilbert basis.
Delete three lemmas `maximal_orthonormal_iff_dense_span`, `exists_subset_is_orthonormal_dense_span`, `exists_is_orthonormal_dense_span` which previously expressed this existence theorem in a more awkward way (before the definition `ℓ²(ι, 𝕜)` was available).
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/analysis/inner_product_space/l2_space.lean
- \+ *lemma* exists_hilbert_basis
- \+ *structure* hilbert_basis
- \+ *lemma* lp.inner_single_left
- \+ *lemma* lp.inner_single_right
- \+ *lemma* orthonormal.exists_hilbert_basis_extension

Modified src/analysis/inner_product_space/projection.lean
- \- *lemma* exists_is_orthonormal_dense_span
- \- *lemma* exists_subset_is_orthonormal_dense_span
- \- *lemma* maximal_orthonormal_iff_dense_span

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry_equiv.coe_of_surjective



## [2022-01-20 08:57:41](https://github.com/leanprover-community/mathlib/commit/53650a0)
feat(*): lemmas about `disjoint` on `set`s and `filter`s ([#11549](https://github.com/leanprover-community/mathlib/pull/11549))
#### Estimated changes
Modified src/data/set/function.lean


Modified src/data/set/lattice.lean
- \+ *lemma* disjoint.ne_of_mem
- \+ *lemma* set.disjoint_iff_forall_ne

Modified src/order/filter/basic.lean
- \+ *lemma* filter.disjoint_comap
- \+ *lemma* filter.disjoint_map

Modified src/topology/basic.lean
- \+ *lemma* disjoint.closure_left
- \+ *lemma* disjoint.closure_right



## [2022-01-20 07:43:43](https://github.com/leanprover-community/mathlib/commit/e96e55d)
feat(analysis/normed_space/finite_dimension): extending partially defined Lipschitz functions ([#11530](https://github.com/leanprover-community/mathlib/pull/11530))
Any Lipschitz function on a subset of a metric space, into a finite-dimensional real vector space, can be extended to a globally defined Lipschitz function (up to worsening slightly the Lipschitz constant).
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* linear_equiv.coe_to_continuous_linear_equiv'
- \+ *lemma* linear_equiv.coe_to_continuous_linear_equiv
- \+ *lemma* linear_equiv.coe_to_continuous_linear_equiv_symm'
- \+ *lemma* linear_equiv.coe_to_continuous_linear_equiv_symm
- \+/\- *def* linear_equiv.to_continuous_linear_equiv
- \+ *lemma* linear_equiv.to_linear_equiv_to_continuous_linear_equiv
- \+ *lemma* linear_equiv.to_linear_equiv_to_continuous_linear_equiv_symm
- \+ *def* lipschitz_extension_constant
- \+ *lemma* lipschitz_extension_constant_pos
- \+ *theorem* lipschitz_on_with.extend_finite_dimension

Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/topology/metric_space/lipschitz.lean
- \+/\- *lemma* continuous_at_of_locally_lipschitz
- \+ *lemma* lipschitz_on_with.extend_pi
- \+ *lemma* lipschitz_on_with.extend_real
- \+ *lemma* lipschitz_with.comp_lipschitz_on_with



## [2022-01-20 02:36:41](https://github.com/leanprover-community/mathlib/commit/0a8848a)
chore(topology/uniform_space/uniform_convergence): Golf some proofs ([#11561](https://github.com/leanprover-community/mathlib/pull/11561))
This PR golfs a couple proofs.
#### Estimated changes
Modified src/topology/uniform_space/uniform_convergence.lean




## [2022-01-20 00:11:03](https://github.com/leanprover-community/mathlib/commit/656372c)
doc(group_theory/free_group): fix linkify ([#11565](https://github.com/leanprover-community/mathlib/pull/11565))
#### Estimated changes
Modified src/group_theory/free_group.lean




## [2022-01-19 22:49:35](https://github.com/leanprover-community/mathlib/commit/0bb4272)
chore(*): to_additive related cleanup ([#11559](https://github.com/leanprover-community/mathlib/pull/11559))
A few to_additive related cleanups
* Move measurability before to_additive to avoid having to manually do it later (or forget).
* Ensure anything tagged to_additive, mono has the additive version also mono'd
* Move simp before to_additive
#### Estimated changes
Modified src/algebra/order/lattice_group.lean


Modified src/algebra/pointwise.lean


Modified src/measure_theory/group/arithmetic.lean


Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable_set_mul_support



## [2022-01-19 19:16:21](https://github.com/leanprover-community/mathlib/commit/7ee41aa)
feat(data/finsupp/basic): lemmas about map domain with only inj_on hypotheses ([#11484](https://github.com/leanprover-community/mathlib/pull/11484))
Also a lemma `sum_update_add` expressing the sum of an update in a monoid in terms of the original sum and the value of the update.
And golf `map_domain_smul`.
From flt-regular.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.map_domain_apply'
- \+ *lemma* finsupp.map_domain_inj_on
- \+ *lemma* finsupp.map_domain_support_of_inj_on
- \+ *lemma* finsupp.sum_update_add



## [2022-01-19 17:41:05](https://github.com/leanprover-community/mathlib/commit/bbd0f76)
chore(*): clean up comment strings in docstrings ([#11557](https://github.com/leanprover-community/mathlib/pull/11557))
The syntax for these was wrong and showed up in doc-gen output unintentionally e.g.
https://leanprover-community.github.io/mathlib_docs/algebra/group/opposite.html#add_monoid_hom.op
#### Estimated changes
Modified src/algebra/category/Mon/filtered_colimits.lean


Modified src/algebra/group/opposite.lean


Modified src/algebra/opposites.lean


Modified src/group_theory/order_of_element.lean


Modified src/measure_theory/group/fundamental_domain.lean


Modified src/topology/algebra/monoid.lean




## [2022-01-19 16:05:57](https://github.com/leanprover-community/mathlib/commit/a90f969)
feat(data/finset/slice): More `finset.slice` and antichain lemmas ([#11397](https://github.com/leanprover-community/mathlib/pull/11397))
Also move `finset.coe_bUnion` to a more sensible location.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.coe_bUnion

Modified src/data/finset/slice.lean
- \+ *lemma* finset.bUnion_slice
- \+/\- *lemma* finset.pairwise_disjoint_slice
- \+ *lemma* finset.sum_card_slice
- \+ *lemma* set.sized.empty_mem_iff
- \+ *lemma* set.sized.subsingleton'
- \+ *lemma* set.sized.univ_mem_iff
- \+ *lemma* set.sized_Union
- \+ *lemma* set.sized_Union₂
- \+ *lemma* set.sized_powerset_len

Modified src/data/set/basic.lean
- \+ *lemma* set.subsingleton_of_forall_eq

Modified src/data/set/finite.lean
- \- *lemma* finset.coe_bUnion

Modified src/order/antichain.lean
- \+ *lemma* is_antichain.bot_mem_iff
- \+ *lemma* is_antichain.greatest_iff
- \+ *lemma* is_antichain.least_iff
- \+ *lemma* is_antichain.top_mem_iff
- \+ *lemma* is_antichain_and_greatest_iff
- \+ *lemma* is_antichain_and_least_iff
- \+ *lemma* is_antichain_singleton
- \+ *lemma* is_greatest.antichain_iff
- \+ *lemma* is_least.antichain_iff
- \+/\- *lemma* set.subsingleton.is_antichain

Modified src/order/bounds.lean
- \+ *lemma* bot_mem_lower_bounds
- \+ *lemma* is_greatest_top_iff
- \+ *lemma* is_least_bot_iff
- \+ *lemma* top_mem_upper_bounds



## [2022-01-19 15:39:30](https://github.com/leanprover-community/mathlib/commit/c72e709)
feat(data/sum/interval): The disjoint sum of two locally finite orders is locally finite ([#11351](https://github.com/leanprover-community/mathlib/pull/11351))
This proves `locally_finite_order (α ⊕ β)` where `α` and `β` are locally finite themselves.
#### Estimated changes
Added src/data/sum/interval.lean
- \+ *lemma* finset.inl_mem_sum_lift₂
- \+ *lemma* finset.inr_mem_sum_lift₂
- \+ *lemma* finset.mem_sum_lift₂
- \+ *def* finset.sum_lift₂
- \+ *lemma* finset.sum_lift₂_eq_empty
- \+ *lemma* finset.sum_lift₂_mono
- \+ *lemma* finset.sum_lift₂_nonempty
- \+ *lemma* sum.Icc_inl_inl
- \+ *lemma* sum.Icc_inl_inr
- \+ *lemma* sum.Icc_inr_inl
- \+ *lemma* sum.Icc_inr_inr
- \+ *lemma* sum.Ico_inl_inl
- \+ *lemma* sum.Ico_inl_inr
- \+ *lemma* sum.Ico_inr_inl
- \+ *lemma* sum.Ico_inr_inr
- \+ *lemma* sum.Ioc_inl_inl
- \+ *lemma* sum.Ioc_inl_inr
- \+ *lemma* sum.Ioc_inr_inl
- \+ *lemma* sum.Ioc_inr_inr
- \+ *lemma* sum.Ioo_inl_inl
- \+ *lemma* sum.Ioo_inl_inr
- \+ *lemma* sum.Ioo_inr_inl
- \+ *lemma* sum.Ioo_inr_inr



## [2022-01-19 13:06:48](https://github.com/leanprover-community/mathlib/commit/dbf59ba)
feat(algebra/roots_of_unity): basic constructor ([#11504](https://github.com/leanprover-community/mathlib/pull/11504))
from flt-regular
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* roots_of_unity.coe_mk_of_pow_eq
- \+ *def* roots_of_unity.mk_of_pow_eq



## [2022-01-19 11:58:04](https://github.com/leanprover-community/mathlib/commit/7ddaf10)
chore(algebra/algebra): algebra_map_int_eq ([#11474](https://github.com/leanprover-community/mathlib/pull/11474))
from flt-regular
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* algebra_map_int_eq

Modified src/data/polynomial/algebra_map.lean
- \- *lemma* polynomial.eval₂_algebra_map_int_X
- \+ *lemma* polynomial.eval₂_int_cast_ring_hom_X
- \- *lemma* polynomial.ring_hom_eval₂_algebra_map_int
- \+ *lemma* polynomial.ring_hom_eval₂_cast_int_ring_hom



## [2022-01-19 10:24:24](https://github.com/leanprover-community/mathlib/commit/4ad74ae)
chore(algebra/order/sub): Generalize to `preorder` and `add_comm_semigroup` ([#11463](https://github.com/leanprover-community/mathlib/pull/11463))
This generalizes a bunch of lemmas from `partial_order` to `preorder` and from `add_comm_monoid` to `add_comm_semigroup`.
It also adds `tsub_tsub_le_tsub_add : a - (b - c) ≤ a - b + c`.
#### Estimated changes
Modified src/algebra/order/sub.lean
- \+/\- *lemma* le_add_tsub'
- \+/\- *lemma* le_add_tsub_swap
- \+ *lemma* tsub_tsub_le_tsub_add



## [2022-01-19 06:53:49](https://github.com/leanprover-community/mathlib/commit/1cfb97d)
feat(analysis/normed/group/pointwise): the closed thickening of a compact set is the addition of a closed ball. ([#11528](https://github.com/leanprover-community/mathlib/pull/11528))
#### Estimated changes
Modified src/analysis/normed/group/pointwise.lean
- \+ *lemma* is_compact.cthickening_eq_add_closed_ball

Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* is_compact.cthickening_eq_bUnion_closed_ball
- \+ *lemma* metric.closed_ball_subset_cthickening
- \+ *lemma* metric.closed_ball_subset_cthickening_singleton
- \+ *lemma* metric.cthickening_singleton
- \+ *lemma* metric.thickening_singleton



## [2022-01-19 06:53:48](https://github.com/leanprover-community/mathlib/commit/ff9b757)
feat(category_theory/bicategory/locally_discrete): define locally discrete bicategory ([#11402](https://github.com/leanprover-community/mathlib/pull/11402))
This PR defines the locally discrete bicategory on a category.
#### Estimated changes
Added src/category_theory/bicategory/locally_discrete.lean
- \+ *def* category_theory.functor.to_oplax_functor
- \+ *def* category_theory.locally_discrete

Modified src/category_theory/bicategory/strict.lean
- \+ *lemma* category_theory.bicategory.eq_to_hom_whisker_right
- \+ *lemma* category_theory.bicategory.whisker_left_eq_to_hom



## [2022-01-18 21:06:28](https://github.com/leanprover-community/mathlib/commit/6dd6525)
feat(measure_theory/measure/measure_space): better definition of to_measurable ([#11529](https://github.com/leanprover-community/mathlib/pull/11529))
Currently, `to_measurable μ t` picks a measurable superset of `t` with the same measure. When the measure of `t` is infinite, it is most often useless. This PR adjusts the definition so that, in the case of sigma-finite spaces, `to_measurable μ t` has good properties even when `t` has infinite measure.
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.is_locally_finite_measure_of_is_finite_measure_on_compacts
- \+ *lemma* measure_theory.measure.exists_subset_measure_lt_top
- \+ *lemma* measure_theory.measure.measure_to_measurable_inter_of_sigma_finite
- \+ *lemma* measure_theory.nonempty_inter_of_measure_lt_add'
- \+ *lemma* measure_theory.nonempty_inter_of_measure_lt_add

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* measure_theory.ae_eq_set_inter
- \+ *lemma* measure_theory.ae_le_set_inter
- \+/\- *def* measure_theory.to_measurable



## [2022-01-18 20:38:47](https://github.com/leanprover-community/mathlib/commit/de53f9c)
feat(data/nat/factorization): add two convenience lemmas ([#11543](https://github.com/leanprover-community/mathlib/pull/11543))
Adds convenience lemmas `prime_of_mem_factorization` and `pos_of_mem_factorization`.
Also adds a different proof of `factorization_prod_pow_eq_self` that doesn't depend on `multiplicative_factorization` and so can appear earlier in the file.
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+ *lemma* nat.pos_of_mem_factorization
- \+ *lemma* nat.prime_of_mem_factorization



## [2022-01-18 17:08:36](https://github.com/leanprover-community/mathlib/commit/5a1cbe3)
feat(linear_algebra,algebra,group_theory): miscellaneous lemmas linking some additive monoid and module operations ([#11525](https://github.com/leanprover-community/mathlib/pull/11525))
This adds:
* `submodule.map_to_add_submonoid`
* `submodule.sup_to_add_submonoid`
* `submodule.supr_to_add_submonoid`
As well as some missing `add_submonoid` lemmas copied from the `submodule` API:
* `add_submonoid.closure_singleton_le_iff_mem`
* `add_submonoid.mem_supr`
* `add_submonoid.supr_eq_closure`
Finally, it generalizes some indices in `supr` and `infi` lemmas from `Type*` to `Sort*`.
This is pre-work for removing a redundant hypothesis from `submodule.mul_induction_on`.
#### Estimated changes
Modified src/algebra/algebra/bilinear.lean
- \+ *lemma* algebra.lmul_left_to_add_monoid_hom
- \+ *lemma* algebra.lmul_right_to_add_monoid_hom

Modified src/group_theory/submonoid/basic.lean
- \+ *lemma* submonoid.closure_singleton_le_iff_mem
- \+ *lemma* submonoid.mem_supr
- \+ *lemma* submonoid.supr_eq_closure

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* linear_map.infi_invariant
- \+/\- *lemma* submodule.comap_infi_map_of_injective
- \+/\- *lemma* submodule.comap_supr_map_of_injective
- \+/\- *lemma* submodule.map_infi_comap_of_surjective
- \+/\- *lemma* submodule.map_supr_comap_of_sujective
- \+ *lemma* submodule.map_to_add_submonoid
- \+ *lemma* submodule.sup_to_add_subgroup
- \+ *lemma* submodule.sup_to_add_submonoid
- \+ *lemma* submodule.supr_to_add_submonoid



## [2022-01-18 16:08:17](https://github.com/leanprover-community/mathlib/commit/a0ff65d)
feat(ring_theory/norm): add is_integral_norm ([#11489](https://github.com/leanprover-community/mathlib/pull/11489))
We add `is_integral_norm`.
From flt-regular
#### Estimated changes
Modified src/ring_theory/norm.lean
- \+ *lemma* algebra.is_integral_norm
- \+ *lemma* algebra.norm_eq_prod_roots
- \+/\- *lemma* algebra.prod_embeddings_eq_finrank_pow
- \+ *lemma* intermediate_field.adjoin_simple.norm_gen_eq_one
- \+ *lemma* intermediate_field.adjoin_simple.norm_gen_eq_prod_roots



## [2022-01-18 15:13:28](https://github.com/leanprover-community/mathlib/commit/6f23973)
feat(ring_theory/graded_algebra/basic): add a helper for construction from an alg hom ([#11541](https://github.com/leanprover-community/mathlib/pull/11541))
Most graded algebras are already equipped with some kind of universal property which gives an easy way to build such an `alg_hom`.
This lemma makes it easier to discharge the associated proof obligations to show that this alg hom forms a decomposition.
This also relaxes a `ring` argument to `semiring`.
#### Estimated changes
Modified src/ring_theory/graded_algebra/basic.lean
- \+ *def* graded_algebra.of_alg_hom



## [2022-01-18 12:22:37](https://github.com/leanprover-community/mathlib/commit/496a744)
feat(measure_theory): generalize `null_of_locally_null` to `outer_measure`, add versions ([#11535](https://github.com/leanprover-community/mathlib/pull/11535))
* generalize `null_of_locally_null`;
* don't intersect with `s` twice;
* add a contraposed version;
* golf.
#### Estimated changes
Modified src/measure_theory/covering/differentiation.lean


Modified src/measure_theory/covering/vitali.lean


Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.exists_mem_forall_mem_nhds_within_pos_measure
- \+ *lemma* measure_theory.exists_ne_forall_mem_nhds_pos_measure_preimage
- \+/\- *lemma* measure_theory.null_of_locally_null

Modified src/measure_theory/measure/outer_measure.lean
- \+ *lemma* measure_theory.outer_measure.exists_mem_forall_mem_nhds_within_pos
- \+ *lemma* measure_theory.outer_measure.null_of_locally_null

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.diam_le_of_subset_closed_ball



## [2022-01-18 12:22:35](https://github.com/leanprover-community/mathlib/commit/be9a5de)
feat(topology/separation): add `t1_space_tfae` ([#11534](https://github.com/leanprover-community/mathlib/pull/11534))
Also add some lemmas about `filter.disjoint`.
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* filter.disjoint_principal_left
- \+ *lemma* filter.disjoint_principal_principal
- \+ *lemma* filter.disjoint_principal_right
- \+ *lemma* filter.disjoint_pure_pure
- \+ *lemma* filter.has_basis.disjoint_basis_iff
- \- *lemma* filter.inf_eq_bot_iff
- \- *lemma* filter.le_iff_forall_disjoint_principal_compl
- \- *lemma* filter.mem_iff_disjoint_principal_compl

Modified src/order/filter/basic.lean
- \+ *lemma* filter.inf_eq_bot_iff

Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/separation.lean
- \+ *lemma* disjoint_nhds_pure
- \+ *lemma* disjoint_pure_nhds
- \- *lemma* finite.is_closed
- \- *lemma* t1_iff_exists_open
- \- *lemma* t1_space_antimono
- \+ *lemma* t1_space_antitone
- \+ *lemma* t1_space_iff_disjoint_nhds_pure
- \+ *lemma* t1_space_iff_disjoint_pure_nhds
- \+ *lemma* t1_space_iff_exists_open
- \+ *lemma* t1_space_tfae



## [2022-01-18 12:22:34](https://github.com/leanprover-community/mathlib/commit/135a92d)
feat(data/set): two simple lemmas ([#11531](https://github.com/leanprover-community/mathlib/pull/11531))
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* disjoint.image
- \+ *lemma* set.inj_on.image_inter

Modified src/data/set/pairwise.lean
- \+ *lemma* pairwise_disjoint.mono

Modified src/measure_theory/measure/haar_lebesgue.lean




## [2022-01-18 12:22:32](https://github.com/leanprover-community/mathlib/commit/5bbc187)
feat(algebra/lie/nilpotent): a non-trivial nilpotent Lie module has non-trivial maximal trivial submodule ([#11515](https://github.com/leanprover-community/mathlib/pull/11515))
The main result is `lie_module.nontrivial_max_triv_of_is_nilpotent`
#### Estimated changes
Modified src/algebra/lie/abelian.lean
- \+ *lemma* lie_module.le_max_triv_iff_bracket_eq_bot

Modified src/algebra/lie/ideal_operations.lean
- \+ *lemma* lie_submodule.lie_eq_bot_iff

Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* lie_module.antitone_lower_central_series
- \+ *lemma* lie_module.lower_central_series_last_le_max_triv
- \+ *lemma* lie_module.nilpotency_length_eq_succ_iff
- \+ *lemma* lie_module.nilpotency_length_eq_zero_iff
- \+ *lemma* lie_module.nontrivial_lower_central_series_last
- \+ *lemma* lie_module.nontrivial_max_triv_of_is_nilpotent

Modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_submodule.lie_span_eq_bot_iff
- \+ *lemma* lie_submodule.nontrivial_iff_ne_bot

Modified src/data/set/basic.lean
- \+ *theorem* set.nontrivial_mono



## [2022-01-18 10:53:40](https://github.com/leanprover-community/mathlib/commit/a0da4f1)
feat(algebra/big_operators/basic): Reindexing a product with a permutation ([#11344](https://github.com/leanprover-community/mathlib/pull/11344))
This proves `(∏ x in s, f (σ x)) = ∏ x in s, f x` for a permutation `σ`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* equiv.perm.prod_comp'
- \+ *lemma* equiv.perm.prod_comp

Modified src/data/finset/basic.lean
- \+ *lemma* finset.map_perm

Modified src/data/finset/card.lean
- \+ *lemma* finset.map_eq_of_subset

Modified src/linear_algebra/matrix/determinant.lean


Modified src/number_theory/sum_four_squares.lean




## [2022-01-18 09:14:43](https://github.com/leanprover-community/mathlib/commit/8d5caba)
chore(order/bounded_order): golf ([#11538](https://github.com/leanprover-community/mathlib/pull/11538))
#### Estimated changes
Modified src/order/bounded_order.lean
- \+/\- *lemma* bot_lt_iff_ne_bot
- \+ *lemma* bot_unique
- \- *theorem* bot_unique
- \+ *lemma* eq_bot_iff
- \- *theorem* eq_bot_iff
- \+ *lemma* eq_bot_mono
- \- *theorem* eq_bot_mono
- \+/\- *lemma* eq_bot_of_minimal
- \+/\- *lemma* eq_bot_or_bot_lt
- \+ *lemma* eq_top_iff
- \- *theorem* eq_top_iff
- \+ *lemma* eq_top_mono
- \- *theorem* eq_top_mono
- \+/\- *lemma* eq_top_or_lt_top
- \+ *lemma* le_bot_iff
- \- *theorem* le_bot_iff
- \+/\- *lemma* ne_bot_of_gt
- \+ *lemma* ne_bot_of_le_ne_bot
- \- *theorem* ne_bot_of_le_ne_bot
- \+ *lemma* ne_top_of_le_ne_top
- \- *theorem* ne_top_of_le_ne_top
- \+/\- *lemma* ne_top_of_lt
- \+ *lemma* top_le_iff
- \- *theorem* top_le_iff
- \+ *lemma* top_unique
- \- *theorem* top_unique



## [2022-01-18 09:14:41](https://github.com/leanprover-community/mathlib/commit/a217b9c)
feat(measure_theory): drop some `measurable_set` assumptions ([#11536](https://github.com/leanprover-community/mathlib/pull/11536))
* make `exists_subordinate_pairwise_disjoint` work for `null_measurable_set`s;
* use `ae_disjoint` in `measure_Union₀`, drop `measure_Union_of_null_inter`;
* prove `measure_inter_add_diff` for `null_measurable_set`s;
* drop some `measurable_set` assumptions in `measure_union`, `measure_diff`, etc;
* golf.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/covering/besicovitch.lean


Modified src/measure_theory/decomposition/jordan.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/decomposition/radon_nikodym.lean


Modified src/measure_theory/function/continuous_map_dense.lean


Modified src/measure_theory/group/fundamental_domain.lean


Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_theory.weighted_smul_union'

Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/set_integral.lean
- \+/\- *lemma* measure_theory.integral_diff
- \+/\- *lemma* measure_theory.integral_union
- \+/\- *lemma* measure_theory.integral_union_ae

Modified src/measure_theory/measure/ae_disjoint.lean
- \+ *lemma* measure_theory.ae_disjoint.diff_ae_eq_left
- \+ *lemma* measure_theory.ae_disjoint.diff_ae_eq_right
- \+ *lemma* measure_theory.ae_disjoint.measure_diff_left
- \+ *lemma* measure_theory.ae_disjoint.measure_diff_right

Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean
- \- *lemma* measure_theory.exists_subordinate_pairwise_disjoint
- \+ *lemma* measure_theory.measure.restrict_union'
- \+/\- *lemma* measure_theory.measure.restrict_union
- \+ *lemma* measure_theory.measure.restrict_union_add_inter'
- \+ *lemma* measure_theory.measure.restrict_union_add_inter₀
- \- *lemma* measure_theory.measure.restrict_union_apply
- \+ *lemma* measure_theory.measure.restrict_union₀
- \- *lemma* measure_theory.measure_Union_of_null_inter
- \+/\- *lemma* measure_theory.measure_diff
- \+ *lemma* measure_theory.measure_diff_add_inter
- \+/\- *lemma* measure_theory.measure_diff_le_iff_le_add
- \+/\- *lemma* measure_theory.measure_diff_lt_of_lt_add
- \+/\- *lemma* measure_theory.measure_eq_measure_of_null_diff
- \+ *lemma* measure_theory.measure_union'
- \+/\- *lemma* measure_theory.measure_union

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* measure_theory.diff_null_ae_eq_self

Modified src/measure_theory/measure/null_measurable.lean
- \+ *lemma* measure_theory.exists_subordinate_pairwise_disjoint
- \+ *lemma* measure_theory.measure_inter_add_diff₀
- \+ *lemma* measure_theory.measure_union_add_inter₀'
- \+ *lemma* measure_theory.measure_union_add_inter₀
- \+ *lemma* measure_theory.measure_union₀'
- \+/\- *lemma* measure_theory.measure_union₀
- \+ *lemma* measure_theory.measure_union₀_aux

Modified src/measure_theory/measure/regular.lean
- \+/\- *lemma* measurable_set.exists_is_closed_lt_add
- \+/\- *lemma* measurable_set.exists_is_compact_lt_add
- \+/\- *lemma* measurable_set.exists_is_open_diff_lt
- \+/\- *lemma* measurable_set.exists_lt_is_compact_of_ne_top
- \+/\- *lemma* measurable_set.measure_eq_supr_is_closed_of_ne_top
- \+/\- *lemma* measurable_set.measure_eq_supr_is_compact_of_ne_top
- \+/\- *lemma* measure_theory.measure.inner_regular.measurable_set_of_open
- \+/\- *lemma* measure_theory.measure.regular.inner_regular_measurable
- \+/\- *lemma* measure_theory.measure.weakly_regular.inner_regular_measurable

Modified src/measure_theory/measure/stieltjes.lean




## [2022-01-18 09:14:39](https://github.com/leanprover-community/mathlib/commit/f23c00f)
chore(algebra/order/ring): move lemmas about invertible into a new file ([#11511](https://github.com/leanprover-community/mathlib/pull/11511))
The motivation here is to eventually be able to use the `one_pow` lemma in `algebra.group.units`. This is one very small step in that direction.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean


Added src/algebra/order/invertible.lean
- \+ *lemma* inv_of_le_one
- \+ *lemma* inv_of_lt_zero
- \+ *lemma* inv_of_nonneg
- \+ *lemma* inv_of_nonpos
- \+ *lemma* inv_of_pos

Modified src/algebra/order/ring.lean
- \- *lemma* inv_of_le_one
- \- *lemma* inv_of_lt_zero
- \- *lemma* inv_of_nonneg
- \- *lemma* inv_of_nonpos
- \- *lemma* inv_of_pos

Modified src/analysis/convex/basic.lean


Modified src/linear_algebra/affine_space/ordered.lean




## [2022-01-18 07:45:51](https://github.com/leanprover-community/mathlib/commit/01fa7f5)
feat(data/fintype/basic): `one_lt_card_iff` and `two_lt_card_iff` ([#11524](https://github.com/leanprover-community/mathlib/pull/11524))
This PR adds `one_lt_card_iff` and `two_lt_card_iff`.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.one_lt_card_iff
- \+ *lemma* fintype.two_lt_card_iff



## [2022-01-18 07:09:41](https://github.com/leanprover-community/mathlib/commit/e895c8f)
chore(cone_category): generalize universes ([#11539](https://github.com/leanprover-community/mathlib/pull/11539))
#### Estimated changes
Modified src/category_theory/limits/cone_category.lean
- \+/\- *def* category_theory.limits.is_colimit.of_preserves_cocone_initial
- \+/\- *def* category_theory.limits.is_colimit.of_reflects_cocone_initial
- \+/\- *def* category_theory.limits.is_limit.of_preserves_cone_terminal
- \+/\- *def* category_theory.limits.is_limit.of_reflects_cone_terminal



## [2022-01-18 03:54:41](https://github.com/leanprover-community/mathlib/commit/813a191)
chore(logic/basic): Make higher `forall_congr`/`exists_congr` lemmas dependent ([#11490](https://github.com/leanprover-community/mathlib/pull/11490))
Currently, `forall₂_congr` and friends take as arguments non dependent propositions like `p q : α → β → Prop`. This prevents them being useful virtually anywhere as most often foralls are nested like `∀ a, a ∈ s → ...` and `a ∈ s` depends on `a`.
This PR turns them into `Π a, β a → Prop` (and similar for higher arities).
As a bonus, it adds the `5`-ary version and golfs all occurrences of nested `forall_congr`s.
#### Estimated changes
Modified src/algebra/associated.lean


Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/box_integral/basic.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/star.lean


Modified src/analysis/normed/group/quotient.lean


Modified src/category_theory/sites/sheaf.lean


Modified src/combinatorics/additive/salem_spencer.lean


Modified src/data/multiset/basic.lean


Modified src/data/set/function.lean


Modified src/data/set/prod.lean


Modified src/geometry/manifold/diffeomorph.lean


Modified src/logic/basic.lean
- \+/\- *lemma* exists₂_congr
- \+/\- *lemma* exists₃_congr
- \+/\- *lemma* exists₄_congr
- \+ *lemma* exists₅_congr
- \+/\- *lemma* forall₂_congr
- \+/\- *lemma* forall₃_congr
- \+/\- *lemma* forall₄_congr
- \+ *lemma* forall₅_congr

Modified src/measure_theory/group/basic.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/order/complete_lattice.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean


Modified src/order/filter/lift.lean


Modified src/order/sup_indep.lean


Modified src/ring_theory/local_properties.lean


Modified src/topology/algebra/mul_action.lean
- \+/\- *lemma* continuous_on_const_smul_iff

Modified src/topology/algebra/uniform_group.lean


Modified src/topology/local_homeomorph.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/separation.lean


Modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/compact_convergence.lean


Modified src/topology/uniform_space/separation.lean


Modified src/topology/uniform_space/uniform_convergence.lean




## [2022-01-18 00:10:59](https://github.com/leanprover-community/mathlib/commit/99e9036)
chore(algebra/algebra/subalgebra): lemmas about top and injectivity ([#11514](https://github.com/leanprover-community/mathlib/pull/11514))
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* algebra.to_submodule_eq_top
- \+ *lemma* algebra.to_subring_eq_top
- \+ *lemma* algebra.to_subsemiring_eq_top
- \+ *lemma* algebra.top_to_subring
- \+ *theorem* subalgebra.to_subring_inj
- \+ *theorem* subalgebra.to_subring_injective
- \+ *theorem* subalgebra.to_subsemiring_inj
- \+ *theorem* subalgebra.to_subsemiring_injective



## [2022-01-17 23:42:43](https://github.com/leanprover-community/mathlib/commit/1e4da8d)
refactor(linear_algebra/{tensor,exterior}_algebra): convert to a directory ([#11513](https://github.com/leanprover-community/mathlib/pull/11513))
These files can be quite slow, so it's useful to be able to add new definitions and lemmas in standalone files, rather than in the same file.
There are a number of open PRs of mine that make this move as part of a new feature, so let's just move them pre-emptively.
#### Estimated changes
Modified src/algebra/lie/universal_enveloping.lean


Modified src/linear_algebra/clifford_algebra/basic.lean


Renamed src/linear_algebra/exterior_algebra.lean to src/linear_algebra/exterior_algebra/basic.lean


Renamed src/linear_algebra/tensor_algebra.lean to src/linear_algebra/tensor_algebra/basic.lean


Modified test/free_algebra.lean




## [2022-01-17 22:39:19](https://github.com/leanprover-community/mathlib/commit/5b36c86)
feat(analysis/normed_space/finite_dimension): the determinant is continuous on the space of continuous linear maps ([#11526](https://github.com/leanprover-community/mathlib/pull/11526))
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* continuous_linear_map.continuous_det

Modified src/linear_algebra/determinant.lean
- \+ *lemma* linear_equiv.coe_of_is_unit_det

Modified src/topology/algebra/module/basic.lean




## [2022-01-17 22:11:44](https://github.com/leanprover-community/mathlib/commit/4072512)
feat(src/group_theory/nilpotent): solvable_of_nilpotent ([#11512](https://github.com/leanprover-community/mathlib/pull/11512))
following the proof on
<https://groupprops.subwiki.org/wiki/Nilpotent_implies_solvable>
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* derived_le_lower_central



## [2022-01-17 21:04:13](https://github.com/leanprover-community/mathlib/commit/274b530)
feat(data/equiv/basic): add `add_equiv.to_int_linear_equiv` ([#11456](https://github.com/leanprover-community/mathlib/pull/11456))
as written by @adamtopaz on [zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/injections.20to.20equiv/near/268038978)
#### Estimated changes
Modified src/data/equiv/module.lean
- \+ *lemma* add_equiv.coe_to_int_linear_equiv
- \+ *lemma* add_equiv.coe_to_linear_equiv
- \+ *lemma* add_equiv.coe_to_linear_equiv_symm
- \+ *lemma* add_equiv.coe_to_nat_linear_equiv
- \+ *def* add_equiv.to_int_linear_equiv
- \+ *lemma* add_equiv.to_int_linear_equiv_refl
- \+ *lemma* add_equiv.to_int_linear_equiv_symm
- \+ *lemma* add_equiv.to_int_linear_equiv_to_add_equiv
- \+ *lemma* add_equiv.to_int_linear_equiv_trans
- \+ *def* add_equiv.to_linear_equiv
- \+ *def* add_equiv.to_nat_linear_equiv
- \+ *lemma* add_equiv.to_nat_linear_equiv_refl
- \+ *lemma* add_equiv.to_nat_linear_equiv_symm
- \+ *lemma* add_equiv.to_nat_linear_equiv_to_add_equiv
- \+ *lemma* add_equiv.to_nat_linear_equiv_trans
- \+ *lemma* linear_equiv.to_add_equiv_to_int_linear_equiv
- \+ *lemma* linear_equiv.to_add_equiv_to_nat_linear_equiv

Modified src/linear_algebra/basic.lean
- \- *lemma* add_equiv.coe_to_linear_equiv
- \- *lemma* add_equiv.coe_to_linear_equiv_symm
- \- *def* add_equiv.to_linear_equiv



## [2022-01-17 19:54:14](https://github.com/leanprover-community/mathlib/commit/1fbef63)
feat(order/filter): add two lemmas ([#11519](https://github.com/leanprover-community/mathlib/pull/11519))
Two easy lemmas (from the sphere eversion project) and some minor style changes.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.eventually_ne_at_top

Modified src/order/filter/basic.lean
- \+ *lemma* filter.diff_mem
- \+/\- *lemma* filter.inter_mem
- \+/\- *lemma* filter.inter_mem_iff
- \+/\- *lemma* filter.mem_of_superset



## [2022-01-17 19:54:13](https://github.com/leanprover-community/mathlib/commit/e096b99)
refactor(set_theory/ordinal_arithmetic): Rename `power` to `opow` ([#11279](https://github.com/leanprover-community/mathlib/pull/11279))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.add_lt_omega_opow
- \- *theorem* ordinal.add_lt_omega_power
- \+ *theorem* ordinal.add_omega_opow
- \- *theorem* ordinal.add_omega_power
- \+ *theorem* ordinal.le_opow_self
- \- *theorem* ordinal.le_power_self
- \+ *theorem* ordinal.log_opow
- \+ *theorem* ordinal.log_opow_mul_add
- \- *theorem* ordinal.log_power
- \- *theorem* ordinal.log_power_mul_add
- \+ *theorem* ordinal.lt_opow_of_limit
- \+ *theorem* ordinal.lt_opow_succ_log
- \- *theorem* ordinal.lt_power_of_limit
- \- *theorem* ordinal.lt_power_succ_log
- \+ *theorem* ordinal.mul_lt_omega_opow
- \- *theorem* ordinal.mul_lt_omega_power
- \+ *theorem* ordinal.mul_omega_opow_opow
- \- *theorem* ordinal.mul_omega_power_power
- \+ *theorem* ordinal.nat_cast_opow
- \- *theorem* ordinal.nat_cast_power
- \+ *theorem* ordinal.one_opow
- \- *theorem* ordinal.one_power
- \+ *def* ordinal.opow
- \+ *theorem* ordinal.opow_add
- \+ *theorem* ordinal.opow_dvd_opow
- \+ *theorem* ordinal.opow_dvd_opow_iff
- \+ *theorem* ordinal.opow_is_limit
- \+ *theorem* ordinal.opow_is_limit_left
- \+ *theorem* ordinal.opow_is_normal
- \+ *theorem* ordinal.opow_le_of_limit
- \+ *theorem* ordinal.opow_le_opow_iff_right
- \+ *theorem* ordinal.opow_le_opow_left
- \+ *theorem* ordinal.opow_le_opow_right
- \+ *theorem* ordinal.opow_limit
- \+ *theorem* ordinal.opow_log_le
- \+ *theorem* ordinal.opow_lt_omega
- \+ *theorem* ordinal.opow_lt_opow_iff_right
- \+ *theorem* ordinal.opow_lt_opow_left_of_succ
- \+ *theorem* ordinal.opow_mul
- \+ *lemma* ordinal.opow_mul_add_lt_opow_mul_succ
- \+ *lemma* ordinal.opow_mul_add_lt_opow_succ
- \+ *lemma* ordinal.opow_mul_add_pos
- \+ *theorem* ordinal.opow_ne_zero
- \+ *theorem* ordinal.opow_omega
- \+ *theorem* ordinal.opow_one
- \+ *theorem* ordinal.opow_pos
- \+ *theorem* ordinal.opow_right_inj
- \+ *theorem* ordinal.opow_succ
- \+ *theorem* ordinal.opow_zero
- \- *def* ordinal.power
- \- *theorem* ordinal.power_add
- \- *theorem* ordinal.power_dvd_power
- \- *theorem* ordinal.power_dvd_power_iff
- \- *theorem* ordinal.power_is_limit
- \- *theorem* ordinal.power_is_limit_left
- \- *theorem* ordinal.power_is_normal
- \- *theorem* ordinal.power_le_of_limit
- \- *theorem* ordinal.power_le_power_iff_right
- \- *theorem* ordinal.power_le_power_left
- \- *theorem* ordinal.power_le_power_right
- \- *theorem* ordinal.power_limit
- \- *theorem* ordinal.power_log_le
- \- *theorem* ordinal.power_lt_omega
- \- *theorem* ordinal.power_lt_power_iff_right
- \- *theorem* ordinal.power_lt_power_left_of_succ
- \- *theorem* ordinal.power_mul
- \- *lemma* ordinal.power_mul_add_lt_power_mul_succ
- \- *lemma* ordinal.power_mul_add_lt_power_succ
- \- *lemma* ordinal.power_mul_add_pos
- \- *theorem* ordinal.power_ne_zero
- \- *theorem* ordinal.power_omega
- \- *theorem* ordinal.power_one
- \- *theorem* ordinal.power_pos
- \- *theorem* ordinal.power_right_inj
- \- *theorem* ordinal.power_succ
- \- *theorem* ordinal.power_zero
- \+ *theorem* ordinal.zero_opow'
- \+ *theorem* ordinal.zero_opow
- \- *theorem* ordinal.zero_power'
- \- *theorem* ordinal.zero_power

Modified src/set_theory/ordinal_notation.lean
- \+ *def* nonote.opow
- \- *def* nonote.power
- \+ *theorem* nonote.repr_opow
- \- *theorem* nonote.repr_power
- \+ *theorem* onote.NF.of_dvd_omega_opow
- \- *theorem* onote.NF.of_dvd_omega_power
- \+ *def* onote.opow
- \+ *def* onote.opow_aux
- \+ *theorem* onote.opow_def
- \- *def* onote.power
- \- *def* onote.power_aux
- \- *theorem* onote.power_def
- \+ *theorem* onote.repr_opow
- \+ *theorem* onote.repr_opow_aux₁
- \+ *theorem* onote.repr_opow_aux₂
- \- *theorem* onote.repr_power
- \- *theorem* onote.repr_power_aux₁
- \- *theorem* onote.repr_power_aux₂
- \+ *theorem* onote.scale_opow_aux
- \- *theorem* onote.scale_power_aux



## [2022-01-17 19:08:49](https://github.com/leanprover-community/mathlib/commit/2a8a01b)
chore(measure_theory/integral/bochner): use set_to_fun lemmas to prove integral properties ([#10717](https://github.com/leanprover-community/mathlib/pull/10717))
#### Estimated changes
Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_theory.weighted_smul_nonneg
- \+ *lemma* measure_theory.weighted_smul_smul_measure



## [2022-01-17 15:56:24](https://github.com/leanprover-community/mathlib/commit/905871f)
feat(analysis/normed_space/spectrum): an algebra homomorphism into the base field is bounded ([#11494](https://github.com/leanprover-community/mathlib/pull/11494))
We prove basic facts about `φ : A →ₐ[𝕜] 𝕜` when `A` is a Banach algebra, namely that `φ` maps elements of `A` to their spectrum, and that `φ` is bounded.
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean
- \+ *lemma* alg_hom.apply_mem_spectrum

Modified src/analysis/normed_space/spectrum.lean
- \+ *lemma* alg_hom.continuous
- \+ *def* alg_hom.to_continuous_linear_map
- \+ *lemma* alg_hom.to_continuous_linear_map_norm

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ring_hom.ker_ne_top



## [2022-01-17 15:10:20](https://github.com/leanprover-community/mathlib/commit/4e31396)
feat(measure_theory/measure): define `ae_disjoint` ([#11500](https://github.com/leanprover-community/mathlib/pull/11500))
I am going to migrate most `disjoint` assumptions to `ae_disjoint`.
#### Estimated changes
Added src/measure_theory/measure/ae_disjoint.lean
- \+ *lemma* disjoint.ae_disjoint
- \+ *lemma* measure_theory.ae_disjoint.Union_left_iff
- \+ *lemma* measure_theory.ae_disjoint.Union_right_iff
- \+ *lemma* measure_theory.ae_disjoint.exists_disjoint_diff
- \+ *lemma* measure_theory.ae_disjoint.mono
- \+ *lemma* measure_theory.ae_disjoint.mono_ae
- \+ *lemma* measure_theory.ae_disjoint.of_null_left
- \+ *lemma* measure_theory.ae_disjoint.of_null_right
- \+ *lemma* measure_theory.ae_disjoint.union_left
- \+ *lemma* measure_theory.ae_disjoint.union_left_iff
- \+ *lemma* measure_theory.ae_disjoint.union_right
- \+ *lemma* measure_theory.ae_disjoint.union_right_iff
- \+ *def* measure_theory.ae_disjoint
- \+ *lemma* measure_theory.exists_null_pairwise_disjoint_diff

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* measure_theory.measure_mono_null_ae



## [2022-01-17 14:43:23](https://github.com/leanprover-community/mathlib/commit/50bdb29)
feat(analysis/complex/cauchy_integral): review docs, add versions without `off_countable` ([#11417](https://github.com/leanprover-community/mathlib/pull/11417))
#### Estimated changes
Modified src/analysis/complex/cauchy_integral.lean
- \+ *lemma* complex.circle_integral_sub_inv_smul_of_continuous_on_of_differentiable_on
- \+ *lemma* complex.circle_integral_sub_inv_smul_of_differentiable_on
- \+ *lemma* complex.has_fpower_series_on_ball_of_continuous_on_of_differentiable_on
- \+ *lemma* complex.integral_boundary_rect_eq_zero_of_continuous_on_of_differentiable_on
- \+ *lemma* complex.integral_boundary_rect_eq_zero_of_differentiable_on
- \+ *lemma* complex.integral_boundary_rect_of_continuous_on_of_has_fderiv_at_real
- \+ *lemma* complex.integral_boundary_rect_of_differentiable_on_real
- \+ *lemma* complex.integral_boundary_rect_of_has_fderiv_at_real_off_countable
- \- *lemma* complex.integral_boundary_rect_of_has_fderiv_within_at_real_off_countable

Modified src/analysis/complex/re_im_topology.lean
- \+ *lemma* is_closed.re_prod_im
- \+ *lemma* is_open.re_prod_im



## [2022-01-17 11:46:31](https://github.com/leanprover-community/mathlib/commit/391bd21)
doc(src/data/equiv/transfer_instances): nontrivial, not nonzero ([#11508](https://github.com/leanprover-community/mathlib/pull/11508))
small docs typo, it seems.
#### Estimated changes
Modified src/data/equiv/transfer_instance.lean




## [2022-01-17 10:14:51](https://github.com/leanprover-community/mathlib/commit/6b475a4)
feat(data/finset/basic): `finset.two_lt_card` ([#11505](https://github.com/leanprover-community/mathlib/pull/11505))
This PR adds lemmas `finset.two_lt_card` and `finset.two_lt_card_iff`, similar to `finset.one_lt_card` and `finset.one_lt_card_iff`.
These lemmas are also similar to `finset.card_eq_three`.
#### Estimated changes
Modified src/data/finset/card.lean
- \+ *lemma* finset.two_lt_card
- \+ *lemma* finset.two_lt_card_iff



## [2022-01-17 10:14:50](https://github.com/leanprover-community/mathlib/commit/079fb16)
feat(analysis/special_functions/complex/arg): `arg_neg` lemmas ([#11503](https://github.com/leanprover-community/mathlib/pull/11503))
Add lemmas about the value of `arg (-x)`: one each for positive and
negative sign of `x.im`, two `iff` lemmas saying exactly when it's
equal to `arg x - π` or `arg x + π`, and a simpler lemma giving the
value of `(arg (-x) : real.angle)` for any nonzero `x`.
These replace the previous lemmas
`arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg` and
`arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg`, which are strictly less
general (they have a hypothesis `x.re < 0` that's not needed unless
the imaginary part is 0).  Those two lemmas are unused in current
mathlib (they were used in the proof of `cos_arg` before the golfing
in [#10365](https://github.com/leanprover-community/mathlib/pull/10365)) and it seems reasonable to me to replace them with the more
general lemmas.
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \- *lemma* complex.arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg
- \- *lemma* complex.arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg
- \+ *lemma* complex.arg_neg_coe_angle
- \+ *lemma* complex.arg_neg_eq_arg_add_pi_iff
- \+ *lemma* complex.arg_neg_eq_arg_add_pi_of_im_neg
- \+ *lemma* complex.arg_neg_eq_arg_sub_pi_iff
- \+ *lemma* complex.arg_neg_eq_arg_sub_pi_of_im_pos



## [2022-01-17 10:14:49](https://github.com/leanprover-community/mathlib/commit/1c56a8d)
feat(order/well_founded_set): Antichains in a partial well order are finite ([#11286](https://github.com/leanprover-community/mathlib/pull/11286))
and when the relation is reflexive and symmetric, it's actually an equivalent condition.
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* set.finite.exists_lt_map_eq_of_range_subset

Modified src/order/well_founded_set.lean
- \+ *lemma* finset.partially_well_ordered_on
- \- *theorem* finset.partially_well_ordered_on
- \+ *lemma* is_antichain.finite_of_partially_well_ordered_on
- \+ *lemma* is_antichain.partially_well_ordered_on_iff
- \+ *lemma* set.finite.partially_well_ordered_on
- \+ *lemma* set.partially_well_ordered_on_iff_finite_antichains



## [2022-01-17 08:42:46](https://github.com/leanprover-community/mathlib/commit/0d5bfd7)
feat(*): add a few lemmas about `function.extend` ([#11498](https://github.com/leanprover-community/mathlib/pull/11498))
I'm going to use `function.extend` as another way to get from
`[encodable ι] (s : ι → set α)` to `t : ℕ → set α` in measure theory.
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *lemma* function.apply_extend

Modified src/order/complete_lattice.lean
- \+ *theorem* supr_extend_bot

Modified src/order/directed.lean
- \+ *lemma* directed.extend_bot



## [2022-01-17 08:42:45](https://github.com/leanprover-community/mathlib/commit/9b70cc6)
feat(data/equiv/encodable): add a few lemmas ([#11497](https://github.com/leanprover-community/mathlib/pull/11497))
* add `simp` lemmas `encodable.encode_inj` and
  `encodable.decode₂_encode`;
* add `encodable.decode₂_eq_some`;
* avoid non-final `simp` in the proof of `encodable.Union_decode₂_disjoint_on`.
#### Estimated changes
Modified src/data/equiv/encodable/basic.lean
- \+ *lemma* encodable.decode₂_encode
- \+ *theorem* encodable.decode₂_eq_some
- \+ *lemma* encodable.encode_inj

Modified src/data/equiv/encodable/lattice.lean




## [2022-01-17 08:42:44](https://github.com/leanprover-community/mathlib/commit/ac76eb3)
feat(algebra/star/unitary): lemmas about group_with_zero ([#11493](https://github.com/leanprover-community/mathlib/pull/11493))
#### Estimated changes
Modified src/algebra/star/unitary.lean
- \+ *lemma* unitary.coe_div
- \+ *lemma* unitary.coe_inv
- \+ *lemma* unitary.coe_zpow
- \+ *lemma* unitary.mem_iff
- \+ *lemma* unitary.mem_iff_self_mul_star
- \+ *lemma* unitary.mem_iff_star_mul_self
- \+ *def* unitary.to_units
- \+ *lemma* unitary.to_units_injective



## [2022-01-17 08:42:43](https://github.com/leanprover-community/mathlib/commit/a88ae0c)
refactor(data/set/lattice): Generalize `mem_bUnion_iff` and `mem_bInter_iff` to dependent families ([#11485](https://github.com/leanprover-community/mathlib/pull/11485))
They're now called `mem_Union₂` and `mem_Inter₂`.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/lie/subalgebra.lean


Modified src/algebra/lie/submodule.lean


Modified src/algebra/module/submodule_lattice.lean


Modified src/algebra/support.lean


Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/analysis/box_integral/partition/basic.lean
- \+/\- *lemma* box_integral.prepartition.mem_Union

Modified src/analysis/box_integral/partition/split.lean


Modified src/analysis/box_integral/partition/tagged.lean
- \+/\- *lemma* box_integral.tagged_prepartition.disj_union_boxes
- \+/\- *lemma* box_integral.tagged_prepartition.mem_Union

Modified src/analysis/convex/cone.lean
- \+/\- *lemma* convex_cone.mem_Inf

Modified src/analysis/convex/extreme.lean


Modified src/analysis/convex/simplicial_complex/basic.lean
- \+/\- *lemma* geometry.simplicial_complex.mem_space_iff

Modified src/data/finset/basic.lean


Modified src/data/semiquot.lean


Modified src/data/set/accumulate.lean


Modified src/data/set/lattice.lean
- \+ *theorem* set.mem_Inter₂
- \+ *theorem* set.mem_Union₂
- \- *theorem* set.mem_bInter_iff
- \- *lemma* set.mem_bUnion_iff'
- \- *theorem* set.mem_bUnion_iff

Modified src/data/set/pairwise.lean


Modified src/dynamics/ergodic/conservative.lean


Modified src/group_theory/subgroup/basic.lean
- \+/\- *lemma* subgroup.mem_Inf

Modified src/group_theory/submonoid/basic.lean
- \+/\- *lemma* submonoid.mem_Inf

Modified src/linear_algebra/affine_space/affine_subspace.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* submodule.mem_span

Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/covering/besicovitch.lean


Modified src/measure_theory/covering/vitali.lean


Modified src/model_theory/basic.lean
- \+/\- *lemma* first_order.language.substructure.mem_Inf

Modified src/order/filter/basic.lean


Modified src/order/ideal.lean


Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/subring/basic.lean
- \+/\- *lemma* subring.mem_Inf

Modified src/ring_theory/subsemiring/basic.lean
- \+/\- *lemma* subsemiring.mem_Inf

Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/compact_open.lean


Modified src/topology/continuous_function/bounded.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/paracompact.lean


Modified src/topology/separation.lean


Modified src/topology/sequences.lean


Modified src/topology/shrinking_lemma.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean




## [2022-01-17 07:55:11](https://github.com/leanprover-community/mathlib/commit/83eff32)
feat(topology/metric_space): more lemmas about disjoint balls ([#11506](https://github.com/leanprover-community/mathlib/pull/11506))
* drop unused lemmas `metric.ball_disjoint` and
  `metric.ball_disjoint_same`; the former was a duplicate of
  `metric.ball_disjoint_ball`;
* add `metric.closed_ball_disjoint_ball`, `metric.closed_ball_disjoint_closed_ball`.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \- *theorem* metric.ball_disjoint
- \- *theorem* metric.ball_disjoint_same
- \+ *lemma* metric.closed_ball_disjoint_ball
- \+ *lemma* metric.closed_ball_disjoint_closed_ball



## [2022-01-17 07:55:09](https://github.com/leanprover-community/mathlib/commit/2f342b8)
feat(measure_theory): generalize some lemmas to `outer_measure` ([#11501](https://github.com/leanprover-community/mathlib/pull/11501))
#### Estimated changes
Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* measure_theory.measure_union_eq_top_iff
- \+/\- *lemma* measure_theory.measure_union_lt_top_iff
- \+/\- *lemma* measure_theory.measure_union_null_iff

Modified src/measure_theory/measure/outer_measure.lean
- \+/\- *lemma* measure_theory.outer_measure.Union_null
- \+ *lemma* measure_theory.outer_measure.Union_null_iff
- \+ *lemma* measure_theory.outer_measure.bUnion_null_iff
- \+ *theorem* measure_theory.outer_measure.mono_null
- \+ *lemma* measure_theory.outer_measure.sUnion_null_iff
- \+ *lemma* measure_theory.outer_measure.univ_eq_zero_iff



## [2022-01-17 07:20:57](https://github.com/leanprover-community/mathlib/commit/43bbaee)
feat(measure_theory/measure): add lemmas, drop `measurable_set` assumptions ([#11499](https://github.com/leanprover-community/mathlib/pull/11499))
* `restrict_eq_self` no longer requires measurability of either set;
* `restrict_apply_self` no longer requires measurability of the set;
* add `restrict_apply_superset` and `restrict_restrict_of_subset` ;
* add `restrict_restrict'` that assumes measurability of the other
  set, drop one `measurable_set` assumption in `restrict_comm`;
* drop measurability assumptions in `restrict_congr_mono`.
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/measure/lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.measure.restrict_apply_self
- \+ *lemma* measure_theory.measure.restrict_apply_superset
- \+/\- *lemma* measure_theory.measure.restrict_comm
- \+/\- *lemma* measure_theory.measure.restrict_congr_mono
- \- *lemma* measure_theory.measure.restrict_eq_self'
- \+/\- *lemma* measure_theory.measure.restrict_eq_self
- \+ *lemma* measure_theory.measure.restrict_restrict'
- \+ *lemma* measure_theory.measure.restrict_restrict_of_subset



## [2022-01-17 00:42:46](https://github.com/leanprover-community/mathlib/commit/6d19eba)
feat(*): add to_sub* lemmas for `map`, `fg` ([#11480](https://github.com/leanprover-community/mathlib/pull/11480))
From flt-regular.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* subalgebra.map_to_submodule
- \+ *lemma* subalgebra.map_to_subsemiring

Modified src/ring_theory/noetherian.lean
- \+ *lemma* subalgebra.fg_bot_to_submodule



## [2022-01-16 23:52:06](https://github.com/leanprover-community/mathlib/commit/4ed7316)
feat(analysis/special_functions/pow): tendsto rpow lemma for ennreals ([#11475](https://github.com/leanprover-community/mathlib/pull/11475))
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* ennreal.continuous_rpow_const
- \+ *lemma* filter.tendsto.ennrpow_const



## [2022-01-16 23:11:56](https://github.com/leanprover-community/mathlib/commit/2c2338e)
chore(data/complex/basic): add of_real_eq_one ([#11496](https://github.com/leanprover-community/mathlib/pull/11496))
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *theorem* complex.of_real_eq_one
- \+ *theorem* complex.of_real_ne_one



## [2022-01-16 23:11:54](https://github.com/leanprover-community/mathlib/commit/1f6bbf9)
feat(analysis/special_functions/complex/arg): `arg_conj`, `arg_inv` lemmas ([#11479](https://github.com/leanprover-community/mathlib/pull/11479))
Add lemmas giving the values of `arg (conj x)` and `arg x⁻¹`, both for
`arg` as a real number and `arg` coerced to `real.angle` (the latter
function being better behaved because it avoids case distinctions
around getting a result into the interval (-π, π]).
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* complex.arg_conj
- \+ *lemma* complex.arg_conj_coe_angle
- \+ *lemma* complex.arg_inv
- \+ *lemma* complex.arg_inv_coe_angle



## [2022-01-16 22:44:43](https://github.com/leanprover-community/mathlib/commit/f4b93c8)
feat(analysis/special_functions/trigonometric/angle): more 2π = 0 lemmas ([#11482](https://github.com/leanprover-community/mathlib/pull/11482))
Add some more lemmas useful for manipulation of `real.angle` expressions.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* real.angle.sub_coe_pi_eq_add_coe_pi
- \+ *lemma* real.angle.two_nsmul_coe_pi
- \+ *lemma* real.angle.two_zsmul_coe_pi



## [2022-01-16 22:07:26](https://github.com/leanprover-community/mathlib/commit/ed57bdd)
feat(number_field): notation for 𝓞 K, an algebra & ∈ 𝓞 K iff ([#11476](https://github.com/leanprover-community/mathlib/pull/11476))
From flt-regular.
#### Estimated changes
Modified src/number_theory/number_field.lean
- \+ *lemma* number_field.mem_ring_of_integers
- \+/\- *lemma* number_field.ring_of_integers.is_integral_coe



## [2022-01-16 21:15:07](https://github.com/leanprover-community/mathlib/commit/5f5bcd8)
feat(order/filter/ultrafilter): add some comap_inf_principal lemmas ([#11495](https://github.com/leanprover-community/mathlib/pull/11495))
...in the setting of ultrafilters
These lemmas are useful to prove e.g. that the continuous image of a
compact set is compact in the setting of convergence spaces.
#### Estimated changes
Modified src/order/filter/ultrafilter.lean
- \+ *lemma* ultrafilter.comap_inf_principal_ne_bot_of_image_mem
- \+ *lemma* ultrafilter.eq_of_le
- \+ *lemma* ultrafilter.of_comap_inf_principal_eq_of_map
- \+ *lemma* ultrafilter.of_comap_inf_principal_mem



## [2022-01-16 15:00:06](https://github.com/leanprover-community/mathlib/commit/d7f8f58)
feat(algebra/star/unitary): (re)define unitary elements of a star monoid ([#11457](https://github.com/leanprover-community/mathlib/pull/11457))
This PR defines `unitary R` for a star monoid `R` as the submonoid containing the elements that satisfy both `star U * U = 1` and `U * star U = 1`. We show basic properties (i.e. that this forms a group) and show that they
preserve the norm when `R` is a C* ring.
Note that this replaces `unitary_submonoid`, which only included the condition `star U * U = 1` -- see [the discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/unitary.20submonoid) on Zulip.
#### Estimated changes
Modified src/algebra/star/self_adjoint.lean


Added src/algebra/star/unitary.lean
- \+ *lemma* unitary.coe_mul_star_self
- \+ *lemma* unitary.coe_star
- \+ *lemma* unitary.coe_star_mul_self
- \+ *lemma* unitary.mul_star_self
- \+ *lemma* unitary.mul_star_self_of_mem
- \+ *lemma* unitary.star_eq_inv'
- \+ *lemma* unitary.star_eq_inv
- \+ *lemma* unitary.star_mem
- \+ *lemma* unitary.star_mem_iff
- \+ *lemma* unitary.star_mul_self
- \+ *lemma* unitary.star_mul_self_of_mem
- \+ *def* unitary

Modified src/analysis/normed_space/star.lean
- \+ *lemma* cstar_ring.norm_coe_unitary
- \+ *lemma* cstar_ring.norm_coe_unitary_mul
- \+ *lemma* cstar_ring.norm_mem_unitary_mul
- \+ *lemma* cstar_ring.norm_mul_coe_unitary
- \+ *lemma* cstar_ring.norm_mul_mem_unitary
- \+ *lemma* cstar_ring.norm_of_mem_unitary
- \+ *lemma* cstar_ring.norm_unitary_smul

Modified src/linear_algebra/unitary_group.lean
- \+/\- *lemma* matrix.unitary_group.star_mul_self
- \+ *abbreviation* matrix.unitary_group
- \- *def* matrix.unitary_group
- \- *lemma* matrix.unitary_submonoid.star_mem
- \- *lemma* matrix.unitary_submonoid.star_mem_iff
- \- *def* unitary_submonoid



## [2022-01-16 15:00:04](https://github.com/leanprover-community/mathlib/commit/1d1f384)
feat(analysis/calculus/dslope): define dslope ([#11432](https://github.com/leanprover-community/mathlib/pull/11432))
#### Estimated changes
Added src/analysis/calculus/dslope.lean
- \+ *lemma* continuous_at.of_dslope
- \+ *lemma* continuous_at_dslope_of_ne
- \+ *lemma* continuous_at_dslope_same
- \+ *lemma* continuous_on.of_dslope
- \+ *lemma* continuous_on_dslope
- \+ *lemma* continuous_within_at.of_dslope
- \+ *lemma* continuous_within_at_dslope_of_ne
- \+ *lemma* differentiable_at.of_dslope
- \+ *lemma* differentiable_at_dslope_of_ne
- \+ *lemma* differentiable_on.of_dslope
- \+ *lemma* differentiable_on_dslope_of_nmem
- \+ *lemma* differentiable_within_at.of_dslope
- \+ *lemma* differentiable_within_at_dslope_of_ne
- \+ *lemma* dslope_eventually_eq_slope_of_ne
- \+ *lemma* dslope_eventually_eq_slope_punctured_nhds
- \+ *lemma* dslope_of_ne
- \+ *lemma* dslope_same
- \+ *lemma* dslope_sub_smul
- \+ *lemma* dslope_sub_smul_of_ne
- \+ *lemma* eq_on_dslope_slope
- \+ *lemma* eq_on_dslope_sub_smul
- \+ *lemma* sub_smul_dslope



## [2022-01-16 13:30:27](https://github.com/leanprover-community/mathlib/commit/1aee8a8)
chore(*): Put `simp` attribute before `to_additive` ([#11488](https://github.com/leanprover-community/mathlib/pull/11488))
A few lemmas were tagged in the wrong order. As tags are applied from left to right, `@[to_additive, simp]` only marks the multiplicative lemma as `simp`. The correct order is thus `@[simp, to_additive]`.
#### Estimated changes
Modified src/algebra/group/opposite.lean
- \+/\- *lemma* mul_opposite.commute_op
- \+/\- *lemma* mul_opposite.commute_unop

Modified src/algebra/order/lattice_group.lean


Modified src/group_theory/submonoid/inverses.lean
- \+/\- *lemma* submonoid.from_left_inv_eq_inv
- \+/\- *lemma* submonoid.from_left_inv_left_inv_equiv_symm
- \+/\- *lemma* submonoid.from_left_inv_one
- \+/\- *lemma* submonoid.left_inv_equiv_symm_eq_inv
- \+/\- *lemma* submonoid.left_inv_equiv_symm_from_left_inv
- \+/\- *lemma* submonoid.left_inv_equiv_symm_mul
- \+/\- *lemma* submonoid.mul_left_inv_equiv_symm



## [2022-01-16 13:30:25](https://github.com/leanprover-community/mathlib/commit/02a4775)
refactor(analysis/normed_space): merge `normed_space` and `semi_normed_space` ([#8218](https://github.com/leanprover-community/mathlib/pull/8218))
There are no theorems which are true for `[normed_group M] [normed_space R M]` but not `[normed_group M] [semi_normed_space R M]`; so there is about as much value to the `semi_normed_space` / `normed_space` distinction as there was between `module` / `semimodule`. Since we eliminated `semimodule`, we should eliminte `semi_normed_space` too.
This relaxes the typeclass arguments of `normed_space` to make it a drop-in replacement for `semi_normed_space`; or viewed another way, this removes `normed_space` and renames `semi_normed_space` to replace it.
This does the same thing to `normed_algebra` and `seminormed_algebra`, but these are hardly used anyway.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/semi_normed_space.20vs.20normed_space/near/245089933)
As with any typeclass refactor, this randomly breaks elaboration in a few places; presumably, it was able to unify arguments from one particular typeclass path, but not from another. To fix this, some type ascriptions have to be added where previously none were needed. In a few rare cases, the elaborator gets so confused that we have to enter tactic mode to produce a term.
This isn't really a new problem - this PR just makes these issues all visible at once, whereas normally we'd only run into one or two at a time. Optimistically Lean 4 will fix all this, but we won't really know until we try.
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/normed_space/add_torsor.lean


Modified src/analysis/normed_space/affine_isometry.lean


Modified src/analysis/normed_space/banach_steinhaus.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *theorem* closure_ball
- \+/\- *lemma* dist_smul
- \+/\- *theorem* frontier_ball
- \+/\- *theorem* frontier_closed_ball
- \+/\- *def* homeomorph_unit_ball
- \+/\- *theorem* interior_closed_ball
- \+/\- *lemma* nndist_smul
- \+/\- *lemma* nnnorm_smul
- \+/\- *lemma* norm_smul
- \+/\- *lemma* norm_smul_of_nonneg
- \- *def* semi_normed_space.restrict_scalars

Modified src/analysis/normed_space/conformal_linear_map.lean


Modified src/analysis/normed_space/dual.lean
- \+/\- *lemma* polar_univ

Modified src/analysis/normed_space/extend.lean
- \+/\- *lemma* continuous_linear_map.extend_to_𝕜'_apply
- \+/\- *lemma* norm_bound

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/hahn_banach.lean


Modified src/analysis/normed_space/linear_isometry.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* continuous_linear_map.op_norm_smul_le
- \+/\- *lemma* continuous_linear_map.to_span_singleton_smul'

Modified src/analysis/normed_space/pi_Lp.lean


Modified src/analysis/normed_space/pointwise.lean


Modified src/analysis/seminorm.lean


Modified src/geometry/manifold/algebra/smooth_functions.lean


Modified src/geometry/manifold/instances/real.lean


Modified src/geometry/manifold/instances/sphere.lean


Modified src/measure_theory/integral/set_to_l1.lean
- \+/\- *lemma* measure_theory.dominated_fin_meas_additive.smul
- \+/\- *lemma* measure_theory.simple_func.set_to_simple_func_smul_left'
- \+/\- *lemma* measure_theory.simple_func.set_to_simple_func_smul_left

Modified src/number_theory/modular.lean


Modified src/topology/metric_space/hausdorff_distance.lean




## [2022-01-16 13:03:59](https://github.com/leanprover-community/mathlib/commit/d60541c)
feat(analysis/seminorm): Add `has_add` and `has_scalar nnreal` ([#11414](https://github.com/leanprover-community/mathlib/pull/11414))
Add instances of `has_add` and `has_scalar nnreal` type classes for `seminorm`.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* seminorm.add_apply
- \+ *lemma* seminorm.coe_add
- \+ *def* seminorm.coe_fn_add_monoid_hom
- \+ *lemma* seminorm.coe_fn_add_monoid_hom_injective
- \+ *lemma* seminorm.coe_smul
- \+ *lemma* seminorm.smul_apply



## [2022-01-16 09:33:17](https://github.com/leanprover-community/mathlib/commit/3fb5b82)
feat(algebra/star/basic): change `star_ring_aut` (notably, complex conjugation) from `ring_equiv` to `ring_hom` and make type argument explicit ([#11418](https://github.com/leanprover-community/mathlib/pull/11418))
Change the underlying object notated by `conj` from
```lean
def star_ring_aut [comm_semiring R] [star_ring R] : ring_aut R :=
```
to
```lean
def star_ring_end [comm_semiring R] [star_ring R] : R →+* R :=
```
and also make the `R` argument explicit.  These two changes allow the notation for conjugate-linear maps, `E →ₗ⋆[R] F` and variants, to pretty-print, see
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Pretty.20printer.20omits.20notation
This is a partial reversion of [#9640](https://github.com/leanprover-community/mathlib/pull/9640), in which complex conjugation was upgraded from `ring_hom` to `ring_equiv`.
#### Estimated changes
Modified src/algebra/module/linear_map.lean


Modified src/algebra/star/basic.lean
- \- *lemma* star_ring_aut_apply
- \- *lemma* star_ring_aut_self_apply
- \+ *def* star_ring_end
- \+ *lemma* star_ring_end_apply
- \+ *lemma* star_ring_end_self_apply

Modified src/analysis/complex/circle.lean
- \+/\- *lemma* coe_inv_circle_eq_conj

Modified src/analysis/complex/isometry.lean


Modified src/analysis/inner_product_space/basic.lean


Modified src/analysis/inner_product_space/dual.lean


Modified src/analysis/inner_product_space/pi_L2.lean


Modified src/analysis/normed_space/linear_isometry.lean


Modified src/analysis/normed_space/star.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/data/equiv/module.lean


Modified src/linear_algebra/matrix/adjugate.lean


Modified src/linear_algebra/matrix/determinant.lean


Modified src/number_theory/modular.lean


Modified src/topology/algebra/module/basic.lean




## [2022-01-15 21:32:40](https://github.com/leanprover-community/mathlib/commit/1a29adc)
feat(measure_theory/integral): weaker assumptions on Ioi integrability ([#11090](https://github.com/leanprover-community/mathlib/pull/11090))
To show a function is integrable given an `ae_cover` it suffices to show boundedness along a filter, not necessarily convergence. This PR adds these generalisations, and uses them to show the older convergence versions.
#### Estimated changes
Modified src/measure_theory/integral/integral_eq_improper.lean
- \+ *lemma* measure_theory.ae_cover.integrable_of_integral_bounded_of_nonneg_ae
- \+ *lemma* measure_theory.ae_cover.integrable_of_integral_norm_bounded
- \+ *lemma* measure_theory.ae_cover.integrable_of_lintegral_nnnorm_bounded'
- \+ *lemma* measure_theory.ae_cover.integrable_of_lintegral_nnnorm_bounded
- \+ *lemma* measure_theory.integrable_of_interval_integral_norm_bounded
- \+ *lemma* measure_theory.integrable_on_Iic_of_interval_integral_norm_bounded
- \+ *lemma* measure_theory.integrable_on_Ioi_of_interval_integral_norm_bounded



## [2022-01-15 20:09:30](https://github.com/leanprover-community/mathlib/commit/1f266d6)
feat(data/pnat/basic): `succ_nat_pred` ([#11455](https://github.com/leanprover-community/mathlib/pull/11455))
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *lemma* pnat.nat_pred_add_one
- \+ *lemma* pnat.nat_pred_eq_pred
- \+ *lemma* pnat.one_add_nat_pred



## [2022-01-15 18:38:48](https://github.com/leanprover-community/mathlib/commit/0b4f07f)
feat(data/set/basic): add singleton_injective ([#11464](https://github.com/leanprover-community/mathlib/pull/11464))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.singleton_injective



## [2022-01-15 17:32:48](https://github.com/leanprover-community/mathlib/commit/37cf695)
feat(measure_theory/integral/set_to_l1): monotonicity properties of set_to_fun ([#10714](https://github.com/leanprover-community/mathlib/pull/10714))
We prove that in a `normed_lattice_add_comm_group`, if `T` is such that `0 ≤ T s x` for `0 ≤ x`,  then `set_to_fun μ T` verifies
- `set_to_fun_mono_left (h : ∀ s x, T' s x ≤ T'' s x) : set_to_fun μ T' hT' f ≤ set_to_fun μ T'' hT'' f`
- `set_to_fun_nonneg (hf : 0 ≤ᵐ[μ] f) : 0 ≤ set_to_fun μ T hT f`
- `set_to_fun_mono (hfg : f ≤ᵐ[μ] g) : set_to_fun μ T hT f ≤ set_to_fun μ T hT g`
#### Estimated changes
Added src/measure_theory/function/lp_order.lean
- \+ *lemma* measure_theory.Lp.coe_fn_le
- \+ *lemma* measure_theory.Lp.coe_fn_nonneg

Modified src/measure_theory/function/simple_func_dense.lean
- \+ *lemma* measure_theory.Lp.simple_func.coe_fn_le
- \+ *lemma* measure_theory.Lp.simple_func.coe_fn_nonneg
- \+ *lemma* measure_theory.Lp.simple_func.coe_fn_zero
- \+ *def* measure_theory.Lp.simple_func.coe_simple_func_nonneg_to_Lp_nonneg
- \+ *lemma* measure_theory.Lp.simple_func.dense_range_coe_simple_func_nonneg_to_Lp_nonneg
- \+ *lemma* measure_theory.Lp.simple_func.exists_simple_func_nonneg_ae_eq

Modified src/measure_theory/integral/set_to_l1.lean
- \+ *lemma* measure_theory.L1.set_to_L1_mono
- \+ *lemma* measure_theory.L1.set_to_L1_mono_left'
- \+ *lemma* measure_theory.L1.set_to_L1_mono_left
- \+ *lemma* measure_theory.L1.set_to_L1_nonneg
- \+ *lemma* measure_theory.L1.simple_func.set_to_L1s_clm_mono
- \+ *lemma* measure_theory.L1.simple_func.set_to_L1s_clm_mono_left'
- \+ *lemma* measure_theory.L1.simple_func.set_to_L1s_clm_mono_left
- \+ *lemma* measure_theory.L1.simple_func.set_to_L1s_clm_nonneg
- \+ *lemma* measure_theory.L1.simple_func.set_to_L1s_mono
- \+ *lemma* measure_theory.L1.simple_func.set_to_L1s_mono_left'
- \+ *lemma* measure_theory.L1.simple_func.set_to_L1s_mono_left
- \+ *lemma* measure_theory.L1.simple_func.set_to_L1s_nonneg
- \+ *lemma* measure_theory.set_to_fun_mono
- \+ *lemma* measure_theory.set_to_fun_mono_left'
- \+ *lemma* measure_theory.set_to_fun_mono_left
- \+ *lemma* measure_theory.set_to_fun_nonneg
- \+/\- *lemma* measure_theory.simple_func.set_to_simple_func_mono
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_mono_left'
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_mono_left
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_nonneg'
- \+ *lemma* measure_theory.simple_func.set_to_simple_func_nonneg



## [2022-01-15 15:30:16](https://github.com/leanprover-community/mathlib/commit/51c5a40)
feat(analysis/special_functions/trigonometric/angle): `neg_coe_pi` ([#11460](https://github.com/leanprover-community/mathlib/pull/11460))
Add the lemma that `-π` and `π` are the same `real.angle` (angle mod 2π).
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* real.angle.neg_coe_pi



## [2022-01-15 14:19:28](https://github.com/leanprover-community/mathlib/commit/ce62dbc)
feat(algebra/star/self_adjoint): module instance on self-adjoint elements of a star algebra ([#11322](https://github.com/leanprover-community/mathlib/pull/11322))
We put a module instance on `self_adjoint A`, where `A` is a `[star_module R A]` and `R` has a trivial star operation. A new typeclass `[has_trivial_star R]` is created for this purpose with an instance on `ℝ`. This allows us to express the fact that e.g. the space of complex Hermitian matrices is a real vector space.
#### Estimated changes
Modified src/algebra/star/basic.lean


Modified src/algebra/star/self_adjoint.lean
- \+ *lemma* self_adjoint.coe_smul

Modified src/data/real/basic.lean




## [2022-01-15 10:42:41](https://github.com/leanprover-community/mathlib/commit/0d1d4c9)
feat(data/finset/basic): strengthen `finset.nonempty.cons_induction` ([#11452](https://github.com/leanprover-community/mathlib/pull/11452))
This change makes it strong enough to be used in three other lemmas.
#### Estimated changes
Modified src/analysis/seminorm.lean


Modified src/data/finset/basic.lean
- \+/\- *lemma* finset.nonempty.cons_induction

Modified src/data/finset/lattice.lean


Modified src/data/real/ennreal.lean




## [2022-01-15 09:16:04](https://github.com/leanprover-community/mathlib/commit/ff19c95)
chore(algebra/group_power/basic): collect together ring lemmas ([#11446](https://github.com/leanprover-community/mathlib/pull/11446))
This reorders the lemmas so that all the ring and comm_ring lemmas can be put in a single section.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+/\- *lemma* eq_or_eq_neg_of_sq_eq_sq
- \+/\- *lemma* mul_neg_one_pow_eq_zero_iff
- \+/\- *theorem* neg_one_pow_eq_or
- \+/\- *lemma* neg_one_pow_mul_eq_zero_iff
- \+/\- *theorem* neg_pow
- \+/\- *theorem* neg_pow_bit0
- \+/\- *theorem* neg_pow_bit1
- \+/\- *lemma* neg_sq
- \+/\- *lemma* of_mul_pow
- \+/\- *lemma* sq_sub_sq
- \+/\- *lemma* sub_sq



## [2022-01-15 07:39:52](https://github.com/leanprover-community/mathlib/commit/df2d70d)
refactor(analysis/inner_product_space/basic): generalize `orthogonal_family` from submodules to maps ([#11254](https://github.com/leanprover-community/mathlib/pull/11254))
The old definition of `orthogonal_family` was a predicate on `V : ι → submodule 𝕜 E`, a family of submodules of an inner product space `E`; the new definition is a predicate on 
```lean
{G : ι → Type*} [Π i, inner_product_space 𝕜 (G i)] (V : Π i, G i →ₗᵢ[𝕜] E)
```
a family of inner product spaces and (injective, generally not surjective) isometries of these inner product spaces into `E`.
The new definition subsumes the old definition, but also applies more cleanly to orthonormal sets of vectors.  An orthonormal set `{v : ι → E}` of vectors in `E` induces an `orthogonal_family` of the new style with `G i` chosen to be `𝕜`, for each `i`, and `V i : G i →ₗᵢ[𝕜] E` the map from `𝕜` to the span of `v i` in `E`.
In [#11255](https://github.com/leanprover-community/mathlib/pull/11255) we write down the induced isometry from the l2 space `lp G 2` into `E` induced by "summing" all the isometries in an orthogonal family.  This works for either the old definition or the new definition.  But with the old definition, an orthonormal set of vectors induces an isometry from the weird l2 space `lp (λ i, span 𝕜 (v i)) 2` into `E`, whereas with the new definition it induces an isometry from the standard l2 space `lp (λ i, 𝕜) 2` into `E`.  This is much more elegant!
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* dfinsupp.inner_sum
- \+ *lemma* dfinsupp.sum_inner
- \+/\- *lemma* direct_sum.submodule_is_internal.collected_basis_orthonormal
- \+/\- *lemma* orthogonal_family.eq_ite
- \+/\- *lemma* orthogonal_family.independent
- \+/\- *lemma* orthogonal_family.inner_right_dfinsupp
- \+/\- *lemma* orthogonal_family.inner_right_fintype
- \+/\- *lemma* orthogonal_family.inner_sum
- \+/\- *lemma* orthogonal_family.norm_sq_diff_sum
- \+/\- *lemma* orthogonal_family.norm_sum
- \+/\- *lemma* orthogonal_family.orthonormal_sigma_orthonormal
- \+/\- *lemma* orthogonal_family.summable_iff_norm_sq_summable
- \+/\- *def* orthogonal_family
- \+ *lemma* orthonormal.orthogonal_family

Modified src/analysis/inner_product_space/pi_L2.lean


Modified src/analysis/inner_product_space/projection.lean


Modified src/analysis/inner_product_space/spectrum.lean
- \+/\- *lemma* inner_product_space.is_self_adjoint.orthogonal_family_eigenspaces'
- \+/\- *lemma* inner_product_space.is_self_adjoint.orthogonal_family_eigenspaces

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry.map_neg

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* linear_isometry.coe_to_span_singleton
- \+ *def* linear_isometry.to_span_singleton
- \+ *lemma* linear_isometry.to_span_singleton_apply



## [2022-01-15 02:46:13](https://github.com/leanprover-community/mathlib/commit/fa41b7a)
feat(topology/algebra/uniform_group): Condition for uniform convergence ([#11391](https://github.com/leanprover-community/mathlib/pull/11391))
This PR adds a lemma regarding uniform convergence on a topological group `G`, placed right after the construction of the `uniform_space` structure on `G`.
#### Estimated changes
Modified src/topology/algebra/uniform_group.lean
- \+ *lemma* topological_group.tendsto_locally_uniformly_iff
- \+ *lemma* topological_group.tendsto_locally_uniformly_on_iff
- \+ *lemma* topological_group.tendsto_uniformly_iff
- \+ *lemma* topological_group.tendsto_uniformly_on_iff



## [2022-01-14 21:29:54](https://github.com/leanprover-community/mathlib/commit/323e388)
feat(algebraic_geometry): More lemmas about affine schemes and basic open sets ([#11449](https://github.com/leanprover-community/mathlib/pull/11449))
#### Estimated changes
Modified src/algebraic_geometry/AffineScheme.lean
- \+ *lemma* algebraic_geometry.Scheme.Spec_map_presheaf_map_eq_to_hom
- \+ *lemma* algebraic_geometry.Scheme.map_prime_spectrum_basic_open_of_affine
- \+ *lemma* algebraic_geometry.is_affine_open.Spec_Γ_identity_hom_app_from_Spec
- \+ *lemma* algebraic_geometry.is_affine_open.basic_open_is_affine
- \+ *def* algebraic_geometry.is_affine_open.from_Spec
- \+ *lemma* algebraic_geometry.is_affine_open.from_Spec_app_eq
- \+ *lemma* algebraic_geometry.is_affine_open.from_Spec_base_preimage
- \+ *lemma* algebraic_geometry.is_affine_open.from_Spec_image_top
- \+ *lemma* algebraic_geometry.is_affine_open.from_Spec_range
- \+ *lemma* algebraic_geometry.is_affine_open.is_compact
- \+ *lemma* algebraic_geometry.is_basis_basic_open

Modified src/algebraic_geometry/Scheme.lean
- \+/\- *lemma* algebraic_geometry.Scheme.basic_open_res
- \+/\- *lemma* algebraic_geometry.Scheme.basic_open_res_eq
- \+ *lemma* algebraic_geometry.Scheme.basic_open_subset
- \+ *lemma* algebraic_geometry.Scheme.comp_coe_base
- \+ *lemma* algebraic_geometry.Scheme.comp_val
- \+ *lemma* algebraic_geometry.Scheme.comp_val_base



## [2022-01-14 19:02:35](https://github.com/leanprover-community/mathlib/commit/f770d6e)
feat(topology/separation): generalize two lemmas ([#11454](https://github.com/leanprover-community/mathlib/pull/11454))
#### Estimated changes
Modified src/topology/separation.lean
- \+/\- *lemma* nhds_eq_nhds_iff
- \+/\- *lemma* nhds_le_nhds_iff



## [2022-01-14 19:02:34](https://github.com/leanprover-community/mathlib/commit/d54375e)
feat(data/nat/totient): `totient_even` ([#11436](https://github.com/leanprover-community/mathlib/pull/11436))
#### Estimated changes
Modified src/data/nat/totient.lean
- \+ *lemma* nat.totient_even



## [2022-01-14 17:47:21](https://github.com/leanprover-community/mathlib/commit/49079c1)
feat(data/finsupp/basic): add `finset_sum_apply` and `coe_fn_add_hom` ([#11423](https://github.com/leanprover-community/mathlib/pull/11423))
`finset_sum_apply`: Given a family of functions `f i : α → ℕ` indexed over `S : finset ι`, the sum of this family over `S` is a function `α → ℕ` whose value at `p : α` is `∑ (i : ι) in S, (f i) p`
`coe_fn_add_monoid_hom`: Coercion from a `finsupp` to a function type is an `add_monoid_hom`. Proved by Alex J. Best
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.coe_finset_sum
- \+ *lemma* finsupp.coe_sum
- \+ *lemma* finsupp.finset_sum_apply



## [2022-01-14 17:47:19](https://github.com/leanprover-community/mathlib/commit/757eaf4)
chore(analysis/calculus/{deriv,mean_value}): use `slope` ([#11419](https://github.com/leanprover-community/mathlib/pull/11419))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/special_functions/log_deriv.lean


Modified src/linear_algebra/affine_space/slope.lean
- \+ *lemma* slope_fun_def

Modified src/measure_theory/integral/interval_integral.lean




## [2022-01-14 17:47:18](https://github.com/leanprover-community/mathlib/commit/653fe45)
feat(analysis/seminorm): `semilattice_sup` on seminorms and lemmas about `ball` ([#11329](https://github.com/leanprover-community/mathlib/pull/11329))
Define `bot` and the the binary `sup` on seminorms, and some lemmas about the supremum of a finite number of seminorms.
Shows that the unit ball of the supremum is given by the intersection of the unit balls.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* seminorm.ball_bot
- \+ *lemma* seminorm.ball_finset_sup'
- \+ *lemma* seminorm.ball_finset_sup
- \+ *lemma* seminorm.ball_finset_sup_eq_Inter
- \+ *lemma* seminorm.ball_sup
- \+ *lemma* seminorm.ball_zero'
- \+ *lemma* seminorm.bot_eq_zero
- \+ *lemma* seminorm.coe_bot
- \+ *lemma* seminorm.coe_sup
- \+ *lemma* seminorm.coe_zero
- \+/\- *lemma* seminorm.ext
- \+ *lemma* seminorm.finset_sup_apply
- \+ *lemma* seminorm.le_def
- \+ *lemma* seminorm.lt_def



## [2022-01-14 16:49:58](https://github.com/leanprover-community/mathlib/commit/2ce607e)
Docs typo in set_theory/cardinal: Wrong type product symbol ([#11453](https://github.com/leanprover-community/mathlib/pull/11453))
#### Estimated changes
Modified src/set_theory/cardinal.lean




## [2022-01-14 15:12:25](https://github.com/leanprover-community/mathlib/commit/d8aed79)
chore(analysis/inner_product_space/projection): Speedup `linear_isometry_equiv.reflections_generate_dim_aux` ([#11443](https://github.com/leanprover-community/mathlib/pull/11443))
This takes it from around 17s to around 6s on my machine.
IMO using `e * f` instead of `f.trans e` makes this proof a little easier to follow, as then we don't have to translate between the two different spellings mid proof (and `prod` uses the `*` spelling internally)
#### Estimated changes
Modified src/analysis/inner_product_space/projection.lean
- \+ *lemma* reflection_inv
- \+ *lemma* reflection_mul_reflection

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry.mul_def
- \+ *lemma* linear_isometry.one_def
- \+ *lemma* linear_isometry_equiv.inv_def
- \+ *lemma* linear_isometry_equiv.mul_def
- \+ *lemma* linear_isometry_equiv.one_def



## [2022-01-14 15:12:24](https://github.com/leanprover-community/mathlib/commit/22a9f2e)
feat(algebra/field/basic): `div_neg_self`, `neg_div_self` ([#11438](https://github.com/leanprover-community/mathlib/pull/11438))
I think these two lemmas are useful as `simp` lemmas, but they don't
seem to be there already.
#### Estimated changes
Modified src/algebra/field/basic.lean
- \+ *lemma* div_neg_self
- \+ *lemma* neg_div_self



## [2022-01-14 14:12:17](https://github.com/leanprover-community/mathlib/commit/201aeaa)
chore(algebra/char_p): ring_char.eq is better in the other direction, with instances, and explicit arguments ([#11439](https://github.com/leanprover-community/mathlib/pull/11439))
#### Estimated changes
Modified src/algebra/char_p/basic.lean
- \+/\- *theorem* ring_char.eq
- \+/\- *lemma* ring_char.eq_zero



## [2022-01-14 13:04:30](https://github.com/leanprover-community/mathlib/commit/011a599)
feat(algebraic_geometry): Gluing morphisms from an open cover. ([#11441](https://github.com/leanprover-community/mathlib/pull/11441))
#### Estimated changes
Modified src/algebraic_geometry/gluing.lean
- \+ *def* algebraic_geometry.Scheme.glue_data.open_cover
- \+ *def* algebraic_geometry.Scheme.open_cover.from_glued
- \+ *lemma* algebraic_geometry.Scheme.open_cover.from_glued_injective
- \+ *lemma* algebraic_geometry.Scheme.open_cover.from_glued_open_embedding
- \+ *lemma* algebraic_geometry.Scheme.open_cover.from_glued_open_map
- \+ *def* algebraic_geometry.Scheme.open_cover.glue_morphisms
- \+ *def* algebraic_geometry.Scheme.open_cover.glued_cover
- \+ *lemma* algebraic_geometry.Scheme.open_cover.glued_cover_cocycle
- \+ *lemma* algebraic_geometry.Scheme.open_cover.glued_cover_cocycle_fst
- \+ *lemma* algebraic_geometry.Scheme.open_cover.glued_cover_cocycle_snd
- \+ *def* algebraic_geometry.Scheme.open_cover.glued_cover_t'
- \+ *lemma* algebraic_geometry.Scheme.open_cover.glued_cover_t'_fst_fst
- \+ *lemma* algebraic_geometry.Scheme.open_cover.glued_cover_t'_fst_snd
- \+ *lemma* algebraic_geometry.Scheme.open_cover.glued_cover_t'_snd_fst
- \+ *lemma* algebraic_geometry.Scheme.open_cover.glued_cover_t'_snd_snd
- \+ *lemma* algebraic_geometry.Scheme.open_cover.ι_from_glued
- \+ *lemma* algebraic_geometry.Scheme.open_cover.ι_glue_morphisms



## [2022-01-14 10:58:50](https://github.com/leanprover-community/mathlib/commit/44351a9)
chore(analysis/complex/circle): add to_units and golf ([#11435](https://github.com/leanprover-community/mathlib/pull/11435))
#### Estimated changes
Modified src/analysis/complex/circle.lean
- \+ *def* circle.to_units

Modified src/analysis/complex/isometry.lean
- \- *def* rotation_aux



## [2022-01-14 10:58:49](https://github.com/leanprover-community/mathlib/commit/38eb719)
feat(data/matrix/notation): relax typeclass assumptions ([#11429](https://github.com/leanprover-community/mathlib/pull/11429))
#### Estimated changes
Modified src/data/matrix/notation.lean
- \+/\- *lemma* matrix.smul_vec2
- \+/\- *lemma* matrix.smul_vec3

Modified src/linear_algebra/cross_product.lean




## [2022-01-14 10:58:47](https://github.com/leanprover-community/mathlib/commit/a861839)
feat(ring_theory/discriminant): add discr_mul_is_integral_mem_adjoin ([#11396](https://github.com/leanprover-community/mathlib/pull/11396))
We add `discr_mul_is_integral_mem_adjoin`: let `K` be the fraction field of an integrally closed domain `R` and let `L` be a finite
separable extension of `K`. Let `B : power_basis K L` be such that `is_integral R B.gen`. Then for all `z : L` that are integral over `R`, we have `(discr K B.basis) • z ∈ adjoin R ({B.gen} : set L)`.
From flt-regular.
#### Estimated changes
Modified src/field_theory/intermediate_field.lean
- \+ *lemma* intermediate_field.aeval_coe
- \+ *lemma* intermediate_field.coe_is_integral_iff
- \+ *lemma* intermediate_field.coe_prod
- \+ *lemma* intermediate_field.coe_sum

Modified src/ring_theory/discriminant.lean
- \+/\- *lemma* algebra.discr_eq_det_embeddings_matrix_reindex_pow_two
- \+ *lemma* algebra.discr_is_integral
- \+ *lemma* algebra.discr_is_unit_of_basis
- \+ *lemma* algebra.discr_mul_is_integral_mem_adjoin
- \+/\- *lemma* algebra.discr_not_zero_of_basis
- \+/\- *lemma* algebra.discr_power_basis_eq_prod
- \+/\- *lemma* algebra.of_power_basis_eq_norm
- \+/\- *lemma* algebra.of_power_basis_eq_prod''
- \+/\- *lemma* algebra.of_power_basis_eq_prod'

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* adjoin_le_integral_closure
- \+ *lemma* is_integral.det

Modified src/ring_theory/trace.lean
- \+ *lemma* algebra.trace_matrix_of_basis_mul_vec



## [2022-01-14 10:07:46](https://github.com/leanprover-community/mathlib/commit/5a6c13b)
feat(algebraic_geometry/open_immersion): Operations on open covers.  ([#11442](https://github.com/leanprover-community/mathlib/pull/11442))
#### Estimated changes
Modified src/algebraic_geometry/open_immersion.lean
- \+ *def* algebraic_geometry.Scheme.open_cover.finite_subcover
- \+ *def* algebraic_geometry.Scheme.open_cover.pullback_cover



## [2022-01-14 10:07:44](https://github.com/leanprover-community/mathlib/commit/e286012)
feat(algebra/ne_zero): `pos_of_ne_zero_coe` ([#11437](https://github.com/leanprover-community/mathlib/pull/11437))
#### Estimated changes
Modified src/algebra/ne_zero.lean
- \+ *lemma* ne_zero.not_char_dvd
- \- *lemma* ne_zero.not_dvd_char
- \+ *lemma* ne_zero.pos_of_ne_zero_coe

Modified src/ring_theory/polynomial/cyclotomic/basic.lean




## [2022-01-14 10:07:43](https://github.com/leanprover-community/mathlib/commit/021baae)
feat(analysis/normed_space/linear_isometry): coercion injectivity lemmas and add_monoid_hom_class ([#11434](https://github.com/leanprover-community/mathlib/pull/11434))
This also registers `linear_isometry` and `linear_isometry_equiv` with `add_monoid_hom_class`.
I found myself wanting one of these while squeezing a simp, so may as well have all of them now.
#### Estimated changes
Modified src/analysis/complex/isometry.lean
- \- *lemma* linear_isometry_equiv.congr_fun

Modified src/analysis/normed_space/linear_isometry.lean
- \- *lemma* linear_isometry.coe_fn_injective
- \+ *lemma* linear_isometry.coe_injective
- \+ *lemma* linear_isometry.to_continuous_linear_map_inj
- \+ *lemma* linear_isometry.to_continuous_linear_map_injective
- \+ *lemma* linear_isometry.to_linear_map_inj
- \+ *lemma* linear_isometry_equiv.coe_injective
- \+ *lemma* linear_isometry_equiv.to_continuous_linear_equiv_inj
- \+ *lemma* linear_isometry_equiv.to_continuous_linear_equiv_injective
- \+ *lemma* linear_isometry_equiv.to_homeomorph_inj
- \+ *lemma* linear_isometry_equiv.to_homeomorph_injective
- \+ *lemma* linear_isometry_equiv.to_isometric_inj
- \+ *lemma* linear_isometry_equiv.to_isometric_injective
- \+ *lemma* linear_isometry_equiv.to_linear_equiv_inj
- \+ *lemma* linear_isometry_equiv.to_linear_isometry_inj
- \+ *lemma* linear_isometry_equiv.to_linear_isometry_injective



## [2022-01-14 10:07:42](https://github.com/leanprover-community/mathlib/commit/61054f7)
feat(topology): some improvements ([#11424](https://github.com/leanprover-community/mathlib/pull/11424))
* Prove a better version of `continuous_on.comp_fract`. Rename `continuous_on.comp_fract` -> `continuous_on.comp_fract''`.
* Rename `finset.closure_Union` -> `finset.closure_bUnion`
* Add `continuous.congr` and `continuous.subtype_coe`
#### Estimated changes
Modified src/topology/algebra/floor_ring.lean
- \+ *lemma* continuous_on.comp_fract''
- \+/\- *lemma* continuous_on.comp_fract'
- \+/\- *lemma* continuous_on.comp_fract

Modified src/topology/basic.lean
- \+ *lemma* continuous.congr
- \- *lemma* finset.closure_Union
- \+ *lemma* finset.closure_bUnion

Modified src/topology/constructions.lean
- \+ *lemma* continuous.subtype_coe



## [2022-01-14 08:37:20](https://github.com/leanprover-community/mathlib/commit/3c1740a)
feat(combinatorics/configuration): Define the order of a projective plane ([#11430](https://github.com/leanprover-community/mathlib/pull/11430))
This PR defines the order of a projective plane, and proves a couple lemmas.
#### Estimated changes
Modified src/combinatorics/configuration.lean
- \+ *lemma* configuration.projective_plane.dual.order
- \+ *lemma* configuration.projective_plane.line_count_eq
- \+ *lemma* configuration.projective_plane.point_count_eq



## [2022-01-14 08:37:18](https://github.com/leanprover-community/mathlib/commit/5a3abca)
feat(topology/subset_properties): some compactness properties ([#11425](https://github.com/leanprover-community/mathlib/pull/11425))
* Add some lemmas about the existence of compact sets
* Add `is_compact.eventually_forall_of_forall_eventually`
* Some cleanup in `topology/subset_properties` and `topology/separation`
#### Estimated changes
Modified src/topology/separation.lean
- \+ *lemma* exists_compact_between
- \+ *lemma* exists_open_between_and_is_compact_closure
- \+ *lemma* exists_open_superset_and_is_compact_closure

Modified src/topology/subset_properties.lean
- \+/\- *lemma* compact_Union
- \+/\- *lemma* compact_space.elim_nhds_subcover
- \+/\- *theorem* compact_space_of_finite_subfamily_closed
- \+/\- *lemma* continuous_on.preimage_clopen_of_clopen
- \+/\- *lemma* finset.compact_bUnion
- \+/\- *lemma* is_clopen_bInter
- \+/\- *lemma* is_clopen_bUnion
- \+/\- *lemma* is_compact.elim_finite_subcover_image
- \+ *lemma* is_compact.eventually_forall_of_forall_eventually
- \+/\- *def* is_compact
- \+/\- *theorem* is_irreducible.image
- \+/\- *theorem* is_preirreducible.image
- \+/\- *lemma* is_preirreducible.preimage
- \+/\- *lemma* set.finite.compact_bUnion



## [2022-01-14 08:37:17](https://github.com/leanprover-community/mathlib/commit/feaf6f5)
feat(algebraic_geometry): lemmas about basic opens in schemes ([#11393](https://github.com/leanprover-community/mathlib/pull/11393))
#### Estimated changes
Modified src/algebraic_geometry/Gamma_Spec_adjunction.lean
- \+ *lemma* algebraic_geometry.Γ_Spec.adjunction_unit_app_app_top

Modified src/algebraic_geometry/Scheme.lean
- \+ *def* algebraic_geometry.Scheme.basic_open
- \+ *lemma* algebraic_geometry.Scheme.basic_open_mul
- \+ *lemma* algebraic_geometry.Scheme.basic_open_of_is_unit
- \+ *lemma* algebraic_geometry.Scheme.basic_open_res
- \+ *lemma* algebraic_geometry.Scheme.basic_open_res_eq
- \+ *lemma* algebraic_geometry.Scheme.basic_open_zero
- \+ *lemma* algebraic_geometry.Scheme.comp_val_c_app
- \+ *lemma* algebraic_geometry.Scheme.congr_app
- \+ *lemma* algebraic_geometry.Scheme.mem_basic_open
- \+ *lemma* algebraic_geometry.Scheme.mem_basic_open_top
- \+ *lemma* algebraic_geometry.Scheme.preimage_basic_open'
- \+ *lemma* algebraic_geometry.Scheme.preimage_basic_open
- \+ *lemma* algebraic_geometry.basic_open_eq_of_affine'
- \+ *lemma* algebraic_geometry.basic_open_eq_of_affine

Modified src/algebraic_geometry/Spec.lean
- \+/\- *def* algebraic_geometry.Spec_Γ_identity

Modified src/algebraic_geometry/locally_ringed_space.lean


Modified src/algebraic_geometry/properties.lean
- \- *lemma* algebraic_geometry.basic_open_eq_of_affine'
- \- *lemma* algebraic_geometry.basic_open_eq_of_affine

Modified src/algebraic_geometry/ringed_space.lean
- \+ *lemma* algebraic_geometry.RingedSpace.basic_open_mul
- \+ *lemma* algebraic_geometry.RingedSpace.basic_open_of_is_unit
- \+/\- *lemma* algebraic_geometry.RingedSpace.basic_open_res
- \+ *lemma* algebraic_geometry.RingedSpace.basic_open_res_eq

Modified src/algebraic_geometry/sheafed_space.lean


Modified src/topology/category/Top/opens.lean
- \+ *lemma* topological_space.opens.inclusion_map_eq_top
- \+ *lemma* topological_space.opens.open_embedding_obj_top



## [2022-01-14 08:37:16](https://github.com/leanprover-community/mathlib/commit/85accb8)
feat(data/{multiset,finset}/sum): Disjoint sum of multisets/finsets ([#11355](https://github.com/leanprover-community/mathlib/pull/11355))
This defines the disjoint union of two multisets/finsets as `multiset (α ⊕ β)`/`finset (α ⊕ β)`.
#### Estimated changes
Added src/data/finset/sum.lean
- \+ *lemma* finset.card_disj_sum
- \+ *def* finset.disj_sum
- \+ *lemma* finset.disj_sum_empty
- \+ *lemma* finset.disj_sum_mono
- \+ *lemma* finset.disj_sum_mono_left
- \+ *lemma* finset.disj_sum_mono_right
- \+ *lemma* finset.disj_sum_ssubset_disj_sum_of_ssubset_of_subset
- \+ *lemma* finset.disj_sum_ssubset_disj_sum_of_subset_of_ssubset
- \+ *lemma* finset.disj_sum_strict_mono_left
- \+ *lemma* finset.disj_sum_strict_mono_right
- \+ *lemma* finset.empty_disj_sum
- \+ *lemma* finset.inl_mem_disj_sum
- \+ *lemma* finset.inr_mem_disj_sum
- \+ *lemma* finset.mem_disj_sum
- \+ *lemma* finset.val_disj_sum

Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.map_lt_map
- \+ *lemma* multiset.map_mono
- \+ *lemma* multiset.map_strict_mono

Added src/data/multiset/sum.lean
- \+ *lemma* multiset.card_disj_sum
- \+ *def* multiset.disj_sum
- \+ *lemma* multiset.disj_sum_lt_disj_sum_of_le_of_lt
- \+ *lemma* multiset.disj_sum_lt_disj_sum_of_lt_of_le
- \+ *lemma* multiset.disj_sum_mono
- \+ *lemma* multiset.disj_sum_mono_left
- \+ *lemma* multiset.disj_sum_mono_right
- \+ *lemma* multiset.disj_sum_strict_mono_left
- \+ *lemma* multiset.disj_sum_strict_mono_right
- \+ *lemma* multiset.disj_sum_zero
- \+ *lemma* multiset.inl_mem_disj_sum
- \+ *lemma* multiset.inr_mem_disj_sum
- \+ *lemma* multiset.mem_disj_sum
- \+ *lemma* multiset.zero_disj_sum

Modified src/logic/basic.lean
- \+ *lemma* or_iff_left
- \+ *lemma* or_iff_right



## [2022-01-14 08:37:15](https://github.com/leanprover-community/mathlib/commit/9a94993)
feat(analysis/inner_product_space/l2): Inner product space structure on `l2` ([#11315](https://github.com/leanprover-community/mathlib/pull/11315))
#### Estimated changes
Added src/analysis/inner_product_space/l2_space.lean
- \+ *lemma* lp.has_sum_inner
- \+ *lemma* lp.inner_eq_tsum
- \+ *lemma* lp.summable_inner

Modified src/analysis/normed_space/lp_space.lean




## [2022-01-14 08:37:14](https://github.com/leanprover-community/mathlib/commit/fb2b1a0)
fix(algebra/star/basic): redefine `star_ordered_ring` ([#11213](https://github.com/leanprover-community/mathlib/pull/11213))
This PR redefines `star_ordered_ring` to remove the `ordered_semiring` assumption, which includes undesirable axioms such as `∀ (a b c : α), a < b → 0 < c → c * a < c * b`. See the discussion on Zulip [here](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Star.20ordered.20ring).
#### Estimated changes
Modified src/algebra/star/basic.lean
- \+ *lemma* star_mul_self_nonneg'
- \+/\- *lemma* star_mul_self_nonneg

Modified src/data/complex/basic.lean


Modified src/data/real/basic.lean


Modified src/data/real/sqrt.lean




## [2022-01-14 06:59:50](https://github.com/leanprover-community/mathlib/commit/60c77d4)
feat(tactic/lint): include linter name in github output ([#11413](https://github.com/leanprover-community/mathlib/pull/11413))
#### Estimated changes
Modified src/tactic/lint/frontend.lean




## [2022-01-14 06:28:53](https://github.com/leanprover-community/mathlib/commit/d248447)
feat(algebraic_geometry): Gluing schemes ([#11431](https://github.com/leanprover-community/mathlib/pull/11431))
#### Estimated changes
Added src/algebraic_geometry/gluing.lean
- \+ *def* algebraic_geometry.Scheme.glue_data.V_pullback_cone
- \+ *def* algebraic_geometry.Scheme.glue_data.V_pullback_cone_is_limit
- \+ *lemma* algebraic_geometry.Scheme.glue_data.glue_condition
- \+ *abbreviation* algebraic_geometry.Scheme.glue_data.glued
- \+ *def* algebraic_geometry.Scheme.glue_data.glued_Scheme
- \+ *lemma* algebraic_geometry.Scheme.glue_data.is_open_iff
- \+ *abbreviation* algebraic_geometry.Scheme.glue_data.iso_LocallyRingedSpace
- \+ *def* algebraic_geometry.Scheme.glue_data.iso_carrier
- \+ *def* algebraic_geometry.Scheme.glue_data.rel
- \+ *abbreviation* algebraic_geometry.Scheme.glue_data.to_LocallyRingedSpace_glue_data
- \+ *abbreviation* algebraic_geometry.Scheme.glue_data.ι
- \+ *lemma* algebraic_geometry.Scheme.glue_data.ι_eq_iff
- \+ *lemma* algebraic_geometry.Scheme.glue_data.ι_iso_LocallyRingedSpace_inv
- \+ *lemma* algebraic_geometry.Scheme.glue_data.ι_iso_carrier_inv
- \+ *lemma* algebraic_geometry.Scheme.glue_data.ι_jointly_surjective
- \+ *structure* algebraic_geometry.Scheme.glue_data

Modified src/algebraic_geometry/presheafed_space.lean
- \+ *lemma* algebraic_geometry.PresheafedSpace.coe_to_fun_eq

Modified src/algebraic_geometry/presheafed_space/gluing.lean
- \+ *def* algebraic_geometry.LocallyRingedSpace.glue_data.V_pullback_cone_is_limit
- \+ *abbreviation* algebraic_geometry.LocallyRingedSpace.glue_data.iso_SheafedSpace
- \+ *abbreviation* algebraic_geometry.LocallyRingedSpace.glue_data.to_SheafedSpace_glue_data
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.glue_data.ι_iso_SheafedSpace_inv
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.glue_data.ι_jointly_surjective
- \+ *structure* algebraic_geometry.LocallyRingedSpace.glue_data
- \- *lemma* algebraic_geometry.PresheafedSpace.coe_to_fun_eq
- \+ *def* algebraic_geometry.PresheafedSpace.glue_data.V_pullback_cone_is_limit
- \+ *lemma* algebraic_geometry.PresheafedSpace.glue_data.ι_jointly_surjective
- \+ *def* algebraic_geometry.SheafedSpace.glue_data.V_pullback_cone_is_limit
- \+ *abbreviation* algebraic_geometry.SheafedSpace.glue_data.iso_PresheafedSpace
- \+ *abbreviation* algebraic_geometry.SheafedSpace.glue_data.to_PresheafedSpace_glue_data
- \+ *lemma* algebraic_geometry.SheafedSpace.glue_data.ι_iso_PresheafedSpace_inv
- \+ *lemma* algebraic_geometry.SheafedSpace.glue_data.ι_jointly_surjective
- \+ *structure* algebraic_geometry.SheafedSpace.glue_data



## [2022-01-13 23:16:00](https://github.com/leanprover-community/mathlib/commit/48fd9f2)
chore(data/list/big_operators): rename vars, reorder lemmas ([#11433](https://github.com/leanprover-community/mathlib/pull/11433))
* use better variable names;
* move lemmas to proper sections;
* relax `[comm_semiring R]` to `[semiring R]` in `dvd_sum`.
#### Estimated changes
Modified src/data/list/big_operators.lean
- \+/\- *lemma* list.all_one_of_le_one_le_of_prod_eq_one
- \+/\- *lemma* list.dvd_prod
- \+/\- *lemma* list.dvd_sum
- \+/\- *lemma* list.eq_of_sum_take_eq
- \+/\- *lemma* list.exists_le_of_sum_le
- \+/\- *lemma* list.exists_lt_of_sum_lt
- \+/\- *lemma* list.head_mul_tail_prod_of_ne_nil
- \+/\- *lemma* list.length_pos_of_prod_ne_one
- \+/\- *lemma* list.length_pos_of_sum_pos
- \+/\- *lemma* list.monotone_sum_take
- \+/\- *lemma* list.nth_zero_mul_tail_prod
- \+/\- *lemma* list.one_le_prod_of_one_le
- \+/\- *lemma* list.one_lt_prod_of_one_lt
- \+/\- *lemma* list.prod_eq_one_iff
- \+/\- *lemma* list.prod_eq_zero
- \+/\- *lemma* list.prod_eq_zero_iff
- \+/\- *lemma* list.prod_erase
- \+/\- *lemma* list.prod_hom
- \+/\- *lemma* list.prod_hom_rel
- \+/\- *lemma* list.prod_hom₂
- \+/\- *lemma* list.prod_inv
- \+/\- *lemma* list.prod_inv_reverse
- \+/\- *lemma* list.prod_is_unit
- \+/\- *lemma* list.prod_join
- \+/\- *lemma* list.prod_map_hom
- \+/\- *lemma* list.prod_ne_zero
- \+/\- *lemma* list.prod_nil
- \+/\- *lemma* list.prod_pos
- \+/\- *lemma* list.prod_reverse_noncomm
- \+/\- *lemma* list.prod_update_nth'
- \+/\- *lemma* list.prod_update_nth
- \+/\- *lemma* list.single_le_prod
- \+/\- *lemma* list.sum_le_foldr_max
- \+/\- *lemma* list.sum_map_mul_left
- \+/\- *lemma* list.sum_map_mul_right
- \+/\- *lemma* monoid_hom.map_list_prod
- \+/\- *lemma* monoid_hom.unop_map_list_prod
- \+/\- *lemma* mul_opposite.op_list_prod
- \+/\- *lemma* mul_opposite.unop_list_prod



## [2022-01-13 21:10:22](https://github.com/leanprover-community/mathlib/commit/e830348)
feat(set_theory/ordinal_arithmetic): Families of ordinals ([#11278](https://github.com/leanprover-community/mathlib/pull/11278))
This PR introduces some API to convert from `ι → β` indexed families to `Π o < b, β` indexed families. This simplifies and contextualizes some existing results.
#### Estimated changes
Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal_arithmetic.lean
- \+ *def* ordinal.bfamily_of_family'
- \+ *theorem* ordinal.bfamily_of_family'_typein
- \+ *def* ordinal.bfamily_of_family
- \+ *theorem* ordinal.bfamily_of_family_typein
- \+ *theorem* ordinal.blsub_eq_blsub
- \+ *theorem* ordinal.blsub_eq_lsub'
- \+/\- *theorem* ordinal.blsub_eq_lsub
- \+ *theorem* ordinal.bsup_eq_bsup
- \+ *theorem* ordinal.bsup_eq_sup'
- \+/\- *theorem* ordinal.bsup_eq_sup
- \- *theorem* ordinal.bsup_type
- \+ *def* ordinal.family_of_bfamily'
- \+ *theorem* ordinal.family_of_bfamily'_enum
- \+ *def* ordinal.family_of_bfamily
- \+ *theorem* ordinal.family_of_bfamily_enum
- \+ *theorem* ordinal.lsub_eq_blsub'
- \+/\- *theorem* ordinal.lsub_eq_blsub
- \+ *theorem* ordinal.lsub_eq_lsub
- \+ *theorem* ordinal.sup_eq_bsup'
- \+/\- *theorem* ordinal.sup_eq_bsup
- \+ *theorem* ordinal.sup_eq_sup



## [2022-01-13 20:16:58](https://github.com/leanprover-community/mathlib/commit/6fa2e46)
feat(algebra/lie/nilpotent): central extensions of nilpotent Lie modules / algebras are nilpotent ([#11422](https://github.com/leanprover-community/mathlib/pull/11422))
The main result is `lie_algebra.nilpotent_of_nilpotent_quotient`.
#### Estimated changes
Modified src/algebra/lie/abelian.lean
- \+ *lemma* lie_module.ideal_oper_max_triv_submodule_eq_bot

Modified src/algebra/lie/basic.lean
- \+ *lemma* lie_module_hom.coe_id
- \+ *def* lie_module_hom.id
- \+ *lemma* lie_module_hom.id_apply

Modified src/algebra/lie/ideal_operations.lean
- \+ *lemma* lie_submodule.map_bracket_eq

Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* coe_lower_central_series_ideal_quot_eq
- \+ *lemma* lie_algebra.nilpotent_of_nilpotent_quotient
- \- *lemma* lie_ideal.lower_central_series_map_le
- \+ *lemma* lie_ideal.map_lower_central_series_le
- \+ *lemma* lie_module.map_lower_central_series_le
- \+ *lemma* lie_module.nilpotent_of_nilpotent_quotient

Modified src/algebra/lie/quotient.lean
- \+ *lemma* lie_submodule.quotient.map_mk'_eq_bot_le
- \+ *lemma* lie_submodule.quotient.mk'_ker
- \+ *lemma* lie_submodule.quotient.mk_eq_zero

Modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_module_hom.comp_ker_incl
- \+ *def* lie_module_hom.ker
- \+ *lemma* lie_module_hom.ker_id
- \+ *lemma* lie_module_hom.le_ker_iff_map
- \+ *lemma* lie_module_hom.mem_ker
- \+/\- *lemma* lie_subalgebra.coe_to_lie_submodule
- \+/\- *lemma* lie_subalgebra.exists_lie_ideal_coe_eq_iff
- \+/\- *lemma* lie_subalgebra.exists_nested_lie_ideal_coe_eq_iff
- \+/\- *lemma* lie_subalgebra.mem_to_lie_submodule
- \+/\- *def* lie_subalgebra.to_lie_submodule
- \+ *lemma* lie_submodule.coe_submodule_map



## [2022-01-13 19:34:18](https://github.com/leanprover-community/mathlib/commit/432e85e)
feat(analysis/normed_space/linear_isometry): add congr_arg and congr_fun ([#11428](https://github.com/leanprover-community/mathlib/pull/11428))
Two trivial lemmas that are missing from this bundled morphism but present on most others.
Turns out I didn't actually need these in the branch I created them in, but we should have them anyway.
#### Estimated changes
Modified src/analysis/normed_space/linear_isometry.lean




## [2022-01-13 19:34:17](https://github.com/leanprover-community/mathlib/commit/8a13846)
feat(analysis/mean_inequalities): Hölder's inequality for infinite sums ([#11314](https://github.com/leanprover-community/mathlib/pull/11314))
State a few versions of Hölder's inequality for infinite sums.
The specific forms of the inequality chosen are parallel to those for Minkowski's inequality in [#10984](https://github.com/leanprover-community/mathlib/pull/10984).
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *theorem* nnreal.Lp_add_le_tsum'
- \+ *theorem* nnreal.inner_le_Lp_mul_Lq_has_sum
- \+ *theorem* nnreal.inner_le_Lp_mul_Lq_tsum'
- \+ *theorem* nnreal.inner_le_Lp_mul_Lq_tsum
- \+ *theorem* nnreal.summable_Lp_add
- \+ *theorem* nnreal.summable_mul_of_Lp_Lq
- \+ *theorem* real.Lp_add_le_tsum_of_nonneg'
- \+ *theorem* real.inner_le_Lp_mul_Lq_has_sum_of_nonneg
- \+ *theorem* real.inner_le_Lp_mul_Lq_tsum_of_nonneg'
- \+ *theorem* real.inner_le_Lp_mul_Lq_tsum_of_nonneg
- \+ *theorem* real.summable_Lp_add_of_nonneg
- \+ *theorem* real.summable_mul_of_Lp_Lq_of_nonneg

Modified src/analysis/normed_space/lp_space.lean




## [2022-01-13 17:57:13](https://github.com/leanprover-community/mathlib/commit/0504425)
feat(analysis/inner_product_space/basic): criterion for summability ([#11224](https://github.com/leanprover-community/mathlib/pull/11224))
In a complete inner product space `E`, a family `f` of mutually-orthogonal elements of `E` is summable, if and only if
`(λ i, ∥f i∥ ^ 2)` is summable.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_sdiff_div_prod_sdiff

Modified src/algebra/big_operators/order.lean
- \+ *lemma* finset.abs_sum_of_nonneg'
- \+ *lemma* finset.abs_sum_of_nonneg
- \+ *lemma* finset.one_le_prod''
- \+ *lemma* finset.one_le_prod'

Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* orthogonal_family.inner_sum
- \+ *lemma* orthogonal_family.norm_sq_diff_sum
- \+ *lemma* orthogonal_family.norm_sum
- \+ *lemma* orthogonal_family.summable_iff_norm_sq_summable



## [2022-01-13 17:19:26](https://github.com/leanprover-community/mathlib/commit/6446ba8)
feat(ring_theory/{trace,norm}): add trace_gen_eq_next_coeff_minpoly and norm_gen_eq_coeff_zero_minpoly  ([#11420](https://github.com/leanprover-community/mathlib/pull/11420))
We add `trace_gen_eq_next_coeff_minpoly` and `norm_gen_eq_coeff_zero_minpoly`.
From flt-regular.
#### Estimated changes
Modified src/field_theory/splitting_field.lean
- \+ *lemma* polynomial.prod_roots_eq_coeff_zero_of_monic_of_split
- \+ *lemma* polynomial.sum_roots_eq_next_coeff_of_monic_of_split

Modified src/ring_theory/norm.lean
- \- *lemma* algebra.norm_gen_eq_prod_roots
- \+ *lemma* algebra.power_basis.norm_gen_eq_coeff_zero_minpoly
- \+ *lemma* algebra.power_basis.norm_gen_eq_prod_roots

Modified src/ring_theory/trace.lean
- \+ *lemma* power_basis.trace_gen_eq_next_coeff_minpoly



## [2022-01-13 16:52:43](https://github.com/leanprover-community/mathlib/commit/ea9f964)
fix(analysis/calculus/fderiv_symmetric): speed up tactic block from 3.6s to 180ms ([#11426](https://github.com/leanprover-community/mathlib/pull/11426))
The timings are measured for the single small begin/end block. The proof as a whole is still around 7.6s, down from 11s.
The fault here was likely the `convert`, which presumably spent a lot of time trying to unify typeclass arguments.
#### Estimated changes
Modified src/analysis/calculus/fderiv_symmetric.lean




## [2022-01-13 16:52:42](https://github.com/leanprover-community/mathlib/commit/0f79668)
feat(measure_theory/function/uniform_integrable): Egorov's theorem ([#11328](https://github.com/leanprover-community/mathlib/pull/11328))
This PR proves Egorov's theorem which is necessary for the Vitali convergence theorem which is vital for the martingale convergence theorems.
#### Estimated changes
Added src/measure_theory/function/uniform_integrable.lean
- \+ *def* measure_theory.egorov.Union_not_convergent_seq
- \+ *lemma* measure_theory.egorov.Union_not_convergent_seq_measurable_set
- \+ *lemma* measure_theory.egorov.Union_not_convergent_seq_subset
- \+ *lemma* measure_theory.egorov.exists_not_convergent_seq_lt
- \+ *lemma* measure_theory.egorov.measure_Union_not_convergent_seq
- \+ *lemma* measure_theory.egorov.measure_inter_not_convergent_seq_eq_zero
- \+ *lemma* measure_theory.egorov.measure_not_convergent_seq_tendsto_zero
- \+ *lemma* measure_theory.egorov.mem_not_convergent_seq_iff
- \+ *def* measure_theory.egorov.not_convergent_seq
- \+ *lemma* measure_theory.egorov.not_convergent_seq_antitone
- \+ *def* measure_theory.egorov.not_convergent_seq_lt_index
- \+ *lemma* measure_theory.egorov.not_convergent_seq_lt_index_spec
- \+ *lemma* measure_theory.egorov.not_convergent_seq_measurable_set
- \+ *lemma* measure_theory.egorov.tendsto_uniformly_on_diff_Union_not_convergent_seq
- \+ *lemma* measure_theory.tendsto_uniformly_on_of_ae_tendsto'
- \+ *theorem* measure_theory.tendsto_uniformly_on_of_ae_tendsto



## [2022-01-13 15:18:51](https://github.com/leanprover-community/mathlib/commit/a16a5b5)
chore(order/lattice_intervals): review ([#11416](https://github.com/leanprover-community/mathlib/pull/11416))
* use `@[reducible] protected def`;
* add `is_least.order_bot` and `is_greatest.order_top`, use them;
* weaken TC assumptions on `set.Ici.bounded_order` and `set.Iic.bounded_order`.
#### Estimated changes
Modified src/order/bounds.lean
- \+ *def* is_greatest.order_top
- \+ *def* is_least.order_bot

Modified src/order/conditionally_complete_lattice.lean
- \+ *theorem* cInf_pair
- \+ *theorem* cSup_pair

Modified src/order/lattice_intervals.lean
- \- *def* set.Icc.bounded_order
- \- *def* set.Icc.order_bot
- \- *def* set.Icc.order_top
- \- *def* set.Ico.order_bot
- \- *def* set.Ioc.order_top



## [2022-01-13 12:25:21](https://github.com/leanprover-community/mathlib/commit/cd4f5c4)
feat(linear_algebra/{cross_product,vectors}): cross product ([#11181](https://github.com/leanprover-community/mathlib/pull/11181))
Defines the cross product for R^3 and gives localized notation for that and the dot product.
Was https://github.com/leanprover-community/mathlib/pull/10959
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/data/matrix/notation.lean
- \+ *lemma* matrix.smul_vec2
- \+ *lemma* matrix.smul_vec3
- \+ *lemma* matrix.vec2_add
- \+ *lemma* matrix.vec2_dot_product'
- \+ *lemma* matrix.vec2_dot_product
- \+ *lemma* matrix.vec2_eq
- \+ *lemma* matrix.vec3_add
- \+ *lemma* matrix.vec3_dot_product'
- \+ *lemma* matrix.vec3_dot_product
- \+ *lemma* matrix.vec3_eq

Added src/linear_algebra/cross_product.lean
- \+ *def* cross.lie_ring
- \+ *lemma* cross_anticomm'
- \+ *lemma* cross_anticomm
- \+ *lemma* cross_apply
- \+ *lemma* cross_cross
- \+ *theorem* cross_dot_cross
- \+ *def* cross_product
- \+ *lemma* cross_self
- \+ *lemma* dot_cross_self
- \+ *lemma* dot_self_cross
- \+ *theorem* jacobi_cross
- \+ *lemma* leibniz_cross
- \+ *theorem* triple_product_eq_det
- \+ *lemma* triple_product_permutation



## [2022-01-13 12:25:20](https://github.com/leanprover-community/mathlib/commit/799cdbb)
feat(data/nat/periodic): periodic functions for nat ([#10888](https://github.com/leanprover-community/mathlib/pull/10888))
Adds a lemma saying that the cardinality of an Ico of length `a` filtered over a periodic predicate of period `a` is the same as the cardinality of `range a` filtered over that predicate.
#### Estimated changes
Modified src/data/int/interval.lean
- \+ *lemma* int.image_Ico_mod

Modified src/data/nat/interval.lean
- \+ *lemma* nat.image_Ico_mod
- \+ *lemma* nat.mod_inj_on_Ico
- \+ *lemma* nat.multiset_Ico_map_mod

Added src/data/nat/periodic.lean
- \+ *lemma* function.periodic.map_mod_nat
- \+ *lemma* nat.filter_Ico_card_eq_of_periodic
- \+ *lemma* nat.filter_multiset_Ico_card_eq_of_periodic
- \+ *lemma* nat.periodic_coprime
- \+ *lemma* nat.periodic_gcd
- \+ *lemma* nat.periodic_mod



## [2022-01-13 12:25:18](https://github.com/leanprover-community/mathlib/commit/6609204)
feat(algebraic_geometry): Gluing presheafed spaces ([#10269](https://github.com/leanprover-community/mathlib/pull/10269))
#### Estimated changes
Added src/algebraic_geometry/presheafed_space/gluing.lean
- \+ *lemma* algebraic_geometry.PresheafedSpace.coe_to_fun_eq
- \+ *abbreviation* algebraic_geometry.PresheafedSpace.glue_data.diagram_over_open
- \+ *abbreviation* algebraic_geometry.PresheafedSpace.glue_data.diagram_over_open_π
- \+ *lemma* algebraic_geometry.PresheafedSpace.glue_data.f_inv_app_f_app
- \+ *def* algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map
- \+ *lemma* algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map_app'
- \+ *lemma* algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map_app
- \+ *lemma* algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map_app_assoc
- \+ *lemma* algebraic_geometry.PresheafedSpace.glue_data.pullback_base
- \+ *lemma* algebraic_geometry.PresheafedSpace.glue_data.snd_inv_app_t_app'
- \+ *lemma* algebraic_geometry.PresheafedSpace.glue_data.snd_inv_app_t_app
- \+ *abbreviation* algebraic_geometry.PresheafedSpace.glue_data.to_Top_glue_data
- \+ *lemma* algebraic_geometry.PresheafedSpace.glue_data.ι_image_preimage_eq
- \+ *def* algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app
- \+ *lemma* algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app_π
- \+ *def* algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app_π_app
- \+ *abbreviation* algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app_π_eq_map
- \+ *lemma* algebraic_geometry.PresheafedSpace.glue_data.ι_open_embedding
- \+ *lemma* algebraic_geometry.PresheafedSpace.glue_data.π_ι_inv_app_eq_id
- \+ *lemma* algebraic_geometry.PresheafedSpace.glue_data.π_ι_inv_app_π
- \+ *structure* algebraic_geometry.PresheafedSpace.glue_data

Modified src/topology/category/Top/limits.lean
- \+ *lemma* Top.pullback_fst_image_snd_preimage
- \+ *lemma* Top.pullback_snd_image_fst_preimage



## [2022-01-13 07:08:20](https://github.com/leanprover-community/mathlib/commit/e6db245)
chore(ring_theory/roots_of_unity): change argument order ([#11415](https://github.com/leanprover-community/mathlib/pull/11415))
this is for easier dot notation in situations such as `refine`.
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+/\- *lemma* is_primitive_root.map_of_injective
- \+/\- *lemma* is_primitive_root.of_map_of_injective



## [2022-01-13 07:08:19](https://github.com/leanprover-community/mathlib/commit/0c84456)
feat(order,data/set/intervals): lemmas about `is_bot`/`is_top` ([#11412](https://github.com/leanprover-community/mathlib/pull/11412))
* add `is_top.Iic_eq`, `is_bot.Ici_eq`, `is_top.Ioi_eq`,
  `is_bot.Iio_eq`, `set.Ioi_top`, `set.Iio_bot`;
* rename `set.Ici_singleton_of_top` and `set.Iic_singleton_of_bot` to
  `is_top.Ici_eq` and `is_bot.Iic_eq`;
* add `is_top_or_exists_gt`, `is_bot_or_exists_lt`, `is_top_top`, and
  `is_bot_bot`;
* add `is_top.to_dual` and `is_bot.to_dual`;
* add `set.empty_ssubset`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.empty_ssubset

Modified src/data/set/intervals/basic.lean
- \+ *lemma* is_bot.Ici_eq
- \+ *lemma* is_bot.Iic_eq
- \+ *lemma* is_bot.Iio_eq
- \+ *lemma* is_top.Ici_eq
- \+ *lemma* is_top.Iic_eq
- \+ *lemma* is_top.Ioi_eq
- \+/\- *lemma* set.Ici_bot
- \- *lemma* set.Ici_singleton_of_top
- \+/\- *lemma* set.Iic_inter_Ioc_of_le
- \- *lemma* set.Iic_singleton_of_bot
- \+/\- *lemma* set.Iic_top
- \+ *lemma* set.Iio_bot
- \+ *lemma* set.Ioi_top

Modified src/order/basic.lean
- \+ *lemma* is_bot_or_exists_lt
- \+ *lemma* is_top_or_exists_gt

Modified src/order/bounded_order.lean
- \+ *lemma* is_bot_bot
- \+ *theorem* is_top_top

Modified src/order/order_dual.lean
- \+ *lemma* is_bot.to_dual
- \+ *lemma* is_top.to_dual



## [2022-01-13 07:08:17](https://github.com/leanprover-community/mathlib/commit/3f1ac6c)
doc(number_theory/cyclotomic/basic): fix docstrings ([#11411](https://github.com/leanprover-community/mathlib/pull/11411))
#### Estimated changes
Modified src/number_theory/cyclotomic/basic.lean




## [2022-01-13 07:08:16](https://github.com/leanprover-community/mathlib/commit/e839c9a)
feat(combinatorics/configuration): Cardinality results for projective plane. ([#11406](https://github.com/leanprover-community/mathlib/pull/11406))
This PR proves several cardinality results for projective planes (e.g., number of points = number of lines, number of points on given line = number of lines on given point).
It looks like the `exists_config` (whose sole purpose is to rule out [the 7th example here](https://en.wikipedia.org/wiki/Projective_plane#Degenerate_planes)) can be weakened slightly.
#### Estimated changes
Modified src/combinatorics/configuration.lean
- \+ *lemma* configuration.projective_plane.card_points_eq_card_lines
- \+ *lemma* configuration.projective_plane.line_count_eq_line_count
- \+ *lemma* configuration.projective_plane.line_count_eq_point_count
- \+ *lemma* configuration.projective_plane.point_count_eq_point_count



## [2022-01-13 06:20:13](https://github.com/leanprover-community/mathlib/commit/12b6b99)
refactor(linear_algebra/affine_space): move def of `slope` to a new file ([#11361](https://github.com/leanprover-community/mathlib/pull/11361))
Also add a few trivial lemmas.
#### Estimated changes
Modified src/linear_algebra/affine_space/ordered.lean
- \- *lemma* eq_of_slope_eq_zero
- \- *lemma* line_map_slope_line_map_slope_line_map
- \- *lemma* line_map_slope_slope_sub_div_sub
- \- *def* slope
- \- *lemma* slope_comm
- \- *lemma* slope_def_field
- \- *lemma* slope_same
- \- *lemma* sub_div_sub_smul_slope_add_sub_div_sub_smul_slope

Added src/linear_algebra/affine_space/slope.lean
- \+ *lemma* eq_of_slope_eq_zero
- \+ *lemma* line_map_slope_line_map_slope_line_map
- \+ *lemma* line_map_slope_slope_sub_div_sub
- \+ *def* slope
- \+ *lemma* slope_comm
- \+ *lemma* slope_def_field
- \+ *lemma* slope_def_module
- \+ *lemma* slope_same
- \+ *lemma* slope_sub_smul
- \+ *lemma* slope_vadd_const
- \+ *lemma* sub_div_sub_smul_slope_add_sub_div_sub_smul_slope
- \+ *lemma* sub_smul_slope
- \+ *lemma* sub_smul_slope_vadd



## [2022-01-13 01:42:28](https://github.com/leanprover-community/mathlib/commit/3fed75a)
doc(data/pfun): fix a typo ([#11410](https://github.com/leanprover-community/mathlib/pull/11410))
#### Estimated changes
Modified src/data/pfun.lean




## [2022-01-13 01:42:26](https://github.com/leanprover-community/mathlib/commit/dfad4c6)
fix(data/equiv/set): Fix doc comment syntax ([#11409](https://github.com/leanprover-community/mathlib/pull/11409))
#### Estimated changes
Modified src/data/equiv/set.lean




## [2022-01-13 01:42:25](https://github.com/leanprover-community/mathlib/commit/1f370bb)
feat(linear_algebra/pi): linear_map.vec_cons and friends ([#11343](https://github.com/leanprover-community/mathlib/pull/11343))
The idea of these definitions is to be able to define a map as `x ↦ ![f₁ x, f₂ x, f₃ x]`, where
`f₁ f₂ f₃` are already linear maps, as `f₁.vec_cons $ f₂.vec_cons $ f₃.vec_cons $ vec_empty`.
This adds the same thing for bilinear maps as `x y ↦ ![f₁ x y, f₂ x y, f₃ x y]`.
While the same thing could be achieved using `linear_map.pi ![f₁, f₂, f₃]`, this is not
definitionally equal to the result using `linear_map.vec_cons`, as `fin.cases` and function
application do not commute definitionally.
Versions for when `f₁ f₂ f₃` are bilinear maps are also provided.
#### Estimated changes
Modified src/linear_algebra/pi.lean
- \+ *def* linear_map.vec_cons
- \+ *lemma* linear_map.vec_cons_apply
- \+ *def* linear_map.vec_cons₂
- \+ *def* linear_map.vec_empty
- \+ *lemma* linear_map.vec_empty_apply
- \+ *def* linear_map.vec_empty₂



## [2022-01-12 22:49:45](https://github.com/leanprover-community/mathlib/commit/e6fab1d)
refactor(order/directed): Make `is_directed` a Prop mixin ([#11238](https://github.com/leanprover-community/mathlib/pull/11238))
This turns `directed_order` into a Prop-valued mixin `is_directed`. The design follows the unbundled relation classes found in core Lean.
The current design created obscure problems when showing that a `semilattice_sup` is directed and we couldn't even state that `semilattice_inf` is codirected. Further, it was kind of already used as a mixin, because there was no point inserting it in the hierarchy.
#### Estimated changes
Modified src/algebra/category/Module/limits.lean
- \+/\- *def* Module.direct_limit_is_colimit

Modified src/algebra/direct_limit.lean
- \+/\- *lemma* add_comm_group.direct_limit.lift_unique
- \+/\- *theorem* add_comm_group.direct_limit.of.zero_exact
- \+/\- *theorem* module.direct_limit.exists_of
- \+/\- *theorem* module.direct_limit.lift_unique
- \+/\- *theorem* module.direct_limit.of.zero_exact
- \+/\- *lemma* module.direct_limit.of.zero_exact_aux
- \+/\- *theorem* ring.direct_limit.exists_of
- \+/\- *theorem* ring.direct_limit.induction_on
- \+/\- *theorem* ring.direct_limit.lift_unique
- \+/\- *lemma* ring.direct_limit.of.zero_exact
- \+/\- *lemma* ring.direct_limit.of.zero_exact_aux
- \+/\- *theorem* ring.direct_limit.of_injective
- \+/\- *theorem* ring.direct_limit.polynomial.exists_of

Modified src/analysis/convex/caratheodory.lean


Modified src/analysis/convex/quasiconvex.lean
- \+/\- *lemma* quasiconcave_on.convex
- \+/\- *lemma* quasiconvex_on.convex

Modified src/category_theory/filtered.lean


Modified src/combinatorics/hall/basic.lean
- \- *def* hall_finset_directed_order

Modified src/data/finset/order.lean
- \+ *lemma* finset.exists_le
- \- *theorem* finset.exists_le

Modified src/data/real/nnreal.lean


Modified src/group_theory/congruence.lean


Modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* measure_theory.simple_func.exists_forall_le

Modified src/order/directed.lean
- \+ *lemma* directed_id
- \+ *lemma* directed_id_iff_is_directed
- \+ *lemma* directed_of
- \+ *lemma* exists_ge_ge
- \+ *lemma* exists_le_le
- \+ *lemma* is_directed_mono

Modified src/order/rel_classes.lean


Modified src/ring_theory/valuation/integral.lean


Modified src/topology/algebra/floor_ring.lean


Modified src/topology/category/Top/limits.lean




## [2022-01-12 20:51:38](https://github.com/leanprover-community/mathlib/commit/2a38097)
feat(combinatorics/configuration): Define projective planes ([#11390](https://github.com/leanprover-community/mathlib/pull/11390))
This PR defines abstract projective planes and their duals. More will be PRed later.
#### Estimated changes
Modified src/combinatorics/configuration.lean




## [2022-01-12 17:52:39](https://github.com/leanprover-community/mathlib/commit/5e48b21)
feat(number_theory/cyclotomic/basic): add cyclotomic_field and cyclotomic_ring ([#11383](https://github.com/leanprover-community/mathlib/pull/11383))
We add `cyclotomic_field` and `cyclotomic_ring`, that provide an explicit cyclotomic extension of a given field/ring.
From flt-regular
#### Estimated changes
Modified src/number_theory/cyclotomic/basic.lean
- \+ *def* cyclotomic_field.algebra_base
- \+ *def* cyclotomic_field
- \+ *lemma* cyclotomic_ring.adjoin_algebra_injective
- \+ *def* cyclotomic_ring.algebra_base
- \+ *lemma* cyclotomic_ring.algebra_base_injective
- \+ *def* cyclotomic_ring

Modified src/ring_theory/localization.lean




## [2022-01-12 17:52:38](https://github.com/leanprover-community/mathlib/commit/fa9d2bf)
feat(data/mv_polynomial/variables): add mv_polynomial.total_deg_finset_sum ([#11375](https://github.com/leanprover-community/mathlib/pull/11375))
Total degree of a sum of mv_polynomials is less than or equal to the maximum of all their degrees.
#### Estimated changes
Modified src/data/mv_polynomial/variables.lean
- \+ *lemma* mv_polynomial.total_degree_finset_sum



## [2022-01-12 17:52:37](https://github.com/leanprover-community/mathlib/commit/258686f)
fix(order/complete_lattice): fix diamond in sup vs max and min vs inf ([#11309](https://github.com/leanprover-community/mathlib/pull/11309))
`complete_linear_order` has separate `max` and `sup` fields. There is no need to have both, so this removes one of them by telling the structure compiler to merge the two fields. The same is true of `inf` and `min`.
As well as diamonds being possible in the abstract case, a handful of concrete example of this diamond existed.
`linear_order` instances with default-populated fields were usually to blame.
#### Estimated changes
Modified src/algebra/tropical/big_operators.lean


Modified src/data/nat/enat.lean
- \- *lemma* enat.inf_eq_min
- \- *lemma* enat.sup_eq_max

Modified src/data/nat/lattice.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.add_top
- \+/\- *lemma* ennreal.top_add

Modified src/order/bounded_order.lean


Modified src/order/complete_lattice.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/lattice.lean
- \+ *lemma* inf_eq_min_default
- \+ *lemma* sup_eq_max_default



## [2022-01-12 16:25:20](https://github.com/leanprover-community/mathlib/commit/975031d)
feat(data/nat/factorization): add lemma `factorization_prod` ([#11395](https://github.com/leanprover-community/mathlib/pull/11395))
For any `p : ℕ` and any function `g : α → ℕ` that's non-zero on `S : finset α`, the power of `p` in `S.prod g` equals the sum over `x ∈ S` of the powers of `p` in `g x`.
Generalises `factorization_mul`, which is the special case where `S.card = 2` and `g = id`.
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+ *lemma* nat.factorization_prod



## [2022-01-12 16:25:17](https://github.com/leanprover-community/mathlib/commit/67593dc)
fix(tactic/ring_exp): fix normalization proof of unchanged subexpressions ([#11394](https://github.com/leanprover-community/mathlib/pull/11394))
When trying to simplify a goal (instead of proving equalities), `ring_exp` will rewrite subexpressions to a normal form, then simplify this normal form by removing extraneous `+ 0`s and `* 1`s. Both steps return a new expression and a proof that the *step*'s input expression equals the output expression.
In some cases where the normal form and simplified form coincide, `ex.simplify` would instead output a proof that *ring_exp*'s input expression equals the output expression, so we'd get a type error in trying to compose a proof that `a = b` with a proof that `a = b`.
This PR fixes that bug by returning instead a proof that `b = b`, as expected.
#### Estimated changes
Modified src/tactic/ring_exp.lean


Modified test/ring_exp.lean




## [2022-01-12 13:36:56](https://github.com/leanprover-community/mathlib/commit/aece00a)
feat(data/sigma/interval): A disjoint sum of locally finite orders is locally finite ([#10929](https://github.com/leanprover-community/mathlib/pull/10929))
This provides `locally_finite_order (Σ i, α i)` in a new file `data.sigma.interval`. This also makes `<` a primitive on `Σ i, α i`.
#### Estimated changes
Added src/data/sigma/interval.lean
- \+ *lemma* sigma.Icc_mk_mk
- \+ *lemma* sigma.Ico_mk_mk
- \+ *lemma* sigma.Ioc_mk_mk
- \+ *lemma* sigma.Ioo_mk_mk
- \+ *lemma* sigma.card_Icc
- \+ *lemma* sigma.card_Ico
- \+ *lemma* sigma.card_Ioc
- \+ *lemma* sigma.card_Ioo

Modified src/data/sigma/order.lean
- \+ *lemma* sigma.le_def
- \+ *inductive* sigma.lt
- \+ *lemma* sigma.lt_def
- \+ *lemma* sigma.mk_le_mk_iff
- \+ *lemma* sigma.mk_lt_mk_iff

Modified src/order/locally_finite.lean




## [2022-01-12 11:08:51](https://github.com/leanprover-community/mathlib/commit/e8eb7d9)
feat(order/cover): `f a` covers `f b` iff `a` covers `b`  ([#11392](https://github.com/leanprover-community/mathlib/pull/11392))
... for order isomorphisms, and also weaker statements.
#### Estimated changes
Modified src/order/cover.lean
- \+ *lemma* apply_covers_apply_iff
- \+ *lemma* covers.image
- \+ *lemma* covers.of_image
- \+ *lemma* densely_ordered_iff_forall_not_covers
- \+ *lemma* of_dual_covers_of_dual_iff



## [2022-01-12 10:06:13](https://github.com/leanprover-community/mathlib/commit/912c47d)
feat(topology/algebra/continuous_monoid_hom): New file ([#11304](https://github.com/leanprover-community/mathlib/pull/11304))
This PR defines continuous monoid homs.
#### Estimated changes
Added src/topology/algebra/continuous_monoid_hom.lean
- \+ *structure* continuous_add_monoid_hom
- \+ *def* continuous_monoid_hom.comp
- \+ *def* continuous_monoid_hom.coprod
- \+ *def* continuous_monoid_hom.diag
- \+ *lemma* continuous_monoid_hom.ext
- \+ *def* continuous_monoid_hom.fst
- \+ *def* continuous_monoid_hom.id
- \+ *def* continuous_monoid_hom.inl
- \+ *def* continuous_monoid_hom.inr
- \+ *def* continuous_monoid_hom.inv
- \+ *def* continuous_monoid_hom.mk'
- \+ *def* continuous_monoid_hom.mul
- \+ *def* continuous_monoid_hom.one
- \+ *def* continuous_monoid_hom.prod
- \+ *def* continuous_monoid_hom.prod_map
- \+ *def* continuous_monoid_hom.snd
- \+ *def* continuous_monoid_hom.swap
- \+ *structure* continuous_monoid_hom



## [2022-01-12 07:31:06](https://github.com/leanprover-community/mathlib/commit/c1f3f1a)
feat(analysis/complex/basic): determinant of `conj_lie` ([#11389](https://github.com/leanprover-community/mathlib/pull/11389))
Add lemmas giving the determinant of `conj_lie`, as a linear map and
as a linear equiv, deduced from the corresponding lemmas for `conj_ae`
which is used to define `conj_lie`.  This completes the basic lemmas
about determinants of linear isometries of `ℂ` (which can thus be used
to talk about how those isometries affect orientations), since we also
have `linear_isometry_complex` describing all such isometries in terms
of `rotation` and `conj_lie`.
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* complex.det_conj_lie
- \+ *lemma* complex.linear_equiv_det_conj_lie



## [2022-01-12 07:31:04](https://github.com/leanprover-community/mathlib/commit/72c86c3)
chore(algebra/ring/basic): generalize `is_domain.to_cancel_monoid_with_zero` to `no_zero_divisors` ([#11387](https://github.com/leanprover-community/mathlib/pull/11387))
This generalization doesn't work for typeclass search as `cancel_monoid_with_zero` implies `no_zero_divisors` which would form a loop, but it can be useful for a `letI` in another proof.
Independent of whether this turns out to be useful, it's nice to show that nontriviality doesn't affect the fact that rings with no zero divisors are cancellative.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *def* no_zero_divisors.to_cancel_monoid_with_zero



## [2022-01-12 07:31:03](https://github.com/leanprover-community/mathlib/commit/cb1b6d9)
feat(algebra/order/floor): adds some missing floor API ([#11336](https://github.com/leanprover-community/mathlib/pull/11336))
#### Estimated changes
Modified src/algebra/order/floor.lean
- \+/\- *lemma* int.ceil_to_nat
- \+/\- *lemma* int.floor_to_nat
- \+ *lemma* nat.cast_ceil_eq_cast_int_ceil
- \+ *lemma* nat.cast_ceil_eq_int_ceil
- \+ *lemma* nat.cast_floor_eq_cast_int_floor
- \+ *lemma* nat.cast_floor_eq_int_floor
- \+ *lemma* nat.floor_le_of_le



## [2022-01-12 07:31:02](https://github.com/leanprover-community/mathlib/commit/bfe9515)
feat(data/multiset/basic): add map_count_true_eq_filter_card ([#11306](https://github.com/leanprover-community/mathlib/pull/11306))
Add a lemma about counting over a map. Spun off of [#10888](https://github.com/leanprover-community/mathlib/pull/10888).
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.count_eq_card_filter_eq
- \+ *lemma* multiset.map_count_true_eq_filter_card



## [2022-01-12 07:31:00](https://github.com/leanprover-community/mathlib/commit/9fd03e1)
chore(order/lexicographic): cleanup ([#11299](https://github.com/leanprover-community/mathlib/pull/11299))
Changes include:
* factoring out `prod.lex.trans` from the proof of `le_trans` in `prod.lex.has_le`, and similarly for `antisymm` and `is_total`
* adding some missing `to_lex` annotations in the `prod.lex.{le,lt}_def` lemmas
* avoiding reproving decidability of `prod.lex`
* replacing some proofs with pattern matching to avoid getting type-incorrect goals where `prod.lex.has_le` appears comparing terms that are not of type `lex`.
#### Estimated changes
Modified src/data/prod.lean
- \+ *lemma* prod.lex.refl_left
- \+ *lemma* prod.lex.refl_right
- \+ *lemma* prod.lex.trans

Modified src/order/lexicographic.lean
- \+/\- *lemma* prod.lex.le_iff
- \+/\- *lemma* prod.lex.lt_iff



## [2022-01-12 07:30:59](https://github.com/leanprover-community/mathlib/commit/deac58a)
feat(topology/uniform_space/compact_convergence): when the domain is locally compact, compact convergence is just locally uniform convergence ([#11292](https://github.com/leanprover-community/mathlib/pull/11292))
Also, locally uniform convergence is just uniform convergence when the domain is compact.
#### Estimated changes
Modified src/topology/uniform_space/compact_convergence.lean
- \+/\- *lemma* continuous_map.tendsto_iff_forall_compact_tendsto_uniformly_on
- \+ *lemma* continuous_map.tendsto_iff_tendsto_locally_uniformly
- \+/\- *lemma* continuous_map.tendsto_iff_tendsto_uniformly
- \+ *lemma* continuous_map.tendsto_locally_uniformly_of_tendsto
- \+ *lemma* continuous_map.tendsto_of_tendsto_locally_uniformly

Modified src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* tendsto_locally_uniformly_iff_tendsto_uniformly_of_compact_space
- \+ *lemma* tendsto_locally_uniformly_on_iff_tendsto_locally_uniformly_comp_coe
- \+ *lemma* tendsto_locally_uniformly_on_iff_tendsto_uniformly_on_of_compact
- \+ *lemma* tendsto_uniformly_on_iff_tendsto_uniformly_comp_coe



## [2022-01-12 07:30:58](https://github.com/leanprover-community/mathlib/commit/2099725)
feat(topology/homotopy/product): Product of homotopic paths ([#11153](https://github.com/leanprover-community/mathlib/pull/11153))
Specialize homotopy products to paths and prove some theorems about the product of paths.
#### Estimated changes
Modified src/topology/homotopy/fundamental_groupoid.lean


Modified src/topology/homotopy/path.lean
- \+ *lemma* path.homotopic.comp_lift
- \+ *lemma* path.homotopic.map_lift
- \+ *def* path.homotopic.quotient.comp
- \+ *def* path.homotopic.quotient.map_fn

Modified src/topology/homotopy/product.lean
- \+ *lemma* path.homotopic.comp_pi_eq_pi_comp
- \+ *lemma* path.homotopic.comp_prod_eq_prod_comp
- \+ *def* path.homotopic.pi
- \+ *def* path.homotopic.pi_homotopy
- \+ *lemma* path.homotopic.pi_lift
- \+ *lemma* path.homotopic.pi_proj
- \+ *def* path.homotopic.prod
- \+ *def* path.homotopic.prod_homotopy
- \+ *lemma* path.homotopic.prod_lift
- \+ *lemma* path.homotopic.prod_proj_left_proj_right
- \+ *def* path.homotopic.proj
- \+ *def* path.homotopic.proj_left
- \+ *lemma* path.homotopic.proj_left_prod
- \+ *lemma* path.homotopic.proj_pi
- \+ *def* path.homotopic.proj_right
- \+ *lemma* path.homotopic.proj_right_prod

Modified src/topology/path_connected.lean
- \+ *lemma* path.pi_coe_fn
- \+ *lemma* path.prod_coe_fn
- \+ *lemma* path.trans_pi_eq_pi_trans
- \+ *lemma* path.trans_prod_eq_prod_trans



## [2022-01-12 05:04:58](https://github.com/leanprover-community/mathlib/commit/15b5e24)
feat(data/polynomial/taylor): taylor's formula ([#11139](https://github.com/leanprover-community/mathlib/pull/11139))
Via proofs about `hasse_deriv`.
Added some monomial API too.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.sup_ite

Modified src/data/nat/with_bot.lean
- \+ *lemma* nat.with_bot.lt_one_iff_le_zero

Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* polynomial.degree_C_lt
- \+ *lemma* polynomial.leading_coeff_pow_X_add_C

Modified src/data/polynomial/hasse_deriv.lean
- \+ *lemma* polynomial.hasse_deriv_eq_zero_of_lt_nat_degree
- \+ *lemma* polynomial.nat_degree_hasse_deriv
- \+ *lemma* polynomial.nat_degree_hasse_deriv_le

Modified src/data/polynomial/taylor.lean
- \+ *lemma* polynomial.nat_degree_taylor
- \+ *lemma* polynomial.sum_taylor_eq
- \+ *lemma* polynomial.taylor_monomial
- \+ *lemma* polynomial.taylor_taylor
- \+ *lemma* polynomial.taylor_zero'
- \+ *lemma* polynomial.taylor_zero



## [2022-01-12 04:02:53](https://github.com/leanprover-community/mathlib/commit/af074c8)
feat(analysis/normed_space/lp_space): API for `lp.single` ([#11307](https://github.com/leanprover-community/mathlib/pull/11307))
Definition and basic properties for `lp.single`, an element of `lp` space supported at one point.
#### Estimated changes
Modified src/analysis/normed_space/lp_space.lean
- \+ *lemma* lp.coe_fn_sum



## [2022-01-12 02:31:11](https://github.com/leanprover-community/mathlib/commit/cdd44cd)
refactor(topology/algebra/uniform_group): Use `to_additive` ([#11366](https://github.com/leanprover-community/mathlib/pull/11366))
This PR replace the definition
`def topological_add_group.to_uniform_space : uniform_space G :=`
with the definition
`@[to_additive] def topological_group.to_uniform_space : uniform_space G :=`
#### Estimated changes
Modified src/topology/algebra/uniform_group.lean
- \- *def* topological_add_group.to_uniform_space
- \+ *def* topological_group.to_uniform_space



## [2022-01-12 00:08:22](https://github.com/leanprover-community/mathlib/commit/89f4786)
feat(analysis/special_functions/pow): norm_num extension for rpow ([#11382](https://github.com/leanprover-community/mathlib/pull/11382))
Fixes [#11374](https://github.com/leanprover-community/mathlib/pull/11374)
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *theorem* zpow_neg_coe_of_pos

Modified src/algebra/star/chsh.lean


Modified src/analysis/special_functions/pow.lean
- \+ *theorem* norm_num.cpow_neg
- \+ *theorem* norm_num.cpow_pos
- \+ *theorem* norm_num.ennrpow_neg
- \+ *theorem* norm_num.ennrpow_pos
- \+ *theorem* norm_num.nnrpow_neg
- \+ *theorem* norm_num.nnrpow_pos
- \+ *theorem* norm_num.rpow_neg
- \+ *theorem* norm_num.rpow_pos

Modified src/tactic/norm_num.lean
- \+ *lemma* norm_num.zpow_neg
- \+ *lemma* norm_num.zpow_pos

Modified test/norm_num.lean




## [2022-01-12 00:08:21](https://github.com/leanprover-community/mathlib/commit/647598b)
feat(data/nat/factorization): add lemma `factorization_le_iff_dvd` ([#11377](https://github.com/leanprover-community/mathlib/pull/11377))
For non-zero `d n : ℕ`, `d.factorization ≤ n.factorization ↔ d ∣ n`
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+ *lemma* nat.factorization_le_iff_dvd



## [2022-01-11 20:49:16](https://github.com/leanprover-community/mathlib/commit/a5f7909)
fix(algebra/tropical/basic): provide explicit min and max ([#11380](https://github.com/leanprover-community/mathlib/pull/11380))
This also renames `tropical.add` to `tropical.has_add`, since this matches how we normally do this, and it makes unfolding easier.
Without this change, we have a diamond where `linear_order.min` is not defeq to `lattice.inf`.
#### Estimated changes
Modified src/algebra/tropical/basic.lean
- \+ *lemma* tropical.inf_eq_add
- \+ *lemma* tropical.min_eq_add
- \+ *lemma* tropical.trop_max_def
- \+ *lemma* tropical.trop_sup_def
- \+ *lemma* tropical.untrop_max
- \+ *lemma* tropical.untrop_sup



## [2022-01-11 20:49:15](https://github.com/leanprover-community/mathlib/commit/73847ff)
feat(algebra/indicator_function): add primed version for `mul_indicator_mul` and `indicator_sub` ([#11379](https://github.com/leanprover-community/mathlib/pull/11379))
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \- *lemma* set.indicator_sub
- \+ *lemma* set.mul_indicator_div'
- \+ *lemma* set.mul_indicator_div
- \+ *lemma* set.mul_indicator_mul'



## [2022-01-11 20:49:14](https://github.com/leanprover-community/mathlib/commit/d1c4961)
feat(data/real/ennreal): add ennreal lemma for `a / 3 + a / 3 + a / 3 = a`  ([#11378](https://github.com/leanprover-community/mathlib/pull/11378))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.add_thirds
- \+ *lemma* ennreal.inv_three_add_inv_three



## [2022-01-11 20:49:13](https://github.com/leanprover-community/mathlib/commit/57a8933)
feat(group_theory/free_group): promote free_group_congr to a mul_equiv ([#11373](https://github.com/leanprover-community/mathlib/pull/11373))
Also some various golfs and cleanups
#### Estimated changes
Modified src/group_theory/free_group.lean
- \+/\- *def* free_group.free_group_congr
- \+ *lemma* free_group.free_group_congr_refl
- \+ *lemma* free_group.free_group_congr_symm
- \+ *lemma* free_group.free_group_congr_trans
- \- *def* free_group.map.aux
- \+/\- *theorem* free_group.map.comp
- \+/\- *lemma* free_group.map.id'
- \+/\- *lemma* free_group.map.id
- \- *def* free_group.map.to_fun
- \+/\- *def* free_group.map
- \+ *lemma* free_group.quot_map_mk



## [2022-01-11 20:49:12](https://github.com/leanprover-community/mathlib/commit/8db96a8)
feat(combinatorics/double_counting): Double-counting the edges of a bipartite graph ([#11372](https://github.com/leanprover-community/mathlib/pull/11372))
This proves a classic of double-counting arguments: If each element of the `|α|` elements on the left is connected to at least `m` elements on the right and each of the `|β|` elements on the right is connected to at most `n` elements on the left, then `|α| * m ≤ |β| * n` because the LHS is less than the number of edges which is less than the RHS.
This is put in a new file `combinatorics.double_counting` with the idea that we could gather double counting arguments here, much as is done with `combinatorics.pigeonhole`.
#### Estimated changes
Added src/combinatorics/double_counting.lean
- \+ *def* finset.bipartite_above
- \+ *lemma* finset.bipartite_above_swap
- \+ *def* finset.bipartite_below
- \+ *lemma* finset.bipartite_below_swap
- \+ *lemma* finset.card_mul_eq_card_mul
- \+ *lemma* finset.card_mul_le_card_mul'
- \+ *lemma* finset.card_mul_le_card_mul
- \+ *lemma* finset.mem_bipartite_above
- \+ *lemma* finset.mem_bipartite_below
- \+ *lemma* finset.sum_card_bipartite_above_eq_sum_card_bipartite_below



## [2022-01-11 20:49:11](https://github.com/leanprover-community/mathlib/commit/93e7741)
feat(ring_theory/witt_vector): Witt vectors over a domain are a domain ([#11346](https://github.com/leanprover-community/mathlib/pull/11346))
#### Estimated changes
Modified src/ring_theory/witt_vector/basic.lean
- \+ *def* witt_vector.constant_coeff

Modified src/ring_theory/witt_vector/defs.lean
- \+ *lemma* witt_vector.add_coeff_zero
- \+ *lemma* witt_vector.mul_coeff_zero

Added src/ring_theory/witt_vector/domain.lean
- \+ *lemma* witt_vector.eq_iterate_verschiebung
- \+ *def* witt_vector.shift
- \+ *lemma* witt_vector.shift_coeff
- \+ *lemma* witt_vector.verschiebung_nonzero
- \+ *lemma* witt_vector.verschiebung_shift

Modified src/ring_theory/witt_vector/identities.lean
- \+ *lemma* witt_vector.coeff_p_pow_eq_zero
- \+ *lemma* witt_vector.iterate_frobenius_coeff
- \+ *lemma* witt_vector.iterate_verschiebung_coeff
- \+ *lemma* witt_vector.iterate_verschiebung_mul
- \+ *lemma* witt_vector.iterate_verschiebung_mul_coeff
- \+ *lemma* witt_vector.iterate_verschiebung_mul_left
- \+ *lemma* witt_vector.mul_char_p_coeff_succ
- \+ *lemma* witt_vector.mul_char_p_coeff_zero
- \+ *lemma* witt_vector.verschiebung_frobenius
- \+ *lemma* witt_vector.verschiebung_frobenius_comm



## [2022-01-11 20:49:09](https://github.com/leanprover-community/mathlib/commit/83b0355)
feat(analysis/complex/isometry): `rotation` matrix representation and determinant ([#11339](https://github.com/leanprover-community/mathlib/pull/11339))
Add lemmas giving the matrix representation of `rotation` (with
respect to `basis_one_I`), and its determinant (both as a linear map
and as a linear equiv).  This is preparation for doing things about
how isometries affect orientations.
#### Estimated changes
Modified src/analysis/complex/isometry.lean
- \+ *lemma* det_rotation
- \+ *lemma* linear_equiv_det_rotation
- \+ *lemma* to_matrix_rotation

Modified src/linear_algebra/general_linear_group.lean


Modified src/number_theory/modular.lean




## [2022-01-11 20:49:08](https://github.com/leanprover-community/mathlib/commit/e4a41e6)
feat(data/complex/module,data/complex/determinant): `conj_ae` matrix representation and determinant ([#11337](https://github.com/leanprover-community/mathlib/pull/11337))
Add lemmas giving the matrix representation of `conj_ae` (with respect
to `basis_one_I`), and its determinant (both as a linear map and as a
linear equiv).  This is preparation for doing things about how
isometries affect orientations (so it's actually `conj_lie` I'm
interested in, but `conj_lie` is defined in terms of `conj_ae` so
proving things first for `conj_ae` seems appropriate).
#### Estimated changes
Added src/data/complex/determinant.lean
- \+ *lemma* complex.det_conj_ae
- \+ *lemma* complex.linear_equiv_det_conj_ae

Modified src/data/complex/module.lean
- \+ *lemma* complex.to_matrix_conj_ae



## [2022-01-11 20:49:07](https://github.com/leanprover-community/mathlib/commit/aa7a439)
feat(algebra/*): injective hom into kernel `map_eq_*_iff` ([#11275](https://github.com/leanprover-community/mathlib/pull/11275))
#### Estimated changes
Modified src/algebra/free_algebra.lean


Modified src/algebra/group/hom.lean
- \+ *lemma* map_eq_one_iff

Modified src/linear_algebra/exterior_algebra.lean


Modified src/linear_algebra/tensor_algebra.lean




## [2022-01-11 20:49:06](https://github.com/leanprover-community/mathlib/commit/94fd004)
feat(order/minimal): Subset of minimal/maximal elements ([#11268](https://github.com/leanprover-community/mathlib/pull/11268))
This defines `minimals r s`/`maximals r s` the minimal/maximal elements of `s` with respect to relation `r`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.sep_empty

Modified src/order/antichain.lean
- \+ *lemma* is_antichain.eq_of_related'
- \- *lemma* is_antichain.mk_is_antichain
- \- *lemma* is_antichain.mk_max
- \- *lemma* is_antichain.mk_subset

Modified src/order/basic.lean
- \+ *lemma* ge_antisymm

Added src/order/minimal.lean
- \+ *lemma* inter_maximals_subset
- \+ *lemma* inter_minimals_subset
- \+ *lemma* is_antichain.max_maximals
- \+ *lemma* is_antichain.max_minimals
- \+ *lemma* is_antichain.maximals_eq
- \+ *lemma* is_antichain.minimals_eq
- \+ *lemma* is_greatest.maximals_eq
- \+ *lemma* is_greatest.mem_maximals
- \+ *lemma* is_least.mem_minimals
- \+ *lemma* is_least.minimals_eq
- \+ *def* maximals
- \+ *lemma* maximals_antichain
- \+ *lemma* maximals_empty
- \+ *lemma* maximals_eq_minimals
- \+ *lemma* maximals_idem
- \+ *lemma* maximals_inter_subset
- \+ *lemma* maximals_mono
- \+ *lemma* maximals_singleton
- \+ *lemma* maximals_subset
- \+ *lemma* maximals_swap
- \+ *lemma* maximals_union
- \+ *def* minimals
- \+ *lemma* minimals_antichain
- \+ *lemma* minimals_empty
- \+ *lemma* minimals_idem
- \+ *lemma* minimals_inter_subset
- \+ *lemma* minimals_mono
- \+ *lemma* minimals_singleton
- \+ *lemma* minimals_subset
- \+ *lemma* minimals_swap
- \+ *lemma* minimals_union
- \+ *lemma* set.subsingleton.maximals_eq
- \+ *lemma* set.subsingleton.minimals_eq

Modified src/order/rel_classes.lean
- \+ *lemma* comm
- \+ *lemma* comm_of



## [2022-01-11 20:49:04](https://github.com/leanprover-community/mathlib/commit/490847e)
feat(data/polynomial/degree/lemmas): add induction principle for non-constant polynomials ([#8463](https://github.com/leanprover-community/mathlib/pull/8463))
This PR introduces an induction principle to prove that a property holds for non-constant polynomials.  It suffices to check that the property holds for
* the sum of a constant polynomial and any polynomial for which the property holds;
* the sum of any two polynomials for which the property holds;
* for non-constant monomials.
I plan to use this to show that polynomials with coefficients in `ℕ` are monotone.
#### Estimated changes
Modified src/data/polynomial/inductions.lean
- \+ *lemma* polynomial.nat_degree_ne_zero_induction_on



## [2022-01-11 17:36:45](https://github.com/leanprover-community/mathlib/commit/b710771)
chore(*): update to 3.38.0c ([#11371](https://github.com/leanprover-community/mathlib/pull/11371))
#### Estimated changes
Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified leanpkg.toml


Modified src/algebra/monoid_algebra/basic.lean


Modified src/algebra/pointwise.lean


Modified src/analysis/analytic/basic.lean


Modified src/category_theory/limits/shapes/wide_pullbacks.lean


Modified src/combinatorics/hall/finite.lean


Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* simple_graph.mem_neighbor_set'

Modified src/computability/tm_to_partrec.lean


Modified src/computability/turing_machine.lean


Modified src/data/dfinsupp/basic.lean


Modified src/data/equiv/basic.lean


Modified src/data/equiv/set.lean


Modified src/data/finset/basic.lean
- \+/\- *lemma* finset.piecewise_coe

Modified src/data/finset/fold.lean


Modified src/data/finsupp/multiset.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_congr'
- \+ *lemma* set.to_finset_congr

Modified src/data/fintype/fin.lean


Modified src/data/list/basic.lean
- \+ *lemma* list.filter_congr'
- \- *lemma* list.filter_congr
- \+ *theorem* list.map_id''

Modified src/data/list/count.lean


Modified src/data/list/intervals.lean


Modified src/data/list/lattice.lean


Modified src/data/list/nodup.lean


Modified src/data/list/perm.lean


Modified src/data/list/permutation.lean


Modified src/data/matrix/block.lean


Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.map_comp_cons
- \+/\- *theorem* multiset.map_congr

Modified src/data/multiset/nodup.lean


Modified src/data/multiset/pi.lean
- \+ *lemma* multiset.pi.cons_ext

Modified src/data/multiset/powerset.lean


Modified src/data/mv_polynomial/basic.lean


Modified src/data/mv_polynomial/rename.lean


Modified src/data/nat/count.lean


Modified src/data/nat/enat.lean


Modified src/data/option/basic.lean
- \+/\- *theorem* option.guard_eq_some'

Modified src/data/pequiv.lean


Modified src/data/pi.lean


Modified src/data/polynomial/basic.lean


Modified src/data/polynomial/derivative.lean


Modified src/data/semiquot.lean


Modified src/data/set/finite.lean


Modified src/data/sym/basic.lean


Modified src/data/vector/basic.lean


Modified src/geometry/manifold/instances/real.lean


Modified src/group_theory/commuting_probability.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/affine_space/basis.lean


Modified src/linear_algebra/affine_space/combination.lean


Modified src/logic/function/basic.lean


Modified src/measure_theory/covering/besicovitch.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/measure_theory/probability_mass_function/constructions.lean


Modified src/order/filter/lift.lean


Modified src/ring_theory/polynomial/symmetric.lean


Modified src/ring_theory/polynomial_algebra.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/set_theory/ordinal_arithmetic.lean


Modified src/tactic/cache.lean


Modified src/tactic/split_ifs.lean


Modified src/topology/algebra/uniform_field.lean


Modified src/topology/bases.lean


Modified src/topology/homotopy/fundamental_groupoid.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/path_connected.lean




## [2022-01-11 13:55:35](https://github.com/leanprover-community/mathlib/commit/b8d2aff)
refactor(ring_theory/discriminant): refactor discr_not_zero_of_linear_independent ([#11370](https://github.com/leanprover-community/mathlib/pull/11370))
`(hcard : fintype.card ι = finite_dimensional.finrank K L) (hli : linear_independent K b)` is better expressed as `b : basis ι K L`.
#### Estimated changes
Modified src/ring_theory/discriminant.lean
- \+ *lemma* algebra.discr_not_zero_of_basis
- \- *lemma* algebra.discr_not_zero_of_linear_independent



## [2022-01-11 13:55:34](https://github.com/leanprover-community/mathlib/commit/380e28e)
chore(set_theory/ordinal_arithmetic): Golfed some proofs ([#11369](https://github.com/leanprover-community/mathlib/pull/11369))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* ordinal.blsub_le_enum_ord
- \+/\- *def* ordinal.enum_ord.order_iso
- \+/\- *theorem* ordinal.enum_ord.strict_mono
- \+/\- *theorem* ordinal.enum_ord.surjective
- \+/\- *def* ordinal.enum_ord
- \+/\- *theorem* ordinal.enum_ord_mem
- \+/\- *theorem* ordinal.enum_ord_range
- \+/\- *theorem* ordinal.eq_enum_ord



## [2022-01-11 13:55:33](https://github.com/leanprover-community/mathlib/commit/2963d7c)
feat(analysis/asymptotics/asymptotics): add `is_bounded_under.is_O_const` ([#11367](https://github.com/leanprover-community/mathlib/pull/11367))
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+ *theorem* filter.is_bounded_under.is_O_const



## [2022-01-11 13:55:32](https://github.com/leanprover-community/mathlib/commit/8f5303a)
refactor(topology/connected): drop `local attribute [instance] connected_component_setoid` ([#11365](https://github.com/leanprover-community/mathlib/pull/11365))
Add a coercion from `X` to `connected_components X` instead.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.disjoint_or_nonempty_inter
- \+/\- *lemma* set.not_disjoint_iff_nonempty_inter

Modified src/topology/category/Profinite/default.lean


Modified src/topology/connected.lean
- \- *lemma* connected_component_nrel_iff
- \- *lemma* connected_component_rel_iff
- \+ *lemma* connected_components.coe_eq_coe'
- \+ *lemma* connected_components.coe_eq_coe
- \+ *lemma* connected_components.coe_ne_coe
- \+ *lemma* connected_components.continuous_coe
- \+ *lemma* connected_components.quotient_map_coe
- \+ *lemma* connected_components.range_coe
- \+ *lemma* connected_components.surjective_coe
- \+/\- *lemma* connected_components_lift_unique'
- \+/\- *lemma* connected_components_preimage_singleton
- \+/\- *def* continuous.connected_components_lift
- \+ *lemma* continuous.connected_components_lift_apply_coe
- \+ *lemma* continuous.connected_components_lift_comp_coe
- \+/\- *lemma* continuous.connected_components_lift_continuous
- \- *lemma* continuous.connected_components_lift_factors
- \+/\- *lemma* continuous.connected_components_lift_unique
- \+ *lemma* continuous.image_eq_of_connected_component_eq
- \- *lemma* continuous.image_eq_of_equiv
- \+ *theorem* disjoint_or_subset_of_clopen
- \+ *lemma* is_clopen.bUnion_connected_component_eq
- \+ *lemma* is_clopen.connected_component_subset
- \- *lemma* is_clopen.eq_union_connected_components
- \+ *theorem* is_preconnected.subset_clopen
- \+/\- *theorem* is_preconnected_iff_subset_of_disjoint_closed
- \+ *lemma* quotient_map.image_connected_component
- \+ *lemma* quotient_map.preimage_connected_component
- \- *theorem* subset_or_disjoint_of_clopen

Modified src/topology/constructions.lean
- \+ *lemma* continuous_quotient_lift_on'

Modified src/topology/separation.lean
- \+/\- *lemma* connected_component_eq_Inter_clopen

Modified src/topology/subset_properties.lean




## [2022-01-11 13:55:30](https://github.com/leanprover-community/mathlib/commit/c1c0fa4)
feat(analysis/calculus/{f,}deriv): add some `iff` lemmas ([#11363](https://github.com/leanprover-community/mathlib/pull/11363))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_at_deriv_iff
- \+ *lemma* has_deriv_within_at_deriv_within_iff

Modified src/analysis/calculus/fderiv.lean
- \+ *theorem* filter.eventually_eq.differentiable_at_iff
- \+ *theorem* filter.eventually_eq.differentiable_within_at_iff
- \+ *theorem* filter.eventually_eq.differentiable_within_at_iff_of_mem
- \+ *theorem* filter.eventually_eq.has_fderiv_at_iff
- \+ *theorem* filter.eventually_eq.has_fderiv_within_at_iff
- \+ *theorem* filter.eventually_eq.has_fderiv_within_at_iff_of_mem



## [2022-01-11 13:55:28](https://github.com/leanprover-community/mathlib/commit/02181c7)
feat(algebra/group/conj): `conj_classes.map` preserves surjectivity ([#11362](https://github.com/leanprover-community/mathlib/pull/11362))
If `f : α →* β` is surjective, then so is `conj_classes.map f : conj_classes α → conj_classes β`.
#### Estimated changes
Modified src/algebra/group/conj.lean
- \+ *lemma* conj_classes.map_surjective



## [2022-01-11 13:55:13](https://github.com/leanprover-community/mathlib/commit/c94a17c)
feat(topology): a few simple lemmas ([#11360](https://github.com/leanprover-community/mathlib/pull/11360))
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* eventually_mem_nhds

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_at_update_same
- \+ *lemma* continuous_within_at_compl_self
- \+ *lemma* continuous_within_at_iff_continuous_at
- \+/\- *lemma* continuous_within_at_update_same
- \+ *lemma* insert_mem_nhds_iff

Modified src/topology/separation.lean
- \+ *lemma* continuous_at_update_of_ne
- \+ *lemma* ne.nhds_within_diff_singleton



## [2022-01-11 13:55:12](https://github.com/leanprover-community/mathlib/commit/56d6a91)
chore(order/basic): Rename `no_bot_order`/`no_top_order` to `no_min_order`/`no_max_order` ([#11357](https://github.com/leanprover-community/mathlib/pull/11357))
because that's really what they are.
`∀ a, ∃ b, b < a` precisely means that every `a` is not a minimal element. The correct statement for an order without bottom elements is `∀ a, ∃ b, ¬ a ≤ b`, which is a weaker condition in general. Both conditions are equivalent over a linear order.
Renames
* `no_bot_order` -> `no_min_order`
* `no_top_order` -> `no_max_order`
* `no_bot` -> `exists_lt`
* `no_top` -> `exists_gt`
#### Estimated changes
Modified src/algebra/order/group.lean


Modified src/algebra/order/nonneg.lean


Modified src/algebra/order/ring.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* normed_group.tendsto_at_top'

Modified src/data/psigma/order.lean


Modified src/data/real/nnreal.lean


Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* set.nonempty_Iio
- \+/\- *lemma* set.nonempty_Ioi

Modified src/data/set/intervals/infinite.lean


Modified src/data/sigma/order.lean


Modified src/data/sum/order.lean
- \- *lemma* sum.no_bot_order_iff
- \+ *lemma* sum.no_max_order_iff
- \+ *lemma* sum.no_min_order_iff
- \- *lemma* sum.no_top_order_iff

Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/integral/integral_eq_improper.lean
- \+/\- *lemma* measure_theory.ae_cover_Ico
- \+/\- *lemma* measure_theory.ae_cover_Iio
- \+/\- *lemma* measure_theory.ae_cover_Ioc
- \+/\- *lemma* measure_theory.ae_cover_Ioi
- \+/\- *lemma* measure_theory.ae_cover_Ioo
- \+/\- *lemma* measure_theory.integrable_of_interval_integral_norm_tendsto
- \+/\- *lemma* measure_theory.integrable_on_Iic_of_interval_integral_norm_tendsto
- \+/\- *lemma* measure_theory.interval_integral_tendsto_integral
- \+/\- *lemma* measure_theory.interval_integral_tendsto_integral_Iic

Modified src/measure_theory/integral/interval_integral.lean


Modified src/order/basic.lean
- \+ *lemma* exists_gt
- \+ *lemma* exists_lt
- \- *lemma* no_bot
- \- *lemma* no_top
- \+/\- *lemma* not_is_bot
- \+/\- *lemma* not_is_top

Modified src/order/bounded_order.lean
- \+/\- *lemma* with_top.lt_iff_exists_coe_btwn

Modified src/order/bounds.lean
- \+/\- *lemma* is_glb.nonempty
- \+/\- *lemma* is_lub.nonempty
- \- *lemma* no_bot_order.lower_bounds_univ
- \+ *lemma* no_max_order.upper_bounds_univ
- \+ *lemma* no_min_order.lower_bounds_univ
- \- *lemma* no_top_order.upper_bounds_univ
- \+/\- *lemma* not_bdd_above_univ
- \+/\- *lemma* not_bdd_below_univ

Modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* cInf_Ioi
- \+/\- *lemma* cSup_Iio

Modified src/order/countable_dense_linear_order.lean
- \+/\- *def* order.partial_iso.defined_at_left
- \+/\- *def* order.partial_iso.defined_at_right
- \+/\- *lemma* order.partial_iso.exists_across
- \+/\- *def* order.partial_iso.fun_of_ideal
- \+/\- *def* order.partial_iso.inv_of_ideal

Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* filter.Iio_mem_at_bot
- \+/\- *lemma* filter.Ioi_mem_at_top
- \+/\- *lemma* filter.at_top_basis_Ioi
- \+/\- *lemma* filter.eventually_gt_at_top
- \+/\- *lemma* filter.eventually_lt_at_bot
- \+/\- *lemma* filter.exists_lt_of_tendsto_at_bot
- \+/\- *lemma* filter.exists_lt_of_tendsto_at_top
- \+/\- *lemma* filter.frequently_at_bot'
- \+/\- *lemma* filter.frequently_at_top'
- \+/\- *lemma* filter.frequently_high_scores
- \+/\- *lemma* filter.frequently_low_scores
- \+/\- *lemma* filter.high_scores
- \+/\- *lemma* filter.low_scores
- \+/\- *lemma* filter.map_coe_Iio_at_bot
- \+/\- *lemma* filter.map_coe_Ioi_at_top
- \+/\- *lemma* filter.tendsto_comp_coe_Iio_at_bot
- \+/\- *lemma* filter.tendsto_comp_coe_Ioi_at_top
- \+/\- *lemma* filter.unbounded_of_tendsto_at_bot'
- \+/\- *lemma* filter.unbounded_of_tendsto_at_bot
- \+/\- *lemma* filter.unbounded_of_tendsto_at_top'
- \+/\- *lemma* filter.unbounded_of_tendsto_at_top

Modified src/order/lattice_intervals.lean


Modified src/order/liminf_limsup.lean
- \+/\- *lemma* filter.not_is_bounded_under_of_tendsto_at_bot
- \+/\- *lemma* filter.not_is_bounded_under_of_tendsto_at_top

Modified src/order/locally_finite.lean


Modified src/order/succ_pred.lean
- \+/\- *lemma* pred_succ
- \+/\- *lemma* succ_pred

Modified src/set_theory/cardinal.lean


Modified src/set_theory/ordinal.lean


Modified src/topology/algebra/ordered/basic.lean
- \+/\- *lemma* closure_Iio
- \+/\- *lemma* closure_Ioi
- \+/\- *lemma* dense.exists_ge
- \+/\- *lemma* dense.exists_gt
- \+/\- *lemma* dense.exists_le
- \+/\- *lemma* dense.exists_lt
- \+/\- *lemma* disjoint_nhds_at_bot
- \+/\- *lemma* disjoint_nhds_at_top
- \+/\- *lemma* exists_seq_strict_anti_tendsto
- \+/\- *lemma* exists_seq_strict_mono_tendsto
- \+/\- *lemma* filter.eventually.exists_Ioo_subset
- \+/\- *lemma* filter.eventually.exists_gt
- \+/\- *lemma* filter.eventually.exists_lt
- \+/\- *lemma* frontier_Icc
- \+/\- *lemma* frontier_Ici
- \+/\- *lemma* frontier_Ico
- \+/\- *lemma* frontier_Iic
- \+/\- *lemma* frontier_Iio
- \+/\- *lemma* frontier_Ioc
- \+/\- *lemma* frontier_Ioi
- \+/\- *lemma* inf_nhds_at_bot
- \+/\- *lemma* inf_nhds_at_top
- \+/\- *lemma* interior_Icc
- \+/\- *lemma* interior_Ici
- \+/\- *lemma* interior_Ico
- \+/\- *lemma* interior_Iic
- \+/\- *lemma* interior_Ioc
- \+/\- *lemma* mem_nhds_iff_exists_Ioo_subset
- \+/\- *lemma* mem_nhds_within_Ici_iff_exists_Icc_subset'
- \+/\- *lemma* mem_nhds_within_Ici_iff_exists_Icc_subset
- \+/\- *lemma* mem_nhds_within_Ici_iff_exists_Ico_subset
- \+/\- *lemma* mem_nhds_within_Iic_iff_exists_Icc_subset'
- \+/\- *lemma* mem_nhds_within_Iic_iff_exists_Icc_subset
- \+/\- *lemma* mem_nhds_within_Iic_iff_exists_Ioc_subset
- \+/\- *lemma* mem_nhds_within_Iio_iff_exists_Ico_subset
- \+/\- *lemma* mem_nhds_within_Iio_iff_exists_Ioo_subset
- \+/\- *lemma* mem_nhds_within_Ioi_iff_exists_Ioc_subset
- \+/\- *lemma* mem_nhds_within_Ioi_iff_exists_Ioo_subset
- \+/\- *lemma* nhds_basis_Ioo
- \+/\- *lemma* nhds_basis_Ioo_pos
- \+/\- *lemma* nhds_basis_Ioo_pos_of_pos
- \+/\- *lemma* nhds_basis_abs_sub_lt
- \+/\- *lemma* nhds_basis_zero_abs_sub_lt
- \+/\- *lemma* nhds_within_Iio_ne_bot
- \+/\- *lemma* nhds_within_Iio_self_ne_bot
- \+/\- *lemma* nhds_within_Ioi_ne_bot
- \+/\- *lemma* nhds_within_Ioi_self_ne_bot
- \+/\- *lemma* not_tendsto_at_bot_of_tendsto_nhds
- \+/\- *lemma* not_tendsto_at_top_of_tendsto_nhds
- \+/\- *lemma* not_tendsto_nhds_of_tendsto_at_bot
- \+/\- *lemma* not_tendsto_nhds_of_tendsto_at_top

Modified src/topology/algebra/ordered/monotone_convergence.lean


Modified src/topology/instances/irrational.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* metric.tendsto_at_top'



## [2022-01-11 13:55:09](https://github.com/leanprover-community/mathlib/commit/be4c5aa)
feat(scripts/lint_mathlib): implement github annotations for mathlib linters ([#11345](https://github.com/leanprover-community/mathlib/pull/11345))
Resolves the last part of [#5863](https://github.com/leanprover-community/mathlib/pull/5863)
This causes `lean --run lint_mathlib --github` to produce error messages understood by github actions, which will tag the lines causing linter failures with annotations in the files changed tab
#### Estimated changes
Modified .github/workflows/build.yml


Modified scripts/lint_mathlib.lean


Modified src/tactic/lint/frontend.lean
- \+ *def* escape_workflow_command



## [2022-01-11 13:55:08](https://github.com/leanprover-community/mathlib/commit/e138d3b)
feat(algebra/big_operators/finprod): `finprod_eq_one_of_forall_eq_one` ([#11335](https://github.com/leanprover-community/mathlib/pull/11335))
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_eq_one_of_forall_eq_one
- \+ *lemma* finprod_mem_eq_one_of_forall_eq_one



## [2022-01-11 13:55:07](https://github.com/leanprover-community/mathlib/commit/eb9c152)
feat(algebra/order/field): lemmas relating `a / b` and `a` when `1 ≤ b` and `1 < b` ([#11333](https://github.com/leanprover-community/mathlib/pull/11333))
This PR is a collection of items that https://github.com/leanprover-community/mathlib/pull/7891 adds in and that aren't declared on `master` yet. Please let me know if I overlooked something.
After merging it, https://github.com/leanprover-community/mathlib/pull/7891 can theoretically be closed.
#### Estimated changes
Modified src/algebra/order/field.lean
- \+ *lemma* div_le_self
- \+/\- *lemma* div_lt_div_of_lt_left
- \+ *lemma* div_lt_self



## [2022-01-11 13:55:05](https://github.com/leanprover-community/mathlib/commit/2865d8c)
refactor(data/set/prod): add notation class for set-like product ([#11300](https://github.com/leanprover-community/mathlib/pull/11300))
This PR adds notation class `has_set_prod` for product of sets and subobjects. I also add an instance for `set`s. Later I want to migrate `finset`s and `sub*` product to this notation class.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/indicator_function.lean


Modified src/algebra/pointwise.lean
- \+/\- *lemma* set.image_mul_prod

Modified src/analysis/ODE/picard_lindelof.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/complex/cauchy_integral.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/combination.lean


Modified src/analysis/convex/star.lean


Modified src/analysis/normed_space/units.lean


Modified src/combinatorics/additive/salem_spencer.lean


Modified src/data/equiv/fin.lean


Modified src/data/equiv/local_equiv.lean


Modified src/data/equiv/set.lean


Modified src/data/finset/prod.lean


Modified src/data/nat/pairing.lean


Modified src/data/set/countable.lean


Modified src/data/set/finite.lean
- \+/\- *lemma* set.finite.prod

Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* set.Ici_prod_Ici
- \+/\- *lemma* set.Ici_prod_eq
- \+/\- *lemma* set.Iic_prod_Iic
- \+/\- *lemma* set.Iic_prod_eq

Modified src/data/set/lattice.lean
- \+/\- *lemma* set.Union_prod
- \+/\- *lemma* set.Union_prod_const
- \+/\- *lemma* set.prod_Union
- \+/\- *lemma* set.prod_eq_seq
- \+/\- *lemma* set.prod_sUnion

Modified src/data/set/prod.lean
- \+/\- *lemma* set.empty_prod
- \+/\- *lemma* set.exists_prod_set
- \+/\- *lemma* set.forall_prod_set
- \+/\- *lemma* set.fst_image_prod
- \+/\- *lemma* set.fst_image_prod_subset
- \+/\- *lemma* set.image_prod
- \+/\- *lemma* set.image_swap_prod
- \+/\- *lemma* set.insert_prod
- \+/\- *lemma* set.mem_prod
- \+/\- *lemma* set.mem_prod_eq
- \+/\- *lemma* set.mk_mem_prod
- \+/\- *lemma* set.mk_preimage_prod_left
- \+/\- *lemma* set.mk_preimage_prod_left_eq_empty
- \+/\- *lemma* set.mk_preimage_prod_right
- \+/\- *lemma* set.mk_preimage_prod_right_eq_empty
- \+/\- *lemma* set.nonempty.fst
- \+/\- *lemma* set.nonempty.prod
- \+/\- *lemma* set.nonempty.snd
- \+/\- *lemma* set.preimage_swap_prod
- \+/\- *lemma* set.prod_diff_prod
- \+/\- *lemma* set.prod_empty
- \+/\- *lemma* set.prod_eq
- \+/\- *lemma* set.prod_eq_empty_iff
- \+/\- *lemma* set.prod_insert
- \+/\- *lemma* set.prod_inter_prod
- \+/\- *lemma* set.prod_mk_mem_set_prod_eq
- \+/\- *lemma* set.prod_mono
- \+/\- *lemma* set.prod_nonempty_iff
- \+/\- *lemma* set.prod_preimage_left
- \+/\- *lemma* set.prod_preimage_right
- \+/\- *lemma* set.prod_singleton
- \+/\- *lemma* set.prod_subset_iff
- \+/\- *lemma* set.prod_subset_preimage_fst
- \+/\- *lemma* set.prod_subset_preimage_snd
- \+/\- *lemma* set.prod_subset_prod_iff
- \+/\- *lemma* set.prod_union
- \+/\- *lemma* set.prod_univ
- \+/\- *lemma* set.singleton_prod
- \+/\- *lemma* set.singleton_prod_singleton
- \+/\- *lemma* set.snd_image_prod
- \+/\- *lemma* set.snd_image_prod_subset
- \+/\- *lemma* set.union_prod
- \+/\- *lemma* set.univ_prod
- \+/\- *lemma* set.univ_prod_univ

Modified src/data/tprod.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/charted_space.lean


Modified src/geometry/manifold/mfderiv.lean


Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/group_theory/submonoid/operations.lean


Modified src/linear_algebra/basic.lean


Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/constructions/prod.lean
- \+/\- *lemma* measure_theory.measure.prod_prod

Modified src/measure_theory/group/prod.lean


Modified src/measure_theory/integral/divergence_theorem.lean


Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/measurable_space.lean
- \+/\- *def* measurable_equiv.set.prod
- \+/\- *lemma* measurable_set_prod_of_nonempty

Modified src/measure_theory/measure/lebesgue.lean
- \+/\- *lemma* region_between_subset

Modified src/order/complete_boolean_algebra.lean
- \+/\- *theorem* Inf_sup_Inf
- \+/\- *theorem* Sup_inf_Sup

Modified src/order/filter/bases.lean
- \+/\- *lemma* filter.mem_prod_self_iff

Modified src/order/filter/basic.lean


Modified src/order/filter/interval.lean


Modified src/order/filter/lift.lean
- \+/\- *lemma* filter.prod_def
- \+/\- *lemma* filter.prod_same_eq

Modified src/order/well_founded_set.lean


Modified src/ring_theory/adjoin/basic.lean


Modified src/ring_theory/subring/basic.lean


Modified src/ring_theory/subsemiring/basic.lean


Modified src/set_theory/cardinal_ordinal.lean


Modified src/topology/algebra/floor_ring.lean


Modified src/topology/algebra/module/basic.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/nonarchimedean/basic.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/bases.lean


Modified src/topology/compact_open.lean
- \+/\- *lemma* continuous_map.image_coev

Modified src/topology/connected.lean


Modified src/topology/constructions.lean
- \+/\- *lemma* is_open_prod_iff

Modified src/topology/continuous_on.lean


Modified src/topology/fiber_bundle.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/lipschitz.lean


Modified src/topology/metric_space/metrizable.lean


Modified src/topology/semicontinuous.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean
- \+/\- *def* sequentially_complete.set_seq_aux

Modified src/topology/uniform_space/compact_separated.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/separation.lean
- \+/\- *lemma* is_separated_def'

Modified src/topology/uniform_space/uniform_convergence.lean


Modified src/topology/uniform_space/uniform_embedding.lean


Modified src/topology/vector_bundle.lean




## [2022-01-11 13:55:04](https://github.com/leanprover-community/mathlib/commit/3cd9088)
feat(ring_theory/polynomial/cyclotomic/basic): add lemmas  ([#11266](https://github.com/leanprover-community/mathlib/pull/11266))
From flt-regular.
#### Estimated changes
Modified src/algebra/ne_zero.lean
- \+ *lemma* ne_zero.not_dvd_char

Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* polynomial.cyclotomic_mul_prime_dvd_eq_pow
- \+ *lemma* polynomial.cyclotomic_mul_prime_eq_pow_of_not_dvd
- \+ *lemma* polynomial.cyclotomic_mul_prime_pow_eq
- \+ *lemma* polynomial.is_root_cyclotomic_iff_char_zero
- \+ *lemma* polynomial.is_root_cyclotomic_prime_pow_mul_iff_of_char_p



## [2022-01-11 13:55:02](https://github.com/leanprover-community/mathlib/commit/4ac13d9)
feat(data/dfinsupp/interval): Finitely supported dependent functions to locally finite orders are locally finite ([#11175](https://github.com/leanprover-community/mathlib/pull/11175))
This provides the ` locally_finite_order` instance for `Π₀ i, α i` in a new file `data.dfinsupp.interval`.
#### Estimated changes
Modified src/data/dfinsupp/basic.lean
- \+/\- *lemma* dfinsupp.mem_support_iff
- \+/\- *lemma* dfinsupp.mk_apply
- \+ *lemma* dfinsupp.mk_of_mem
- \+ *lemma* dfinsupp.mk_of_not_mem
- \+ *lemma* dfinsupp.not_mem_support_iff

Added src/data/dfinsupp/interval.lean
- \+ *lemma* dfinsupp.card_Icc
- \+ *lemma* dfinsupp.card_Ico
- \+ *lemma* dfinsupp.card_Ioc
- \+ *lemma* dfinsupp.card_Ioo
- \+ *lemma* dfinsupp.card_pi
- \+ *lemma* dfinsupp.mem_pi
- \+ *lemma* dfinsupp.mem_range_Icc_apply_iff
- \+ *lemma* dfinsupp.mem_singleton_apply_iff
- \+ *def* dfinsupp.pi
- \+ *def* dfinsupp.range_Icc
- \+ *lemma* dfinsupp.range_Icc_apply
- \+ *def* dfinsupp.singleton
- \+ *lemma* dfinsupp.support_range_Icc_subset
- \+ *lemma* finset.card_dfinsupp
- \+ *def* finset.dfinsupp
- \+ *lemma* finset.mem_dfinsupp_iff
- \+ *lemma* finset.mem_dfinsupp_iff_of_support_subset

Modified src/data/dfinsupp/order.lean
- \+/\- *lemma* dfinsupp.le_iff'
- \+/\- *lemma* dfinsupp.le_iff
- \- *lemma* dfinsupp.not_mem_support_iff
- \+/\- *lemma* dfinsupp.single_le_iff

Modified src/data/finset/basic.lean
- \+ *lemma* finset.not_mem_mono

Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.cons_le_cons
- \- *theorem* multiset.cons_le_cons
- \+ *lemma* multiset.cons_le_cons_iff
- \- *theorem* multiset.cons_le_cons_iff
- \+ *lemma* multiset.le_cons_of_not_mem
- \- *theorem* multiset.le_cons_of_not_mem
- \+ *lemma* multiset.le_zero
- \- *theorem* multiset.le_zero
- \+ *lemma* multiset.mem_of_le
- \- *theorem* multiset.mem_of_le
- \+ *lemma* multiset.not_mem_mono
- \+ *lemma* multiset.subset_of_le
- \- *theorem* multiset.subset_of_le



## [2022-01-11 11:13:20](https://github.com/leanprover-community/mathlib/commit/40b6b45)
feat(category_theory): `Cat` is a strict bicategory ([#11348](https://github.com/leanprover-community/mathlib/pull/11348))
This PR defines a bicategory structure on `Cat`. This also introduces the propositional type class `bicategory.strict`, and proves that `Cat` is an instance of this class.
#### Estimated changes
Added src/category_theory/bicategory/strict.lean


Modified src/category_theory/category/Cat.lean




## [2022-01-11 11:13:19](https://github.com/leanprover-community/mathlib/commit/a4052f9)
feat(ring_theory/hahn_series): order_pow ([#11334](https://github.com/leanprover-community/mathlib/pull/11334))
Generalize to have `no_zero_divisors (hahn_series Γ R)`,
which generalizes `order_mul`.
Also provide `coeff_eq_zero_of_lt_order`.
#### Estimated changes
Modified src/ring_theory/hahn_series.lean
- \+ *lemma* hahn_series.coeff_eq_zero_of_lt_order
- \+/\- *lemma* hahn_series.order_mul
- \+ *lemma* hahn_series.order_pow



## [2022-01-11 11:13:18](https://github.com/leanprover-community/mathlib/commit/90ba054)
feat(algebraic_geometry): Define the category of `AffineScheme`s ([#11326](https://github.com/leanprover-community/mathlib/pull/11326))
#### Estimated changes
Added src/algebraic_geometry/AffineScheme.lean
- \+ *def* algebraic_geometry.AffineScheme.Spec
- \+ *def* algebraic_geometry.AffineScheme.equiv_CommRing
- \+ *def* algebraic_geometry.AffineScheme.forget_to_Scheme
- \+ *def* algebraic_geometry.AffineScheme.Γ
- \+ *def* algebraic_geometry.AffineScheme
- \+ *def* algebraic_geometry.Scheme.iso_Spec
- \+ *lemma* algebraic_geometry.is_affine_of_iso
- \+ *def* algebraic_geometry.is_affine_open
- \+ *lemma* algebraic_geometry.is_basis_affine_open
- \+ *lemma* algebraic_geometry.mem_AffineScheme
- \+ *lemma* algebraic_geometry.range_is_affine_open_of_open_immersion
- \+ *lemma* algebraic_geometry.top_is_affine_open

Modified src/algebraic_geometry/Gamma_Spec_adjunction.lean


Modified src/algebraic_geometry/open_immersion.lean
- \+ *def* algebraic_geometry.Scheme.of_restrict
- \+ *def* algebraic_geometry.Scheme.restrict
- \+ *def* algebraic_geometry.is_open_immersion.iso_of_range_eq
- \+ *def* algebraic_geometry.is_open_immersion.iso_restrict
- \+ *def* algebraic_geometry.is_open_immersion.lift
- \+ *lemma* algebraic_geometry.is_open_immersion.lift_fac
- \+ *lemma* algebraic_geometry.is_open_immersion.lift_uniq

Modified src/category_theory/adjunction/reflective.lean
- \+ *def* category_theory.equiv_ess_image_of_reflective



## [2022-01-11 11:13:17](https://github.com/leanprover-community/mathlib/commit/c03bd32)
feat(analysis/normed_space/star): add lemmas about continuity and norm of identity ([#11324](https://github.com/leanprover-community/mathlib/pull/11324))
#### Estimated changes
Modified src/analysis/normed_space/star.lean
- \+ *lemma* continuous.star
- \+ *lemma* continuous_at.star
- \+ *lemma* continuous_at_star
- \+ *lemma* continuous_on.star
- \+ *lemma* continuous_on_star
- \+ *lemma* continuous_star
- \+ *lemma* continuous_within_at.star
- \+ *lemma* continuous_within_at_star
- \+ *lemma* cstar_ring.norm_one
- \+/\- *lemma* cstar_ring.norm_self_mul_star
- \+/\- *lemma* cstar_ring.norm_star_mul_self'
- \+ *lemma* filter.tendsto.star
- \+/\- *lemma* star_isometry
- \+/\- *def* star_normed_group_hom
- \+ *lemma* tendsto_star



## [2022-01-11 11:13:16](https://github.com/leanprover-community/mathlib/commit/ebbc973)
feat(data/mv_polynomial): assorted mv_polynomial and finsupp lemmas ([#11319](https://github.com/leanprover-community/mathlib/pull/11319))
Mostly around total degree, supports and homogeneous components.
From flt-regular.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.support_smul_eq

Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.monomial_eq_zero
- \+/\- *lemma* mv_polynomial.monomial_zero

Modified src/data/mv_polynomial/variables.lean
- \+ *lemma* mv_polynomial.total_degree_X_pow
- \+ *lemma* mv_polynomial.total_degree_monomial

Modified src/ring_theory/polynomial/homogeneous.lean
- \+ *lemma* mv_polynomial.homogeneous_component_C_mul
- \+ *lemma* mv_polynomial.is_homogeneous_of_total_degree_zero



## [2022-01-11 11:13:15](https://github.com/leanprover-community/mathlib/commit/c500b99)
feat(ring_theory/laurent): coe from R[[x]] to R((x)) ([#11318](https://github.com/leanprover-community/mathlib/pull/11318))
And actually the changes reported in [#11295](https://github.com/leanprover-community/mathlib/pull/11295)
Generalize `power_series.coeff_smul`
#### Estimated changes
Modified src/ring_theory/hahn_series.lean
- \+ *lemma* hahn_series.of_power_series_C
- \+ *lemma* hahn_series.of_power_series_X
- \+ *lemma* hahn_series.of_power_series_X_pow

Modified src/ring_theory/laurent_series.lean
- \- *lemma* laurent_series.of_power_series_C
- \- *lemma* laurent_series.of_power_series_X
- \- *lemma* laurent_series.of_power_series_X_pow
- \- *lemma* polynomial.coe_coe
- \- *lemma* polynomial.coe_laurent
- \- *lemma* polynomial.coe_laurent_C
- \- *lemma* polynomial.coe_laurent_X
- \- *lemma* polynomial.coe_laurent_add
- \- *lemma* polynomial.coe_laurent_mul
- \- *lemma* polynomial.coe_laurent_one
- \- *lemma* polynomial.coe_laurent_smul
- \- *lemma* polynomial.coe_laurent_zero
- \- *lemma* polynomial.coeff_coe_laurent
- \- *lemma* polynomial.coeff_coe_laurent_coe
- \+ *lemma* power_series.coe_C
- \+ *lemma* power_series.coe_X
- \+ *lemma* power_series.coe_add
- \+ *lemma* power_series.coe_bit0
- \+ *lemma* power_series.coe_bit1
- \+ *lemma* power_series.coe_mul
- \+ *lemma* power_series.coe_one
- \+ *lemma* power_series.coe_pow
- \+ *lemma* power_series.coe_smul
- \+ *lemma* power_series.coe_zero
- \+ *lemma* power_series.coeff_coe

Modified src/ring_theory/power_series/basic.lean
- \+/\- *lemma* power_series.coeff_smul



## [2022-01-11 11:13:14](https://github.com/leanprover-community/mathlib/commit/be594eb)
feat(linear_algebra/finite_dimensional): Define rank of set of vectors ([#11290](https://github.com/leanprover-community/mathlib/pull/11290))
Added in the definition of "rank of a set of vectors" and a useful lemma about the rank when one set is a subset of the other.
Read the zulip stream here: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/First.20Time.20Contributing
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* set.finrank_mono



## [2022-01-11 11:13:13](https://github.com/leanprover-community/mathlib/commit/b7f8f72)
feat(category_theory/bicategory/functor): define oplax functors and their composition ([#11277](https://github.com/leanprover-community/mathlib/pull/11277))
This PR defines oplax functors between bicategories and their composition.
#### Estimated changes
Added src/category_theory/bicategory/functor.lean
- \+ *def* category_theory.oplax_functor.comp
- \+ *def* category_theory.oplax_functor.id
- \+ *def* category_theory.oplax_functor.map_functor
- \+ *def* category_theory.oplax_functor.map₂_associator_aux
- \+ *lemma* category_theory.oplax_functor.to_prelax_functor_map
- \+ *lemma* category_theory.oplax_functor.to_prelax_functor_map₂
- \+ *lemma* category_theory.oplax_functor.to_prelax_functor_obj
- \+ *structure* category_theory.oplax_functor
- \+ *def* category_theory.prelax_functor.comp
- \+ *def* category_theory.prelax_functor.id
- \+ *lemma* category_theory.prelax_functor.to_prefunctor_map
- \+ *lemma* category_theory.prelax_functor.to_prefunctor_obj
- \+ *structure* category_theory.prelax_functor



## [2022-01-11 11:13:11](https://github.com/leanprover-community/mathlib/commit/624cb70)
feat(set_theory/ordinal_arithmetic): Extra lemmas about suprema ([#11178](https://github.com/leanprover-community/mathlib/pull/11178))
Proved lemmas pertaining to when suprema or least strict upper bounds are zero.
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+ *lemma* ordinal.eq_zero_of_out_empty
- \+ *theorem* ordinal.out_empty_iff_eq_zero

Modified src/set_theory/ordinal_arithmetic.lean
- \+ *lemma* ordinal.blsub_eq_zero
- \+ *theorem* ordinal.blsub_eq_zero_iff
- \+ *lemma* ordinal.blsub_pos
- \+ *theorem* ordinal.bsup_eq_zero_iff
- \+ *lemma* ordinal.lsub_eq_zero
- \+ *theorem* ordinal.lsub_eq_zero_iff
- \+ *lemma* ordinal.lsub_pos
- \+ *theorem* ordinal.sup_eq_zero_iff



## [2022-01-11 08:13:33](https://github.com/leanprover-community/mathlib/commit/de9944b)
refactor(analysis/complex/circle): The circle group is commutative ([#11368](https://github.com/leanprover-community/mathlib/pull/11368))
This PR upgrades the `group circle` instance to a `comm_group circle` instance.
#### Estimated changes
Modified src/analysis/complex/circle.lean




## [2022-01-11 08:13:31](https://github.com/leanprover-community/mathlib/commit/e8839a3)
refactor(logic/small, *): Infer `f : α → β` when followed by a simple condition on `f` ([#11037](https://github.com/leanprover-community/mathlib/pull/11037))
#### Estimated changes
Modified src/data/equiv/encodable/small.lean


Modified src/data/equiv/set.lean
- \+/\- *theorem* equiv.apply_of_injective_symm
- \+/\- *lemma* equiv.coe_of_injective_symm
- \+/\- *theorem* equiv.of_injective_symm_apply
- \+/\- *lemma* equiv.self_comp_of_injective_symm

Modified src/data/fin/basic.lean


Modified src/group_theory/perm/sign.lean


Modified src/linear_algebra/basis.lean


Modified src/logic/small.lean
- \+/\- *theorem* small_of_injective
- \+/\- *theorem* small_of_surjective



## [2022-01-11 02:45:39](https://github.com/leanprover-community/mathlib/commit/89bff5e)
feat(algebra/big_operators): add product versions of some sum lemmas ([#11358](https://github.com/leanprover-community/mathlib/pull/11358))
and to_additive to get the old ones back
#### Estimated changes
Modified src/algebra/big_operators/multiset.lean
- \+ *lemma* multiset.le_prod_of_mem
- \- *lemma* multiset.le_sum_of_mem
- \+ *lemma* multiset.prod_eq_one_iff
- \- *lemma* multiset.sum_eq_zero_iff

Modified src/data/list/big_operators.lean
- \+ *lemma* list.prod_eq_one_iff
- \- *lemma* list.sum_eq_zero_iff



## [2022-01-11 02:45:38](https://github.com/leanprover-community/mathlib/commit/d8a75bd)
chore(simple_graph/basic): Fix typo in docstring: adjacent vertices, not edges ([#11356](https://github.com/leanprover-community/mathlib/pull/11356))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean




## [2022-01-10 23:30:59](https://github.com/leanprover-community/mathlib/commit/8910f6d)
feat(ring_theory/discriminant): remove an assumption ([#11359](https://github.com/leanprover-community/mathlib/pull/11359))
We remove a `nonempty` assumption.
#### Estimated changes
Modified src/ring_theory/discriminant.lean
- \+/\- *lemma* algebra.discr_not_zero_of_linear_independent



## [2022-01-10 23:30:58](https://github.com/leanprover-community/mathlib/commit/fd51bda)
feat(analysis/normed_space/linear_isometry): basis ext lemmas ([#11331](https://github.com/leanprover-community/mathlib/pull/11331))
Add lemmas that two linear isometries / linear isometric equivalences
are equal if they are equal on basis vectors, similar to such lemmas
for equality on basis vectors of other kinds of maps.
#### Estimated changes
Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* basis.ext_linear_isometry
- \+ *lemma* basis.ext_linear_isometry_equiv



## [2022-01-10 23:30:57](https://github.com/leanprover-community/mathlib/commit/3b55b94)
feat(analysis/inner_product_space/basic): inner products of linear combinations of orthonormal vectors ([#11323](https://github.com/leanprover-community/mathlib/pull/11323))
There are some lemmas about the inner product of a linear combination
of orthonormal vectors with one vector from that orthonormal family.
Add similar lemmas where both sides of the inner product are linear
combinations.
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* orthonormal.inner_finsupp_eq_sum_left
- \+ *lemma* orthonormal.inner_finsupp_eq_sum_right
- \+ *lemma* orthonormal.inner_left_sum
- \+ *lemma* orthonormal.inner_right_sum
- \+ *lemma* orthonormal.inner_sum



## [2022-01-10 23:30:55](https://github.com/leanprover-community/mathlib/commit/fd52481)
feat(group_theory/abelianization): Add fintype instance ([#11302](https://github.com/leanprover-community/mathlib/pull/11302))
Adds `fintype` instance for `abelianization`.
#### Estimated changes
Modified src/group_theory/abelianization.lean




## [2022-01-10 23:30:54](https://github.com/leanprover-community/mathlib/commit/2642c89)
feat(analysis/inner_product_space/orientation): orientations of real inner product spaces ([#11269](https://github.com/leanprover-community/mathlib/pull/11269))
Add definitions and lemmas relating to orientations of real inner
product spaces, in particular constructing an orthonormal basis with a
given orientation in finite positive dimension.
This is in a new file since nothing else about inner product spaces
needs to depend on orientations.
#### Estimated changes
Added src/analysis/inner_product_space/orientation.lean
- \+ *lemma* orientation.fin_orthonormal_basis_orientation
- \+ *lemma* orthonormal.orthonormal_adjust_to_orientation



## [2022-01-10 23:30:52](https://github.com/leanprover-community/mathlib/commit/4e7e5a6)
feat(set_theory/ordinal_arithmetic): Enumerating unbounded sets of ordinals with ordinals ([#10979](https://github.com/leanprover-community/mathlib/pull/10979))
This PR introduces `enum_ord`, which enumerates an unbounded set of ordinals using ordinals. This is used to build an explicit order isomorphism `enum_ord.order_iso`.
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+ *theorem* ordinal.not_lt_omin

Modified src/set_theory/ordinal_arithmetic.lean
- \+ *def* ordinal.CNF
- \+ *theorem* ordinal.blsub_le_enum_ord
- \+ *def* ordinal.enum_ord.order_iso
- \+ *theorem* ordinal.enum_ord.strict_mono
- \+ *theorem* ordinal.enum_ord.surjective
- \+ *def* ordinal.enum_ord
- \+ *theorem* ordinal.enum_ord_def'
- \+ *lemma* ordinal.enum_ord_def'_H
- \+ *theorem* ordinal.enum_ord_def
- \+ *lemma* ordinal.enum_ord_def_H
- \+ *theorem* ordinal.enum_ord_mem
- \+ *theorem* ordinal.enum_ord_range
- \+ *theorem* ordinal.eq_enum_ord



## [2022-01-10 23:30:51](https://github.com/leanprover-community/mathlib/commit/8e92af1)
feat(algebra/associated): add lemmas to split [#9345](https://github.com/leanprover-community/mathlib/pull/9345) ([#10941](https://github.com/leanprover-community/mathlib/pull/10941))
This PR contains lemmas from PR [[#9345](https://github.com/leanprover-community/mathlib/pull/9345)](https://github.com/leanprover-community/mathlib/pull/9345), which was starting to get quite lengthy.
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* associates.bot_eq_one
- \+ *lemma* associates.le_one_iff
- \+ *lemma* associates.mk_injective
- \+ *lemma* dvd_not_unit.is_unit_of_irreducible_right
- \+ *lemma* dvd_not_unit.ne
- \+ *lemma* dvd_not_unit.not_associated
- \+ *lemma* dvd_not_unit.not_unit
- \+ *lemma* dvd_not_unit_of_dvd_not_unit_associated
- \+ *lemma* is_unit_of_associated_mul
- \+ *lemma* not_irreducible_of_not_unit_dvd_not_unit
- \+ *lemma* not_is_unit_of_not_is_unit_dvd
- \+ *lemma* pow_injective_of_not_unit

Modified src/algebra/divisibility.lean
- \+ *theorem* ne_zero_of_dvd_ne_zero



## [2022-01-10 23:30:50](https://github.com/leanprover-community/mathlib/commit/4bf4859)
feat(data/finsupp/pointwise): add a definition of the pointwise action of functions on finsupps ([#10933](https://github.com/leanprover-community/mathlib/pull/10933))
I couldn't find this, and it seems like quite a natural way to talk about multiplying functions with finsupps.
I'm not sure what additional lemmas would be useful yet, as I don't have a particular application in mind at present so suggestions/additions are welcome
#### Estimated changes
Modified src/data/finsupp/pointwise.lean
- \+ *lemma* finsupp.coe_pointwise_module



## [2022-01-10 19:54:28](https://github.com/leanprover-community/mathlib/commit/2e003c9)
feat(data/set/basic): add decidable instances for boolean operations ([#11354](https://github.com/leanprover-community/mathlib/pull/11354))
Add decidability instances for `a ∈ s ∩ t`, etc.
#### Estimated changes
Modified src/data/set/basic.lean




## [2022-01-10 19:54:26](https://github.com/leanprover-community/mathlib/commit/427e5b5)
feat(data/nat/factorization): Evaluating a multiplicative function over prime power divisors ([#11167](https://github.com/leanprover-community/mathlib/pull/11167))
For any multiplicative function `f` with `f 1 = 1` and any `n > 0`, we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n`.
Also provides an alternative version that swaps the `0 < n` condition for an extra `f 0 = 1` condition, as suggested by @ericrbg. 
This allows a very simple proof that `n.factorization.prod pow = n`
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+ *lemma* nat.factorization_prod_pow_eq_self
- \+ *lemma* nat.multiplicative_factorization'
- \+ *lemma* nat.multiplicative_factorization

Modified src/number_theory/arithmetic_function.lean
- \+ *lemma* nat.arithmetic_function.is_multiplicative.multiplicative_factorization



## [2022-01-10 16:17:20](https://github.com/leanprover-community/mathlib/commit/dc3cbb7)
feat(data/polynomial/erase_lead): introduce two lemmas to compute `nat_degree`s under certain maps ([#11265](https://github.com/leanprover-community/mathlib/pull/11265))
This PR is a step in the direction of simplifying [#11139](https://github.com/leanprover-community/mathlib/pull/11139).
It contains a proof of the helper lemmas `map_nat_degree_eq_sub` and `map_nat_degree_eq_nat_degree` to shorten the proof of `nat_degree_hasse_deriv` and `nat_degree_taylor`.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2311139.20taylor.20sum.20and.20nat_degree_taylor)
#### Estimated changes
Modified src/data/polynomial/erase_lead.lean
- \+ *lemma* polynomial.map_nat_degree_eq_nat_degree
- \+ *lemma* polynomial.map_nat_degree_eq_sub
- \+ *lemma* polynomial.mono_map_nat_degree_eq



## [2022-01-10 16:17:19](https://github.com/leanprover-community/mathlib/commit/168ad7f)
feat(data/nat/cast): generalize to `fun_like` ([#11128](https://github.com/leanprover-community/mathlib/pull/11128))
#### Estimated changes
Modified archive/100-theorems-list/16_abel_ruffini.lean


Modified src/algebra/algebra/basic.lean
- \- *lemma* alg_hom.map_nat_cast

Modified src/algebra/char_p/basic.lean
- \+/\- *theorem* frobenius_nat_cast

Modified src/algebra/char_p/pi.lean


Modified src/algebra/char_p/quotient.lean


Modified src/algebra/char_p/subring.lean


Modified src/algebra/char_zero.lean


Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/ne_zero.lean
- \+ *lemma* ne_zero.nat_of_injective
- \- *lemma* ne_zero.of_injective'
- \+/\- *lemma* ne_zero.of_injective

Modified src/data/complex/basic.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/data/int/cast.lean


Modified src/data/matrix/char_p.lean


Modified src/data/nat/cast.lean
- \- *lemma* add_monoid_hom.eq_nat_cast
- \+/\- *lemma* add_monoid_hom.ext_nat
- \- *lemma* add_monoid_hom.map_nat_cast
- \+ *lemma* eq_nat_cast'
- \+ *lemma* eq_nat_cast
- \+ *theorem* ext_nat''
- \+ *lemma* ext_nat'
- \+ *lemma* ext_nat
- \+ *lemma* map_nat_cast'
- \+ *lemma* map_nat_cast
- \+/\- *theorem* monoid_with_zero_hom.ext_nat
- \+/\- *theorem* nat.cast_one
- \+/\- *lemma* nat.cast_two
- \+/\- *lemma* nat.coe_nat_dvd
- \+/\- *lemma* nat.commute_cast
- \- *lemma* ring_hom.eq_nat_cast
- \- *lemma* ring_hom.ext_nat
- \- *lemma* ring_hom.map_nat_cast
- \+/\- *lemma* with_top.coe_nat

Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/basic.lean


Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/eval.lean
- \- *theorem* polynomial.map_nat_cast

Modified src/data/real/nnreal.lean


Modified src/data/zmod/basic.lean


Modified src/number_theory/basic.lean


Modified src/number_theory/class_number/finite.lean


Modified src/number_theory/cyclotomic/basic.lean


Modified src/number_theory/padics/ring_homs.lean


Modified src/ring_theory/perfection.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/cyclotomic/basic.lean


Modified src/ring_theory/polynomial/dickson.lean


Modified src/ring_theory/polynomial/pochhammer.lean


Modified src/ring_theory/subring/basic.lean
- \+/\- *lemma* subring.coe_nat_cast

Modified src/ring_theory/witt_vector/compare.lean


Modified src/ring_theory/witt_vector/is_poly.lean


Modified src/ring_theory/witt_vector/verschiebung.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean




## [2022-01-10 13:08:00](https://github.com/leanprover-community/mathlib/commit/1533f15)
feat(logic/basic): add eq_true_eq_id ([#11341](https://github.com/leanprover-community/mathlib/pull/11341))
Adds the simp lemma `eq_true_eq_id : eq true = id`, a sort of curried version of `eq_true : (a = true) = a` in core.
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* eq_true_eq_id



## [2022-01-10 13:07:59](https://github.com/leanprover-community/mathlib/commit/fabc510)
feat(linear_algebra/determinant): `linear_equiv.det_conj` ([#11340](https://github.com/leanprover-community/mathlib/pull/11340))
Add a version of the `linear_map.det_conj` lemma for `linear_equiv.det`.
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* linear_equiv.det_conj



## [2022-01-10 13:07:57](https://github.com/leanprover-community/mathlib/commit/48b21e5)
feat(probability_theory/martingale): one direction of the optional stopping theorem ([#11007](https://github.com/leanprover-community/mathlib/pull/11007))
#### Estimated changes
Modified src/probability_theory/martingale.lean
- \+ *lemma* measure_theory.submartingale.expected_stopped_value_mono
- \+ *lemma* measure_theory.submartingale.integrable_stopped_value

Modified src/probability_theory/stopping.lean
- \+ *lemma* measure_theory.integrable_stopped_value
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_lt
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_lt_le
- \+ *lemma* measure_theory.mem_ℒp_stopped_value
- \+ *lemma* measure_theory.stopped_value_eq
- \+ *lemma* measure_theory.stopped_value_sub_eq_sum'
- \+ *lemma* measure_theory.stopped_value_sub_eq_sum



## [2022-01-10 10:18:16](https://github.com/leanprover-community/mathlib/commit/7782157)
feat (data/finset/lattice): add more finset induction lemmas ([#10889](https://github.com/leanprover-community/mathlib/pull/10889))
2 more finset induction lemmas based on the order imposed by a function.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.induction_on_max_value
- \+ *lemma* finset.induction_on_min_value



## [2022-01-10 01:23:46](https://github.com/leanprover-community/mathlib/commit/99fe7ac)
chore(data/set/function): move inv_fun_on out of `logic/function/basic` ([#11330](https://github.com/leanprover-community/mathlib/pull/11330))
This removes `function.inv_fun_on_eq'` as it is a duplicate of `inj_on.left_inv_on_inv_fun_on`.
#### Estimated changes
Modified src/data/set/function.lean
- \+ *theorem* function.inv_fun_on_eq
- \+ *theorem* function.inv_fun_on_mem
- \+ *theorem* function.inv_fun_on_neg
- \+ *theorem* function.inv_fun_on_pos

Modified src/logic/function/basic.lean
- \- *theorem* function.inv_fun_on_eq'
- \- *theorem* function.inv_fun_on_eq
- \- *theorem* function.inv_fun_on_mem
- \- *theorem* function.inv_fun_on_neg
- \- *theorem* function.inv_fun_on_pos

Modified src/measure_theory/covering/vitali.lean




## [2022-01-09 23:15:30](https://github.com/leanprover-community/mathlib/commit/6a10939)
fix(docs/references.bib): syntax error ([#11342](https://github.com/leanprover-community/mathlib/pull/11342))
This broke the docs build.
#### Estimated changes
Modified docs/references.bib




## [2022-01-09 21:08:06](https://github.com/leanprover-community/mathlib/commit/ce17b65)
feat(topology/algebra/monoid): to_additivize some lemmas ([#11310](https://github.com/leanprover-community/mathlib/pull/11310))
Uncomment a commented out to additive line that looks like its been there
for 3 years (since
https://github.com/leanprover-community/mathlib/commit/581cf19bf1885ef874c39c9902a93f579bc8c22d)
The changes to to_additive in the past few years now make the
generated lemma useful.
Also to_additivize a bunch of other lemmas in this file.
#### Estimated changes
Modified src/topology/algebra/monoid.lean




## [2022-01-09 18:06:11](https://github.com/leanprover-community/mathlib/commit/d13b3a4)
chore(*): update to 3.37.0c ([#11325](https://github.com/leanprover-community/mathlib/pull/11325))
the major breaking change this version is making `default`'s parameters
implicit, as opposed to explicit. there was also some slight "free"
golfing due to the better `out_param` simp support.
#### Estimated changes
Modified counterexamples/phillips.lean


Modified leanpkg.toml


Modified src/algebra/add_torsor.lean


Modified src/algebra/big_operators/basic.lean


Modified src/algebra/big_operators/finprod.lean
- \+/\- *lemma* finprod_unique

Modified src/algebra/continued_fractions/basic.lean


Modified src/algebra/continued_fractions/computation/basic.lean


Modified src/algebra/direct_sum/basic.lean


Modified src/algebra/free.lean


Modified src/algebra/graded_monoid.lean


Modified src/algebra/group/type_tags.lean


Modified src/algebra/group/units.lean


Modified src/algebra/lie/cartan_matrix.lean


Modified src/algebra/linear_recurrence.lean


Modified src/algebra/module/linear_map.lean
- \+/\- *lemma* linear_map.default_def

Modified src/algebra/opposites.lean


Modified src/algebra/tropical/basic.lean


Modified src/algebraic_geometry/presheafed_space.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/normed_space/affine_isometry.lean


Modified src/analysis/normed_space/lp_space.lean


Modified src/analysis/normed_space/pi_Lp.lean


Modified src/category_theory/action.lean


Modified src/category_theory/arrow.lean


Modified src/category_theory/category/Kleisli.lean


Modified src/category_theory/category/pairwise.lean


Modified src/category_theory/closed/cartesian.lean


Modified src/category_theory/closed/zero.lean


Modified src/category_theory/comma.lean


Modified src/category_theory/connected_components.lean


Modified src/category_theory/graded_object.lean


Modified src/category_theory/lifting_properties.lean


Modified src/category_theory/limits/shapes/multiequalizer.lean


Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/limits/types.lean


Modified src/category_theory/monad/algebra.lean


Modified src/category_theory/monad/kleisli.lean


Modified src/category_theory/over.lean


Modified src/category_theory/path_category.lean


Modified src/category_theory/preadditive/Mat.lean


Modified src/category_theory/quotient.lean


Modified src/category_theory/sites/sheaf.lean


Modified src/category_theory/sites/sheaf_of_types.lean


Modified src/category_theory/skeletal.lean


Modified src/combinatorics/hales_jewett.lean


Modified src/combinatorics/quiver/connected_component.lean


Modified src/combinatorics/quiver/subquiver.lean


Modified src/combinatorics/simple_graph/degree_sum.lean


Modified src/computability/DFA.lean


Modified src/computability/primrec.lean


Modified src/computability/reduce.lean


Modified src/computability/tm_computable.lean


Modified src/computability/turing_machine.lean


Modified src/control/functor.lean


Modified src/data/array/lemmas.lean


Modified src/data/bool/basic.lean
- \+/\- *theorem* bool.default_bool

Modified src/data/bundle.lean


Modified src/data/equiv/basic.lean


Modified src/data/equiv/embedding.lean


Modified src/data/equiv/encodable/basic.lean


Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.unique_ext
- \+/\- *lemma* finsupp.unique_ext_iff
- \+/\- *lemma* finsupp.unique_single

Modified src/data/fintype/basic.lean
- \+/\- *lemma* finset.univ_unique

Modified src/data/holor.lean


Modified src/data/int/basic.lean
- \+/\- *lemma* int.default_eq_zero

Modified src/data/lazy_list.lean


Modified src/data/list/basic.lean
- \+/\- *theorem* list.take'_nil

Modified src/data/list/big_operators.lean


Modified src/data/list/defs.lean


Modified src/data/list/func.lean
- \+/\- *lemma* list.func.get_nil
- \+/\- *lemma* list.func.get_pointwise
- \+/\- *lemma* list.func.nil_pointwise

Modified src/data/matrix/basis.lean


Modified src/data/opposite.lean


Modified src/data/option/defs.lean


Modified src/data/pfunctor/multivariate/M.lean


Modified src/data/pfunctor/multivariate/basic.lean


Modified src/data/pfunctor/univariate/M.lean


Modified src/data/pfunctor/univariate/basic.lean


Modified src/data/qpf/multivariate/constructions/cofix.lean


Modified src/data/qpf/multivariate/constructions/const.lean


Modified src/data/qpf/multivariate/constructions/prj.lean


Modified src/data/qpf/multivariate/constructions/quot.lean


Modified src/data/qpf/multivariate/constructions/sigma.lean


Modified src/data/qpf/univariate/basic.lean


Modified src/data/quot.lean


Modified src/data/rbmap/basic.lean


Modified src/data/semiquot.lean


Modified src/data/seq/seq.lean


Modified src/data/set/basic.lean
- \+/\- *lemma* set.default_coe_singleton
- \+/\- *lemma* set.range_unique
- \+/\- *lemma* set.univ_unique

Modified src/data/set/lattice.lean


Modified src/data/setoid/partition.lean


Modified src/data/sigma/basic.lean


Modified src/data/stream/init.lean


Modified src/data/string/basic.lean
- \+/\- *lemma* string.head_empty

Modified src/data/sym/basic.lean


Modified src/data/tprod.lean


Modified src/data/typevec.lean


Modified src/data/vector/basic.lean


Modified src/geometry/euclidean/circumcenter.lean


Modified src/geometry/manifold/partition_of_unity.lean


Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/geometry/manifold/times_cont_mdiff_map.lean


Modified src/group_theory/free_abelian_group.lean


Modified src/group_theory/nielsen_schreier.lean
- \+/\- *def* is_free_groupoid.spanning_tree.tree_hom

Modified src/group_theory/perm/basic.lean
- \+/\- *lemma* equiv.perm.default_perm

Modified src/linear_algebra/affine_space/affine_map.lean


Modified src/linear_algebra/affine_space/independent.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/linear_algebra/matrix/block.lean


Modified src/linear_algebra/matrix/determinant.lean


Modified src/linear_algebra/std_basis.lean


Modified src/logic/basic.lean


Modified src/logic/embedding.lean


Modified src/logic/nontrivial.lean


Modified src/logic/unique.lean
- \+/\- *lemma* fin.default_eq_zero
- \+/\- *lemma* unique.default_eq
- \+/\- *lemma* unique.eq_default
- \+/\- *lemma* unique.exists_iff
- \+/\- *lemma* unique.forall_iff

Modified src/measure_theory/covering/besicovitch.lean


Modified src/measure_theory/function/ae_eq_fun.lean


Modified src/measure_theory/function/strongly_measurable.lean


Modified src/measure_theory/integral/integrable_on.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/measure/finite_measure_weak_convergence.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/probability_mass_function/basic.lean


Modified src/meta/expr.lean


Modified src/order/basic.lean


Modified src/order/conditionally_complete_lattice.lean
- \+/\- *theorem* infi_unique
- \+/\- *theorem* supr_unique

Modified src/order/countable_dense_linear_order.lean


Modified src/order/extension.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/germ.lean


Modified src/order/filter/ultrafilter.lean


Modified src/order/ideal.lean


Modified src/order/jordan_holder.lean


Modified src/order/omega_complete_partial_order.lean


Modified src/order/pfilter.lean


Modified src/order/rel_iso.lean
- \+/\- *lemma* rel_iso.default_def

Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/witt_vector/truncated.lean


Modified src/set_theory/lists.lean


Modified src/set_theory/zfc.lean


Modified src/tactic/cache.lean


Modified src/tactic/cancel_denoms.lean


Modified src/tactic/core.lean


Modified src/tactic/derive_inhabited.lean


Modified src/tactic/explode.lean


Modified src/tactic/explode_widget.lean


Modified src/tactic/fix_reflect_string.lean


Modified src/tactic/interactive.lean


Modified src/tactic/rcases.lean


Modified src/tactic/split_ifs.lean


Modified src/testing/slim_check/functions.lean


Modified src/testing/slim_check/sampleable.lean


Modified src/testing/slim_check/testable.lean


Modified src/topology/algebra/filter_basis.lean


Modified src/topology/algebra/module/basic.lean
- \+/\- *lemma* continuous_linear_equiv.coe_fun_unique
- \+/\- *lemma* continuous_linear_map.default_def

Modified src/topology/algebra/nonarchimedean/bases.lean


Modified src/topology/algebra/ordered/compact.lean


Modified src/topology/compact_open.lean


Modified src/topology/compacts.lean


Modified src/topology/connected.lean


Modified src/topology/continuous_function/basic.lean


Modified src/topology/continuous_function/bounded.lean


Modified src/topology/locally_constant/basic.lean


Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/partition_of_unity.lean


Modified src/topology/path_connected.lean


Modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean


Modified src/topology/tietze_extension.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/completion.lean


Modified test/inhabit.lean


Modified test/instance_cache.lean


Modified test/lint_coe_t.lean
- \+/\- *def* int_to_a

Modified test/lint_simp_nf.lean
- \+/\- *def* c
- \+/\- *def* d
- \+/\- *def* f
- \+/\- *def* h

Modified test/pi_simp.lean
- \+/\- *def* test.eval_default

Modified test/qpf.lean




## [2022-01-09 18:06:09](https://github.com/leanprover-community/mathlib/commit/47a8d5a)
refactor(data/{sigma,psigma}/order): Use `lex` synonym and new notation ([#11235](https://github.com/leanprover-community/mathlib/pull/11235))
This introduces notations `Σₗ i, α i` and `Σₗ' i, α i` for `lex (Σ i, α i)` and `lex (Σ' i, α i)` and use them instead of the instance switch with locale `lex`.
#### Estimated changes
Modified src/data/psigma/order.lean


Modified src/data/sigma/order.lean




## [2022-01-09 16:18:25](https://github.com/leanprover-community/mathlib/commit/2bb25f0)
feat(algebra/periodic): lifting to function on quotient group ([#11321](https://github.com/leanprover-community/mathlib/pull/11321))
I want to make more use of the type `real.angle` in
`analysis.special_functions.trigonometric.angle`, including defining
functions from this type in terms of periodic functions from `ℝ`.  To
support defining such functions, add a definition `periodic.lift` that
lifts a periodic function from `α` to a function from
`α ⧸ (add_subgroup.zmultiples c)`, along with a lemma
`periodic.lift_coe` about the values of the resulting function.
#### Estimated changes
Modified src/algebra/periodic.lean
- \+ *def* function.periodic.lift
- \+ *lemma* function.periodic.lift_coe



## [2022-01-09 16:18:24](https://github.com/leanprover-community/mathlib/commit/49ba33e)
feat(vscode): add a snippet for inserting a module docstring template ([#11312](https://github.com/leanprover-community/mathlib/pull/11312))
We already have a vscode snippet for adding copyright headers, this PR adds a similar one to generate a default module docstring with many of the common sections stubbed out.
By default it takes the filename, converts underscores to spaces and capitalizes each word to create the title, as this seems a sensible default. But otherwise all text is a static default example following the documentation style page to make it easier to remember the various recommended secitons.
To test do `ctrl+shift+p` to open the command pallette, type insert snippet, enter, and type module and it should show up.
See also [#3186](https://github.com/leanprover-community/mathlib/pull/3186)
#### Estimated changes
Added .vscode/module-docstring.code-snippets




## [2022-01-09 16:18:23](https://github.com/leanprover-community/mathlib/commit/fadbd95)
feat(field_theory/ratfunc): ratfunc.lift_on without is_domain ([#11227](https://github.com/leanprover-community/mathlib/pull/11227))
We might want to state results about rational functions without assuming
that the base ring is an integral domain.
Cf. Misconceptions about $K_X$, Kleiman, Steven; Stacks01X1
#### Estimated changes
Modified docs/references.bib


Modified src/field_theory/ratfunc.lean
- \+ *lemma* ratfunc.lift_on_condition_of_lift_on'_condition
- \+ *lemma* ratfunc.lift_on_of_fraction_ring_mk



## [2022-01-09 13:09:57](https://github.com/leanprover-community/mathlib/commit/9c224ff)
split(data/set/functor): Split off `data.set.lattice` ([#11327](https://github.com/leanprover-community/mathlib/pull/11327))
This moves the functor structure of `set` in a new file `data.set.functor`.
Also adds `alternative set` because it's quick and easy.
#### Estimated changes
Modified src/computability/NFA.lean


Modified src/control/traversable/instances.lean


Modified src/data/set/finite.lean


Added src/data/set/functor.lean
- \+ *lemma* set.bind_def
- \+ *lemma* set.fmap_eq_image
- \+ *lemma* set.pure_def
- \+ *lemma* set.seq_eq_set_seq

Modified src/data/set/lattice.lean
- \- *lemma* set.bind_def
- \- *lemma* set.fmap_eq_image
- \- *lemma* set.pure_def
- \- *lemma* set.seq_eq_set_seq



## [2022-01-09 07:58:15](https://github.com/leanprover-community/mathlib/commit/ad4ea53)
chore(*): miscellaneous to_additive related cleanup ([#11316](https://github.com/leanprover-community/mathlib/pull/11316))
A few cleanup changes related to to_additive:
* After https://github.com/leanprover-community/lean/pull/618 was merged, we no longer need to add namespaces manually in filtered_colimits and open subgroup
* to_additive can now generate some more lemmas in big_operators/fin
* to_additive now handles a proof in measure/haar better than it used to
  so remove a workaround there
#### Estimated changes
Modified src/algebra/big_operators/fin.lean
- \- *lemma* fin.sum_filter_succ_lt
- \- *lemma* fin.sum_filter_zero_lt

Modified src/algebra/category/CommRing/filtered_colimits.lean


Modified src/measure_theory/measure/haar.lean


Modified src/topology/algebra/open_subgroup.lean




## [2022-01-09 06:06:07](https://github.com/leanprover-community/mathlib/commit/ca5e55c)
feat(linear_algebra/basis): `basis.ext`, `basis.ext'` for semilinear maps ([#11317](https://github.com/leanprover-community/mathlib/pull/11317))
Extend `basis.ext` and `basis.ext'` to apply to the general
(semilinear) case of `linear_map` and `linear_equiv`.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+/\- *theorem* basis.ext'
- \+/\- *theorem* basis.ext



## [2022-01-09 03:54:54](https://github.com/leanprover-community/mathlib/commit/a58553d)
feat(data/nat/factorization): Add lemmas on factorizations of pairs of coprime numbers ([#10850](https://github.com/leanprover-community/mathlib/pull/10850))
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+ *lemma* nat.factorization_disjoint_of_coprime
- \+ *lemma* nat.factorization_mul_of_coprime
- \+ *lemma* nat.factorization_mul_support_of_coprime
- \+ *lemma* nat.factorization_mul_support_of_pos



## [2022-01-09 01:21:32](https://github.com/leanprover-community/mathlib/commit/d4846b3)
chore(ring_theory/fractional_ideal): fix typo ([#11311](https://github.com/leanprover-community/mathlib/pull/11311))
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean




## [2022-01-08 23:10:53](https://github.com/leanprover-community/mathlib/commit/22ff4eb)
feat(combinatorics/simple_graph/matchings): even_card_vertices_of_perfect_matching ([#11083](https://github.com/leanprover-community/mathlib/pull/11083))
#### Estimated changes
Modified src/combinatorics/simple_graph/matching.lean
- \+ *lemma* simple_graph.subgraph.is_matching.even_card
- \+ *lemma* simple_graph.subgraph.is_matching.to_edge.surjective
- \+ *lemma* simple_graph.subgraph.is_matching.to_edge_eq_of_adj
- \+ *lemma* simple_graph.subgraph.is_matching.to_edge_eq_to_edge_of_adj
- \+ *lemma* simple_graph.subgraph.is_perfect_matching.even_card
- \+ *lemma* simple_graph.subgraph.is_perfect_matching_iff_forall_degree

Modified src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* simple_graph.subgraph.adj.of_spanning_coe
- \+ *lemma* simple_graph.subgraph.degree_spanning_coe
- \+ *lemma* simple_graph.subgraph.is_spanning.card_verts
- \+ *lemma* simple_graph.subgraph.neighbor_set_subset_verts
- \- *lemma* simple_graph.subgraph.spanning_coe_adj_sub



## [2022-01-08 21:54:48](https://github.com/leanprover-community/mathlib/commit/0a75fdf)
feat(linear_algebra/eigenspace): prove eigenvalues are exactly elements of the spectrum when the space is finite dimensional ([#10961](https://github.com/leanprover-community/mathlib/pull/10961))
This adds `has_eigenvalue_iff_mem_spectrum` and then uses it to golf `exists_eigenvalue`
- [x] depends on: [#10912](https://github.com/leanprover-community/mathlib/pull/10912) 
- [x] depends on: [#10919](https://github.com/leanprover-community/mathlib/pull/10919)
#### Estimated changes
Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* module.End.has_eigenvalue_iff_mem_spectrum



## [2022-01-08 18:36:59](https://github.com/leanprover-community/mathlib/commit/ee136d9)
chore(set_theory/game/domineering): extract repeated goal into lemma and golf ([#11298](https://github.com/leanprover-community/mathlib/pull/11298))
`fst_pred_mem_erase_of_mem_right` and `snd_pred_mem_erase_of_mem_left` were common subgoals that appeared in two lemmas each.
#### Estimated changes
Modified src/set_theory/game/domineering.lean
- \+ *lemma* pgame.domineering.fst_pred_mem_erase_of_mem_right
- \+ *lemma* pgame.domineering.mem_left
- \+ *lemma* pgame.domineering.mem_right
- \+/\- *def* pgame.domineering.shift_right
- \+/\- *def* pgame.domineering.shift_up
- \+ *lemma* pgame.domineering.snd_pred_mem_erase_of_mem_left



## [2022-01-08 18:36:57](https://github.com/leanprover-community/mathlib/commit/84dbe31)
feat(topology/basic): add explicit definition of continuous_at ([#11296](https://github.com/leanprover-community/mathlib/pull/11296))
This was convenient in a demo.
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* continuous_at_def



## [2022-01-08 18:36:56](https://github.com/leanprover-community/mathlib/commit/25704ca)
docs(algebra/covariant_and_contravariant): minor typos ([#11293](https://github.com/leanprover-community/mathlib/pull/11293))
#### Estimated changes
Modified src/algebra/covariant_and_contravariant.lean




## [2022-01-08 18:36:54](https://github.com/leanprover-community/mathlib/commit/09f6989)
chore(analysis/normed_space/banach): move more to the `continuous_linear_map` NS ([#11263](https://github.com/leanprover-community/mathlib/pull/11263))
## Rename
* `open_mapping` → `continuous_linear_map.is_open_map`;
* `open_mapping_affine` → `affine_map.is_open_map`;
### New lemmas
* `continuous_linear_map.quotient_map`,
* `continuous_linear_map.interior_preimage`,
* `continuous_linear_map.closure_preimage`,
* `continuous_linear_map.frontier_preimage`.
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/analysis/normed_space/add_torsor_bases.lean


Modified src/analysis/normed_space/banach.lean
- \+ *lemma* affine_map.is_open_map
- \+ *lemma* continuous_linear_map.closure_preimage
- \+ *lemma* continuous_linear_map.exists_approx_preimage_norm_le
- \+ *theorem* continuous_linear_map.exists_preimage_norm_le
- \+ *lemma* continuous_linear_map.frontier_preimage
- \+ *lemma* continuous_linear_map.interior_preimage
- \- *lemma* exists_approx_preimage_norm_le
- \- *theorem* exists_preimage_norm_le
- \- *theorem* open_mapping
- \- *lemma* open_mapping_affine



## [2022-01-08 18:36:52](https://github.com/leanprover-community/mathlib/commit/60e279b)
chore(*): update to lean 3.36.0 ([#11253](https://github.com/leanprover-community/mathlib/pull/11253))
The main breaking change is the change in elaboration of double membership binders into x hx y hy, from x y hx hy.
#### Estimated changes
Modified archive/imo/imo1994_q1.lean


Modified archive/imo/imo2021_q1.lean


Modified leanpkg.toml


Modified src/algebra/lie/solvable.lean


Modified src/algebraic_geometry/prime_spectrum/basic.lean


Modified src/algebraic_geometry/properties.lean


Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/analysis/ODE/gronwall.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/box_integral/basic.lean


Modified src/analysis/box_integral/divergence_theorem.lean


Modified src/analysis/calculus/fderiv_measurable.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/convex/exposed.lean


Modified src/analysis/convex/extreme.lean


Modified src/analysis/convex/simplicial_complex/basic.lean


Modified src/analysis/convex/topology.lean


Modified src/analysis/normed/group/basic.lean


Modified src/combinatorics/hindman.lean


Modified src/data/complex/exponential.lean


Modified src/data/finset/lattice.lean
- \+/\- *lemma* finset.inf'_induction
- \+/\- *lemma* finset.inf_induction
- \+/\- *lemma* finset.sup'_induction
- \+/\- *lemma* finset.sup_induction

Modified src/data/finset/sort.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq.lean


Modified src/data/semiquot.lean


Modified src/data/set/basic.lean


Modified src/data/set/constructions.lean


Modified src/group_theory/complement.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/linear_algebra/affine_space/combination.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/finsupp.lean


Modified src/logic/basic.lean
- \+ *lemma* ball_cond_comm
- \+ *lemma* ball_mem_comm

Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/constructions/prod.lean


Modified src/measure_theory/integral/divergence_theorem.lean


Modified src/measure_theory/integral/set_to_l1.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/pi_system.lean


Modified src/number_theory/padics/padic_integers.lean


Modified src/number_theory/padics/padic_numbers.lean


Modified src/order/compactly_generated.lean


Modified src/order/countable_dense_linear_order.lean


Modified src/order/ideal.lean


Modified src/order/pfilter.lean


Modified src/order/prime_ideal.lean


Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/ideal/local_ring.lean


Modified src/ring_theory/localization.lean


Modified src/tactic/core.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/pretty_cases.lean


Modified src/tactic/squeeze.lean


Modified src/tactic/transfer.lean


Modified src/topology/algebra/ordered/intermediate_value.lean


Modified src/topology/algebra/semigroup.lean


Modified src/topology/algebra/uniform_filter_basis.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/algebra/valuation.lean


Modified src/topology/algebra/valued_field.lean


Modified src/topology/basic.lean


Modified src/topology/category/Compactum.lean


Modified src/topology/connected.lean


Modified src/topology/continuous_function/bounded.lean


Modified src/topology/continuous_function/stone_weierstrass.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/antilipschitz.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/holder.lean


Modified src/topology/path_connected.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/compact_separated.lean


Modified src/topology/uniform_space/separation.lean




## [2022-01-08 16:29:06](https://github.com/leanprover-community/mathlib/commit/dd1242d)
feat(algebra/associated): generalize nat.prime.pow_dvd_of_dvd_mul_{left,right} ([#11301](https://github.com/leanprover-community/mathlib/pull/11301))
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* prime.pow_dvd_of_dvd_mul_left
- \+ *lemma* prime.pow_dvd_of_dvd_mul_right

Modified src/data/nat/prime.lean
- \- *lemma* nat.prime.pow_dvd_of_dvd_mul_left
- \- *lemma* nat.prime.pow_dvd_of_dvd_mul_right



## [2022-01-08 16:29:05](https://github.com/leanprover-community/mathlib/commit/c76e113)
feat(ring_theory/laurent): coercion of R[x] to R((x)) lemmas ([#11295](https://github.com/leanprover-community/mathlib/pull/11295))
Make the coercion be `simp`-normal as opposed to `(algebra_map _ _)`.
Also generalize `of_power_series Γ R (power_series.C R r) = hahn_series.C r` and similarly for `X` to be true for any `[ordered semiring Γ]`, not just `ℤ`.
#### Estimated changes
Modified src/ring_theory/laurent_series.lean
- \+ *lemma* laurent_series.of_power_series_C
- \+ *lemma* polynomial.coe_coe
- \+ *lemma* polynomial.coe_laurent
- \+ *lemma* polynomial.coe_laurent_C
- \+ *lemma* polynomial.coe_laurent_X
- \+ *lemma* polynomial.coe_laurent_add
- \+ *lemma* polynomial.coe_laurent_mul
- \+ *lemma* polynomial.coe_laurent_one
- \+ *lemma* polynomial.coe_laurent_smul
- \+ *lemma* polynomial.coe_laurent_zero
- \+ *lemma* polynomial.coeff_coe_laurent
- \+ *lemma* polynomial.coeff_coe_laurent_coe



## [2022-01-08 16:29:04](https://github.com/leanprover-community/mathlib/commit/1162509)
chore(data/fin/vec_notation): generalize smul_cons ([#11285](https://github.com/leanprover-community/mathlib/pull/11285))
#### Estimated changes
Modified src/data/complex/module.lean


Modified src/data/fin/vec_notation.lean
- \+/\- *lemma* matrix.smul_cons
- \+/\- *lemma* matrix.smul_empty



## [2022-01-08 16:29:01](https://github.com/leanprover-community/mathlib/commit/56f021a)
feat(data/polynomial/{erase_lead + denoms_clearable}): strengthen a lemma ([#11257](https://github.com/leanprover-community/mathlib/pull/11257))
This PR is a step in the direction of simplifying [#11139](https://github.com/leanprover-community/mathlib/pull/11139) .
It strengthens lemma `induction_with_nat_degree_le` by showing that restriction can be strengthened on one of the assumptions.
~~It proves a lemma computing the `nat_degree` under functions on polynomials that include the shift of a variable.~~
EDIT: the lemma was moved to the later PR [#11265](https://github.com/leanprover-community/mathlib/pull/11265).
It fixes the unique use of lemma `induction_with_nat_degree_le`.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2311139.20taylor.20sum.20and.20nat_degree_taylor)
#### Estimated changes
Modified src/data/polynomial/denoms_clearable.lean


Modified src/data/polynomial/erase_lead.lean
- \+/\- *lemma* polynomial.induction_with_nat_degree_le



## [2022-01-08 16:28:59](https://github.com/leanprover-community/mathlib/commit/b181a12)
refactor(combinatorics/quiver): split into several files ([#11006](https://github.com/leanprover-community/mathlib/pull/11006))
This PR splits `combinatorics/quiver.lean` into several files. The main reason for this is to ensure that the category theory library only imports the necessary definitions (and not for example the stuff on arborescences).
Also adds some more documentation, and fixes a bug in the definition of weakly connected components.
#### Estimated changes
Modified src/category_theory/category/basic.lean


Modified src/category_theory/path_category.lean


Deleted src/combinatorics/quiver.lean
- \- *def* prefunctor.comp
- \- *def* prefunctor.id
- \- *def* prefunctor.map_path
- \- *lemma* prefunctor.map_path_comp
- \- *lemma* prefunctor.map_path_cons
- \- *lemma* prefunctor.map_path_nil
- \- *structure* prefunctor
- \- *def* quiver.empty
- \- *lemma* quiver.empty_arrow
- \- *def* quiver.geodesic_subtree
- \- *def* quiver.hom.op
- \- *def* quiver.hom.to_path
- \- *def* quiver.hom.unop
- \- *def* quiver.labelling
- \- *def* quiver.path.comp
- \- *lemma* quiver.path.comp_assoc
- \- *lemma* quiver.path.comp_cons
- \- *lemma* quiver.path.comp_nil
- \- *def* quiver.path.length
- \- *lemma* quiver.path.length_cons
- \- *lemma* quiver.path.length_nil
- \- *lemma* quiver.path.nil_comp
- \- *def* quiver.path.reverse
- \- *inductive* quiver.path
- \- *def* quiver.reverse
- \- *def* quiver.root
- \- *lemma* quiver.shortest_path_spec
- \- *def* quiver.symmetrify
- \- *structure* quiver.total
- \- *def* quiver.weakly_connected_component
- \- *def* quiver.wide_subquiver_equiv_set_total
- \- *def* quiver.wide_subquiver_symmetrify
- \- *def* quiver.zigzag_setoid
- \- *def* wide_subquiver.to_Type
- \- *def* wide_subquiver

Added src/combinatorics/quiver/arborescence.lean
- \+ *def* quiver.geodesic_subtree
- \+ *def* quiver.root
- \+ *lemma* quiver.shortest_path_spec

Added src/combinatorics/quiver/basic.lean
- \+ *def* prefunctor.comp
- \+ *def* prefunctor.id
- \+ *structure* prefunctor
- \+ *def* quiver.empty
- \+ *lemma* quiver.empty_arrow
- \+ *def* quiver.hom.op
- \+ *def* quiver.hom.unop

Added src/combinatorics/quiver/connected_component.lean
- \+ *def* quiver.path.reverse
- \+ *def* quiver.reverse
- \+ *def* quiver.symmetrify
- \+ *def* quiver.weakly_connected_component
- \+ *def* quiver.wide_subquiver_symmetrify
- \+ *def* quiver.zigzag_setoid

Added src/combinatorics/quiver/path.lean
- \+ *def* prefunctor.map_path
- \+ *lemma* prefunctor.map_path_comp
- \+ *lemma* prefunctor.map_path_cons
- \+ *lemma* prefunctor.map_path_nil
- \+ *def* quiver.hom.to_path
- \+ *def* quiver.path.comp
- \+ *lemma* quiver.path.comp_assoc
- \+ *lemma* quiver.path.comp_cons
- \+ *lemma* quiver.path.comp_nil
- \+ *def* quiver.path.length
- \+ *lemma* quiver.path.length_cons
- \+ *lemma* quiver.path.length_nil
- \+ *lemma* quiver.path.nil_comp
- \+ *inductive* quiver.path

Added src/combinatorics/quiver/subquiver.lean
- \+ *def* quiver.labelling
- \+ *structure* quiver.total
- \+ *def* quiver.wide_subquiver_equiv_set_total
- \+ *def* wide_subquiver.to_Type
- \+ *def* wide_subquiver

Modified src/group_theory/nielsen_schreier.lean




## [2022-01-08 16:28:58](https://github.com/leanprover-community/mathlib/commit/9b3fec5)
feat(algebraic_geometry): Gamma-Spec adjunction ([#9802](https://github.com/leanprover-community/mathlib/pull/9802))
Define the adjunction between the functors Gamma (global sections) and Spec (to LocallyRingedSpace).
I'm currently working on a more general version in http://arxiv.org/pdf/1103.2139.pdf (Theorem 2), which may require refactoring `structure_sheaf` and `Spec`.
#### Estimated changes
Added src/algebraic_geometry/Gamma_Spec_adjunction.lean
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.comp_ring_hom_ext
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.is_unit_res_to_Γ_Spec_map_basic_open
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.not_mem_prime_iff_unit_in_stalk
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.to_stalk_stalk_map_to_Γ_Spec
- \+ *abbreviation* algebraic_geometry.LocallyRingedSpace.to_to_Γ_Spec_map_basic_open
- \+ *def* algebraic_geometry.LocallyRingedSpace.to_Γ_Spec
- \+ *def* algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_SheafedSpace
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_SheafedSpace_app_eq
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_SheafedSpace_app_spec
- \+ *def* algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_base
- \+ *def* algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_c_app
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_c_app_iff
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_c_app_spec
- \+ *def* algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_c_basic_opens
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_continuous
- \+ *def* algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_fun
- \+ *abbreviation* algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_map_basic_open
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_map_basic_open_eq
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_preim_basic_open_eq
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.Γ_Spec_left_triangle
- \+ *def* algebraic_geometry.LocallyRingedSpace.Γ_to_stalk
- \+ *def* algebraic_geometry.identity_to_Γ_Spec
- \+ *def* algebraic_geometry.Γ_Spec.LocallyRingedSpace_adjunction
- \+ *def* algebraic_geometry.Γ_Spec.adjunction
- \+ *lemma* algebraic_geometry.Γ_Spec.adjunction_counit_app
- \+ *lemma* algebraic_geometry.Γ_Spec.adjunction_hom_equiv
- \+ *lemma* algebraic_geometry.Γ_Spec.adjunction_hom_equiv_apply
- \+ *lemma* algebraic_geometry.Γ_Spec.adjunction_hom_equiv_symm_apply
- \+ *lemma* algebraic_geometry.Γ_Spec.adjunction_unit_app
- \+ *lemma* algebraic_geometry.Γ_Spec.left_triangle
- \+ *lemma* algebraic_geometry.Γ_Spec.right_triangle

Modified src/algebraic_geometry/Spec.lean


Modified src/algebraic_geometry/structure_sheaf.lean
- \- *lemma* algebraic_geometry.structure_sheaf.is_localization.to_basic_open
- \- *lemma* algebraic_geometry.structure_sheaf.is_localization.to_stalk
- \+ *lemma* algebraic_geometry.structure_sheaf.open_algebra_map
- \+ *lemma* algebraic_geometry.structure_sheaf.stalk_algebra_map



## [2022-01-08 15:04:37](https://github.com/leanprover-community/mathlib/commit/b1955dc)
feat(data/matrix/basic): infix notation for matrix.dot_product in locale matrix ([#11289](https://github.com/leanprover-community/mathlib/pull/11289))
I created an infix notation for `matrix.dot_product` in locale `matrix`. The notation was consulted with @eric-wieser in [#11181](https://github.com/leanprover-community/mathlib/pull/11181).
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *lemma* matrix.add_dot_product
- \+/\- *lemma* matrix.diagonal_dot_product
- \+/\- *lemma* matrix.dot_product_add
- \+/\- *lemma* matrix.dot_product_diagonal'
- \+/\- *lemma* matrix.dot_product_diagonal
- \+/\- *lemma* matrix.dot_product_neg
- \+/\- *lemma* matrix.dot_product_single
- \+/\- *lemma* matrix.dot_product_star
- \+/\- *lemma* matrix.dot_product_sub
- \+/\- *lemma* matrix.dot_product_zero'
- \+/\- *lemma* matrix.dot_product_zero
- \+/\- *lemma* matrix.neg_dot_product
- \+/\- *lemma* matrix.single_dot_product
- \+/\- *lemma* matrix.star_dot_product
- \+/\- *lemma* matrix.star_dot_product_star
- \+/\- *lemma* matrix.sub_dot_product
- \+/\- *lemma* matrix.zero_dot_product'
- \+/\- *lemma* matrix.zero_dot_product



## [2022-01-08 15:04:36](https://github.com/leanprover-community/mathlib/commit/4304127)
feat(ring_theory/power_series): teach simp to simplify more coercions of polynomials  to power series ([#11287](https://github.com/leanprover-community/mathlib/pull/11287))
So that simp can prove that the polynomial `5 * X^2 + X + 1` coerced to a power series is the same thing with the power series generator `X`. Likewise for `mv_power_series`.
#### Estimated changes
Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* mv_polynomial.coe_bit0
- \+ *lemma* mv_polynomial.coe_bit1
- \+ *lemma* mv_polynomial.coe_pow
- \+ *lemma* polynomial.coe_bit0
- \+ *lemma* polynomial.coe_bit1
- \+ *lemma* polynomial.coe_pow



## [2022-01-08 15:04:35](https://github.com/leanprover-community/mathlib/commit/e871386)
feat(number_theory/cyclotomic/basic): add lemmas ([#11264](https://github.com/leanprover-community/mathlib/pull/11264))
From flt-regular.
#### Estimated changes
Modified src/number_theory/cyclotomic/basic.lean
- \+ *lemma* is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots
- \+ *lemma* is_cyclotomic_extension.finite_dimensional
- \+ *lemma* is_cyclotomic_extension.integral
- \+ *lemma* is_cyclotomic_extension.splits_X_pow_sub_one
- \+ *lemma* is_cyclotomic_extension.splits_cyclotomic
- \+ *lemma* is_cyclotomic_extension.splitting_field_X_pow_sub_one
- \+ *lemma* is_cyclotomic_extension.splitting_field_cyclotomic



## [2022-01-08 15:04:33](https://github.com/leanprover-community/mathlib/commit/c7fa66e)
feat(data/nat/prime): power to factor count divides natural ([#11226](https://github.com/leanprover-community/mathlib/pull/11226))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.pow_factors_count_dvd



## [2022-01-08 15:04:32](https://github.com/leanprover-community/mathlib/commit/4d79d5f)
chore(measure_theory/group/arithmetic): use implicit argument for measurable_space ([#11205](https://github.com/leanprover-community/mathlib/pull/11205))
The `measurable_space` argument is inferred from other arguments (like `measurable f` or a measure for example) instead of being a type class. This ensures that the lemmas are usable without `@` when several measurable space structures are used for the same type.
Also use more `variables`.
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean


Modified src/measure_theory/function/special_functions.lean
- \+/\- *lemma* ae_measurable.inner
- \+/\- *lemma* measurable.inner

Modified src/measure_theory/group/arithmetic.lean
- \+/\- *lemma* ae_measurable.const_div
- \+/\- *lemma* ae_measurable.const_mul
- \+/\- *lemma* ae_measurable.const_pow
- \+/\- *lemma* ae_measurable.const_smul'
- \+/\- *lemma* ae_measurable.const_smul
- \+/\- *lemma* ae_measurable.div'
- \+/\- *lemma* ae_measurable.div
- \+/\- *lemma* ae_measurable.div_const
- \+/\- *lemma* ae_measurable.inv
- \+/\- *lemma* ae_measurable.mul'
- \+/\- *lemma* ae_measurable.mul
- \+/\- *lemma* ae_measurable.mul_const
- \+/\- *lemma* ae_measurable.pow
- \+/\- *lemma* ae_measurable.pow_const
- \+/\- *lemma* ae_measurable.smul_const
- \+/\- *lemma* finset.ae_measurable_prod'
- \+/\- *lemma* finset.ae_measurable_prod
- \+/\- *lemma* finset.measurable_prod'
- \+/\- *lemma* finset.measurable_prod
- \+/\- *lemma* list.ae_measurable_prod'
- \+/\- *lemma* list.ae_measurable_prod
- \+/\- *lemma* measurable.const_div
- \+/\- *lemma* measurable.const_mul
- \+/\- *lemma* measurable.const_pow
- \+/\- *lemma* measurable.const_smul'
- \+/\- *lemma* measurable.const_smul
- \+/\- *lemma* measurable.div'
- \+/\- *lemma* measurable.div
- \+/\- *lemma* measurable.div_const
- \+/\- *lemma* measurable.inv
- \+/\- *lemma* measurable.mul'
- \+/\- *lemma* measurable.mul
- \+/\- *lemma* measurable.mul_const
- \+/\- *lemma* measurable.pow
- \+/\- *lemma* measurable.pow_const
- \+/\- *lemma* measurable.smul
- \+/\- *lemma* measurable.smul_const
- \+/\- *lemma* measurable_set_eq_fun
- \+/\- *lemma* multiset.ae_measurable_prod'
- \+/\- *lemma* multiset.ae_measurable_prod



## [2022-01-08 14:24:00](https://github.com/leanprover-community/mathlib/commit/2231173)
feat(group_theory/commuting_probability): New file ([#11243](https://github.com/leanprover-community/mathlib/pull/11243))
This PR introduces commuting probabilities of finite groups.
#### Estimated changes
Added src/group_theory/commuting_probability.lean
- \+ *lemma* card_comm_eq_card_conj_classes_mul_card
- \+ *def* comm_prob
- \+ *lemma* comm_prob_def'
- \+ *lemma* comm_prob_def
- \+ *lemma* comm_prob_eq_one_iff
- \+ *lemma* comm_prob_le_one
- \+ *lemma* comm_prob_pos



## [2022-01-08 07:22:54](https://github.com/leanprover-community/mathlib/commit/07f9b8e)
feat(data/sum/order): Linear and disjoint sums of orders ([#11157](https://github.com/leanprover-community/mathlib/pull/11157))
This defines the disjoint sum of two orders on `α ⊕ β` and the linear (aka lexicographic) sum of two orders on `α ⊕ₗ β` (a type synonym of `α ⊕ β`) in a new file `data.sum.order`.
#### Estimated changes
Modified src/algebra/lie/classical.lean


Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.sum_assoc
- \- *theorem* equiv.sum_assoc_apply_in1
- \- *theorem* equiv.sum_assoc_apply_in2
- \- *theorem* equiv.sum_assoc_apply_in3
- \+ *lemma* equiv.sum_assoc_apply_inl_inl
- \+ *lemma* equiv.sum_assoc_apply_inl_inr
- \+ *lemma* equiv.sum_assoc_apply_inr
- \+ *lemma* equiv.sum_assoc_symm_apply_inl
- \+ *lemma* equiv.sum_assoc_symm_apply_inr_inl
- \+ *lemma* equiv.sum_assoc_symm_apply_inr_inr
- \+/\- *def* equiv.sum_comm

Modified src/data/sum/basic.lean
- \+ *lemma* sum.get_left_eq_none_iff
- \+ *lemma* sum.get_right_eq_none_iff
- \+ *lemma* sum.lift_rel.mono
- \+ *lemma* sum.lift_rel.mono_left
- \+ *lemma* sum.lift_rel.mono_right
- \+ *inductive* sum.lift_rel
- \+ *lemma* sum.lift_rel_inl_inl
- \+ *lemma* sum.lift_rel_inr_inr
- \+ *lemma* sum.lift_rel_swap_iff
- \+ *lemma* sum.not_lift_rel_inl_inr
- \+ *lemma* sum.not_lift_rel_inr_inl

Added src/data/sum/order.lean
- \+ *def* order_iso.sum_assoc
- \+ *lemma* order_iso.sum_assoc_apply_inl_inl
- \+ *lemma* order_iso.sum_assoc_apply_inl_inr
- \+ *lemma* order_iso.sum_assoc_apply_inr
- \+ *lemma* order_iso.sum_assoc_symm_apply_inl
- \+ *lemma* order_iso.sum_assoc_symm_apply_inr_inl
- \+ *lemma* order_iso.sum_assoc_symm_apply_inr_inr
- \+ *def* order_iso.sum_comm
- \+ *lemma* order_iso.sum_comm_symm
- \+ *def* order_iso.sum_dual_distrib
- \+ *lemma* order_iso.sum_dual_distrib_inl
- \+ *lemma* order_iso.sum_dual_distrib_inr
- \+ *lemma* order_iso.sum_dual_distrib_symm_inl
- \+ *lemma* order_iso.sum_dual_distrib_symm_inr
- \+ *def* order_iso.sum_lex_assoc
- \+ *lemma* order_iso.sum_lex_assoc_apply_inl_inl
- \+ *lemma* order_iso.sum_lex_assoc_apply_inl_inr
- \+ *lemma* order_iso.sum_lex_assoc_apply_inr
- \+ *lemma* order_iso.sum_lex_assoc_symm_apply_inl
- \+ *lemma* order_iso.sum_lex_assoc_symm_apply_inr_inl
- \+ *lemma* order_iso.sum_lex_assoc_symm_apply_inr_inr
- \+ *def* order_iso.sum_lex_dual_antidistrib
- \+ *lemma* order_iso.sum_lex_dual_antidistrib_inl
- \+ *lemma* order_iso.sum_lex_dual_antidistrib_inr
- \+ *lemma* order_iso.sum_lex_dual_antidistrib_symm_inl
- \+ *lemma* order_iso.sum_lex_dual_antidistrib_symm_inr
- \+ *lemma* sum.densely_ordered_iff
- \+ *lemma* sum.inl_le_inl_iff
- \+ *lemma* sum.inl_lt_inl_iff
- \+ *lemma* sum.inl_mono
- \+ *lemma* sum.inl_strict_mono
- \+ *abbreviation* sum.inlₗ
- \+ *lemma* sum.inr_le_inr_iff
- \+ *lemma* sum.inr_lt_inr_iff
- \+ *lemma* sum.inr_mono
- \+ *lemma* sum.inr_strict_mono
- \+ *abbreviation* sum.inrₗ
- \+ *lemma* sum.le_def
- \+ *lemma* sum.lex.inl_bot
- \+ *lemma* sum.lex.inl_le_inl_iff
- \+ *lemma* sum.lex.inl_le_inr
- \+ *lemma* sum.lex.inl_lt_inl_iff
- \+ *lemma* sum.lex.inl_lt_inr
- \+ *lemma* sum.lex.inl_mono
- \+ *lemma* sum.lex.inl_strict_mono
- \+ *lemma* sum.lex.inr_le_inr_iff
- \+ *lemma* sum.lex.inr_lt_inr_iff
- \+ *lemma* sum.lex.inr_mono
- \+ *lemma* sum.lex.inr_strict_mono
- \+ *lemma* sum.lex.inr_top
- \+ *lemma* sum.lex.le_def
- \+ *lemma* sum.lex.lt_def
- \+ *lemma* sum.lex.not_inr_le_inl
- \+ *lemma* sum.lex.not_inr_lt_inl
- \+ *lemma* sum.lex.to_lex_le_to_lex
- \+ *lemma* sum.lex.to_lex_lt_to_lex
- \+ *lemma* sum.lex.to_lex_mono
- \+ *lemma* sum.lex.to_lex_strict_mono
- \+ *lemma* sum.lift_rel.refl
- \+ *lemma* sum.lift_rel.trans
- \+ *lemma* sum.lt_def
- \+ *lemma* sum.no_bot_order_iff
- \+ *lemma* sum.no_top_order_iff
- \+ *lemma* sum.not_inl_le_inr
- \+ *lemma* sum.not_inl_lt_inr
- \+ *lemma* sum.not_inr_le_inl
- \+ *lemma* sum.not_inr_lt_inl
- \+ *lemma* sum.swap_le_swap_iff
- \+ *lemma* sum.swap_lt_swap_iff

Modified src/logic/basic.lean
- \+ *lemma* or.imp3

Modified src/order/lexicographic.lean
- \+/\- *def* of_lex
- \+/\- *def* to_lex

Modified src/order/rel_classes.lean
- \+ *lemma* antisymm_of

Modified src/set_theory/ordinal.lean


Modified src/tactic/induction.lean




## [2022-01-08 00:14:42](https://github.com/leanprover-community/mathlib/commit/303e77c)
feat(topology/metric_space/hausdorff_distance): make iffs ([#11288](https://github.com/leanprover-community/mathlib/pull/11288))
* Make `exists_edist_lt_of_inf_edist_lt` and `exists_dist_lt_of_inf_edist_lt` iffs. Rename to `inf_[e]dist_lt_iff`.
* Simplify some proofs
#### Estimated changes
Modified src/analysis/normed_space/riesz_lemma.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/topology/metric_space/hausdorff_distance.lean
- \- *lemma* emetric.exists_edist_lt_of_inf_edist_lt
- \+ *lemma* emetric.inf_edist_lt_iff
- \- *lemma* metric.exists_dist_lt_of_inf_dist_lt
- \+ *lemma* metric.inf_dist_lt_iff



## [2022-01-07 18:21:53](https://github.com/leanprover-community/mathlib/commit/5cbfddd)
feat(data/finset/sym): Symmetric powers of a finset ([#11142](https://github.com/leanprover-community/mathlib/pull/11142))
This defines `finset.sym` and `finset.sym2`, which are the `finset` analogs of `sym` and `sym2`, in a new file `data.finset.sym`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.disjoint_filter_filter_neg

Modified src/data/finset/prod.lean
- \+ *lemma* finset.diag_union_off_diag
- \+ *lemma* finset.disjoint_diag_off_diag
- \+ *lemma* finset.product_eq_empty

Added src/data/finset/sym.lean
- \+ *lemma* finset.diag_mem_sym2_iff
- \+ *lemma* finset.eq_empty_of_sym_eq_empty
- \+ *lemma* finset.image_diag_union_image_off_diag
- \+ *lemma* finset.is_diag_mk_of_mem_diag
- \+ *lemma* finset.mem_sym2_iff
- \+ *lemma* finset.mem_sym_iff
- \+ *lemma* finset.mk_mem_sym2_iff
- \+ *lemma* finset.not_is_diag_mk_of_mem_off_diag
- \+ *lemma* finset.repeat_mem_sym
- \+ *lemma* finset.sym2_empty
- \+ *lemma* finset.sym2_eq_empty
- \+ *lemma* finset.sym2_mono
- \+ *lemma* finset.sym2_nonempty
- \+ *lemma* finset.sym2_singleton
- \+ *lemma* finset.sym2_univ
- \+ *lemma* finset.sym_empty
- \+ *lemma* finset.sym_eq_empty
- \+ *lemma* finset.sym_inter
- \+ *lemma* finset.sym_mono
- \+ *lemma* finset.sym_nonempty
- \+ *lemma* finset.sym_singleton
- \+ *lemma* finset.sym_succ
- \+ *lemma* finset.sym_union
- \+ *lemma* finset.sym_univ
- \+ *lemma* finset.sym_zero

Modified src/data/sym/basic.lean
- \+ *lemma* sym.coe_repeat
- \+ *lemma* sym.eq_repeat_iff
- \+ *lemma* sym.mem_repeat

Modified src/data/sym/card.lean
- \+ *lemma* finset.card_sym2
- \+/\- *lemma* sym2.card_image_diag

Modified src/data/sym/sym2.lean
- \+ *lemma* sym2.ball
- \+ *lemma* sym2.out_fst_mem
- \+ *lemma* sym2.out_snd_mem



## [2022-01-07 18:21:52](https://github.com/leanprover-community/mathlib/commit/a8d37c1)
feat(data/nat/factorization): Defining `factorization` ([#10540](https://github.com/leanprover-community/mathlib/pull/10540))
Defining `factorization` as a `finsupp`, as discussed in
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Prime.20factorizations
and 
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Proof.20of.20Euler's.20product.20formula.20for.20totient
This is the first of a series of PRs to build up the infrastructure needed for the proof of Euler's product formula for the totient function.
#### Estimated changes
Added src/data/nat/factorization.lean
- \+ *lemma* nat.factor_iff_mem_factorization
- \+ *lemma* nat.factorization_eq_count
- \+ *lemma* nat.factorization_eq_zero_iff
- \+ *lemma* nat.factorization_inj
- \+ *lemma* nat.factorization_mul
- \+ *lemma* nat.factorization_one
- \+ *lemma* nat.factorization_pow
- \+ *lemma* nat.factorization_zero
- \+ *lemma* nat.prime.factorization
- \+ *lemma* nat.prime.factorization_pow
- \+ *lemma* nat.support_factorization

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* associated_of_factorization_eq
- \+ *lemma* factorization_eq_count
- \+ *lemma* factorization_mul
- \+ *lemma* factorization_one
- \+ *lemma* factorization_pow
- \+ *lemma* factorization_zero
- \+ *lemma* support_factorization



## [2022-01-07 18:21:50](https://github.com/leanprover-community/mathlib/commit/3b02ad7)
feat(topology/homotopy/equiv): Add homotopy equivalences between topological spaces ([#10529](https://github.com/leanprover-community/mathlib/pull/10529))
#### Estimated changes
Modified src/topology/continuous_function/basic.lean
- \+ *lemma* continuous_map.comp_id
- \+ *lemma* continuous_map.id_comp

Added src/topology/homotopy/equiv.lean
- \+ *lemma* continuous_map.homotopy_equiv.coe_inv_fun
- \+ *lemma* continuous_map.homotopy_equiv.continuous
- \+ *def* continuous_map.homotopy_equiv.refl
- \+ *def* continuous_map.homotopy_equiv.simps.apply
- \+ *def* continuous_map.homotopy_equiv.simps.symm_apply
- \+ *def* continuous_map.homotopy_equiv.symm
- \+ *lemma* continuous_map.homotopy_equiv.symm_trans
- \+ *lemma* continuous_map.homotopy_equiv.to_fun_eq_coe
- \+ *def* continuous_map.homotopy_equiv.trans
- \+ *structure* continuous_map.homotopy_equiv
- \+ *lemma* homeomorph.coe_to_homotopy_equiv
- \+ *lemma* homeomorph.refl_to_homotopy_equiv
- \+ *lemma* homeomorph.symm_to_homotopy_equiv
- \+ *def* homeomorph.to_homotopy_equiv
- \+ *lemma* homeomorph.trans_to_homotopy_equiv



## [2022-01-07 16:25:53](https://github.com/leanprover-community/mathlib/commit/13e99c7)
feat(algebra,linear_algebra,ring_theory): more is_central_scalar instances ([#11297](https://github.com/leanprover-community/mathlib/pull/11297))
This provides new transitive scalar actions:
* on `lie_submodule R L M` that match the actions on `submodule R M`
* on quotients by `lie_submodule R L M` that match the actions on quotients by `submodule R M`
The rest of the instances in this PR live in `Prop` so do not define any further actions.
This also fixes some overly verbose instance names.
#### Estimated changes
Modified src/algebra/direct_sum/module.lean


Modified src/algebra/lie/quotient.lean


Modified src/algebra/lie/subalgebra.lean


Modified src/algebra/lie/submodule.lean


Modified src/linear_algebra/quotient.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/derivation.lean




## [2022-01-07 16:25:52](https://github.com/leanprover-community/mathlib/commit/b8f5d0a)
chore(category_theory/abelian/basic): abelian categories have finite limits and finite colimits. ([#11271](https://github.com/leanprover-community/mathlib/pull/11271))
#### Estimated changes
Modified src/category_theory/abelian/basic.lean




## [2022-01-07 14:24:20](https://github.com/leanprover-community/mathlib/commit/b430316)
chore(topology/algebra/module/basic): add continuous_linear_map.is_central_scalar ([#11291](https://github.com/leanprover-community/mathlib/pull/11291))
#### Estimated changes
Modified src/topology/algebra/module/basic.lean




## [2022-01-07 14:24:17](https://github.com/leanprover-community/mathlib/commit/3b7a783)
feat(topology/*): Gluing topological spaces ([#9864](https://github.com/leanprover-community/mathlib/pull/9864))
#### Estimated changes
Modified src/algebraic_geometry/properties.lean


Added src/category_theory/concrete_category/elementwise.lean


Modified src/category_theory/limits/concrete_category.lean


Modified src/category_theory/limits/shapes/concrete_category.lean


Modified src/logic/function/basic.lean
- \+ *lemma* inv_image.equivalence

Added src/topology/gluing.lean
- \+ *lemma* Top.glue_data.eqv_gen_of_π_eq
- \+ *def* Top.glue_data.from_open_subsets_glue
- \+ *lemma* Top.glue_data.from_open_subsets_glue_injective
- \+ *lemma* Top.glue_data.from_open_subsets_glue_is_open_map
- \+ *lemma* Top.glue_data.from_open_subsets_glue_open_embedding
- \+ *lemma* Top.glue_data.image_inter
- \+ *lemma* Top.glue_data.is_open_iff
- \+ *def* Top.glue_data.mk'
- \+ *def* Top.glue_data.mk_core.t'
- \+ *lemma* Top.glue_data.mk_core.t_inv
- \+ *structure* Top.glue_data.mk_core
- \+ *def* Top.glue_data.of_open_subsets
- \+ *def* Top.glue_data.open_cover_glue_homeo
- \+ *lemma* Top.glue_data.open_image_open
- \+ *lemma* Top.glue_data.preimage_image_eq_image'
- \+ *lemma* Top.glue_data.preimage_image_eq_image
- \+ *lemma* Top.glue_data.preimage_range
- \+ *lemma* Top.glue_data.range_from_open_subsets_glue
- \+ *def* Top.glue_data.rel
- \+ *lemma* Top.glue_data.rel_equiv
- \+ *lemma* Top.glue_data.ι_eq_iff_rel
- \+ *lemma* Top.glue_data.ι_from_open_subsets_glue
- \+ *lemma* Top.glue_data.ι_injective
- \+ *lemma* Top.glue_data.ι_jointly_surjective
- \+ *lemma* Top.glue_data.ι_open_embedding
- \+ *lemma* Top.glue_data.π_surjective
- \+ *structure* Top.glue_data



## [2022-01-07 12:43:41](https://github.com/leanprover-community/mathlib/commit/6fb638b)
feat(*): add lemmas, golf ([#11294](https://github.com/leanprover-community/mathlib/pull/11294))
### New lemmas
* `function.mul_support_nonempty_iff` and `function.support_nonempty_iff`;
* `set.infinite_union`;
* `nat.exists_subseq_of_forall_mem_union` (to be used in an upcoming mass golfing of `is_pwo`/`is_wf`);
* `hahn_series.coeff_inj`, `hahn_series.coeff_injective`, `hahn_series.coeff_fun_eq_zero_iff`, `hahn_series.support_eq_empty_iff`;
* `nat.coe_order_embedding_of_set` (`simp` + `rfl`);
* `nat.subtype.of_nat_range`, `nat.subtype.coe_comp_of_nat_range`.
### Golfed proofs
* `set.countable.prod`;
*  `nat.order_embedding_of_set_range`;
*  `hahn-series.support_nonempty_iff`;
### Renamed
* `set.finite.union_iff` → `set.finite_union`, add `@[simp]` attr;
* `set.finite.diff` → `set.finite.of_diff`, drop 1 arg;
#### Estimated changes
Modified src/algebra/support.lean
- \+ *lemma* function.mul_support_nonempty_iff

Modified src/data/equiv/denumerable.lean
- \+ *lemma* nat.subtype.coe_comp_of_nat_range
- \+ *lemma* nat.subtype.of_nat_range

Modified src/data/set/countable.lean


Modified src/data/set/finite.lean
- \- *lemma* set.finite.diff
- \+ *lemma* set.finite.of_diff
- \- *lemma* set.finite.union_iff
- \+ *lemma* set.finite_union
- \+ *lemma* set.infinite_union

Modified src/number_theory/modular.lean


Modified src/order/order_iso_nat.lean
- \+ *lemma* nat.coe_order_embedding_of_set
- \+ *theorem* nat.exists_subseq_of_forall_mem_union
- \+/\- *lemma* nat.order_embedding_of_set_apply

Modified src/ring_theory/hahn_series.lean
- \+ *lemma* hahn_series.coeff_fun_eq_zero_iff
- \+ *lemma* hahn_series.coeff_inj
- \+ *lemma* hahn_series.coeff_injective
- \+/\- *def* hahn_series.support
- \+ *lemma* hahn_series.support_eq_empty_iff
- \+/\- *lemma* hahn_series.support_nonempty_iff
- \+/\- *lemma* hahn_series.support_zero
- \+/\- *lemma* hahn_series.zero_coeff



## [2022-01-06 19:34:08](https://github.com/leanprover-community/mathlib/commit/0b96630)
feat(algebra/{monoid_algebra/basic,free_non_unital_non_assoc_algebra,lie/free}): generalize typeclasses ([#11283](https://github.com/leanprover-community/mathlib/pull/11283))
This fixes a number of missing or problematic typeclasses:
* The smul typeclasses on `monoid_algebra` had overly strong assumptions
* `add_comm_group (monoid_algebra k G)` was missing.
* `monoid_algebra` had diamonds in its int-module structures, which were different between the one inferred from `ring` and `add_group`.
* `monoid_algebra` was missing an instance of the new `non_unital_non_assoc_ring`.
* `free_non_unital_non_assoc_algebra` was missing a lot of smul typeclasses and transitive module structures that it should inherit from `monoid_algebra`. Since every instance should just be inherited, we change `free_non_unital_non_assoc_algebra` to an abbreviation.
* `free_lie_algebra` had diamonds in its int-module and nat-module structures.
* `free_lie_algebra` was missing transitive module structures.
This also golfs some proofs about `free_non_unital_non_assoc_algebra`, and removes the `irreducible` attributes since these just make some obvious proofs more awkward.
#### Estimated changes
Modified src/algebra/free_non_unital_non_assoc_algebra.lean
- \+ *abbreviation* free_non_unital_non_assoc_algebra
- \- *def* free_non_unital_non_assoc_algebra

Modified src/algebra/lie/free.lean
- \+/\- *lemma* free_lie_algebra.rel.add_left
- \+/\- *lemma* free_lie_algebra.rel.neg
- \+ *lemma* free_lie_algebra.rel.smul_of_tower
- \+ *lemma* free_lie_algebra.rel.sub_left
- \+ *lemma* free_lie_algebra.rel.sub_right

Modified src/algebra/monoid_algebra/basic.lean




## [2022-01-06 17:51:55](https://github.com/leanprover-community/mathlib/commit/d0bf8bd)
feat(set_theory/ordinal): `ordinal` is a successor order ([#11284](https://github.com/leanprover-community/mathlib/pull/11284))
This provides the `succ_order` instance for `ordinal`.
#### Estimated changes
Modified src/set_theory/ordinal.lean




## [2022-01-06 17:51:52](https://github.com/leanprover-community/mathlib/commit/5893fbf)
feat(data/polynomial/monic): add two lemmas on degrees of monic polynomials ([#11259](https://github.com/leanprover-community/mathlib/pull/11259))
This PR is a step in the direction of simplifying [#11139](https://github.com/leanprover-community/mathlib/pull/11139).
The two lemmas involve computing the degree of a power of monic polynomials.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2311139.20taylor.20sum.20and.20nat_degree_taylor)
#### Estimated changes
Modified src/data/polynomial/monic.lean
- \+ *lemma* polynomial.monic.nat_degree_pow
- \+ *lemma* polynomial.nat_degree_pow_X_add_C



## [2022-01-06 14:41:11](https://github.com/leanprover-community/mathlib/commit/9b39ab2)
feat(algebra/group/freiman): Freiman homomorphisms ([#10497](https://github.com/leanprover-community/mathlib/pull/10497))
This defines Freiman homomorphisms, which are maps preserving products of `n` elements (but only in the codomain. One can never get back to the domain).
This is useful in additive combinatorics.
#### Estimated changes
Added src/algebra/group/freiman.lean
- \+ *structure* add_freiman_hom
- \+ *lemma* freiman_hom.cancel_left_on
- \+ *lemma* freiman_hom.cancel_right
- \+ *lemma* freiman_hom.cancel_right_on
- \+ *lemma* freiman_hom.coe_comp
- \+ *lemma* freiman_hom.coe_mk
- \+ *lemma* freiman_hom.comp_apply
- \+ *lemma* freiman_hom.comp_assoc
- \+ *lemma* freiman_hom.comp_id
- \+ *def* freiman_hom.const
- \+ *lemma* freiman_hom.const_apply
- \+ *lemma* freiman_hom.const_comp
- \+ *lemma* freiman_hom.div_apply
- \+ *lemma* freiman_hom.div_comp
- \+ *lemma* freiman_hom.ext
- \+ *def* freiman_hom.freiman_hom_class_of_le
- \+ *lemma* freiman_hom.id_comp
- \+ *lemma* freiman_hom.inv_apply
- \+ *lemma* freiman_hom.inv_comp
- \+ *lemma* freiman_hom.mk_coe
- \+ *lemma* freiman_hom.mul_apply
- \+ *lemma* freiman_hom.mul_comp
- \+ *lemma* freiman_hom.one_apply
- \+ *lemma* freiman_hom.one_comp
- \+ *def* freiman_hom.to_freiman_hom
- \+ *lemma* freiman_hom.to_freiman_hom_coe
- \+ *lemma* freiman_hom.to_freiman_hom_injective
- \+ *lemma* freiman_hom.to_fun_eq_coe
- \+ *structure* freiman_hom
- \+ *lemma* map_prod_eq_map_prod
- \+ *lemma* map_prod_eq_map_prod_of_le
- \+ *def* monoid_hom.to_freiman_hom
- \+ *lemma* monoid_hom.to_freiman_hom_coe
- \+ *lemma* monoid_hom.to_freiman_hom_injective

Modified src/data/fun_like.lean




## [2022-01-06 12:39:56](https://github.com/leanprover-community/mathlib/commit/d2428fa)
feat(ring_theory/localization): Localization is the localization of localization. ([#11145](https://github.com/leanprover-community/mathlib/pull/11145))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.exists_image_iff

Modified src/ring_theory/localization.lean
- \+ *lemma* is_localization.is_localization_of_is_exists_mul_mem
- \+ *lemma* is_localization.is_localization_of_submonoid_le
- \+ *def* is_localization.localization_algebra_of_submonoid_le
- \+ *lemma* is_localization.localization_is_scalar_tower_of_submonoid_le



## [2022-01-06 10:39:24](https://github.com/leanprover-community/mathlib/commit/54c2567)
feat(category_theory/sites): The pushforward pullback adjunction ([#11273](https://github.com/leanprover-community/mathlib/pull/11273))
#### Estimated changes
Modified src/category_theory/sites/cover_preserving.lean
- \+ *lemma* category_theory.compatible_preserving_of_flat
- \+ *def* category_theory.sites.pullback_pushforward_adjunction
- \+ *def* category_theory.sites.pushforward



## [2022-01-06 10:39:23](https://github.com/leanprover-community/mathlib/commit/7af5e86)
feat(algebra/big_operators/multiset): Multiset product under some usual maps ([#10907](https://github.com/leanprover-community/mathlib/pull/10907))
Product of the image of a multiset under `λ a, (f a)⁻¹`, `λ a, f a / g a`, `λ a, f a ^ n` (for `n` in `ℕ` and `ℤ`).
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* finset.prod_inv_distrib

Modified src/algebra/big_operators/multiset.lean
- \+/\- *lemma* multiset.pow_count
- \+ *lemma* multiset.prod_hom'
- \+ *lemma* multiset.prod_hom₂
- \+ *lemma* multiset.prod_map_div
- \+ *lemma* multiset.prod_map_div₀
- \+ *lemma* multiset.prod_map_inv'
- \+ *lemma* multiset.prod_map_inv₀
- \+/\- *lemma* multiset.prod_map_mul
- \+/\- *lemma* multiset.prod_map_one
- \+ *lemma* multiset.prod_map_pow
- \+ *lemma* multiset.prod_map_zpow
- \+ *lemma* multiset.prod_map_zpow₀

Modified src/algebra/group/prod.lean
- \+ *def* div_monoid_hom
- \+ *def* div_monoid_with_zero_hom
- \+ *def* mul_monoid_hom
- \+ *def* mul_monoid_with_zero_hom
- \+ *def* mul_mul_hom

Modified src/algebra/group_with_zero/basic.lean
- \+ *def* inv_monoid_with_zero_hom

Modified src/algebra/smul_with_zero.lean
- \+ *def* smul_monoid_with_zero_hom

Modified src/data/list/basic.lean
- \+ *lemma* list.foldl_hom₂
- \+ *lemma* list.foldr_hom₂

Modified src/data/list/big_operators.lean
- \+/\- *lemma* list.prod_hom_rel
- \+ *lemma* list.prod_hom₂

Modified src/group_theory/group_action/prod.lean
- \+ *def* smul_monoid_hom
- \+ *def* smul_mul_hom



## [2022-01-06 09:57:30](https://github.com/leanprover-community/mathlib/commit/c391512)
feat(topology/metric_space/kuratowski): make the Kuratowski embedding have codomain the "true" ℓ^∞(ℕ) ([#11280](https://github.com/leanprover-community/mathlib/pull/11280))
(Previously, we didn't have the "true" ℓ^∞(ℕ), so we used the space of bounded continuous functions on `ℕ` equipped with the discrete topology.)
#### Estimated changes
Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/kuratowski.lean
- \- *def* ℓ_infty_ℝ



## [2022-01-06 07:55:41](https://github.com/leanprover-community/mathlib/commit/f07f87e)
feat(ring_theory/power_series/basic): algebra, solving TODOs ([#11267](https://github.com/leanprover-community/mathlib/pull/11267))
`algebra (mv_polynomial σ R) (mv_power_series σ A)`
`algebra (mv_power_series σ R) (mv_power_series σ A)`
`algebra (polynomial R) (power_series A)`
`algebra (power_series R) (power_series A)`
`coe_to_mv_power_series.alg_hom`
`coe_to_power_series.alg_hom`
And API about the injectivity of coercions
#### Estimated changes
Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* mv_polynomial.algebra_map_apply
- \+/\- *lemma* mv_polynomial.coe_add
- \+ *lemma* mv_polynomial.coe_def
- \+ *lemma* mv_polynomial.coe_eq_one_iff
- \+ *lemma* mv_polynomial.coe_eq_zero_iff
- \+ *lemma* mv_polynomial.coe_inj
- \+ *lemma* mv_polynomial.coe_injective
- \+/\- *lemma* mv_polynomial.coe_mul
- \+ *def* mv_polynomial.coe_to_mv_power_series.alg_hom
- \+ *lemma* mv_polynomial.coe_to_mv_power_series.alg_hom_apply
- \+ *lemma* mv_polynomial.coe_to_mv_power_series.ring_hom_apply
- \+/\- *lemma* mv_polynomial.coeff_coe
- \+ *lemma* mv_power_series.algebra_map_apply''
- \+ *lemma* mv_power_series.algebra_map_apply'
- \+/\- *lemma* polynomial.coe_add
- \+ *lemma* polynomial.coe_def
- \+ *lemma* polynomial.coe_eq_one_iff
- \+ *lemma* polynomial.coe_eq_zero_iff
- \+ *lemma* polynomial.coe_inj
- \+ *lemma* polynomial.coe_injective
- \+/\- *lemma* polynomial.coe_mul
- \+ *def* polynomial.coe_to_power_series.alg_hom
- \+ *lemma* polynomial.coe_to_power_series.alg_hom_apply
- \+/\- *def* polynomial.coe_to_power_series.ring_hom
- \+ *lemma* polynomial.coe_to_power_series.ring_hom_apply
- \+/\- *lemma* polynomial.coeff_coe
- \+ *lemma* power_series.algebra_map_apply''
- \+ *lemma* power_series.algebra_map_apply'
- \+ *lemma* power_series.map_C
- \+ *lemma* power_series.map_X



## [2022-01-06 07:55:40](https://github.com/leanprover-community/mathlib/commit/6952172)
feat(data/nat/digits): digits_len ([#11187](https://github.com/leanprover-community/mathlib/pull/11187))
Via a new `data.nat.log` import.
Also unprivate `digits_eq_cons_digits_div`.
The file needs a refactor to make the names more mathlib-like,
otherwise I would have named it `length_digits`.
#### Estimated changes
Modified src/data/nat/digits.lean
- \+ *lemma* nat.digits_eq_cons_digits_div
- \+ *lemma* nat.digits_len



## [2022-01-06 07:05:28](https://github.com/leanprover-community/mathlib/commit/b3260f3)
feat(measure_theory/constructions/borel_space): new lemma tendsto_measure_cthickening ([#11009](https://github.com/leanprover-community/mathlib/pull/11009))
Prove that, when `r` tends to `0`, the measure of the `r`-thickening of a set `s` tends to the measure of `s`.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* tendsto_measure_cthickening
- \+ *lemma* tendsto_measure_cthickening_of_is_closed
- \+ *lemma* tendsto_measure_cthickening_of_is_compact

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.tendsto_measure_bInter_gt



## [2022-01-05 23:45:35](https://github.com/leanprover-community/mathlib/commit/9f28b5d)
chore(ci): update some workflows to use custom bot token ([#11274](https://github.com/leanprover-community/mathlib/pull/11274))
#### Estimated changes
Modified .github/workflows/add_label_from_review.yml


Modified .github/workflows/dependent-issues.yml


Modified .github/workflows/merge_conflicts.yml




## [2022-01-05 23:45:33](https://github.com/leanprover-community/mathlib/commit/e718965)
feat(topology/uniform_space/compact_convergence): when the domain is compact, compact convergence is just uniform convergence ([#11262](https://github.com/leanprover-community/mathlib/pull/11262))
#### Estimated changes
Modified src/topology/uniform_space/compact_convergence.lean
- \+ *lemma* continuous_map.has_basis_compact_convergence_uniformity_of_compact
- \+ *lemma* continuous_map.tendsto_iff_tendsto_uniformly



## [2022-01-05 23:45:32](https://github.com/leanprover-community/mathlib/commit/a7611b2)
chore(*): notation for `units` ([#11236](https://github.com/leanprover-community/mathlib/pull/11236))
#### Estimated changes
Modified counterexamples/direct_sum_is_internal.lean
- \+/\- *lemma* units_int.one_ne_neg_one
- \+/\- *def* with_sign

Modified src/algebra/algebra/basic.lean


Modified src/algebra/algebra/spectrum.lean
- \+/\- *lemma* spectrum.smul_mem_smul_iff
- \+/\- *theorem* spectrum.unit_mem_mul_iff_mem_swap_mul
- \+/\- *theorem* spectrum.unit_smul_eq_smul

Modified src/algebra/associated.lean
- \+/\- *def* associated
- \+/\- *theorem* associates.coe_unit_eq_one
- \+/\- *theorem* associates.units_eq_one
- \+/\- *theorem* unit_associated_one
- \+/\- *lemma* units_eq_one

Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* units.coe_prod

Modified src/algebra/divisibility.lean


Modified src/algebra/field/basic.lean
- \+/\- *lemma* ring_hom.map_units_inv

Modified src/algebra/gcd_monoid/basic.lean
- \+/\- *theorem* exists_eq_pow_of_mul_eq_pow
- \+/\- *theorem* lcm_units_coe_left
- \+/\- *theorem* lcm_units_coe_right
- \+/\- *lemma* normalize_coe_units

Modified src/algebra/group/commute.lean


Modified src/algebra/group/conj.lean
- \+/\- *def* is_conj

Modified src/algebra/group/opposite.lean
- \+/\- *lemma* units.coe_op_equiv_symm
- \+/\- *lemma* units.coe_unop_op_equiv
- \+/\- *def* units.op_equiv

Modified src/algebra/group/prod.lean
- \+/\- *def* embed_product
- \+/\- *def* mul_equiv.prod_units

Modified src/algebra/group/semiconj.lean
- \+/\- *theorem* semiconj_by.units_coe
- \+/\- *theorem* semiconj_by.units_coe_iff
- \+/\- *lemma* semiconj_by.units_inv_right
- \+/\- *lemma* semiconj_by.units_inv_right_iff
- \+/\- *lemma* semiconj_by.units_inv_symm_left
- \+/\- *lemma* semiconj_by.units_inv_symm_left_iff
- \+/\- *theorem* semiconj_by.units_of_coe
- \+/\- *lemma* units.mk_semiconj_by

Modified src/algebra/group/units.lean
- \+/\- *def* divp
- \+/\- *theorem* divp_assoc
- \+/\- *theorem* divp_divp_eq_divp_mul
- \+/\- *theorem* divp_eq_divp_iff
- \+/\- *theorem* divp_eq_iff_mul_eq
- \+/\- *theorem* divp_eq_one_iff_eq
- \+/\- *theorem* divp_inv
- \+/\- *theorem* divp_left_inj
- \+/\- *theorem* divp_mul_cancel
- \+/\- *theorem* divp_mul_divp
- \+/\- *theorem* divp_self
- \+/\- *def* is_unit
- \+/\- *theorem* mul_divp_cancel
- \+/\- *theorem* one_divp
- \+/\- *lemma* units.coe_eq_one
- \+/\- *lemma* units.coe_one
- \+/\- *def* units.copy
- \+/\- *lemma* units.copy_eq
- \+/\- *theorem* units.eq_iff
- \+/\- *theorem* units.ext_iff
- \+/\- *lemma* units.inv_eq_coe_inv
- \+/\- *lemma* units.inv_eq_of_mul_eq_one
- \+/\- *lemma* units.inv_mul_cancel_left
- \+/\- *lemma* units.inv_mul_cancel_right
- \+/\- *lemma* units.inv_mul_of_eq
- \+/\- *lemma* units.inv_unique
- \+/\- *theorem* units.is_unit_mul_units
- \+/\- *theorem* units.is_unit_units_mul
- \+/\- *theorem* units.mk_coe
- \+/\- *lemma* units.mul_inv_cancel_left
- \+/\- *lemma* units.mul_inv_cancel_right
- \+/\- *lemma* units.mul_inv_of_eq
- \+/\- *theorem* units.mul_left_inj
- \+/\- *theorem* units.mul_right_inj
- \+/\- *def* units.simps.coe
- \+/\- *def* units.simps.coe_inv

Modified src/algebra/group/units_hom.lean
- \+/\- *def* monoid_hom.to_hom_units
- \+/\- *def* units.coe_hom
- \+/\- *lemma* units.coe_hom_apply
- \+/\- *lemma* units.coe_lift_right
- \+/\- *lemma* units.coe_map
- \+/\- *lemma* units.coe_map_inv
- \+/\- *def* units.lift_right
- \+/\- *lemma* units.lift_right_inv_mul
- \+/\- *def* units.map
- \+/\- *lemma* units.map_id
- \+/\- *lemma* units.mul_lift_right_inv

Modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* commute.units_zpow_left
- \+/\- *lemma* commute.units_zpow_right
- \+/\- *lemma* int.units_pow_eq_pow_mod_two
- \+/\- *lemma* int.units_sq
- \+/\- *lemma* semiconj_by.units_zpow_right
- \+/\- *lemma* units.coe_pow
- \+/\- *lemma* units.coe_zpow
- \+/\- *lemma* units.conj_pow'
- \+/\- *lemma* units.conj_pow

Modified src/algebra/group_with_zero/basic.lean
- \+/\- *theorem* divp_eq_div
- \+/\- *lemma* ring.inverse_unit
- \+/\- *lemma* units.coe_inv'
- \+/\- *lemma* units.exists_iff_ne_zero
- \+/\- *lemma* units.inv_mul'
- \+/\- *def* units.mk0
- \+/\- *lemma* units.mk0_coe
- \+/\- *lemma* units.mul_inv'
- \+/\- *lemma* units.mul_left_eq_zero
- \+/\- *lemma* units.mul_right_eq_zero
- \+/\- *lemma* units.ne_zero

Modified src/algebra/group_with_zero/power.lean
- \+/\- *lemma* units.coe_zpow₀

Modified src/algebra/invertible.lean
- \+/\- *lemma* inv_of_units
- \+/\- *def* unit_of_invertible
- \+/\- *def* units.invertible

Modified src/algebra/lie/skew_adjoint.lean
- \+/\- *lemma* mem_skew_adjoint_matrices_lie_subalgebra_unit_smul

Modified src/algebra/module/basic.lean
- \+/\- *theorem* units.neg_smul

Modified src/algebra/module/linear_map.lean


Modified src/algebra/order/group.lean


Modified src/algebra/order/monoid.lean
- \+/\- *theorem* units.coe_le_coe
- \+/\- *theorem* units.coe_lt_coe
- \+/\- *theorem* units.max_coe
- \+/\- *theorem* units.min_coe

Modified src/algebra/order/ring.lean
- \+/\- *lemma* units.inv_neg
- \+/\- *lemma* units.inv_pos

Modified src/algebra/order/with_zero.lean
- \+/\- *lemma* units.zero_lt

Modified src/algebra/regular/basic.lean
- \+/\- *lemma* units.is_regular

Modified src/algebra/regular/smul.lean
- \+/\- *lemma* units.is_smul_regular

Modified src/algebra/ring/basic.lean
- \+/\- *lemma* units.inv_eq_self_iff

Modified src/algebra/star/basic.lean
- \+/\- *lemma* units.coe_star
- \+/\- *lemma* units.coe_star_inv

Modified src/algebraic_geometry/EllipticCurve.lean


Modified src/analysis/asymptotics/asymptotics.lean
- \+/\- *theorem* asymptotics.is_O_with.const_mul_right'
- \+/\- *theorem* asymptotics.is_O_with_self_const_mul'

Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* differentiable_at_inverse
- \+/\- *lemma* fderiv_inverse
- \+/\- *lemma* has_fderiv_at_ring_inverse

Modified src/analysis/calculus/times_cont_diff.lean
- \+/\- *lemma* times_cont_diff_at_ring_inverse

Modified src/analysis/normed_space/add_torsor_bases.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* units.norm_pos

Modified src/analysis/normed_space/int.lean
- \+/\- *lemma* int.nnnorm_coe_units
- \+/\- *lemma* int.norm_coe_units

Modified src/analysis/normed_space/units.lean
- \+/\- *lemma* normed_ring.inverse_add
- \+/\- *lemma* normed_ring.inverse_add_norm
- \+/\- *lemma* normed_ring.inverse_add_norm_diff_first_order
- \+/\- *lemma* normed_ring.inverse_add_norm_diff_nth_order
- \+/\- *lemma* normed_ring.inverse_add_norm_diff_second_order
- \+/\- *lemma* normed_ring.inverse_add_nth_order
- \+/\- *lemma* normed_ring.inverse_continuous_at
- \+/\- *def* units.add
- \+/\- *lemma* units.is_open_map_coe
- \+/\- *def* units.one_sub
- \+/\- *lemma* units.open_embedding_coe
- \+/\- *def* units.unit_of_nearby

Modified src/category_theory/endomorphism.lean
- \+/\- *def* category_theory.Aut.units_End_equiv_Aut

Modified src/category_theory/single_obj.lean
- \+/\- *def* units.to_Aut
- \+/\- *lemma* units.to_Aut_hom
- \+/\- *lemma* units.to_Aut_inv

Modified src/data/equiv/mul_add.lean
- \+/\- *def* to_units
- \+/\- *lemma* units.coe_inv
- \+/\- *def* units.map_equiv
- \+/\- *def* units.mul_left
- \+/\- *lemma* units.mul_left_bijective
- \+/\- *lemma* units.mul_left_symm
- \+/\- *def* units.mul_right
- \+/\- *lemma* units.mul_right_bijective
- \+/\- *lemma* units.mul_right_symm

Modified src/data/fintype/basic.lean
- \+/\- *lemma* fintype.card_units
- \+/\- *theorem* fintype.card_units_int
- \+/\- *def* units_equiv_ne_zero
- \+/\- *lemma* units_int.univ

Modified src/data/int/absolute_value.lean
- \+/\- *lemma* absolute_value.map_units_int
- \+/\- *lemma* absolute_value.map_units_int_cast
- \+/\- *lemma* absolute_value.map_units_int_smul

Modified src/data/int/basic.lean
- \+/\- *lemma* int.units_coe_mul_self
- \+/\- *theorem* int.units_eq_one_or
- \+/\- *lemma* int.units_inv_eq_self
- \+/\- *lemma* int.units_mul_self
- \+/\- *theorem* int.units_nat_abs

Modified src/data/matrix/rank.lean
- \+/\- *lemma* matrix.rank_unit

Modified src/data/nat/basic.lean
- \+/\- *theorem* nat.units_eq_one

Modified src/data/nat/totient.lean
- \+/\- *lemma* nat.card_units_zmod_lt_sub_one
- \+/\- *lemma* nat.prime_iff_card_units
- \+/\- *lemma* zmod.card_units_eq_totient

Modified src/data/polynomial/field_division.lean
- \+/\- *lemma* polynomial.coeff_inv_units

Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* polynomial.coeff_coe_units_zero_ne_zero
- \+/\- *lemma* polynomial.degree_coe_units
- \+/\- *lemma* polynomial.nat_degree_coe_units
- \+/\- *lemma* polynomial.units_coeff_zero_smul

Modified src/data/real/ennreal.lean


Modified src/data/real/nnreal.lean


Modified src/data/real/sign.lean


Modified src/data/zmod/basic.lean
- \+/\- *lemma* zmod.inv_coe_unit
- \+/\- *def* zmod.unit_of_coprime
- \+/\- *lemma* zmod.val_coe_unit_coprime

Modified src/deprecated/group.lean
- \+/\- *lemma* units.coe_is_monoid_hom
- \+/\- *lemma* units.coe_map'
- \+/\- *def* units.map'

Modified src/dynamics/circle/rotation_number/translation_number.lean
- \+/\- *lemma* circle_deg1_lift.coe_to_order_iso
- \+/\- *lemma* circle_deg1_lift.coe_to_order_iso_inv
- \+/\- *lemma* circle_deg1_lift.coe_to_order_iso_symm
- \+/\- *def* circle_deg1_lift.to_order_iso
- \+/\- *def* circle_deg1_lift.translate
- \+/\- *lemma* circle_deg1_lift.translation_number_conj_eq'
- \+/\- *lemma* circle_deg1_lift.translation_number_conj_eq
- \+/\- *lemma* circle_deg1_lift.translation_number_units_inv
- \+/\- *lemma* circle_deg1_lift.translation_number_zpow
- \+/\- *lemma* circle_deg1_lift.units_apply_inv_apply
- \+/\- *lemma* circle_deg1_lift.units_coe
- \+/\- *lemma* circle_deg1_lift.units_inv_apply_apply
- \+/\- *lemma* circle_deg1_lift.units_semiconj_of_translation_number_eq

Modified src/field_theory/finite/basic.lean
- \+/\- *lemma* finite_field.prod_univ_units_id_eq_neg_one
- \+/\- *lemma* finite_field.sum_pow_units
- \+/\- *lemma* zmod.card_units
- \+/\- *lemma* zmod.pow_totient
- \+/\- *theorem* zmod.units_pow_card_sub_one_eq_one

Modified src/field_theory/separable.lean
- \+/\- *lemma* polynomial.separable_X_pow_sub_C_unit

Modified src/field_theory/splitting_field.lean


Modified src/geometry/manifold/instances/units_of_normed_algebra.lean
- \+/\- *lemma* units.chart_at_apply
- \+/\- *lemma* units.chart_at_source

Modified src/group_theory/congruence.lean


Modified src/group_theory/group_action/units.lean
- \+/\- *lemma* units.smul_def

Modified src/group_theory/monoid_localization.lean


Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* order_of_units

Modified src/group_theory/perm/cycle_type.lean


Modified src/group_theory/perm/sign.lean
- \+/\- *lemma* equiv.perm.eq_sign_of_surjective_hom
- \+/\- *def* equiv.perm.sign
- \+/\- *def* equiv.perm.sign_aux2
- \+/\- *def* equiv.perm.sign_aux3
- \+/\- *def* equiv.perm.sign_aux
- \+/\- *lemma* equiv.perm.sign_surjective

Modified src/group_theory/specific_groups/quaternion.lean


Modified src/group_theory/submonoid/center.lean


Modified src/group_theory/submonoid/inverses.lean
- \+/\- *lemma* submonoid.unit_mem_left_inv

Modified src/linear_algebra/affine_space/affine_equiv.lean
- \+/\- *lemma* affine_equiv.coe_homothety_units_mul_hom_apply
- \+/\- *lemma* affine_equiv.coe_homothety_units_mul_hom_apply_symm
- \+/\- *def* affine_equiv.equiv_units_affine_map
- \+/\- *def* affine_equiv.homothety_units_mul_hom

Modified src/linear_algebra/basic.lean
- \+/\- *def* linear_equiv.smul_of_unit
- \+/\- *def* linear_map.general_linear_group

Modified src/linear_algebra/basis.lean
- \+/\- *def* basis.units_smul
- \+/\- *lemma* basis.units_smul_apply

Modified src/linear_algebra/determinant.lean
- \+/\- *lemma* basis.det_units_smul

Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/general_linear_group.lean
- \+/\- *def* matrix.general_linear_group.det

Modified src/linear_algebra/linear_independent.lean


Modified src/linear_algebra/matrix/basis.lean
- \+/\- *lemma* basis.to_matrix_units_smul

Modified src/linear_algebra/matrix/determinant.lean
- \+/\- *lemma* matrix.det_units_conj'
- \+/\- *lemma* matrix.det_units_conj

Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+/\- *lemma* matrix.inv_smul'
- \+/\- *def* matrix.unit_of_det_invertible

Modified src/linear_algebra/matrix/zpow.lean
- \+/\- *lemma* matrix.units.coe_inv''
- \+/\- *lemma* matrix.units.coe_zpow

Modified src/linear_algebra/orientation.lean
- \+/\- *lemma* module.ray.units_smul_of_neg
- \+/\- *lemma* module.ray.units_smul_of_pos
- \+/\- *lemma* units_inv_smul
- \+/\- *lemma* units_smul_eq_neg_iff
- \+/\- *lemma* units_smul_eq_self_iff

Modified src/linear_algebra/quadratic_form/basic.lean


Modified src/linear_algebra/quadratic_form/real.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/linear_algebra/trace.lean
- \+/\- *theorem* linear_map.trace_conj

Modified src/measure_theory/group/arithmetic.lean


Modified src/number_theory/arithmetic_function.lean
- \+/\- *def* nat.arithmetic_function.zeta_unit

Modified src/number_theory/lucas_lehmer.lean
- \+/\- *lemma* lucas_lehmer.X.units_card

Modified src/number_theory/lucas_primality.lean


Modified src/number_theory/padics/padic_integers.lean
- \+/\- *def* padic_int.mk_units
- \+/\- *lemma* padic_int.norm_units
- \+/\- *def* padic_int.unit_coeff

Modified src/number_theory/quadratic_reciprocity.lean
- \+/\- *lemma* zmod.euler_criterion_units

Modified src/ring_theory/class_group.lean
- \+/\- *def* class_group
- \+/\- *lemma* coe_to_principal_ideal
- \+/\- *def* to_principal_ideal
- \+/\- *lemma* to_principal_ideal_eq_iff

Modified src/ring_theory/discrete_valuation_ring.lean
- \+/\- *lemma* discrete_valuation_ring.add_val_def'
- \+/\- *lemma* discrete_valuation_ring.add_val_def
- \+/\- *lemma* discrete_valuation_ring.unit_mul_pow_congr_unit

Modified src/ring_theory/fintype.lean


Modified src/ring_theory/fractional_ideal.lean
- \+/\- *lemma* fractional_ideal.fg_unit

Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/multiplicity.lean
- \+/\- *lemma* multiplicity.unit_left
- \+/\- *lemma* multiplicity.unit_right

Modified src/ring_theory/power_series/basic.lean
- \+/\- *lemma* mv_power_series.coeff_inv_of_unit
- \+/\- *lemma* mv_power_series.constant_coeff_inv_of_unit
- \+/\- *def* mv_power_series.inv_of_unit
- \+/\- *lemma* mv_power_series.mul_inv_of_unit
- \+/\- *lemma* power_series.coeff_inv_of_unit
- \+/\- *lemma* power_series.constant_coeff_inv_of_unit
- \+/\- *def* power_series.inv_of_unit
- \+/\- *lemma* power_series.mul_inv_of_unit

Modified src/ring_theory/power_series/well_known.lean
- \+/\- *lemma* power_series.coeff_inv_units_sub
- \+/\- *lemma* power_series.constant_coeff_inv_units_sub
- \+/\- *def* power_series.inv_units_sub
- \+/\- *lemma* power_series.inv_units_sub_mul_X
- \+/\- *lemma* power_series.inv_units_sub_mul_sub
- \+/\- *lemma* power_series.map_inv_units_sub

Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/roots_of_unity.lean
- \+/\- *lemma* is_primitive_root.coe_units_iff
- \+/\- *lemma* is_primitive_root.eq_pow_of_mem_roots_of_unity
- \+/\- *lemma* is_primitive_root.is_primitive_root_iff'
- \+/\- *lemma* is_primitive_root.zpowers_eq
- \+/\- *lemma* map_roots_of_unity
- \+/\- *lemma* mem_roots_of_unity
- \+/\- *lemma* mem_roots_of_unity_iff_mem_nth_roots
- \+/\- *def* roots_of_unity

Modified src/ring_theory/subring/basic.lean


Modified src/ring_theory/subsemiring/basic.lean
- \+/\- *lemma* mem_pos_monoid

Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/valuation/basic.lean
- \+/\- *lemma* add_valuation.map_units_inv
- \+/\- *def* valuation.lt_add_subgroup
- \+/\- *lemma* valuation.map_units_inv
- \+/\- *theorem* valuation.unit_map_eq

Modified src/ring_theory/valuation/integers.lean


Modified src/topology/algebra/field.lean
- \+/\- *lemma* topological_division_ring.continuous_units_inv
- \+/\- *lemma* topological_division_ring.units_top_group
- \+/\- *lemma* topological_ring.induced_units.continuous_coe
- \+/\- *def* topological_ring.topological_space_units

Modified src/topology/algebra/group.lean
- \+/\- *def* units.homeomorph.prod_units

Modified src/topology/algebra/module/basic.lean
- \+/\- *def* continuous_linear_equiv.of_unit
- \+/\- *def* continuous_linear_equiv.to_unit
- \+/\- *def* continuous_linear_equiv.units_equiv
- \+/\- *lemma* continuous_linear_equiv.units_equiv_apply
- \+/\- *def* continuous_linear_equiv.units_equiv_aut
- \+/\- *lemma* continuous_linear_equiv.units_equiv_aut_apply
- \+/\- *lemma* continuous_linear_equiv.units_equiv_aut_apply_symm

Modified src/topology/algebra/monoid.lean
- \+/\- *lemma* units.continuous_coe

Modified src/topology/algebra/mul_action.lean


Modified src/topology/algebra/valuation.lean
- \+/\- *lemma* valued.subgroups_basis

Modified src/topology/algebra/valued_field.lean
- \+/\- *lemma* valuation.inversion_estimate

Modified src/topology/algebra/with_zero_topology.lean
- \+/\- *lemma* linear_ordered_comm_group_with_zero.directed_lt
- \+/\- *lemma* linear_ordered_comm_group_with_zero.has_basis_nhds_units
- \+/\- *lemma* linear_ordered_comm_group_with_zero.nhds_coe_units
- \+/\- *lemma* linear_ordered_comm_group_with_zero.nhds_zero_of_units
- \+/\- *lemma* linear_ordered_comm_group_with_zero.singleton_nhds_of_units
- \+/\- *lemma* linear_ordered_comm_group_with_zero.tendsto_units

Modified test/instance_diamonds.lean




## [2022-01-05 23:45:31](https://github.com/leanprover-community/mathlib/commit/cac4e19)
feat(set_theory/ordinal_arithmetic): Proved characterization of `log` ([#11192](https://github.com/leanprover-community/mathlib/pull/11192))
As well as a few simple missing lemmas.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.le_mul_left
- \+ *theorem* ordinal.le_mul_right
- \+ *theorem* ordinal.log_one
- \+ *theorem* ordinal.log_power
- \+ *theorem* ordinal.log_power_mul_add
- \+ *theorem* ordinal.lt_one_iff_zero
- \+ *lemma* ordinal.power_mul_add_lt_power_mul_succ
- \+ *lemma* ordinal.power_mul_add_lt_power_succ
- \+ *lemma* ordinal.power_mul_add_pos



## [2022-01-05 23:45:29](https://github.com/leanprover-community/mathlib/commit/b67857e)
refactor(set_theory/ordinal_arithmetic): Reworked `sup` and `bsup` API ([#11048](https://github.com/leanprover-community/mathlib/pull/11048))
This PR does two things:
- It reworks and matches, for the most part, the API for `ordinal.sup` and `ordinal.bsup`.
- It introduces `ordinal.lsub` and `ordinal.blsub` for (bounded) least strict upper bounds, and proves the expected results.
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+ *theorem* ordinal.succ_ne_self
- \+ *theorem* ordinal.typein_lt_self
- \+/\- *theorem* ordinal.typein_lt_type

Modified src/set_theory/ordinal_arithmetic.lean
- \+ *def* ordinal.blsub
- \+ *theorem* ordinal.blsub_eq_lsub
- \+ *theorem* ordinal.blsub_id
- \+ *theorem* ordinal.blsub_le_bsup_succ
- \+ *theorem* ordinal.blsub_le_iff_lt
- \+ *theorem* ordinal.blsub_type
- \+ *theorem* ordinal.bsup_eq_blsub
- \+ *theorem* ordinal.bsup_eq_sup
- \+ *theorem* ordinal.bsup_le_blsub
- \+ *theorem* ordinal.bsup_not_succ_of_ne_bsup
- \+ *theorem* ordinal.bsup_succ_eq_blsub
- \+ *theorem* ordinal.bsup_succ_le_blsub
- \+/\- *theorem* ordinal.is_normal.bsup
- \+ *def* ordinal.lsub
- \+ *theorem* ordinal.lsub_eq_blsub
- \+ *theorem* ordinal.lsub_le_iff_lt
- \+ *theorem* ordinal.lsub_le_sup_succ
- \+ *theorem* ordinal.lt_blsub
- \+/\- *theorem* ordinal.lt_bsup
- \+ *theorem* ordinal.lt_bsup_of_limit
- \+ *theorem* ordinal.lt_bsup_of_ne_bsup
- \+ *theorem* ordinal.lt_lsub
- \+ *theorem* ordinal.lt_sup_of_ne_sup
- \+ *theorem* ordinal.sup_eq_bsup
- \+ *theorem* ordinal.sup_eq_lsub
- \+ *theorem* ordinal.sup_le_lsub
- \+ *theorem* ordinal.sup_not_succ_of_ne_sup
- \- *lemma* ordinal.sup_succ
- \+ *theorem* ordinal.sup_succ_eq_lsub
- \+ *theorem* ordinal.sup_succ_le_lsub



## [2022-01-05 22:31:56](https://github.com/leanprover-community/mathlib/commit/771d144)
feat(analysis/normed_space/lp_space): completeness of the lp space on `Π i, E i` ([#11094](https://github.com/leanprover-community/mathlib/pull/11094))
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *lemma* normed_group.uniformity_basis_dist

Modified src/analysis/normed/group/pointwise.lean
- \+ *lemma* metric.bounded.exists_pos_norm_le

Modified src/analysis/normed_space/lp_space.lean
- \+ *lemma* lp.mem_ℓp_of_tendsto
- \+ *lemma* lp.norm_apply_le_norm
- \+ *lemma* lp.norm_apply_le_of_tendsto
- \+ *lemma* lp.norm_le_of_forall_le'
- \+ *lemma* lp.norm_le_of_forall_le
- \+ *lemma* lp.norm_le_of_forall_sum_le
- \+ *lemma* lp.norm_le_of_tendsto
- \+ *lemma* lp.norm_le_of_tsum_le
- \+ *lemma* lp.sum_rpow_le_norm_rpow
- \+ *lemma* lp.sum_rpow_le_of_tendsto
- \+ *lemma* lp.tendsto_lp_of_tendsto_pi
- \+ *lemma* lp.uniform_continuous_coe
- \+ *lemma* mem_ℓp_gen'
- \+/\- *lemma* mem_ℓp_gen

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.eventually_at_bot_curry
- \+ *lemma* filter.eventually_at_top_curry

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* finite_of_summable_const

Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy_seq.eventually_eventually



## [2022-01-05 19:08:16](https://github.com/leanprover-community/mathlib/commit/8b2d181)
feat(ring_theory/laurent_series): laurent_series is_fraction_ring over power_series ([#11220](https://github.com/leanprover-community/mathlib/pull/11220))
#### Estimated changes
Modified src/ring_theory/laurent_series.lean


Modified src/ring_theory/localization.lean
- \+ *lemma* is_localization.of_le

Modified src/ring_theory/non_zero_divisors.lean
- \+ *lemma* is_unit_of_mem_non_zero_divisors

Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* power_series.X_ne_zero



## [2022-01-05 17:28:18](https://github.com/leanprover-community/mathlib/commit/f6dfea6)
feat(measure_theory/integral): Cauchy integral formula for a circle ([#10000](https://github.com/leanprover-community/mathlib/pull/10000))
#### Estimated changes
Modified src/analysis/box_integral/box/basic.lean
- \+ *lemma* box_integral.box.Ioo_subset_coe
- \+ *lemma* box_integral.box.Union_Ioo_of_tendsto
- \+ *lemma* box_integral.box.exists_seq_mono_tendsto
- \+/\- *def* box_integral.box.face
- \+ *lemma* box_integral.box.monotone_face

Modified src/analysis/box_integral/partition/measure.lean
- \+ *lemma* box_integral.box.Ioo_ae_eq_Icc
- \+ *lemma* box_integral.box.coe_ae_eq_Icc
- \+/\- *lemma* box_integral.box.measurable_set_Icc
- \+ *lemma* box_integral.box.measurable_set_Ioo
- \+/\- *lemma* box_integral.box.measurable_set_coe
- \+/\- *lemma* box_integral.box.measure_Icc_lt_top
- \+/\- *lemma* box_integral.box.measure_coe_lt_top

Added src/analysis/complex/cauchy_integral.lean
- \+ *lemma* complex.circle_integral_div_sub_of_differentiable_on_off_countable
- \+ *lemma* complex.circle_integral_eq_zero_of_differentiable_on_off_countable
- \+ *lemma* complex.circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
- \+ *lemma* complex.circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable
- \+ *lemma* complex.circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
- \+ *lemma* complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable
- \+ *lemma* complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable_aux
- \+ *lemma* complex.has_fpower_series_on_ball_of_differentiable_off_countable
- \+ *lemma* complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
- \+ *lemma* complex.integral_boundary_rect_of_has_fderiv_within_at_real_off_countable
- \+ *lemma* complex.two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable

Modified src/measure_theory/constructions/pi.lean
- \+ *lemma* measure_theory.measure.pi_Ioo_ae_eq_pi_Ioc

Modified src/measure_theory/integral/divergence_theorem.lean
- \+ *lemma* measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable_aux₁
- \+ *lemma* measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable_aux₂

Modified src/topology/separation.lean
- \+ *lemma* tendsto_nhds_unique_of_frequently_eq



## [2022-01-05 16:16:53](https://github.com/leanprover-community/mathlib/commit/6bf9041)
doc(analysis/normed/group/basic): show notation in the typeclass docstring ([#11260](https://github.com/leanprover-community/mathlib/pull/11260))
#### Estimated changes
Modified src/analysis/normed/group/basic.lean




## [2022-01-05 16:16:51](https://github.com/leanprover-community/mathlib/commit/3ab1c1c)
feat(algebra/polynomial/big_operators): lemmas about polynomial degree of products ([#11258](https://github.com/leanprover-community/mathlib/pull/11258))
These already existed for `nat_degree` but `degree` versions seemed missing.
from flt-regular
#### Estimated changes
Modified src/algebra/polynomial/big_operators.lean
- \+ *lemma* polynomial.degree_list_prod_le
- \+ *lemma* polynomial.degree_multiset_prod_le
- \+ *lemma* polynomial.degree_prod_le



## [2022-01-05 16:16:50](https://github.com/leanprover-community/mathlib/commit/a1f4ac3)
chore(topology): move 3 files to `topology/algebra/module/` ([#11242](https://github.com/leanprover-community/mathlib/pull/11242))
#### Estimated changes
Modified src/analysis/normed_space/banach_steinhaus.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/linear_isometry.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/weak_dual.lean


Modified src/measure_theory/measure/finite_measure_weak_convergence.lean


Modified src/topology/algebra/algebra.lean


Modified src/topology/algebra/continuous_affine_map.lean


Modified src/topology/algebra/filter_basis.lean


Renamed src/topology/algebra/module.lean to src/topology/algebra/module/basic.lean


Renamed src/topology/algebra/multilinear.lean to src/topology/algebra/module/multilinear.lean


Renamed src/topology/algebra/weak_dual_topology.lean to src/topology/algebra/module/weak_dual.lean


Modified src/topology/continuous_function/algebra.lean


Modified src/topology/instances/real_vector_space.lean


Modified src/topology/vector_bundle.lean




## [2022-01-05 14:15:46](https://github.com/leanprover-community/mathlib/commit/9fd7a02)
feat(category_theory/sites/left_exact): Sheafification is left exact. ([#11252](https://github.com/leanprover-community/mathlib/pull/11252))
#### Estimated changes
Added src/category_theory/sites/left_exact.lean
- \+ *def* category_theory.grothendieck_topology.cone_comp_evaluation_of_cone_comp_diagram_functor_comp_evaluation
- \+ *abbreviation* category_theory.grothendieck_topology.lift_to_diagram_limit_obj
- \+ *def* category_theory.grothendieck_topology.lift_to_plus_obj_limit_obj
- \+ *lemma* category_theory.grothendieck_topology.lift_to_plus_obj_limit_obj_fac



## [2022-01-05 14:15:44](https://github.com/leanprover-community/mathlib/commit/a580727)
chore(topology/omega_complete_partial_order): golf ([#11250](https://github.com/leanprover-community/mathlib/pull/11250))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.set_of_bijective

Modified src/order/omega_complete_partial_order.lean
- \+ *lemma* complete_lattice.inf_continuous'

Modified src/topology/omega_complete_partial_order.lean
- \+/\- *theorem* Scott.is_open_sUnion



## [2022-01-05 14:15:40](https://github.com/leanprover-community/mathlib/commit/802f23c)
feat(data/fintype/basic): `set_fintype_card_eq_univ_iff` ([#11244](https://github.com/leanprover-community/mathlib/pull/11244))
Adds companion lemma to `set_fintype_card_le_univ`. This PR also moves several `set.to_finset` lemmas earlier in the file.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+/\- *lemma* set.to_finset_empty
- \+/\- *lemma* set.to_finset_eq_empty_iff
- \+/\- *def* set_fintype
- \+ *lemma* set_fintype_card_eq_univ_iff
- \+/\- *lemma* set_fintype_card_le_univ



## [2022-01-05 14:15:39](https://github.com/leanprover-community/mathlib/commit/b27e33a)
feat(data/{fin/vec_notation, matrix/notation}): `cons_{add,sub,dot_product}_cons` ([#11241](https://github.com/leanprover-community/mathlib/pull/11241))
While these can be proved by `simp`, they are not rejected by the simp linter.
#### Estimated changes
Modified src/data/fin/vec_notation.lean
- \+ *lemma* matrix.cons_add_cons
- \+ *lemma* matrix.cons_sub_cons

Modified src/data/matrix/notation.lean
- \+ *lemma* matrix.cons_dot_product_cons



## [2022-01-05 14:15:38](https://github.com/leanprover-community/mathlib/commit/98b64f4)
feat(linear_algebra/orientation): bases from orientations ([#11234](https://github.com/leanprover-community/mathlib/pull/11234))
Add a lemma giving the orientation of a basis constructed with
`units_smul`, and thus definitions and lemmas to construct a basis
from an orientation.
#### Estimated changes
Modified src/linear_algebra/orientation.lean
- \+ *def* basis.adjust_to_orientation
- \+ *lemma* basis.adjust_to_orientation_apply_eq_or_eq_neg
- \+ *lemma* basis.orientation_adjust_to_orientation
- \+ *lemma* basis.orientation_neg_single
- \+ *lemma* basis.orientation_units_smul
- \+ *def* orientation.some_basis
- \+ *lemma* orientation.some_basis_orientation



## [2022-01-05 14:15:37](https://github.com/leanprover-community/mathlib/commit/33b5d26)
feat(analysis/complex): `re`, `im`, and `closure`/`interior`/`frontier` ([#11215](https://github.com/leanprover-community/mathlib/pull/11215))
#### Estimated changes
Modified src/analysis/complex/basic.lean


Added src/analysis/complex/re_im_topology.lean
- \+ *lemma* complex.closure_preimage_im
- \+ *lemma* complex.closure_preimage_re
- \+ *lemma* complex.closure_preimage_re_inter_preimage_im
- \+ *lemma* complex.closure_set_of_im_lt
- \+ *lemma* complex.closure_set_of_lt_im
- \+ *lemma* complex.closure_set_of_lt_re
- \+ *lemma* complex.closure_set_of_re_lt
- \+ *lemma* complex.frontier_preimage_im
- \+ *lemma* complex.frontier_preimage_re
- \+ *lemma* complex.frontier_preimage_re_inter_preimage_im
- \+ *lemma* complex.frontier_set_of_im_le
- \+ *lemma* complex.frontier_set_of_im_lt
- \+ *lemma* complex.frontier_set_of_le_im
- \+ *lemma* complex.frontier_set_of_le_re
- \+ *lemma* complex.frontier_set_of_le_re_and_im_le
- \+ *lemma* complex.frontier_set_of_le_re_and_le_im
- \+ *lemma* complex.frontier_set_of_lt_im
- \+ *lemma* complex.frontier_set_of_lt_re
- \+ *lemma* complex.frontier_set_of_re_le
- \+ *lemma* complex.frontier_set_of_re_lt
- \+ *lemma* complex.interior_preimage_im
- \+ *lemma* complex.interior_preimage_re
- \+ *lemma* complex.interior_preimage_re_inter_preimage_im
- \+ *lemma* complex.interior_set_of_im_le
- \+ *lemma* complex.interior_set_of_le_im
- \+ *lemma* complex.interior_set_of_le_re
- \+ *lemma* complex.interior_set_of_re_le
- \+ *lemma* complex.is_open_map_im
- \+ *lemma* complex.is_open_map_re
- \+ *lemma* complex.is_topological_fiber_bundle_im
- \+ *lemma* complex.is_topological_fiber_bundle_re
- \+ *lemma* complex.is_trivial_topological_fiber_bundle_im
- \+ *lemma* complex.is_trivial_topological_fiber_bundle_re
- \+ *lemma* complex.quotient_map_im
- \+ *lemma* complex.quotient_map_re

Modified src/data/complex/basic.lean
- \+/\- *def* complex.equiv_real_prod
- \- *theorem* complex.equiv_real_prod_apply
- \- *theorem* complex.equiv_real_prod_symm_im
- \- *theorem* complex.equiv_real_prod_symm_re

Modified src/topology/homeomorph.lean
- \+ *lemma* homeomorph.preimage_frontier



## [2022-01-05 14:15:35](https://github.com/leanprover-community/mathlib/commit/3115ced)
feat(ring_theory/non_zero_divisors): mul_{left,right}_cancel API ([#11211](https://github.com/leanprover-community/mathlib/pull/11211))
Not all `monoid_with_zero` are `cancel_monoid_with_zero`,
so we can't use `mul_right_cancel₀` everywhere. However, by definition,
multiplication by non-zero-divisors is 0 iff the multiplicand is 0.
In the context of a ring, that allows us to `mul_cancel_right`
#### Estimated changes
Modified src/ring_theory/non_zero_divisors.lean
- \+ *lemma* mem_non_zero_divisors_iff
- \+ *lemma* mul_cancel_left_coe_non_zero_divisor
- \+ *lemma* mul_cancel_left_mem_non_zero_divisor
- \+ *lemma* mul_cancel_right_coe_non_zero_divisor
- \+ *lemma* mul_cancel_right_mem_non_zero_divisor
- \+ *lemma* mul_left_coe_non_zero_divisors_eq_zero_iff
- \+ *lemma* mul_left_mem_non_zero_divisors_eq_zero_iff
- \+ *lemma* mul_right_coe_non_zero_divisors_eq_zero_iff
- \+ *lemma* mul_right_mem_non_zero_divisors_eq_zero_iff



## [2022-01-05 14:15:34](https://github.com/leanprover-community/mathlib/commit/3bd2044)
chore(data/nat/prime): reuse a result from algebra.big_operators.associated ([#11143](https://github.com/leanprover-community/mathlib/pull/11143))
#### Estimated changes
Modified src/algebra/big_operators/associated.lean
- \- *lemma* nat.prime.dvd_finset_prod_iff
- \- *lemma* nat.prime.dvd_finsupp_prod_iff
- \- *lemma* prime.dvd_prod_iff

Added src/data/list/prime.lean
- \+ *lemma* mem_list_primes_of_dvd_prod
- \+ *lemma* perm_of_prod_eq_prod
- \+ *lemma* prime.dvd_prod_iff
- \+ *lemma* prime.not_dvd_prod
- \+ *lemma* prime_dvd_prime_iff_eq

Modified src/data/nat/prime.lean
- \- *lemma* nat.mem_list_primes_of_dvd_prod
- \- *lemma* nat.perm_of_prod_eq_prod
- \- *lemma* nat.prime.dvd_prod_iff
- \- *lemma* nat.prime.not_dvd_prod



## [2022-01-05 14:15:33](https://github.com/leanprover-community/mathlib/commit/57a9f8b)
chore(group_theory/sub{monoid,group}, linear_algebra/basic): rename equivalences to mapped subobjects ([#11075](https://github.com/leanprover-community/mathlib/pull/11075))
This makes the names shorter and more uniform:
* `add_equiv.map_add_submonoid`
* `add_equiv.map_add_subgroup`
* `linear_equiv.map_submodule`
#### Estimated changes
Modified src/algebra/lie/subalgebra.lean
- \+ *def* lie_equiv.lie_subalgebra_map
- \+ *lemma* lie_equiv.lie_subalgebra_map_apply
- \- *def* lie_equiv.of_subalgebra
- \- *lemma* lie_equiv.of_subalgebra_apply

Modified src/group_theory/group_action/basic.lean


Modified src/group_theory/subgroup/basic.lean
- \- *def* mul_equiv.subgroup_equiv_map
- \+ *def* mul_equiv.subgroup_map

Modified src/group_theory/subgroup/pointwise.lean


Modified src/group_theory/submonoid/operations.lean
- \- *def* mul_equiv.submonoid_equiv_map
- \+ *def* mul_equiv.submonoid_map

Modified src/linear_algebra/basic.lean
- \- *def* linear_equiv.of_submodule
- \- *lemma* linear_equiv.of_submodule_apply
- \- *lemma* linear_equiv.of_submodule_symm_apply
- \+ *def* linear_equiv.submodule_map
- \+ *lemma* linear_equiv.submodule_map_apply
- \+ *lemma* linear_equiv.submodule_map_symm_apply

Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finite_dimensional.lean




## [2022-01-05 14:15:32](https://github.com/leanprover-community/mathlib/commit/7e5eebd)
feat(linear_algebra/clifford_algebra/equivs): There is a clifford algebra isomorphic to the dual numbers ([#10730](https://github.com/leanprover-community/mathlib/pull/10730))
This adds a brief file on the dual numbers, and then shows that they are equivalent to the clifford algebra with `Q = (0 : quadratic_form R R)`.
#### Estimated changes
Added src/algebra/dual_number.lean
- \+ *lemma* dual_number.alg_hom_ext
- \+ *def* dual_number.eps
- \+ *lemma* dual_number.eps_mul_eps
- \+ *lemma* dual_number.fst_eps
- \+ *lemma* dual_number.inr_eq_smul_eps
- \+ *def* dual_number.lift
- \+ *lemma* dual_number.lift_apply_eps
- \+ *lemma* dual_number.lift_eps
- \+ *lemma* dual_number.snd_eps
- \+ *lemma* dual_number.snd_mul
- \+ *abbreviation* dual_number

Modified src/linear_algebra/clifford_algebra/equivs.lean
- \+ *lemma* clifford_algebra_dual_number.equiv_symm_eps
- \+ *lemma* clifford_algebra_dual_number.equiv_ι
- \+ *lemma* clifford_algebra_dual_number.ι_mul_ι



## [2022-01-05 12:21:49](https://github.com/leanprover-community/mathlib/commit/cef3258)
chore(group_theory/group_action/defs): add instances to copy statements about left actions to right actions when the two are equal ([#10949](https://github.com/leanprover-community/mathlib/pull/10949))
While these instances are usually available elsewhere, these shortcuts can reduce the number of typeclass assumptions other lemmas needs.
Since the instances carry no data, the only harm they can cause is performance.
There were some typeclass loops brought on by some bad instance unification, similar to the ones removed by @Vierkantor in 9ee2a50aa439d092c8dea16c1f82f7f8e1f1ea2c. We turn these into `lemma`s and  duplicate the docstring explaining the problem. That commit has a much longer explanation of the problem.
#### Estimated changes
Modified src/group_theory/group_action/defs.lean
- \+ *lemma* has_scalar.comp.smul_comm_class'
- \+ *lemma* has_scalar.comp.smul_comm_class



## [2022-01-05 11:32:02](https://github.com/leanprover-community/mathlib/commit/8d5830e)
chore(measure_theory/measurable_space): use implicit measurable_space argument ([#11230](https://github.com/leanprover-community/mathlib/pull/11230))
The `measurable_space` argument is inferred from other arguments (like `measurable f` or a measure for example) instead of being a type class. This ensures that the lemmas are usable without `@` when several measurable space structures are used for the same type.
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean


Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable.indicator
- \+/\- *lemma* measurable.ite
- \+/\- *lemma* measurable.piecewise
- \+/\- *lemma* measurable_from_top
- \+/\- *lemma* measurable_fst
- \+/\- *lemma* measurable_inl
- \+/\- *lemma* measurable_inr
- \+/\- *lemma* measurable_of_subsingleton_codomain
- \+/\- *lemma* measurable_prod
- \+/\- *lemma* measurable_set.exists_measurable_proj
- \+/\- *lemma* measurable_set_preimage
- \+/\- *lemma* measurable_set_range_inl
- \+/\- *lemma* measurable_set_range_inr
- \+/\- *lemma* measurable_snd
- \+/\- *lemma* measurable_swap
- \+/\- *lemma* measurable_swap_iff
- \+/\- *lemma* measurable_to_encodable
- \+/\- *lemma* measurable_unit
- \+/\- *lemma* subsingleton.measurable

Modified src/measure_theory/measurable_space_def.lean
- \+/\- *lemma* measurable.comp
- \+/\- *lemma* measurable_set.empty
- \+/\- *def* measurable_set

Modified src/probability_theory/stopping.lean




## [2022-01-05 08:10:47](https://github.com/leanprover-community/mathlib/commit/4912740)
chore(analysis/inner_product_space/basic): extract common `variables` ([#11214](https://github.com/leanprover-community/mathlib/pull/11214))
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+/\- *lemma* direct_sum.submodule_is_internal.collected_basis_orthonormal
- \+/\- *lemma* orthogonal_family.comp
- \+/\- *lemma* orthogonal_family.eq_ite
- \+/\- *lemma* orthogonal_family.independent
- \+/\- *lemma* orthogonal_family.inner_right_dfinsupp
- \+/\- *lemma* orthogonal_family.inner_right_fintype
- \+/\- *lemma* orthogonal_family.orthonormal_sigma_orthonormal



## [2022-01-05 08:10:46](https://github.com/leanprover-community/mathlib/commit/b72d2ab)
feat(algebra/ring/basic): Introduce non-unital, non-associative rings ([#11124](https://github.com/leanprover-community/mathlib/pull/11124))
Adds the class `non_unital_non_assoc_ring` to `algebra.ring.basic` to represent rings which are not assumed to be unital or associative and shows that (unital, associative) rings are instances of `non_unital_non_assoc_ring`.
Needed by [#11073](https://github.com/leanprover-community/mathlib/pull/11073).
#### Estimated changes
Modified src/algebra/ring/basic.lean


Modified src/algebra/ring/opposite.lean


Modified src/algebra/ring/pi.lean


Modified src/algebra/ring/prod.lean


Modified src/algebra/ring/ulift.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/data/finsupp/pointwise.lean




## [2022-01-05 06:18:07](https://github.com/leanprover-community/mathlib/commit/58b1429)
chore(algebra/group/pi): `pow_apply` can be `rfl` ([#11249](https://github.com/leanprover-community/mathlib/pull/11249))
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+/\- *lemma* pi.pow_apply



## [2022-01-05 01:44:24](https://github.com/leanprover-community/mathlib/commit/4093834)
feat(measure_theory/measure/finite_measure_weak_convergence): add definition and lemmas of pairing measures with nonnegative continuous test functions. ([#9430](https://github.com/leanprover-community/mathlib/pull/9430))
Add definition and lemmas about pairing of `finite_measure`s and `probability_measure`s with nonnegative continuous test functions. These pairings will be used in the definition of the topology of weak convergence (convergence in distribution): the topology will be defined as an induced topology based on them.
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* is_finite_measure.lintegral_lt_top_of_bounded_to_ennreal

Modified src/measure_theory/measure/finite_measure_weak_convergence.lean
- \+ *lemma* bounded_continuous_function.nnreal.to_ennreal_comp_measurable
- \+ *lemma* measure_theory.finite_measure.lintegral_lt_top_of_bounded_continuous_to_nnreal
- \+ *def* measure_theory.finite_measure.test_against_nn
- \+ *lemma* measure_theory.finite_measure.test_against_nn_add
- \+ *lemma* measure_theory.finite_measure.test_against_nn_coe_eq
- \+ *lemma* measure_theory.finite_measure.test_against_nn_const
- \+ *lemma* measure_theory.finite_measure.test_against_nn_lipschitz
- \+ *lemma* measure_theory.finite_measure.test_against_nn_lipschitz_estimate
- \+ *lemma* measure_theory.finite_measure.test_against_nn_mono
- \+ *lemma* measure_theory.finite_measure.test_against_nn_smul
- \+ *def* measure_theory.finite_measure.to_weak_dual_bounded_continuous_nnreal
- \+ *lemma* measure_theory.probability_measure.lintegral_lt_top_of_bounded_continuous_to_nnreal
- \+ *def* measure_theory.probability_measure.test_against_nn
- \+ *lemma* measure_theory.probability_measure.test_against_nn_coe_eq
- \+ *lemma* measure_theory.probability_measure.test_against_nn_const
- \+ *lemma* measure_theory.probability_measure.test_against_nn_lipschitz
- \+ *lemma* measure_theory.probability_measure.test_against_nn_mono
- \+ *lemma* measure_theory.probability_measure.to_finite_measure_test_against_nn_eq_test_against_nn
- \+ *def* measure_theory.probability_measure.to_weak_dual_bounded_continuous_nnreal

Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.nnreal.upper_bound

Modified src/topology/metric_space/basic.lean
- \+ *lemma* nnreal.le_add_nndist
- \+ *lemma* nnreal.nndist_zero_eq_val'
- \+ *lemma* nnreal.nndist_zero_eq_val



## [2022-01-04 23:41:45](https://github.com/leanprover-community/mathlib/commit/5c8243f)
fix(algebra/group/type_tags): resolve an instance diamond caused by over-eager unfolding ([#11240](https://github.com/leanprover-community/mathlib/pull/11240))
By setting the `one` and `zero` fields manually, we ensure that they are syntactically equal to the ones found via `has_one` and `has_zero`, rather than potentially having typeclass arguments resolved in a different way.
This seems to fix the failing test.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Diamond.20in.20multiplicative.20nat/near/266824443)
#### Estimated changes
Modified src/algebra/group/type_tags.lean


Modified test/instance_diamonds.lean




## [2022-01-04 22:10:13](https://github.com/leanprover-community/mathlib/commit/862854e)
chore(ring_theory/localization): fix typo in module docstring ([#11245](https://github.com/leanprover-community/mathlib/pull/11245))
There was a mismatch in the module docstring to the decl name later.
#### Estimated changes
Modified src/ring_theory/localization.lean




## [2022-01-04 18:47:59](https://github.com/leanprover-community/mathlib/commit/dc352a6)
chore(.github): include co-author attributions in PR template ([#11239](https://github.com/leanprover-community/mathlib/pull/11239))
#### Estimated changes
Modified .github/PULL_REQUEST_TEMPLATE.md




## [2022-01-04 18:47:58](https://github.com/leanprover-community/mathlib/commit/692b6b7)
chore(analysis/inner_product_space/basic): adjust decidability assumptions ([#11212](https://github.com/leanprover-community/mathlib/pull/11212))
Eliminate the `open_locale classical` in `inner_product_space.basic` and replace by specific decidability assumptions.
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean




## [2022-01-04 18:47:57](https://github.com/leanprover-community/mathlib/commit/49cbce2)
chore(data/fintype/basic): set.to_finset_univ generalization ([#11174](https://github.com/leanprover-community/mathlib/pull/11174))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean


Modified src/data/fintype/basic.lean
- \+/\- *lemma* set.to_finset_univ

Modified src/group_theory/specific_groups/cyclic.lean




## [2022-01-04 18:47:56](https://github.com/leanprover-community/mathlib/commit/037147e)
feat(probability_theory/stopping): define stopped process ([#10851](https://github.com/leanprover-community/mathlib/pull/10851))
#### Estimated changes
Modified src/probability_theory/stopping.lean
- \+ *lemma* measure_theory.adapted.stopped_process
- \+ *lemma* measure_theory.integrable_stopped_process
- \+/\- *lemma* measure_theory.is_stopping_time.measurable_set_eq
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_ge
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_le
- \+ *lemma* measure_theory.measurable_stopped_process
- \+ *lemma* measure_theory.mem_ℒp_stopped_process
- \+ *def* measure_theory.stopped_process
- \+ *lemma* measure_theory.stopped_process_eq
- \+ *lemma* measure_theory.stopped_process_eq_of_ge
- \+ *lemma* measure_theory.stopped_process_eq_of_le
- \+ *def* measure_theory.stopped_value



## [2022-01-04 16:45:27](https://github.com/leanprover-community/mathlib/commit/5df2e7b)
chore(data/polynomial, data/finset/lattice): basic lemmas ([#11237](https://github.com/leanprover-community/mathlib/pull/11237))
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.coe_inf_of_nonempty
- \+ *lemma* finset.coe_sup_of_nonempty

Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* polynomial.degree_mono



## [2022-01-04 16:45:25](https://github.com/leanprover-community/mathlib/commit/5f3f01f)
feat(set_theory/ordinal_arithmetic): Proved `add_log_le_log_mul` ([#11228](https://github.com/leanprover-community/mathlib/pull/11228))
That is, `log b u + log b v ≤ log b (u * v)`. The other direction holds only when `b ≠ 2` and `b` is principal multiplicative, and will be added at a much later PR.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.add_log_le_log_mul



## [2022-01-04 16:45:24](https://github.com/leanprover-community/mathlib/commit/18330f6)
feat(tactic/abel): support 0 in group expressions ([#11201](https://github.com/leanprover-community/mathlib/pull/11201))
[As reported on Zulip.](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60abel.60.20not.20rewriting.20with.20.60sub_zero.60/near/266645648)
fixes [#11200](https://github.com/leanprover-community/mathlib/pull/11200)
#### Estimated changes
Modified src/tactic/abel.lean


Modified test/abel.lean




## [2022-01-04 16:45:23](https://github.com/leanprover-community/mathlib/commit/b0f2f55)
feat(set_theory/ordinal_arithmetic): Proved `dvd_iff_mod_eq_zero` ([#11195](https://github.com/leanprover-community/mathlib/pull/11195))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.dvd_iff_mod_eq_zero
- \+ *theorem* ordinal.dvd_of_mod_eq_zero
- \+ *theorem* ordinal.mod_eq_zero_of_dvd



## [2022-01-04 16:45:22](https://github.com/leanprover-community/mathlib/commit/7f244cf)
feat(category_theory/limits/filtered_colimits_commute_with_finite_limits): A curried variant of the fact that filtered colimits commute with finite limits. ([#11154](https://github.com/leanprover-community/mathlib/pull/11154))
#### Estimated changes
Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean
- \+ *lemma* category_theory.limits.ι_colimit_limit_iso_limit_π



## [2022-01-04 16:45:20](https://github.com/leanprover-community/mathlib/commit/06c3ab2)
feat(ring_theory/discriminant): add of_power_basis_eq_norm ([#11149](https://github.com/leanprover-community/mathlib/pull/11149))
From flt-regular.
#### Estimated changes
Modified src/data/fin/interval.lean
- \+ *lemma* fin.prod_filter_lt_mul_neg_eq_prod_off_diag

Modified src/ring_theory/discriminant.lean
- \+ *lemma* algebra.of_power_basis_eq_norm
- \+ *lemma* algebra.of_power_basis_eq_prod''
- \+ *lemma* algebra.of_power_basis_eq_prod'



## [2022-01-04 16:45:19](https://github.com/leanprover-community/mathlib/commit/4a0e844)
feat(data/finset): to_finset empty iff ([#11088](https://github.com/leanprover-community/mathlib/pull/11088))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* list.to_finset_eq_empty_iff



## [2022-01-04 16:45:18](https://github.com/leanprover-community/mathlib/commit/68d2d21)
feat(testing/slim_check): teach slim_check about `finsupp`s ([#10916](https://github.com/leanprover-community/mathlib/pull/10916))
We add some instances so that `slim_check` can generate `finsupp`s and hence try to provide counterexamples for them.
As the way the original slim_check for functions works is to generate a finite list of random values and pick a default for the rest of the values these `total_functions` are quite close to finsupps already, we just have to map the default value to zero, and prove various things about the support.
There might be conceptually nicer ways of building this instance but this seems functional enough.
Seeing as many finsupp defs are classical (and noncomputable) this isn't quite as useful for generating counterexamples as I originally hoped.
See the test at `test/slim_check.lean` for a basic example of usage
I wrote this while working on flt-regular but it is hopefully useful outside of that
#### Estimated changes
Modified src/testing/slim_check/functions.lean
- \+ *def* slim_check.total_function.apply_finsupp
- \+ *def* slim_check.total_function.zero_default
- \+ *def* slim_check.total_function.zero_default_supp

Modified test/slim_check.lean




## [2022-01-04 16:45:16](https://github.com/leanprover-community/mathlib/commit/7d42ded)
chore(*): Rename instances ([#9200](https://github.com/leanprover-community/mathlib/pull/9200))
Rename
* `lattice_of_linear_order` -> `linear_order.to_lattice`
* `distrib_lattice_of_linear_order` -> `linear_order.to_distrib_lattice`
to follow the naming convention (well, it's currently not explicitly written there, but autogenerated names follow that).
#### Estimated changes
Modified src/algebra/char_p/exp_char.lean


Modified src/algebra/order/monoid.lean


Modified src/data/fin/basic.lean


Modified src/data/int/order.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/lattice.lean


Modified src/data/real/hyperreal.lean


Modified src/order/atoms.lean


Modified src/order/filter/filter_product.lean
- \- *lemma* filter.germ.lattice_of_linear_order_eq_filter_germ_lattice
- \+ *lemma* filter.germ.linear_order.to_lattice_eq_filter_germ_lattice

Modified src/order/lattice.lean




## [2022-01-04 15:37:18](https://github.com/leanprover-community/mathlib/commit/b99a98e)
doc(category_theory/limits/shapes/pullbacks): fix doc ([#11225](https://github.com/leanprover-community/mathlib/pull/11225))
the link doesn't work with the full stop
#### Estimated changes
Modified src/category_theory/limits/shapes/pullbacks.lean




## [2022-01-04 13:36:42](https://github.com/leanprover-community/mathlib/commit/a30375e)
feat(topology/fiber_bundle): a topological fiber bundle is a quotient map ([#11194](https://github.com/leanprover-community/mathlib/pull/11194))
* The projection map of a topological fiber bundle (pre)trivialization
  is surjective onto its base set.
* The projection map of a topological fiber bundle with a nonempty
  fiber is surjective. Since it is also a continuous open map, it is a
  quotient map.
* Golf a few proofs.
#### Estimated changes
Modified src/topology/fiber_bundle.lean
- \+ *lemma* is_topological_fiber_bundle.map_proj_nhds
- \+ *lemma* is_topological_fiber_bundle.quotient_map_proj
- \+ *lemma* is_topological_fiber_bundle.surjective_proj
- \+ *lemma* topological_fiber_bundle.pretrivialization.proj_surj_on_base_set
- \+ *lemma* topological_fiber_bundle.trivialization.proj_surj_on_base_set



## [2022-01-04 13:36:33](https://github.com/leanprover-community/mathlib/commit/aa82ba0)
feat(algebra/opposites): add `add_opposite` ([#11080](https://github.com/leanprover-community/mathlib/pull/11080))
Add `add_opposite`, add `to_additive` here and there. More `to_additive` can be added as needed later.
#### Estimated changes
Modified src/algebra/group/opposite.lean
- \+ *def* add_equiv.mul_op
- \+ *def* add_equiv.mul_unop
- \- *def* add_equiv.op
- \- *def* add_equiv.unop
- \+ *def* add_monoid_hom.mul_op
- \+ *lemma* add_monoid_hom.mul_op_ext
- \+ *def* add_monoid_hom.mul_unop
- \- *def* add_monoid_hom.op
- \- *lemma* add_monoid_hom.op_ext
- \- *def* add_monoid_hom.unop
- \+ *def* add_opposite.op_mul_equiv
- \+ *lemma* add_opposite.op_mul_equiv_to_equiv
- \+ *lemma* add_opposite.op_pow
- \+ *lemma* add_opposite.unop_pow
- \+ *lemma* commute.op
- \+/\- *def* monoid_hom.from_opposite
- \+/\- *def* monoid_hom.op
- \+/\- *def* monoid_hom.to_opposite
- \+/\- *def* monoid_hom.unop
- \+/\- *def* mul_equiv.unop
- \- *lemma* mul_opposite.commute.op
- \+/\- *lemma* mul_opposite.commute.unop
- \+/\- *lemma* mul_opposite.commute_op
- \+/\- *lemma* mul_opposite.commute_unop
- \- *lemma* mul_opposite.semiconj_by.op
- \- *lemma* mul_opposite.semiconj_by.unop
- \+/\- *lemma* mul_opposite.semiconj_by_op
- \+/\- *lemma* mul_opposite.semiconj_by_unop
- \+ *lemma* semiconj_by.op
- \+ *lemma* semiconj_by.unop
- \+/\- *lemma* units.coe_op_equiv_symm
- \+/\- *lemma* units.coe_unop_op_equiv
- \+/\- *def* units.op_equiv

Modified src/algebra/opposites.lean
- \+ *lemma* add_opposite.op_div
- \+ *lemma* add_opposite.op_eq_one_iff
- \+ *lemma* add_opposite.op_inv
- \+ *lemma* add_opposite.op_mul
- \+ *lemma* add_opposite.op_one
- \+ *lemma* add_opposite.unop_div
- \+ *lemma* add_opposite.unop_eq_one_iff
- \+ *lemma* add_opposite.unop_inv
- \+ *lemma* add_opposite.unop_mul
- \+ *lemma* add_opposite.unop_one
- \+/\- *lemma* mul_opposite.op_bijective
- \+/\- *lemma* mul_opposite.op_comp_unop
- \+/\- *lemma* mul_opposite.op_eq_one_iff
- \+/\- *lemma* mul_opposite.op_eq_zero_iff
- \+/\- *lemma* mul_opposite.op_inj
- \+/\- *lemma* mul_opposite.op_injective
- \+/\- *lemma* mul_opposite.op_inv
- \+/\- *lemma* mul_opposite.op_mul
- \+/\- *lemma* mul_opposite.op_ne_zero_iff
- \+/\- *lemma* mul_opposite.op_one
- \+/\- *lemma* mul_opposite.op_smul
- \+/\- *lemma* mul_opposite.op_surjective
- \+/\- *lemma* mul_opposite.op_unop
- \+/\- *lemma* mul_opposite.unop_bijective
- \+/\- *lemma* mul_opposite.unop_comp_op
- \+/\- *lemma* mul_opposite.unop_eq_one_iff
- \+/\- *lemma* mul_opposite.unop_eq_zero_iff
- \+/\- *lemma* mul_opposite.unop_inj
- \+/\- *lemma* mul_opposite.unop_injective
- \+/\- *lemma* mul_opposite.unop_inv
- \+/\- *lemma* mul_opposite.unop_mul
- \+/\- *lemma* mul_opposite.unop_ne_zero_iff
- \+/\- *lemma* mul_opposite.unop_one
- \+/\- *lemma* mul_opposite.unop_op
- \+/\- *lemma* mul_opposite.unop_smul
- \+/\- *lemma* mul_opposite.unop_surjective

Modified src/algebra/ring/opposite.lean


Modified src/data/equiv/ring.lean


Modified src/group_theory/group_action/opposite.lean
- \+/\- *lemma* op_smul_eq_mul



## [2022-01-04 13:36:24](https://github.com/leanprover-community/mathlib/commit/a7aa2c8)
feat(data/finset/sigma): A way to lift `finset`-valued functions to a sigma type ([#10958](https://github.com/leanprover-community/mathlib/pull/10958))
This defines `finset.sigma_lift : (Π i, α i → β i → finset (γ i)) → Σ i, α i → Σ i, β i → finset (Σ i, γ i)` as the function which returns the finset corresponding to the first coordinate of `a b : Σ i, α i` if they have the same, or the empty set else.
#### Estimated changes
Modified src/data/finset/sigma.lean
- \+ *lemma* finset.card_sigma_lift
- \+ *lemma* finset.mem_sigma_lift
- \+ *lemma* finset.mk_mem_sigma_lift
- \+ *lemma* finset.not_mem_sigma_lift_of_ne_left
- \+ *lemma* finset.not_mem_sigma_lift_of_ne_right
- \+ *def* finset.sigma_lift
- \+ *lemma* finset.sigma_lift_eq_empty
- \+ *lemma* finset.sigma_lift_mono
- \+ *lemma* finset.sigma_lift_nonempty



## [2022-01-04 13:36:16](https://github.com/leanprover-community/mathlib/commit/8bd2059)
feat(data/finset/slice): `r`-sets and slice ([#10685](https://github.com/leanprover-community/mathlib/pull/10685))
Two simple nonetheless useful definitions about set families. A family of `r`-sets is a set of finsets of cardinality `r`. The slice of a set family is its subset of `r`-sets.
#### Estimated changes
Modified src/combinatorics/set_family/shadow.lean


Added src/data/finset/slice.lean
- \+ *lemma* finset.eq_of_mem_slice
- \+ *lemma* finset.mem_slice
- \+ *lemma* finset.ne_of_mem_slice
- \+ *lemma* finset.pairwise_disjoint_slice
- \+ *lemma* finset.sized_slice
- \+ *def* finset.slice
- \+ *lemma* finset.slice_subset
- \+ *lemma* finset.subset_powerset_len_univ_iff
- \+ *lemma* set.sized.card_le
- \+ *lemma* set.sized.mono
- \+ *def* set.sized
- \+ *lemma* set.sized_union

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.mem_powerset_len_univ_iff



## [2022-01-04 12:08:44](https://github.com/leanprover-community/mathlib/commit/1aec9a1)
feat(analysis/inner_product_space/dual,adjoint): add some lemmas about extensionality with respect to a basis ([#11176](https://github.com/leanprover-community/mathlib/pull/11176))
This PR adds some lemmas about extensionality in inner product spaces with respect to a basis.
#### Estimated changes
Modified src/analysis/inner_product_space/adjoint.lean
- \+ *lemma* linear_map.eq_adjoint_iff_basis
- \+ *lemma* linear_map.eq_adjoint_iff_basis_left
- \+ *lemma* linear_map.eq_adjoint_iff_basis_right

Modified src/analysis/inner_product_space/dual.lean
- \+ *lemma* inner_product_space.ext_inner_left_basis
- \+ *lemma* inner_product_space.ext_inner_right_basis



## [2022-01-04 09:44:51](https://github.com/leanprover-community/mathlib/commit/03872fd)
feat(*): Prerequisites for the Spec gamma adjunction ([#11209](https://github.com/leanprover-community/mathlib/pull/11209))
#### Estimated changes
Modified src/algebraic_geometry/Scheme.lean
- \+ *lemma* algebraic_geometry.Scheme.forget_to_LocallyRingedSpace_preimage

Modified src/algebraic_geometry/Spec.lean
- \+ *lemma* algebraic_geometry.Spec.basic_open_hom_ext

Modified src/algebraic_geometry/locally_ringed_space.lean
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.comp_val_c
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.comp_val_c_app

Modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+ *lemma* local_ring.comap_closed_point
- \+ *lemma* local_ring.is_local_ring_hom_iff_comap_closed_point
- \- *lemma* local_ring.local_hom_iff_comap_closed_point
- \+ *lemma* prime_spectrum.comap_comp_apply

Modified src/algebraic_geometry/ringed_space.lean
- \+ *lemma* algebraic_geometry.RingedSpace.mem_top_basic_open

Modified src/algebraic_geometry/stalks.lean
- \+ *abbreviation* algebraic_geometry.PresheafedSpace.stalk
- \- *def* algebraic_geometry.PresheafedSpace.stalk

Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *lemma* algebraic_geometry.structure_sheaf.is_localization.to_basic_open
- \+ *lemma* algebraic_geometry.structure_sheaf.is_localization.to_stalk

Modified src/category_theory/adjunction/basic.lean
- \+ *lemma* category_theory.adjunction.hom_equiv_id
- \+ *lemma* category_theory.adjunction.hom_equiv_symm_id

Modified src/topology/sheaves/presheaf.lean
- \+ *lemma* Top.presheaf.pushforward_eq'_hom_app
- \+ *lemma* Top.presheaf.pushforward_map_app'



## [2022-01-04 09:44:50](https://github.com/leanprover-community/mathlib/commit/9a8e9fa)
chore(category_theory/limits): Generalize universes for `preserves/shapes/pullback.lean` ([#10780](https://github.com/leanprover-community/mathlib/pull/10780))
#### Estimated changes
Modified src/category_theory/limits/constructions/epi_mono.lean


Modified src/category_theory/limits/functor_category.lean
- \- *def* category_theory.limits.preserves_colimits_of_evaluation
- \+/\- *def* category_theory.limits.preserves_colimits_of_shape_of_evaluation
- \- *def* category_theory.limits.preserves_limits_of_evaluation
- \+/\- *def* category_theory.limits.preserves_limits_of_shape_of_evaluation
- \+ *def* category_theory.limits.{w'

Modified src/category_theory/limits/is_limit.lean
- \+ *def* category_theory.limits.is_colimit.of_whisker_equivalence
- \+ *def* category_theory.limits.is_colimit.whisker_equivalence_equiv
- \+ *def* category_theory.limits.is_limit.of_whisker_equivalence
- \+ *def* category_theory.limits.is_limit.whisker_equivalence_equiv

Modified src/category_theory/limits/preserves/limits.lean


Modified src/category_theory/limits/preserves/shapes/pullbacks.lean
- \+/\- *def* category_theory.limits.is_colimit_of_has_pushout_of_preserves_colimit
- \+/\- *def* category_theory.limits.is_limit_of_has_pullback_of_preserves_limit
- \+/\- *def* category_theory.limits.preserves_pullback_symmetry
- \+/\- *def* category_theory.limits.preserves_pushout_symmetry

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* category_theory.limits.walking_cospan_equiv
- \+ *def* category_theory.limits.walking_cospan_functor
- \+ *lemma* category_theory.limits.walking_cospan_functor_id
- \+ *lemma* category_theory.limits.walking_cospan_functor_inl
- \+ *lemma* category_theory.limits.walking_cospan_functor_inr
- \+ *lemma* category_theory.limits.walking_cospan_functor_left
- \+ *lemma* category_theory.limits.walking_cospan_functor_one
- \+ *lemma* category_theory.limits.walking_cospan_functor_right
- \+ *def* category_theory.limits.walking_span_equiv
- \+ *def* category_theory.limits.walking_span_functor
- \+ *lemma* category_theory.limits.walking_span_functor_fst
- \+ *lemma* category_theory.limits.walking_span_functor_id
- \+ *lemma* category_theory.limits.walking_span_functor_left
- \+ *lemma* category_theory.limits.walking_span_functor_right
- \+ *lemma* category_theory.limits.walking_span_functor_snd
- \+ *lemma* category_theory.limits.walking_span_functor_zero



## [2022-01-04 07:46:59](https://github.com/leanprover-community/mathlib/commit/044c1de)
feat(analysis/special_functions/trigonometric): a few lemmas ([#11217](https://github.com/leanprover-community/mathlib/pull/11217))
Add a few trivial lemmas about `arcsin`/`arccos`.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/inverse.lean
- \+ *lemma* real.arccos_le_pi_div_four
- \+ *lemma* real.arccos_le_pi_div_two
- \+ *lemma* real.pi_div_four_le_arcsin



## [2022-01-04 07:46:58](https://github.com/leanprover-community/mathlib/commit/3045014)
feat(algebra/order/ring): turn `mul_self_pos` into an `iff` ([#11216](https://github.com/leanprover-community/mathlib/pull/11216))
#### Estimated changes
Modified archive/imo/imo1998_q2.lean


Modified src/algebra/order/ring.lean
- \+/\- *lemma* mul_self_pos

Modified src/analysis/inner_product_space/conformal_linear_map.lean


Modified src/linear_algebra/quadratic_form/basic.lean




## [2022-01-04 07:46:57](https://github.com/leanprover-community/mathlib/commit/85784b0)
feat(linear_algebra/determinant): `det_units_smul` and `det_is_unit_smul` ([#11206](https://github.com/leanprover-community/mathlib/pull/11206))
Add lemmas giving the determinant of a basis constructed with
`units_smul` or `is_unit_smul` with respect to the original basis.
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* basis.det_is_unit_smul
- \+ *lemma* basis.det_units_smul



## [2022-01-04 07:46:56](https://github.com/leanprover-community/mathlib/commit/1fc7a93)
chore(topology/metric_space/hausdorff_distance): slightly tidy some proofs ([#11203](https://github.com/leanprover-community/mathlib/pull/11203))
#### Estimated changes
Modified src/topology/metric_space/hausdorff_distance.lean




## [2022-01-04 07:46:55](https://github.com/leanprover-community/mathlib/commit/9d1503a)
feat(field_theory.intermediate_field): add intermediate_field.map_map ([#11020](https://github.com/leanprover-community/mathlib/pull/11020))
#### Estimated changes
Modified src/data/polynomial/eval.lean


Modified src/field_theory/intermediate_field.lean
- \+ *lemma* intermediate_field.map_map

Modified src/field_theory/primitive_element.lean




## [2022-01-04 06:31:42](https://github.com/leanprover-community/mathlib/commit/71dc1ea)
feat(topology/maps): preimage of closure/frontier under an open map ([#11189](https://github.com/leanprover-community/mathlib/pull/11189))
We had lemmas about `interior`. Add versions about `frontier` and `closure`.
#### Estimated changes
Modified src/analysis/normed_space/add_torsor_bases.lean


Modified src/topology/maps.lean
- \+/\- *lemma* is_open_map.interior_preimage_subset_preimage_interior
- \+ *lemma* is_open_map.maps_to_interior
- \+ *lemma* is_open_map.of_sections
- \+ *lemma* is_open_map.preimage_closure_eq_closure_preimage
- \+ *lemma* is_open_map.preimage_closure_subset_closure_preimage
- \+ *lemma* is_open_map.preimage_frontier_eq_frontier_preimage
- \+ *lemma* is_open_map.preimage_frontier_subset_frontier_preimage
- \+/\- *lemma* is_open_map.preimage_interior_eq_interior_preimage



## [2022-01-04 03:53:12](https://github.com/leanprover-community/mathlib/commit/8f391aa)
chore(algebra/module/submodule): switch `subtype_eq_val` to `coe_subtype` ([#11210](https://github.com/leanprover-community/mathlib/pull/11210))
Change the name and form of a lemma, from
```lean
lemma subtype_eq_val : ((submodule.subtype p) : p → M) = subtype.val := rfl
```
to
```lean
lemma coe_subtype : ((submodule.subtype p) : p → M) = coe := rfl
```
The latter is the simp-normal form so I claim it should be preferred.
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+ *lemma* submodule.coe_subtype
- \- *lemma* submodule.subtype_eq_val

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/finite_dimensional.lean




## [2022-01-04 01:48:54](https://github.com/leanprover-community/mathlib/commit/4daaff0)
feat(data/nat/prime): factors sublist of product ([#11104](https://github.com/leanprover-community/mathlib/pull/11104))
This PR changes the existing `factors_subset_right` to give a stronger sublist conclusion (which trivially can be used to reproduce the subst version).
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.factors_sublist_of_dvd
- \+ *lemma* nat.factors_sublist_right



## [2022-01-03 20:30:05](https://github.com/leanprover-community/mathlib/commit/62d814a)
refactor(order/lexicographic): Change the `lex` synonym ([#10926](https://github.com/leanprover-community/mathlib/pull/10926))
At least five types have a natural lexicographic order, namely:
* `α ⊕ β` where everything on the left is smaller than everything on the right
* `Σ i, α i` where things are first ordered following `ι`, then following `α i`
* `Σ' i, α i` where things are first ordered following `ι`, then following `α i`
* `α × β` where things are first ordered following `α`, then following `β`
* `finset α`, which is in a specific sene the dual of `finset.colex`.
And we could even add `Π i, α i`, `ι →₀ α`, `Π₀ i, α i`, etc... although those haven't come up yet in practice.
Hence, we generalize the `lex` synonym away from `prod` to make it a general purpose synonym to equip a type with its lexicographical order. What was `lex α β` now is `α ×ₗ β`.
Note that this PR doesn't add any of the aforementioned instances.
#### Estimated changes
Modified src/data/fin/tuple/sort.lean
- \+/\- *def* tuple.graph

Modified src/order/basic.lean


Modified src/order/lexicographic.lean
- \+/\- *def* lex
- \- *lemma* lex_le_iff
- \- *lemma* lex_lt_iff
- \+ *def* of_lex
- \+ *lemma* of_lex_inj
- \+ *lemma* of_lex_symm_eq
- \+ *lemma* of_lex_to_lex
- \+ *lemma* prod.lex.le_iff
- \+ *lemma* prod.lex.lt_iff
- \+ *def* to_lex
- \+ *lemma* to_lex_inj
- \+ *lemma* to_lex_of_lex
- \+ *lemma* to_lex_symm_eq

Modified src/order/locally_finite.lean


Modified src/tactic/linarith/preprocessing.lean




## [2022-01-03 18:55:41](https://github.com/leanprover-community/mathlib/commit/9d0fd52)
feat(measure_theory/function/lp_space): use has_measurable_add2 instead of second_countable_topology ([#11202](https://github.com/leanprover-community/mathlib/pull/11202))
Use the weaker assumption `[has_measurable_add₂ E]` instead of `[second_countable_topology E]` in 4 lemmas.
#### Estimated changes
Modified src/measure_theory/function/lp_space.lean
- \+/\- *lemma* measure_theory.snorm'_sum_le
- \+/\- *lemma* measure_theory.snorm_sum_le



## [2022-01-03 16:25:35](https://github.com/leanprover-community/mathlib/commit/7249895)
feat(analysis/inner_product_space/basic): negating orthonormal vectors ([#11208](https://github.com/leanprover-community/mathlib/pull/11208))
Add a lemma that, given an orthonormal family, negating some of the
vectors in it produces another orthonormal family.
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* orthonormal.orthonormal_of_forall_eq_or_eq_neg



## [2022-01-03 15:26:28](https://github.com/leanprover-community/mathlib/commit/83f4036)
feat(*/cyclotomic): update is_root_cyclotomic_iff to use ne_zero ([#11071](https://github.com/leanprover-community/mathlib/pull/11071))
#### Estimated changes
Modified src/number_theory/primes_congruent_one.lean


Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+/\- *lemma* polynomial.is_root_cyclotomic_iff

Modified src/ring_theory/polynomial/cyclotomic/eval.lean




## [2022-01-03 14:30:17](https://github.com/leanprover-community/mathlib/commit/236d978)
feat(linear_algebra/matrix/basis): `to_matrix_units_smul` and `to_matrix_is_unit_smul` ([#11191](https://github.com/leanprover-community/mathlib/pull/11191))
Add lemmas that applying `to_matrix` to a basis constructed with
`units_smul` or `is_unit_smul` produces the corresponding diagonal
matrix.
#### Estimated changes
Modified src/linear_algebra/matrix/basis.lean
- \+ *lemma* basis.to_matrix_is_unit_smul
- \+ *lemma* basis.to_matrix_units_smul



## [2022-01-03 12:49:02](https://github.com/leanprover-community/mathlib/commit/4b3198b)
feat(combinatorics/configuration): `has_lines` implies `has_points`, and vice versa ([#11170](https://github.com/leanprover-community/mathlib/pull/11170))
If `|P| = |L|`, then `has_lines` and `has_points` are equivalent!
#### Estimated changes
Modified src/combinatorics/configuration.lean




## [2022-01-03 11:27:40](https://github.com/leanprover-community/mathlib/commit/a10cb2f)
feat(algebra/big_operators/associated): `dvd_prod_iff` for `finset` and `finsupp` ([#10675](https://github.com/leanprover-community/mathlib/pull/10675))
Adding the counterparts of `dvd_prod_iff` (in [#10624](https://github.com/leanprover-community/mathlib/pull/10624)) for `finset` and `finsupp`.
#### Estimated changes
Modified src/algebra/big_operators/associated.lean
- \+ *lemma* nat.prime.dvd_finset_prod_iff
- \+ *lemma* nat.prime.dvd_finsupp_prod_iff
- \+ *lemma* prime.dvd_finset_prod_iff
- \+ *lemma* prime.dvd_finsupp_prod_iff
- \+/\- *lemma* prime.dvd_prod_iff



## [2022-01-03 10:32:11](https://github.com/leanprover-community/mathlib/commit/a813cf5)
chore(algebra/algebra/spectrum): move `exists_spectrum_of_is_alg_closed_of_finite_dimensional` ([#10919](https://github.com/leanprover-community/mathlib/pull/10919))
Move a lemma from `field_theory/is_alg_closed/basic` into `algebra/algebra/spectrum` which belongs in this relatively new file. Also, rename (now in `spectrum` namespace) and refactor it slightly; and update the two references to it accordingly.
- [x] depends on: [#10783](https://github.com/leanprover-community/mathlib/pull/10783)
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean
- \+ *lemma* spectrum.nonempty_of_is_alg_closed_of_finite_dimensional

Modified src/category_theory/preadditive/schur.lean


Modified src/field_theory/is_alg_closed/basic.lean
- \- *lemma* exists_spectrum_of_is_alg_closed_of_finite_dimensional

Modified src/linear_algebra/eigenspace.lean




## [2022-01-03 07:35:22](https://github.com/leanprover-community/mathlib/commit/49bf3d3)
feat(data/polynomial/taylor): taylor_mul ([#11193](https://github.com/leanprover-community/mathlib/pull/11193))
#### Estimated changes
Modified src/data/polynomial/taylor.lean
- \+ *lemma* polynomial.taylor_mul



## [2022-01-03 07:35:21](https://github.com/leanprover-community/mathlib/commit/a49ee49)
feat(data/finset/functor): Functor structures for `finset` ([#10980](https://github.com/leanprover-community/mathlib/pull/10980))
This defines the monad, the commutative applicative and the (almost) traversable functor structures on `finset`.
It all goes in a new file `data.finset.functor` and picks up the `functor` instance that was stranded in `data.finset.basic` by Scott in [#2997](https://github.com/leanprover-community/mathlib/pull/2997).
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.mem_image
- \- *theorem* finset.mem_image
- \+ *lemma* finset.mem_image_const
- \+ *lemma* finset.mem_image_const_self
- \+ *lemma* finset.mem_image_of_mem
- \- *theorem* finset.mem_image_of_mem

Added src/data/finset/functor.lean
- \+ *lemma* finset.bind_def
- \+ *lemma* finset.fmap_def
- \+ *lemma* finset.id_traverse
- \+ *lemma* finset.map_comp_coe
- \+ *lemma* finset.map_traverse
- \+ *lemma* finset.pure_def
- \+ *lemma* finset.seq_def
- \+ *lemma* finset.seq_left_def
- \+ *lemma* finset.seq_right_def
- \+ *def* finset.traverse

Modified src/data/finset/lattice.lean
- \+ *lemma* finset.inf_top
- \+ *lemma* finset.sup_bot
- \+ *lemma* finset.sup_singleton''



## [2022-01-03 06:54:39](https://github.com/leanprover-community/mathlib/commit/138c61f)
chore(field_theory/ratfunc): comm_ring (ratfunc K) ([#11188](https://github.com/leanprover-community/mathlib/pull/11188))
Previously, the file only gave a `field (ratfunc K)` instance,
requiring `comm_ring K` and `is_domain K`.
In fact, `ratfunc K` is a `comm_ring` regardless of the `is_domain`.
The upstream instance is proven first, with a generalized tactic.
#### Estimated changes
Modified src/field_theory/ratfunc.lean




## [2022-01-02 23:55:46](https://github.com/leanprover-community/mathlib/commit/03a5482)
chore(topology/continuous_on): fix a typo ([#11190](https://github.com/leanprover-community/mathlib/pull/11190))
`eventually_nhds_with_of_forall` → `eventually_nhds_within_of_forall`
#### Estimated changes
Modified src/analysis/calculus/lhopital.lean


Modified src/topology/algebra/floor_ring.lean


Modified src/topology/continuous_on.lean
- \- *lemma* eventually_nhds_with_of_forall
- \+ *lemma* eventually_nhds_within_of_forall



## [2022-01-02 17:21:44](https://github.com/leanprover-community/mathlib/commit/3f77761)
feat(ring_theory/algebraic): algebraic functions ([#11156](https://github.com/leanprover-community/mathlib/pull/11156))
Accessible via a new `algebra (polynomial R) (R → R)`
and a generalization that gives `algebra (polynomial R) (S → S)` when `[algebra R S]`.
#### Estimated changes
Modified src/ring_theory/algebraic.lean
- \+ *lemma* polynomial.algebra_map_pi_eq_aeval
- \+ *lemma* polynomial.algebra_map_pi_self_eq_eval
- \+ *lemma* polynomial_smul_apply'
- \+ *lemma* polynomial_smul_apply



## [2022-01-01 20:23:07](https://github.com/leanprover-community/mathlib/commit/ebdbe6b)
feat(topology/algebra/ordered): new lemmas, update ([#11184](https://github.com/leanprover-community/mathlib/pull/11184))
* In `exists_seq_strict_mono_tendsto'` and `exists_seq_strict_anti_tendsto'`, prove that `u n` belongs to the corresponding open interval.
* Add `exists_seq_strict_anti_strict_mono_tendsto`.
* Rename `is_lub_of_tendsto` to `is_lub_of_tendsto_at_top`, rename `is_glb_of_tendsto` to `is_glb_of_tendsto_at_bot`.
* Add `is_lub_of_tendsto_at_bot`, `is_glb_of_tendsto_at_top`.
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* exists_seq_strict_anti_strict_mono_tendsto

Modified src/topology/algebra/ordered/monotone_convergence.lean
- \- *lemma* is_glb_of_tendsto
- \+ *lemma* is_glb_of_tendsto_at_bot
- \+ *lemma* is_glb_of_tendsto_at_top
- \- *lemma* is_lub_of_tendsto
- \+ *lemma* is_lub_of_tendsto_at_bot
- \+ *lemma* is_lub_of_tendsto_at_top
- \+/\- *lemma* monotone.ge_of_tendsto
- \+/\- *lemma* monotone.le_of_tendsto



## [2022-01-01 19:07:15](https://github.com/leanprover-community/mathlib/commit/02d02df)
chore(measure_theory): fix TC assumptions in 2 lemmas ([#11185](https://github.com/leanprover-community/mathlib/pull/11185))
With new assumptions, these lemmas work, e.g., for `β = ι → ℝ`.
#### Estimated changes
Modified src/measure_theory/integral/integrable_on.lean




## [2022-01-01 19:07:13](https://github.com/leanprover-community/mathlib/commit/c1b1041)
feat(topology/metric_space/basic): add `fin.dist_insert_nth_insert_nth` ([#11183](https://github.com/leanprover-community/mathlib/pull/11183))
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* fin.dist_insert_nth_insert_nth
- \+ *lemma* fin.nndist_insert_nth_insert_nth
- \+ *lemma* nndist_pi_le_iff



## [2022-01-01 17:09:52](https://github.com/leanprover-community/mathlib/commit/6486e9b)
chore(order/rel_classes): Removed unnecessary `classical` ([#11180](https://github.com/leanprover-community/mathlib/pull/11180))
Not sure what that was doing here.
#### Estimated changes
Modified src/order/rel_classes.lean




## [2022-01-01 15:44:59](https://github.com/leanprover-community/mathlib/commit/93cf56c)
feat(algebraic_geometry/*): The map `F.stalk y ⟶ F.stalk x` for `x ⤳ y` ([#11144](https://github.com/leanprover-community/mathlib/pull/11144))
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+ *lemma* prime_spectrum.le_iff_specializes
- \+ *def* prime_spectrum.localization_map_of_specializes

Modified src/algebraic_geometry/stalks.lean
- \+ *lemma* algebraic_geometry.PresheafedSpace.stalk_map.stalk_specializes_stalk_map

Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *lemma* algebraic_geometry.structure_sheaf.localization_to_stalk_stalk_specializes
- \+ *lemma* algebraic_geometry.structure_sheaf.localization_to_stalk_stalk_to_fiber_ring_hom
- \+ *lemma* algebraic_geometry.structure_sheaf.stalk_specializes_stalk_to_fiber
- \+ *lemma* algebraic_geometry.structure_sheaf.stalk_to_fiber_ring_hom_localization_to_stalk
- \+ *lemma* algebraic_geometry.structure_sheaf.to_stalk_stalk_specializes

Modified src/topology/sheaves/stalks.lean
- \+ *lemma* Top.presheaf.germ_stalk_specializes'
- \+ *lemma* Top.presheaf.germ_stalk_specializes
- \+ *def* Top.presheaf.stalk_specializes
- \+ *lemma* Top.presheaf.stalk_specializes_stalk_functor_map
- \+ *lemma* Top.presheaf.stalk_specializes_stalk_pushforward



## [2022-01-01 14:44:14](https://github.com/leanprover-community/mathlib/commit/892d465)
feat(linear_algebra/multilinear/basic): the space of multilinear maps is finite-dimensional when the components are finite-dimensional ([#10504](https://github.com/leanprover-community/mathlib/pull/10504))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/linear_algebra/multilinear/basic.lean




## [2022-01-01 13:55:32](https://github.com/leanprover-community/mathlib/commit/5353369)
feat(combinatorics/configuration): Line count equals point count ([#11169](https://github.com/leanprover-community/mathlib/pull/11169))
In a configuration satisfying `has_lines` or `has_points`, if the number of points equals the number of lines, then the number of lines through a given point equals the number of points on a given line.
#### Estimated changes
Modified src/combinatorics/configuration.lean
- \+ *lemma* configuration.has_lines.line_count_eq_point_count
- \+ *lemma* configuration.has_points.line_count_eq_point_count



## [2022-01-01 13:55:31](https://github.com/leanprover-community/mathlib/commit/a6c82af)
feat(group_theory/specific_groups/*): computes the exponents of the dihedral and generalised quaternion groups ([#11166](https://github.com/leanprover-community/mathlib/pull/11166))
This PR shows that the exponent of the dihedral group of order `2n` is equal to `lcm n 2` and that the exponent of the generalised quaternion group of order `4n` is `2 * lcm n 2`
#### Estimated changes
Modified src/group_theory/specific_groups/dihedral.lean
- \+ *lemma* dihedral_group.exponent

Modified src/group_theory/specific_groups/quaternion.lean
- \+ *lemma* quaternion_group.exponent
- \+/\- *lemma* quaternion_group.order_of_a_one



## [2022-01-01 13:55:30](https://github.com/leanprover-community/mathlib/commit/ad76a5e)
feat(data/nat/log): log_mul, log_div ([#11164](https://github.com/leanprover-community/mathlib/pull/11164))
Even with division over natural, the log "spec" holds.
#### Estimated changes
Modified src/data/nat/log.lean
- \+ *lemma* nat.log_div_base
- \+ *lemma* nat.log_div_mul_self
- \+ *lemma* nat.log_mul_base



## [2022-01-01 11:59:04](https://github.com/leanprover-community/mathlib/commit/23b01cc)
feat(algebraic_geometry): The function field of an integral scheme ([#11147](https://github.com/leanprover-community/mathlib/pull/11147))
#### Estimated changes
Modified src/algebra/field/basic.lean


Added src/algebraic_geometry/function_field.lean
- \+ *abbreviation* algebraic_geometry.Scheme.function_field
- \+ *abbreviation* algebraic_geometry.Scheme.germ_to_function_field
- \+ *lemma* algebraic_geometry.Scheme.germ_to_function_field_injective
- \+ *lemma* algebraic_geometry.germ_injective_of_is_integral

Modified src/algebraic_geometry/prime_spectrum/basic.lean


Modified src/algebraic_geometry/properties.lean
- \+ *lemma* algebraic_geometry.affine_is_integral_iff
- \+ *lemma* algebraic_geometry.affine_is_reduced_iff
- \+ *lemma* algebraic_geometry.is_integral_iff_is_irreducible_and_is_reduced
- \+ *lemma* algebraic_geometry.is_integral_of_is_irreducible_is_reduced
- \+ *lemma* algebraic_geometry.is_integral_of_open_immersion
- \+ *lemma* algebraic_geometry.map_injective_of_is_integral

Modified src/topology/opens.lean
- \+ *lemma* topological_space.opens.coe_top
- \+ *lemma* topological_space.opens.ne_bot_iff_nonempty
- \+ *lemma* topological_space.opens.not_nonempty_iff_eq_bot



## [2022-01-01 02:32:45](https://github.com/leanprover-community/mathlib/commit/1594b0c)
feat(normed_space/lp_space): Lp space for `Π i, E i` ([#11015](https://github.com/leanprover-community/mathlib/pull/11015))
For a family `Π i, E i` of normed spaces, define the subgroup with finite lp norm, and prove it is a `normed_group`.  Many parts adapted from the development of `measure_theory.Lp` by @RemyDegenne.
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Lp.20space
#### Estimated changes
Added src/analysis/normed_space/lp_space.lean
- \+ *lemma* lp.coe_fn_add
- \+ *lemma* lp.coe_fn_neg
- \+ *lemma* lp.coe_fn_smul
- \+ *lemma* lp.coe_fn_sub
- \+ *lemma* lp.coe_fn_zero
- \+ *lemma* lp.coe_lp_submodule
- \+ *lemma* lp.eq_zero'
- \+ *lemma* lp.eq_zero_iff_coe_fn_eq_zero
- \+ *lemma* lp.ext
- \+ *lemma* lp.has_sum_norm
- \+ *lemma* lp.is_lub_norm
- \+ *def* lp.lp_submodule
- \+ *lemma* lp.mem_lp_const_smul
- \+ *lemma* lp.norm_const_smul
- \+ *lemma* lp.norm_eq_card_dsupport
- \+ *lemma* lp.norm_eq_csupr
- \+ *lemma* lp.norm_eq_tsum_rpow
- \+ *lemma* lp.norm_eq_zero_iff
- \+ *lemma* lp.norm_neg
- \+ *lemma* lp.norm_nonneg'
- \+ *lemma* lp.norm_rpow_eq_tsum
- \+ *lemma* lp.norm_zero
- \+ *def* lp
- \+ *lemma* mem_ℓp.add
- \+ *lemma* mem_ℓp.bdd_above
- \+ *lemma* mem_ℓp.const_mul
- \+ *lemma* mem_ℓp.const_smul
- \+ *lemma* mem_ℓp.finite_dsupport
- \+ *lemma* mem_ℓp.finset_sum
- \+ *lemma* mem_ℓp.neg
- \+ *lemma* mem_ℓp.neg_iff
- \+ *lemma* mem_ℓp.of_exponent_ge
- \+ *lemma* mem_ℓp.sub
- \+ *lemma* mem_ℓp.summable
- \+ *def* mem_ℓp
- \+ *lemma* mem_ℓp_gen
- \+ *lemma* mem_ℓp_gen_iff
- \+ *lemma* mem_ℓp_infty
- \+ *lemma* mem_ℓp_infty_iff
- \+ *lemma* mem_ℓp_zero
- \+ *lemma* mem_ℓp_zero_iff
- \+ *def* pre_lp
- \+ *lemma* zero_mem_ℓp'
- \+ *lemma* zero_mem_ℓp

Modified src/analysis/normed_space/pi_Lp.lean


Modified src/analysis/special_functions/pow.lean
- \+ *lemma* real.rpow_le_rpow_of_exponent_ge'
- \+ *lemma* real.rpow_left_inj_on

Modified src/data/set/basic.lean


Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum_zero_iff_of_nonneg

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* eventually_gt_of_tendsto_gt
- \+ *lemma* eventually_lt_of_tendsto_lt



## [2022-01-01 00:20:37](https://github.com/leanprover-community/mathlib/commit/742ec88)
feat(data/set/*): lemmas about `monotone`/`antitone` and sets/intervals ([#11173](https://github.com/leanprover-community/mathlib/pull/11173))
* Rename `set.monotone_inter` and `set.monotone_union` to
  `monotone.inter` and `monotone.union`.
* Add `antitone` versions of some `monotone` lemmas.
* Specialize `Union_Inter_of_monotone` for `set.pi`.
* Add lemmas about `⋃ x, Ioi (f x)`, `⋃ x, Iio (f x)`, and `⋃ x, Ioo (f x) (g x)`.
* Add dot notation lemmas `monotone.Ixx` and `antitone.Ixx`.
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* set.Union_pi_of_monotone
- \+ *lemma* set.Union_univ_pi_of_monotone

Modified src/data/set/intervals/disjoint.lean
- \+ *lemma* is_glb.Union_Ioi_eq
- \+ *lemma* is_glb.bUnion_Ioi_eq
- \+ *lemma* is_lub.Union_Iio_eq
- \+ *lemma* is_lub.bUnion_Iio_eq
- \+/\- *lemma* set.Union_Ico_eq_Iio_self_iff
- \+/\- *lemma* set.Union_Ioc_eq_Ioi_self_iff
- \+/\- *lemma* set.bUnion_Ico_eq_Iio_self_iff
- \+/\- *lemma* set.bUnion_Ioc_eq_Ioi_self_iff

Modified src/data/set/intervals/monotone.lean
- \+ *lemma* Union_Ioo_of_mono_of_is_glb_of_is_lub
- \+ *lemma* antitone_Ici
- \+ *lemma* antitone_Ioi
- \+ *lemma* monotone_Iic
- \+ *lemma* monotone_Iio
- \+/\- *def* order_iso_Ioo_neg_one_one

Modified src/data/set/lattice.lean
- \+ *theorem* antitone.inter
- \+ *theorem* antitone.union
- \+ *theorem* monotone.inter
- \+ *theorem* monotone.union
- \+ *theorem* set.antitone_set_of
- \- *theorem* set.monotone_inter
- \- *theorem* set.monotone_union

Modified src/order/lattice.lean
- \+ *lemma* antitone.le_map_inf
- \+ *lemma* antitone.map_inf
- \+ *lemma* antitone.map_sup
- \+ *lemma* antitone.map_sup_le

Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2022-01-01 00:20:36](https://github.com/leanprover-community/mathlib/commit/979f2e7)
fix(order/filter/ultrafilter): dedup instance names ([#11171](https://github.com/leanprover-community/mathlib/pull/11171))
#### Estimated changes
Modified src/order/filter/ultrafilter.lean




## [2022-01-01 00:20:35](https://github.com/leanprover-community/mathlib/commit/da54388)
feat(combinatorics/simple_graph/srg): is_SRG_with for complete graphs, edgeless graphs, and complements ([#5698](https://github.com/leanprover-community/mathlib/pull/5698))
We add the definition of a strongly regular graph and prove some useful lemmas about them.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* simple_graph.bot_degree
- \+ *lemma* simple_graph.card_common_neighbors_top
- \+ *lemma* simple_graph.common_neighbors_top_eq
- \- *lemma* simple_graph.complete_graph_is_regular
- \- *lemma* simple_graph.is_regular_compl_of_is_regular
- \+ *lemma* simple_graph.is_regular_of_degree.compl
- \+ *lemma* simple_graph.is_regular_of_degree.degree_eq
- \+ *lemma* simple_graph.is_regular_of_degree.top
- \- *lemma* simple_graph.is_regular_of_degree_eq
- \+ *lemma* simple_graph.ne_of_adj_of_not_adj
- \+ *lemma* simple_graph.neighbor_finset_compl
- \+ *lemma* simple_graph.neighbor_finset_def

Modified src/combinatorics/simple_graph/strongly_regular.lean
- \+ *lemma* simple_graph.bot_strongly_regular
- \+ *lemma* simple_graph.compl_neighbor_finset_sdiff_inter_eq
- \- *lemma* simple_graph.complete_strongly_regular
- \- *structure* simple_graph.is_SRG_of
- \+ *lemma* simple_graph.is_SRG_with.card_common_neighbors_eq_of_adj_compl
- \+ *lemma* simple_graph.is_SRG_with.card_common_neighbors_eq_of_not_adj_compl
- \+ *lemma* simple_graph.is_SRG_with.card_neighbor_finset_union_eq
- \+ *lemma* simple_graph.is_SRG_with.card_neighbor_finset_union_of_adj
- \+ *lemma* simple_graph.is_SRG_with.card_neighbor_finset_union_of_not_adj
- \+ *lemma* simple_graph.is_SRG_with.compl
- \+ *lemma* simple_graph.is_SRG_with.compl_is_regular
- \+ *lemma* simple_graph.is_SRG_with.top
- \+ *structure* simple_graph.is_SRG_with
- \+ *lemma* simple_graph.sdiff_compl_neighbor_finset_inter_eq

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.compl_inter
- \+ *lemma* finset.compl_union
- \+ *lemma* finset.inter_compl
- \+/\- *lemma* finset.union_compl

Modified src/data/set/finite.lean
- \+ *lemma* set.to_finset_sdiff
- \+ *lemma* set.to_finset_singleton

Modified src/measure_theory/measure/outer_measure.lean


