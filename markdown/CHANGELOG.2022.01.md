## [2022-01-31 22:22:23](https://github.com/leanprover-community/mathlib/commit/731d93b)
feat(group_theory/sylow): the normalizer is self-normalizing ([#11638](https://github.com/leanprover-community/mathlib/pull/11638))
with hat tip to Thomas Browning for a proof on Zuplip.
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *lemma* normal_of_normalizer_normal
- \+ *lemma* normalizer_normalizer
- \+ *lemma* normal_of_normalizer_condition



## [2022-01-31 22:22:22](https://github.com/leanprover-community/mathlib/commit/5964343)
feat(data/equiv): define `mul_equiv_class` ([#10760](https://github.com/leanprover-community/mathlib/pull/10760))
This PR defines a class of types of multiplicative (additive) equivalences, along the lines of [#9888](https://github.com/leanprover-community/mathlib/pull/9888).
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+/\- *lemma* map_eq_one_iff
- \+ *lemma* map_ne_one_iff
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \- *lemma* map_mul
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \- *lemma* map_one
- \+/\- *lemma* map_eq_one_iff
- \- *lemma* map_inv
- \- *lemma* add_equiv.map_sub

Modified src/data/fun_like/basic.lean
- \+ *lemma* coe_eq_coe_fn



## [2022-01-31 20:42:48](https://github.com/leanprover-community/mathlib/commit/a0bb6ea)
feat(algebraic_geometry): Open covers of the fibred product. ([#11733](https://github.com/leanprover-community/mathlib/pull/11733))
#### Estimated changes
Modified src/algebraic_geometry/open_immersion.lean
- \+ *def* open_cover_of_is_iso
- \+ *def* open_cover.copy
- \+ *def* open_cover.pushforward_iso

Modified src/algebraic_geometry/pullbacks.lean
- \+ *def* open_cover_of_left
- \+ *def* open_cover_of_right
- \+ *def* open_cover_of_base'
- \+ *def* open_cover_of_base



## [2022-01-31 20:42:46](https://github.com/leanprover-community/mathlib/commit/6130e57)
feat(topology/metric_space/basic): add some lemmas about spheres ([#11719](https://github.com/leanprover-community/mathlib/pull/11719))
#### Estimated changes
Modified src/analysis/normed_space/is_R_or_C.lean
- \+ *lemma* normed_space.sphere_nonempty_is_R_or_C

Modified src/topology/metric_space/basic.lean
- \+ *lemma* bounded_sphere
- \+ *theorem* sphere_eq_empty_of_subsingleton
- \+ *theorem* sphere_is_empty_of_subsingleton



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
- \+ *theorem* ord_card_unbounded
- \+ *theorem* eq_aleph'_of_eq_card_ord
- \+ *theorem* ord_aleph'_eq_enum_card
- \+ *theorem* ord_card_unbounded'
- \+ *theorem* eq_aleph_of_eq_card_ord
- \+ *theorem* ord_aleph_eq_enum_card

Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* is_normal.lt_nfp
- \+/\- *theorem* is_normal.le_nfp
- \+ *theorem* is_normal.nfp_unbounded
- \+/\- *theorem* deriv_limit
- \+ *theorem* is_normal.fp_iff_deriv'
- \+/\- *theorem* is_normal.fp_iff_deriv
- \+ *theorem* deriv_eq_enum_fp
- \+/\- *theorem* is_normal.lt_nfp
- \+/\- *theorem* is_normal.le_nfp
- \+/\- *theorem* deriv_limit
- \+/\- *theorem* is_normal.fp_iff_deriv



## [2022-01-31 19:55:53](https://github.com/leanprover-community/mathlib/commit/750f53c)
feat(analysis/seminorm): define the topology induced by a family of seminorms ([#11604](https://github.com/leanprover-community/mathlib/pull/11604))
Define the topology induced by a single seminorm and by a family of seminorms and show that boundedness of linear maps implies continuity.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* smul_le_smul
- \+ *lemma* finset_sup_le_sum
- \+ *lemma* ball_smul
- \+/\- *lemma* ball_finset_sup_eq_Inter
- \+/\- *lemma* ball_finset_sup
- \+ *lemma* seminorm_basis_zero_iff
- \+ *lemma* seminorm_basis_zero_mem
- \+ *lemma* seminorm_basis_zero_singleton_mem
- \+ *lemma* seminorm_basis_zero_nonempty
- \+ *lemma* seminorm_basis_zero_intersect
- \+ *lemma* seminorm_basis_zero_zero
- \+ *lemma* seminorm_basis_zero_add
- \+ *lemma* seminorm_basis_zero_neg
- \+ *lemma* seminorm_basis_zero_smul_right
- \+ *lemma* seminorm_basis_zero_smul
- \+ *lemma* seminorm_basis_zero_smul_left
- \+ *lemma* is_bounded_const
- \+ *lemma* const_is_bounded
- \+ *lemma* is_bounded_sup
- \+ *lemma* with_seminorms_eq
- \+ *lemma* continuous_from_bounded
- \+ *lemma* cont_with_seminorms_normed_space
- \+ *lemma* cont_normed_space_to_with_seminorms
- \+/\- *lemma* ball_finset_sup_eq_Inter
- \+/\- *lemma* ball_finset_sup
- \+ *def* pullback
- \+ *def* seminorm_basis_zero
- \+ *def* seminorm_add_group_filter_basis
- \+ *def* seminorm_module_filter_basis
- \+ *def* is_bounded



## [2022-01-31 15:42:13](https://github.com/leanprover-community/mathlib/commit/ccbb848)
feat(set_theory/ordinal_arithmetic): `lt_add_of_limit` ([#11748](https://github.com/leanprover-community/mathlib/pull/11748))
Both `lt_mul_of_limit` and `lt_opow_of_limit` already existed, so this exclusion is odd to say the least.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* lt_add_of_limit



## [2022-01-31 15:42:12](https://github.com/leanprover-community/mathlib/commit/c0be8dc)
feat(model_theory/basic): define quotient structures ([#11747](https://github.com/leanprover-community/mathlib/pull/11747))
Defines prestructures and quotient structures
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *lemma* fun_map_quotient_mk
- \+ *lemma* realize_term_quotient_mk



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
- \+ *lemma* _root_.comm_group.center_eq_top
- \+ *def* _root_.group.comm_group_of_center_eq_top



## [2022-01-31 15:42:08](https://github.com/leanprover-community/mathlib/commit/ff02774)
feat(algebra/squarefree): norm_num extension for squarefree ([#11666](https://github.com/leanprover-community/mathlib/pull/11666))
Adds two methods for computing `squarefree`: an improved algorithm for VM computation of squarefreedom via the `min_sq_fac` function, and a proof procedure which follows the same evaluation strategy as a `norm_num` extension.
#### Estimated changes
Modified src/algebra/squarefree.lean
- \+ *lemma* squarefree_iff_min_sq_fac
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

Modified src/data/nat/prime.lean
- \+ *lemma* min_fac_lemma
- \+/\- *theorem* min_fac_aux_has_prop
- \+/\- *theorem* min_fac_aux_has_prop

Modified test/norm_num_ext.lean



## [2022-01-31 15:42:06](https://github.com/leanprover-community/mathlib/commit/c04daaf)
feat(measure_theory): typeclass for measures positive on nonempty opens ([#11652](https://github.com/leanprover-community/mathlib/pull/11652))
Add a typeclass for measures positive on nonempty opens, migrate `is(_add?)_haar_measure` to this API.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* continuous.is_open_pos_measure_map

Modified src/measure_theory/covering/besicovitch_vector_space.lean

Modified src/measure_theory/group/basic.lean
- \+ *lemma* is_open_pos_measure_of_mul_left_invariant_of_compact
- \+ *lemma* is_open_pos_measure_of_mul_left_invariant_of_regular
- \- *lemma* measure_pos_of_is_open_of_is_mul_left_invariant
- \- *lemma* null_iff_empty_of_is_mul_left_invariant
- \- *lemma* _root_.is_open.haar_pos
- \- *lemma* haar_pos_of_nonempty_interior

Modified src/measure_theory/integral/interval_integral.lean

Modified src/measure_theory/measure/haar.lean

Modified src/measure_theory/measure/haar_lebesgue.lean
- \- *lemma* add_haar_ball_pos
- \- *lemma* add_haar_closed_ball_pos

Created src/measure_theory/measure/open_pos.lean
- \+ *lemma* _root_.is_open.measure_ne_zero
- \+ *lemma* _root_.is_open.measure_pos
- \+ *lemma* _root_.is_open.measure_pos_iff
- \+ *lemma* _root_.is_open.measure_eq_zero_iff
- \+ *lemma* measure_pos_of_nonempty_interior
- \+ *lemma* measure_pos_of_mem_nhds
- \+ *lemma* is_open_pos_measure_smul
- \+ *lemma* _root_.has_le.le.is_open_pos_measure
- \+ *lemma* _root_.is_open.eq_empty_of_measure_zero
- \+ *lemma* interior_eq_empty_of_null
- \+ *lemma* eq_on_open_of_ae_eq
- \+ *lemma* eq_of_ae_eq
- \+ *lemma* eq_on_of_ae_eq
- \+ *lemma* _root_.continuous.ae_eq_iff_eq
- \+ *lemma* measure_Ioi_pos
- \+ *lemma* measure_Iio_pos
- \+ *lemma* measure_Ioo_pos
- \+ *lemma* measure_Ioo_eq_zero
- \+ *lemma* eq_on_Ioo_of_ae_eq
- \+ *lemma* eq_on_Ioc_of_ae_eq
- \+ *lemma* eq_on_Ico_of_ae_eq
- \+ *lemma* eq_on_Icc_of_ae_eq
- \+ *lemma* measure_ball_pos
- \+ *lemma* measure_closed_ball_pos
- \+ *lemma* measure_ball_pos
- \+ *lemma* measure_closed_ball_pos

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* Ioo_subset_closure_interior
- \+ *lemma* closure_interior_Icc
- \+ *lemma* Ioc_subset_closure_interior
- \+ *lemma* Ico_subset_closure_interior

Modified src/topology/separation.lean
- \+ *lemma* set.eq_on.of_subset_closure



## [2022-01-31 15:42:05](https://github.com/leanprover-community/mathlib/commit/d6440a8)
feat(group_theory/nilpotent): add lemmas about `G / center G` ([#11592](https://github.com/leanprover-community/mathlib/pull/11592))
in particular its nilpotency class and an induction principle based on
that.
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* comap_upper_central_series_quotient_center
- \+ *lemma* nilpotency_class_zero_iff_subsingleton
- \+ *lemma* nilpotency_class_quotient_center
- \+ *lemma* nilpotency_class_eq_quotient_center_plus_one
- \+ *lemma* nilpotent_center_quotient_ind

Modified src/group_theory/quotient_group.lean
- \+ *lemma* comap_comap_center



## [2022-01-31 15:42:04](https://github.com/leanprover-community/mathlib/commit/06bb5b6)
feat(topology/nhds_set): define neighborhoods of a set ([#11520](https://github.com/leanprover-community/mathlib/pull/11520))
* Co-authored by @PatrickMassot
* From the sphere eversion project
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* subset_interior_iff
- \+ *lemma* interior_eq_univ
- \+ *lemma* is_open.mem_nhds_iff

Created src/topology/nhds_set.lean
- \+ *lemma* mem_nhds_set_iff_forall
- \+ *lemma* subset_interior_iff_mem_nhds_set
- \+ *lemma* mem_nhds_set_iff_exists
- \+ *lemma* is_open.mem_nhds_set
- \+ *lemma* nhds_set_singleton
- \+ *lemma* mem_nhds_set_interior
- \+ *lemma* mem_nhds_set_empty
- \+ *lemma* nhds_set_empty
- \+ *lemma* nhds_set_univ
- \+ *lemma* monotone_nhds_set
- \+ *lemma* union_mem_nhds_set
- \+ *def* nhds_set

Modified src/topology/separation.lean
- \+ *lemma* compl_singleton_mem_nhds_iff
- \+ *lemma* compl_singleton_mem_nhds_set_iff
- \+ *lemma* nhds_set_le_iff
- \+ *lemma* nhds_set_inj_iff
- \+ *lemma* injective_nhds_set
- \+ *lemma* strict_mono_nhds_set
- \+ *lemma* nhds_le_nhds_set



## [2022-01-31 15:42:02](https://github.com/leanprover-community/mathlib/commit/366d13e)
feat(scripts/lint_style): Add a check for unfreeze_local_instances ([#11509](https://github.com/leanprover-community/mathlib/pull/11509))
#### Estimated changes
Modified scripts/lint-style.py
- \+ *def* unfreeze_local_instances_check(lines,

Modified src/tactic/choose.lean



## [2022-01-31 14:14:34](https://github.com/leanprover-community/mathlib/commit/ada43f0)
feat(order/hom/complete_lattice): Complete lattice homomorphisms ([#11741](https://github.com/leanprover-community/mathlib/pull/11741))
Define frame homs and complete lattice homs using the `fun_like` along with weaker homomorphisms that only preserve `Sup`, `Inf`.
#### Estimated changes
Created src/order/hom/complete_lattice.lean
- \+ *lemma* map_supr
- \+ *lemma* map_supr₂
- \+ *lemma* map_infi
- \+ *lemma* map_infi₂
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *lemma* coe_bot
- \+ *lemma* bot_apply
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *lemma* coe_top
- \+ *lemma* top_apply
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *lemma* coe_bot
- \+ *lemma* bot_apply
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *def* comp
- \+ *def* comp
- \+ *def* to_lattice_hom
- \+ *def* comp
- \+ *def* to_Inf_hom
- \+ *def* comp



## [2022-01-31 14:14:32](https://github.com/leanprover-community/mathlib/commit/08fed82)
feat(category_theory/preadditive): the Yoneda embedding for preadditive categories ([#11740](https://github.com/leanprover-community/mathlib/pull/11740))
#### Estimated changes
Modified src/category_theory/endomorphism.lean
- \+ *lemma* smul_right
- \+ *lemma* smul_left

Modified src/category_theory/preadditive/default.lean

Modified src/category_theory/preadditive/opposite.lean

Created src/category_theory/preadditive/yoneda.lean
- \+ *lemma* whiskering_preadditive_yoneda
- \+ *lemma* whiskering_preadditive_coyoneda
- \+ *def* preadditive_yoneda_obj
- \+ *def* preadditive_yoneda
- \+ *def* preadditive_coyoneda_obj
- \+ *def* preadditive_coyoneda



## [2022-01-31 14:14:30](https://github.com/leanprover-community/mathlib/commit/323287e)
feat(data/polynomial/reverse): lemmas about evaluating reversed polynomials ([#11705](https://github.com/leanprover-community/mathlib/pull/11705))
#### Estimated changes
Modified src/data/polynomial/reverse.lean
- \+ *lemma* rev_at_zero
- \+ *lemma* reflect_C
- \+ *lemma* eval₂_reflect_mul_pow
- \+ *lemma* eval₂_reflect_eq_zero_iff
- \+ *lemma* eval₂_reverse_mul_pow
- \+ *lemma* eval₂_reverse_eq_zero_iff



## [2022-01-31 14:14:27](https://github.com/leanprover-community/mathlib/commit/bb2b58e)
feat(data/{nat,int}/parity): add division lemmas ([#11570](https://github.com/leanprover-community/mathlib/pull/11570))
Add lemmas of the form `even n → n / 2 * 2 = n` and `odd n → n / 2 * 2 + 1 = n`
#### Estimated changes
Modified src/data/int/parity.lean
- \+ *lemma* two_mul_div_two_of_even
- \+ *lemma* div_two_mul_two_of_even
- \+ *lemma* two_mul_div_two_add_one_of_odd
- \+ *lemma* div_two_mul_two_add_one_of_odd
- \+ *lemma* add_one_div_two_mul_two_of_odd
- \+ *lemma* two_mul_div_two_of_odd

Modified src/data/nat/parity.lean
- \+ *lemma* two_mul_div_two_of_even
- \+ *lemma* div_two_mul_two_of_even
- \+ *lemma* two_mul_div_two_add_one_of_odd
- \+ *lemma* div_two_mul_two_add_one_of_odd
- \+ *lemma* one_add_div_two_mul_two_of_odd



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

Created src/linear_algebra/clifford_algebra/grading.lean
- \+ *lemma* one_le_even_odd_zero
- \+ *lemma* range_ι_le_even_odd_one
- \+ *lemma* even_odd_mul_le
- \+ *lemma* graded_algebra.ι_apply
- \+ *lemma* graded_algebra.ι_sq_scalar
- \+ *lemma* supr_ι_range_eq_top
- \+ *def* even_odd
- \+ *def* graded_algebra.ι

Created src/linear_algebra/exterior_algebra/grading.lean
- \+ *lemma* graded_algebra.ι_apply
- \+ *lemma* graded_algebra.ι_sq_zero
- \+ *def* graded_algebra.ι

Created src/linear_algebra/tensor_algebra/grading.lean
- \+ *lemma* graded_algebra.ι_apply
- \+ *def* graded_algebra.ι



## [2022-01-31 12:36:17](https://github.com/leanprover-community/mathlib/commit/45cfb25)
refactor(order/bounded_order): Use `is_min`/`is_max` ([#11408](https://github.com/leanprover-community/mathlib/pull/11408))
Golf `order.bounded_order` and `data.set.basic` using `is_min`/`is_max`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *lemma* subsingleton_is_top
- \+/\- *lemma* subsingleton_is_bot
- \+/\- *lemma* subsingleton_is_top
- \+/\- *lemma* subsingleton_is_bot

Modified src/data/set/intervals/basic.lean
- \+ *lemma* _root_.is_max.Ioi_eq
- \+ *lemma* _root_.is_min.Iio_eq
- \+ *lemma* _root_.is_max.Ici_eq
- \+ *lemma* _root_.is_min.Iic_eq
- \+/\- *lemma* Ici_top
- \+/\- *lemma* Ioi_top
- \+/\- *lemma* Iic_bot
- \+/\- *lemma* Iio_bot
- \- *lemma* _root_.is_top.Ioi_eq
- \- *lemma* _root_.is_bot.Iio_eq
- \- *lemma* _root_.is_top.Ici_eq
- \- *lemma* _root_.is_bot.Iic_eq
- \+/\- *lemma* Ici_top
- \+/\- *lemma* Ioi_top
- \+/\- *lemma* Iic_bot
- \+/\- *lemma* Iio_bot

Modified src/order/atoms.lean
- \+ *lemma* eq_bot_of_lt
- \+ *lemma* eq_top_of_lt

Modified src/order/basic.lean
- \+ *lemma* eq_or_gt_of_le

Modified src/order/bounded_order.lean
- \+ *lemma* le_top
- \+ *lemma* is_top_top
- \+ *lemma* is_max_top
- \+ *lemma* not_top_lt
- \+/\- *lemma* ne_top_of_lt
- \+ *lemma* is_max_iff_eq_top
- \+ *lemma* is_top_iff_eq_top
- \+ *lemma* bot_le
- \+/\- *lemma* is_bot_bot
- \+ *lemma* is_min_bot
- \+ *lemma* not_lt_bot
- \+/\- *lemma* ne_bot_of_gt
- \+ *lemma* is_min_iff_eq_bot
- \+ *lemma* is_bot_iff_eq_bot
- \+/\- *lemma* eq_bot_or_bot_lt
- \+/\- *lemma* top_ne_bot
- \+ *lemma* bot_lt_top
- \+/\- *lemma* ne_top_of_lt
- \+/\- *lemma* is_bot_bot
- \+/\- *lemma* eq_bot_or_bot_lt
- \+/\- *lemma* ne_bot_of_gt
- \+/\- *lemma* top_ne_bot
- \- *theorem* le_top
- \- *theorem* not_top_lt
- \- *theorem* is_top_top
- \- *theorem* is_top_iff_eq_top
- \- *theorem* bot_le
- \- *theorem* not_lt_bot
- \- *theorem* is_bot_iff_eq_bot

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
- \+ *lemma* restrict_roots_of_unity_coe_apply
- \+ *lemma* map_root_of_unity_eq_pow_self
- \+/\- *lemma* map_of_injective
- \+/\- *lemma* of_map_of_injective
- \+/\- *lemma* map_iff_of_injective
- \- *lemma* ring_hom.restrict_roots_of_unity_coe_apply
- \- *lemma* ring_hom.map_root_of_unity_eq_pow_self
- \+/\- *lemma* map_of_injective
- \+/\- *lemma* of_map_of_injective
- \+/\- *lemma* map_iff_of_injective
- \+ *def* restrict_roots_of_unity
- \- *def* ring_hom.restrict_roots_of_unity



## [2022-01-31 11:21:33](https://github.com/leanprover-community/mathlib/commit/406719e)
feat(order/hom/lattice): Composition of lattice homs ([#11676](https://github.com/leanprover-community/mathlib/pull/11676))
Define `top_hom.comp`, `bot_hom.comp`, `sup_hom.comp`, `inf_hom.comp`, `lattice_hom.comp`, `bounded_lattice_hom.comp`, `order_hom.to_lattice_hom`.
#### Estimated changes
Modified src/order/hom/lattice.lean
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* coe_comp_sup_hom
- \+ *lemma* coe_comp_inf_hom
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *lemma* coe_to_lattice_hom
- \+ *lemma* to_lattice_hom_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* coe_comp_lattice_hom
- \+ *lemma* coe_comp_sup_hom
- \+ *lemma* coe_comp_inf_hom
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *def* comp
- \+ *def* comp
- \+ *def* comp
- \+ *def* comp
- \+ *def* comp
- \+ *def* to_lattice_hom_class
- \+ *def* to_lattice_hom
- \+ *def* comp



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
- \+ *lemma* one_apply
- \+/\- *def* refl
- \+/\- *def* refl



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
- \+ *lemma* coe_to_nnreal_ae_eq
- \+ *lemma* integrable_with_density_iff_integrable_smul
- \+ *lemma* integrable_with_density_iff_integrable_smul'

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* supr_lintegral_measurable_le_eq_lintegral
- \+/\- *lemma* lintegral_map
- \+/\- *lemma* lintegral_map'
- \+ *lemma* lintegral_map_le
- \+ *lemma* with_density_congr_ae
- \+ *lemma* with_density_apply_eq_zero
- \+ *lemma* ae_with_density_iff
- \+ *lemma* ae_with_density_iff_ae_restrict
- \+ *lemma* ae_measurable_with_density_iff
- \+ *lemma* ae_measurable_with_density_ennreal_iff
- \+/\- *lemma* set_lintegral_with_density_eq_set_lintegral_mul
- \+ *lemma* lintegral_with_density_eq_lintegral_mul₀'
- \+ *lemma* lintegral_with_density_eq_lintegral_mul₀
- \+ *lemma* lintegral_with_density_le_lintegral_mul
- \+ *lemma* lintegral_with_density_eq_lintegral_mul_non_measurable
- \+ *lemma* set_lintegral_with_density_eq_set_lintegral_mul_non_measurable
- \+ *lemma* lintegral_with_density_eq_lintegral_mul_non_measurable₀
- \+ *lemma* set_lintegral_with_density_eq_set_lintegral_mul_non_measurable₀
- \+/\- *lemma* lintegral_map
- \+/\- *lemma* lintegral_map'
- \+/\- *lemma* set_lintegral_with_density_eq_set_lintegral_mul
- \+/\- *def* lintegral
- \+/\- *def* lintegral

Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* ae_of_ae_restrict_of_ae_restrict_compl
- \+/\- *lemma* ae_of_ae_restrict_of_ae_restrict_compl

Modified src/probability_theory/density.lean



## [2022-01-31 09:46:27](https://github.com/leanprover-community/mathlib/commit/0c0ab69)
feat(topology/algebra/continuous_monoid_hom): Add `topological_group` instance ([#11707](https://github.com/leanprover-community/mathlib/pull/11707))
This PR proves that continuous monoid homs form a topological group.
#### Estimated changes
Modified src/topology/algebra/continuous_monoid_hom.lean
- \+ *lemma* is_inducing
- \+ *lemma* is_embedding



## [2022-01-31 09:46:26](https://github.com/leanprover-community/mathlib/commit/b3ad3f2)
feat(data/set/lattice): review ([#11672](https://github.com/leanprover-community/mathlib/pull/11672))
* generalize `set.Union_coe_set` and `set.Inter_coe_set` to dependent functions;
* add `bInter_Union`, `sUnion_Union`;
* drop `sUnion_bUnion`, `sInter_bUnion`.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+/\- *lemma* Union_coe_set
- \+/\- *lemma* Inter_coe_set
- \+ *lemma* bInter_Union
- \+ *lemma* sUnion_Union
- \+/\- *lemma* Union_coe_set
- \+/\- *lemma* Inter_coe_set
- \- *lemma* sInter_bUnion
- \- *lemma* sUnion_bUnion
- \+/\- *theorem* sInter_Union
- \+/\- *theorem* sInter_Union

Modified src/order/filter/basic.lean

Modified src/topology/metric_space/baire.lean

Modified src/topology/paracompact.lean



## [2022-01-31 09:17:53](https://github.com/leanprover-community/mathlib/commit/6319a23)
feat(number_theory/cyclotomic): simplify `ne_zero`s ([#11715](https://github.com/leanprover-community/mathlib/pull/11715))
For flt-regular.
#### Estimated changes
Modified src/algebra/ne_zero.lean
- \+ *lemma* trans
- \+/\- *lemma* of_no_zero_smul_divisors
- \+/\- *lemma* of_no_zero_smul_divisors

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
- \+ *lemma* coe_comap_of_ker_is_p_group
- \+ *lemma* coe_comap_of_injective
- \+ *lemma* coe_subtype
- \+ *def* comap_of_ker_is_p_group
- \+ *def* comap_of_injective
- \+ *def* subtype



## [2022-01-30 14:09:00](https://github.com/leanprover-community/mathlib/commit/02c720e)
chore(*): Rename `prod_dvd_prod` ([#11734](https://github.com/leanprover-community/mathlib/pull/11734))
In [#11693](https://github.com/leanprover-community/mathlib/pull/11693) I introduced the counterpart for `multiset` of `finset.prod_dvd_prod`.  It makes sense for these to have the same name, but there's already a different lemma called `multiset.prod_dvd_prod`, so the new lemma was named `multiset.prod_dvd_prod_of_dvd` instead.  As discussed with @riccardobrasca and @ericrbg at [#11693](https://github.com/leanprover-community/mathlib/pull/11693), this PR brings the names of the two counterpart lemmas into alignment, and also renames `multiset.prod_dvd_prod` to something more informative.
Renaming as follows:
`multiset.prod_dvd_prod` to `multiset.prod_dvd_prod_of_le`
`finset.prod_dvd_prod` to `finset.prod_dvd_prod_of_dvd`
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_dvd_prod_of_dvd
- \- *lemma* prod_dvd_prod

Modified src/algebra/big_operators/multiset.lean
- \+ *lemma* prod_dvd_prod_of_le
- \- *lemma* prod_dvd_prod

Modified src/algebra/squarefree.lean

Modified src/ring_theory/unique_factorization_domain.lean



## [2022-01-30 11:14:54](https://github.com/leanprover-community/mathlib/commit/a248bef)
feat(data/pnat/basic): 0 < n as a fact ([#11729](https://github.com/leanprover-community/mathlib/pull/11729))
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *lemma* fact_pos



## [2022-01-30 10:31:37](https://github.com/leanprover-community/mathlib/commit/dde904e)
chore(ring_theory/localization) weaken hypothesis from field to comm_ring ([#11713](https://github.com/leanprover-community/mathlib/pull/11713))
also making `B` an explicit argument
#### Estimated changes
Modified src/number_theory/class_number/finite.lean

Modified src/ring_theory/dedekind_domain.lean

Modified src/ring_theory/localization.lean
- \+/\- *lemma* is_algebraic_iff
- \+/\- *lemma* comap_is_algebraic_iff
- \+/\- *lemma* is_algebraic_iff
- \+/\- *lemma* comap_is_algebraic_iff



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
Created src/tactic/linear_combination.lean
- \+ *lemma* left_mul_both_sides
- \+ *lemma* sum_two_equations
- \+ *lemma* left_minus_right
- \+ *lemma* all_on_left_equiv
- \+ *lemma* replace_eq_expr

Created test/linear_combination.lean



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
- \+ *lemma* smul_eq_C_smul
- \+ *lemma* lift_monoid_with_zero_hom_apply_of_fraction_ring_mk
- \+ *lemma* lift_monoid_with_zero_hom_injective
- \+ *lemma* lift_ring_hom_apply_of_fraction_ring_mk
- \+ *lemma* lift_ring_hom_injective
- \+ *lemma* div_smul
- \+ *lemma* algebra_map_apply
- \+ *lemma* lift_monoid_with_zero_hom_apply_div
- \+ *lemma* lift_ring_hom_apply_div
- \+ *lemma* lift_alg_hom_apply_of_fraction_ring_mk
- \+ *lemma* lift_alg_hom_injective
- \+ *lemma* lift_alg_hom_apply_div
- \+ *lemma* map_denom_ne_zero
- \+ *lemma* lift_monoid_with_zero_hom_apply
- \+ *lemma* lift_ring_hom_apply
- \+ *lemma* lift_alg_hom_apply
- \+ *lemma* smul_eq_C_mul
- \+ *lemma* coe_def
- \+ *lemma* coe_num_denom
- \+ *lemma* coe_injective
- \+ *lemma* coe_apply
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* coe_add
- \+ *lemma* coe_mul
- \+ *lemma* coe_div
- \+ *lemma* coe_C
- \+ *lemma* coe_smul
- \+ *lemma* coe_X
- \+ *lemma* algebra_map_apply_div
- \+ *def* lift_monoid_with_zero_hom
- \+ *def* lift_ring_hom
- \+ *def* lift_alg_hom
- \+ *def* coe_alg_hom

Modified src/ring_theory/euclidean_domain.lean
- \+ *lemma* gcd_ne_zero_of_left
- \+ *lemma* gcd_ne_zero_of_right

Modified src/ring_theory/hahn_series.lean
- \+ *lemma* algebra_map_apply'
- \+ *lemma* _root_.polynomial.algebra_map_hahn_series_apply
- \+ *lemma* _root_.polynomial.algebra_map_hahn_series_injective

Modified src/ring_theory/localization.lean

Modified src/ring_theory/power_series/basic.lean



## [2022-01-29 21:10:10](https://github.com/leanprover-community/mathlib/commit/ff35218)
feat(analysis/convex/topology): add lemmas ([#11615](https://github.com/leanprover-community/mathlib/pull/11615))
#### Estimated changes
Modified src/analysis/convex/topology.lean
- \+ *lemma* convex.combo_interior_self_subset_interior
- \+ *lemma* convex.combo_self_interior_subset_interior
- \+ *lemma* convex.combo_mem_interior_left
- \+ *lemma* convex.combo_mem_interior_right
- \+ *lemma* convex.open_segment_subset_interior_left
- \+ *lemma* convex.open_segment_subset_interior_right
- \+/\- *lemma* convex.add_smul_sub_mem_interior
- \+/\- *lemma* convex.add_smul_mem_interior
- \+/\- *lemma* convex.add_smul_sub_mem_interior
- \+/\- *lemma* convex.add_smul_mem_interior

Modified src/topology/algebra/group.lean
- \+/\- *lemma* is_open.mul_left
- \+/\- *lemma* is_open.mul_left

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* is_closed.epigraph
- \+ *lemma* is_closed.hypograph



## [2022-01-29 20:28:18](https://github.com/leanprover-community/mathlib/commit/4085363)
feat(number_theory/prime_counting): The prime counting function ([#9080](https://github.com/leanprover-community/mathlib/pull/9080))
With an eye to implementing [this proof](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.238002/near/251178921), I am adding a file to define the prime counting function and prove a simple upper bound on it.
#### Estimated changes
Modified src/data/nat/totient.lean
- \+/\- *lemma* totient_eq_card_coprime
- \+ *lemma* filter_coprime_Ico_eq_totient
- \+ *lemma* Ico_filter_coprime_le
- \+/\- *lemma* totient_eq_card_coprime
- \+/\- *def* totient
- \+/\- *def* totient

Created src/number_theory/prime_counting.lean
- \+ *lemma* monotone_prime_counting'
- \+ *lemma* monotone_prime_counting
- \+ *lemma* prime_counting'_add_le
- \+ *def* prime_counting'
- \+ *def* prime_counting

Modified src/set_theory/fincard.lean
- \+/\- *lemma* card_eq_fintype_card
- \+/\- *lemma* card_eq_zero_of_infinite
- \+/\- *lemma* card_eq_fintype_card
- \+/\- *lemma* card_eq_zero_of_infinite
- \- *def* card



## [2022-01-29 19:47:13](https://github.com/leanprover-community/mathlib/commit/74250a0)
chore(representation_theory/maschke): remove recover ([#11721](https://github.com/leanprover-community/mathlib/pull/11721))
#### Estimated changes
Modified src/representation_theory/maschke.lean



## [2022-01-29 14:01:52](https://github.com/leanprover-community/mathlib/commit/49b8b91)
feat(data/fintype/order): `bool` is a boolean algebra ([#11694](https://github.com/leanprover-community/mathlib/pull/11694))
Provide the `boolean_algebra` instance for `bool` and use the machinery from `data.fintype.order` to deduce `complete_boolean_algebra bool` and `complete_linear_order bool`.
#### Estimated changes
Modified src/data/bool/basic.lean
- \+ *lemma* band_bnot_self
- \+ *lemma* bnot_band_self
- \+ *lemma* bor_bnot_self
- \+ *lemma* bnot_bor_self

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
- \+/\- *lemma* map_mul_left_eq_self
- \+/\- *lemma* map_mul_right_eq_self
- \+ *lemma* forall_measure_preimage_mul_iff
- \+ *lemma* forall_measure_preimage_mul_right_iff
- \+ *lemma* measure_preimage_mul
- \+ *lemma* measure_preimage_mul_right
- \+/\- *lemma* inv_apply
- \+/\- *lemma* regular_inv_iff
- \+ *lemma* measure_pos_of_is_open_of_is_mul_left_invariant
- \+ *lemma* null_iff_empty_of_is_mul_left_invariant
- \+ *lemma* null_iff_of_is_mul_left_invariant
- \+ *lemma* measure_ne_zero_iff_nonempty_of_is_mul_left_invariant
- \+ *lemma* measure_pos_iff_nonempty_of_is_mul_left_invariant
- \+ *lemma* measure_lt_top_of_is_compact_of_is_mul_left_invariant
- \+ *lemma* measure_lt_top_of_is_compact_of_is_mul_left_invariant'
- \+/\- *lemma* lintegral_eq_zero_of_is_mul_left_invariant
- \+/\- *lemma* lintegral_mul_left_eq_self
- \+/\- *lemma* lintegral_mul_right_eq_self
- \- *lemma* is_mul_left_invariant.smul
- \- *lemma* is_mul_right_invariant.smul
- \+/\- *lemma* map_mul_left_eq_self
- \- *lemma* _root_.measure_theory.is_mul_left_invariant.measure_preimage_mul
- \+/\- *lemma* map_mul_right_eq_self
- \+/\- *lemma* inv_apply
- \+/\- *lemma* regular_inv_iff
- \- *lemma* is_mul_left_invariant.inv
- \- *lemma* is_mul_right_invariant.inv
- \- *lemma* is_mul_right_invariant_inv
- \- *lemma* is_mul_left_invariant_inv
- \- *lemma* is_mul_left_invariant.measure_pos_of_is_open
- \- *lemma* is_mul_left_invariant.null_iff_empty
- \- *lemma* is_mul_left_invariant.null_iff
- \- *lemma* is_mul_left_invariant.measure_ne_zero_iff_nonempty
- \- *lemma* is_mul_left_invariant.measure_pos_iff_nonempty
- \- *lemma* is_mul_left_invariant.measure_lt_top_of_is_compact
- \- *lemma* is_mul_left_invariant.measure_lt_top_of_is_compact'
- \+/\- *lemma* lintegral_eq_zero_of_is_mul_left_invariant
- \+/\- *lemma* lintegral_mul_left_eq_self
- \+/\- *lemma* lintegral_mul_right_eq_self
- \- *lemma* is_mul_left_invariant_haar
- \- *lemma* haar_preimage_mul
- \- *lemma* haar_preimage_mul_right
- \- *def* is_mul_left_invariant
- \- *def* is_mul_right_invariant

Modified src/measure_theory/group/prod.lean
- \+/\- *lemma* map_prod_mul_eq
- \+/\- *lemma* map_prod_mul_eq_swap
- \+/\- *lemma* map_prod_inv_mul_eq
- \+/\- *lemma* map_prod_inv_mul_eq_swap
- \+/\- *lemma* map_prod_mul_inv_eq
- \+/\- *lemma* quasi_measure_preserving_inv
- \+/\- *lemma* measure_inv_null
- \+/\- *lemma* lintegral_lintegral_mul_inv
- \+/\- *lemma* measure_mul_right_null
- \+/\- *lemma* measure_mul_right_ne_zero
- \+/\- *lemma* measure_lintegral_div_measure
- \+/\- *lemma* measure_mul_measure_eq
- \+/\- *lemma* map_prod_mul_eq
- \+/\- *lemma* map_prod_mul_eq_swap
- \+/\- *lemma* map_prod_inv_mul_eq
- \+/\- *lemma* map_prod_inv_mul_eq_swap
- \+/\- *lemma* map_prod_mul_inv_eq
- \+/\- *lemma* quasi_measure_preserving_inv
- \+/\- *lemma* measure_inv_null
- \+/\- *lemma* lintegral_lintegral_mul_inv
- \+/\- *lemma* measure_mul_right_null
- \+/\- *lemma* measure_mul_right_ne_zero
- \+/\- *lemma* measure_lintegral_div_measure
- \+/\- *lemma* measure_mul_measure_eq

Modified src/measure_theory/integral/bochner.lean
- \+/\- *lemma* integral_mul_left_eq_self
- \+/\- *lemma* integral_mul_right_eq_self
- \+/\- *lemma* integral_zero_of_mul_left_eq_neg
- \+/\- *lemma* integral_zero_of_mul_right_eq_neg
- \+/\- *lemma* integral_mul_left_eq_self
- \+/\- *lemma* integral_mul_right_eq_self
- \+/\- *lemma* integral_zero_of_mul_left_eq_neg
- \+/\- *lemma* integral_zero_of_mul_right_eq_neg

Modified src/measure_theory/measure/haar.lean
- \- *lemma* is_mul_left_invariant_haar_measure
- \+/\- *theorem* haar_measure_unique
- \+/\- *theorem* regular_of_is_mul_left_invariant
- \+/\- *theorem* haar_measure_unique
- \+/\- *theorem* regular_of_is_mul_left_invariant

Modified src/measure_theory/measure/haar_lebesgue.lean
- \- *lemma* is_add_left_invariant_real_volume
- \- *lemma* is_add_left_invariant_real_volume_pi



## [2022-01-29 01:17:00](https://github.com/leanprover-community/mathlib/commit/44105f8)
feat(analysis/inner_product_space): proof of the Lax Milgram theorem ([#11491](https://github.com/leanprover-community/mathlib/pull/11491))
My work on the Lax Milgram theorem, as suggested by @hrmacbeth. Done following the [slides from Peter Howard (Texas A&M University)](https://www.math.tamu.edu/~phoward/m612/s20/elliptic2.pdf).
Closes [#10213](https://github.com/leanprover-community/mathlib/pull/10213).
#### Estimated changes
Modified docs/references.bib

Modified docs/undergrad.yaml

Modified src/analysis/inner_product_space/dual.lean
- \+ *lemma* continuous_linear_map_of_bilin_apply
- \+ *lemma* unique_continuous_linear_map_of_bilin
- \+ *def* continuous_linear_map_of_bilin

Created src/analysis/inner_product_space/lax_milgram.lean
- \+ *lemma* bounded_below
- \+ *lemma* antilipschitz
- \+ *lemma* ker_eq_bot
- \+ *lemma* closed_range
- \+ *lemma* range_eq_top
- \+ *lemma* continuous_linear_equiv_of_bilin_apply
- \+ *lemma* unique_continuous_linear_equiv_of_bilin
- \+ *def* continuous_linear_equiv_of_bilin

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

Created src/number_theory/cyclotomic/zeta.lean
- \+ *lemma* zeta_spec
- \+ *lemma* zeta_spec'
- \+ *lemma* zeta_primitive_root
- \+ *lemma* zeta_minpoly
- \+ *lemma* zeta.power_basis_gen_minpoly
- \+ *def* zeta
- \+ *def* zeta.power_basis
- \+ *def* zeta.embeddings_equiv_primitive_roots



## [2022-01-28 16:51:36](https://github.com/leanprover-community/mathlib/commit/02c3146)
feat(analysis/complex): removable singularity theorem ([#11686](https://github.com/leanprover-community/mathlib/pull/11686))
#### Estimated changes
Created src/analysis/complex/removable_singularity.lean
- \+ *lemma* analytic_at_of_differentiable_on_punctured_nhds_of_continuous_at
- \+ *lemma* differentiable_on_compl_singleton_and_continuous_at_iff
- \+ *lemma* differentiable_on_dslope
- \+ *lemma* differentiable_on_update_lim_of_is_o
- \+ *lemma* differentiable_on_update_lim_insert_of_is_o
- \+ *lemma* differentiable_on_update_lim_of_bdd_above
- \+ *lemma* tendsto_lim_of_differentiable_on_punctured_nhds_of_is_o
- \+ *lemma* tendsto_lim_of_differentiable_on_punctured_nhds_of_bounded_under



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
- \+ *lemma* right.one_le_pow_of_le
- \+ *lemma* right.pow_le_one_of_le
- \+ *lemma* pow_le_pow_of_le
- \+ *lemma* left.pow_lt_one_of_lt
- \+ *lemma* left.pow_lt_one_iff
- \+ *lemma* right.pow_lt_one_of_lt
- \+ *lemma* right.pow_lt_one_iff

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
- \+ *lemma* sup_inf_distrib_left
- \+ *lemma* sup_inf_distrib_right
- \+ *lemma* inf_sup_distrib_left
- \+ *lemma* inf_sup_distrib_right

Modified src/data/fintype/order.lean
- \+ *def* to_order_bot
- \+ *def* to_order_top
- \+ *def* to_bounded_order
- \- *def* fintype.to_order_bot
- \- *def* fintype.to_order_top
- \- *def* fintype.to_bounded_order

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
- \+ *lemma* to_finset_prod_dvd_prod

Modified src/algebra/big_operators/multiset.lean
- \+ *lemma* prod_dvd_prod_of_dvd



## [2022-01-28 15:19:17](https://github.com/leanprover-community/mathlib/commit/c50a60d)
feat(analysis/convex/specific_functions): sin is strictly concave ([#11688](https://github.com/leanprover-community/mathlib/pull/11688))
#### Estimated changes
Modified src/analysis/convex/specific_functions.lean
- \+ *lemma* strict_concave_on_sin_Icc
- \+ *lemma* strict_concave_on_cos_Icc



## [2022-01-28 15:19:16](https://github.com/leanprover-community/mathlib/commit/92c64c4)
feat(group_theory/nilpotent): add upper_central_series_eq_top_iff_nilpotency_class_le ([#11670](https://github.com/leanprover-community/mathlib/pull/11670))
and the analogue for the lower central series.
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* upper_central_series_eq_top_iff_nilpotency_class_le
- \+ *lemma* lower_central_series_eq_bot_iff_nilpotency_class_le



## [2022-01-28 15:19:15](https://github.com/leanprover-community/mathlib/commit/7a485b1)
feat(topology/continuous_function/algebra): `C(α, β)` is a topological group ([#11665](https://github.com/leanprover-community/mathlib/pull/11665))
This PR proves that `C(α, β)` is a topological group. I had to borrow the fix from [#11229](https://github.com/leanprover-community/mathlib/pull/11229) to avoid a diamond.
#### Estimated changes
Modified src/topology/continuous_function/algebra.lean

Modified src/topology/continuous_function/compact.lean
- \+ *lemma* uniform_inducing_equiv_bounded_of_compact
- \+ *lemma* uniform_embedding_equiv_bounded_of_compact



## [2022-01-28 15:19:14](https://github.com/leanprover-community/mathlib/commit/113ab32)
feat(ring_theory/power_series/basic): API about inv ([#11617](https://github.com/leanprover-community/mathlib/pull/11617))
Also rename protected lemmas
`mul_inv`  to `mul_inv_cancel`
`inv_mul` to `inv_mul_cancel`
#### Estimated changes
Modified src/number_theory/bernoulli.lean

Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* smul_eq_C_mul
- \+ *lemma* zero_inv
- \+ *lemma* one_inv
- \+ *lemma* C_inv
- \+ *lemma* X_inv
- \+ *lemma* smul_inv
- \+ *lemma* smul_eq_C_mul
- \+ *lemma* zero_inv
- \+ *lemma* one_inv
- \+ *lemma* C_inv
- \+ *lemma* X_inv
- \+ *lemma* smul_inv
- \+ *lemma* constant_coeff_coe



## [2022-01-28 15:19:13](https://github.com/leanprover-community/mathlib/commit/36dd6a6)
feat(algebra/squarefree): squarefree iff no square irreducible divisors ([#11544](https://github.com/leanprover-community/mathlib/pull/11544))
#### Estimated changes
Modified src/algebra/squarefree.lean
- \+ *lemma* irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree
- \+ *lemma* squarefree_iff_irreducible_sq_not_dvd_of_ne_zero
- \+ *lemma* squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible
- \+ *lemma* squarefree_iff_prime_sq_not_dvd



## [2022-01-28 15:19:11](https://github.com/leanprover-community/mathlib/commit/fb9c5d3)
feat(cyclotomic/basic): diverse roots of unity lemmas ([#11473](https://github.com/leanprover-community/mathlib/pull/11473))
From flt-regular.
#### Estimated changes
Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* is_root_of_unity_of_root_cyclotomic
- \+/\- *lemma* is_root_cyclotomic
- \+/\- *lemma* is_root_cyclotomic_iff
- \+ *lemma* roots_cyclotomic_nodup
- \+ *lemma* cyclotomic.roots_to_finset_eq_primitive_roots
- \+ *lemma* cyclotomic.roots_eq_primitive_roots_val
- \+/\- *lemma* is_root_cyclotomic
- \+/\- *lemma* is_root_cyclotomic_iff



## [2022-01-28 15:19:10](https://github.com/leanprover-community/mathlib/commit/91a1afb)
feat(algebraic_geometry): The function field is the fraction field of stalks ([#11129](https://github.com/leanprover-community/mathlib/pull/11129))
#### Estimated changes
Modified src/algebraic_geometry/function_field.lean
- \+ *lemma* generic_point_eq_of_is_open_immersion
- \+ *lemma* generic_point_eq_bot_of_affine
- \+ *lemma* is_affine_open.prime_ideal_of_generic_point
- \+ *lemma* function_field_is_fraction_ring_of_is_affine_open



## [2022-01-28 15:19:08](https://github.com/leanprover-community/mathlib/commit/0b6330d)
feat(data/finsupp/interval): Finitely supported functions to a locally finite order are locally finite ([#10930](https://github.com/leanprover-community/mathlib/pull/10930))
... when the codomain itself is locally finite.
This allows getting rid of `finsupp.Iic_finset`.
#### Estimated changes
Modified src/data/finsupp/antidiagonal.lean
- \- *lemma* mem_Iic_finset
- \- *lemma* coe_Iic_finset
- \- *lemma* finite_le_nat
- \- *lemma* finite_lt_nat
- \- *def* Iic_finset

Created src/data/finsupp/interval.lean
- \+ *lemma* mem_range_singleton_apply_iff
- \+ *lemma* mem_range_Icc_apply_iff
- \+ *lemma* card_Icc
- \+ *lemma* card_Ico
- \+ *lemma* card_Ioc
- \+ *lemma* card_Ioo
- \+ *def* range_singleton
- \+ *def* range_Icc

Modified src/ring_theory/power_series/basic.lean



## [2022-01-28 13:31:09](https://github.com/leanprover-community/mathlib/commit/445be96)
fix(tactic/squeeze): `squeeze_simp` providing invalid suggestions ([#11696](https://github.com/leanprover-community/mathlib/pull/11696))
`squeeze_simp` was previously permuting the lemmas passed to `simp`, which caused failures in cases where the lemma order mattered. The fix is to ensure that `squeeze_simp` does not change the order of passed lemmas.
Closes [#3097](https://github.com/leanprover-community/mathlib/pull/3097)
#### Estimated changes
Modified src/meta/expr.lean

Modified src/tactic/squeeze.lean

Modified test/squeeze.lean
- \+ *lemma* k
- \+ *lemma* l
- \+ *def* a
- \+ *def* b
- \+ *def* c
- \+ *def* f



## [2022-01-28 13:31:08](https://github.com/leanprover-community/mathlib/commit/3837abc)
feat(data/list/*): subperm_singleton_iff ([#11680](https://github.com/leanprover-community/mathlib/pull/11680))
#### Estimated changes
Modified src/data/list/count.lean
- \+/\- *lemma* count_pos
- \+ *lemma* one_le_count_iff_mem
- \+/\- *lemma* count_pos

Modified src/data/list/perm.lean
- \+ *lemma* subperm_singleton_iff



## [2022-01-28 13:31:06](https://github.com/leanprover-community/mathlib/commit/1e44add)
feat(order/filter/countable_Inter): review ([#11673](https://github.com/leanprover-community/mathlib/pull/11673))
- drop `_sets` in more names;
- add `filter.of_countable_Inter` and instances for
  `filter.map`/`filter.comap`;
- add docs.
#### Estimated changes
Modified src/order/filter/countable_Inter.lean
- \+ *lemma* countable_sInter_mem
- \+ *lemma* countable_Inter_mem
- \+ *lemma* filter.mem_of_countable_Inter
- \- *lemma* countable_sInter_mem_sets
- \- *lemma* countable_Inter_mem_sets
- \+ *def* filter.of_countable_Inter



## [2022-01-28 13:31:05](https://github.com/leanprover-community/mathlib/commit/680733c)
feat(order/hom/basic): `compl` as a dual order isomorphism ([#11630](https://github.com/leanprover-community/mathlib/pull/11630))
#### Estimated changes
Modified src/order/hom/basic.lean
- \+ *theorem* compl_strict_anti
- \+ *theorem* compl_antitone
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
- \+/\- *lemma* not_is_bot
- \+/\- *lemma* not_is_top
- \+ *lemma* is_bot_to_dual_iff
- \+ *lemma* is_top_to_dual_iff
- \+ *lemma* is_min_to_dual_iff
- \+ *lemma* is_max_to_dual_iff
- \+ *lemma* is_bot_of_dual_iff
- \+ *lemma* is_top_of_dual_iff
- \+ *lemma* is_min_of_dual_iff
- \+ *lemma* is_max_of_dual_iff
- \+ *lemma* is_bot.mono
- \+ *lemma* is_top.mono
- \+ *lemma* is_min.mono
- \+ *lemma* is_max.mono
- \+ *lemma* is_min.not_lt
- \+ *lemma* is_max.not_lt
- \+ *lemma* is_min_iff_forall_not_lt
- \+ *lemma* is_max_iff_forall_not_lt
- \+ *lemma* not_is_min_iff
- \+ *lemma* not_is_max_iff
- \+ *lemma* not_is_min
- \+ *lemma* not_is_max
- \+/\- *lemma* is_top.unique
- \- *lemma* is_top.to_dual
- \- *lemma* is_bot.to_dual
- \+/\- *lemma* not_is_bot
- \+/\- *lemma* not_is_top
- \+/\- *lemma* is_top.unique
- \+ *def* is_min
- \+ *def* is_max

Modified src/order/order_dual.lean



## [2022-01-28 13:31:02](https://github.com/leanprover-community/mathlib/commit/2fa5977)
feat(category_theory/bicategory/natural_transformation): define oplax natural transformations ([#11404](https://github.com/leanprover-community/mathlib/pull/11404))
This PR define oplax natural transformations between oplax functors.
We give a composition and a category structure on oplax natural transformations.
#### Estimated changes
Created src/category_theory/bicategory/natural_transformation.lean
- \+ *lemma* whisker_left_naturality_naturality
- \+ *lemma* whisker_right_naturality_naturality
- \+ *lemma* whisker_left_naturality_comp
- \+ *lemma* whisker_right_naturality_comp
- \+ *lemma* whisker_left_naturality_id
- \+ *lemma* whisker_right_naturality_id
- \+ *lemma* whisker_left_naturality
- \+ *lemma* whisker_right_naturality
- \+ *def* id
- \+ *def* vcomp
- \+ *def* id
- \+ *def* vcomp
- \+ *def* modification_iso.of_components



## [2022-01-28 13:31:00](https://github.com/leanprover-community/mathlib/commit/b9db169)
chore(order/locally_finite): fill in finset interval API ([#11338](https://github.com/leanprover-community/mathlib/pull/11338))
A bunch of statements about finset intervals, mimicking the set interval API and mostly proved using it. `simp` attributes are  chosen as they were for sets. Also some golf.
#### Estimated changes
Modified src/data/finset/locally_finite.lean
- \+/\- *lemma* left_mem_Icc
- \+/\- *lemma* left_mem_Ico
- \+/\- *lemma* right_mem_Icc
- \+/\- *lemma* right_mem_Ioc
- \+ *lemma* Icc_subset_Icc
- \+ *lemma* Ico_subset_Ico
- \+ *lemma* Ioc_subset_Ioc
- \+ *lemma* Ioo_subset_Ioo
- \+ *lemma* Icc_subset_Icc_left
- \+ *lemma* Ico_subset_Ico_left
- \+ *lemma* Ioc_subset_Ioc_left
- \+ *lemma* Ioo_subset_Ioo_left
- \+ *lemma* Icc_subset_Icc_right
- \+ *lemma* Ico_subset_Ico_right
- \+ *lemma* Ioc_subset_Ioc_right
- \+ *lemma* Ioo_subset_Ioo_right
- \+ *lemma* Ico_subset_Ioo_left
- \+ *lemma* Ioc_subset_Ioo_right
- \+ *lemma* Icc_subset_Ico_right
- \+ *lemma* Ioo_subset_Ico_self
- \+ *lemma* Ioo_subset_Ioc_self
- \+ *lemma* Ico_subset_Icc_self
- \+ *lemma* Ioc_subset_Icc_self
- \+ *lemma* Ioo_subset_Icc_self
- \+ *lemma* Icc_subset_Icc_iff
- \+ *lemma* Icc_subset_Ioo_iff
- \+ *lemma* Icc_subset_Ico_iff
- \+ *lemma* Icc_subset_Ioc_iff
- \+ *lemma* Icc_ssubset_Icc_left
- \+ *lemma* Icc_ssubset_Icc_right
- \+/\- *lemma* Ico_self
- \+/\- *lemma* Ioc_self
- \+/\- *lemma* Ioo_self
- \+/\- *lemma* _root_.bdd_below.finite_of_bdd_above
- \+/\- *lemma* Ico_filter_lt_of_le_left
- \+/\- *lemma* Ico_filter_lt_of_right_le
- \+/\- *lemma* Ico_filter_lt_of_le_right
- \+/\- *lemma* Ico_filter_le_of_right_le
- \+/\- *lemma* filter_lt_lt_eq_Ioo
- \+/\- *lemma* filter_lt_le_eq_Ioc
- \+/\- *lemma* filter_le_lt_eq_Ico
- \+/\- *lemma* filter_le_le_eq_Icc
- \+/\- *lemma* filter_lt_eq_Ioi
- \+/\- *lemma* filter_le_eq_Ici
- \+/\- *lemma* filter_gt_eq_Iio
- \+/\- *lemma* filter_ge_eq_Iic
- \+ *lemma* Icc_subset_Ici_self
- \+ *lemma* Ico_subset_Ici_self
- \+ *lemma* Ioc_subset_Ici_self
- \+ *lemma* Ioo_subset_Ici_self
- \+ *lemma* Ioi_subset_Ici_self
- \+ *lemma* Ioc_subset_Ioi_self
- \+ *lemma* Ioo_subset_Ioi_self
- \+/\- *lemma* _root_.bdd_below.finite
- \+ *lemma* Icc_subset_Iic_self
- \+ *lemma* Ico_subset_Iic_self
- \+ *lemma* Ioc_subset_Iic_self
- \+ *lemma* Ioo_subset_Iic_self
- \+ *lemma* Iio_subset_Iic_self
- \+ *lemma* Ico_subset_Iio_self
- \+ *lemma* Ioo_subset_Iio_self
- \+/\- *lemma* _root_.bdd_above.finite
- \+/\- *lemma* Icc_erase_left
- \+/\- *lemma* Icc_erase_right
- \+ *lemma* Ico_erase_left
- \+ *lemma* Ioc_erase_right
- \+ *lemma* Icc_diff_both
- \+/\- *lemma* Ico_insert_right
- \+ *lemma* Ioc_insert_left
- \+/\- *lemma* Ioo_insert_left
- \+ *lemma* Ioo_insert_right
- \+ *lemma* Icc_diff_Ico_self
- \+ *lemma* Icc_diff_Ioc_self
- \+ *lemma* Icc_diff_Ioo_self
- \+ *lemma* Ico_diff_Ioo_self
- \+ *lemma* Ioc_diff_Ioo_self
- \+ *lemma* Icc_eq_cons_Ico
- \+ *lemma* Icc_eq_cons_Ioc
- \+ *lemma* card_Ioo_eq_card_Ioc_sub_one
- \+ *lemma* Ici_erase
- \+ *lemma* Ioi_insert
- \+ *lemma* Ici_eq_cons_Ioi
- \+ *lemma* Iic_erase
- \+ *lemma* Iio_insert
- \+ *lemma* Iic_eq_cons_Iio
- \+/\- *lemma* image_add_right_Icc
- \+/\- *lemma* image_add_right_Ico
- \+/\- *lemma* image_add_right_Ioc
- \+/\- *lemma* image_add_right_Ioo
- \+/\- *lemma* Ico_self
- \+/\- *lemma* Ioc_self
- \+/\- *lemma* Ioo_self
- \+/\- *lemma* left_mem_Icc
- \+/\- *lemma* left_mem_Ico
- \+/\- *lemma* right_mem_Icc
- \+/\- *lemma* right_mem_Ioc
- \+/\- *lemma* Ico_filter_lt_of_le_left
- \+/\- *lemma* Ico_filter_lt_of_right_le
- \+/\- *lemma* Ico_filter_lt_of_le_right
- \+/\- *lemma* Ico_filter_le_of_right_le
- \+/\- *lemma* _root_.bdd_below.finite_of_bdd_above
- \+/\- *lemma* filter_lt_lt_eq_Ioo
- \+/\- *lemma* filter_lt_le_eq_Ioc
- \+/\- *lemma* filter_le_lt_eq_Ico
- \+/\- *lemma* filter_le_le_eq_Icc
- \+/\- *lemma* filter_lt_eq_Ioi
- \+/\- *lemma* filter_le_eq_Ici
- \+/\- *lemma* filter_gt_eq_Iio
- \+/\- *lemma* filter_ge_eq_Iic
- \+/\- *lemma* Icc_erase_left
- \+/\- *lemma* Icc_erase_right
- \+/\- *lemma* Ico_insert_right
- \+/\- *lemma* Ioo_insert_left
- \+/\- *lemma* _root_.bdd_below.finite
- \+/\- *lemma* _root_.bdd_above.finite
- \+/\- *lemma* image_add_right_Icc
- \+/\- *lemma* image_add_right_Ico
- \+/\- *lemma* image_add_right_Ioc
- \+/\- *lemma* image_add_right_Ioo
- \+/\- *def* _root_.set.fintype_of_mem_bounds
- \+/\- *def* _root_.set.fintype_of_mem_bounds

Modified src/order/locally_finite.lean
- \+/\- *lemma* mem_Icc
- \+/\- *lemma* mem_Ico
- \+/\- *lemma* mem_Ioc
- \+/\- *lemma* mem_Ioo
- \+/\- *lemma* coe_Icc
- \+/\- *lemma* coe_Ico
- \+/\- *lemma* coe_Ioc
- \+/\- *lemma* coe_Ioo
- \+/\- *lemma* mem_Ici
- \+/\- *lemma* mem_Ioi
- \+/\- *lemma* mem_Iic
- \+/\- *lemma* mem_Iio
- \+/\- *lemma* mem_Icc
- \+/\- *lemma* mem_Ico
- \+/\- *lemma* mem_Ioc
- \+/\- *lemma* mem_Ioo
- \+/\- *lemma* coe_Icc
- \+/\- *lemma* coe_Ico
- \+/\- *lemma* coe_Ioc
- \+/\- *lemma* coe_Ioo
- \+/\- *lemma* mem_Ici
- \+/\- *lemma* mem_Ioi
- \+/\- *lemma* mem_Iic
- \+/\- *lemma* mem_Iio
- \- *theorem* Ico_subset_Ico



## [2022-01-28 13:03:39](https://github.com/leanprover-community/mathlib/commit/924aab1)
feat(ring_theory/polynomial/eisenstein): add miscellaneous results about Eisenstein polynomials ([#11697](https://github.com/leanprover-community/mathlib/pull/11697))
Miscellaneous results about Eisenstein polynomials
From flt-regular.
#### Estimated changes
Created src/ring_theory/polynomial/eisenstein.lean
- \+ *lemma* map
- \+ *lemma* exists_mem_adjoin_mul_eq_pow_nat_degree
- \+ *lemma* exists_mem_adjoin_mul_eq_pow_nat_degree_le
- \+ *lemma* pow_nat_degree_le_of_root_of_monic_mem
- \+ *lemma* pow_nat_degree_le_of_aeval_zero_of_monic_mem_map
- \+ *lemma* is_weakly_eisenstein_at
- \+ *lemma* coeff_mem
- \+ *lemma* irreducible



## [2022-01-28 11:11:22](https://github.com/leanprover-community/mathlib/commit/e290b29)
feat(data/quot): add subsingleton instances ([#11668](https://github.com/leanprover-community/mathlib/pull/11668))
#### Estimated changes
Modified src/data/quot.lean



## [2022-01-28 08:38:09](https://github.com/leanprover-community/mathlib/commit/bf347f9)
feat(algebraic_geometry): Fiber products of schemes ([#10605](https://github.com/leanprover-community/mathlib/pull/10605))
#### Estimated changes
Modified src/algebraic_geometry/gluing.lean
- \+ *lemma* hom_ext

Modified src/algebraic_geometry/pullbacks.lean
- \+ *lemma* pullback_fst_ι_to_V_fst
- \+ *lemma* pullback_fst_ι_to_V_snd
- \+ *lemma* lift_comp_ι
- \+ *lemma* pullback_p1_iso_hom_fst
- \+ *lemma* pullback_p1_iso_hom_snd
- \+ *lemma* pullback_p1_iso_inv_fst
- \+ *lemma* pullback_p1_iso_inv_snd
- \+ *lemma* pullback_p1_iso_hom_ι
- \+ *lemma* has_pullback_of_cover
- \+ *lemma* affine_affine_has_pullback
- \+ *def* pullback_fst_ι_to_V
- \+ *def* pullback_p1_iso
- \+ *def* glued_is_limit



## [2022-01-28 07:26:07](https://github.com/leanprover-community/mathlib/commit/67dcdef)
feat(data/mv_polynomial/derivation): derivations of `mv_polynomial`s ([#9145](https://github.com/leanprover-community/mathlib/pull/9145))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean

Created src/data/mv_polynomial/derivation.lean
- \+ *lemma* mk_derivationₗ_monomial
- \+ *lemma* mk_derivationₗ_C
- \+ *lemma* mk_derivationₗ_X
- \+ *lemma* derivation_C
- \+ *lemma* derivation_C_mul
- \+ *lemma* derivation_eq_on_supported
- \+ *lemma* derivation_eq_of_forall_mem_vars
- \+ *lemma* derivation_eq_zero_of_forall_mem_vars
- \+ *lemma* derivation_ext
- \+ *lemma* leibniz_iff_X
- \+ *lemma* mk_derivation_X
- \+ *lemma* mk_derivation_monomial
- \+ *def* mk_derivationₗ
- \+ *def* mk_derivation
- \+ *def* mk_derivation_equiv

Modified src/data/mv_polynomial/pderiv.lean
- \+/\- *lemma* pderiv_monomial
- \+/\- *lemma* pderiv_C
- \+/\- *lemma* pderiv_X
- \+/\- *lemma* pderiv_X_self
- \+ *lemma* pderiv_X_of_ne
- \+/\- *lemma* pderiv_eq_zero_of_not_mem_vars
- \+/\- *lemma* pderiv_C_mul
- \+/\- *lemma* pderiv_monomial
- \+/\- *lemma* pderiv_C
- \+/\- *lemma* pderiv_eq_zero_of_not_mem_vars
- \+/\- *lemma* pderiv_X
- \+/\- *lemma* pderiv_X_self
- \- *lemma* pderiv_monomial_mul
- \+/\- *lemma* pderiv_C_mul
- \- *lemma* pderiv_pow
- \- *lemma* pderiv_nat_cast
- \+/\- *def* pderiv
- \+/\- *def* pderiv

Modified src/ring_theory/derivation.lean
- \+ *lemma* map_sum

Modified src/ring_theory/polynomial/bernstein.lean



## [2022-01-28 06:58:36](https://github.com/leanprover-community/mathlib/commit/6687cf1)
feat(group_theory/sylow): `fintype (sylow p H)` from `fintype (sylow p G)` ([#11664](https://github.com/leanprover-community/mathlib/pull/11664))
If the number of Sylow `p`-subgroups of `G` is finite, then the number of Sylow `p`-subgroups of `H` is finite.
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+ *lemma* ker_is_p_group_of_injective

Modified src/group_theory/sylow.lean
- \+ *lemma* sylow.exists_comap_eq_of_ker_is_p_group
- \+ *lemma* sylow.exists_comap_eq_of_injective
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

Created src/order/complete_lattice_intervals.lean
- \+ *lemma* subset_Sup_def
- \+ *lemma* subset_Sup_of_within
- \+ *lemma* subset_Inf_def
- \+ *lemma* subset_Inf_of_within
- \+ *lemma* Sup_within_of_ord_connected
- \+ *lemma* Inf_within_of_ord_connected

Modified src/order/conditionally_complete_lattice.lean
- \- *lemma* subset_Sup_def
- \- *lemma* subset_Sup_of_within
- \- *lemma* subset_Inf_def
- \- *lemma* subset_Inf_of_within
- \- *lemma* Sup_within_of_ord_connected
- \- *lemma* Inf_within_of_ord_connected

Modified src/topology/algebra/ordered/intermediate_value.lean



## [2022-01-27 23:05:41](https://github.com/leanprover-community/mathlib/commit/21cea47)
feat(analysis/special_functions/log): log of natural power ([#11685](https://github.com/leanprover-community/mathlib/pull/11685))
The rpow versions are already present, but the natural/integer versions can also be very helpful (eg for squares).
#### Estimated changes
Modified src/analysis/special_functions/log.lean
- \+ *lemma* log_pow
- \+ *lemma* log_zpow



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
- \+ *lemma* to_refl_trans_gen
- \+ *lemma* mono
- \+ *lemma* trans_gen.mono
- \+ *lemma* trans_gen.swap
- \+ *lemma* trans_gen_swap
- \+ *lemma* refl_trans_gen.swap
- \+ *lemma* refl_trans_gen_swap
- \- *lemma* refl_gen.to_refl_trans_gen

Renamed src/order/succ_pred.lean to src/order/succ_pred/basic.lean
- \+/\- *lemma* succ.rec
- \+/\- *lemma* pred.rec
- \+/\- *lemma* succ.rec
- \+/\- *lemma* pred.rec

Created src/order/succ_pred/relation.lean
- \+ *lemma* refl_trans_gen_of_succ_of_le
- \+ *lemma* refl_trans_gen_of_succ_of_ge
- \+ *lemma* trans_gen_of_succ_of_lt
- \+ *lemma* trans_gen_of_succ_of_gt
- \+ *lemma* refl_trans_gen_of_succ
- \+ *lemma* trans_gen_of_succ_of_ne
- \+ *lemma* trans_gen_of_succ_of_reflexive
- \+ *lemma* refl_trans_gen_of_pred_of_ge
- \+ *lemma* refl_trans_gen_of_pred_of_le
- \+ *lemma* trans_gen_of_pred_of_gt
- \+ *lemma* trans_gen_of_pred_of_lt
- \+ *lemma* refl_trans_gen_of_pred
- \+ *lemma* trans_gen_of_pred_of_ne
- \+ *lemma* trans_gen_of_pred_of_reflexive

Modified src/set_theory/ordinal.lean



## [2022-01-27 23:05:38](https://github.com/leanprover-community/mathlib/commit/0a721cc)
feat(data/nat): a predicate for prime powers ([#11313](https://github.com/leanprover-community/mathlib/pull/11313))
Adds a predicate for prime powers, in preparation for defining the von Mangoldt function.
cc @stuart-presnell since you might be needing this material soon, and @jcommelin if you have thoughts about generalising this to rings/UFDs?
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* associated.of_pow_associated_of_prime
- \+ *lemma* associated.of_pow_associated_of_prime'

Created src/algebra/is_prime_pow.lean
- \+ *lemma* is_prime_pow_def
- \+ *lemma* is_prime_pow_iff_pow_succ
- \+ *lemma* not_is_prime_pow_zero
- \+ *lemma* not_is_prime_pow_one
- \+ *lemma* prime.is_prime_pow
- \+ *lemma* is_prime_pow.pow
- \+ *lemma* is_prime_pow.ne_one
- \+ *lemma* eq_of_prime_pow_eq
- \+ *lemma* eq_of_prime_pow_eq'
- \+ *lemma* is_prime_pow_nat_iff
- \+ *lemma* is_prime_pow_nat_iff_bounded
- \+ *lemma* is_prime_pow.min_fac_pow_factorization_eq
- \+ *lemma* is_prime_pow_of_min_fac_pow_factorization_eq
- \+ *lemma* is_prime_pow_iff_min_fac_pow_factorization_eq
- \+ *lemma* is_prime_pow.dvd
- \+ *lemma* is_prime_pow_iff_unique_prime_dvd
- \+ *lemma* is_prime_pow.two_le
- \+ *theorem* is_prime_pow.ne_zero
- \+ *theorem* is_prime_pow.pos
- \+ *theorem* is_prime_pow.one_lt
- \+ *def* is_prime_pow

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
Created archive/100-theorems-list/37_solution_of_cubic.lean
- \+ *lemma* cube_root_of_unity_sum
- \+ *lemma* cubic_basic_eq_zero_iff
- \+ *lemma* cubic_monic_eq_zero_iff
- \+ *lemma* cubic_eq_zero_iff_of_p_eq_zero
- \+ *theorem* cubic_eq_zero_iff

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
- \+ *theorem* sup_eq_lsub_iff_succ
- \+ *theorem* sup_eq_lsub_iff_lt_sup
- \+ *theorem* bsup_eq_blsub_iff_succ
- \+ *theorem* bsup_eq_blsub_iff_lt_bsup
- \- *theorem* sup_eq_lsub
- \- *theorem* bsup_eq_blsub



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
- \+ *theorem* mem_inf_principal'



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
- \+ *lemma* factorization_eq_zero_of_non_prime
- \+ *lemma* prime_pow_dvd_iff_le_factorization
- \+ *lemma* exists_factorization_lt_of_lt
- \+ *lemma* div_factorization_eq_tsub_of_dvd
- \+ *lemma* dvd_iff_div_factorization_eq_tsub
- \+ *lemma* pow_factorization_dvd
- \+ *lemma* dvd_iff_prime_pow_dvd_dvd



## [2022-01-26 20:14:54](https://github.com/leanprover-community/mathlib/commit/97e01cd)
feat(group_theory/free_abelian_group_finsupp): various equiv.of_free_*_group lemmas ([#11469](https://github.com/leanprover-community/mathlib/pull/11469))
Namely `equiv.of_free_abelian_group_linear_equiv`,
`equiv.of_free_abelian_group_equiv` and `equiv.of_free_group_equiv`
#### Estimated changes
Modified src/group_theory/free_abelian_group_finsupp.lean
- \+ *def* equiv.of_free_abelian_group_linear_equiv
- \+ *def* equiv.of_free_abelian_group_equiv
- \+ *def* equiv.of_free_group_equiv
- \+ *def* equiv.of_is_free_group_equiv

Modified src/group_theory/free_group.lean



## [2022-01-26 17:10:48](https://github.com/leanprover-community/mathlib/commit/8fbc009)
feat(data/{dfinsupp,finsupp}/basic): `fun_like` instances for `Π₀ i, α i` and `ι →₀ α` ([#11667](https://github.com/leanprover-community/mathlib/pull/11667))
This provides the `fun_like` instances for `finsupp` and `dfinsupp` and deprecates the lemmas that are now provided by the `fun_like` API.
#### Estimated changes
Modified src/data/dfinsupp/basic.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coe_fn_injective
- \+/\- *lemma* coe_fn_injective
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff

Modified src/data/finsupp/basic.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coe_fn_inj
- \+/\- *lemma* coe_fn_injective
- \+/\- *lemma* congr_fun
- \+/\- *lemma* coe_fn_injective
- \+/\- *lemma* coe_fn_inj
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* congr_fun



## [2022-01-26 17:10:46](https://github.com/leanprover-community/mathlib/commit/c447a31)
feat(algebraic_geometry): Stalk is localization of affine open.  ([#11640](https://github.com/leanprover-community/mathlib/pull/11640))
#### Estimated changes
Modified src/algebra/category/CommRing/basic.lean
- \+ *lemma* CommRing_iso_to_ring_equiv_to_ring_hom
- \+ *lemma* CommRing_iso_to_ring_equiv_symm_to_ring_hom

Modified src/algebraic_geometry/AffineScheme.lean
- \+ *lemma* is_affine_open.from_Spec_prime_ideal_of
- \+ *lemma* is_affine_open.is_localization_stalk_aux
- \+ *lemma* is_affine_open.is_localization_stalk
- \+ *def* is_affine_open.prime_ideal_of

Modified src/algebraic_geometry/Scheme.lean
- \+ *lemma* id_val_base
- \+ *lemma* id_coe_base
- \+ *lemma* id_app
- \+ *lemma* app_eq
- \+ *lemma* inv_val_c_app

Modified src/algebraic_geometry/Spec.lean

Modified src/algebraic_geometry/properties.lean
- \+ *lemma* is_reduced_of_is_affine_is_reduced
- \+ *lemma* reduce_to_affine_nbhd
- \+ *lemma* is_integral_of_is_affine_is_domain

Modified src/ring_theory/localization.lean
- \+ *lemma* mk'_eq_zero_iff
- \+ *lemma* non_zero_divisors_le_comap
- \+ *lemma* map_non_zero_divisors_le
- \+ *lemma* is_fraction_ring_of_is_localization
- \+ *lemma* nontrivial
- \+ *lemma* is_fraction_ring_of_is_domain_of_is_localization

Modified src/topology/category/Top/opens.lean
- \+ *lemma* adjunction_counit_app_self

Modified src/topology/sheaves/stalks.lean
- \+ *lemma* stalk_open_algebra_map



## [2022-01-26 15:22:43](https://github.com/leanprover-community/mathlib/commit/b8fcac5)
feat(data/nat/basic): three small `dvd_iff...` lemmas ([#11669](https://github.com/leanprover-community/mathlib/pull/11669))
Three biconditionals for proving `d ∣ n`
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* dvd_iff_div_mul_eq
- \+ *lemma* dvd_iff_le_div_mul
- \+ *lemma* dvd_iff_dvd_dvd



## [2022-01-26 13:30:01](https://github.com/leanprover-community/mathlib/commit/c5a8a81)
refactor(topology/algebra/uniform_group): Use `to_additive`. ([#11662](https://github.com/leanprover-community/mathlib/pull/11662))
This PR refactors `topology/algebra/uniform_group` to use `to_additive`.
#### Estimated changes
Modified src/topology/algebra/group_completion.lean

Modified src/topology/algebra/uniform_group.lean
- \+ *lemma* uniform_continuous_div
- \+ *lemma* uniform_continuous.div
- \+ *lemma* uniform_continuous.inv
- \+ *lemma* uniform_continuous_inv
- \+ *lemma* uniform_continuous.mul
- \+ *lemma* uniform_continuous_mul
- \+ *lemma* uniformity_translate_mul
- \+ *lemma* uniform_embedding_translate_mul
- \+ *lemma* uniformity_eq_comap_nhds_one
- \+/\- *lemma* group_separation_rel
- \+ *lemma* uniform_continuous_of_tendsto_one
- \+ *lemma* monoid_hom.uniform_continuous_of_continuous_at_one
- \+ *lemma* uniform_continuous_monoid_hom_of_continuous
- \+ *lemma* cauchy_seq.mul
- \+ *lemma* uniformity_eq_comap_nhds_one'
- \+ *lemma* topological_group_is_uniform
- \+ *lemma* topological_group.separated_iff_one_closed
- \+ *lemma* topological_group.separated_of_one_sep
- \+ *lemma* uniform_group.to_uniform_space_eq
- \+ *lemma* tendsto_div_comap_self
- \- *lemma* uniform_continuous_sub
- \- *lemma* uniform_continuous.sub
- \- *lemma* uniform_continuous.neg
- \- *lemma* uniform_continuous_neg
- \- *lemma* uniform_continuous.add
- \- *lemma* uniform_continuous_add
- \- *lemma* uniformity_translate
- \- *lemma* uniform_embedding_translate
- \- *lemma* uniformity_eq_comap_nhds_zero
- \+/\- *lemma* group_separation_rel
- \- *lemma* uniform_continuous_of_tendsto_zero
- \- *lemma* add_monoid_hom.uniform_continuous_of_continuous_at_zero
- \- *lemma* uniform_continuous_of_continuous
- \- *lemma* cauchy_seq.add
- \- *lemma* uniformity_eq_comap_nhds_zero'
- \- *lemma* topological_add_group_is_uniform
- \- *lemma* topological_add_group.separated_iff_zero_closed
- \- *lemma* topological_add_group.separated_of_zero_sep
- \- *lemma* to_uniform_space_eq
- \- *lemma* tendsto_sub_comap_self
- \+ *theorem* uniform_group.mk'
- \- *theorem* uniform_add_group.mk'

Modified src/topology/algebra/uniform_ring.lean



## [2022-01-26 13:30:00](https://github.com/leanprover-community/mathlib/commit/5472f0a)
feat(group_theory/subgroup/basic): add lemmas related to map, comap, normalizer ([#11637](https://github.com/leanprover-community/mathlib/pull/11637))
which are useful when `H < K < G` and one needs to move from `subgroup
G` to `subgroup K`
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+ *lemma* comap_subtype

Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* comap_subtype_self_eq_top
- \+ *lemma* comap_normalizer_eq_of_injective_of_le_range
- \+ *lemma* comap_subtype_normalizer_eq



## [2022-01-26 13:29:59](https://github.com/leanprover-community/mathlib/commit/2b25723)
feat(group_theory/sylow): add characteristic_of_normal ([#11636](https://github.com/leanprover-community/mathlib/pull/11636))
A normal sylow subgroup is characteristic.
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *lemma* sylow.smul_eq_of_normal
- \+ *lemma* subsingleton_of_normal
- \+ *lemma* characteristic_of_normal



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
- \+ *lemma* orthonormal.comp_linear_isometry
- \+ *lemma* orthonormal.comp_linear_isometry_equiv
- \+ *lemma* linear_map.coe_isometry_of_orthonormal
- \+ *lemma* linear_map.isometry_of_orthonormal_to_linear_map
- \+ *lemma* linear_equiv.coe_isometry_of_orthonormal
- \+ *lemma* linear_equiv.isometry_of_orthonormal_to_linear_equiv
- \+ *lemma* orthonormal.equiv_to_linear_equiv
- \+ *lemma* orthonormal.equiv_apply
- \+ *lemma* orthonormal.equiv_refl
- \+ *lemma* orthonormal.equiv_symm
- \+ *lemma* orthonormal.equiv_trans
- \+ *lemma* orthonormal.map_equiv
- \+ *def* linear_map.isometry_of_orthonormal
- \+ *def* linear_equiv.isometry_of_orthonormal
- \+ *def* orthonormal.equiv



## [2022-01-26 13:29:57](https://github.com/leanprover-community/mathlib/commit/631f339)
feat(measure_theory/measure/haar_lebesgue): a density point for closed balls is a density point for rescalings of arbitrary sets ([#11620](https://github.com/leanprover-community/mathlib/pull/11620))
Consider a point `x` in a finite-dimensional real vector space with a Haar measure, at which a set `s` has density one, with respect to closed balls (i.e., a Lebesgue density point of `s`). Then `s` has also density one at `x` with respect to any measurable set `t`: the proportion of points in `s` belonging to a rescaled copy `{x} + r • t` of `t` tends to one as `r` tends to zero. In particular, `s ∩ ({x} + r • t)` is nonempty for small enough `r`.
#### Estimated changes
Modified src/measure_theory/measure/haar_lebesgue.lean
- \+ *lemma* add_haar_ball_mul_of_pos
- \+ *lemma* add_haar_ball_mul
- \+ *lemma* add_haar_closed_ball_mul_of_pos
- \+ *lemma* add_haar_closed_ball_mul
- \+ *lemma* add_haar_singleton_add_smul_div_singleton_add_smul
- \+ *lemma* tendsto_add_haar_inter_smul_zero_of_density_zero_aux1
- \+ *lemma* tendsto_add_haar_inter_smul_zero_of_density_zero_aux2
- \+ *lemma* tendsto_add_haar_inter_smul_zero_of_density_zero
- \+ *lemma* tendsto_add_haar_inter_smul_one_of_density_one_aux
- \+ *lemma* tendsto_add_haar_inter_smul_one_of_density_one
- \+ *lemma* eventually_nonempty_inter_smul_of_density_one

Modified src/topology/metric_space/basic.lean
- \+ *lemma* Union_inter_closed_ball_nat



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
- \+ *lemma* ne_zero_of_norm_ne_zero
- \+ *lemma* ne_zero_of_mem_sphere
- \+ *lemma* ne_zero_of_mem_unit_sphere
- \+ *lemma* ne_zero_of_nnnorm_ne_zero
- \+ *lemma* norm_ne_zero_iff
- \+ *lemma* nnnorm_ne_zero_iff
- \- *lemma* ne_zero_of_norm_pos
- \- *lemma* nonzero_of_mem_sphere
- \- *lemma* nonzero_of_mem_unit_sphere

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* ne_neg_of_mem_sphere
- \+/\- *lemma* ne_neg_of_mem_sphere

Modified src/analysis/normed_space/spectrum.lean

Modified src/analysis/seminorm.lean
- \+ *lemma* balanced_univ
- \+ *lemma* absorbs.mono
- \+ *lemma* absorbs.mono_left
- \+ *lemma* absorbs.mono_right
- \+ *lemma* absorbs.union
- \+ *lemma* absorbs_union
- \+ *lemma* absorbent.absorbs
- \+ *lemma* balanced.smul_mono
- \+ *lemma* absorbs.inter
- \+ *lemma* absorbs_inter
- \+ *lemma* absorbent_univ
- \+/\- *lemma* balanced_zero_union_interior
- \+ *lemma* absorbs_zero_iff
- \+ *lemma* absorbent.zero_mem
- \+/\- *lemma* mem_ball
- \+/\- *lemma* balanced_ball_zero
- \+ *lemma* coe_norm_seminorm
- \+ *lemma* ball_norm_seminorm
- \+/\- *lemma* absorbent_ball_zero
- \+/\- *lemma* absorbent_ball
- \+/\- *lemma* balanced_ball_zero
- \+ *lemma* gauge_mono
- \+/\- *lemma* exists_lt_of_gauge_lt
- \+ *lemma* gauge_zero'
- \+ *lemma* gauge_empty
- \+ *lemma* gauge_of_subset_zero
- \+/\- *lemma* gauge_le_of_mem
- \+ *lemma* gauge_le_eq
- \+ *lemma* gauge_lt_eq'
- \+ *lemma* gauge_lt_eq
- \+ *lemma* convex.gauge_le
- \+ *lemma* balanced.star_convex
- \+ *lemma* le_gauge_of_not_mem
- \+/\- *lemma* one_le_gauge_of_not_mem
- \+ *lemma* gauge_smul_left_of_nonneg
- \+ *lemma* gauge_smul_left
- \+/\- *lemma* interior_subset_gauge_lt_one
- \+/\- *lemma* gauge_lt_one_eq_self_of_open
- \+/\- *lemma* gauge_lt_one_of_mem_of_open
- \+ *lemma* gauge_lt_of_mem_smul
- \+ *lemma* gauge_seminorm_lt_one_of_open
- \+ *lemma* gauge_unit_ball
- \+ *lemma* smul_unit_ball
- \+ *lemma* gauge_ball
- \+ *lemma* mul_gauge_le_norm
- \- *lemma* balanced.univ
- \+/\- *lemma* balanced_zero_union_interior
- \+/\- *lemma* mem_ball
- \+/\- *lemma* balanced_ball_zero
- \+/\- *lemma* absorbent_ball_zero
- \+/\- *lemma* absorbent_ball
- \+/\- *lemma* exists_lt_of_gauge_lt
- \+/\- *lemma* gauge_le_of_mem
- \- *lemma* gauge_le_one_eq'
- \- *lemma* gauge_le_one_eq
- \- *lemma* gauge_lt_one_eq'
- \- *lemma* gauge_lt_one_eq
- \- *lemma* convex.gauge_le_one
- \+/\- *lemma* interior_subset_gauge_lt_one
- \+/\- *lemma* gauge_lt_one_eq_self_of_open
- \+/\- *lemma* gauge_lt_one_of_mem_of_open
- \+/\- *lemma* one_le_gauge_of_not_mem
- \- *lemma* seminorm.gauge_ball
- \+ *def* norm_seminorm
- \+/\- *def* gauge_seminorm
- \+/\- *def* gauge_seminorm

Modified src/geometry/manifold/instances/sphere.lean



## [2022-01-26 13:29:53](https://github.com/leanprover-community/mathlib/commit/573ca83)
feat(analysis/seminorm): add some lemmas for seminorm balls ([#11471](https://github.com/leanprover-community/mathlib/pull/11471))
Add some lemmas for seminorm balls.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* ball_mono
- \+ *lemma* ball_antitone
- \+ *lemma* ball_add_ball_subset
- \+ *lemma* ball_smul_ball
- \+ *lemma* neg_ball
- \+ *lemma* smul_ball_preimage



## [2022-01-26 13:29:52](https://github.com/leanprover-community/mathlib/commit/07d8ca6)
feat(combinatorics/configuration): Formula for cardinality of a projective plane ([#11462](https://github.com/leanprover-community/mathlib/pull/11462))
This PR proves the formula for the cardinality of a projective plane in terms of the order.
#### Estimated changes
Modified src/combinatorics/configuration.lean
- \+ *lemma* card_points
- \+ *lemma* card_lines



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

Created src/algebra/order/hom/monoid.lean
- \+ *lemma* ext
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_mk
- \+ *lemma* mk_coe
- \+ *lemma* coe_monoid_hom
- \+ *lemma* coe_order_hom
- \+ *lemma* to_monoid_hom_injective
- \+ *lemma* to_order_hom_injective
- \+ *lemma* coe_id
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* coe_comp_monoid_hom
- \+ *lemma* coe_comp_order_hom
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *lemma* coe_one
- \+ *lemma* one_apply
- \+ *lemma* one_comp
- \+ *lemma* comp_one
- \+ *lemma* coe_mul
- \+ *lemma* mul_apply
- \+ *lemma* mul_comp
- \+ *lemma* comp_mul
- \+ *lemma* to_monoid_hom_eq_coe
- \+ *lemma* to_order_hom_eq_coe
- \+ *lemma* ext
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_mk
- \+ *lemma* mk_coe
- \+ *lemma* coe_monoid_with_zero_hom
- \+ *lemma* coe_order_monoid_hom
- \+ *lemma* to_order_monoid_hom_injective
- \+ *lemma* to_monoid_with_zero_hom_injective
- \+ *lemma* coe_id
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* coe_comp_monoid_with_zero_hom
- \+ *lemma* coe_comp_order_monoid_hom
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *lemma* coe_mul
- \+ *lemma* mul_apply
- \+ *lemma* mul_comp
- \+ *lemma* comp_mul
- \+ *lemma* to_monoid_with_zero_hom_eq_coe
- \+ *lemma* to_order_monoid_hom_eq_coe
- \+ *def* to_order_hom
- \+ *def* comp
- \+ *def* mk'
- \+ *def* to_order_monoid_hom
- \+ *def* comp

Modified src/order/hom/basic.lean



## [2022-01-26 11:25:56](https://github.com/leanprover-community/mathlib/commit/20aae83)
feat(order/hom/lattice): Lattice homomorphisms ([#11610](https://github.com/leanprover-community/mathlib/pull/11610))
This defines (bounded) lattice homomorphisms using the `fun_like` along with weaker homomorphisms that only preserve `sup`, `inf`, `top`, `bot`.
#### Estimated changes
Created src/order/hom/lattice.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_top
- \+ *lemma* top_apply
- \+ *lemma* coe_inf
- \+ *lemma* inf_apply
- \+ *lemma* coe_sup
- \+ *lemma* sup_apply
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_bot
- \+ *lemma* bot_apply
- \+ *lemma* coe_inf
- \+ *lemma* inf_apply
- \+ *lemma* coe_sup
- \+ *lemma* sup_apply
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_sup
- \+ *lemma* sup_apply
- \+ *lemma* coe_const
- \+ *lemma* const_apply
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_inf
- \+ *lemma* inf_apply
- \+ *lemma* coe_const
- \+ *lemma* const_apply
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *def* const
- \+ *def* const
- \+ *def* to_inf_hom
- \+ *def* to_top_hom
- \+ *def* to_bot_hom



## [2022-01-26 10:04:22](https://github.com/leanprover-community/mathlib/commit/09c6ce8)
feat(group_theory/subgroup/basic): add normalizer_condition definition ([#11587](https://github.com/leanprover-community/mathlib/pull/11587))
and an equivalent formula that is a bit easier to work with.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* _root_.normalizer_condition_iff_only_full_group_self_normalizing
- \+ *def* _root_.normalizer_condition



## [2022-01-26 09:10:25](https://github.com/leanprover-community/mathlib/commit/c294e4b)
feat(topology/*): replace some `a < b` assumptions with `a ≠ b` ([#11650](https://github.com/leanprover-community/mathlib/pull/11650))
#### Estimated changes
Modified src/analysis/box_integral/box/basic.lean
- \+ *lemma* lower_ne_upper

Modified src/analysis/calculus/extend_deriv.lean

Modified src/analysis/calculus/local_extr.lean

Modified src/analysis/normed_space/basic.lean

Modified src/analysis/special_functions/trigonometric/basic.lean

Modified src/measure_theory/integral/interval_integral.lean

Modified src/topology/algebra/ordered/basic.lean
- \+/\- *lemma* closure_Ioo
- \+/\- *lemma* closure_Ioc
- \+/\- *lemma* closure_Ico
- \+/\- *lemma* closure_Ioo
- \+/\- *lemma* closure_Ioc
- \+/\- *lemma* closure_Ico

Modified src/topology/algebra/ordered/extend_from.lean



## [2022-01-25 23:46:56](https://github.com/leanprover-community/mathlib/commit/20a461f)
feat(algebra/big_operators/order): The size of a finset of disjoint finsets is less than the size of its union ([#11654](https://github.com/leanprover-community/mathlib/pull/11654))
Prove `card_le_card_bUnion`, its corollary `card_le_card_bUnion_add_card_fiber` where we drop the nonemptiness condition in exchange of a `+` card of the fiber of `∅` on the RHS, and its useful special case `card_le_card_bUnion_add_one`.
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+ *lemma* card_le_card_bUnion
- \+ *lemma* card_le_card_bUnion_add_card_fiber
- \+ *lemma* card_le_card_bUnion_add_one



## [2022-01-25 22:24:52](https://github.com/leanprover-community/mathlib/commit/b237af5)
refactor(set_theory/ordinal_arithmetic): Rename `lsub_le_iff_lt` to `lsub_le` ([#11661](https://github.com/leanprover-community/mathlib/pull/11661))
This way, it directly corresponds to `sup_le`. Ditto for `blsub_le_iff_lt`.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* lsub_le
- \+ *theorem* blsub_le
- \- *theorem* lsub_le_iff_lt
- \- *theorem* blsub_le_iff_lt



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
- \+ *lemma* lie_module.to_endomorphism_module_End
- \+ *def* lie_ring_module.of_associative_module
- \+ *def* lie_module.of_associative_module

Modified src/algebra/module/linear_map.lean



## [2022-01-25 20:59:08](https://github.com/leanprover-community/mathlib/commit/99608cc)
feat(group_theory/sub{monoid,group}, linear_algebra/basic): add `supr_induction` for `submonoid`, `add_submonoid`, `subgroup`, `add_subgroup`, and `submodule` ([#11556](https://github.com/leanprover-community/mathlib/pull/11556))
This also adds dependent versions, which match the style of the dependent versions of `submodule.span_induction` and `submonoid.closure_induction` in [#11555](https://github.com/leanprover-community/mathlib/pull/11555).
Primarily it's the group and module versions that are useful here, as they remove the inv and smul obligations that would appear if using `closure_induction` or `span_induction`.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+/\- *lemma* mem_supr_of_mem
- \+ *lemma* supr_eq_closure
- \+ *lemma* supr_induction
- \+ *lemma* supr_induction'
- \+/\- *lemma* mem_supr_of_mem

Modified src/group_theory/submonoid/membership.lean
- \+/\- *lemma* mem_supr_of_mem
- \+ *lemma* supr_induction
- \+ *lemma* supr_induction'
- \+/\- *lemma* mem_supr_of_mem

Modified src/linear_algebra/basic.lean
- \+ *lemma* supr_induction
- \+ *lemma* supr_induction'



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
- \+/\- *lemma* closure_induction'
- \+/\- *lemma* closure_induction'

Modified src/group_theory/submonoid/basic.lean
- \+ *lemma* closure_induction'

Modified src/group_theory/submonoid/operations.lean
- \- *lemma* closure_induction'

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* span_induction'
- \+/\- *lemma* span_induction'

Modified src/model_theory/basic.lean
- \+/\- *lemma* closure_induction'
- \+/\- *lemma* closure_induction'



## [2022-01-25 20:59:06](https://github.com/leanprover-community/mathlib/commit/7e09827)
feat(analysis/inner_product_space/adjoint): matrix and linear map adjoints agree ([#11551](https://github.com/leanprover-community/mathlib/pull/11551))
#### Estimated changes
Modified src/analysis/inner_product_space/adjoint.lean
- \+ *lemma* conj_transpose_eq_adjoint



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
- \+ *theorem* aleph'_pos
- \+ *theorem* aleph_pos



## [2022-01-25 17:30:28](https://github.com/leanprover-community/mathlib/commit/6184db1)
feat(topology/algebra/mul_action2): quotient by a properly discontinuous group action is t2 ([#10465](https://github.com/leanprover-community/mathlib/pull/10465))
We prove that the quotient of a Hausdorff (t2) locally compact space by a properly discontinuous group action is itself Hausdorff.
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \+ *lemma* quotient_preimage_image_eq_union_mul
- \+ *lemma* image_inter_image_iff

Modified src/topology/algebra/mul_action.lean

Created src/topology/algebra/mul_action2.lean
- \+ *lemma* is_open_map_quotient_mk_mul
- \+ *def* homeomorph.smul
- \+ *def* homeomorph.vadd

Modified src/topology/separation.lean
- \+ *lemma* t2_space_iff_nhds
- \+ *lemma* t2_separation_nhds
- \+ *lemma* t2_separation_compact_nhds

Modified src/topology/subset_properties.lean
- \+ *lemma* local_compact_nhds



## [2022-01-25 13:19:58](https://github.com/leanprover-community/mathlib/commit/4d761f4)
feat(algebra/group/hom): Notation for `monoid_with_zero_hom` ([#11632](https://github.com/leanprover-community/mathlib/pull/11632))
Introduce notation `→*₀` for `monoid_with_zero_hom` and use it everywhere.
#### Estimated changes
Modified src/algebra/gcd_monoid/basic.lean
- \+/\- *def* normalize
- \+/\- *def* normalize

Modified src/algebra/group/hom.lean
- \+/\- *lemma* monoid_with_zero_hom.ext
- \+/\- *lemma* monoid_with_zero_hom.ext_iff
- \+/\- *lemma* monoid_with_zero_hom.mk_coe
- \+/\- *lemma* monoid_with_zero_hom.comp_apply
- \+/\- *lemma* monoid_with_zero_hom.cancel_right
- \+/\- *lemma* monoid_with_zero_hom.cancel_left
- \+/\- *lemma* monoid_with_zero_hom.ext
- \+/\- *lemma* monoid_with_zero_hom.ext_iff
- \+/\- *lemma* monoid_with_zero_hom.mk_coe
- \+/\- *lemma* monoid_with_zero_hom.comp_apply
- \+/\- *lemma* monoid_with_zero_hom.cancel_right
- \+/\- *lemma* monoid_with_zero_hom.cancel_left
- \+/\- *theorem* monoid_with_zero_hom.congr_fun
- \+/\- *theorem* monoid_with_zero_hom.congr_arg
- \+/\- *theorem* monoid_with_zero_hom.congr_fun
- \+/\- *theorem* monoid_with_zero_hom.congr_arg
- \+/\- *def* monoid_with_zero_hom.id
- \+/\- *def* monoid_with_zero_hom.id

Modified src/algebra/group/prod.lean
- \+/\- *def* mul_monoid_with_zero_hom
- \+/\- *def* div_monoid_with_zero_hom
- \+/\- *def* mul_monoid_with_zero_hom
- \+/\- *def* div_monoid_with_zero_hom

Modified src/algebra/group_with_zero/basic.lean
- \+/\- *def* inv_monoid_with_zero_hom
- \+/\- *def* inv_monoid_with_zero_hom

Modified src/algebra/group_with_zero/power.lean

Modified src/algebra/order/absolute_value.lean
- \+/\- *def* to_monoid_with_zero_hom
- \+/\- *def* abv_hom
- \+/\- *def* to_monoid_with_zero_hom
- \+/\- *def* abv_hom

Modified src/algebra/order/field.lean
- \+/\- *lemma* abs_div
- \+/\- *lemma* abs_inv
- \+/\- *lemma* abs_div
- \+/\- *lemma* abs_inv

Modified src/algebra/order/ring.lean
- \+/\- *def* abs_hom
- \+/\- *def* abs_hom

Modified src/algebra/quaternion.lean
- \+/\- *def* norm_sq
- \+/\- *def* norm_sq

Modified src/algebra/ring/basic.lean

Modified src/algebra/smul_with_zero.lean
- \+/\- *def* mul_action_with_zero.comp_hom
- \+/\- *def* mul_action_with_zero.comp_hom

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_div
- \+/\- *lemma* nnnorm_div
- \+/\- *lemma* norm_inv
- \+/\- *lemma* norm_zpow
- \+/\- *lemma* norm_div
- \+/\- *lemma* nnnorm_div
- \+/\- *lemma* norm_inv
- \+/\- *lemma* norm_zpow
- \+/\- *def* norm_hom
- \+/\- *def* nnnorm_hom
- \+/\- *def* norm_hom
- \+/\- *def* nnnorm_hom

Modified src/data/complex/basic.lean
- \+/\- *def* norm_sq
- \+/\- *def* norm_sq

Modified src/data/complex/is_R_or_C.lean
- \+/\- *def* norm_sq
- \+/\- *def* norm_sq

Modified src/data/fintype/basic.lean

Modified src/data/int/cast.lean
- \+ *lemma* ext_int
- \+ *lemma* ext_int'
- \- *theorem* ext_int
- \- *theorem* ext_int'

Modified src/data/nat/cast.lean

Modified src/data/rat/cast.lean
- \+/\- *theorem* ext_rat
- \+/\- *theorem* ext_rat_on_pnat
- \+/\- *theorem* ext_rat
- \+/\- *theorem* ext_rat_on_pnat

Modified src/data/real/nnreal.lean

Modified src/data/real/sqrt.lean

Modified src/ring_theory/non_zero_divisors.lean
- \+/\- *lemma* monoid_with_zero_hom.map_ne_zero_of_mem_non_zero_divisors
- \+/\- *lemma* monoid_with_zero_hom.map_le_non_zero_divisors_of_injective
- \+/\- *lemma* monoid_with_zero_hom.map_ne_zero_of_mem_non_zero_divisors
- \+/\- *lemma* monoid_with_zero_hom.map_le_non_zero_divisors_of_injective

Modified src/ring_theory/valuation/basic.lean
- \+/\- *lemma* coe_coe
- \+/\- *lemma* map
- \+/\- *lemma* coe_coe
- \+/\- *lemma* map
- \+/\- *def* map
- \+/\- *def* map



## [2022-01-25 12:25:39](https://github.com/leanprover-community/mathlib/commit/1b3da83)
feat(combinatorics/simple_graph/coloring): add inequalities from embeddings ([#11548](https://github.com/leanprover-community/mathlib/pull/11548))
Also add a lemma that the chromatic number of an infinite complete graph is zero (i.e., it needs infinitely many colors), as suggested by @arthurpaulino.
#### Estimated changes
Modified src/combinatorics/simple_graph/coloring.lean
- \+ *lemma* colorable.mono
- \+ *lemma* colorable.of_embedding
- \+ *lemma* chromatic_number_pos
- \+ *lemma* colorable_of_chromatic_number_pos
- \+ *lemma* colorable.mono_left
- \+ *lemma* colorable.chromatic_number_le_of_forall_imp
- \+ *lemma* colorable.chromatic_number_mono
- \+ *lemma* colorable.chromatic_number_mono_of_embedding
- \+ *lemma* chromatic_number_top
- \+ *lemma* chromatic_number_top_eq_zero_of_infinite
- \- *lemma* colorable.of_le
- \- *lemma* zero_lt_chromatic_number
- \- *lemma* colorable_of_le_colorable
- \- *lemma* chromatic_number_le_of_forall_imp
- \- *lemma* chromatic_number_le_of_le_colorable
- \- *lemma* chromatic_number_complete_graph

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
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* injective_comp
- \+/\- *lemma* comp_injective
- \+/\- *lemma* surjective_comp
- \+/\- *lemma* comp_surjective
- \+/\- *lemma* bijective_comp
- \+/\- *lemma* comp_bijective
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* injective_comp
- \+/\- *lemma* comp_injective
- \+/\- *lemma* surjective_comp
- \+/\- *lemma* comp_surjective
- \+/\- *lemma* bijective_comp
- \+/\- *lemma* comp_bijective
- \+/\- *theorem* coe_fn_injective
- \+/\- *theorem* apply_eq_iff_eq
- \+/\- *theorem* coe_fn_injective
- \+/\- *theorem* apply_eq_iff_eq

Renamed src/data/fun_like.lean to src/data/fun_like/basic.lean

Created src/data/fun_like/embedding.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* map_op
- \+ *lemma* map_cool
- \+ *lemma* do_something
- \+ *lemma* apply_eq_iff_eq
- \+ *lemma* comp_injective
- \+ *theorem* ext

Created src/data/fun_like/equiv.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* map_cool
- \+ *lemma* do_something
- \+ *lemma* inv_injective
- \+ *lemma* injective_comp
- \+ *lemma* surjective_comp
- \+ *lemma* bijective_comp
- \+ *lemma* comp_injective
- \+ *lemma* comp_surjective
- \+ *lemma* comp_bijective
- \+ *theorem* ext
- \+ *theorem* apply_eq_iff_eq

Modified src/logic/embedding.lean
- \+/\- *lemma* coe_injective
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* apply_eq_iff_eq
- \+/\- *lemma* coe_injective
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* apply_eq_iff_eq

Modified src/order/rel_iso.lean



## [2022-01-25 10:04:17](https://github.com/leanprover-community/mathlib/commit/6b32241)
feat(model_theory/basic): Terms, formulas, and definable sets ([#11067](https://github.com/leanprover-community/mathlib/pull/11067))
Defines first-order terms, formulas, sentences and theories
Defines the boolean algebra of definable sets
(Several of these definitions are based on those from the flypitch project.)
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *lemma* realize_not
- \+ *lemma* is_definable_empty
- \+ *lemma* is_definable_univ
- \+ *lemma* is_definable.inter
- \+ *lemma* is_definable.union
- \+ *lemma* is_definable.compl
- \+ *lemma* is_definable.sdiff
- \+ *lemma* mem_top
- \+ *lemma* coe_top
- \+ *lemma* not_mem_bot
- \+ *lemma* coe_bot
- \+ *lemma* le_iff
- \+ *lemma* coe_sup
- \+ *lemma* mem_sup
- \+ *lemma* coe_inf
- \+ *lemma* mem_inf
- \+ *lemma* mem_compl
- \+ *lemma* coe_compl
- \+ *def* realize_term
- \+ *def* formula
- \+ *def* sentence
- \+ *def* theory
- \+ *def* bd_not
- \+ *def* realize_bounded_formula
- \+ *def* realize_formula
- \+ *def* realize_sentence
- \+ *def* definable_set



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
- \+/\- *def* legendre_sym
- \+/\- *def* legendre_sym



## [2022-01-25 07:15:51](https://github.com/leanprover-community/mathlib/commit/f7a597a)
feat(group_theory/nilpotent): add nilpotency_class inequalities ([#11585](https://github.com/leanprover-community/mathlib/pull/11585))
Every theorem that proves `nilpotency G'` (e.g. for subgroups, images,
preimages) should be accompanied by a lemma relating their
`nilpotency_class`, so add thse lmmeas for subgroups and preimages.
Also add nilpotency lemmas for surjective homomorphisms and quotions,
including nilpotency_class lemmas.
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* upper_central_series_nilpotency_class
- \+ *lemma* lower_central_series_nilpotency_class
- \+ *lemma* subgroup.nilpotency_class_le
- \+/\- *lemma* is_nilpotent_of_ker_le_center
- \+ *lemma* nilpotency_class_le_of_ker_le_center
- \+ *lemma* nilpotent_of_surjective
- \+ *lemma* nilpotency_class_le_of_surjective
- \+ *lemma* nilpotency_class_quotient_le
- \+/\- *lemma* is_nilpotent_of_ker_le_center



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

Modified src/order/rel_classes.lean



## [2022-01-25 03:33:32](https://github.com/leanprover-community/mathlib/commit/b834415)
chore(topology/metric_space/gromov_hausdorff): Golf some theorems ([#11591](https://github.com/leanprover-community/mathlib/pull/11591))
#### Estimated changes
Modified src/topology/metric_space/gromov_hausdorff.lean



## [2022-01-25 03:33:31](https://github.com/leanprover-community/mathlib/commit/88479be)
feat(algebra/big_operators/basic): add lemma `finset.prod_dvd_prod` ([#11521](https://github.com/leanprover-community/mathlib/pull/11521))
For any `S : finset α`, if `∀ a ∈ S, g1 a ∣ g2 a` then `S.prod g1 ∣ S.prod g2`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_dvd_prod



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
Created src/data/finset/finsupp.lean
- \+ *lemma* mem_finsupp_iff
- \+ *lemma* mem_finsupp_iff_of_support_subset
- \+ *lemma* card_finsupp
- \+ *lemma* mem_pi
- \+ *lemma* card_pi
- \+ *def* pi

Modified src/data/finsupp/basic.lean
- \+/\- *def* zip_with
- \+/\- *def* emb_domain.add_monoid_hom
- \+/\- *def* map_domain_embedding
- \+/\- *def* zip_with
- \+/\- *def* emb_domain.add_monoid_hom
- \+/\- *def* map_domain_embedding

Created src/data/finsupp/indicator.lean
- \+ *lemma* indicator_of_mem
- \+ *lemma* indicator_of_not_mem
- \+ *lemma* indicator_apply
- \+ *lemma* indicator_injective
- \+ *lemma* support_indicator_subset
- \+ *def* indicator



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
- \+ *lemma* up_le_up
- \+ *lemma* up_lt_up
- \+ *lemma* down_subset_down
- \+ *lemma* down_ssubset_down
- \- *def* set_semiring



## [2022-01-24 21:01:25](https://github.com/leanprover-community/mathlib/commit/9e799a0)
feat(algebra/pointwise): Scalar multiplication lemmas ([#11486](https://github.com/leanprover-community/mathlib/pull/11486))
This proves a bunch of lemmas about pointwise scalar multiplication of sets, moves `has_vsub` to `algebra.group.defs` and pointwise `vsub` lemmas to `algebra.pointwise`.
I'm also adding a few sections because having `{s t : set α}` is nice for multiplication but not for scalar multiplication.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \- *lemma* vsub_empty
- \- *lemma* empty_vsub
- \- *lemma* singleton_vsub
- \- *lemma* vsub_singleton
- \- *lemma* finite.vsub
- \- *lemma* vsub_mem_vsub
- \- *lemma* mem_vsub
- \- *lemma* vsub_subset_vsub
- \- *lemma* vsub_self_mono
- \- *lemma* vsub_subset_iff
- \- *lemma* vadd_subset_vadd
- \- *lemma* set_vadd_singleton
- \- *lemma* finite.vadd

Modified src/algebra/group/defs.lean

Modified src/algebra/pointwise.lean
- \+/\- *lemma* singleton_one
- \+/\- *lemma* mem_one
- \+/\- *lemma* one_mem_one
- \+ *lemma* one_subset
- \+ *lemma* one_nonempty
- \+ *lemma* image_one
- \+/\- *lemma* image2_mul
- \+/\- *lemma* mem_mul
- \+/\- *lemma* mul_mem_mul
- \+/\- *lemma* mul_subset_mul
- \+/\- *lemma* image_mul_prod
- \+/\- *lemma* empty_mul
- \+/\- *lemma* mul_empty
- \+/\- *lemma* mul_singleton
- \+/\- *lemma* singleton_mul
- \+/\- *lemma* singleton_mul_singleton
- \+/\- *lemma* mul_subset_mul_left
- \+/\- *lemma* mul_subset_mul_right
- \+/\- *lemma* union_mul
- \+/\- *lemma* mul_union
- \+ *lemma* inter_mul_subset
- \+ *lemma* mul_inter_subset
- \+/\- *lemma* Union_mul_left_image
- \+/\- *lemma* Union_mul_right_image
- \+/\- *lemma* Union_mul
- \+/\- *lemma* mul_Union
- \+ *lemma* Union₂_mul
- \+ *lemma* mul_Union₂
- \+ *lemma* Inter_mul_subset
- \+ *lemma* mul_Inter_subset
- \+ *lemma* Inter₂_mul_subset
- \+ *lemma* mul_Inter₂_subset
- \+/\- *lemma* image_mul_left
- \+/\- *lemma* image_mul_right
- \+/\- *lemma* image_mul_right'
- \+/\- *lemma* preimage_mul_left_one
- \+/\- *lemma* preimage_mul_right_one
- \+/\- *lemma* preimage_mul_right_one'
- \+ *lemma* subset_mul_left
- \+ *lemma* subset_mul_right
- \+ *lemma* mul_univ
- \+ *lemma* univ_mul
- \+/\- *lemma* image2_smul
- \+/\- *lemma* image_smul_prod
- \+/\- *lemma* mem_smul
- \+ *lemma* smul_mem_smul
- \+ *lemma* smul_subset_smul
- \+ *lemma* smul_subset_iff
- \+ *lemma* empty_smul
- \+ *lemma* smul_empty
- \+/\- *lemma* smul_singleton
- \+/\- *lemma* singleton_smul
- \+ *lemma* singleton_smul_singleton
- \+ *lemma* smul_subset_smul_left
- \+ *lemma* smul_subset_smul_right
- \+ *lemma* union_smul
- \+ *lemma* smul_union
- \+ *lemma* inter_smul_subset
- \+ *lemma* smul_inter_subset
- \+ *lemma* Union_smul_left_image
- \+ *lemma* Union_smul_right_image
- \+ *lemma* Union_smul
- \+ *lemma* smul_Union
- \+ *lemma* Union₂_smul
- \+ *lemma* smul_Union₂
- \+ *lemma* Inter_smul_subset
- \+ *lemma* smul_Inter_subset
- \+ *lemma* Inter₂_smul_subset
- \+ *lemma* smul_Inter₂_subset
- \+/\- *lemma* image_smul
- \+/\- *lemma* mem_smul_set
- \+/\- *lemma* smul_mem_smul_set
- \+/\- *lemma* mem_smul_of_mem
- \+/\- *lemma* smul_set_empty
- \+ *lemma* smul_set_singleton
- \+/\- *lemma* smul_set_mono
- \+/\- *lemma* smul_set_union
- \+/\- *lemma* smul_set_inter_subset
- \+ *lemma* smul_set_Union
- \+ *lemma* smul_set_Union₂
- \+ *lemma* smul_set_Inter_subset
- \+ *lemma* smul_set_Inter₂_subset
- \+ *lemma* finite.smul_set
- \+/\- *lemma* smul_set_inter
- \+/\- *lemma* smul_set_inter₀
- \+ *lemma* smul_set_univ
- \+ *lemma* smul_univ
- \+ *lemma* image2_vsub
- \+ *lemma* image_vsub_prod
- \+ *lemma* mem_vsub
- \+ *lemma* vsub_mem_vsub
- \+ *lemma* vsub_subset_vsub
- \+ *lemma* vsub_subset_iff
- \+ *lemma* empty_vsub
- \+ *lemma* vsub_empty
- \+ *lemma* vsub_singleton
- \+ *lemma* singleton_vsub
- \+ *lemma* singleton_vsub_singleton
- \+ *lemma* vsub_subset_vsub_left
- \+ *lemma* vsub_subset_vsub_right
- \+ *lemma* union_vsub
- \+ *lemma* vsub_union
- \+ *lemma* inter_vsub_subset
- \+ *lemma* vsub_inter_subset
- \+ *lemma* Union_vsub_left_image
- \+ *lemma* Union_vsub_right_image
- \+ *lemma* Union_vsub
- \+ *lemma* vsub_Union
- \+ *lemma* Union₂_vsub
- \+ *lemma* vsub_Union₂
- \+ *lemma* Inter_vsub_subset
- \+ *lemma* vsub_Inter_subset
- \+ *lemma* Inter₂_vsub_subset
- \+ *lemma* vsub_Inter₂_subset
- \+ *lemma* finite.vsub
- \+ *lemma* vsub_self_mono
- \+ *lemma* neg_smul_set
- \+ *lemma* smul_set_neg
- \+/\- *lemma* zero_smul_set
- \+/\- *lemma* zero_smul_subset
- \+/\- *lemma* subsingleton_zero_smul_set
- \+ *lemma* zero_mem_smul_set
- \+ *lemma* zero_mem_smul_iff
- \+ *lemma* zero_mem_smul_set_iff
- \+/\- *lemma* smul_mem_smul_set_iff₀
- \+/\- *lemma* mem_smul_set_iff_inv_smul_mem₀
- \+/\- *lemma* mem_inv_smul_set_iff₀
- \+/\- *lemma* preimage_smul₀
- \+/\- *lemma* preimage_smul_inv₀
- \+/\- *lemma* set_smul_subset_set_smul_iff₀
- \+/\- *lemma* set_smul_subset_iff₀
- \+/\- *lemma* subset_set_smul_iff₀
- \+ *lemma* smul_univ₀
- \+ *lemma* smul_set_univ₀
- \+/\- *lemma* singleton_one
- \+/\- *lemma* mem_one
- \+/\- *lemma* one_mem_one
- \+/\- *lemma* image2_mul
- \+/\- *lemma* mem_mul
- \+/\- *lemma* mul_mem_mul
- \+/\- *lemma* image_mul_prod
- \+/\- *lemma* image_mul_left
- \+/\- *lemma* image_mul_right
- \+/\- *lemma* image_mul_right'
- \+/\- *lemma* preimage_mul_left_one
- \+/\- *lemma* preimage_mul_right_one
- \+/\- *lemma* preimage_mul_right_one'
- \+/\- *lemma* mul_singleton
- \+/\- *lemma* singleton_mul
- \+/\- *lemma* singleton_mul_singleton
- \+/\- *lemma* empty_mul
- \+/\- *lemma* mul_empty
- \+/\- *lemma* mul_subset_mul
- \+/\- *lemma* mul_subset_mul_left
- \+/\- *lemma* mul_subset_mul_right
- \+/\- *lemma* union_mul
- \+/\- *lemma* mul_union
- \+/\- *lemma* Union_mul_left_image
- \+/\- *lemma* Union_mul_right_image
- \+/\- *lemma* Union_mul
- \+/\- *lemma* mul_Union
- \+/\- *lemma* image_smul
- \+/\- *lemma* mem_smul_set
- \+/\- *lemma* smul_mem_smul_set
- \+/\- *lemma* smul_set_union
- \+/\- *lemma* smul_set_inter
- \+/\- *lemma* smul_set_inter₀
- \+/\- *lemma* smul_set_inter_subset
- \+/\- *lemma* smul_set_empty
- \+/\- *lemma* smul_set_mono
- \+/\- *lemma* image2_smul
- \+/\- *lemma* mem_smul
- \+/\- *lemma* mem_smul_of_mem
- \+/\- *lemma* image_smul_prod
- \+/\- *lemma* smul_singleton
- \+/\- *lemma* singleton_smul
- \+/\- *lemma* zero_smul_set
- \+/\- *lemma* zero_smul_subset
- \+/\- *lemma* subsingleton_zero_smul_set
- \+/\- *lemma* smul_mem_smul_set_iff₀
- \+/\- *lemma* mem_smul_set_iff_inv_smul_mem₀
- \+/\- *lemma* mem_inv_smul_set_iff₀
- \+/\- *lemma* preimage_smul₀
- \+/\- *lemma* preimage_smul_inv₀
- \+/\- *lemma* set_smul_subset_set_smul_iff₀
- \+/\- *lemma* set_smul_subset_iff₀
- \+/\- *lemma* subset_set_smul_iff₀
- \+/\- *theorem* range_smul_range
- \- *theorem* one_subset
- \- *theorem* one_nonempty
- \- *theorem* image_one
- \+/\- *theorem* range_smul_range
- \+/\- *def* singleton_mul_hom
- \+/\- *def* singleton_mul_hom

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
- \+/\- *lemma* map_bracket_eq
- \+ *lemma* map_comap_le
- \+ *lemma* map_comap_eq
- \+ *lemma* le_comap_map
- \+ *lemma* comap_map_eq
- \+ *lemma* comap_bracket_eq
- \+ *lemma* map_comap_incl
- \+/\- *lemma* map_bracket_eq

Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* lcs_zero
- \+ *lemma* lcs_succ
- \+/\- *lemma* lower_central_series_succ
- \+ *lemma* lcs_le_self
- \+ *lemma* lower_central_series_eq_lcs_comap
- \+ *lemma* lower_central_series_map_eq_lcs
- \+/\- *lemma* lower_central_series_succ
- \+ *def* lcs
- \+/\- *def* lower_central_series
- \+/\- *def* lower_central_series

Modified src/algebra/lie/submodule.lean
- \+ *lemma* incl_coe
- \+ *lemma* coe_submodule_comap
- \+ *lemma* ker_coe_submodule
- \+ *lemma* ker_eq_bot
- \+ *lemma* ker_incl
- \+ *lemma* range_incl
- \+ *lemma* comap_incl_self



## [2022-01-24 16:03:56](https://github.com/leanprover-community/mathlib/commit/a631839)
feat(analysis/special_functions/pow): add nnreal variant of rpow_pos ([#11619](https://github.com/leanprover-community/mathlib/pull/11619))
This matches the lemma for ennreal.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* rpow_pos



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
- \+ *lemma* segment_subset_iff
- \+ *lemma* open_segment_subset_iff
- \+ *lemma* mem_segment_iff_div
- \+ *lemma* mem_open_segment_iff_div
- \+/\- *lemma* convex_iff_open_segment_subset
- \+/\- *lemma* convex.linear_image
- \+/\- *lemma* convex_iff_open_segment_subset
- \+/\- *lemma* convex.linear_image

Modified src/analysis/convex/function.lean
- \+ *lemma* convex_on_of_convex_epigraph
- \+ *lemma* concave_on_of_convex_hypograph
- \+ *lemma* convex_on.open_segment_subset_strict_epigraph
- \+ *lemma* concave_on.open_segment_subset_strict_hypograph
- \+/\- *lemma* convex_on.convex_strict_epigraph
- \+/\- *lemma* convex_on.convex_strict_epigraph

Modified src/analysis/convex/strict.lean



## [2022-01-24 16:03:53](https://github.com/leanprover-community/mathlib/commit/a52ce83)
feat(combinatorics/configuration): The order of a projective plane is at least 2 ([#11550](https://github.com/leanprover-community/mathlib/pull/11550))
This PR proves that the order of a projective plane is strictly larger than 1.
#### Estimated changes
Modified src/combinatorics/configuration.lean
- \+ *lemma* one_lt_order
- \+ *lemma* two_lt_line_count
- \+ *lemma* two_lt_point_count



## [2022-01-24 16:03:52](https://github.com/leanprover-community/mathlib/commit/9150268)
feat (algebraic_geometry): Constructions of fibred products of schemes ([#11450](https://github.com/leanprover-community/mathlib/pull/11450))
This is the first half of the PRs about constructing fibred products of schemes, where we
construct all the relevant schemes and morphisms but yet to show that they are actually
fibred products.
#### Estimated changes
Created src/algebraic_geometry/pullbacks.lean
- \+ *lemma* t_fst_fst
- \+ *lemma* t_fst_snd
- \+ *lemma* t_snd
- \+ *lemma* t_id
- \+ *lemma* t'_fst_fst_fst
- \+ *lemma* t'_fst_fst_snd
- \+ *lemma* t'_fst_snd
- \+ *lemma* t'_snd_fst_fst
- \+ *lemma* t'_snd_fst_snd
- \+ *lemma* t'_snd_snd
- \+ *lemma* cocycle_fst_fst_fst
- \+ *lemma* cocycle_fst_fst_snd
- \+ *lemma* cocycle_fst_snd
- \+ *lemma* cocycle_snd_fst_fst
- \+ *lemma* cocycle_snd_fst_snd
- \+ *lemma* cocycle_snd_snd
- \+ *lemma* cocycle
- \+ *lemma* p_comm
- \+ *lemma* glued_lift_pullback_map_fst
- \+ *lemma* glued_lift_pullback_map_snd
- \+ *lemma* glued_lift_p1
- \+ *lemma* glued_lift_p2
- \+ *def* V
- \+ *def* t
- \+ *def* t'
- \+ *def* gluing
- \+ *def* p1
- \+ *def* p2
- \+ *def* glued_lift_pullback_map
- \+ *def* glued_lift



## [2022-01-24 14:20:36](https://github.com/leanprover-community/mathlib/commit/4a6709b)
feat(data/{int,nat}/gcd): add `nat.gcd_greatest` ([#11611](https://github.com/leanprover-community/mathlib/pull/11611))
Add lemma characterising `gcd` in `ℕ`, counterpart of `int.gcd_greatest`.  Also add shorter proof of `int.gcd_greatest`.
#### Estimated changes
Modified src/data/int/gcd.lean

Modified src/data/nat/gcd.lean
- \+ *theorem* gcd_greatest



## [2022-01-24 14:20:33](https://github.com/leanprover-community/mathlib/commit/bc2f73f)
feat(topology/uniform_space/uniform_convergence): Product of `tendsto_uniformly` ([#11562](https://github.com/leanprover-community/mathlib/pull/11562))
This PR adds lemmas `tendsto_uniformly_on.prod` and `tendsto_uniformly.prod`.
#### Estimated changes
Modified src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* tendsto_uniformly_on.prod_map
- \+ *lemma* tendsto_uniformly.prod_map
- \+ *lemma* tendsto_uniformly_on.prod
- \+ *lemma* tendsto_uniformly.prod



## [2022-01-24 12:47:20](https://github.com/leanprover-community/mathlib/commit/f99af7d)
chore(data/set/lattice): Generalize more `⋃`/`⋂` lemmas to dependent families ([#11516](https://github.com/leanprover-community/mathlib/pull/11516))
The "bounded union" and "bounded intersection" are both instances of nested `⋃`/`⋂`. But they only apply when the inner one runs over a predicate `p : ι → Prop`, and the resulting set couldn't depend on `p`. This generalizes to `κ : ι → Sort*` and allows dependence on `κ i`.
The lemmas are renamed from `bUnion`/`bInter` to `Union₂`/`Inter₂` to show that they are more general. Some generalizations lead to unification problems, so I've kept the `b` version around.
Some lemmas were missing between `⋃` and `⋂` or between `⋃`/`⋂` and nested `⋃`/`⋂`, so I'm adding them as well.
Renames
#### Estimated changes
Modified src/algebra/module/submodule_lattice.lean

Modified src/analysis/box_integral/partition/basic.lean
- \+/\- *lemma* Union_subset
- \+/\- *lemma* Union_subset

Modified src/analysis/box_integral/partition/tagged.lean
- \+/\- *lemma* Union_subset
- \+/\- *lemma* Union_subset

Modified src/analysis/convex/simplicial_complex/basic.lean

Modified src/analysis/normed_space/weak_dual.lean

Modified src/analysis/seminorm.lean

Modified src/data/set/accumulate.lean

Modified src/data/set/intervals/disjoint.lean

Modified src/data/set/lattice.lean
- \+ *lemma* mem_Union
- \+ *lemma* mem_Inter
- \+ *lemma* mem_Union₂
- \+ *lemma* mem_Inter₂
- \+ *lemma* mem_Union_of_mem
- \+ *lemma* mem_Union₂_of_mem
- \+ *lemma* mem_Inter_of_mem
- \+ *lemma* mem_Inter₂_of_mem
- \+ *lemma* Union_subset
- \+ *lemma* Union₂_subset
- \+ *lemma* subset_Inter₂
- \+ *lemma* Union_subset_iff
- \+ *lemma* Union₂_subset_iff
- \+ *lemma* subset_Inter_iff
- \+ *lemma* subset_Inter₂_iff
- \+ *lemma* subset_Union₂
- \+ *lemma* subset_Union_of_subset
- \+ *lemma* Inter₂_subset
- \+/\- *lemma* Inter_subset_of_subset
- \+ *lemma* Union_mono
- \+ *lemma* Union₂_mono
- \+ *lemma* Inter_mono
- \+ *lemma* Inter₂_mono
- \+ *lemma* Union_mono'
- \+ *lemma* Union₂_mono'
- \+ *lemma* Inter_mono'
- \+ *lemma* Inter₂_mono'
- \+ *lemma* Union₂_subset_Union
- \+ *lemma* Inter_subset_Inter₂
- \+ *lemma* Union_set_of
- \+ *lemma* Union_congr_of_surjective
- \+ *lemma* Inter_congr_of_surjective
- \+ *lemma* compl_Union₂
- \+ *lemma* compl_Inter₂
- \+/\- *lemma* Union_Inter_subset
- \+ *lemma* bUnion_mono
- \+ *lemma* bInter_mono
- \+/\- *lemma* Inter_congr
- \+ *lemma* Inter₂_congr
- \+/\- *lemma* Union_congr
- \+ *lemma* Union₂_congr
- \+ *lemma* inter_Union₂
- \+ *lemma* Union₂_inter
- \+ *lemma* Union₂_eq_univ_iff
- \+ *lemma* Inter₂_eq_empty_iff
- \+ *lemma* nonempty_Inter₂
- \+/\- *lemma* Union_range_eq_Union
- \+/\- *lemma* union_distrib_Inter_left
- \+ *lemma* union_distrib_Inter₂_left
- \+/\- *lemma* union_distrib_Inter_right
- \+ *lemma* union_distrib_Inter₂_right
- \+ *lemma* maps_to_Union₂
- \+ *lemma* maps_to_Union₂_Union₂
- \+ *lemma* maps_to_Inter₂
- \+ *lemma* maps_to_Inter₂_Inter₂
- \+ *lemma* image_Inter₂_subset
- \+ *lemma* surj_on_Union₂
- \+ *lemma* surj_on_Union₂_Union₂
- \+ *lemma* image_Union₂
- \+ *lemma* preimage_Union
- \+ *lemma* preimage_Union₂
- \+/\- *lemma* preimage_Inter
- \+ *lemma* preimage_Inter₂
- \+/\- *lemma* prod_Union
- \+ *lemma* prod_Union₂
- \+/\- *lemma* Union_prod_const
- \+ *lemma* Union₂_prod_const
- \+ *lemma* image2_Union₂_left
- \+ *lemma* image2_Union₂_right
- \+ *lemma* image2_Inter_subset_left
- \+ *lemma* image2_Inter_subset_right
- \+ *lemma* image2_Inter₂_subset_left
- \+ *lemma* image2_Inter₂_subset_right
- \+/\- *lemma* Inter_subset_of_subset
- \- *lemma* Inter_subset_Inter
- \- *lemma* Inter_subset_Inter2
- \+/\- *lemma* Union_congr
- \+/\- *lemma* Inter_congr
- \+/\- *lemma* Union_Inter_subset
- \- *lemma* bInter_congr
- \- *lemma* bUnion_congr
- \- *lemma* bUnion_eq_univ_iff
- \- *lemma* bInter_eq_empty_iff
- \- *lemma* Union_subset_Union
- \- *lemma* Union_subset_Union2
- \+/\- *lemma* Union_range_eq_Union
- \+/\- *lemma* union_distrib_Inter_right
- \+/\- *lemma* union_distrib_Inter_left
- \- *lemma* union_distrib_bInter_left
- \- *lemma* union_distrib_bInter_right
- \- *lemma* maps_to_bUnion
- \- *lemma* maps_to_bUnion_bUnion
- \- *lemma* maps_to_bInter
- \- *lemma* maps_to_bInter_bInter
- \- *lemma* image_bInter_subset
- \- *lemma* surj_on_bUnion
- \- *lemma* surj_on_bUnion_bUnion
- \- *lemma* image_bUnion
- \+/\- *lemma* preimage_Inter
- \- *lemma* preimage_bInter
- \+/\- *lemma* prod_Union
- \- *lemma* prod_bUnion
- \+/\- *lemma* Union_prod_const
- \- *lemma* bUnion_prod_const
- \- *theorem* mem_Union
- \- *theorem* mem_Union₂
- \- *theorem* mem_Inter
- \- *theorem* mem_Inter₂
- \- *theorem* Union_subset
- \- *theorem* Union_subset_iff
- \- *theorem* mem_Inter_of_mem
- \- *theorem* subset_Inter_iff
- \- *theorem* subset_subset_Union
- \- *theorem* bUnion_subset
- \- *theorem* subset_bInter
- \- *theorem* bUnion_subset_bUnion
- \- *theorem* bInter_mono'
- \- *theorem* bInter_mono
- \- *theorem* bUnion_mono
- \- *theorem* compl_bUnion
- \- *theorem* compl_bInter
- \- *theorem* inter_bUnion
- \- *theorem* bUnion_inter
- \- *theorem* nonempty_bInter
- \- *theorem* bUnion_subset_Union
- \- *theorem* preimage_Union
- \- *theorem* preimage_bUnion

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
- \+ *lemma* mem_normalizer_iff'
- \+ *lemma* normalizer_eq_self_iff

Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* neg_mem_iff

Modified src/algebra/lie/submodule.lean
- \+ *lemma* to_submodule_eq_coe
- \+ *lemma* mk_eq_zero



## [2022-01-24 11:34:45](https://github.com/leanprover-community/mathlib/commit/dac4f40)
feat(analysis/normed_space/linear_isometry): `to_linear_equiv_trans` ([#11628](https://github.com/leanprover-community/mathlib/pull/11628))
Add a lemma relating `trans` for `linear_isometry_equiv` and
`linear_equiv`.
#### Estimated changes
Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* to_linear_equiv_trans



## [2022-01-24 11:34:44](https://github.com/leanprover-community/mathlib/commit/ed90301)
feat(group_theory/commuting_probability): Commuting probability inequalities ([#11564](https://github.com/leanprover-community/mathlib/pull/11564))
This PR adds some inequalities for the commuting probability.
#### Estimated changes
Modified src/group_theory/commuting_probability.lean
- \+ *lemma* subgroup.comm_prob_subgroup_le
- \+ *lemma* subgroup.comm_prob_quotient_le
- \+ *lemma* inv_card_commutator_le_comm_prob



## [2022-01-24 10:02:38](https://github.com/leanprover-community/mathlib/commit/9ef7f6b)
feat(linear_algebra/orientation): `eq_neg_iff_eq_neg` ([#11629](https://github.com/leanprover-community/mathlib/pull/11629))
Add two more `module.ray` lemmas about negation.
#### Estimated changes
Modified src/linear_algebra/orientation.lean
- \+ *lemma* neg_involutive



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
- \+/\- *def* is_atom
- \+/\- *def* is_coatom

Modified src/order/directed.lean
- \+ *lemma* directed_id_iff
- \+ *lemma* directed_on_univ
- \+ *lemma* directed_on_univ_iff
- \- *lemma* directed_id_iff_is_directed

Modified src/order/ideal.lean
- \+/\- *lemma* ext
- \+ *lemma* coe_injective
- \+ *lemma* coe_inj
- \+ *lemma* ext_iff
- \+/\- *lemma* inter_nonempty
- \+/\- *lemma* principal_le_iff
- \+/\- *lemma* mem_principal
- \+/\- *lemma* mem_compl_of_ge
- \+/\- *lemma* bot_mem
- \+/\- *lemma* coe_top
- \+/\- *lemma* is_proper_of_ne_top
- \+/\- *lemma* is_proper.ne_top
- \+/\- *lemma* _root_.is_coatom.is_proper
- \+/\- *lemma* is_proper_iff_ne_top
- \+/\- *lemma* is_maximal.is_coatom
- \+/\- *lemma* is_maximal.is_coatom'
- \+/\- *lemma* _root_.is_coatom.is_maximal
- \+/\- *lemma* is_maximal_iff_is_coatom
- \+ *lemma* top_of_top_mem
- \+/\- *lemma* is_proper.top_not_mem
- \+/\- *lemma* mem_inf
- \+/\- *lemma* mem_sup
- \+/\- *lemma* eq_sup_of_le_sup
- \+/\- *lemma* mem_ideal_of_cofinals
- \+/\- *lemma* mem_principal
- \+/\- *lemma* ext
- \- *lemma* ext_set_eq
- \- *lemma* ext'_iff
- \- *lemma* is_ideal
- \+/\- *lemma* principal_le_iff
- \+/\- *lemma* mem_compl_of_ge
- \+/\- *lemma* inter_nonempty
- \+/\- *lemma* bot_mem
- \+/\- *lemma* coe_top
- \- *lemma* top_of_mem_top
- \+/\- *lemma* is_proper_of_ne_top
- \+/\- *lemma* is_proper.ne_top
- \+/\- *lemma* is_proper.top_not_mem
- \+/\- *lemma* _root_.is_coatom.is_proper
- \+/\- *lemma* is_proper_iff_ne_top
- \+/\- *lemma* is_maximal.is_coatom
- \+/\- *lemma* is_maximal.is_coatom'
- \+/\- *lemma* _root_.is_coatom.is_maximal
- \+/\- *lemma* is_maximal_iff_is_coatom
- \- *lemma* sup_le
- \+/\- *lemma* mem_inf
- \+/\- *lemma* mem_sup
- \+/\- *lemma* eq_sup_of_le_sup
- \+/\- *lemma* mem_ideal_of_cofinals
- \+/\- *def* is_ideal.to_ideal
- \+/\- *def* principal
- \+/\- *def* is_ideal.to_ideal
- \+/\- *def* principal
- \- *def* inf
- \- *def* sup



## [2022-01-24 10:02:36](https://github.com/leanprover-community/mathlib/commit/9becbc7)
feat(algebra/order/rearrangement) : Rearrangement Inequality ([#10861](https://github.com/leanprover-community/mathlib/pull/10861))
A range of variants of the rearrangement inequality.
This is stated with scalar multiplication of a linear ring over an additive linear group, rather than having everything be in a linear ring. We couldn't find general statements of the rearrangement inequality in the literature, but this very much seems like an improvement.
#### Estimated changes
Created src/algebra/order/rearrangement.lean
- \+ *lemma* monovary_on.sum_smul_comp_perm_le_sum_smul
- \+ *lemma* monovary_on.sum_comp_perm_smul_le_sum_smul
- \+ *lemma* antivary_on.sum_smul_le_sum_smul_comp_perm
- \+ *lemma* antivary_on.sum_smul_le_sum_comp_perm_smul
- \+ *lemma* monovary.sum_smul_comp_perm_le_sum_smul
- \+ *lemma* monovary.sum_comp_perm_smul_le_sum_smul
- \+ *lemma* antivary.sum_smul_le_sum_smul_comp_perm
- \+ *lemma* antivary.sum_smul_le_sum_comp_perm_smul
- \+ *lemma* monovary_on.sum_mul_comp_perm_le_sum_mul
- \+ *lemma* monovary_on.sum_comp_perm_mul_le_sum_mul
- \+ *lemma* antivary_on.sum_mul_le_sum_mul_comp_perm
- \+ *lemma* antivary_on.sum_mul_le_sum_comp_perm_mul
- \+ *lemma* monovary.sum_mul_comp_perm_le_sum_mul
- \+ *lemma* monovary.sum_comp_perm_mul_le_sum_mul
- \+ *lemma* antivary.sum_mul_le_sum_mul_comp_perm
- \+ *lemma* antivary.sum_mul_le_sum_comp_perm_mul

Modified src/order/monovary.lean



## [2022-01-24 07:24:57](https://github.com/leanprover-community/mathlib/commit/8c64be0)
chore(category_theory/abelian): Moved more stuff into `pseudoelement` locale ([#11621](https://github.com/leanprover-community/mathlib/pull/11621))
The `ext` lemma triggers unwantedly in lots of places.
#### Estimated changes
Modified src/category_theory/abelian/diagram_lemmas/four.lean

Modified src/category_theory/abelian/pseudoelements.lean
- \+/\- *theorem* zero_morphism_ext
- \+/\- *theorem* zero_morphism_ext'
- \+/\- *theorem* zero_morphism_ext
- \+/\- *theorem* zero_morphism_ext'



## [2022-01-24 05:54:29](https://github.com/leanprover-community/mathlib/commit/8f73b07)
feat(set_theory/surreal/dyadic): define add_monoid_hom structure on dyadic map ([#11052](https://github.com/leanprover-community/mathlib/pull/11052))
The proof is mechanical and mostly requires unraveling definitions.
The above map cannot be extended to ring morphism as so far there's not multiplication structure on surreal numbers.
#### Estimated changes
Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* pow_apply
- \+ *lemma* log_mul
- \+/\- *theorem* log_pow_eq_self
- \+/\- *theorem* log_pow_eq_self

Modified src/ring_theory/localization.lean
- \+ *lemma* lift_on_zero

Modified src/set_theory/surreal/dyadic.lean
- \+ *lemma* dyadic_map_apply
- \+ *lemma* dyadic_map_apply_pow
- \+/\- *def* dyadic_map
- \+/\- *def* dyadic_map



## [2022-01-24 03:52:26](https://github.com/leanprover-community/mathlib/commit/32cd278)
feat(analysis/asymptotics): add a few lemmas ([#11623](https://github.com/leanprover-community/mathlib/pull/11623))
* rename `is_o.tendsto_0` to `is_o.tendsto_div_nhds_zero`, add `is_o.tendsto_inv_smul_nhds_zero`;
* add `is_o_const_left` and `filter.is_bounded_under.is_o_sub_self_inv`.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotic_equivalent.lean

Modified src/analysis/asymptotics/asymptotics.lean
- \+ *lemma* is_o_const_left_of_ne
- \+ *lemma* is_o_const_left
- \+/\- *theorem* _root_.filter.is_bounded_under.is_O_const
- \+ *theorem* is_o.tendsto_div_nhds_zero
- \+ *theorem* is_o.tendsto_inv_smul_nhds_zero
- \+/\- *theorem* _root_.filter.is_bounded_under.is_O_const
- \- *theorem* is_o.tendsto_0

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
- \+ *lemma* reindex_refl



## [2022-01-23 15:43:45](https://github.com/leanprover-community/mathlib/commit/5449ffa)
feat(data/nat/prime): factors of non-prime powers ([#11546](https://github.com/leanprover-community/mathlib/pull/11546))
Adds the result `pow_factors_to_finset`, fills in `factors_mul_to_finset_of_coprime` for the sake of completion, and adjusts statements to take `ne_zero` rather than pos assumptions.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* to_finset.ext_iff
- \+ *lemma* to_finset.ext

Modified src/data/nat/factorization.lean
- \+ *lemma* factorization_mul_support
- \- *lemma* factorization_mul_support_of_pos

Modified src/data/nat/prime.lean
- \+/\- *lemma* mem_factors
- \+ *lemma* mem_factors_mul
- \+ *lemma* factors_mul_to_finset
- \+ *lemma* pow_succ_factors_to_finset
- \+ *lemma* pow_factors_to_finset
- \+/\- *lemma* prime_pow_prime_divisor
- \+/\- *lemma* coprime_factors_disjoint
- \+ *lemma* mem_factors_mul_of_coprime
- \+ *lemma* factors_mul_to_finset_of_coprime
- \+/\- *lemma* mem_factors
- \+/\- *lemma* prime_pow_prime_divisor
- \- *lemma* mem_factors_mul_of_pos
- \- *lemma* factors_mul_of_pos
- \+/\- *lemma* coprime_factors_disjoint
- \- *lemma* factors_mul_of_coprime

Modified src/group_theory/p_group.lean



## [2022-01-23 13:55:13](https://github.com/leanprover-community/mathlib/commit/59ef8ce)
feat(measure_theory/measure): assorted lemmas ([#11612](https://github.com/leanprover-community/mathlib/pull/11612))
* add `ae_disjoint_compl_left/right`;
* deduce `restrict_to_measurable` and `restrict_to_measurable_of_sigma_finite` from @sgouezel 's lemmas about measures of intersections;
* add `ae_restrict_mem₀`;
* add `ae_eq_univ`.
#### Estimated changes
Modified src/measure_theory/measure/ae_disjoint.lean
- \+ *lemma* ae_disjoint_compl_left
- \+ *lemma* ae_disjoint_compl_right

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* restrict_to_measurable
- \+/\- *lemma* ae_restrict_iff'
- \+/\- *lemma* ae_restrict_mem
- \+ *lemma* ae_restrict_mem₀
- \+ *lemma* restrict_to_measurable_of_sigma_finite
- \+/\- *lemma* ae_restrict_iff'
- \+/\- *lemma* ae_restrict_mem

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* ae_eq_univ



## [2022-01-23 10:59:21](https://github.com/leanprover-community/mathlib/commit/d0f392e)
feat(analysis/calculus/inverse): a map which approximates a linear map on a set admits a nice global extension ([#11568](https://github.com/leanprover-community/mathlib/pull/11568))
And several other results on maps that are well approximated by linear maps on some subset of the space (not necessarily open).
#### Estimated changes
Modified src/analysis/calculus/inverse.lean
- \+ *lemma* approximates_linear_on_empty
- \+ *lemma* approximates_linear_on_iff_lipschitz_on_with
- \+/\- *lemma* open_image
- \+ *lemma* to_inv
- \+ *lemma* exists_homeomorph_extension
- \+/\- *lemma* open_image
- \+ *def* to_homeomorph

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* bound_of_antilipschitz
- \+ *theorem* antilipschitz_of_bound

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* Ici_mem_at_top

Modified src/topology/metric_space/basic.lean
- \+ *lemma* forall_of_forall_mem_closed_ball
- \+ *lemma* forall_of_forall_mem_ball



## [2022-01-23 07:44:41](https://github.com/leanprover-community/mathlib/commit/b1ad301)
feat(number_theory/cyclotomic/basic): add missing lemmas ([#11451](https://github.com/leanprover-community/mathlib/pull/11451))
We add some missing lemmas about cyclotomic extensions.
From flt-regular.
#### Estimated changes
Modified src/number_theory/cyclotomic/basic.lean
- \+ *lemma* adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic
- \+ *lemma* adjoin_primitive_root_eq_top
- \+ *lemma* eq_adjoin_primitive_root



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
- \+/\- *lemma* is_R_or_C.norm_coe_norm

Modified src/data/complex/is_R_or_C.lean
- \+/\- *lemma* re_add_im
- \+/\- *lemma* of_real_re
- \+/\- *lemma* of_real_im
- \+/\- *lemma* mul_re
- \+/\- *lemma* mul_im
- \+/\- *lemma* of_real_zero
- \+/\- *lemma* zero_re'
- \+/\- *lemma* of_real_one
- \+/\- *lemma* one_re
- \+/\- *lemma* one_im
- \+/\- *lemma* bit0_re
- \+/\- *lemma* bit1_re
- \+/\- *lemma* bit0_im
- \+/\- *lemma* bit1_im
- \+/\- *lemma* of_real_add
- \+/\- *lemma* of_real_bit0
- \+/\- *lemma* of_real_bit1
- \+/\- *lemma* of_real_neg
- \+/\- *lemma* of_real_mul
- \+/\- *lemma* of_real_smul
- \+/\- *lemma* of_real_mul_re
- \+/\- *lemma* of_real_mul_im
- \+/\- *lemma* smul_re
- \+/\- *lemma* smul_im
- \+/\- *lemma* I_re
- \+/\- *lemma* I_im
- \+/\- *lemma* I_im'
- \+/\- *lemma* I_mul_re
- \+/\- *lemma* conj_re
- \+/\- *lemma* conj_im
- \+/\- *lemma* conj_I
- \+/\- *lemma* conj_of_real
- \+/\- *lemma* conj_bit0
- \+/\- *lemma* conj_bit1
- \+/\- *lemma* conj_neg_I
- \+/\- *lemma* conj_eq_re_sub_im
- \+/\- *lemma* conj_smul
- \+/\- *lemma* norm_sq_of_real
- \+/\- *lemma* norm_sq_zero
- \+/\- *lemma* norm_sq_one
- \+/\- *lemma* norm_sq_eq_zero
- \+/\- *lemma* norm_sq_pos
- \+/\- *lemma* norm_sq_neg
- \+/\- *lemma* norm_sq_conj
- \+/\- *lemma* norm_sq_mul
- \+/\- *lemma* of_real_sub
- \+/\- *lemma* of_real_pow
- \+/\- *lemma* norm_sq_sub
- \+/\- *lemma* inv_re
- \+/\- *lemma* inv_im
- \+/\- *lemma* of_real_inv
- \+/\- *lemma* of_real_div
- \+/\- *lemma* of_real_zpow
- \+/\- *lemma* div_I
- \+/\- *lemma* inv_I
- \+/\- *lemma* norm_sq_inv
- \+/\- *lemma* norm_sq_div
- \+/\- *lemma* norm_conj
- \+/\- *lemma* nat_cast_re
- \+/\- *lemma* nat_cast_im
- \+/\- *lemma* int_cast_re
- \+/\- *lemma* int_cast_im
- \+/\- *lemma* rat_cast_re
- \+/\- *lemma* rat_cast_im
- \+/\- *lemma* norm_eq_abs
- \+/\- *lemma* abs_zero
- \+/\- *lemma* abs_one
- \+/\- *lemma* abs_two
- \+/\- *lemma* abs_eq_zero
- \+/\- *lemma* abs_conj
- \+/\- *lemma* abs_mul
- \+/\- *lemma* abs_abs
- \+/\- *lemma* abs_pos
- \+/\- *lemma* abs_neg
- \+/\- *lemma* abs_cast_nat
- \+/\- *lemma* of_real_prod
- \+/\- *lemma* of_real_sum
- \+/\- *lemma* of_real_finsupp_sum
- \+/\- *lemma* of_real_finsupp_prod
- \+/\- *lemma* re_to_real
- \+/\- *lemma* im_to_real
- \+/\- *lemma* conj_to_real
- \+/\- *lemma* I_to_real
- \+/\- *lemma* norm_sq_to_real
- \+/\- *lemma* abs_to_real
- \+/\- *lemma* re_lm_coe
- \+/\- *lemma* re_clm_norm
- \+/\- *lemma* re_clm_coe
- \+/\- *lemma* re_clm_apply
- \+/\- *lemma* im_lm_coe
- \+/\- *lemma* im_clm_coe
- \+/\- *lemma* im_clm_apply
- \+/\- *lemma* conj_ae_coe
- \+/\- *lemma* conj_lie_apply
- \+/\- *lemma* conj_cle_coe
- \+/\- *lemma* conj_cle_apply
- \+/\- *lemma* conj_cle_norm
- \+/\- *lemma* of_real_am_coe
- \+/\- *lemma* of_real_li_apply
- \+/\- *lemma* of_real_clm_coe
- \+/\- *lemma* of_real_clm_apply
- \+/\- *lemma* of_real_clm_norm
- \+/\- *lemma* re_add_im
- \+/\- *lemma* of_real_re
- \+/\- *lemma* of_real_im
- \+/\- *lemma* mul_re
- \+/\- *lemma* mul_im
- \+/\- *lemma* of_real_zero
- \+/\- *lemma* zero_re'
- \+/\- *lemma* of_real_one
- \+/\- *lemma* one_re
- \+/\- *lemma* one_im
- \+/\- *lemma* bit0_re
- \+/\- *lemma* bit1_re
- \+/\- *lemma* bit0_im
- \+/\- *lemma* bit1_im
- \+/\- *lemma* of_real_add
- \+/\- *lemma* of_real_bit0
- \+/\- *lemma* of_real_bit1
- \+/\- *lemma* of_real_neg
- \+/\- *lemma* of_real_mul
- \+/\- *lemma* of_real_smul
- \+/\- *lemma* of_real_mul_re
- \+/\- *lemma* of_real_mul_im
- \+/\- *lemma* smul_re
- \+/\- *lemma* smul_im
- \+/\- *lemma* I_re
- \+/\- *lemma* I_im
- \+/\- *lemma* I_im'
- \+/\- *lemma* I_mul_re
- \+/\- *lemma* conj_re
- \+/\- *lemma* conj_im
- \+/\- *lemma* conj_I
- \+/\- *lemma* conj_of_real
- \+/\- *lemma* conj_bit0
- \+/\- *lemma* conj_bit1
- \+/\- *lemma* conj_neg_I
- \+/\- *lemma* conj_eq_re_sub_im
- \+/\- *lemma* conj_smul
- \+/\- *lemma* norm_sq_of_real
- \+/\- *lemma* norm_sq_zero
- \+/\- *lemma* norm_sq_one
- \+/\- *lemma* norm_sq_eq_zero
- \+/\- *lemma* norm_sq_pos
- \+/\- *lemma* norm_sq_neg
- \+/\- *lemma* norm_sq_conj
- \+/\- *lemma* norm_sq_mul
- \+/\- *lemma* of_real_sub
- \+/\- *lemma* of_real_pow
- \+/\- *lemma* norm_sq_sub
- \+/\- *lemma* inv_re
- \+/\- *lemma* inv_im
- \+/\- *lemma* of_real_inv
- \+/\- *lemma* of_real_div
- \+/\- *lemma* of_real_zpow
- \+/\- *lemma* div_I
- \+/\- *lemma* inv_I
- \+/\- *lemma* norm_sq_inv
- \+/\- *lemma* norm_sq_div
- \+/\- *lemma* norm_conj
- \+/\- *lemma* nat_cast_re
- \+/\- *lemma* nat_cast_im
- \+/\- *lemma* int_cast_re
- \+/\- *lemma* int_cast_im
- \+/\- *lemma* rat_cast_re
- \+/\- *lemma* rat_cast_im
- \+/\- *lemma* norm_eq_abs
- \+/\- *lemma* abs_zero
- \+/\- *lemma* abs_one
- \+/\- *lemma* abs_two
- \+/\- *lemma* abs_eq_zero
- \+/\- *lemma* abs_conj
- \+/\- *lemma* abs_mul
- \+/\- *lemma* abs_abs
- \+/\- *lemma* abs_pos
- \+/\- *lemma* abs_neg
- \+/\- *lemma* abs_cast_nat
- \+/\- *lemma* of_real_prod
- \+/\- *lemma* of_real_sum
- \+/\- *lemma* of_real_finsupp_sum
- \+/\- *lemma* of_real_finsupp_prod
- \+/\- *lemma* re_to_real
- \+/\- *lemma* im_to_real
- \+/\- *lemma* conj_to_real
- \+/\- *lemma* I_to_real
- \+/\- *lemma* norm_sq_to_real
- \+/\- *lemma* abs_to_real
- \+/\- *lemma* re_lm_coe
- \+/\- *lemma* re_clm_norm
- \+/\- *lemma* re_clm_coe
- \+/\- *lemma* re_clm_apply
- \+/\- *lemma* im_lm_coe
- \+/\- *lemma* im_clm_coe
- \+/\- *lemma* im_clm_apply
- \+/\- *lemma* conj_ae_coe
- \+/\- *lemma* conj_lie_apply
- \+/\- *lemma* conj_cle_coe
- \+/\- *lemma* conj_cle_apply
- \+/\- *lemma* conj_cle_norm
- \+/\- *lemma* of_real_am_coe
- \+/\- *lemma* of_real_li_apply
- \+/\- *lemma* of_real_clm_coe
- \+/\- *lemma* of_real_clm_apply
- \+/\- *lemma* of_real_clm_norm
- \+/\- *theorem* of_real_eq_zero
- \+/\- *theorem* of_real_nat_cast
- \+/\- *theorem* of_real_int_cast
- \+/\- *theorem* of_real_rat_cast
- \+/\- *theorem* abs_inv
- \+/\- *theorem* abs_div
- \+/\- *theorem* of_real_eq_zero
- \+/\- *theorem* of_real_nat_cast
- \+/\- *theorem* of_real_nat_cast
- \+/\- *theorem* of_real_int_cast
- \+/\- *theorem* of_real_rat_cast
- \+/\- *theorem* abs_inv
- \+/\- *theorem* abs_div



## [2022-01-22 23:39:48](https://github.com/leanprover-community/mathlib/commit/84dbe7b)
feat(measure_theory/covering): Lebesgue density points ([#11554](https://github.com/leanprover-community/mathlib/pull/11554))
We show in the general context of differentiation of measures that `μ (s ∩ a) / μ a` converges, when `a` shrinks towards a point `x`, to `1` for almost every `x` in `s`, and to `0` for almost every point outside of `s`. In other words, almost every point of `s` is a Lebesgue density points of `s`. Of course, this requires assumptions on allowed sets `a`. We state this in the general context of Vitali families. We also give easier to use versions in spaces with the Besicovitch property (e.g., final dimensional real vector spaces), where one can take for `a` the closed balls centered at `x`.
#### Estimated changes
Modified src/measure_theory/covering/besicovitch.lean
- \+ *lemma* tendsto_filter_at
- \+ *lemma* ae_tendsto_rn_deriv
- \+ *lemma* ae_tendsto_measure_inter_div_of_measurable_set
- \+ *lemma* ae_tendsto_measure_inter_div
- \+/\- *theorem* exists_disjoint_closed_ball_covering_ae_aux
- \+/\- *theorem* exists_disjoint_closed_ball_covering_ae
- \+/\- *theorem* exists_disjoint_closed_ball_covering_ae_aux
- \+/\- *theorem* exists_disjoint_closed_ball_covering_ae

Modified src/measure_theory/covering/differentiation.lean
- \+ *lemma* ae_tendsto_measure_inter_div_of_measurable_set
- \+ *lemma* ae_tendsto_measure_inter_div

Modified src/measure_theory/covering/vitali_family.lean
- \+ *lemma* eventually_filter_at_measurable_set

Modified src/measure_theory/decomposition/lebesgue.lean
- \+ *theorem* rn_deriv_restrict

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* with_density_indicator_one



## [2022-01-22 22:28:56](https://github.com/leanprover-community/mathlib/commit/a196f9b)
chore(measure_theory/probability_mass_function): Move pmf monad operations into a seperate file ([#11579](https://github.com/leanprover-community/mathlib/pull/11579))
This PR moves the `pure`, `bind`, and `bind_on_support` operations on `pmf` into a new `probability_mass_function/monad.lean` file.
#### Estimated changes
Modified src/measure_theory/probability_mass_function/basic.lean
- \- *lemma* pure_apply
- \- *lemma* support_pure
- \- *lemma* mem_support_pure_iff:
- \- *lemma* bind_apply
- \- *lemma* support_bind
- \- *lemma* mem_support_bind_iff
- \- *lemma* coe_bind_apply
- \- *lemma* pure_bind
- \- *lemma* bind_pure
- \- *lemma* bind_bind
- \- *lemma* bind_comm
- \- *def* pure
- \- *def* bind

Modified src/measure_theory/probability_mass_function/constructions.lean
- \- *lemma* bind_on_support_apply
- \- *lemma* support_bind_on_support
- \- *lemma* mem_support_bind_on_support_iff
- \- *lemma* bind_on_support_eq_bind
- \- *lemma* coe_bind_on_support_apply
- \- *lemma* bind_on_support_eq_zero_iff
- \- *lemma* pure_bind_on_support
- \- *lemma* bind_on_support_pure
- \- *lemma* bind_on_support_bind_on_support
- \- *lemma* bind_on_support_comm
- \- *def* bind_on_support

Created src/measure_theory/probability_mass_function/monad.lean
- \+ *lemma* pure_apply
- \+ *lemma* support_pure
- \+ *lemma* mem_support_pure_iff:
- \+ *lemma* bind_apply
- \+ *lemma* support_bind
- \+ *lemma* mem_support_bind_iff
- \+ *lemma* coe_bind_apply
- \+ *lemma* pure_bind
- \+ *lemma* bind_pure
- \+ *lemma* bind_bind
- \+ *lemma* bind_comm
- \+ *lemma* bind_on_support_apply
- \+ *lemma* support_bind_on_support
- \+ *lemma* mem_support_bind_on_support_iff
- \+ *lemma* bind_on_support_eq_bind
- \+ *lemma* coe_bind_on_support_apply
- \+ *lemma* bind_on_support_eq_zero_iff
- \+ *lemma* pure_bind_on_support
- \+ *lemma* bind_on_support_pure
- \+ *lemma* bind_on_support_bind_on_support
- \+ *lemma* bind_on_support_comm
- \+ *def* pure
- \+ *def* bind
- \+ *def* bind_on_support



## [2022-01-22 22:28:55](https://github.com/leanprover-community/mathlib/commit/31db25b)
feat(topology/instances/ennreal): continuity of subtraction on ennreal ([#11527](https://github.com/leanprover-community/mathlib/pull/11527))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* mul_inv

Modified src/data/real/nnreal.lean
- \+ *lemma* inv_lt_inv_iff
- \+ *lemma* inv_lt_inv

Modified src/topology/instances/ennreal.lean
- \+ *lemma* tendsto_sub



## [2022-01-22 20:53:55](https://github.com/leanprover-community/mathlib/commit/159d9ac)
split(order/max): Split off `order.basic` ([#11603](https://github.com/leanprover-community/mathlib/pull/11603))
This moves `is_bot`, `is_top`, `no_min_order`, `no_max_order` to a new file `order.max`.
#### Estimated changes
Modified src/order/basic.lean
- \- *lemma* exists_gt
- \- *lemma* not_is_top
- \- *lemma* is_top.unique
- \- *lemma* is_top_or_exists_gt
- \- *lemma* exists_lt
- \- *lemma* not_is_bot
- \- *lemma* is_bot.unique
- \- *lemma* is_bot_or_exists_lt
- \- *def* is_top
- \- *def* is_bot

Modified src/order/bounded_order.lean

Created src/order/max.lean
- \+ *lemma* is_top.to_dual
- \+ *lemma* is_bot.to_dual
- \+ *lemma* not_is_bot
- \+ *lemma* not_is_top
- \+ *lemma* is_bot.unique
- \+ *lemma* is_top.unique
- \+ *lemma* is_top_or_exists_gt
- \+ *lemma* is_bot_or_exists_lt
- \+ *def* is_bot
- \+ *def* is_top

Modified src/order/order_dual.lean
- \- *lemma* is_top.to_dual
- \- *lemma* is_bot.to_dual



## [2022-01-22 20:00:08](https://github.com/leanprover-community/mathlib/commit/5080d64)
feat(topology): add a few lemmas ([#11607](https://github.com/leanprover-community/mathlib/pull/11607))
* add `homeomorph.preimage_interior`, `homeomorph.image_interior`,
  reorder lemmas;
* add `is_open.smul₀` and `interior_smul₀`.
#### Estimated changes
Modified src/topology/algebra/mul_action.lean
- \+ *lemma* is_open.smul₀
- \+ *lemma* interior_smul₀

Modified src/topology/homeomorph.lean
- \+/\- *lemma* preimage_closure
- \+/\- *lemma* image_closure
- \+ *lemma* preimage_interior
- \+ *lemma* image_interior
- \+/\- *lemma* preimage_closure
- \+/\- *lemma* image_closure



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
- \+ *lemma* mk_eq_of
- \+ *lemma* lift_of
- \+ *lemma* map_of
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *lemma* map_map_apply
- \+ *lemma* abelianization_congr_of
- \+ *lemma* abelianization_congr_refl
- \+ *lemma* abelianization_congr_symm
- \+ *lemma* abelianization_congr_trans
- \+ *def* map
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
- \+ *lemma* upper_central_series_one
- \+ *lemma* lower_central_series_one



## [2022-01-22 13:06:17](https://github.com/leanprover-community/mathlib/commit/b630b8c)
feat(order/antichain): Strong antichains ([#11400](https://github.com/leanprover-community/mathlib/pull/11400))
This introduces a predicate `is_strong_antichain` to state that a set is a strong antichain with respect to a relation.
`s` is a strong (upward) antichain wrt `r` if for all `a ≠ b` in `s` there is some `c` such that `¬ r a c` or `¬ r b c`. A strong downward antichain of the swapped relation.
#### Estimated changes
Modified src/data/set/pairwise.lean

Modified src/order/antichain.lean
- \+ *lemma* mono
- \+ *lemma* eq
- \+ *lemma* swap
- \+ *lemma* image
- \+ *lemma* preimage
- \+ *lemma* _root_.is_strong_antichain_insert
- \+ *lemma* set.subsingleton.is_strong_antichain
- \- *lemma* eq_of_related
- \- *lemma* eq_of_related'
- \+ *def* is_strong_antichain

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
- \+ *lemma* mul_to_add_submonoid

Modified src/ring_theory/fractional_ideal.lean



## [2022-01-21 23:07:46](https://github.com/leanprover-community/mathlib/commit/5e9c0a5)
feat(group_theory/subgroup/basic): add center_le_normalizer ([#11590](https://github.com/leanprover-community/mathlib/pull/11590))
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* center_le_normalizer



## [2022-01-21 22:19:47](https://github.com/leanprover-community/mathlib/commit/d99f2fd)
chore(analysis/normed/group/basic): merge `norm` and `semi_norm` lemmas on `prod` and `pi` ([#11492](https://github.com/leanprover-community/mathlib/pull/11492))
`norm` and `semi_norm` are the same operator, so there is no need to have two sets of lemmas.
As a result the elaborator needs a few hints for some applications of the `pi` lemmas, but this is par for the course for pi typeclass instances anyway.
#### Estimated changes
Modified src/analysis/analytic/basic.lean

Modified src/analysis/normed/group/basic.lean
- \+/\- *lemma* prod.norm_def
- \+/\- *lemma* prod.nnnorm_def
- \+/\- *lemma* norm_fst_le
- \+/\- *lemma* norm_snd_le
- \+/\- *lemma* norm_prod_le_iff
- \+/\- *lemma* pi_norm_le_iff
- \+/\- *lemma* pi_norm_lt_iff
- \+/\- *lemma* norm_le_pi_norm
- \+/\- *lemma* pi_norm_const
- \+/\- *lemma* pi_nnnorm_const
- \- *lemma* prod.semi_norm_def
- \- *lemma* prod.nnsemi_norm_def
- \- *lemma* semi_norm_fst_le
- \- *lemma* semi_norm_snd_le
- \- *lemma* semi_norm_prod_le_iff
- \- *lemma* pi_semi_norm_le_iff
- \- *lemma* pi_semi_norm_lt_iff
- \- *lemma* semi_norm_le_pi_norm
- \- *lemma* pi_semi_norm_const
- \- *lemma* pi_nnsemi_norm_const
- \+/\- *lemma* prod.norm_def
- \+/\- *lemma* prod.nnnorm_def
- \+/\- *lemma* norm_fst_le
- \+/\- *lemma* norm_snd_le
- \+/\- *lemma* norm_prod_le_iff
- \+/\- *lemma* pi_norm_le_iff
- \+/\- *lemma* pi_norm_lt_iff
- \+/\- *lemma* norm_le_pi_norm
- \+/\- *lemma* pi_norm_const
- \+/\- *lemma* pi_nnnorm_const

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
- \+ *lemma* fourier_series_repr
- \+ *lemma* has_sum_fourier_series
- \+ *lemma* tsum_sq_fourier_series_repr
- \+ *def* fourier_series



## [2022-01-21 15:40:51](https://github.com/leanprover-community/mathlib/commit/9c39019)
refactor(src/order/bounded): Invert iff direction ([#11582](https://github.com/leanprover-community/mathlib/pull/11582))
That way, `unbounded_gt_iff_unbounded_ge` corresponds to `unbounded_lt_iff_unbounded_le`.
#### Estimated changes
Modified src/order/bounded.lean
- \+ *lemma* unbounded_gt_iff_unbounded_ge
- \- *lemma* unbounded_ge_iff_unbounded_gt



## [2022-01-21 10:54:30](https://github.com/leanprover-community/mathlib/commit/ca79513)
feat(order/bounded): Proved many lemmas about bounded and unbounded sets ([#11179](https://github.com/leanprover-community/mathlib/pull/11179))
These include more convenient characterizations of unboundedness in preorders and linear orders, and many results about bounded intervals and initial segments.
#### Estimated changes
Created src/order/bounded.lean
- \+ *lemma* unbounded_le_of_forall_exists_lt
- \+ *lemma* unbounded_le_iff
- \+ *lemma* unbounded_lt_of_forall_exists_le
- \+ *lemma* unbounded_lt_iff
- \+ *lemma* unbounded_ge_of_forall_exists_gt
- \+ *lemma* unbounded_ge_iff
- \+ *lemma* unbounded_gt_of_forall_exists_ge
- \+ *lemma* unbounded_gt_iff
- \+ *lemma* bounded.rel_mono
- \+ *lemma* bounded_le_of_bounded_lt
- \+ *lemma* unbounded.rel_mono
- \+ *lemma* unbounded_lt_of_unbounded_le
- \+ *lemma* bounded_le_iff_bounded_lt
- \+ *lemma* unbounded_lt_iff_unbounded_le
- \+ *lemma* bounded_ge_of_bounded_gt
- \+ *lemma* unbounded_gt_of_unbounded_ge
- \+ *lemma* bounded_ge_iff_bounded_gt
- \+ *lemma* unbounded_ge_iff_unbounded_gt
- \+ *theorem* bounded.mono
- \+ *theorem* unbounded.mono
- \+ *theorem* bounded_self
- \+ *theorem* bounded_lt_Iio
- \+ *theorem* bounded_le_Iio
- \+ *theorem* bounded_le_Iic
- \+ *theorem* bounded_lt_Iic
- \+ *theorem* bounded_gt_Ioi
- \+ *theorem* bounded_ge_Ioi
- \+ *theorem* bounded_ge_Ici
- \+ *theorem* bounded_gt_Ici
- \+ *theorem* bounded_lt_Ioo
- \+ *theorem* bounded_lt_Ico
- \+ *theorem* bounded_lt_Ioc
- \+ *theorem* bounded_lt_Icc
- \+ *theorem* bounded_le_Ioo
- \+ *theorem* bounded_le_Ico
- \+ *theorem* bounded_le_Ioc
- \+ *theorem* bounded_le_Icc
- \+ *theorem* bounded_gt_Ioo
- \+ *theorem* bounded_gt_Ioc
- \+ *theorem* bounded_gt_Ico
- \+ *theorem* bounded_gt_Icc
- \+ *theorem* bounded_ge_Ioo
- \+ *theorem* bounded_ge_Ioc
- \+ *theorem* bounded_ge_Ico
- \+ *theorem* bounded_ge_Icc
- \+ *theorem* unbounded_le_Ioi
- \+ *theorem* unbounded_le_Ici
- \+ *theorem* unbounded_lt_Ioi
- \+ *theorem* unbounded_lt_Ici
- \+ *theorem* bounded_inter_not
- \+ *theorem* unbounded_inter_not
- \+ *theorem* bounded_le_inter_not_le
- \+ *theorem* unbounded_le_inter_not_le
- \+ *theorem* bounded_le_inter_lt
- \+ *theorem* unbounded_le_inter_lt
- \+ *theorem* bounded_le_inter_le
- \+ *theorem* unbounded_le_inter_le
- \+ *theorem* bounded_lt_inter_not_lt
- \+ *theorem* unbounded_lt_inter_not_lt
- \+ *theorem* bounded_lt_inter_le
- \+ *theorem* unbounded_lt_inter_le
- \+ *theorem* bounded_lt_inter_lt
- \+ *theorem* unbounded_lt_inter_lt
- \+ *theorem* bounded_ge_inter_not_ge
- \+ *theorem* unbounded_ge_inter_not_ge
- \+ *theorem* bounded_ge_inter_gt
- \+ *theorem* unbounded_ge_inter_gt
- \+ *theorem* bounded_ge_inter_ge
- \+ *theorem* unbounded_ge_iff_unbounded_inter_ge
- \+ *theorem* bounded_gt_inter_not_gt
- \+ *theorem* unbounded_gt_inter_not_gt
- \+ *theorem* bounded_gt_inter_ge
- \+ *theorem* unbounded_inter_ge
- \+ *theorem* bounded_gt_inter_gt
- \+ *theorem* unbounded_gt_inter_gt

Modified src/order/lattice.lean
- \+ *theorem* lt_sup_of_lt_left
- \+ *theorem* lt_sup_of_lt_right
- \+ *theorem* inf_lt_of_left_lt
- \+ *theorem* inf_lt_of_right_lt

Modified src/order/rel_classes.lean
- \+/\- *def* bounded
- \+/\- *def* bounded



## [2022-01-21 04:46:35](https://github.com/leanprover-community/mathlib/commit/884d813)
chore(analysis/inner_product_space/dual): remove unneeded `complete_space` assumption in four lemmas ([#11578](https://github.com/leanprover-community/mathlib/pull/11578))
We remove the `[complete_space E]` assumption in four lemmas.
#### Estimated changes
Modified src/analysis/inner_product_space/dual.lean
- \+/\- *lemma* ext_inner_left
- \+/\- *lemma* ext_inner_right
- \+/\- *lemma* ext_inner_left_basis
- \+/\- *lemma* ext_inner_right_basis
- \+/\- *lemma* ext_inner_left
- \+/\- *lemma* ext_inner_right
- \+/\- *lemma* ext_inner_left_basis
- \+/\- *lemma* ext_inner_right_basis



## [2022-01-21 03:07:37](https://github.com/leanprover-community/mathlib/commit/80e072e)
feat(data/finset/basic): random golf ([#11576](https://github.com/leanprover-community/mathlib/pull/11576))
#### Estimated changes
Modified src/data/finset/basic.lean



## [2022-01-21 00:16:10](https://github.com/leanprover-community/mathlib/commit/d71cab9)
feat(analysis/seminorm): add composition with linear maps ([#11477](https://github.com/leanprover-community/mathlib/pull/11477))
This PR defines the composition of seminorms with linear maps and shows that composition is monotone and calculates the seminorm ball of the composition.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* zero_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_id
- \+ *lemma* comp_zero
- \+ *lemma* zero_comp
- \+ *lemma* comp_comp
- \+ *lemma* add_comp
- \+ *lemma* comp_triangle
- \+ *lemma* smul_comp
- \+ *lemma* comp_mono
- \+ *lemma* comp_smul
- \+ *lemma* comp_smul_apply
- \+ *lemma* ball_comp
- \+ *def* comp



## [2022-01-20 22:45:37](https://github.com/leanprover-community/mathlib/commit/6c97821)
feat(group_theory/submonoid/pointwise): add pointwise multiplication to `add_submonoid`s ([#11522](https://github.com/leanprover-community/mathlib/pull/11522))
#### Estimated changes
Modified src/group_theory/submonoid/pointwise.lean
- \+ *lemma* mul_subset_mul
- \+ *theorem* mul_mem_mul
- \+ *theorem* mul_le
- \+ *theorem* closure_mul_closure
- \+ *theorem* mul_bot
- \+ *theorem* bot_mul
- \+ *theorem* mul_le_mul
- \+ *theorem* mul_le_mul_left
- \+ *theorem* mul_le_mul_right



## [2022-01-20 19:35:50](https://github.com/leanprover-community/mathlib/commit/adadd4a)
feat(measure_theory/function/lp_space): some variations of Markov's inequality formulated using `snorm` ([#11478](https://github.com/leanprover-community/mathlib/pull/11478))
#### Estimated changes
Modified docs/undergrad.yaml

Modified src/measure_theory/function/lp_space.lean
- \+ *lemma* pow_mul_meas_ge_le_snorm
- \+ *lemma* mul_meas_ge_le_pow_snorm
- \+ *lemma* mul_meas_ge_le_pow_snorm'
- \+ *lemma* meas_ge_le_mul_pow_snorm
- \+ *lemma* pow_mul_meas_ge_le_norm
- \+ *lemma* mul_meas_ge_le_pow_norm
- \+ *lemma* mul_meas_ge_le_pow_norm'
- \+ *lemma* meas_ge_le_mul_pow_norm



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
- \+ *lemma* eq_of_ne_mem



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
- \+ *lemma* is_decending_rev_series_of_is_ascending
- \+ *lemma* is_ascending_rev_series_of_is_descending
- \+ *lemma* least_ascending_central_series_length_eq_nilpotency_class
- \+ *lemma* least_descending_central_series_length_eq_nilpotency_class
- \+ *lemma* lower_central_series_length_eq_nilpotency_class



## [2022-01-20 16:01:23](https://github.com/leanprover-community/mathlib/commit/b5e542d)
feat(measure_theory/measurable_space): defining a measurable function on countably many pieces ([#11532](https://github.com/leanprover-community/mathlib/pull/11532))
Also, remove `open_locale classical` in this file and add decidability assumptions where needed. And add a few isolated useful lemmas.
#### Estimated changes
Modified src/measure_theory/group/basic.lean

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable_find_greatest'
- \+/\- *lemma* measurable_find_greatest
- \+/\- *lemma* measurable_find
- \+/\- *lemma* measurable_from_prod_encodable
- \+ *lemma* measurable.find
- \+ *lemma* exists_measurable_piecewise_nat
- \+/\- *lemma* measurable_update
- \+/\- *lemma* measurable_set_pi_of_nonempty
- \+/\- *lemma* measurable_tprod_elim
- \+/\- *lemma* measurable_tprod_elim'
- \+/\- *lemma* measurable_find_greatest'
- \+/\- *lemma* measurable_find_greatest
- \+/\- *lemma* measurable_find
- \+/\- *lemma* measurable_from_prod_encodable
- \+/\- *lemma* measurable_update
- \+/\- *lemma* measurable_set_pi_of_nonempty
- \+/\- *lemma* measurable_tprod_elim
- \+/\- *lemma* measurable_tprod_elim'
- \+ *def* pi_measurable_equiv_tprod

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
- \+ *lemma* tendsto_uniformly_on.comp'
- \+ *lemma* tendsto_uniformly.comp'



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
- \+ *lemma* inner_single_left
- \+ *lemma* inner_single_right
- \+ *lemma* _root_.orthonormal.exists_hilbert_basis_extension
- \+ *lemma* _root_.exists_hilbert_basis

Modified src/analysis/inner_product_space/projection.lean
- \- *lemma* maximal_orthonormal_iff_dense_span
- \- *lemma* exists_subset_is_orthonormal_dense_span
- \- *lemma* exists_is_orthonormal_dense_span

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* coe_of_surjective



## [2022-01-20 08:57:41](https://github.com/leanprover-community/mathlib/commit/53650a0)
feat(*): lemmas about `disjoint` on `set`s and `filter`s ([#11549](https://github.com/leanprover-community/mathlib/pull/11549))
#### Estimated changes
Modified src/data/set/function.lean

Modified src/data/set/lattice.lean
- \+ *lemma* disjoint_iff_forall_ne
- \+ *lemma* _root_.disjoint.ne_of_mem

Modified src/order/filter/basic.lean
- \+ *lemma* disjoint_comap
- \+/\- *lemma* map_inf
- \+ *lemma* disjoint_map
- \+/\- *lemma* map_inf

Modified src/topology/basic.lean
- \+ *lemma* disjoint.closure_left
- \+ *lemma* disjoint.closure_right



## [2022-01-20 07:43:43](https://github.com/leanprover-community/mathlib/commit/e96e55d)
feat(analysis/normed_space/finite_dimension): extending partially defined Lipschitz functions ([#11530](https://github.com/leanprover-community/mathlib/pull/11530))
Any Lipschitz function on a subset of a metric space, into a finite-dimensional real vector space, can be extended to a globally defined Lipschitz function (up to worsening slightly the Lipschitz constant).
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* coe_to_continuous_linear_equiv
- \+ *lemma* coe_to_continuous_linear_equiv'
- \+ *lemma* coe_to_continuous_linear_equiv_symm
- \+ *lemma* coe_to_continuous_linear_equiv_symm'
- \+ *lemma* to_linear_equiv_to_continuous_linear_equiv
- \+ *lemma* to_linear_equiv_to_continuous_linear_equiv_symm
- \+ *lemma* lipschitz_extension_constant_pos
- \+ *theorem* lipschitz_on_with.extend_finite_dimension
- \+ *def* to_continuous_linear_equiv
- \+ *def* lipschitz_extension_constant
- \- *def* linear_equiv.to_continuous_linear_equiv

Modified src/measure_theory/measure/haar_lebesgue.lean

Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* comp_lipschitz_on_with
- \+/\- *lemma* continuous_at_of_locally_lipschitz
- \+ *lemma* lipschitz_on_with.extend_real
- \+ *lemma* lipschitz_on_with.extend_pi
- \+/\- *lemma* continuous_at_of_locally_lipschitz



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
- \+/\- *lemma* measurable_set_mul_support



## [2022-01-19 19:16:21](https://github.com/leanprover-community/mathlib/commit/7ee41aa)
feat(data/finsupp/basic): lemmas about map domain with only inj_on hypotheses ([#11484](https://github.com/leanprover-community/mathlib/pull/11484))
Also a lemma `sum_update_add` expressing the sum of an update in a monoid in terms of the original sum and the value of the update.
And golf `map_domain_smul`.
From flt-regular.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* map_domain_apply'
- \+ *lemma* map_domain_support_of_inj_on
- \+/\- *lemma* map_domain_support_of_injective
- \+ *lemma* sum_update_add
- \+ *lemma* map_domain_inj_on
- \+/\- *lemma* map_domain_support_of_injective



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
- \+ *lemma* coe_bUnion

Modified src/data/finset/slice.lean
- \+ *lemma* sized_Union
- \+ *lemma* sized_Union₂
- \+ *lemma* sized.subsingleton'
- \+ *lemma* sized.empty_mem_iff
- \+ *lemma* sized.univ_mem_iff
- \+ *lemma* sized_powerset_len
- \+/\- *lemma* pairwise_disjoint_slice
- \+ *lemma* bUnion_slice
- \+ *lemma* sum_card_slice
- \+/\- *lemma* pairwise_disjoint_slice

Modified src/data/set/basic.lean
- \+ *lemma* subsingleton_of_forall_eq

Modified src/data/set/finite.lean
- \- *lemma* coe_bUnion

Modified src/order/antichain.lean
- \+ *lemma* is_antichain_singleton
- \+/\- *lemma* set.subsingleton.is_antichain
- \+ *lemma* is_antichain_and_least_iff
- \+ *lemma* is_antichain_and_greatest_iff
- \+ *lemma* is_antichain.least_iff
- \+ *lemma* is_antichain.greatest_iff
- \+ *lemma* is_least.antichain_iff
- \+ *lemma* is_greatest.antichain_iff
- \+ *lemma* is_antichain.bot_mem_iff
- \+ *lemma* is_antichain.top_mem_iff
- \+/\- *lemma* set.subsingleton.is_antichain

Modified src/order/bounds.lean
- \+ *lemma* bot_mem_lower_bounds
- \+ *lemma* top_mem_upper_bounds
- \+ *lemma* is_least_bot_iff
- \+ *lemma* is_greatest_top_iff



## [2022-01-19 15:39:30](https://github.com/leanprover-community/mathlib/commit/c72e709)
feat(data/sum/interval): The disjoint sum of two locally finite orders is locally finite ([#11351](https://github.com/leanprover-community/mathlib/pull/11351))
This proves `locally_finite_order (α ⊕ β)` where `α` and `β` are locally finite themselves.
#### Estimated changes
Created src/data/sum/interval.lean
- \+ *lemma* mem_sum_lift₂
- \+ *lemma* inl_mem_sum_lift₂
- \+ *lemma* inr_mem_sum_lift₂
- \+ *lemma* sum_lift₂_eq_empty
- \+ *lemma* sum_lift₂_nonempty
- \+ *lemma* sum_lift₂_mono
- \+ *lemma* Icc_inl_inl
- \+ *lemma* Ico_inl_inl
- \+ *lemma* Ioc_inl_inl
- \+ *lemma* Ioo_inl_inl
- \+ *lemma* Icc_inl_inr
- \+ *lemma* Ico_inl_inr
- \+ *lemma* Ioc_inl_inr
- \+ *lemma* Ioo_inl_inr
- \+ *lemma* Icc_inr_inl
- \+ *lemma* Ico_inr_inl
- \+ *lemma* Ioc_inr_inl
- \+ *lemma* Ioo_inr_inl
- \+ *lemma* Icc_inr_inr
- \+ *lemma* Ico_inr_inr
- \+ *lemma* Ioc_inr_inr
- \+ *lemma* Ioo_inr_inr
- \+ *def* sum_lift₂



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
- \+ *lemma* ring_hom_eval₂_cast_int_ring_hom
- \+ *lemma* eval₂_int_cast_ring_hom_X
- \- *lemma* ring_hom_eval₂_algebra_map_int
- \- *lemma* eval₂_algebra_map_int_X



## [2022-01-19 10:24:24](https://github.com/leanprover-community/mathlib/commit/4ad74ae)
chore(algebra/order/sub): Generalize to `preorder` and `add_comm_semigroup` ([#11463](https://github.com/leanprover-community/mathlib/pull/11463))
This generalizes a bunch of lemmas from `partial_order` to `preorder` and from `add_comm_monoid` to `add_comm_semigroup`.
It also adds `tsub_tsub_le_tsub_add : a - (b - c) ≤ a - b + c`.
#### Estimated changes
Modified src/algebra/order/sub.lean
- \+/\- *lemma* tsub_le_tsub_left
- \+/\- *lemma* tsub_le_tsub
- \+/\- *lemma* add_tsub_le_assoc
- \+/\- *lemma* add_le_add_add_tsub
- \+/\- *lemma* le_tsub_add_add
- \+/\- *lemma* tsub_le_tsub_add_tsub
- \+/\- *lemma* tsub_tsub_tsub_le_tsub
- \+ *lemma* tsub_tsub_le_tsub_add
- \+/\- *lemma* le_add_tsub_swap
- \+/\- *lemma* le_add_tsub'
- \+/\- *lemma* le_tsub_of_add_le_left
- \+/\- *lemma* le_tsub_of_add_le_right
- \+/\- *lemma* tsub_le_tsub_left
- \+/\- *lemma* tsub_le_tsub
- \+/\- *lemma* add_le_add_add_tsub
- \+/\- *lemma* add_tsub_le_assoc
- \+/\- *lemma* le_tsub_add_add
- \+/\- *lemma* tsub_le_tsub_add_tsub
- \+/\- *lemma* tsub_tsub_tsub_le_tsub
- \+/\- *lemma* le_add_tsub_swap
- \+/\- *lemma* le_add_tsub'
- \+/\- *lemma* le_tsub_of_add_le_left
- \+/\- *lemma* le_tsub_of_add_le_right



## [2022-01-19 06:53:49](https://github.com/leanprover-community/mathlib/commit/1cfb97d)
feat(analysis/normed/group/pointwise): the closed thickening of a compact set is the addition of a closed ball. ([#11528](https://github.com/leanprover-community/mathlib/pull/11528))
#### Estimated changes
Modified src/analysis/normed/group/pointwise.lean
- \+ *lemma* is_compact.cthickening_eq_add_closed_ball

Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* thickening_singleton
- \+ *lemma* cthickening_singleton
- \+ *lemma* closed_ball_subset_cthickening_singleton
- \+ *lemma* closed_ball_subset_cthickening
- \+ *lemma* _root_.is_compact.cthickening_eq_bUnion_closed_ball



## [2022-01-19 06:53:48](https://github.com/leanprover-community/mathlib/commit/ff9b757)
feat(category_theory/bicategory/locally_discrete): define locally discrete bicategory ([#11402](https://github.com/leanprover-community/mathlib/pull/11402))
This PR defines the locally discrete bicategory on a category.
#### Estimated changes
Created src/category_theory/bicategory/locally_discrete.lean
- \+ *def* locally_discrete
- \+ *def* functor.to_oplax_functor

Modified src/category_theory/bicategory/strict.lean
- \+ *lemma* whisker_left_eq_to_hom
- \+ *lemma* eq_to_hom_whisker_right



## [2022-01-18 21:06:28](https://github.com/leanprover-community/mathlib/commit/6dd6525)
feat(measure_theory/measure/measure_space): better definition of to_measurable ([#11529](https://github.com/leanprover-community/mathlib/pull/11529))
Currently, `to_measurable μ t` picks a measurable superset of `t` with the same measure. When the measure of `t` is infinite, it is most often useless. This PR adjusts the definition so that, in the case of sigma-finite spaces, `to_measurable μ t` has good properties even when `t` has infinite measure.
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* nonempty_inter_of_measure_lt_add
- \+ *lemma* nonempty_inter_of_measure_lt_add'
- \+ *lemma* exists_subset_measure_lt_top
- \+ *lemma* measure_to_measurable_inter_of_sigma_finite
- \+ *lemma* is_locally_finite_measure_of_is_finite_measure_on_compacts

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* ae_le_set_inter
- \+ *lemma* ae_eq_set_inter
- \+/\- *def* to_measurable
- \+/\- *def* to_measurable



## [2022-01-18 20:38:47](https://github.com/leanprover-community/mathlib/commit/de53f9c)
feat(data/nat/factorization): add two convenience lemmas ([#11543](https://github.com/leanprover-community/mathlib/pull/11543))
Adds convenience lemmas `prime_of_mem_factorization` and `pos_of_mem_factorization`.
Also adds a different proof of `factorization_prod_pow_eq_self` that doesn't depend on `multiplicative_factorization` and so can appear earlier in the file.
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+/\- *lemma* factorization_prod_pow_eq_self
- \+ *lemma* prime_of_mem_factorization
- \+ *lemma* pos_of_mem_factorization
- \+/\- *lemma* factorization_prod_pow_eq_self



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
- \+ *lemma* lmul_left_to_add_monoid_hom
- \+ *lemma* lmul_right_to_add_monoid_hom

Modified src/group_theory/submonoid/basic.lean
- \+ *lemma* closure_singleton_le_iff_mem
- \+ *lemma* mem_supr
- \+ *lemma* supr_eq_closure

Modified src/linear_algebra/basic.lean
- \+ *lemma* map_to_add_submonoid
- \+/\- *lemma* map_supr_comap_of_sujective
- \+/\- *lemma* map_infi_comap_of_surjective
- \+/\- *lemma* comap_infi_map_of_injective
- \+/\- *lemma* comap_supr_map_of_injective
- \+/\- *lemma* _root_.linear_map.infi_invariant
- \+ *lemma* sup_to_add_submonoid
- \+ *lemma* sup_to_add_subgroup
- \+ *lemma* supr_to_add_submonoid
- \+/\- *lemma* map_supr_comap_of_sujective
- \+/\- *lemma* map_infi_comap_of_surjective
- \+/\- *lemma* comap_infi_map_of_injective
- \+/\- *lemma* comap_supr_map_of_injective
- \+/\- *lemma* _root_.linear_map.infi_invariant



## [2022-01-18 16:08:17](https://github.com/leanprover-community/mathlib/commit/a0ff65d)
feat(ring_theory/norm): add is_integral_norm ([#11489](https://github.com/leanprover-community/mathlib/pull/11489))
We add `is_integral_norm`.
From flt-regular
#### Estimated changes
Modified src/ring_theory/norm.lean
- \+ *lemma* _root_.intermediate_field.adjoin_simple.norm_gen_eq_one
- \+ *lemma* _root_.intermediate_field.adjoin_simple.norm_gen_eq_prod_roots
- \+ *lemma* norm_eq_prod_roots
- \+/\- *lemma* prod_embeddings_eq_finrank_pow
- \+ *lemma* is_integral_norm
- \+/\- *lemma* prod_embeddings_eq_finrank_pow



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
- \+/\- *lemma* null_of_locally_null
- \+ *lemma* exists_mem_forall_mem_nhds_within_pos_measure
- \+ *lemma* exists_ne_forall_mem_nhds_pos_measure_preimage
- \+/\- *lemma* null_of_locally_null

Modified src/measure_theory/measure/outer_measure.lean
- \+ *lemma* null_of_locally_null
- \+ *lemma* exists_mem_forall_mem_nhds_within_pos

Modified src/topology/metric_space/basic.lean
- \+ *lemma* diam_le_of_subset_closed_ball
- \+/\- *lemma* diam_closed_ball
- \+/\- *lemma* diam_closed_ball



## [2022-01-18 12:22:35](https://github.com/leanprover-community/mathlib/commit/be9a5de)
feat(topology/separation): add `t1_space_tfae` ([#11534](https://github.com/leanprover-community/mathlib/pull/11534))
Also add some lemmas about `filter.disjoint`.
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* has_basis.disjoint_basis_iff
- \+ *lemma* disjoint_principal_right
- \+ *lemma* disjoint_principal_left
- \+ *lemma* disjoint_principal_principal
- \+ *lemma* disjoint_pure_pure
- \- *lemma* inf_eq_bot_iff
- \- *lemma* mem_iff_disjoint_principal_compl
- \- *lemma* le_iff_forall_disjoint_principal_compl

Modified src/order/filter/basic.lean
- \+ *lemma* inf_eq_bot_iff

Modified src/topology/algebra/ordered/basic.lean

Modified src/topology/separation.lean
- \+ *lemma* t1_space_tfae
- \+ *lemma* t1_space_iff_exists_open
- \+ *lemma* t1_space_iff_disjoint_pure_nhds
- \+ *lemma* t1_space_iff_disjoint_nhds_pure
- \+ *lemma* disjoint_pure_nhds
- \+ *lemma* disjoint_nhds_pure
- \+ *lemma* t1_space_antitone
- \- *lemma* finite.is_closed
- \- *lemma* t1_space_antimono
- \- *lemma* t1_iff_exists_open



## [2022-01-18 12:22:34](https://github.com/leanprover-community/mathlib/commit/135a92d)
feat(data/set): two simple lemmas ([#11531](https://github.com/leanprover-community/mathlib/pull/11531))
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* inj_on.image_inter
- \+ *lemma* _root_.disjoint.image

Modified src/data/set/pairwise.lean
- \+ *lemma* pairwise_disjoint.mono

Modified src/measure_theory/measure/haar_lebesgue.lean



## [2022-01-18 12:22:32](https://github.com/leanprover-community/mathlib/commit/5bbc187)
feat(algebra/lie/nilpotent): a non-trivial nilpotent Lie module has non-trivial maximal trivial submodule ([#11515](https://github.com/leanprover-community/mathlib/pull/11515))
The main result is `lie_module.nontrivial_max_triv_of_is_nilpotent`
#### Estimated changes
Modified src/algebra/lie/abelian.lean
- \+ *lemma* le_max_triv_iff_bracket_eq_bot

Modified src/algebra/lie/ideal_operations.lean
- \+ *lemma* lie_eq_bot_iff

Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* antitone_lower_central_series
- \+ *lemma* nilpotency_length_eq_zero_iff
- \+ *lemma* nilpotency_length_eq_succ_iff
- \+ *lemma* lower_central_series_last_le_max_triv
- \+ *lemma* nontrivial_lower_central_series_last
- \+ *lemma* nontrivial_max_triv_of_is_nilpotent

Modified src/algebra/lie/submodule.lean
- \+ *lemma* nontrivial_iff_ne_bot
- \+ *lemma* lie_span_eq_bot_iff

Modified src/data/set/basic.lean
- \+ *theorem* nontrivial_mono



## [2022-01-18 10:53:40](https://github.com/leanprover-community/mathlib/commit/a0da4f1)
feat(algebra/big_operators/basic): Reindexing a product with a permutation ([#11344](https://github.com/leanprover-community/mathlib/pull/11344))
This proves `(∏ x in s, f (σ x)) = ∏ x in s, f x` for a permutation `σ`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* _root_.equiv.perm.prod_comp
- \+ *lemma* _root_.equiv.perm.prod_comp'

Modified src/data/finset/basic.lean
- \+ *lemma* map_perm

Modified src/data/finset/card.lean
- \+ *lemma* map_eq_of_subset

Modified src/linear_algebra/matrix/determinant.lean

Modified src/number_theory/sum_four_squares.lean



## [2022-01-18 09:14:43](https://github.com/leanprover-community/mathlib/commit/8d5caba)
chore(order/bounded_order): golf ([#11538](https://github.com/leanprover-community/mathlib/pull/11538))
#### Estimated changes
Modified src/order/bounded_order.lean
- \+ *lemma* top_le_iff
- \+ *lemma* top_unique
- \+ *lemma* eq_top_iff
- \+ *lemma* eq_top_mono
- \+/\- *lemma* eq_top_or_lt_top
- \+/\- *lemma* ne_top_of_lt
- \+/\- *lemma* ne.lt_top
- \+/\- *lemma* ne.lt_top'
- \+ *lemma* ne_top_of_le_ne_top
- \+ *lemma* le_bot_iff
- \+ *lemma* bot_unique
- \+ *lemma* eq_bot_iff
- \+ *lemma* eq_bot_mono
- \+/\- *lemma* bot_lt_iff_ne_bot
- \+/\- *lemma* eq_bot_or_bot_lt
- \+/\- *lemma* ne_bot_of_gt
- \+/\- *lemma* eq_bot_of_minimal
- \+ *lemma* ne_bot_of_le_ne_bot
- \+/\- *lemma* eq_top_or_lt_top
- \+/\- *lemma* ne_top_of_lt
- \+/\- *lemma* ne.lt_top
- \+/\- *lemma* ne.lt_top'
- \+/\- *lemma* bot_lt_iff_ne_bot
- \+/\- *lemma* eq_bot_or_bot_lt
- \+/\- *lemma* ne_bot_of_gt
- \+/\- *lemma* eq_bot_of_minimal
- \- *theorem* top_unique
- \- *theorem* eq_top_iff
- \- *theorem* top_le_iff
- \- *theorem* eq_top_mono
- \- *theorem* ne_top_of_le_ne_top
- \- *theorem* bot_unique
- \- *theorem* eq_bot_iff
- \- *theorem* le_bot_iff
- \- *theorem* ne_bot_of_le_ne_bot
- \- *theorem* eq_bot_mono



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
- \+ *lemma* weighted_smul_union'
- \+/\- *lemma* weighted_smul_union
- \+/\- *lemma* weighted_smul_union

Modified src/measure_theory/integral/interval_integral.lean

Modified src/measure_theory/integral/set_integral.lean
- \+/\- *lemma* integral_union_ae
- \+/\- *lemma* integral_union
- \+/\- *lemma* integral_diff
- \+/\- *lemma* integral_union
- \+/\- *lemma* integral_union_ae
- \+/\- *lemma* integral_diff

Modified src/measure_theory/measure/ae_disjoint.lean
- \+ *lemma* diff_ae_eq_left
- \+ *lemma* diff_ae_eq_right
- \+ *lemma* measure_diff_left
- \+ *lemma* measure_diff_right

Modified src/measure_theory/measure/haar_lebesgue.lean

Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_union
- \+ *lemma* measure_union'
- \+/\- *lemma* measure_inter_add_diff
- \+ *lemma* measure_diff_add_inter
- \+/\- *lemma* measure_union_add_inter
- \+/\- *lemma* measure_union_add_inter'
- \+/\- *lemma* measure_diff
- \+/\- *lemma* measure_diff_lt_of_lt_add
- \+/\- *lemma* measure_diff_le_iff_le_add
- \+/\- *lemma* measure_eq_measure_of_null_diff
- \+ *lemma* restrict_union_add_inter₀
- \+/\- *lemma* restrict_union_add_inter
- \+ *lemma* restrict_union_add_inter'
- \+ *lemma* restrict_union₀
- \+/\- *lemma* restrict_union
- \+ *lemma* restrict_union'
- \+/\- *lemma* measure_union
- \+/\- *lemma* measure_diff
- \+/\- *lemma* measure_diff_lt_of_lt_add
- \+/\- *lemma* measure_diff_le_iff_le_add
- \+/\- *lemma* measure_eq_measure_of_null_diff
- \- *lemma* exists_subordinate_pairwise_disjoint
- \- *lemma* measure_Union_of_null_inter
- \+/\- *lemma* measure_inter_add_diff
- \+/\- *lemma* measure_union_add_inter
- \+/\- *lemma* measure_union_add_inter'
- \- *lemma* restrict_union_apply
- \+/\- *lemma* restrict_union
- \+/\- *lemma* restrict_union_add_inter

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* diff_null_ae_eq_self

Modified src/measure_theory/measure/null_measurable.lean
- \+ *lemma* exists_subordinate_pairwise_disjoint
- \+ *lemma* measure_union₀_aux
- \+ *lemma* measure_inter_add_diff₀
- \+ *lemma* measure_union_add_inter₀
- \+ *lemma* measure_union_add_inter₀'
- \+/\- *lemma* measure_union₀
- \+ *lemma* measure_union₀'
- \+/\- *lemma* measure_union₀

Modified src/measure_theory/measure/regular.lean
- \+/\- *lemma* _root_.measurable_set.exists_is_open_diff_lt
- \+/\- *lemma* measurable_set_of_open
- \+/\- *lemma* inner_regular_measurable
- \+/\- *lemma* _root_.measurable_set.exists_is_compact_lt_add
- \+/\- *lemma* _root_.measurable_set.exists_lt_is_compact_of_ne_top
- \+/\- *lemma* _root_.measurable_set.measure_eq_supr_is_compact_of_ne_top
- \+/\- *lemma* inner_regular_measurable
- \+/\- *lemma* _root_.measurable_set.exists_is_closed_lt_add
- \+/\- *lemma* _root_.measurable_set.measure_eq_supr_is_closed_of_ne_top
- \+/\- *lemma* _root_.measurable_set.exists_is_open_diff_lt
- \+/\- *lemma* measurable_set_of_open
- \+/\- *lemma* inner_regular_measurable
- \+/\- *lemma* _root_.measurable_set.exists_is_compact_lt_add
- \+/\- *lemma* _root_.measurable_set.exists_lt_is_compact_of_ne_top
- \+/\- *lemma* _root_.measurable_set.measure_eq_supr_is_compact_of_ne_top
- \+/\- *lemma* inner_regular_measurable
- \+/\- *lemma* _root_.measurable_set.exists_is_closed_lt_add
- \+/\- *lemma* _root_.measurable_set.measure_eq_supr_is_closed_of_ne_top

Modified src/measure_theory/measure/stieltjes.lean



## [2022-01-18 09:14:39](https://github.com/leanprover-community/mathlib/commit/f23c00f)
chore(algebra/order/ring): move lemmas about invertible into a new file ([#11511](https://github.com/leanprover-community/mathlib/pull/11511))
The motivation here is to eventually be able to use the `one_pow` lemma in `algebra.group.units`. This is one very small step in that direction.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean

Created src/algebra/order/invertible.lean
- \+ *lemma* inv_of_pos
- \+ *lemma* inv_of_nonpos
- \+ *lemma* inv_of_nonneg
- \+ *lemma* inv_of_lt_zero
- \+ *lemma* inv_of_le_one

Modified src/algebra/order/ring.lean
- \- *lemma* inv_of_pos
- \- *lemma* inv_of_nonpos
- \- *lemma* inv_of_nonneg
- \- *lemma* inv_of_lt_zero
- \- *lemma* inv_of_le_one

Modified src/analysis/convex/basic.lean

Modified src/linear_algebra/affine_space/ordered.lean



## [2022-01-18 07:45:51](https://github.com/leanprover-community/mathlib/commit/01fa7f5)
feat(data/fintype/basic): `one_lt_card_iff` and `two_lt_card_iff` ([#11524](https://github.com/leanprover-community/mathlib/pull/11524))
This PR adds `one_lt_card_iff` and `two_lt_card_iff`.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* one_lt_card_iff
- \+ *lemma* two_lt_card_iff



## [2022-01-18 07:09:41](https://github.com/leanprover-community/mathlib/commit/e895c8f)
chore(cone_category): generalize universes ([#11539](https://github.com/leanprover-community/mathlib/pull/11539))
#### Estimated changes
Modified src/category_theory/limits/cone_category.lean
- \+/\- *def* is_limit.of_preserves_cone_terminal
- \+/\- *def* is_limit.of_reflects_cone_terminal
- \+/\- *def* is_colimit.of_preserves_cocone_initial
- \+/\- *def* is_colimit.of_reflects_cocone_initial
- \+/\- *def* is_limit.of_preserves_cone_terminal
- \+/\- *def* is_limit.of_reflects_cone_terminal
- \+/\- *def* is_colimit.of_preserves_cocone_initial
- \+/\- *def* is_colimit.of_reflects_cocone_initial



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
- \+/\- *lemma* forall₂_congr
- \+/\- *lemma* forall₃_congr
- \+/\- *lemma* forall₄_congr
- \+ *lemma* forall₅_congr
- \+/\- *lemma* exists₂_congr
- \+/\- *lemma* exists₃_congr
- \+/\- *lemma* exists₄_congr
- \+ *lemma* exists₅_congr
- \+/\- *lemma* forall_imp
- \+/\- *lemma* forall_imp
- \+/\- *lemma* forall₂_congr
- \+/\- *lemma* forall₃_congr
- \+/\- *lemma* forall₄_congr
- \+/\- *lemma* exists₂_congr
- \+/\- *lemma* exists₃_congr
- \+/\- *lemma* exists₄_congr

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
- \+ *lemma* top_to_subring
- \+ *lemma* to_submodule_eq_top
- \+ *lemma* to_subsemiring_eq_top
- \+ *lemma* to_subring_eq_top
- \+ *theorem* to_subsemiring_injective
- \+ *theorem* to_subsemiring_inj
- \+ *theorem* to_subring_injective
- \+ *theorem* to_subring_inj



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
- \+ *lemma* coe_to_linear_equiv
- \+ *lemma* coe_to_linear_equiv_symm
- \+ *lemma* coe_to_nat_linear_equiv
- \+ *lemma* to_nat_linear_equiv_to_add_equiv
- \+ *lemma* _root_.linear_equiv.to_add_equiv_to_nat_linear_equiv
- \+ *lemma* to_nat_linear_equiv_symm
- \+ *lemma* to_nat_linear_equiv_refl
- \+ *lemma* to_nat_linear_equiv_trans
- \+ *lemma* coe_to_int_linear_equiv
- \+ *lemma* to_int_linear_equiv_to_add_equiv
- \+ *lemma* _root_.linear_equiv.to_add_equiv_to_int_linear_equiv
- \+ *lemma* to_int_linear_equiv_symm
- \+ *lemma* to_int_linear_equiv_refl
- \+ *lemma* to_int_linear_equiv_trans
- \+ *def* to_linear_equiv
- \+ *def* to_nat_linear_equiv
- \+ *def* to_int_linear_equiv

Modified src/linear_algebra/basic.lean
- \- *lemma* coe_to_linear_equiv
- \- *lemma* coe_to_linear_equiv_symm
- \- *def* to_linear_equiv



## [2022-01-17 19:54:14](https://github.com/leanprover-community/mathlib/commit/1fbef63)
feat(order/filter): add two lemmas ([#11519](https://github.com/leanprover-community/mathlib/pull/11519))
Two easy lemmas (from the sphere eversion project) and some minor style changes.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* eventually_ne_at_top

Modified src/order/filter/basic.lean
- \+/\- *lemma* mem_of_superset
- \+/\- *lemma* inter_mem
- \+/\- *lemma* inter_mem_iff
- \+ *lemma* diff_mem
- \+/\- *lemma* mem_of_superset
- \+/\- *lemma* inter_mem
- \+/\- *lemma* inter_mem_iff



## [2022-01-17 19:54:13](https://github.com/leanprover-community/mathlib/commit/e096b99)
refactor(set_theory/ordinal_arithmetic): Rename `power` to `opow` ([#11279](https://github.com/leanprover-community/mathlib/pull/11279))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *lemma* opow_mul_add_pos
- \+ *lemma* opow_mul_add_lt_opow_mul_succ
- \+ *lemma* opow_mul_add_lt_opow_succ
- \- *lemma* power_mul_add_pos
- \- *lemma* power_mul_add_lt_power_mul_succ
- \- *lemma* power_mul_add_lt_power_succ
- \+ *theorem* zero_opow'
- \+ *theorem* zero_opow
- \+ *theorem* opow_zero
- \+ *theorem* opow_succ
- \+ *theorem* opow_limit
- \+ *theorem* opow_le_of_limit
- \+ *theorem* lt_opow_of_limit
- \+ *theorem* opow_one
- \+ *theorem* one_opow
- \+ *theorem* opow_pos
- \+ *theorem* opow_ne_zero
- \+ *theorem* opow_is_normal
- \+ *theorem* opow_lt_opow_iff_right
- \+ *theorem* opow_le_opow_iff_right
- \+ *theorem* opow_right_inj
- \+ *theorem* opow_is_limit
- \+ *theorem* opow_is_limit_left
- \+ *theorem* opow_le_opow_right
- \+ *theorem* opow_le_opow_left
- \+ *theorem* le_opow_self
- \+ *theorem* opow_lt_opow_left_of_succ
- \+ *theorem* opow_add
- \+ *theorem* opow_dvd_opow
- \+ *theorem* opow_dvd_opow_iff
- \+ *theorem* opow_mul
- \+ *theorem* lt_opow_succ_log
- \+ *theorem* opow_log_le
- \+ *theorem* log_opow_mul_add
- \+ *theorem* log_opow
- \+ *theorem* nat_cast_opow
- \+ *theorem* opow_lt_omega
- \+ *theorem* add_omega_opow
- \+ *theorem* add_lt_omega_opow
- \+ *theorem* mul_lt_omega_opow
- \+ *theorem* mul_omega_opow_opow
- \+ *theorem* opow_omega
- \- *theorem* zero_power'
- \- *theorem* zero_power
- \- *theorem* power_zero
- \- *theorem* power_succ
- \- *theorem* power_limit
- \- *theorem* power_le_of_limit
- \- *theorem* lt_power_of_limit
- \- *theorem* power_one
- \- *theorem* one_power
- \- *theorem* power_pos
- \- *theorem* power_ne_zero
- \- *theorem* power_is_normal
- \- *theorem* power_lt_power_iff_right
- \- *theorem* power_le_power_iff_right
- \- *theorem* power_right_inj
- \- *theorem* power_is_limit
- \- *theorem* power_is_limit_left
- \- *theorem* power_le_power_right
- \- *theorem* power_le_power_left
- \- *theorem* le_power_self
- \- *theorem* power_lt_power_left_of_succ
- \- *theorem* power_add
- \- *theorem* power_dvd_power
- \- *theorem* power_dvd_power_iff
- \- *theorem* power_mul
- \- *theorem* lt_power_succ_log
- \- *theorem* power_log_le
- \- *theorem* log_power_mul_add
- \- *theorem* log_power
- \- *theorem* nat_cast_power
- \- *theorem* power_lt_omega
- \- *theorem* add_omega_power
- \- *theorem* add_lt_omega_power
- \- *theorem* mul_lt_omega_power
- \- *theorem* mul_omega_power_power
- \- *theorem* power_omega
- \+ *def* opow
- \- *def* power

Modified src/set_theory/ordinal_notation.lean
- \+ *theorem* NF.of_dvd_omega_opow
- \+ *theorem* opow_def
- \+ *theorem* scale_opow_aux
- \+ *theorem* repr_opow_aux₁
- \+ *theorem* repr_opow_aux₂
- \+ *theorem* repr_opow
- \+ *theorem* repr_opow
- \- *theorem* NF.of_dvd_omega_power
- \- *theorem* power_def
- \- *theorem* scale_power_aux
- \- *theorem* repr_power_aux₁
- \- *theorem* repr_power_aux₂
- \- *theorem* repr_power
- \- *theorem* repr_power
- \+ *def* opow_aux
- \+ *def* opow
- \+ *def* opow
- \- *def* power_aux
- \- *def* power
- \- *def* power



## [2022-01-17 19:08:49](https://github.com/leanprover-community/mathlib/commit/2a8a01b)
chore(measure_theory/integral/bochner): use set_to_fun lemmas to prove integral properties ([#10717](https://github.com/leanprover-community/mathlib/pull/10717))
#### Estimated changes
Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* weighted_smul_smul_measure
- \+ *lemma* weighted_smul_nonneg



## [2022-01-17 15:56:24](https://github.com/leanprover-community/mathlib/commit/905871f)
feat(analysis/normed_space/spectrum): an algebra homomorphism into the base field is bounded ([#11494](https://github.com/leanprover-community/mathlib/pull/11494))
We prove basic facts about `φ : A →ₐ[𝕜] 𝕜` when `A` is a Banach algebra, namely that `φ` maps elements of `A` to their spectrum, and that `φ` is bounded.
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean
- \+ *lemma* apply_mem_spectrum

Modified src/analysis/normed_space/spectrum.lean
- \+ *lemma* continuous
- \+ *lemma* to_continuous_linear_map_norm
- \+ *def* to_continuous_linear_map

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ker_ne_top



## [2022-01-17 15:10:20](https://github.com/leanprover-community/mathlib/commit/4e31396)
feat(measure_theory/measure): define `ae_disjoint` ([#11500](https://github.com/leanprover-community/mathlib/pull/11500))
I am going to migrate most `disjoint` assumptions to `ae_disjoint`.
#### Estimated changes
Created src/measure_theory/measure/ae_disjoint.lean
- \+ *lemma* exists_null_pairwise_disjoint_diff
- \+ *lemma* _root_.disjoint.ae_disjoint
- \+ *lemma* mono_ae
- \+ *lemma* mono
- \+ *lemma* Union_left_iff
- \+ *lemma* Union_right_iff
- \+ *lemma* union_left_iff
- \+ *lemma* union_right_iff
- \+ *lemma* union_left
- \+ *lemma* union_right
- \+ *lemma* exists_disjoint_diff
- \+ *lemma* of_null_right
- \+ *lemma* of_null_left
- \+ *def* ae_disjoint

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* measure_mono_null_ae



## [2022-01-17 14:43:23](https://github.com/leanprover-community/mathlib/commit/50bdb29)
feat(analysis/complex/cauchy_integral): review docs, add versions without `off_countable` ([#11417](https://github.com/leanprover-community/mathlib/pull/11417))
#### Estimated changes
Modified src/analysis/complex/cauchy_integral.lean
- \+ *lemma* integral_boundary_rect_of_has_fderiv_at_real_off_countable
- \+ *lemma* integral_boundary_rect_of_continuous_on_of_has_fderiv_at_real
- \+ *lemma* integral_boundary_rect_of_differentiable_on_real
- \+ *lemma* integral_boundary_rect_eq_zero_of_continuous_on_of_differentiable_on
- \+ *lemma* integral_boundary_rect_eq_zero_of_differentiable_on
- \+ *lemma* circle_integral_sub_inv_smul_of_continuous_on_of_differentiable_on
- \+ *lemma* circle_integral_sub_inv_smul_of_differentiable_on
- \+ *lemma* has_fpower_series_on_ball_of_continuous_on_of_differentiable_on
- \- *lemma* integral_boundary_rect_of_has_fderiv_within_at_real_off_countable

Modified src/analysis/complex/re_im_topology.lean
- \+ *lemma* is_open.re_prod_im
- \+ *lemma* is_closed.re_prod_im



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
- \+ *lemma* two_lt_card_iff
- \+ *lemma* two_lt_card



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
- \+ *lemma* arg_neg_eq_arg_sub_pi_of_im_pos
- \+ *lemma* arg_neg_eq_arg_add_pi_of_im_neg
- \+ *lemma* arg_neg_eq_arg_sub_pi_iff
- \+ *lemma* arg_neg_eq_arg_add_pi_iff
- \+ *lemma* arg_neg_coe_angle
- \- *lemma* arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg
- \- *lemma* arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg



## [2022-01-17 10:14:49](https://github.com/leanprover-community/mathlib/commit/1c56a8d)
feat(order/well_founded_set): Antichains in a partial well order are finite ([#11286](https://github.com/leanprover-community/mathlib/pull/11286))
and when the relation is reflexive and symmetric, it's actually an equivalent condition.
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* finite.exists_lt_map_eq_of_range_subset

Modified src/order/well_founded_set.lean
- \+ *lemma* _root_.is_antichain.finite_of_partially_well_ordered_on
- \+ *lemma* finite.partially_well_ordered_on
- \+ *lemma* _root_.is_antichain.partially_well_ordered_on_iff
- \+ *lemma* partially_well_ordered_on_iff_finite_antichains
- \+ *lemma* partially_well_ordered_on
- \- *theorem* partially_well_ordered_on



## [2022-01-17 08:42:46](https://github.com/leanprover-community/mathlib/commit/0d5bfd7)
feat(*): add a few lemmas about `function.extend` ([#11498](https://github.com/leanprover-community/mathlib/pull/11498))
I'm going to use `function.extend` as another way to get from
`[encodable ι] (s : ι → set α)` to `t : ℕ → set α` in measure theory.
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *lemma* apply_extend

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
- \+ *lemma* encode_inj
- \+ *lemma* decode₂_encode
- \+ *theorem* decode₂_eq_some

Modified src/data/equiv/encodable/lattice.lean



## [2022-01-17 08:42:44](https://github.com/leanprover-community/mathlib/commit/ac76eb3)
feat(algebra/star/unitary): lemmas about group_with_zero ([#11493](https://github.com/leanprover-community/mathlib/pull/11493))
#### Estimated changes
Modified src/algebra/star/unitary.lean
- \+ *lemma* mem_iff
- \+ *lemma* to_units_injective
- \+ *lemma* mem_iff_star_mul_self
- \+ *lemma* mem_iff_self_mul_star
- \+ *lemma* coe_inv
- \+ *lemma* coe_div
- \+ *lemma* coe_zpow
- \+ *def* to_units



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
- \+/\- *lemma* mem_Union
- \+/\- *lemma* mem_Union

Modified src/analysis/box_integral/partition/split.lean

Modified src/analysis/box_integral/partition/tagged.lean
- \+/\- *lemma* mem_Union
- \+/\- *lemma* disj_union_boxes
- \+/\- *lemma* mem_Union
- \+/\- *lemma* disj_union_boxes

Modified src/analysis/convex/cone.lean
- \+/\- *lemma* mem_Inf
- \+/\- *lemma* mem_Inf

Modified src/analysis/convex/extreme.lean

Modified src/analysis/convex/simplicial_complex/basic.lean
- \+/\- *lemma* mem_space_iff
- \+/\- *lemma* mem_space_iff

Modified src/data/finset/basic.lean

Modified src/data/semiquot.lean

Modified src/data/set/accumulate.lean

Modified src/data/set/lattice.lean
- \- *lemma* mem_bUnion_iff'
- \+ *theorem* mem_Union₂
- \+ *theorem* mem_Inter₂
- \- *theorem* mem_bUnion_iff
- \- *theorem* mem_bInter_iff

Modified src/data/set/pairwise.lean

Modified src/dynamics/ergodic/conservative.lean

Modified src/group_theory/subgroup/basic.lean
- \+/\- *lemma* mem_Inf
- \+/\- *lemma* mem_Inf

Modified src/group_theory/submonoid/basic.lean
- \+/\- *lemma* mem_Inf
- \+/\- *lemma* mem_Inf

Modified src/linear_algebra/affine_space/affine_subspace.lean

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* mem_span
- \+/\- *lemma* mem_span

Modified src/measure_theory/constructions/borel_space.lean

Modified src/measure_theory/covering/besicovitch.lean

Modified src/measure_theory/covering/vitali.lean

Modified src/model_theory/basic.lean
- \+/\- *lemma* mem_Inf
- \+/\- *lemma* mem_Inf

Modified src/order/filter/basic.lean

Modified src/order/ideal.lean

Modified src/ring_theory/finiteness.lean

Modified src/ring_theory/ideal/operations.lean

Modified src/ring_theory/subring/basic.lean
- \+/\- *lemma* mem_Inf
- \+/\- *lemma* mem_Inf

Modified src/ring_theory/subsemiring/basic.lean
- \+/\- *lemma* mem_Inf
- \+/\- *lemma* mem_Inf

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
- \+ *lemma* closed_ball_disjoint_ball
- \+ *lemma* closed_ball_disjoint_closed_ball
- \- *theorem* ball_disjoint
- \- *theorem* ball_disjoint_same



## [2022-01-17 07:55:09](https://github.com/leanprover-community/mathlib/commit/2f342b8)
feat(measure_theory): generalize some lemmas to `outer_measure` ([#11501](https://github.com/leanprover-community/mathlib/pull/11501))
#### Estimated changes
Modified src/measure_theory/measure/measure_space_def.lean
- \+/\- *lemma* measure_union_null_iff
- \+/\- *lemma* measure_union_lt_top_iff
- \+ *lemma* measure_union_eq_top_iff
- \+/\- *lemma* measure_union_null_iff
- \+/\- *lemma* measure_union_lt_top_iff

Modified src/measure_theory/measure/outer_measure.lean
- \+/\- *lemma* Union_null
- \+ *lemma* Union_null_iff
- \+ *lemma* bUnion_null_iff
- \+ *lemma* sUnion_null_iff
- \+ *lemma* univ_eq_zero_iff
- \+/\- *lemma* Union_null
- \+ *theorem* mono_null



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
- \+/\- *lemma* restrict_le_self
- \+/\- *lemma* restrict_eq_self
- \+/\- *lemma* restrict_apply_self
- \+ *lemma* restrict_apply_superset
- \+ *lemma* restrict_restrict_of_subset
- \+ *lemma* restrict_restrict'
- \+/\- *lemma* restrict_comm
- \+/\- *lemma* restrict_congr_mono
- \- *lemma* restrict_eq_self'
- \+/\- *lemma* restrict_eq_self
- \+/\- *lemma* restrict_apply_self
- \+/\- *lemma* restrict_comm
- \+/\- *lemma* restrict_le_self
- \+/\- *lemma* restrict_congr_mono



## [2022-01-17 00:42:46](https://github.com/leanprover-community/mathlib/commit/6d19eba)
feat(*): add to_sub* lemmas for `map`, `fg` ([#11480](https://github.com/leanprover-community/mathlib/pull/11480))
From flt-regular.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* map_to_submodule
- \+ *lemma* map_to_subsemiring

Modified src/ring_theory/noetherian.lean
- \+ *lemma* _root_.subalgebra.fg_bot_to_submodule



## [2022-01-16 23:52:06](https://github.com/leanprover-community/mathlib/commit/4ed7316)
feat(analysis/special_functions/pow): tendsto rpow lemma for ennreals ([#11475](https://github.com/leanprover-community/mathlib/pull/11475))
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* continuous_rpow_const
- \+ *lemma* filter.tendsto.ennrpow_const
- \+/\- *lemma* continuous_rpow_const



## [2022-01-16 23:11:56](https://github.com/leanprover-community/mathlib/commit/2c2338e)
chore(data/complex/basic): add of_real_eq_one ([#11496](https://github.com/leanprover-community/mathlib/pull/11496))
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *theorem* of_real_eq_one
- \+ *theorem* of_real_ne_one



## [2022-01-16 23:11:54](https://github.com/leanprover-community/mathlib/commit/1f6bbf9)
feat(analysis/special_functions/complex/arg): `arg_conj`, `arg_inv` lemmas ([#11479](https://github.com/leanprover-community/mathlib/pull/11479))
Add lemmas giving the values of `arg (conj x)` and `arg x⁻¹`, both for
`arg` as a real number and `arg` coerced to `real.angle` (the latter
function being better behaved because it avoids case distinctions
around getting a result into the interval (-π, π]).
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* arg_conj
- \+ *lemma* arg_inv
- \+ *lemma* arg_conj_coe_angle
- \+ *lemma* arg_inv_coe_angle



## [2022-01-16 22:44:43](https://github.com/leanprover-community/mathlib/commit/f4b93c8)
feat(analysis/special_functions/trigonometric/angle): more 2π = 0 lemmas ([#11482](https://github.com/leanprover-community/mathlib/pull/11482))
Add some more lemmas useful for manipulation of `real.angle` expressions.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* sub_coe_pi_eq_add_coe_pi
- \+ *lemma* two_nsmul_coe_pi
- \+ *lemma* two_zsmul_coe_pi



## [2022-01-16 22:07:26](https://github.com/leanprover-community/mathlib/commit/ed57bdd)
feat(number_field): notation for 𝓞 K, an algebra & ∈ 𝓞 K iff ([#11476](https://github.com/leanprover-community/mathlib/pull/11476))
From flt-regular.
#### Estimated changes
Modified src/number_theory/number_field.lean
- \+ *lemma* mem_ring_of_integers
- \+/\- *lemma* is_integral_coe
- \+/\- *lemma* is_integral_coe



## [2022-01-16 21:15:07](https://github.com/leanprover-community/mathlib/commit/5f5bcd8)
feat(order/filter/ultrafilter): add some comap_inf_principal lemmas ([#11495](https://github.com/leanprover-community/mathlib/pull/11495))
...in the setting of ultrafilters
These lemmas are useful to prove e.g. that the continuous image of a
compact set is compact in the setting of convergence spaces.
#### Estimated changes
Modified src/order/filter/ultrafilter.lean
- \+ *lemma* eq_of_le
- \+ *lemma* comap_inf_principal_ne_bot_of_image_mem
- \+ *lemma* of_comap_inf_principal_mem
- \+ *lemma* of_comap_inf_principal_eq_of_map



## [2022-01-16 15:00:06](https://github.com/leanprover-community/mathlib/commit/d7f8f58)
feat(algebra/star/unitary): (re)define unitary elements of a star monoid ([#11457](https://github.com/leanprover-community/mathlib/pull/11457))
This PR defines `unitary R` for a star monoid `R` as the submonoid containing the elements that satisfy both `star U * U = 1` and `U * star U = 1`. We show basic properties (i.e. that this forms a group) and show that they
preserve the norm when `R` is a C* ring.
Note that this replaces `unitary_submonoid`, which only included the condition `star U * U = 1` -- see [the discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/unitary.20submonoid) on Zulip.
#### Estimated changes
Modified src/algebra/star/self_adjoint.lean

Created src/algebra/star/unitary.lean
- \+ *lemma* star_mul_self_of_mem
- \+ *lemma* mul_star_self_of_mem
- \+ *lemma* star_mem
- \+ *lemma* star_mem_iff
- \+ *lemma* coe_star
- \+ *lemma* coe_star_mul_self
- \+ *lemma* coe_mul_star_self
- \+ *lemma* star_mul_self
- \+ *lemma* mul_star_self
- \+ *lemma* star_eq_inv
- \+ *lemma* star_eq_inv'
- \+ *def* unitary

Modified src/analysis/normed_space/star.lean
- \+ *lemma* norm_coe_unitary
- \+ *lemma* norm_of_mem_unitary
- \+ *lemma* norm_coe_unitary_mul
- \+ *lemma* norm_unitary_smul
- \+ *lemma* norm_mem_unitary_mul
- \+ *lemma* norm_mul_coe_unitary
- \+ *lemma* norm_mul_mem_unitary

Modified src/linear_algebra/unitary_group.lean
- \+/\- *lemma* star_mul_self
- \- *lemma* star_mem
- \- *lemma* star_mem_iff
- \+/\- *lemma* star_mul_self
- \- *def* unitary_submonoid
- \- *def* unitary_group



## [2022-01-16 15:00:04](https://github.com/leanprover-community/mathlib/commit/1d1f384)
feat(analysis/calculus/dslope): define dslope ([#11432](https://github.com/leanprover-community/mathlib/pull/11432))
#### Estimated changes
Created src/analysis/calculus/dslope.lean
- \+ *lemma* dslope_same
- \+ *lemma* dslope_of_ne
- \+ *lemma* eq_on_dslope_slope
- \+ *lemma* dslope_eventually_eq_slope_of_ne
- \+ *lemma* dslope_eventually_eq_slope_punctured_nhds
- \+ *lemma* sub_smul_dslope
- \+ *lemma* dslope_sub_smul_of_ne
- \+ *lemma* eq_on_dslope_sub_smul
- \+ *lemma* dslope_sub_smul
- \+ *lemma* continuous_at_dslope_same
- \+ *lemma* continuous_within_at.of_dslope
- \+ *lemma* continuous_at.of_dslope
- \+ *lemma* continuous_on.of_dslope
- \+ *lemma* continuous_within_at_dslope_of_ne
- \+ *lemma* continuous_at_dslope_of_ne
- \+ *lemma* continuous_on_dslope
- \+ *lemma* differentiable_within_at.of_dslope
- \+ *lemma* differentiable_at.of_dslope
- \+ *lemma* differentiable_on.of_dslope
- \+ *lemma* differentiable_within_at_dslope_of_ne
- \+ *lemma* differentiable_on_dslope_of_nmem
- \+ *lemma* differentiable_at_dslope_of_ne



## [2022-01-16 13:30:27](https://github.com/leanprover-community/mathlib/commit/1aee8a8)
chore(*): Put `simp` attribute before `to_additive` ([#11488](https://github.com/leanprover-community/mathlib/pull/11488))
A few lemmas were tagged in the wrong order. As tags are applied from left to right, `@[to_additive, simp]` only marks the multiplicative lemma as `simp`. The correct order is thus `@[simp, to_additive]`.
#### Estimated changes
Modified src/algebra/group/opposite.lean
- \+/\- *lemma* commute_op
- \+/\- *lemma* commute_unop
- \+/\- *lemma* commute_op
- \+/\- *lemma* commute_unop

Modified src/algebra/order/lattice_group.lean

Modified src/group_theory/submonoid/inverses.lean
- \+/\- *lemma* from_left_inv_one
- \+/\- *lemma* from_left_inv_left_inv_equiv_symm
- \+/\- *lemma* left_inv_equiv_symm_from_left_inv
- \+/\- *lemma* left_inv_equiv_symm_mul
- \+/\- *lemma* mul_left_inv_equiv_symm
- \+/\- *lemma* from_left_inv_eq_inv
- \+/\- *lemma* left_inv_equiv_symm_eq_inv
- \+/\- *lemma* from_left_inv_one
- \+/\- *lemma* from_left_inv_left_inv_equiv_symm
- \+/\- *lemma* left_inv_equiv_symm_from_left_inv
- \+/\- *lemma* left_inv_equiv_symm_mul
- \+/\- *lemma* mul_left_inv_equiv_symm
- \+/\- *lemma* from_left_inv_eq_inv
- \+/\- *lemma* left_inv_equiv_symm_eq_inv



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
- \+/\- *lemma* norm_smul
- \+/\- *lemma* dist_smul
- \+/\- *lemma* nnnorm_smul
- \+/\- *lemma* nndist_smul
- \+/\- *lemma* norm_smul_of_nonneg
- \+/\- *lemma* norm_smul
- \+/\- *lemma* dist_smul
- \+/\- *lemma* nnnorm_smul
- \+/\- *lemma* nndist_smul
- \+/\- *lemma* norm_smul_of_nonneg
- \+/\- *theorem* closure_ball
- \+/\- *theorem* frontier_ball
- \+/\- *theorem* interior_closed_ball
- \+/\- *theorem* frontier_closed_ball
- \+/\- *theorem* closure_ball
- \+/\- *theorem* frontier_ball
- \+/\- *theorem* interior_closed_ball
- \+/\- *theorem* frontier_closed_ball
- \+/\- *def* homeomorph_unit_ball
- \+/\- *def* homeomorph_unit_ball
- \- *def* semi_normed_space.restrict_scalars

Modified src/analysis/normed_space/conformal_linear_map.lean

Modified src/analysis/normed_space/dual.lean
- \+/\- *lemma* polar_univ
- \+/\- *lemma* polar_univ

Modified src/analysis/normed_space/extend.lean
- \+/\- *lemma* norm_bound
- \+/\- *lemma* continuous_linear_map.extend_to_𝕜'_apply
- \+/\- *lemma* norm_bound
- \+/\- *lemma* continuous_linear_map.extend_to_𝕜'_apply

Modified src/analysis/normed_space/finite_dimension.lean

Modified src/analysis/normed_space/hahn_banach.lean

Modified src/analysis/normed_space/linear_isometry.lean

Modified src/analysis/normed_space/multilinear.lean

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* to_span_singleton_smul'
- \+/\- *lemma* op_norm_smul_le
- \+/\- *lemma* to_span_singleton_smul'
- \+/\- *lemma* op_norm_smul_le

Modified src/analysis/normed_space/pi_Lp.lean

Modified src/analysis/normed_space/pointwise.lean

Modified src/analysis/seminorm.lean

Modified src/geometry/manifold/algebra/smooth_functions.lean

Modified src/geometry/manifold/instances/real.lean

Modified src/geometry/manifold/instances/sphere.lean

Modified src/measure_theory/integral/set_to_l1.lean
- \+/\- *lemma* smul
- \+/\- *lemma* set_to_simple_func_smul_left
- \+/\- *lemma* set_to_simple_func_smul_left'
- \+/\- *lemma* smul
- \+/\- *lemma* set_to_simple_func_smul_left
- \+/\- *lemma* set_to_simple_func_smul_left'

Modified src/number_theory/modular.lean

Modified src/topology/metric_space/hausdorff_distance.lean



## [2022-01-16 13:03:59](https://github.com/leanprover-community/mathlib/commit/d60541c)
feat(analysis/seminorm): Add `has_add` and `has_scalar nnreal` ([#11414](https://github.com/leanprover-community/mathlib/pull/11414))
Add instances of `has_add` and `has_scalar nnreal` type classes for `seminorm`.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* coe_smul
- \+ *lemma* smul_apply
- \+ *lemma* coe_add
- \+ *lemma* add_apply
- \+ *lemma* coe_fn_add_monoid_hom_injective
- \+ *def* coe_fn_add_monoid_hom



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
- \+ *lemma* star_ring_end_apply
- \+ *lemma* star_ring_end_self_apply
- \- *lemma* star_ring_aut_apply
- \- *lemma* star_ring_aut_self_apply
- \+ *def* star_ring_end

Modified src/analysis/complex/circle.lean
- \+/\- *lemma* coe_inv_circle_eq_conj
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
- \+ *lemma* ae_cover.integrable_of_lintegral_nnnorm_bounded
- \+ *lemma* ae_cover.integrable_of_lintegral_nnnorm_bounded'
- \+ *lemma* ae_cover.integrable_of_integral_norm_bounded
- \+/\- *lemma* ae_cover.integrable_of_integral_norm_tendsto
- \+ *lemma* ae_cover.integrable_of_integral_bounded_of_nonneg_ae
- \+ *lemma* integrable_of_interval_integral_norm_bounded
- \+/\- *lemma* integrable_of_interval_integral_norm_tendsto
- \+ *lemma* integrable_on_Iic_of_interval_integral_norm_bounded
- \+/\- *lemma* integrable_on_Iic_of_interval_integral_norm_tendsto
- \+ *lemma* integrable_on_Ioi_of_interval_integral_norm_bounded
- \+/\- *lemma* integrable_on_Ioi_of_interval_integral_norm_tendsto
- \+/\- *lemma* ae_cover.integrable_of_integral_norm_tendsto
- \+/\- *lemma* integrable_of_interval_integral_norm_tendsto
- \+/\- *lemma* integrable_on_Iic_of_interval_integral_norm_tendsto
- \+/\- *lemma* integrable_on_Ioi_of_interval_integral_norm_tendsto



## [2022-01-15 20:09:30](https://github.com/leanprover-community/mathlib/commit/1f266d6)
feat(data/pnat/basic): `succ_nat_pred` ([#11455](https://github.com/leanprover-community/mathlib/pull/11455))
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *lemma* pnat.one_add_nat_pred
- \+ *lemma* pnat.nat_pred_add_one
- \+ *lemma* pnat.nat_pred_eq_pred



## [2022-01-15 18:38:48](https://github.com/leanprover-community/mathlib/commit/0b4f07f)
feat(data/set/basic): add singleton_injective ([#11464](https://github.com/leanprover-community/mathlib/pull/11464))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* singleton_injective



## [2022-01-15 17:32:48](https://github.com/leanprover-community/mathlib/commit/37cf695)
feat(measure_theory/integral/set_to_l1): monotonicity properties of set_to_fun ([#10714](https://github.com/leanprover-community/mathlib/pull/10714))
We prove that in a `normed_lattice_add_comm_group`, if `T` is such that `0 ≤ T s x` for `0 ≤ x`,  then `set_to_fun μ T` verifies
- `set_to_fun_mono_left (h : ∀ s x, T' s x ≤ T'' s x) : set_to_fun μ T' hT' f ≤ set_to_fun μ T'' hT'' f`
- `set_to_fun_nonneg (hf : 0 ≤ᵐ[μ] f) : 0 ≤ set_to_fun μ T hT f`
- `set_to_fun_mono (hfg : f ≤ᵐ[μ] g) : set_to_fun μ T hT f ≤ set_to_fun μ T hT g`
#### Estimated changes
Created src/measure_theory/function/lp_order.lean
- \+ *lemma* coe_fn_le
- \+ *lemma* coe_fn_nonneg

Modified src/measure_theory/function/simple_func_dense.lean
- \+ *lemma* coe_fn_le
- \+ *lemma* coe_fn_zero
- \+ *lemma* coe_fn_nonneg
- \+ *lemma* exists_simple_func_nonneg_ae_eq
- \+ *lemma* dense_range_coe_simple_func_nonneg_to_Lp_nonneg
- \+ *def* coe_simple_func_nonneg_to_Lp_nonneg

Modified src/measure_theory/integral/set_to_l1.lean
- \+ *lemma* set_to_simple_func_mono_left
- \+ *lemma* set_to_simple_func_mono_left'
- \+ *lemma* set_to_simple_func_nonneg
- \+ *lemma* set_to_simple_func_nonneg'
- \+/\- *lemma* set_to_simple_func_mono
- \+ *lemma* set_to_L1s_mono_left
- \+ *lemma* set_to_L1s_mono_left'
- \+ *lemma* set_to_L1s_nonneg
- \+ *lemma* set_to_L1s_mono
- \+ *lemma* set_to_L1s_clm_mono_left
- \+ *lemma* set_to_L1s_clm_mono_left'
- \+ *lemma* set_to_L1s_clm_nonneg
- \+ *lemma* set_to_L1s_clm_mono
- \+ *lemma* set_to_L1_mono_left'
- \+ *lemma* set_to_L1_mono_left
- \+ *lemma* set_to_L1_nonneg
- \+ *lemma* set_to_L1_mono
- \+ *lemma* set_to_fun_mono_left'
- \+ *lemma* set_to_fun_mono_left
- \+ *lemma* set_to_fun_nonneg
- \+ *lemma* set_to_fun_mono
- \+/\- *lemma* set_to_simple_func_mono



## [2022-01-15 15:30:16](https://github.com/leanprover-community/mathlib/commit/51c5a40)
feat(analysis/special_functions/trigonometric/angle): `neg_coe_pi` ([#11460](https://github.com/leanprover-community/mathlib/pull/11460))
Add the lemma that `-π` and `π` are the same `real.angle` (angle mod 2π).
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* neg_coe_pi



## [2022-01-15 14:19:28](https://github.com/leanprover-community/mathlib/commit/ce62dbc)
feat(algebra/star/self_adjoint): module instance on self-adjoint elements of a star algebra ([#11322](https://github.com/leanprover-community/mathlib/pull/11322))
We put a module instance on `self_adjoint A`, where `A` is a `[star_module R A]` and `R` has a trivial star operation. A new typeclass `[has_trivial_star R]` is created for this purpose with an instance on `ℝ`. This allows us to express the fact that e.g. the space of complex Hermitian matrices is a real vector space.
#### Estimated changes
Modified src/algebra/star/basic.lean

Modified src/algebra/star/self_adjoint.lean
- \+ *lemma* coe_smul

Modified src/data/real/basic.lean



## [2022-01-15 10:42:41](https://github.com/leanprover-community/mathlib/commit/0d1d4c9)
feat(data/finset/basic): strengthen `finset.nonempty.cons_induction` ([#11452](https://github.com/leanprover-community/mathlib/pull/11452))
This change makes it strong enough to be used in three other lemmas.
#### Estimated changes
Modified src/analysis/seminorm.lean

Modified src/data/finset/basic.lean
- \+/\- *lemma* nonempty.cons_induction
- \+/\- *lemma* nonempty.cons_induction

Modified src/data/finset/lattice.lean

Modified src/data/real/ennreal.lean



## [2022-01-15 09:16:04](https://github.com/leanprover-community/mathlib/commit/ff19c95)
chore(algebra/group_power/basic): collect together ring lemmas ([#11446](https://github.com/leanprover-community/mathlib/pull/11446))
This reorders the lemmas so that all the ring and comm_ring lemmas can be put in a single section.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+/\- *lemma* neg_one_pow_mul_eq_zero_iff
- \+/\- *lemma* mul_neg_one_pow_eq_zero_iff
- \+/\- *lemma* neg_sq
- \+/\- *lemma* sq_sub_sq
- \+/\- *lemma* eq_or_eq_neg_of_sq_eq_sq
- \+/\- *lemma* sub_sq
- \+/\- *lemma* of_mul_pow
- \+/\- *lemma* neg_one_pow_mul_eq_zero_iff
- \+/\- *lemma* mul_neg_one_pow_eq_zero_iff
- \+/\- *lemma* sq_sub_sq
- \+/\- *lemma* eq_or_eq_neg_of_sq_eq_sq
- \+/\- *lemma* neg_sq
- \+/\- *lemma* sub_sq
- \+/\- *lemma* of_mul_pow
- \+/\- *theorem* neg_one_pow_eq_or
- \+/\- *theorem* neg_pow
- \+/\- *theorem* neg_pow_bit0
- \+/\- *theorem* neg_pow_bit1
- \+/\- *theorem* neg_pow
- \+/\- *theorem* neg_pow_bit0
- \+/\- *theorem* neg_pow_bit1
- \+/\- *theorem* neg_one_pow_eq_or



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
- \+ *lemma* dfinsupp.sum_inner
- \+ *lemma* dfinsupp.inner_sum
- \+ *lemma* orthonormal.orthogonal_family
- \+/\- *lemma* orthogonal_family.eq_ite
- \+/\- *lemma* orthogonal_family.inner_right_dfinsupp
- \+/\- *lemma* orthogonal_family.inner_right_fintype
- \+/\- *lemma* orthogonal_family.inner_sum
- \+/\- *lemma* orthogonal_family.norm_sum
- \+/\- *lemma* orthogonal_family.orthonormal_sigma_orthonormal
- \+/\- *lemma* orthogonal_family.norm_sq_diff_sum
- \+/\- *lemma* orthogonal_family.summable_iff_norm_sq_summable
- \+/\- *lemma* orthogonal_family.independent
- \+/\- *lemma* direct_sum.submodule_is_internal.collected_basis_orthonormal
- \+/\- *lemma* orthogonal_family.eq_ite
- \+/\- *lemma* orthogonal_family.inner_right_dfinsupp
- \+/\- *lemma* orthogonal_family.inner_right_fintype
- \+/\- *lemma* orthogonal_family.inner_sum
- \+/\- *lemma* orthogonal_family.norm_sum
- \+/\- *lemma* orthogonal_family.independent
- \+/\- *lemma* orthogonal_family.orthonormal_sigma_orthonormal
- \+/\- *lemma* direct_sum.submodule_is_internal.collected_basis_orthonormal
- \+/\- *lemma* orthogonal_family.norm_sq_diff_sum
- \+/\- *lemma* orthogonal_family.summable_iff_norm_sq_summable
- \+/\- *def* orthogonal_family
- \+/\- *def* orthogonal_family

Modified src/analysis/inner_product_space/pi_L2.lean

Modified src/analysis/inner_product_space/projection.lean

Modified src/analysis/inner_product_space/spectrum.lean
- \+/\- *lemma* orthogonal_family_eigenspaces
- \+/\- *lemma* orthogonal_family_eigenspaces'
- \+/\- *lemma* orthogonal_family_eigenspaces
- \+/\- *lemma* orthogonal_family_eigenspaces'

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* map_neg

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* _root_.linear_isometry.to_span_singleton_apply
- \+ *lemma* _root_.linear_isometry.coe_to_span_singleton
- \+ *def* _root_.linear_isometry.to_span_singleton



## [2022-01-15 02:46:13](https://github.com/leanprover-community/mathlib/commit/fa41b7a)
feat(topology/algebra/uniform_group): Condition for uniform convergence ([#11391](https://github.com/leanprover-community/mathlib/pull/11391))
This PR adds a lemma regarding uniform convergence on a topological group `G`, placed right after the construction of the `uniform_space` structure on `G`.
#### Estimated changes
Modified src/topology/algebra/uniform_group.lean
- \+ *lemma* topological_group.tendsto_uniformly_iff
- \+ *lemma* topological_group.tendsto_uniformly_on_iff
- \+ *lemma* topological_group.tendsto_locally_uniformly_iff
- \+ *lemma* topological_group.tendsto_locally_uniformly_on_iff



## [2022-01-14 21:29:54](https://github.com/leanprover-community/mathlib/commit/323e388)
feat(algebraic_geometry): More lemmas about affine schemes and basic open sets ([#11449](https://github.com/leanprover-community/mathlib/pull/11449))
#### Estimated changes
Modified src/algebraic_geometry/AffineScheme.lean
- \+ *lemma* is_affine_open.from_Spec_range
- \+ *lemma* is_affine_open.from_Spec_image_top
- \+ *lemma* is_affine_open.is_compact
- \+ *lemma* is_affine_open.from_Spec_base_preimage
- \+ *lemma* Scheme.Spec_map_presheaf_map_eq_to_hom
- \+ *lemma* is_affine_open.Spec_Γ_identity_hom_app_from_Spec
- \+ *lemma* is_affine_open.from_Spec_app_eq
- \+ *lemma* is_affine_open.basic_open_is_affine
- \+ *lemma* Scheme.map_prime_spectrum_basic_open_of_affine
- \+ *lemma* is_basis_basic_open
- \+ *def* is_affine_open.from_Spec

Modified src/algebraic_geometry/Scheme.lean
- \+ *lemma* comp_val
- \+ *lemma* comp_coe_base
- \+ *lemma* comp_val_base
- \+/\- *lemma* basic_open_res
- \+/\- *lemma* basic_open_res_eq
- \+ *lemma* basic_open_subset
- \+/\- *lemma* basic_open_res
- \+/\- *lemma* basic_open_res_eq



## [2022-01-14 19:02:35](https://github.com/leanprover-community/mathlib/commit/f770d6e)
feat(topology/separation): generalize two lemmas ([#11454](https://github.com/leanprover-community/mathlib/pull/11454))
#### Estimated changes
Modified src/topology/separation.lean
- \+/\- *lemma* nhds_le_nhds_iff
- \+/\- *lemma* nhds_eq_nhds_iff
- \+/\- *lemma* nhds_eq_nhds_iff
- \+/\- *lemma* nhds_le_nhds_iff



## [2022-01-14 19:02:34](https://github.com/leanprover-community/mathlib/commit/d54375e)
feat(data/nat/totient): `totient_even` ([#11436](https://github.com/leanprover-community/mathlib/pull/11436))
#### Estimated changes
Modified src/data/nat/totient.lean
- \+ *lemma* totient_even



## [2022-01-14 17:47:21](https://github.com/leanprover-community/mathlib/commit/49079c1)
feat(data/finsupp/basic): add `finset_sum_apply` and `coe_fn_add_hom` ([#11423](https://github.com/leanprover-community/mathlib/pull/11423))
`finset_sum_apply`: Given a family of functions `f i : α → ℕ` indexed over `S : finset ι`, the sum of this family over `S` is a function `α → ℕ` whose value at `p : α` is `∑ (i : ι) in S, (f i) p`
`coe_fn_add_monoid_hom`: Coercion from a `finsupp` to a function type is an `add_monoid_hom`. Proved by Alex J. Best
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finset_sum_apply
- \+ *lemma* coe_finset_sum
- \+ *lemma* coe_sum



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
- \+/\- *lemma* ext
- \+ *lemma* coe_zero
- \+ *lemma* coe_sup
- \+ *lemma* le_def
- \+ *lemma* lt_def
- \+ *lemma* coe_bot
- \+ *lemma* bot_eq_zero
- \+ *lemma* finset_sup_apply
- \+ *lemma* ball_zero'
- \+ *lemma* ball_sup
- \+ *lemma* ball_finset_sup'
- \+ *lemma* ball_bot
- \+ *lemma* ball_finset_sup_eq_Inter
- \+ *lemma* ball_finset_sup
- \+/\- *lemma* ext



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
- \+ *lemma* one_def
- \+ *lemma* mul_def
- \+ *lemma* one_def
- \+ *lemma* mul_def
- \+ *lemma* inv_def



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
- \+/\- *lemma* eq_zero
- \+/\- *lemma* eq_zero
- \+/\- *theorem* eq
- \+/\- *theorem* eq



## [2022-01-14 13:04:30](https://github.com/leanprover-community/mathlib/commit/011a599)
feat(algebraic_geometry): Gluing morphisms from an open cover. ([#11441](https://github.com/leanprover-community/mathlib/pull/11441))
#### Estimated changes
Modified src/algebraic_geometry/gluing.lean
- \+ *lemma* glued_cover_t'_fst_fst
- \+ *lemma* glued_cover_t'_fst_snd
- \+ *lemma* glued_cover_t'_snd_fst
- \+ *lemma* glued_cover_t'_snd_snd
- \+ *lemma* glued_cover_cocycle_fst
- \+ *lemma* glued_cover_cocycle_snd
- \+ *lemma* glued_cover_cocycle
- \+ *lemma* ι_from_glued
- \+ *lemma* from_glued_injective
- \+ *lemma* from_glued_open_map
- \+ *lemma* from_glued_open_embedding
- \+ *lemma* ι_glue_morphisms
- \+ *def* open_cover
- \+ *def* glued_cover_t'
- \+ *def* glued_cover
- \+ *def* from_glued
- \+ *def* glue_morphisms



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
- \+/\- *lemma* smul_vec2
- \+/\- *lemma* smul_vec3
- \+/\- *lemma* smul_vec2
- \+/\- *lemma* smul_vec3

Modified src/linear_algebra/cross_product.lean



## [2022-01-14 10:58:47](https://github.com/leanprover-community/mathlib/commit/a861839)
feat(ring_theory/discriminant): add discr_mul_is_integral_mem_adjoin ([#11396](https://github.com/leanprover-community/mathlib/pull/11396))
We add `discr_mul_is_integral_mem_adjoin`: let `K` be the fraction field of an integrally closed domain `R` and let `L` be a finite
separable extension of `K`. Let `B : power_basis K L` be such that `is_integral R B.gen`. Then for all `z : L` that are integral over `R`, we have `(discr K B.basis) • z ∈ adjoin R ({B.gen} : set L)`.
From flt-regular.
#### Estimated changes
Modified src/field_theory/intermediate_field.lean
- \+ *lemma* coe_sum
- \+ *lemma* coe_prod
- \+ *lemma* aeval_coe
- \+ *lemma* coe_is_integral_iff

Modified src/ring_theory/discriminant.lean
- \+/\- *lemma* discr_not_zero_of_basis
- \+ *lemma* discr_is_unit_of_basis
- \+/\- *lemma* discr_eq_det_embeddings_matrix_reindex_pow_two
- \+/\- *lemma* discr_power_basis_eq_prod
- \+/\- *lemma* of_power_basis_eq_prod'
- \+/\- *lemma* of_power_basis_eq_prod''
- \+/\- *lemma* of_power_basis_eq_norm
- \+ *lemma* discr_is_integral
- \+ *lemma* discr_mul_is_integral_mem_adjoin
- \+/\- *lemma* discr_not_zero_of_basis
- \+/\- *lemma* discr_eq_det_embeddings_matrix_reindex_pow_two
- \+/\- *lemma* discr_power_basis_eq_prod
- \+/\- *lemma* of_power_basis_eq_prod'
- \+/\- *lemma* of_power_basis_eq_prod''
- \+/\- *lemma* of_power_basis_eq_norm

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* adjoin_le_integral_closure
- \+ *lemma* is_integral.det

Modified src/ring_theory/trace.lean
- \+ *lemma* trace_matrix_of_basis_mul_vec



## [2022-01-14 10:07:46](https://github.com/leanprover-community/mathlib/commit/5a6c13b)
feat(algebraic_geometry/open_immersion): Operations on open covers.  ([#11442](https://github.com/leanprover-community/mathlib/pull/11442))
#### Estimated changes
Modified src/algebraic_geometry/open_immersion.lean
- \+ *def* open_cover.finite_subcover
- \+ *def* Scheme.open_cover.pullback_cover



## [2022-01-14 10:07:44](https://github.com/leanprover-community/mathlib/commit/e286012)
feat(algebra/ne_zero): `pos_of_ne_zero_coe` ([#11437](https://github.com/leanprover-community/mathlib/pull/11437))
#### Estimated changes
Modified src/algebra/ne_zero.lean
- \+ *lemma* not_char_dvd
- \+ *lemma* pos_of_ne_zero_coe
- \- *lemma* not_dvd_char

Modified src/ring_theory/polynomial/cyclotomic/basic.lean



## [2022-01-14 10:07:43](https://github.com/leanprover-community/mathlib/commit/021baae)
feat(analysis/normed_space/linear_isometry): coercion injectivity lemmas and add_monoid_hom_class ([#11434](https://github.com/leanprover-community/mathlib/pull/11434))
This also registers `linear_isometry` and `linear_isometry_equiv` with `add_monoid_hom_class`.
I found myself wanting one of these while squeezing a simp, so may as well have all of them now.
#### Estimated changes
Modified src/analysis/complex/isometry.lean
- \- *lemma* linear_isometry_equiv.congr_fun

Modified src/analysis/normed_space/linear_isometry.lean
- \+/\- *lemma* to_linear_map_injective
- \+ *lemma* to_linear_map_inj
- \+ *lemma* coe_injective
- \+ *lemma* to_continuous_linear_map_injective
- \+ *lemma* to_continuous_linear_map_inj
- \+/\- *lemma* to_linear_equiv_injective
- \+ *lemma* to_linear_equiv_inj
- \+ *lemma* coe_injective
- \+ *lemma* to_linear_isometry_injective
- \+ *lemma* to_linear_isometry_inj
- \+ *lemma* to_isometric_injective
- \+ *lemma* to_isometric_inj
- \+ *lemma* to_homeomorph_injective
- \+ *lemma* to_homeomorph_inj
- \+ *lemma* to_continuous_linear_equiv_injective
- \+ *lemma* to_continuous_linear_equiv_inj
- \+/\- *lemma* to_linear_map_injective
- \- *lemma* coe_fn_injective
- \+/\- *lemma* to_linear_equiv_injective



## [2022-01-14 10:07:42](https://github.com/leanprover-community/mathlib/commit/61054f7)
feat(topology): some improvements ([#11424](https://github.com/leanprover-community/mathlib/pull/11424))
* Prove a better version of `continuous_on.comp_fract`. Rename `continuous_on.comp_fract` -> `continuous_on.comp_fract''`.
* Rename `finset.closure_Union` -> `finset.closure_bUnion`
* Add `continuous.congr` and `continuous.subtype_coe`
#### Estimated changes
Modified src/topology/algebra/floor_ring.lean
- \+/\- *lemma* continuous_on.comp_fract'
- \+/\- *lemma* continuous_on.comp_fract
- \+ *lemma* continuous_on.comp_fract''
- \+/\- *lemma* continuous_on.comp_fract'
- \+/\- *lemma* continuous_on.comp_fract

Modified src/topology/basic.lean
- \+ *lemma* finset.closure_bUnion
- \+ *lemma* continuous.congr
- \- *lemma* finset.closure_Union

Modified src/topology/constructions.lean
- \+ *lemma* continuous.subtype_coe



## [2022-01-14 08:37:20](https://github.com/leanprover-community/mathlib/commit/3c1740a)
feat(combinatorics/configuration): Define the order of a projective plane ([#11430](https://github.com/leanprover-community/mathlib/pull/11430))
This PR defines the order of a projective plane, and proves a couple lemmas.
#### Estimated changes
Modified src/combinatorics/configuration.lean
- \+ *lemma* dual.order
- \+ *lemma* line_count_eq
- \+ *lemma* point_count_eq



## [2022-01-14 08:37:18](https://github.com/leanprover-community/mathlib/commit/5a3abca)
feat(topology/subset_properties): some compactness properties ([#11425](https://github.com/leanprover-community/mathlib/pull/11425))
* Add some lemmas about the existence of compact sets
* Add `is_compact.eventually_forall_of_forall_eventually`
* Some cleanup in `topology/subset_properties` and `topology/separation`
#### Estimated changes
Modified src/topology/separation.lean
- \+ *lemma* exists_open_superset_and_is_compact_closure
- \+ *lemma* exists_compact_between
- \+ *lemma* exists_open_between_and_is_compact_closure

Modified src/topology/subset_properties.lean
- \+/\- *lemma* is_compact.elim_finite_subcover_image
- \+ *lemma* is_compact.eventually_forall_of_forall_eventually
- \+/\- *lemma* set.finite.compact_bUnion
- \+/\- *lemma* finset.compact_bUnion
- \+/\- *lemma* compact_Union
- \+/\- *lemma* compact_space.elim_nhds_subcover
- \+/\- *lemma* is_clopen_bUnion
- \+/\- *lemma* is_clopen_bInter
- \+/\- *lemma* continuous_on.preimage_clopen_of_clopen
- \+/\- *lemma* is_preirreducible.preimage
- \+/\- *lemma* is_compact.elim_finite_subcover_image
- \+/\- *lemma* set.finite.compact_bUnion
- \+/\- *lemma* finset.compact_bUnion
- \+/\- *lemma* compact_Union
- \+/\- *lemma* compact_space.elim_nhds_subcover
- \+/\- *lemma* is_clopen_bUnion
- \+/\- *lemma* is_clopen_bInter
- \+/\- *lemma* continuous_on.preimage_clopen_of_clopen
- \+/\- *lemma* is_preirreducible.preimage
- \+/\- *theorem* compact_space_of_finite_subfamily_closed
- \+/\- *theorem* is_preirreducible.image
- \+/\- *theorem* is_irreducible.image
- \+/\- *theorem* compact_space_of_finite_subfamily_closed
- \+/\- *theorem* is_preirreducible.image
- \+/\- *theorem* is_irreducible.image
- \+/\- *def* is_compact
- \+/\- *def* is_compact



## [2022-01-14 08:37:17](https://github.com/leanprover-community/mathlib/commit/feaf6f5)
feat(algebraic_geometry): lemmas about basic opens in schemes ([#11393](https://github.com/leanprover-community/mathlib/pull/11393))
#### Estimated changes
Modified src/algebraic_geometry/Gamma_Spec_adjunction.lean
- \+ *lemma* adjunction_unit_app_app_top

Modified src/algebraic_geometry/Scheme.lean
- \+ *lemma* comp_val_c_app
- \+ *lemma* congr_app
- \+ *lemma* mem_basic_open
- \+ *lemma* mem_basic_open_top
- \+ *lemma* basic_open_res
- \+ *lemma* basic_open_res_eq
- \+ *lemma* preimage_basic_open
- \+ *lemma* preimage_basic_open'
- \+ *lemma* basic_open_zero
- \+ *lemma* basic_open_mul
- \+ *lemma* basic_open_of_is_unit
- \+ *lemma* basic_open_eq_of_affine
- \+ *lemma* basic_open_eq_of_affine'
- \+ *def* basic_open

Modified src/algebraic_geometry/Spec.lean
- \+/\- *def* Spec_Γ_identity
- \+/\- *def* Spec_Γ_identity

Modified src/algebraic_geometry/locally_ringed_space.lean

Modified src/algebraic_geometry/properties.lean
- \- *lemma* basic_open_eq_of_affine
- \- *lemma* basic_open_eq_of_affine'

Modified src/algebraic_geometry/ringed_space.lean
- \+/\- *lemma* basic_open_res
- \+ *lemma* basic_open_res_eq
- \+ *lemma* basic_open_mul
- \+ *lemma* basic_open_of_is_unit
- \+/\- *lemma* basic_open_res

Modified src/algebraic_geometry/sheafed_space.lean

Modified src/topology/category/Top/opens.lean
- \+ *lemma* open_embedding_obj_top
- \+ *lemma* inclusion_map_eq_top



## [2022-01-14 08:37:16](https://github.com/leanprover-community/mathlib/commit/85accb8)
feat(data/{multiset,finset}/sum): Disjoint sum of multisets/finsets ([#11355](https://github.com/leanprover-community/mathlib/pull/11355))
This defines the disjoint union of two multisets/finsets as `multiset (α ⊕ β)`/`finset (α ⊕ β)`.
#### Estimated changes
Created src/data/finset/sum.lean
- \+ *lemma* val_disj_sum
- \+ *lemma* empty_disj_sum
- \+ *lemma* disj_sum_empty
- \+ *lemma* card_disj_sum
- \+ *lemma* mem_disj_sum
- \+ *lemma* inl_mem_disj_sum
- \+ *lemma* inr_mem_disj_sum
- \+ *lemma* disj_sum_mono
- \+ *lemma* disj_sum_mono_left
- \+ *lemma* disj_sum_mono_right
- \+ *lemma* disj_sum_ssubset_disj_sum_of_ssubset_of_subset
- \+ *lemma* disj_sum_ssubset_disj_sum_of_subset_of_ssubset
- \+ *lemma* disj_sum_strict_mono_left
- \+ *lemma* disj_sum_strict_mono_right
- \+ *def* disj_sum

Modified src/data/multiset/basic.lean
- \+ *lemma* map_lt_map
- \+ *lemma* map_mono
- \+ *lemma* map_strict_mono

Created src/data/multiset/sum.lean
- \+ *lemma* zero_disj_sum
- \+ *lemma* disj_sum_zero
- \+ *lemma* card_disj_sum
- \+ *lemma* mem_disj_sum
- \+ *lemma* inl_mem_disj_sum
- \+ *lemma* inr_mem_disj_sum
- \+ *lemma* disj_sum_mono
- \+ *lemma* disj_sum_mono_left
- \+ *lemma* disj_sum_mono_right
- \+ *lemma* disj_sum_lt_disj_sum_of_lt_of_le
- \+ *lemma* disj_sum_lt_disj_sum_of_le_of_lt
- \+ *lemma* disj_sum_strict_mono_left
- \+ *lemma* disj_sum_strict_mono_right
- \+ *def* disj_sum

Modified src/logic/basic.lean
- \+ *lemma* or_iff_left
- \+ *lemma* or_iff_right



## [2022-01-14 08:37:15](https://github.com/leanprover-community/mathlib/commit/9a94993)
feat(analysis/inner_product_space/l2): Inner product space structure on `l2` ([#11315](https://github.com/leanprover-community/mathlib/pull/11315))
#### Estimated changes
Created src/analysis/inner_product_space/l2_space.lean
- \+ *lemma* summable_inner
- \+ *lemma* inner_eq_tsum
- \+ *lemma* has_sum_inner

Modified src/analysis/normed_space/lp_space.lean



## [2022-01-14 08:37:14](https://github.com/leanprover-community/mathlib/commit/fb2b1a0)
fix(algebra/star/basic): redefine `star_ordered_ring` ([#11213](https://github.com/leanprover-community/mathlib/pull/11213))
This PR redefines `star_ordered_ring` to remove the `ordered_semiring` assumption, which includes undesirable axioms such as `∀ (a b c : α), a < b → 0 < c → c * a < c * b`. See the discussion on Zulip [here](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Star.20ordered.20ring).
#### Estimated changes
Modified src/algebra/star/basic.lean
- \+/\- *lemma* star_mul_self_nonneg
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
Created src/algebraic_geometry/gluing.lean
- \+ *lemma* ι_iso_LocallyRingedSpace_inv
- \+ *lemma* ι_jointly_surjective
- \+ *lemma* glue_condition
- \+ *lemma* ι_iso_carrier_inv
- \+ *lemma* ι_eq_iff
- \+ *lemma* is_open_iff
- \+ *def* glued_Scheme
- \+ *def* V_pullback_cone
- \+ *def* V_pullback_cone_is_limit
- \+ *def* iso_carrier
- \+ *def* rel

Modified src/algebraic_geometry/presheafed_space.lean
- \+ *lemma* coe_to_fun_eq

Modified src/algebraic_geometry/presheafed_space/gluing.lean
- \+ *lemma* ι_jointly_surjective
- \+ *lemma* ι_iso_PresheafedSpace_inv
- \+ *lemma* ι_jointly_surjective
- \+ *lemma* ι_iso_SheafedSpace_inv
- \+ *lemma* ι_jointly_surjective
- \- *lemma* coe_to_fun_eq
- \+ *def* V_pullback_cone_is_limit
- \+ *def* V_pullback_cone_is_limit
- \+ *def* V_pullback_cone_is_limit



## [2022-01-13 23:16:00](https://github.com/leanprover-community/mathlib/commit/48fd9f2)
chore(data/list/big_operators): rename vars, reorder lemmas ([#11433](https://github.com/leanprover-community/mathlib/pull/11433))
* use better variable names;
* move lemmas to proper sections;
* relax `[comm_semiring R]` to `[semiring R]` in `dvd_sum`.
#### Estimated changes
Modified src/data/list/big_operators.lean
- \+/\- *lemma* prod_nil
- \+/\- *lemma* prod_join
- \+/\- *lemma* prod_hom_rel
- \+/\- *lemma* prod_hom
- \+/\- *lemma* prod_hom₂
- \+/\- *lemma* prod_map_hom
- \+/\- *lemma* prod_is_unit
- \+/\- *lemma* length_pos_of_prod_ne_one
- \+/\- *lemma* prod_update_nth
- \+/\- *lemma* nth_zero_mul_tail_prod
- \+/\- *lemma* head_mul_tail_prod_of_ne_nil
- \+/\- *lemma* prod_eq_zero
- \+/\- *lemma* prod_eq_zero_iff
- \+/\- *lemma* prod_ne_zero
- \+/\- *lemma* prod_inv_reverse
- \+/\- *lemma* prod_reverse_noncomm
- \+/\- *lemma* prod_inv
- \+/\- *lemma* prod_update_nth'
- \+/\- *lemma* eq_of_sum_take_eq
- \+/\- *lemma* monotone_sum_take
- \+/\- *lemma* one_le_prod_of_one_le
- \+/\- *lemma* one_lt_prod_of_one_lt
- \+/\- *lemma* single_le_prod
- \+/\- *lemma* all_one_of_le_one_le_of_prod_eq_one
- \+/\- *lemma* prod_eq_one_iff
- \+/\- *lemma* length_pos_of_sum_pos
- \+/\- *lemma* sum_le_foldr_max
- \+/\- *lemma* prod_erase
- \+/\- *lemma* dvd_prod
- \+/\- *lemma* dvd_sum
- \+/\- *lemma* exists_lt_of_sum_lt
- \+/\- *lemma* exists_le_of_sum_le
- \+/\- *lemma* prod_pos
- \+/\- *lemma* sum_map_mul_left
- \+/\- *lemma* sum_map_mul_right
- \+ *lemma* op_list_prod
- \+/\- *lemma* _root_.mul_opposite.unop_list_prod
- \+ *lemma* map_list_prod
- \+ *lemma* unop_map_list_prod
- \+/\- *lemma* prod_nil
- \+/\- *lemma* prod_join
- \+/\- *lemma* prod_eq_zero
- \+/\- *lemma* prod_eq_zero_iff
- \+/\- *lemma* prod_ne_zero
- \+/\- *lemma* prod_hom_rel
- \+/\- *lemma* prod_hom
- \+/\- *lemma* prod_hom₂
- \+/\- *lemma* prod_is_unit
- \+/\- *lemma* length_pos_of_prod_ne_one
- \+/\- *lemma* prod_update_nth
- \- *lemma* _root_.mul_opposite.op_list_prod
- \+/\- *lemma* _root_.mul_opposite.unop_list_prod
- \+/\- *lemma* prod_inv_reverse
- \+/\- *lemma* prod_reverse_noncomm
- \+/\- *lemma* prod_inv
- \+/\- *lemma* prod_update_nth'
- \+/\- *lemma* eq_of_sum_take_eq
- \+/\- *lemma* monotone_sum_take
- \+/\- *lemma* one_le_prod_of_one_le
- \+/\- *lemma* one_lt_prod_of_one_lt
- \+/\- *lemma* single_le_prod
- \+/\- *lemma* all_one_of_le_one_le_of_prod_eq_one
- \+/\- *lemma* prod_eq_one_iff
- \+/\- *lemma* length_pos_of_sum_pos
- \+/\- *lemma* sum_le_foldr_max
- \+/\- *lemma* prod_erase
- \+/\- *lemma* dvd_prod
- \+/\- *lemma* dvd_sum
- \+/\- *lemma* exists_lt_of_sum_lt
- \+/\- *lemma* exists_le_of_sum_le
- \+/\- *lemma* nth_zero_mul_tail_prod
- \+/\- *lemma* head_mul_tail_prod_of_ne_nil
- \+/\- *lemma* prod_pos
- \- *lemma* _root_.monoid_hom.map_list_prod
- \- *lemma* _root_.monoid_hom.unop_map_list_prod
- \+/\- *lemma* prod_map_hom
- \+/\- *lemma* sum_map_mul_left
- \+/\- *lemma* sum_map_mul_right



## [2022-01-13 21:10:22](https://github.com/leanprover-community/mathlib/commit/e830348)
feat(set_theory/ordinal_arithmetic): Families of ordinals ([#11278](https://github.com/leanprover-community/mathlib/pull/11278))
This PR introduces some API to convert from `ι → β` indexed families to `Π o < b, β` indexed families. This simplifies and contextualizes some existing results.
#### Estimated changes
Modified src/set_theory/cofinality.lean

Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* bfamily_of_family'_typein
- \+ *theorem* bfamily_of_family_typein
- \+ *theorem* family_of_bfamily'_enum
- \+ *theorem* family_of_bfamily_enum
- \+ *theorem* bsup_eq_sup'
- \+ *theorem* sup_eq_sup
- \+/\- *theorem* bsup_eq_sup
- \+ *theorem* sup_eq_bsup'
- \+ *theorem* bsup_eq_bsup
- \+/\- *theorem* sup_eq_bsup
- \+ *theorem* blsub_eq_lsub'
- \+ *theorem* lsub_eq_lsub
- \+/\- *theorem* blsub_eq_lsub
- \+ *theorem* lsub_eq_blsub'
- \+ *theorem* blsub_eq_blsub
- \+/\- *theorem* lsub_eq_blsub
- \- *theorem* bsup_type
- \+/\- *theorem* sup_eq_bsup
- \+/\- *theorem* bsup_eq_sup
- \+/\- *theorem* lsub_eq_blsub
- \+/\- *theorem* blsub_eq_lsub
- \+ *def* bfamily_of_family'
- \+ *def* bfamily_of_family
- \+ *def* family_of_bfamily'
- \+ *def* family_of_bfamily



## [2022-01-13 20:16:58](https://github.com/leanprover-community/mathlib/commit/6fa2e46)
feat(algebra/lie/nilpotent): central extensions of nilpotent Lie modules / algebras are nilpotent ([#11422](https://github.com/leanprover-community/mathlib/pull/11422))
The main result is `lie_algebra.nilpotent_of_nilpotent_quotient`.
#### Estimated changes
Modified src/algebra/lie/abelian.lean
- \+ *lemma* ideal_oper_max_triv_submodule_eq_bot

Modified src/algebra/lie/basic.lean
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *def* id

Modified src/algebra/lie/ideal_operations.lean
- \+ *lemma* map_bracket_eq

Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* map_lower_central_series_le
- \+ *lemma* nilpotent_of_nilpotent_quotient
- \+ *lemma* coe_lower_central_series_ideal_quot_eq
- \+ *lemma* lie_algebra.nilpotent_of_nilpotent_quotient
- \+ *lemma* lie_ideal.map_lower_central_series_le
- \- *lemma* lie_ideal.lower_central_series_map_le

Modified src/algebra/lie/quotient.lean
- \+ *lemma* mk_eq_zero
- \+ *lemma* mk'_ker
- \+ *lemma* map_mk'_eq_bot_le

Modified src/algebra/lie/submodule.lean
- \+/\- *lemma* coe_to_lie_submodule
- \+/\- *lemma* mem_to_lie_submodule
- \+/\- *lemma* exists_lie_ideal_coe_eq_iff
- \+/\- *lemma* exists_nested_lie_ideal_coe_eq_iff
- \+ *lemma* coe_submodule_map
- \+ *lemma* mem_ker
- \+ *lemma* ker_id
- \+ *lemma* comp_ker_incl
- \+ *lemma* le_ker_iff_map
- \+/\- *lemma* coe_to_lie_submodule
- \+/\- *lemma* mem_to_lie_submodule
- \+/\- *lemma* exists_lie_ideal_coe_eq_iff
- \+/\- *lemma* exists_nested_lie_ideal_coe_eq_iff
- \+/\- *def* to_lie_submodule
- \+ *def* ker
- \+/\- *def* to_lie_submodule



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
- \+ *theorem* inner_le_Lp_mul_Lq_tsum
- \+ *theorem* summable_mul_of_Lp_Lq
- \+ *theorem* inner_le_Lp_mul_Lq_tsum'
- \+ *theorem* inner_le_Lp_mul_Lq_has_sum
- \+ *theorem* summable_Lp_add
- \+ *theorem* Lp_add_le_tsum'
- \+ *theorem* inner_le_Lp_mul_Lq_tsum_of_nonneg
- \+ *theorem* summable_mul_of_Lp_Lq_of_nonneg
- \+ *theorem* inner_le_Lp_mul_Lq_tsum_of_nonneg'
- \+ *theorem* inner_le_Lp_mul_Lq_has_sum_of_nonneg
- \+ *theorem* summable_Lp_add_of_nonneg
- \+ *theorem* Lp_add_le_tsum_of_nonneg'

Modified src/analysis/normed_space/lp_space.lean



## [2022-01-13 17:57:13](https://github.com/leanprover-community/mathlib/commit/0504425)
feat(analysis/inner_product_space/basic): criterion for summability ([#11224](https://github.com/leanprover-community/mathlib/pull/11224))
In a complete inner product space `E`, a family `f` of mutually-orthogonal elements of `E` is summable, if and only if
`(λ i, ∥f i∥ ^ 2)` is summable.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_sdiff_div_prod_sdiff

Modified src/algebra/big_operators/order.lean
- \+ *lemma* one_le_prod'
- \+ *lemma* one_le_prod''
- \+ *lemma* abs_sum_of_nonneg
- \+ *lemma* abs_sum_of_nonneg'

Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* orthogonal_family.inner_sum
- \+ *lemma* orthogonal_family.norm_sum
- \+ *lemma* orthogonal_family.norm_sq_diff_sum
- \+ *lemma* orthogonal_family.summable_iff_norm_sq_summable



## [2022-01-13 17:19:26](https://github.com/leanprover-community/mathlib/commit/6446ba8)
feat(ring_theory/{trace,norm}): add trace_gen_eq_next_coeff_minpoly and norm_gen_eq_coeff_zero_minpoly  ([#11420](https://github.com/leanprover-community/mathlib/pull/11420))
We add `trace_gen_eq_next_coeff_minpoly` and `norm_gen_eq_coeff_zero_minpoly`.
From flt-regular.
#### Estimated changes
Modified src/field_theory/splitting_field.lean
- \+ *lemma* prod_roots_eq_coeff_zero_of_monic_of_split
- \+ *lemma* sum_roots_eq_next_coeff_of_monic_of_split

Modified src/ring_theory/norm.lean
- \+ *lemma* power_basis.norm_gen_eq_coeff_zero_minpoly
- \+ *lemma* power_basis.norm_gen_eq_prod_roots
- \- *lemma* norm_gen_eq_prod_roots

Modified src/ring_theory/trace.lean
- \+ *lemma* power_basis.trace_gen_eq_next_coeff_minpoly
- \+/\- *lemma* power_basis.trace_gen_eq_sum_roots
- \+/\- *lemma* power_basis.trace_gen_eq_sum_roots



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
Created src/measure_theory/function/uniform_integrable.lean
- \+ *lemma* mem_not_convergent_seq_iff
- \+ *lemma* not_convergent_seq_antitone
- \+ *lemma* measure_inter_not_convergent_seq_eq_zero
- \+ *lemma* not_convergent_seq_measurable_set
- \+ *lemma* measure_not_convergent_seq_tendsto_zero
- \+ *lemma* exists_not_convergent_seq_lt
- \+ *lemma* not_convergent_seq_lt_index_spec
- \+ *lemma* Union_not_convergent_seq_measurable_set
- \+ *lemma* measure_Union_not_convergent_seq
- \+ *lemma* Union_not_convergent_seq_subset
- \+ *lemma* tendsto_uniformly_on_diff_Union_not_convergent_seq
- \+ *lemma* tendsto_uniformly_on_of_ae_tendsto'
- \+ *theorem* tendsto_uniformly_on_of_ae_tendsto
- \+ *def* not_convergent_seq
- \+ *def* not_convergent_seq_lt_index
- \+ *def* Union_not_convergent_seq



## [2022-01-13 15:18:51](https://github.com/leanprover-community/mathlib/commit/a16a5b5)
chore(order/lattice_intervals): review ([#11416](https://github.com/leanprover-community/mathlib/pull/11416))
* use `@[reducible] protected def`;
* add `is_least.order_bot` and `is_greatest.order_top`, use them;
* weaken TC assumptions on `set.Ici.bounded_order` and `set.Iic.bounded_order`.
#### Estimated changes
Modified src/order/bounds.lean
- \+ *def* is_least.order_bot
- \+ *def* is_greatest.order_top

Modified src/order/conditionally_complete_lattice.lean
- \+ *theorem* cSup_pair
- \+ *theorem* cInf_pair

Modified src/order/lattice_intervals.lean
- \- *def* order_bot
- \- *def* order_top
- \- *def* order_bot
- \- *def* order_top
- \- *def* bounded_order



## [2022-01-13 12:25:21](https://github.com/leanprover-community/mathlib/commit/cd4f5c4)
feat(linear_algebra/{cross_product,vectors}): cross product ([#11181](https://github.com/leanprover-community/mathlib/pull/11181))
Defines the cross product for R^3 and gives localized notation for that and the dot product.
Was https://github.com/leanprover-community/mathlib/pull/10959
#### Estimated changes
Modified docs/undergrad.yaml

Modified src/data/matrix/notation.lean
- \+ *lemma* vec2_eq
- \+ *lemma* vec3_eq
- \+ *lemma* vec2_add
- \+ *lemma* vec3_add
- \+ *lemma* smul_vec2
- \+ *lemma* smul_vec3
- \+ *lemma* vec2_dot_product'
- \+ *lemma* vec2_dot_product
- \+ *lemma* vec3_dot_product'
- \+ *lemma* vec3_dot_product

Created src/linear_algebra/cross_product.lean
- \+ *lemma* cross_apply
- \+ *lemma* cross_anticomm
- \+ *lemma* cross_anticomm'
- \+ *lemma* cross_self
- \+ *lemma* dot_self_cross
- \+ *lemma* dot_cross_self
- \+ *lemma* triple_product_permutation
- \+ *lemma* leibniz_cross
- \+ *lemma* cross_cross
- \+ *theorem* triple_product_eq_det
- \+ *theorem* cross_dot_cross
- \+ *theorem* jacobi_cross
- \+ *def* cross_product
- \+ *def* cross.lie_ring



## [2022-01-13 12:25:20](https://github.com/leanprover-community/mathlib/commit/799cdbb)
feat(data/nat/periodic): periodic functions for nat ([#10888](https://github.com/leanprover-community/mathlib/pull/10888))
Adds a lemma saying that the cardinality of an Ico of length `a` filtered over a periodic predicate of period `a` is the same as the cardinality of `range a` filtered over that predicate.
#### Estimated changes
Modified src/data/int/interval.lean
- \+ *lemma* image_Ico_mod

Modified src/data/nat/interval.lean
- \+ *lemma* mod_inj_on_Ico
- \+ *lemma* image_Ico_mod
- \+ *lemma* multiset_Ico_map_mod

Created src/data/nat/periodic.lean
- \+ *lemma* periodic_gcd
- \+ *lemma* periodic_coprime
- \+ *lemma* periodic_mod
- \+ *lemma* _root_.function.periodic.map_mod_nat
- \+ *lemma* filter_multiset_Ico_card_eq_of_periodic
- \+ *lemma* filter_Ico_card_eq_of_periodic



## [2022-01-13 12:25:18](https://github.com/leanprover-community/mathlib/commit/6609204)
feat(algebraic_geometry): Gluing presheafed spaces ([#10269](https://github.com/leanprover-community/mathlib/pull/10269))
#### Estimated changes
Created src/algebraic_geometry/presheafed_space/gluing.lean
- \+ *lemma* coe_to_fun_eq
- \+ *lemma* ι_open_embedding
- \+ *lemma* pullback_base
- \+ *lemma* f_inv_app_f_app
- \+ *lemma* itself
- \+ *lemma* snd_inv_app_t_app'
- \+ *lemma* snd_inv_app_t_app
- \+ *lemma* ι_image_preimage_eq
- \+ *lemma* opens_image_preimage_map_app'
- \+ *lemma* opens_image_preimage_map_app
- \+ *lemma* opens_image_preimage_map_app_assoc
- \+ *lemma* ι_inv_app_π
- \+ *lemma* π_ι_inv_app_π
- \+ *lemma* π_ι_inv_app_eq_id
- \+ *def* opens_image_preimage_map
- \+ *def* ι_inv_app_π_app
- \+ *def* ι_inv_app

Modified src/topology/category/Top/limits.lean
- \+ *lemma* pullback_snd_image_fst_preimage
- \+ *lemma* pullback_fst_image_snd_preimage



## [2022-01-13 07:08:20](https://github.com/leanprover-community/mathlib/commit/e6db245)
chore(ring_theory/roots_of_unity): change argument order ([#11415](https://github.com/leanprover-community/mathlib/pull/11415))
this is for easier dot notation in situations such as `refine`.
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+/\- *lemma* map_of_injective
- \+/\- *lemma* of_map_of_injective
- \+/\- *lemma* map_of_injective
- \+/\- *lemma* of_map_of_injective



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
- \+ *lemma* empty_ssubset

Modified src/data/set/intervals/basic.lean
- \+ *lemma* _root_.is_top.Iic_eq
- \+ *lemma* _root_.is_bot.Ici_eq
- \+ *lemma* _root_.is_top.Ioi_eq
- \+ *lemma* _root_.is_bot.Iio_eq
- \+ *lemma* _root_.is_top.Ici_eq
- \+ *lemma* _root_.is_bot.Iic_eq
- \+/\- *lemma* Iic_inter_Ioc_of_le
- \+/\- *lemma* Ici_top
- \+ *lemma* Ioi_top
- \+/\- *lemma* Iic_top
- \+/\- *lemma* Iic_bot
- \+ *lemma* Iio_bot
- \+/\- *lemma* Ici_bot
- \- *lemma* Ici_singleton_of_top
- \- *lemma* Iic_singleton_of_bot
- \+/\- *lemma* Iic_inter_Ioc_of_le
- \+/\- *lemma* Ici_top
- \+/\- *lemma* Iic_top
- \+/\- *lemma* Iic_bot
- \+/\- *lemma* Ici_bot

Modified src/order/basic.lean
- \+ *lemma* is_top_or_exists_gt
- \+ *lemma* is_bot_or_exists_lt

Modified src/order/bounded_order.lean
- \+ *lemma* is_bot_bot
- \+ *theorem* is_top_top

Modified src/order/order_dual.lean
- \+ *lemma* is_top.to_dual
- \+ *lemma* is_bot.to_dual



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
- \+ *lemma* card_points_eq_card_lines
- \+ *lemma* line_count_eq_line_count
- \+ *lemma* point_count_eq_point_count
- \+ *lemma* line_count_eq_point_count



## [2022-01-13 06:20:13](https://github.com/leanprover-community/mathlib/commit/12b6b99)
refactor(linear_algebra/affine_space): move def of `slope` to a new file ([#11361](https://github.com/leanprover-community/mathlib/pull/11361))
Also add a few trivial lemmas.
#### Estimated changes
Modified src/linear_algebra/affine_space/ordered.lean
- \- *lemma* slope_def_field
- \- *lemma* slope_same
- \- *lemma* eq_of_slope_eq_zero
- \- *lemma* slope_comm
- \- *lemma* sub_div_sub_smul_slope_add_sub_div_sub_smul_slope
- \- *lemma* line_map_slope_slope_sub_div_sub
- \- *lemma* line_map_slope_line_map_slope_line_map
- \- *def* slope

Created src/linear_algebra/affine_space/slope.lean
- \+ *lemma* slope_def_field
- \+ *lemma* slope_same
- \+ *lemma* slope_def_module
- \+ *lemma* sub_smul_slope
- \+ *lemma* sub_smul_slope_vadd
- \+ *lemma* slope_vadd_const
- \+ *lemma* slope_sub_smul
- \+ *lemma* eq_of_slope_eq_zero
- \+ *lemma* slope_comm
- \+ *lemma* sub_div_sub_smul_slope_add_sub_div_sub_smul_slope
- \+ *lemma* line_map_slope_slope_sub_div_sub
- \+ *lemma* line_map_slope_line_map_slope_line_map
- \+ *def* slope



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
- \+ *lemma* linear_map.vec_empty_apply
- \+ *lemma* linear_map.vec_cons_apply
- \+ *def* linear_map.vec_empty
- \+ *def* linear_map.vec_cons
- \+ *def* linear_map.vec_empty₂
- \+ *def* linear_map.vec_cons₂



## [2022-01-12 22:49:45](https://github.com/leanprover-community/mathlib/commit/e6fab1d)
refactor(order/directed): Make `is_directed` a Prop mixin ([#11238](https://github.com/leanprover-community/mathlib/pull/11238))
This turns `directed_order` into a Prop-valued mixin `is_directed`. The design follows the unbundled relation classes found in core Lean.
The current design created obscure problems when showing that a `semilattice_sup` is directed and we couldn't even state that `semilattice_inf` is codirected. Further, it was kind of already used as a mixin, because there was no point inserting it in the hierarchy.
#### Estimated changes
Modified src/algebra/category/Module/limits.lean
- \+/\- *def* direct_limit_is_colimit
- \+/\- *def* direct_limit_is_colimit

Modified src/algebra/direct_limit.lean
- \+/\- *lemma* of.zero_exact_aux
- \+/\- *lemma* lift_unique
- \+/\- *lemma* of.zero_exact_aux
- \+/\- *lemma* of.zero_exact
- \+/\- *lemma* of.zero_exact_aux
- \+/\- *lemma* lift_unique
- \+/\- *lemma* of.zero_exact_aux
- \+/\- *lemma* of.zero_exact
- \+/\- *theorem* exists_of
- \+/\- *theorem* lift_unique
- \+/\- *theorem* of.zero_exact
- \+/\- *theorem* of.zero_exact
- \+/\- *theorem* exists_of
- \+/\- *theorem* polynomial.exists_of
- \+/\- *theorem* induction_on
- \+/\- *theorem* of_injective
- \+/\- *theorem* lift_unique
- \+/\- *theorem* exists_of
- \+/\- *theorem* lift_unique
- \+/\- *theorem* of.zero_exact
- \+/\- *theorem* of.zero_exact
- \+/\- *theorem* exists_of
- \+/\- *theorem* polynomial.exists_of
- \+/\- *theorem* induction_on
- \+/\- *theorem* of_injective
- \+/\- *theorem* lift_unique

Modified src/analysis/convex/caratheodory.lean

Modified src/analysis/convex/quasiconvex.lean
- \+/\- *lemma* quasiconvex_on.convex
- \+/\- *lemma* quasiconcave_on.convex
- \+/\- *lemma* quasiconvex_on.convex
- \+/\- *lemma* quasiconcave_on.convex

Modified src/category_theory/filtered.lean

Modified src/combinatorics/hall/basic.lean
- \- *def* hall_finset_directed_order

Modified src/data/finset/order.lean
- \+ *lemma* finset.exists_le
- \- *theorem* finset.exists_le

Modified src/data/real/nnreal.lean

Modified src/group_theory/congruence.lean

Modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* exists_forall_le
- \+/\- *lemma* exists_forall_le

Modified src/order/directed.lean
- \+ *lemma* directed_of
- \+ *lemma* directed_id
- \+ *lemma* directed_id_iff_is_directed
- \+ *lemma* is_directed_mono
- \+ *lemma* exists_ge_ge
- \+ *lemma* exists_le_le

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
- \+ *lemma* algebra_base_injective
- \+ *lemma* adjoin_algebra_injective
- \+ *def* cyclotomic_field
- \+ *def* cyclotomic_field.algebra_base
- \+ *def* cyclotomic_ring
- \+ *def* algebra_base

Modified src/ring_theory/localization.lean



## [2022-01-12 17:52:38](https://github.com/leanprover-community/mathlib/commit/fa9d2bf)
feat(data/mv_polynomial/variables): add mv_polynomial.total_deg_finset_sum ([#11375](https://github.com/leanprover-community/mathlib/pull/11375))
Total degree of a sum of mv_polynomials is less than or equal to the maximum of all their degrees.
#### Estimated changes
Modified src/data/mv_polynomial/variables.lean
- \+ *lemma* total_degree_finset_sum



## [2022-01-12 17:52:37](https://github.com/leanprover-community/mathlib/commit/258686f)
fix(order/complete_lattice): fix diamond in sup vs max and min vs inf ([#11309](https://github.com/leanprover-community/mathlib/pull/11309))
`complete_linear_order` has separate `max` and `sup` fields. There is no need to have both, so this removes one of them by telling the structure compiler to merge the two fields. The same is true of `inf` and `min`.
As well as diamonds being possible in the abstract case, a handful of concrete example of this diamond existed.
`linear_order` instances with default-populated fields were usually to blame.
#### Estimated changes
Modified src/algebra/tropical/big_operators.lean

Modified src/data/nat/enat.lean
- \- *lemma* sup_eq_max
- \- *lemma* inf_eq_min

Modified src/data/nat/lattice.lean

Modified src/data/real/ennreal.lean
- \+/\- *lemma* add_top
- \+/\- *lemma* top_add
- \+/\- *lemma* add_top
- \+/\- *lemma* top_add

Modified src/order/bounded_order.lean

Modified src/order/complete_lattice.lean

Modified src/order/conditionally_complete_lattice.lean

Modified src/order/lattice.lean
- \+ *lemma* sup_eq_max_default
- \+ *lemma* inf_eq_min_default



## [2022-01-12 16:25:20](https://github.com/leanprover-community/mathlib/commit/975031d)
feat(data/nat/factorization): add lemma `factorization_prod` ([#11395](https://github.com/leanprover-community/mathlib/pull/11395))
For any `p : ℕ` and any function `g : α → ℕ` that's non-zero on `S : finset α`, the power of `p` in `S.prod g` equals the sum over `x ∈ S` of the powers of `p` in `g x`.
Generalises `factorization_mul`, which is the special case where `S.card = 2` and `g = id`.
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+ *lemma* factorization_prod



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
Created src/data/sigma/interval.lean
- \+ *lemma* card_Icc
- \+ *lemma* card_Ico
- \+ *lemma* card_Ioc
- \+ *lemma* card_Ioo
- \+ *lemma* Icc_mk_mk
- \+ *lemma* Ico_mk_mk
- \+ *lemma* Ioc_mk_mk
- \+ *lemma* Ioo_mk_mk

Modified src/data/sigma/order.lean
- \+ *lemma* mk_le_mk_iff
- \+ *lemma* mk_lt_mk_iff
- \+ *lemma* le_def
- \+ *lemma* lt_def

Modified src/order/locally_finite.lean



## [2022-01-12 11:08:51](https://github.com/leanprover-community/mathlib/commit/e8eb7d9)
feat(order/cover): `f a` covers `f b` iff `a` covers `b`  ([#11392](https://github.com/leanprover-community/mathlib/pull/11392))
... for order isomorphisms, and also weaker statements.
#### Estimated changes
Modified src/order/cover.lean
- \+/\- *lemma* not_covers
- \+ *lemma* densely_ordered_iff_forall_not_covers
- \+ *lemma* of_dual_covers_of_dual_iff
- \+ *lemma* covers.of_image
- \+ *lemma* covers.image
- \+ *lemma* apply_covers_apply_iff
- \+/\- *lemma* not_covers



## [2022-01-12 10:06:13](https://github.com/leanprover-community/mathlib/commit/912c47d)
feat(topology/algebra/continuous_monoid_hom): New file ([#11304](https://github.com/leanprover-community/mathlib/pull/11304))
This PR defines continuous monoid homs.
#### Estimated changes
Created src/topology/algebra/continuous_monoid_hom.lean
- \+ *lemma* ext
- \+ *def* mk'
- \+ *def* comp
- \+ *def* prod
- \+ *def* prod_map
- \+ *def* one
- \+ *def* id
- \+ *def* fst
- \+ *def* snd
- \+ *def* inl
- \+ *def* inr
- \+ *def* diag
- \+ *def* swap
- \+ *def* mul
- \+ *def* inv
- \+ *def* coprod



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
- \+ *lemma* det_conj_lie
- \+ *lemma* linear_equiv_det_conj_lie



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
- \+ *lemma* floor_le_of_le
- \+ *lemma* int.floor_to_nat
- \+ *lemma* int.ceil_to_nat
- \+ *lemma* nat.cast_floor_eq_int_floor
- \+ *lemma* nat.cast_floor_eq_cast_int_floor
- \+ *lemma* nat.cast_ceil_eq_int_ceil
- \+ *lemma* nat.cast_ceil_eq_cast_int_ceil
- \- *lemma* floor_to_nat
- \- *lemma* ceil_to_nat



## [2022-01-12 07:31:02](https://github.com/leanprover-community/mathlib/commit/bfe9515)
feat(data/multiset/basic): add map_count_true_eq_filter_card ([#11306](https://github.com/leanprover-community/mathlib/pull/11306))
Add a lemma about counting over a map. Spun off of [#10888](https://github.com/leanprover-community/mathlib/pull/10888).
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* count_eq_card_filter_eq
- \+ *lemma* map_count_true_eq_filter_card



## [2022-01-12 07:31:00](https://github.com/leanprover-community/mathlib/commit/9fd03e1)
chore(order/lexicographic): cleanup ([#11299](https://github.com/leanprover-community/mathlib/pull/11299))
Changes include:
* factoring out `prod.lex.trans` from the proof of `le_trans` in `prod.lex.has_le`, and similarly for `antisymm` and `is_total`
* adding some missing `to_lex` annotations in the `prod.lex.{le,lt}_def` lemmas
* avoiding reproving decidability of `prod.lex`
* replacing some proofs with pattern matching to avoid getting type-incorrect goals where `prod.lex.has_le` appears comparing terms that are not of type `lex`.
#### Estimated changes
Modified src/data/prod.lean
- \+ *lemma* lex.refl_left
- \+ *lemma* lex.refl_right
- \+ *lemma* lex.trans

Modified src/order/lexicographic.lean
- \+/\- *lemma* le_iff
- \+/\- *lemma* lt_iff
- \+/\- *lemma* le_iff
- \+/\- *lemma* lt_iff



## [2022-01-12 07:30:59](https://github.com/leanprover-community/mathlib/commit/deac58a)
feat(topology/uniform_space/compact_convergence): when the domain is locally compact, compact convergence is just locally uniform convergence ([#11292](https://github.com/leanprover-community/mathlib/pull/11292))
Also, locally uniform convergence is just uniform convergence when the domain is compact.
#### Estimated changes
Modified src/topology/uniform_space/compact_convergence.lean
- \+/\- *lemma* tendsto_iff_forall_compact_tendsto_uniformly_on
- \+ *lemma* tendsto_of_tendsto_locally_uniformly
- \+ *lemma* tendsto_locally_uniformly_of_tendsto
- \+ *lemma* tendsto_iff_tendsto_locally_uniformly
- \+/\- *lemma* tendsto_iff_tendsto_uniformly
- \+/\- *lemma* tendsto_iff_forall_compact_tendsto_uniformly_on
- \+/\- *lemma* tendsto_iff_tendsto_uniformly

Modified src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* tendsto_uniformly_on_iff_tendsto_uniformly_comp_coe
- \+ *lemma* tendsto_locally_uniformly_on_iff_tendsto_locally_uniformly_comp_coe
- \+ *lemma* tendsto_locally_uniformly_iff_tendsto_uniformly_of_compact_space
- \+ *lemma* tendsto_locally_uniformly_on_iff_tendsto_uniformly_on_of_compact



## [2022-01-12 07:30:58](https://github.com/leanprover-community/mathlib/commit/2099725)
feat(topology/homotopy/product): Product of homotopic paths ([#11153](https://github.com/leanprover-community/mathlib/pull/11153))
Specialize homotopy products to paths and prove some theorems about the product of paths.
#### Estimated changes
Modified src/topology/homotopy/fundamental_groupoid.lean

Modified src/topology/homotopy/path.lean
- \+ *lemma* comp_lift
- \+ *lemma* map_lift
- \+ *def* quotient.comp
- \+ *def* quotient.map_fn

Modified src/topology/homotopy/product.lean
- \+ *lemma* pi_lift
- \+ *lemma* comp_pi_eq_pi_comp
- \+ *lemma* proj_pi
- \+ *lemma* pi_proj
- \+ *lemma* prod_lift
- \+ *lemma* comp_prod_eq_prod_comp
- \+ *lemma* proj_left_prod
- \+ *lemma* proj_right_prod
- \+ *lemma* prod_proj_left_proj_right
- \+ *def* pi_homotopy
- \+ *def* pi
- \+ *def* proj
- \+ *def* prod_homotopy
- \+ *def* prod
- \+ *def* proj_left
- \+ *def* proj_right

Modified src/topology/path_connected.lean
- \+ *lemma* prod_coe_fn
- \+ *lemma* trans_prod_eq_prod_trans
- \+ *lemma* pi_coe_fn
- \+ *lemma* trans_pi_eq_pi_trans



## [2022-01-12 05:04:58](https://github.com/leanprover-community/mathlib/commit/15b5e24)
feat(data/polynomial/taylor): taylor's formula ([#11139](https://github.com/leanprover-community/mathlib/pull/11139))
Via proofs about `hasse_deriv`.
Added some monomial API too.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* sup_ite

Modified src/data/nat/with_bot.lean
- \+ *lemma* with_bot.lt_one_iff_le_zero

Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* degree_C_lt
- \+ *lemma* leading_coeff_pow_X_add_C

Modified src/data/polynomial/hasse_deriv.lean
- \+ *lemma* hasse_deriv_eq_zero_of_lt_nat_degree
- \+ *lemma* nat_degree_hasse_deriv_le
- \+ *lemma* nat_degree_hasse_deriv

Modified src/data/polynomial/taylor.lean
- \+ *lemma* taylor_zero'
- \+ *lemma* taylor_zero
- \+ *lemma* taylor_monomial
- \+ *lemma* nat_degree_taylor
- \+ *lemma* taylor_taylor
- \+ *lemma* sum_taylor_eq



## [2022-01-12 04:02:53](https://github.com/leanprover-community/mathlib/commit/af074c8)
feat(analysis/normed_space/lp_space): API for `lp.single` ([#11307](https://github.com/leanprover-community/mathlib/pull/11307))
Definition and basic properties for `lp.single`, an element of `lp` space supported at one point.
#### Estimated changes
Modified src/analysis/normed_space/lp_space.lean
- \+ *lemma* coe_fn_sum



## [2022-01-12 02:31:11](https://github.com/leanprover-community/mathlib/commit/cdd44cd)
refactor(topology/algebra/uniform_group): Use `to_additive` ([#11366](https://github.com/leanprover-community/mathlib/pull/11366))
This PR replace the definition
`def topological_add_group.to_uniform_space : uniform_space G :=`
with the definition
`@[to_additive] def topological_group.to_uniform_space : uniform_space G :=`
#### Estimated changes
Modified src/topology/algebra/uniform_group.lean
- \+ *def* topological_group.to_uniform_space
- \- *def* topological_add_group.to_uniform_space



## [2022-01-12 00:08:22](https://github.com/leanprover-community/mathlib/commit/89f4786)
feat(analysis/special_functions/pow): norm_num extension for rpow ([#11382](https://github.com/leanprover-community/mathlib/pull/11382))
Fixes [#11374](https://github.com/leanprover-community/mathlib/pull/11374)
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *theorem* zpow_neg_coe_of_pos

Modified src/algebra/star/chsh.lean

Modified src/analysis/special_functions/pow.lean
- \+ *theorem* rpow_pos
- \+ *theorem* rpow_neg
- \+ *theorem* cpow_pos
- \+ *theorem* cpow_neg
- \+ *theorem* nnrpow_pos
- \+ *theorem* nnrpow_neg
- \+ *theorem* ennrpow_pos
- \+ *theorem* ennrpow_neg

Modified src/tactic/norm_num.lean
- \+ *lemma* zpow_pos
- \+ *lemma* zpow_neg

Modified test/norm_num.lean



## [2022-01-12 00:08:21](https://github.com/leanprover-community/mathlib/commit/647598b)
feat(data/nat/factorization): add lemma `factorization_le_iff_dvd` ([#11377](https://github.com/leanprover-community/mathlib/pull/11377))
For non-zero `d n : ℕ`, `d.factorization ≤ n.factorization ↔ d ∣ n`
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+ *lemma* factorization_le_iff_dvd



## [2022-01-11 20:49:16](https://github.com/leanprover-community/mathlib/commit/a5f7909)
fix(algebra/tropical/basic): provide explicit min and max ([#11380](https://github.com/leanprover-community/mathlib/pull/11380))
This also renames `tropical.add` to `tropical.has_add`, since this matches how we normally do this, and it makes unfolding easier.
Without this change, we have a diamond where `linear_order.min` is not defeq to `lattice.inf`.
#### Estimated changes
Modified src/algebra/tropical/basic.lean
- \+ *lemma* untrop_sup
- \+ *lemma* untrop_max
- \+ *lemma* min_eq_add
- \+ *lemma* inf_eq_add
- \+ *lemma* trop_max_def
- \+ *lemma* trop_sup_def



## [2022-01-11 20:49:15](https://github.com/leanprover-community/mathlib/commit/73847ff)
feat(algebra/indicator_function): add primed version for `mul_indicator_mul` and `indicator_sub` ([#11379](https://github.com/leanprover-community/mathlib/pull/11379))
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+ *lemma* mul_indicator_mul'
- \+ *lemma* mul_indicator_div
- \+ *lemma* mul_indicator_div'
- \- *lemma* indicator_sub



## [2022-01-11 20:49:14](https://github.com/leanprover-community/mathlib/commit/d1c4961)
feat(data/real/ennreal): add ennreal lemma for `a / 3 + a / 3 + a / 3 = a`  ([#11378](https://github.com/leanprover-community/mathlib/pull/11378))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* inv_three_add_inv_three
- \+ *lemma* add_thirds



## [2022-01-11 20:49:13](https://github.com/leanprover-community/mathlib/commit/57a8933)
feat(group_theory/free_group): promote free_group_congr to a mul_equiv ([#11373](https://github.com/leanprover-community/mathlib/pull/11373))
Also some various golfs and cleanups
#### Estimated changes
Modified src/group_theory/free_group.lean
- \+ *lemma* quot_map_mk
- \+/\- *lemma* map.id
- \+/\- *lemma* map.id'
- \+ *lemma* free_group_congr_refl
- \+ *lemma* free_group_congr_symm
- \+ *lemma* free_group_congr_trans
- \+/\- *lemma* map.id
- \+/\- *lemma* map.id'
- \+/\- *theorem* map.comp
- \+/\- *theorem* map.comp
- \+/\- *def* map
- \+/\- *def* free_group_congr
- \- *def* map.aux
- \- *def* map.to_fun
- \+/\- *def* map
- \+/\- *def* free_group_congr



## [2022-01-11 20:49:12](https://github.com/leanprover-community/mathlib/commit/8db96a8)
feat(combinatorics/double_counting): Double-counting the edges of a bipartite graph ([#11372](https://github.com/leanprover-community/mathlib/pull/11372))
This proves a classic of double-counting arguments: If each element of the `|α|` elements on the left is connected to at least `m` elements on the right and each of the `|β|` elements on the right is connected to at most `n` elements on the left, then `|α| * m ≤ |β| * n` because the LHS is less than the number of edges which is less than the RHS.
This is put in a new file `combinatorics.double_counting` with the idea that we could gather double counting arguments here, much as is done with `combinatorics.pigeonhole`.
#### Estimated changes
Created src/combinatorics/double_counting.lean
- \+ *lemma* bipartite_below_swap
- \+ *lemma* bipartite_above_swap
- \+ *lemma* mem_bipartite_below
- \+ *lemma* mem_bipartite_above
- \+ *lemma* sum_card_bipartite_above_eq_sum_card_bipartite_below
- \+ *lemma* card_mul_le_card_mul
- \+ *lemma* card_mul_le_card_mul'
- \+ *lemma* card_mul_eq_card_mul
- \+ *def* bipartite_below
- \+ *def* bipartite_above



## [2022-01-11 20:49:11](https://github.com/leanprover-community/mathlib/commit/93e7741)
feat(ring_theory/witt_vector): Witt vectors over a domain are a domain ([#11346](https://github.com/leanprover-community/mathlib/pull/11346))
#### Estimated changes
Modified src/ring_theory/witt_vector/basic.lean
- \+ *def* constant_coeff

Modified src/ring_theory/witt_vector/defs.lean
- \+ *lemma* add_coeff_zero
- \+ *lemma* mul_coeff_zero

Created src/ring_theory/witt_vector/domain.lean
- \+ *lemma* shift_coeff
- \+ *lemma* verschiebung_shift
- \+ *lemma* eq_iterate_verschiebung
- \+ *lemma* verschiebung_nonzero
- \+ *def* shift

Modified src/ring_theory/witt_vector/identities.lean
- \+ *lemma* coeff_p_pow_eq_zero
- \+ *lemma* mul_char_p_coeff_zero
- \+ *lemma* mul_char_p_coeff_succ
- \+ *lemma* verschiebung_frobenius
- \+ *lemma* verschiebung_frobenius_comm
- \+ *lemma* iterate_verschiebung_coeff
- \+ *lemma* iterate_verschiebung_mul_left
- \+ *lemma* iterate_verschiebung_mul
- \+ *lemma* iterate_frobenius_coeff
- \+ *lemma* iterate_verschiebung_mul_coeff



## [2022-01-11 20:49:09](https://github.com/leanprover-community/mathlib/commit/83b0355)
feat(analysis/complex/isometry): `rotation` matrix representation and determinant ([#11339](https://github.com/leanprover-community/mathlib/pull/11339))
Add lemmas giving the matrix representation of `rotation` (with
respect to `basis_one_I`), and its determinant (both as a linear map
and as a linear equiv).  This is preparation for doing things about
how isometries affect orientations.
#### Estimated changes
Modified src/analysis/complex/isometry.lean
- \+ *lemma* to_matrix_rotation
- \+ *lemma* det_rotation
- \+ *lemma* linear_equiv_det_rotation

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
Created src/data/complex/determinant.lean
- \+ *lemma* det_conj_ae
- \+ *lemma* linear_equiv_det_conj_ae

Modified src/data/complex/module.lean
- \+ *lemma* to_matrix_conj_ae



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
- \+ *lemma* sep_empty

Modified src/order/antichain.lean
- \+ *lemma* eq_of_related'
- \- *lemma* mk_is_antichain
- \- *lemma* mk_subset
- \- *lemma* mk_max

Modified src/order/basic.lean
- \+ *lemma* ge_antisymm

Created src/order/minimal.lean
- \+ *lemma* maximals_subset
- \+ *lemma* minimals_subset
- \+ *lemma* maximals_empty
- \+ *lemma* minimals_empty
- \+ *lemma* maximals_singleton
- \+ *lemma* minimals_singleton
- \+ *lemma* maximals_swap
- \+ *lemma* minimals_swap
- \+ *lemma* maximals_antichain
- \+ *lemma* minimals_antichain
- \+ *lemma* maximals_eq_minimals
- \+ *lemma* set.subsingleton.maximals_eq
- \+ *lemma* set.subsingleton.minimals_eq
- \+ *lemma* maximals_mono
- \+ *lemma* minimals_mono
- \+ *lemma* maximals_union
- \+ *lemma* minimals_union
- \+ *lemma* maximals_inter_subset
- \+ *lemma* minimals_inter_subset
- \+ *lemma* inter_maximals_subset
- \+ *lemma* inter_minimals_subset
- \+ *lemma* _root_.is_antichain.maximals_eq
- \+ *lemma* _root_.is_antichain.minimals_eq
- \+ *lemma* maximals_idem
- \+ *lemma* minimals_idem
- \+ *lemma* is_antichain.max_maximals
- \+ *lemma* is_antichain.max_minimals
- \+ *lemma* is_least.mem_minimals
- \+ *lemma* is_greatest.mem_maximals
- \+ *lemma* is_least.minimals_eq
- \+ *lemma* is_greatest.maximals_eq
- \+ *def* maximals
- \+ *def* minimals

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
- \+ *lemma* nat_degree_ne_zero_induction_on



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
- \+ *lemma* mem_neighbor_set'

Modified src/computability/tm_to_partrec.lean

Modified src/computability/turing_machine.lean

Modified src/data/dfinsupp/basic.lean

Modified src/data/equiv/basic.lean

Modified src/data/equiv/set.lean

Modified src/data/finset/basic.lean
- \+/\- *lemma* piecewise_coe
- \+/\- *lemma* piecewise_coe

Modified src/data/finset/fold.lean

Modified src/data/finsupp/multiset.lean

Modified src/data/fintype/basic.lean
- \+ *lemma* card_congr'
- \+ *lemma* to_finset_congr

Modified src/data/fintype/fin.lean

Modified src/data/list/basic.lean
- \+ *lemma* filter_congr'
- \- *lemma* filter_congr
- \+ *theorem* map_id''

Modified src/data/list/count.lean

Modified src/data/list/intervals.lean

Modified src/data/list/lattice.lean

Modified src/data/list/nodup.lean

Modified src/data/list/perm.lean

Modified src/data/list/permutation.lean

Modified src/data/matrix/block.lean

Modified src/data/multiset/basic.lean
- \+/\- *lemma* map_hcongr
- \+/\- *lemma* map_hcongr
- \+/\- *theorem* map_congr
- \+ *theorem* map_comp_cons
- \+/\- *theorem* map_congr

Modified src/data/multiset/nodup.lean

Modified src/data/multiset/pi.lean
- \+ *lemma* pi.cons_ext

Modified src/data/multiset/powerset.lean

Modified src/data/mv_polynomial/basic.lean

Modified src/data/mv_polynomial/rename.lean

Modified src/data/nat/count.lean

Modified src/data/nat/enat.lean

Modified src/data/option/basic.lean
- \+/\- *theorem* guard_eq_some'
- \+/\- *theorem* guard_eq_some'

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
- \+ *lemma* discr_not_zero_of_basis
- \- *lemma* discr_not_zero_of_linear_independent



## [2022-01-11 13:55:34](https://github.com/leanprover-community/mathlib/commit/380e28e)
chore(set_theory/ordinal_arithmetic): Golfed some proofs ([#11369](https://github.com/leanprover-community/mathlib/pull/11369))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* enum_ord_mem
- \+/\- *theorem* blsub_le_enum_ord
- \+/\- *theorem* enum_ord.strict_mono
- \+/\- *theorem* enum_ord.surjective
- \+/\- *theorem* enum_ord_range
- \+/\- *theorem* eq_enum_ord
- \+/\- *theorem* enum_ord_mem
- \+/\- *theorem* blsub_le_enum_ord
- \+/\- *theorem* enum_ord.strict_mono
- \+/\- *theorem* enum_ord.surjective
- \+/\- *theorem* enum_ord_range
- \+/\- *theorem* eq_enum_ord
- \+/\- *def* enum_ord
- \+/\- *def* enum_ord.order_iso
- \+/\- *def* enum_ord
- \+/\- *def* enum_ord.order_iso



## [2022-01-11 13:55:33](https://github.com/leanprover-community/mathlib/commit/2963d7c)
feat(analysis/asymptotics/asymptotics): add `is_bounded_under.is_O_const` ([#11367](https://github.com/leanprover-community/mathlib/pull/11367))
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+ *theorem* _root_.filter.is_bounded_under.is_O_const
- \+/\- *theorem* is_O_const_of_tendsto
- \+/\- *theorem* is_O_const_of_tendsto



## [2022-01-11 13:55:32](https://github.com/leanprover-community/mathlib/commit/8f5303a)
refactor(topology/connected): drop `local attribute [instance] connected_component_setoid` ([#11365](https://github.com/leanprover-community/mathlib/pull/11365))
Add a coercion from `X` to `connected_components X` instead.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+/\- *lemma* not_disjoint_iff_nonempty_inter
- \+ *lemma* disjoint_or_nonempty_inter
- \+/\- *lemma* not_disjoint_iff_nonempty_inter

Modified src/topology/category/Profinite/default.lean

Modified src/topology/connected.lean
- \+ *lemma* is_clopen.connected_component_subset
- \+ *lemma* is_clopen.bUnion_connected_component_eq
- \+ *lemma* quotient_map.preimage_connected_component
- \+ *lemma* quotient_map.image_connected_component
- \+ *lemma* coe_eq_coe
- \+ *lemma* coe_ne_coe
- \+ *lemma* coe_eq_coe'
- \+ *lemma* surjective_coe
- \+ *lemma* quotient_map_coe
- \+ *lemma* continuous_coe
- \+ *lemma* range_coe
- \+ *lemma* continuous.image_eq_of_connected_component_eq
- \+/\- *lemma* continuous.connected_components_lift_continuous
- \+ *lemma* continuous.connected_components_lift_apply_coe
- \+ *lemma* continuous.connected_components_lift_comp_coe
- \+/\- *lemma* connected_components_lift_unique'
- \+/\- *lemma* continuous.connected_components_lift_unique
- \+/\- *lemma* connected_components_preimage_singleton
- \- *lemma* is_clopen.eq_union_connected_components
- \- *lemma* connected_component_rel_iff
- \- *lemma* connected_component_nrel_iff
- \- *lemma* continuous.image_eq_of_equiv
- \+/\- *lemma* continuous.connected_components_lift_continuous
- \- *lemma* continuous.connected_components_lift_factors
- \+/\- *lemma* continuous.connected_components_lift_unique
- \+/\- *lemma* connected_components_lift_unique'
- \+/\- *lemma* connected_components_preimage_singleton
- \+ *theorem* is_preconnected.subset_clopen
- \+ *theorem* disjoint_or_subset_of_clopen
- \+/\- *theorem* is_preconnected_iff_subset_of_disjoint_closed
- \- *theorem* subset_or_disjoint_of_clopen
- \+/\- *theorem* is_preconnected_iff_subset_of_disjoint_closed
- \+/\- *def* continuous.connected_components_lift
- \+/\- *def* continuous.connected_components_lift

Modified src/topology/constructions.lean
- \+ *lemma* continuous_quotient_lift_on'

Modified src/topology/separation.lean
- \+/\- *lemma* connected_component_eq_Inter_clopen
- \+/\- *lemma* connected_component_eq_Inter_clopen

Modified src/topology/subset_properties.lean



## [2022-01-11 13:55:30](https://github.com/leanprover-community/mathlib/commit/c1c0fa4)
feat(analysis/calculus/{f,}deriv): add some `iff` lemmas ([#11363](https://github.com/leanprover-community/mathlib/pull/11363))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_at_deriv_iff
- \+ *lemma* has_deriv_within_at_deriv_within_iff

Modified src/analysis/calculus/fderiv.lean
- \+ *theorem* filter.eventually_eq.has_fderiv_at_iff
- \+ *theorem* filter.eventually_eq.differentiable_at_iff
- \+ *theorem* filter.eventually_eq.has_fderiv_within_at_iff
- \+ *theorem* filter.eventually_eq.has_fderiv_within_at_iff_of_mem
- \+ *theorem* filter.eventually_eq.differentiable_within_at_iff
- \+ *theorem* filter.eventually_eq.differentiable_within_at_iff_of_mem



## [2022-01-11 13:55:28](https://github.com/leanprover-community/mathlib/commit/02181c7)
feat(algebra/group/conj): `conj_classes.map` preserves surjectivity ([#11362](https://github.com/leanprover-community/mathlib/pull/11362))
If `f : α →* β` is surjective, then so is `conj_classes.map f : conj_classes α → conj_classes β`.
#### Estimated changes
Modified src/algebra/group/conj.lean
- \+ *lemma* map_surjective



## [2022-01-11 13:55:13](https://github.com/leanprover-community/mathlib/commit/c94a17c)
feat(topology): a few simple lemmas ([#11360](https://github.com/leanprover-community/mathlib/pull/11360))
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* eventually_mem_nhds

Modified src/topology/continuous_on.lean
- \+ *lemma* insert_mem_nhds_iff
- \+ *lemma* continuous_within_at_compl_self
- \+/\- *lemma* continuous_within_at_update_same
- \+ *lemma* continuous_at_update_same
- \+ *lemma* continuous_within_at_iff_continuous_at
- \+/\- *lemma* continuous_within_at_update_same

Modified src/topology/separation.lean
- \+ *lemma* ne.nhds_within_diff_singleton
- \+ *lemma* continuous_at_update_of_ne



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
- \+/\- *lemma* normed_group.tendsto_at_top'

Modified src/data/psigma/order.lean

Modified src/data/real/nnreal.lean

Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* nonempty_Ioi
- \+/\- *lemma* nonempty_Iio
- \+/\- *lemma* nonempty_Ioi
- \+/\- *lemma* nonempty_Iio

Modified src/data/set/intervals/infinite.lean

Modified src/data/sigma/order.lean

Modified src/data/sum/order.lean
- \+ *lemma* no_min_order_iff
- \+ *lemma* no_max_order_iff
- \- *lemma* no_bot_order_iff
- \- *lemma* no_top_order_iff

Modified src/measure_theory/constructions/borel_space.lean

Modified src/measure_theory/integral/integral_eq_improper.lean
- \+/\- *lemma* ae_cover_Ioo
- \+/\- *lemma* ae_cover_Ioc
- \+/\- *lemma* ae_cover_Ico
- \+/\- *lemma* ae_cover_Ioi
- \+/\- *lemma* ae_cover_Iio
- \+/\- *lemma* integrable_of_interval_integral_norm_tendsto
- \+/\- *lemma* integrable_on_Iic_of_interval_integral_norm_tendsto
- \+/\- *lemma* interval_integral_tendsto_integral
- \+/\- *lemma* interval_integral_tendsto_integral_Iic
- \+/\- *lemma* ae_cover_Ioo
- \+/\- *lemma* ae_cover_Ioc
- \+/\- *lemma* ae_cover_Ico
- \+/\- *lemma* ae_cover_Ioi
- \+/\- *lemma* ae_cover_Iio
- \+/\- *lemma* integrable_of_interval_integral_norm_tendsto
- \+/\- *lemma* integrable_on_Iic_of_interval_integral_norm_tendsto
- \+/\- *lemma* interval_integral_tendsto_integral
- \+/\- *lemma* interval_integral_tendsto_integral_Iic

Modified src/measure_theory/integral/interval_integral.lean

Modified src/order/basic.lean
- \+ *lemma* exists_gt
- \+/\- *lemma* not_is_top
- \+ *lemma* exists_lt
- \+/\- *lemma* not_is_bot
- \- *lemma* no_top
- \+/\- *lemma* not_is_top
- \- *lemma* no_bot
- \+/\- *lemma* not_is_bot

Modified src/order/bounded_order.lean
- \+/\- *lemma* lt_iff_exists_coe_btwn
- \+/\- *lemma* lt_iff_exists_coe_btwn

Modified src/order/bounds.lean
- \+ *lemma* no_max_order.upper_bounds_univ
- \+ *lemma* no_min_order.lower_bounds_univ
- \+/\- *lemma* not_bdd_above_univ
- \+/\- *lemma* not_bdd_below_univ
- \+/\- *lemma* is_lub.nonempty
- \+/\- *lemma* is_glb.nonempty
- \- *lemma* no_top_order.upper_bounds_univ
- \- *lemma* no_bot_order.lower_bounds_univ
- \+/\- *lemma* not_bdd_above_univ
- \+/\- *lemma* not_bdd_below_univ
- \+/\- *lemma* is_lub.nonempty
- \+/\- *lemma* is_glb.nonempty

Modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* cInf_Ioi
- \+/\- *lemma* cSup_Iio
- \+/\- *lemma* cInf_Ioi
- \+/\- *lemma* cSup_Iio

Modified src/order/countable_dense_linear_order.lean
- \+/\- *lemma* exists_across
- \+/\- *lemma* exists_across
- \+/\- *def* defined_at_left
- \+/\- *def* defined_at_right
- \+/\- *def* fun_of_ideal
- \+/\- *def* inv_of_ideal
- \+/\- *def* defined_at_left
- \+/\- *def* defined_at_right
- \+/\- *def* fun_of_ideal
- \+/\- *def* inv_of_ideal

Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* Ioi_mem_at_top
- \+/\- *lemma* Iio_mem_at_bot
- \+/\- *lemma* eventually_gt_at_top
- \+/\- *lemma* eventually_lt_at_bot
- \+/\- *lemma* at_top_basis_Ioi
- \+/\- *lemma* frequently_at_top'
- \+/\- *lemma* frequently_at_bot'
- \+/\- *lemma* exists_lt_of_tendsto_at_top
- \+/\- *lemma* exists_lt_of_tendsto_at_bot
- \+/\- *lemma* high_scores
- \+/\- *lemma* low_scores
- \+/\- *lemma* frequently_high_scores
- \+/\- *lemma* frequently_low_scores
- \+/\- *lemma* map_coe_Ioi_at_top
- \+/\- *lemma* map_coe_Iio_at_bot
- \+/\- *lemma* tendsto_comp_coe_Ioi_at_top
- \+/\- *lemma* tendsto_comp_coe_Iio_at_bot
- \+/\- *lemma* unbounded_of_tendsto_at_top
- \+/\- *lemma* unbounded_of_tendsto_at_bot
- \+/\- *lemma* unbounded_of_tendsto_at_top'
- \+/\- *lemma* unbounded_of_tendsto_at_bot'
- \+/\- *lemma* Ioi_mem_at_top
- \+/\- *lemma* Iio_mem_at_bot
- \+/\- *lemma* eventually_gt_at_top
- \+/\- *lemma* eventually_lt_at_bot
- \+/\- *lemma* at_top_basis_Ioi
- \+/\- *lemma* frequently_at_top'
- \+/\- *lemma* frequently_at_bot'
- \+/\- *lemma* exists_lt_of_tendsto_at_top
- \+/\- *lemma* exists_lt_of_tendsto_at_bot
- \+/\- *lemma* high_scores
- \+/\- *lemma* low_scores
- \+/\- *lemma* frequently_high_scores
- \+/\- *lemma* frequently_low_scores
- \+/\- *lemma* map_coe_Ioi_at_top
- \+/\- *lemma* map_coe_Iio_at_bot
- \+/\- *lemma* tendsto_comp_coe_Ioi_at_top
- \+/\- *lemma* tendsto_comp_coe_Iio_at_bot
- \+/\- *lemma* unbounded_of_tendsto_at_top
- \+/\- *lemma* unbounded_of_tendsto_at_bot
- \+/\- *lemma* unbounded_of_tendsto_at_top'
- \+/\- *lemma* unbounded_of_tendsto_at_bot'

Modified src/order/lattice_intervals.lean

Modified src/order/liminf_limsup.lean
- \+/\- *lemma* not_is_bounded_under_of_tendsto_at_top
- \+/\- *lemma* not_is_bounded_under_of_tendsto_at_bot
- \+/\- *lemma* not_is_bounded_under_of_tendsto_at_top
- \+/\- *lemma* not_is_bounded_under_of_tendsto_at_bot

Modified src/order/locally_finite.lean

Modified src/order/succ_pred.lean
- \+/\- *lemma* succ_pred
- \+/\- *lemma* pred_succ
- \+/\- *lemma* succ_pred
- \+/\- *lemma* pred_succ

Modified src/set_theory/cardinal.lean

Modified src/set_theory/ordinal.lean

Modified src/topology/algebra/ordered/basic.lean
- \+/\- *lemma* dense.exists_lt
- \+/\- *lemma* dense.exists_gt
- \+/\- *lemma* dense.exists_le
- \+/\- *lemma* dense.exists_ge
- \+/\- *lemma* mem_nhds_iff_exists_Ioo_subset
- \+/\- *lemma* nhds_basis_Ioo
- \+/\- *lemma* filter.eventually.exists_Ioo_subset
- \+/\- *lemma* disjoint_nhds_at_top
- \+/\- *lemma* inf_nhds_at_top
- \+/\- *lemma* disjoint_nhds_at_bot
- \+/\- *lemma* inf_nhds_at_bot
- \+/\- *lemma* not_tendsto_nhds_of_tendsto_at_top
- \+/\- *lemma* not_tendsto_at_top_of_tendsto_nhds
- \+/\- *lemma* not_tendsto_nhds_of_tendsto_at_bot
- \+/\- *lemma* not_tendsto_at_bot_of_tendsto_nhds
- \+/\- *lemma* mem_nhds_within_Ioi_iff_exists_Ioo_subset
- \+/\- *lemma* mem_nhds_within_Ioi_iff_exists_Ioc_subset
- \+/\- *lemma* mem_nhds_within_Iio_iff_exists_Ioo_subset
- \+/\- *lemma* mem_nhds_within_Iio_iff_exists_Ico_subset
- \+/\- *lemma* mem_nhds_within_Ici_iff_exists_Ico_subset
- \+/\- *lemma* mem_nhds_within_Ici_iff_exists_Icc_subset'
- \+/\- *lemma* mem_nhds_within_Iic_iff_exists_Ioc_subset
- \+/\- *lemma* mem_nhds_within_Iic_iff_exists_Icc_subset'
- \+/\- *lemma* mem_nhds_within_Ici_iff_exists_Icc_subset
- \+/\- *lemma* mem_nhds_within_Iic_iff_exists_Icc_subset
- \+/\- *lemma* nhds_basis_Ioo_pos
- \+/\- *lemma* nhds_basis_abs_sub_lt
- \+/\- *lemma* nhds_basis_zero_abs_sub_lt
- \+/\- *lemma* nhds_basis_Ioo_pos_of_pos
- \+/\- *lemma* exists_seq_strict_mono_tendsto
- \+/\- *lemma* exists_seq_strict_anti_tendsto
- \+/\- *lemma* closure_Ioi
- \+/\- *lemma* closure_Iio
- \+/\- *lemma* interior_Ici
- \+/\- *lemma* interior_Iic
- \+/\- *lemma* interior_Icc
- \+/\- *lemma* interior_Ico
- \+/\- *lemma* interior_Ioc
- \+/\- *lemma* frontier_Ici
- \+/\- *lemma* frontier_Iic
- \+/\- *lemma* frontier_Ioi
- \+/\- *lemma* frontier_Iio
- \+/\- *lemma* frontier_Icc
- \+/\- *lemma* frontier_Ico
- \+/\- *lemma* frontier_Ioc
- \+/\- *lemma* nhds_within_Ioi_ne_bot
- \+/\- *lemma* nhds_within_Ioi_self_ne_bot
- \+/\- *lemma* filter.eventually.exists_gt
- \+/\- *lemma* nhds_within_Iio_ne_bot
- \+/\- *lemma* nhds_within_Iio_self_ne_bot
- \+/\- *lemma* filter.eventually.exists_lt
- \+/\- *lemma* dense.exists_lt
- \+/\- *lemma* dense.exists_gt
- \+/\- *lemma* dense.exists_le
- \+/\- *lemma* dense.exists_ge
- \+/\- *lemma* mem_nhds_iff_exists_Ioo_subset
- \+/\- *lemma* nhds_basis_Ioo
- \+/\- *lemma* filter.eventually.exists_Ioo_subset
- \+/\- *lemma* disjoint_nhds_at_top
- \+/\- *lemma* inf_nhds_at_top
- \+/\- *lemma* disjoint_nhds_at_bot
- \+/\- *lemma* inf_nhds_at_bot
- \+/\- *lemma* not_tendsto_nhds_of_tendsto_at_top
- \+/\- *lemma* not_tendsto_at_top_of_tendsto_nhds
- \+/\- *lemma* not_tendsto_nhds_of_tendsto_at_bot
- \+/\- *lemma* not_tendsto_at_bot_of_tendsto_nhds
- \+/\- *lemma* mem_nhds_within_Ioi_iff_exists_Ioo_subset
- \+/\- *lemma* mem_nhds_within_Ioi_iff_exists_Ioc_subset
- \+/\- *lemma* mem_nhds_within_Iio_iff_exists_Ioo_subset
- \+/\- *lemma* mem_nhds_within_Iio_iff_exists_Ico_subset
- \+/\- *lemma* mem_nhds_within_Ici_iff_exists_Ico_subset
- \+/\- *lemma* mem_nhds_within_Ici_iff_exists_Icc_subset'
- \+/\- *lemma* mem_nhds_within_Iic_iff_exists_Ioc_subset
- \+/\- *lemma* mem_nhds_within_Iic_iff_exists_Icc_subset'
- \+/\- *lemma* mem_nhds_within_Ici_iff_exists_Icc_subset
- \+/\- *lemma* mem_nhds_within_Iic_iff_exists_Icc_subset
- \+/\- *lemma* nhds_basis_Ioo_pos
- \+/\- *lemma* nhds_basis_abs_sub_lt
- \+/\- *lemma* nhds_basis_zero_abs_sub_lt
- \+/\- *lemma* nhds_basis_Ioo_pos_of_pos
- \+/\- *lemma* exists_seq_strict_mono_tendsto
- \+/\- *lemma* exists_seq_strict_anti_tendsto
- \+/\- *lemma* closure_Ioi
- \+/\- *lemma* closure_Iio
- \+/\- *lemma* interior_Ici
- \+/\- *lemma* interior_Iic
- \+/\- *lemma* interior_Icc
- \+/\- *lemma* interior_Ico
- \+/\- *lemma* interior_Ioc
- \+/\- *lemma* frontier_Ici
- \+/\- *lemma* frontier_Iic
- \+/\- *lemma* frontier_Ioi
- \+/\- *lemma* frontier_Iio
- \+/\- *lemma* frontier_Icc
- \+/\- *lemma* frontier_Ico
- \+/\- *lemma* frontier_Ioc
- \+/\- *lemma* nhds_within_Ioi_ne_bot
- \+/\- *lemma* nhds_within_Ioi_self_ne_bot
- \+/\- *lemma* filter.eventually.exists_gt
- \+/\- *lemma* nhds_within_Iio_ne_bot
- \+/\- *lemma* nhds_within_Iio_self_ne_bot
- \+/\- *lemma* filter.eventually.exists_lt

Modified src/topology/algebra/ordered/monotone_convergence.lean

Modified src/topology/instances/irrational.lean

Modified src/topology/instances/real.lean

Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* tendsto_at_top'
- \+/\- *theorem* tendsto_at_top'



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
- \+ *lemma* finprod_mem_eq_one_of_forall_eq_one
- \+ *lemma* finprod_eq_one_of_forall_eq_one



## [2022-01-11 13:55:07](https://github.com/leanprover-community/mathlib/commit/eb9c152)
feat(algebra/order/field): lemmas relating `a / b` and `a` when `1 ≤ b` and `1 < b` ([#11333](https://github.com/leanprover-community/mathlib/pull/11333))
This PR is a collection of items that https://github.com/leanprover-community/mathlib/pull/7891 adds in and that aren't declared on `master` yet. Please let me know if I overlooked something.
After merging it, https://github.com/leanprover-community/mathlib/pull/7891 can theoretically be closed.
#### Estimated changes
Modified src/algebra/order/field.lean
- \+/\- *lemma* div_lt_div_of_lt_left
- \+ *lemma* div_le_self
- \+ *lemma* div_lt_self
- \+/\- *lemma* div_lt_div_of_lt_left



## [2022-01-11 13:55:05](https://github.com/leanprover-community/mathlib/commit/2865d8c)
refactor(data/set/prod): add notation class for set-like product ([#11300](https://github.com/leanprover-community/mathlib/pull/11300))
This PR adds notation class `has_set_prod` for product of sets and subobjects. I also add an instance for `set`s. Later I want to migrate `finset`s and `sub*` product to this notation class.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean

Modified src/algebra/indicator_function.lean

Modified src/algebra/pointwise.lean
- \+/\- *lemma* image_mul_prod
- \+/\- *lemma* image_mul_prod

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
- \+/\- *lemma* finite.prod
- \+/\- *lemma* finite.prod

Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* Iic_prod_Iic
- \+/\- *lemma* Ici_prod_Ici
- \+/\- *lemma* Ici_prod_eq
- \+/\- *lemma* Iic_prod_eq
- \+/\- *lemma* Iic_prod_Iic
- \+/\- *lemma* Ici_prod_Ici
- \+/\- *lemma* Ici_prod_eq
- \+/\- *lemma* Iic_prod_eq

Modified src/data/set/lattice.lean
- \+/\- *lemma* prod_Union
- \+/\- *lemma* prod_sUnion
- \+/\- *lemma* Union_prod_const
- \+/\- *lemma* Union_prod
- \+/\- *lemma* prod_eq_seq
- \+/\- *lemma* prod_Union
- \+/\- *lemma* prod_sUnion
- \+/\- *lemma* Union_prod_const
- \+/\- *lemma* Union_prod
- \+/\- *lemma* prod_eq_seq

Modified src/data/set/prod.lean
- \+/\- *lemma* prod_eq
- \+/\- *lemma* mem_prod_eq
- \+/\- *lemma* mem_prod
- \+/\- *lemma* prod_mk_mem_set_prod_eq
- \+/\- *lemma* mk_mem_prod
- \+/\- *lemma* prod_mono
- \+/\- *lemma* prod_subset_iff
- \+/\- *lemma* forall_prod_set
- \+/\- *lemma* exists_prod_set
- \+/\- *lemma* prod_empty
- \+/\- *lemma* empty_prod
- \+/\- *lemma* univ_prod_univ
- \+/\- *lemma* univ_prod
- \+/\- *lemma* prod_univ
- \+/\- *lemma* singleton_prod
- \+/\- *lemma* prod_singleton
- \+/\- *lemma* singleton_prod_singleton
- \+/\- *lemma* union_prod
- \+/\- *lemma* prod_union
- \+/\- *lemma* prod_inter_prod
- \+/\- *lemma* insert_prod
- \+/\- *lemma* prod_insert
- \+/\- *lemma* prod_preimage_left
- \+/\- *lemma* prod_preimage_right
- \+/\- *lemma* mk_preimage_prod_left
- \+/\- *lemma* mk_preimage_prod_right
- \+/\- *lemma* mk_preimage_prod_left_eq_empty
- \+/\- *lemma* mk_preimage_prod_right_eq_empty
- \+/\- *lemma* preimage_swap_prod
- \+/\- *lemma* image_swap_prod
- \+/\- *lemma* nonempty.prod
- \+/\- *lemma* nonempty.fst
- \+/\- *lemma* nonempty.snd
- \+/\- *lemma* prod_nonempty_iff
- \+/\- *lemma* prod_eq_empty_iff
- \+/\- *lemma* fst_image_prod_subset
- \+/\- *lemma* prod_subset_preimage_fst
- \+/\- *lemma* fst_image_prod
- \+/\- *lemma* snd_image_prod_subset
- \+/\- *lemma* prod_subset_preimage_snd
- \+/\- *lemma* snd_image_prod
- \+/\- *lemma* prod_diff_prod
- \+/\- *lemma* prod_subset_prod_iff
- \+/\- *lemma* image_prod
- \+/\- *lemma* prod_eq
- \+/\- *lemma* mem_prod_eq
- \+/\- *lemma* mem_prod
- \+/\- *lemma* prod_mk_mem_set_prod_eq
- \+/\- *lemma* mk_mem_prod
- \+/\- *lemma* prod_mono
- \+/\- *lemma* prod_subset_iff
- \+/\- *lemma* forall_prod_set
- \+/\- *lemma* exists_prod_set
- \+/\- *lemma* prod_empty
- \+/\- *lemma* empty_prod
- \+/\- *lemma* univ_prod_univ
- \+/\- *lemma* univ_prod
- \+/\- *lemma* prod_univ
- \+/\- *lemma* singleton_prod
- \+/\- *lemma* prod_singleton
- \+/\- *lemma* singleton_prod_singleton
- \+/\- *lemma* union_prod
- \+/\- *lemma* prod_union
- \+/\- *lemma* prod_inter_prod
- \+/\- *lemma* insert_prod
- \+/\- *lemma* prod_insert
- \+/\- *lemma* prod_preimage_left
- \+/\- *lemma* prod_preimage_right
- \+/\- *lemma* mk_preimage_prod_left
- \+/\- *lemma* mk_preimage_prod_right
- \+/\- *lemma* mk_preimage_prod_left_eq_empty
- \+/\- *lemma* mk_preimage_prod_right_eq_empty
- \+/\- *lemma* preimage_swap_prod
- \+/\- *lemma* image_swap_prod
- \+/\- *lemma* nonempty.prod
- \+/\- *lemma* nonempty.fst
- \+/\- *lemma* nonempty.snd
- \+/\- *lemma* prod_nonempty_iff
- \+/\- *lemma* prod_eq_empty_iff
- \+/\- *lemma* fst_image_prod_subset
- \+/\- *lemma* prod_subset_preimage_fst
- \+/\- *lemma* fst_image_prod
- \+/\- *lemma* snd_image_prod_subset
- \+/\- *lemma* prod_subset_preimage_snd
- \+/\- *lemma* snd_image_prod
- \+/\- *lemma* prod_diff_prod
- \+/\- *lemma* prod_subset_prod_iff
- \+/\- *lemma* image_prod

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
- \+/\- *lemma* prod_prod
- \+/\- *lemma* prod_prod

Modified src/measure_theory/group/prod.lean

Modified src/measure_theory/integral/divergence_theorem.lean

Modified src/measure_theory/integral/interval_integral.lean

Modified src/measure_theory/integral/lebesgue.lean

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable_set_prod_of_nonempty
- \+/\- *lemma* measurable_set_prod_of_nonempty
- \+/\- *def* set.prod
- \+/\- *def* set.prod

Modified src/measure_theory/measure/lebesgue.lean
- \+/\- *lemma* region_between_subset
- \+/\- *lemma* region_between_subset

Modified src/order/complete_boolean_algebra.lean
- \+/\- *theorem* Inf_sup_Inf
- \+/\- *theorem* Sup_inf_Sup
- \+/\- *theorem* Inf_sup_Inf
- \+/\- *theorem* Sup_inf_Sup

Modified src/order/filter/bases.lean
- \+/\- *lemma* mem_prod_self_iff
- \+/\- *lemma* mem_prod_self_iff

Modified src/order/filter/basic.lean

Modified src/order/filter/interval.lean

Modified src/order/filter/lift.lean
- \+/\- *lemma* prod_def
- \+/\- *lemma* prod_same_eq
- \+/\- *lemma* prod_def
- \+/\- *lemma* prod_same_eq

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
- \+/\- *lemma* image_coev
- \+/\- *lemma* image_coev

Modified src/topology/connected.lean

Modified src/topology/constructions.lean
- \+/\- *lemma* is_open_prod_iff
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
- \+/\- *def* set_seq_aux
- \+/\- *def* set_seq_aux

Modified src/topology/uniform_space/compact_separated.lean

Modified src/topology/uniform_space/completion.lean

Modified src/topology/uniform_space/separation.lean
- \+/\- *lemma* is_separated_def'
- \+/\- *lemma* is_separated_def'

Modified src/topology/uniform_space/uniform_convergence.lean

Modified src/topology/uniform_space/uniform_embedding.lean

Modified src/topology/vector_bundle.lean



## [2022-01-11 13:55:04](https://github.com/leanprover-community/mathlib/commit/3cd9088)
feat(ring_theory/polynomial/cyclotomic/basic): add lemmas  ([#11266](https://github.com/leanprover-community/mathlib/pull/11266))
From flt-regular.
#### Estimated changes
Modified src/algebra/ne_zero.lean
- \+ *lemma* not_dvd_char

Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* is_root_cyclotomic_iff_char_zero
- \+ *lemma* cyclotomic_mul_prime_eq_pow_of_not_dvd
- \+ *lemma* cyclotomic_mul_prime_dvd_eq_pow
- \+ *lemma* cyclotomic_mul_prime_pow_eq
- \+ *lemma* is_root_cyclotomic_prime_pow_mul_iff_of_char_p



## [2022-01-11 13:55:02](https://github.com/leanprover-community/mathlib/commit/4ac13d9)
feat(data/dfinsupp/interval): Finitely supported dependent functions to locally finite orders are locally finite ([#11175](https://github.com/leanprover-community/mathlib/pull/11175))
This provides the ` locally_finite_order` instance for `Π₀ i, α i` in a new file `data.dfinsupp.interval`.
#### Estimated changes
Modified src/data/dfinsupp/basic.lean
- \+/\- *lemma* mk_apply
- \+ *lemma* mk_of_mem
- \+ *lemma* mk_of_not_mem
- \+/\- *lemma* mem_support_iff
- \+ *lemma* not_mem_support_iff
- \+/\- *lemma* mk_apply
- \+/\- *lemma* mem_support_iff

Created src/data/dfinsupp/interval.lean
- \+ *lemma* card_dfinsupp
- \+ *lemma* mem_dfinsupp_iff
- \+ *lemma* mem_dfinsupp_iff_of_support_subset
- \+ *lemma* mem_singleton_apply_iff
- \+ *lemma* range_Icc_apply
- \+ *lemma* mem_range_Icc_apply_iff
- \+ *lemma* support_range_Icc_subset
- \+ *lemma* mem_pi
- \+ *lemma* card_pi
- \+ *lemma* card_Icc
- \+ *lemma* card_Ico
- \+ *lemma* card_Ioc
- \+ *lemma* card_Ioo
- \+ *def* dfinsupp
- \+ *def* singleton
- \+ *def* range_Icc
- \+ *def* pi

Modified src/data/dfinsupp/order.lean
- \+/\- *lemma* le_iff'
- \+/\- *lemma* le_iff
- \+/\- *lemma* single_le_iff
- \- *lemma* not_mem_support_iff
- \+/\- *lemma* le_iff'
- \+/\- *lemma* le_iff
- \+/\- *lemma* single_le_iff

Modified src/data/finset/basic.lean
- \+ *lemma* not_mem_mono

Modified src/data/multiset/basic.lean
- \+ *lemma* subset_of_le
- \+ *lemma* mem_of_le
- \+ *lemma* not_mem_mono
- \+ *lemma* le_zero
- \+ *lemma* cons_le_cons_iff
- \+ *lemma* cons_le_cons
- \+ *lemma* le_cons_of_not_mem
- \- *theorem* subset_of_le
- \- *theorem* mem_of_le
- \- *theorem* le_zero
- \- *theorem* cons_le_cons_iff
- \- *theorem* cons_le_cons
- \- *theorem* le_cons_of_not_mem



## [2022-01-11 11:13:20](https://github.com/leanprover-community/mathlib/commit/40b6b45)
feat(category_theory): `Cat` is a strict bicategory ([#11348](https://github.com/leanprover-community/mathlib/pull/11348))
This PR defines a bicategory structure on `Cat`. This also introduces the propositional type class `bicategory.strict`, and proves that `Cat` is an instance of this class.
#### Estimated changes
Created src/category_theory/bicategory/strict.lean

Modified src/category_theory/category/Cat.lean



## [2022-01-11 11:13:19](https://github.com/leanprover-community/mathlib/commit/a4052f9)
feat(ring_theory/hahn_series): order_pow ([#11334](https://github.com/leanprover-community/mathlib/pull/11334))
Generalize to have `no_zero_divisors (hahn_series Γ R)`,
which generalizes `order_mul`.
Also provide `coeff_eq_zero_of_lt_order`.
#### Estimated changes
Modified src/ring_theory/hahn_series.lean
- \+ *lemma* coeff_eq_zero_of_lt_order
- \+/\- *lemma* order_mul
- \+ *lemma* order_pow
- \+/\- *lemma* order_mul



## [2022-01-11 11:13:18](https://github.com/leanprover-community/mathlib/commit/90ba054)
feat(algebraic_geometry): Define the category of `AffineScheme`s ([#11326](https://github.com/leanprover-community/mathlib/pull/11326))
#### Estimated changes
Created src/algebraic_geometry/AffineScheme.lean
- \+ *lemma* mem_AffineScheme
- \+ *lemma* is_affine_of_iso
- \+ *lemma* range_is_affine_open_of_open_immersion
- \+ *lemma* top_is_affine_open
- \+ *lemma* is_basis_affine_open
- \+ *def* AffineScheme
- \+ *def* Scheme.iso_Spec
- \+ *def* Spec
- \+ *def* forget_to_Scheme
- \+ *def* Γ
- \+ *def* equiv_CommRing
- \+ *def* is_affine_open

Modified src/algebraic_geometry/Gamma_Spec_adjunction.lean

Modified src/algebraic_geometry/open_immersion.lean
- \+ *lemma* lift_fac
- \+ *lemma* lift_uniq
- \+ *def* Scheme.restrict
- \+ *def* Scheme.of_restrict
- \+ *def* iso_restrict
- \+ *def* lift
- \+ *def* iso_of_range_eq

Modified src/category_theory/adjunction/reflective.lean
- \+ *def* equiv_ess_image_of_reflective



## [2022-01-11 11:13:17](https://github.com/leanprover-community/mathlib/commit/c03bd32)
feat(analysis/normed_space/star): add lemmas about continuity and norm of identity ([#11324](https://github.com/leanprover-community/mathlib/pull/11324))
#### Estimated changes
Modified src/analysis/normed_space/star.lean
- \+/\- *lemma* star_isometry
- \+ *lemma* continuous_star
- \+ *lemma* continuous_on_star
- \+ *lemma* continuous_at_star
- \+ *lemma* continuous_within_at_star
- \+ *lemma* tendsto_star
- \+ *lemma* filter.tendsto.star
- \+ *lemma* continuous.star
- \+ *lemma* continuous_at.star
- \+ *lemma* continuous_on.star
- \+ *lemma* continuous_within_at.star
- \+ *lemma* norm_self_mul_star
- \+ *lemma* norm_star_mul_self'
- \+ *lemma* norm_one
- \+/\- *lemma* star_isometry
- \- *lemma* cstar_ring.norm_self_mul_star
- \- *lemma* cstar_ring.norm_star_mul_self'
- \+/\- *def* star_normed_group_hom
- \+/\- *def* star_normed_group_hom



## [2022-01-11 11:13:16](https://github.com/leanprover-community/mathlib/commit/ebbc973)
feat(data/mv_polynomial): assorted mv_polynomial and finsupp lemmas ([#11319](https://github.com/leanprover-community/mathlib/pull/11319))
Mostly around total degree, supports and homogeneous components.
From flt-regular.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* support_smul_eq

Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* monomial_zero
- \+ *lemma* monomial_eq_zero
- \+/\- *lemma* monomial_zero

Modified src/data/mv_polynomial/variables.lean
- \+ *lemma* total_degree_monomial
- \+ *lemma* total_degree_X_pow

Modified src/ring_theory/polynomial/homogeneous.lean
- \+ *lemma* is_homogeneous_of_total_degree_zero
- \+ *lemma* homogeneous_component_C_mul



## [2022-01-11 11:13:15](https://github.com/leanprover-community/mathlib/commit/c500b99)
feat(ring_theory/laurent): coe from R[[x]] to R((x)) ([#11318](https://github.com/leanprover-community/mathlib/pull/11318))
And actually the changes reported in [#11295](https://github.com/leanprover-community/mathlib/pull/11295)
Generalize `power_series.coeff_smul`
#### Estimated changes
Modified src/ring_theory/hahn_series.lean
- \+ *lemma* of_power_series_C
- \+ *lemma* of_power_series_X
- \+ *lemma* of_power_series_X_pow

Modified src/ring_theory/laurent_series.lean
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* coe_add
- \+ *lemma* coe_mul
- \+ *lemma* coeff_coe
- \+ *lemma* coe_C
- \+ *lemma* coe_X
- \+ *lemma* coe_smul
- \+ *lemma* coe_bit0
- \+ *lemma* coe_bit1
- \+ *lemma* coe_pow
- \- *lemma* of_power_series_C
- \- *lemma* of_power_series_X
- \- *lemma* of_power_series_X_pow
- \- *lemma* coe_laurent
- \- *lemma* coe_coe
- \- *lemma* coe_laurent_zero
- \- *lemma* coe_laurent_one
- \- *lemma* coe_laurent_add
- \- *lemma* coe_laurent_mul
- \- *lemma* coeff_coe_laurent_coe
- \- *lemma* coeff_coe_laurent
- \- *lemma* coe_laurent_C
- \- *lemma* coe_laurent_X
- \- *lemma* coe_laurent_smul

Modified src/ring_theory/power_series/basic.lean
- \+/\- *lemma* coeff_smul
- \+/\- *lemma* coeff_smul



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
Created src/category_theory/bicategory/functor.lean
- \+ *lemma* to_prefunctor_obj
- \+ *lemma* to_prefunctor_map
- \+ *lemma* to_prelax_functor_obj
- \+ *lemma* to_prelax_functor_map
- \+ *lemma* to_prelax_functor_map₂
- \+ *def* id
- \+ *def* comp
- \+ *def* oplax_functor.map₂_associator_aux
- \+ *def* map_functor
- \+ *def* id
- \+ *def* comp



## [2022-01-11 11:13:11](https://github.com/leanprover-community/mathlib/commit/624cb70)
feat(set_theory/ordinal_arithmetic): Extra lemmas about suprema ([#11178](https://github.com/leanprover-community/mathlib/pull/11178))
Proved lemmas pertaining to when suprema or least strict upper bounds are zero.
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+ *lemma* eq_zero_of_out_empty
- \+ *theorem* out_empty_iff_eq_zero

Modified src/set_theory/ordinal_arithmetic.lean
- \+ *lemma* lsub_eq_zero
- \+ *lemma* lsub_pos
- \+ *lemma* blsub_eq_zero
- \+ *lemma* blsub_pos
- \+ *theorem* sup_eq_zero_iff
- \+ *theorem* bsup_eq_zero_iff
- \+ *theorem* lsub_eq_zero_iff
- \+ *theorem* blsub_eq_zero_iff



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
- \+/\- *lemma* coe_of_injective_symm
- \+/\- *lemma* self_comp_of_injective_symm
- \+/\- *lemma* coe_of_injective_symm
- \+/\- *lemma* self_comp_of_injective_symm
- \+/\- *theorem* apply_of_injective_symm
- \+/\- *theorem* of_injective_symm_apply
- \+/\- *theorem* apply_of_injective_symm
- \+/\- *theorem* of_injective_symm_apply

Modified src/data/fin/basic.lean

Modified src/group_theory/perm/sign.lean

Modified src/linear_algebra/basis.lean

Modified src/logic/small.lean
- \+/\- *theorem* small_of_injective
- \+/\- *theorem* small_of_surjective
- \+/\- *theorem* small_of_injective
- \+/\- *theorem* small_of_surjective



## [2022-01-11 02:45:39](https://github.com/leanprover-community/mathlib/commit/89bff5e)
feat(algebra/big_operators): add product versions of some sum lemmas ([#11358](https://github.com/leanprover-community/mathlib/pull/11358))
and to_additive to get the old ones back
#### Estimated changes
Modified src/algebra/big_operators/multiset.lean
- \+ *lemma* prod_eq_one_iff
- \+ *lemma* le_prod_of_mem
- \- *lemma* sum_eq_zero_iff
- \- *lemma* le_sum_of_mem

Modified src/data/list/big_operators.lean
- \+ *lemma* prod_eq_one_iff
- \- *lemma* sum_eq_zero_iff



## [2022-01-11 02:45:38](https://github.com/leanprover-community/mathlib/commit/d8a75bd)
chore(simple_graph/basic): Fix typo in docstring: adjacent vertices, not edges ([#11356](https://github.com/leanprover-community/mathlib/pull/11356))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean



## [2022-01-10 23:30:59](https://github.com/leanprover-community/mathlib/commit/8910f6d)
feat(ring_theory/discriminant): remove an assumption ([#11359](https://github.com/leanprover-community/mathlib/pull/11359))
We remove a `nonempty` assumption.
#### Estimated changes
Modified src/ring_theory/discriminant.lean
- \+/\- *lemma* discr_not_zero_of_linear_independent
- \+/\- *lemma* discr_not_zero_of_linear_independent



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
- \+ *lemma* orthonormal.inner_right_sum
- \+ *lemma* orthonormal.inner_left_sum
- \+ *lemma* orthonormal.inner_finsupp_eq_sum_left
- \+ *lemma* orthonormal.inner_finsupp_eq_sum_right
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
Created src/analysis/inner_product_space/orientation.lean
- \+ *lemma* orthonormal.orthonormal_adjust_to_orientation
- \+ *lemma* orientation.fin_orthonormal_basis_orientation



## [2022-01-10 23:30:52](https://github.com/leanprover-community/mathlib/commit/4e7e5a6)
feat(set_theory/ordinal_arithmetic): Enumerating unbounded sets of ordinals with ordinals ([#10979](https://github.com/leanprover-community/mathlib/pull/10979))
This PR introduces `enum_ord`, which enumerates an unbounded set of ordinals using ordinals. This is used to build an explicit order isomorphism `enum_ord.order_iso`.
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+ *theorem* not_lt_omin

Modified src/set_theory/ordinal_arithmetic.lean
- \+ *lemma* enum_ord_def'_H
- \+ *lemma* enum_ord_def_H
- \+ *theorem* enum_ord_def'
- \+ *theorem* enum_ord_mem
- \+ *theorem* blsub_le_enum_ord
- \+ *theorem* enum_ord.strict_mono
- \+ *theorem* enum_ord_def
- \+ *theorem* enum_ord.surjective
- \+ *theorem* enum_ord_range
- \+ *theorem* eq_enum_ord
- \+ *def* enum_ord
- \+ *def* enum_ord.order_iso
- \+ *def* CNF



## [2022-01-10 23:30:51](https://github.com/leanprover-community/mathlib/commit/8e92af1)
feat(algebra/associated): add lemmas to split [#9345](https://github.com/leanprover-community/mathlib/pull/9345) ([#10941](https://github.com/leanprover-community/mathlib/pull/10941))
This PR contains lemmas from PR [[#9345](https://github.com/leanprover-community/mathlib/pull/9345)](https://github.com/leanprover-community/mathlib/pull/9345), which was starting to get quite lengthy.
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* not_is_unit_of_not_is_unit_dvd
- \+ *lemma* bot_eq_one
- \+ *lemma* mk_injective
- \+ *lemma* le_one_iff
- \+ *lemma* dvd_not_unit.is_unit_of_irreducible_right
- \+ *lemma* not_irreducible_of_not_unit_dvd_not_unit
- \+ *lemma* dvd_not_unit.not_unit
- \+ *lemma* is_unit_of_associated_mul
- \+ *lemma* dvd_not_unit.not_associated
- \+ *lemma* dvd_not_unit_of_dvd_not_unit_associated
- \+ *lemma* dvd_not_unit.ne
- \+ *lemma* pow_injective_of_not_unit

Modified src/algebra/divisibility.lean
- \+ *theorem* ne_zero_of_dvd_ne_zero



## [2022-01-10 23:30:50](https://github.com/leanprover-community/mathlib/commit/4bf4859)
feat(data/finsupp/pointwise): add a definition of the pointwise action of functions on finsupps ([#10933](https://github.com/leanprover-community/mathlib/pull/10933))
I couldn't find this, and it seems like quite a natural way to talk about multiplying functions with finsupps.
I'm not sure what additional lemmas would be useful yet, as I don't have a particular application in mind at present so suggestions/additions are welcome
#### Estimated changes
Modified src/data/finsupp/pointwise.lean
- \+ *lemma* coe_pointwise_module



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
- \+ *lemma* multiplicative_factorization
- \+ *lemma* multiplicative_factorization'
- \+ *lemma* factorization_prod_pow_eq_self

Modified src/number_theory/arithmetic_function.lean
- \+ *lemma* multiplicative_factorization



## [2022-01-10 16:17:20](https://github.com/leanprover-community/mathlib/commit/dc3cbb7)
feat(data/polynomial/erase_lead): introduce two lemmas to compute `nat_degree`s under certain maps ([#11265](https://github.com/leanprover-community/mathlib/pull/11265))
This PR is a step in the direction of simplifying [#11139](https://github.com/leanprover-community/mathlib/pull/11139).
It contains a proof of the helper lemmas `map_nat_degree_eq_sub` and `map_nat_degree_eq_nat_degree` to shorten the proof of `nat_degree_hasse_deriv` and `nat_degree_taylor`.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2311139.20taylor.20sum.20and.20nat_degree_taylor)
#### Estimated changes
Modified src/data/polynomial/erase_lead.lean
- \+ *lemma* mono_map_nat_degree_eq
- \+ *lemma* map_nat_degree_eq_sub
- \+ *lemma* map_nat_degree_eq_nat_degree



## [2022-01-10 16:17:19](https://github.com/leanprover-community/mathlib/commit/168ad7f)
feat(data/nat/cast): generalize to `fun_like` ([#11128](https://github.com/leanprover-community/mathlib/pull/11128))
#### Estimated changes
Modified archive/100-theorems-list/16_abel_ruffini.lean

Modified src/algebra/algebra/basic.lean
- \- *lemma* map_nat_cast

Modified src/algebra/char_p/basic.lean
- \+/\- *theorem* frobenius_nat_cast
- \+/\- *theorem* frobenius_nat_cast

Modified src/algebra/char_p/pi.lean

Modified src/algebra/char_p/quotient.lean

Modified src/algebra/char_p/subring.lean

Modified src/algebra/char_zero.lean

Modified src/algebra/group_power/lemmas.lean

Modified src/algebra/ne_zero.lean
- \+/\- *lemma* of_injective
- \+ *lemma* nat_of_injective
- \- *lemma* of_injective'
- \+/\- *lemma* of_injective

Modified src/data/complex/basic.lean

Modified src/data/complex/is_R_or_C.lean

Modified src/data/int/cast.lean

Modified src/data/matrix/char_p.lean

Modified src/data/nat/cast.lean
- \+/\- *lemma* cast_two
- \+/\- *lemma* commute_cast
- \+/\- *lemma* coe_nat_dvd
- \+ *lemma* ext_nat'
- \+ *lemma* add_monoid_hom.ext_nat
- \+ *lemma* eq_nat_cast'
- \+ *lemma* map_nat_cast'
- \+/\- *lemma* eq_nat_cast
- \+/\- *lemma* map_nat_cast
- \+/\- *lemma* ext_nat
- \+/\- *lemma* coe_nat
- \+/\- *lemma* cast_two
- \+/\- *lemma* commute_cast
- \+/\- *lemma* coe_nat_dvd
- \+/\- *lemma* ext_nat
- \+/\- *lemma* eq_nat_cast
- \+/\- *lemma* map_nat_cast
- \+/\- *lemma* eq_nat_cast
- \+/\- *lemma* map_nat_cast
- \+/\- *lemma* ext_nat
- \+/\- *lemma* coe_nat
- \+/\- *theorem* cast_one
- \+ *theorem* ext_nat''
- \+ *theorem* monoid_with_zero_hom.ext_nat
- \+/\- *theorem* cast_one
- \- *theorem* ext_nat

Modified src/data/polynomial/algebra_map.lean

Modified src/data/polynomial/basic.lean

Modified src/data/polynomial/derivative.lean

Modified src/data/polynomial/eval.lean
- \- *theorem* map_nat_cast

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
- \+/\- *lemma* coe_nat_cast
- \+/\- *lemma* coe_nat_cast

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
- \+ *lemma* det_conj



## [2022-01-10 13:07:57](https://github.com/leanprover-community/mathlib/commit/48b21e5)
feat(probability_theory/martingale): one direction of the optional stopping theorem ([#11007](https://github.com/leanprover-community/mathlib/pull/11007))
#### Estimated changes
Modified src/probability_theory/martingale.lean
- \+ *lemma* integrable_stopped_value
- \+ *lemma* expected_stopped_value_mono

Modified src/probability_theory/stopping.lean
- \+ *lemma* is_stopping_time.measurable_set_lt
- \+ *lemma* is_stopping_time.measurable_set_lt_le
- \+ *lemma* stopped_value_sub_eq_sum
- \+ *lemma* stopped_value_sub_eq_sum'
- \+ *lemma* stopped_value_eq
- \+ *lemma* mem_ℒp_stopped_value
- \+ *lemma* integrable_stopped_value



## [2022-01-10 10:18:16](https://github.com/leanprover-community/mathlib/commit/7782157)
feat (data/finset/lattice): add more finset induction lemmas ([#10889](https://github.com/leanprover-community/mathlib/pull/10889))
2 more finset induction lemmas based on the order imposed by a function.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* induction_on_max_value
- \+ *lemma* induction_on_min_value



## [2022-01-10 01:23:46](https://github.com/leanprover-community/mathlib/commit/99fe7ac)
chore(data/set/function): move inv_fun_on out of `logic/function/basic` ([#11330](https://github.com/leanprover-community/mathlib/pull/11330))
This removes `function.inv_fun_on_eq'` as it is a duplicate of `inj_on.left_inv_on_inv_fun_on`.
#### Estimated changes
Modified src/data/set/function.lean
- \+ *theorem* inv_fun_on_pos
- \+ *theorem* inv_fun_on_mem
- \+ *theorem* inv_fun_on_eq
- \+ *theorem* inv_fun_on_neg

Modified src/logic/function/basic.lean
- \- *theorem* inv_fun_on_pos
- \- *theorem* inv_fun_on_mem
- \- *theorem* inv_fun_on_eq
- \- *theorem* inv_fun_on_eq'
- \- *theorem* inv_fun_on_neg

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
- \+/\- *lemma* default_def
- \+/\- *lemma* default_def

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
- \+/\- *theorem* default_bool
- \+/\- *theorem* default_bool

Modified src/data/bundle.lean

Modified src/data/equiv/basic.lean

Modified src/data/equiv/embedding.lean

Modified src/data/equiv/encodable/basic.lean

Modified src/data/finsupp/basic.lean
- \+/\- *lemma* unique_single
- \+/\- *lemma* unique_ext
- \+/\- *lemma* unique_ext_iff
- \+/\- *lemma* unique_single
- \+/\- *lemma* unique_ext
- \+/\- *lemma* unique_ext_iff

Modified src/data/fintype/basic.lean
- \+/\- *lemma* univ_unique
- \+/\- *lemma* univ_unique

Modified src/data/holor.lean

Modified src/data/int/basic.lean
- \+/\- *lemma* default_eq_zero
- \+/\- *lemma* default_eq_zero

Modified src/data/lazy_list.lean

Modified src/data/list/basic.lean
- \+/\- *theorem* take'_nil
- \+/\- *theorem* take'_nil

Modified src/data/list/big_operators.lean

Modified src/data/list/defs.lean

Modified src/data/list/func.lean
- \+/\- *lemma* get_nil
- \+/\- *lemma* nil_pointwise
- \+/\- *lemma* get_pointwise
- \+/\- *lemma* get_nil
- \+/\- *lemma* nil_pointwise
- \+/\- *lemma* get_pointwise

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
- \+/\- *lemma* univ_unique
- \+/\- *lemma* default_coe_singleton
- \+/\- *lemma* range_unique
- \+/\- *lemma* univ_unique
- \+/\- *lemma* default_coe_singleton
- \+/\- *lemma* range_unique

Modified src/data/set/lattice.lean

Modified src/data/setoid/partition.lean

Modified src/data/sigma/basic.lean

Modified src/data/stream/init.lean

Modified src/data/string/basic.lean
- \+/\- *lemma* head_empty
- \+/\- *lemma* head_empty

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
- \+/\- *def* tree_hom
- \+/\- *def* tree_hom

Modified src/group_theory/perm/basic.lean
- \+/\- *lemma* default_perm
- \+/\- *lemma* default_perm

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
- \+/\- *lemma* eq_default
- \+/\- *lemma* default_eq
- \+/\- *lemma* forall_iff
- \+/\- *lemma* exists_iff
- \+/\- *lemma* fin.default_eq_zero
- \+/\- *lemma* eq_default
- \+/\- *lemma* default_eq
- \+/\- *lemma* forall_iff
- \+/\- *lemma* exists_iff

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
- \+/\- *theorem* supr_unique
- \+/\- *theorem* infi_unique
- \+/\- *theorem* supr_unique
- \+/\- *theorem* infi_unique

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
- \+/\- *lemma* default_def
- \+/\- *lemma* default_def

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
- \+/\- *lemma* default_def
- \+/\- *lemma* coe_fun_unique
- \+/\- *lemma* default_def
- \+/\- *lemma* coe_fun_unique

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
- \+/\- *def* int_to_a

Modified test/lint_simp_nf.lean
- \+/\- *def* f
- \+/\- *def* c
- \+/\- *def* d
- \+/\- *def* h
- \+/\- *def* f
- \+/\- *def* c
- \+/\- *def* d
- \+/\- *def* h

Modified test/pi_simp.lean
- \+/\- *def* eval_default
- \+/\- *def* eval_default

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
- \+ *lemma* periodic.lift_coe
- \+ *def* periodic.lift



## [2022-01-09 16:18:24](https://github.com/leanprover-community/mathlib/commit/49ba33e)
feat(vscode): add a snippet for inserting a module docstring template ([#11312](https://github.com/leanprover-community/mathlib/pull/11312))
We already have a vscode snippet for adding copyright headers, this PR adds a similar one to generate a default module docstring with many of the common sections stubbed out.
By default it takes the filename, converts underscores to spaces and capitalizes each word to create the title, as this seems a sensible default. But otherwise all text is a static default example following the documentation style page to make it easier to remember the various recommended secitons.
To test do `ctrl+shift+p` to open the command pallette, type insert snippet, enter, and type module and it should show up.
See also [#3186](https://github.com/leanprover-community/mathlib/pull/3186)
#### Estimated changes
Created .vscode/module-docstring.code-snippets



## [2022-01-09 16:18:23](https://github.com/leanprover-community/mathlib/commit/fadbd95)
feat(field_theory/ratfunc): ratfunc.lift_on without is_domain ([#11227](https://github.com/leanprover-community/mathlib/pull/11227))
We might want to state results about rational functions without assuming
that the base ring is an integral domain.
Cf. Misconceptions about $K_X$, Kleiman, Steven; Stacks01X1
#### Estimated changes
Modified docs/references.bib

Modified src/field_theory/ratfunc.lean
- \+ *lemma* lift_on_of_fraction_ring_mk
- \+ *lemma* lift_on_condition_of_lift_on'_condition



## [2022-01-09 13:09:57](https://github.com/leanprover-community/mathlib/commit/9c224ff)
split(data/set/functor): Split off `data.set.lattice` ([#11327](https://github.com/leanprover-community/mathlib/pull/11327))
This moves the functor structure of `set` in a new file `data.set.functor`.
Also adds `alternative set` because it's quick and easy.
#### Estimated changes
Modified src/computability/NFA.lean

Modified src/control/traversable/instances.lean

Modified src/data/set/finite.lean

Created src/data/set/functor.lean
- \+ *lemma* bind_def
- \+ *lemma* fmap_eq_image
- \+ *lemma* seq_eq_set_seq
- \+ *lemma* pure_def

Modified src/data/set/lattice.lean
- \- *lemma* bind_def
- \- *lemma* fmap_eq_image
- \- *lemma* seq_eq_set_seq
- \- *lemma* pure_def



## [2022-01-09 07:58:15](https://github.com/leanprover-community/mathlib/commit/ad4ea53)
chore(*): miscellaneous to_additive related cleanup ([#11316](https://github.com/leanprover-community/mathlib/pull/11316))
A few cleanup changes related to to_additive:
* After https://github.com/leanprover-community/lean/pull/618 was merged, we no longer need to add namespaces manually in filtered_colimits and open subgroup
* to_additive can now generate some more lemmas in big_operators/fin
* to_additive now handles a proof in measure/haar better than it used to
  so remove a workaround there
#### Estimated changes
Modified src/algebra/big_operators/fin.lean
- \- *lemma* sum_filter_zero_lt
- \- *lemma* sum_filter_succ_lt

Modified src/algebra/category/CommRing/filtered_colimits.lean

Modified src/measure_theory/measure/haar.lean

Modified src/topology/algebra/open_subgroup.lean



## [2022-01-09 06:06:07](https://github.com/leanprover-community/mathlib/commit/ca5e55c)
feat(linear_algebra/basis): `basis.ext`, `basis.ext'` for semilinear maps ([#11317](https://github.com/leanprover-community/mathlib/pull/11317))
Extend `basis.ext` and `basis.ext'` to apply to the general
(semilinear) case of `linear_map` and `linear_equiv`.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+/\- *theorem* ext
- \+/\- *theorem* ext'
- \+/\- *theorem* ext
- \+/\- *theorem* ext'



## [2022-01-09 03:54:54](https://github.com/leanprover-community/mathlib/commit/a58553d)
feat(data/nat/factorization): Add lemmas on factorizations of pairs of coprime numbers ([#10850](https://github.com/leanprover-community/mathlib/pull/10850))
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+ *lemma* factorization_disjoint_of_coprime
- \+ *lemma* factorization_mul_of_coprime
- \+ *lemma* factorization_mul_support_of_coprime
- \+ *lemma* factorization_mul_support_of_pos



## [2022-01-09 01:21:32](https://github.com/leanprover-community/mathlib/commit/d4846b3)
chore(ring_theory/fractional_ideal): fix typo ([#11311](https://github.com/leanprover-community/mathlib/pull/11311))
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean



## [2022-01-08 23:10:53](https://github.com/leanprover-community/mathlib/commit/22ff4eb)
feat(combinatorics/simple_graph/matchings): even_card_vertices_of_perfect_matching ([#11083](https://github.com/leanprover-community/mathlib/pull/11083))
#### Estimated changes
Modified src/combinatorics/simple_graph/matching.lean
- \+ *lemma* is_matching.to_edge_eq_of_adj
- \+ *lemma* is_matching.to_edge.surjective
- \+ *lemma* is_matching.to_edge_eq_to_edge_of_adj
- \+ *lemma* is_matching.even_card
- \+ *lemma* is_perfect_matching_iff_forall_degree
- \+ *lemma* is_perfect_matching.even_card

Modified src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* adj.of_spanning_coe
- \+ *lemma* neighbor_set_subset_verts
- \+ *lemma* is_spanning.card_verts
- \+ *lemma* degree_spanning_coe
- \- *lemma* spanning_coe_adj_sub



## [2022-01-08 21:54:48](https://github.com/leanprover-community/mathlib/commit/0a75fdf)
feat(linear_algebra/eigenspace): prove eigenvalues are exactly elements of the spectrum when the space is finite dimensional ([#10961](https://github.com/leanprover-community/mathlib/pull/10961))
This adds `has_eigenvalue_iff_mem_spectrum` and then uses it to golf `exists_eigenvalue`
- [x] depends on: [#10912](https://github.com/leanprover-community/mathlib/pull/10912) 
- [x] depends on: [#10919](https://github.com/leanprover-community/mathlib/pull/10919)
#### Estimated changes
Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* has_eigenvalue_iff_mem_spectrum



## [2022-01-08 18:36:59](https://github.com/leanprover-community/mathlib/commit/ee136d9)
chore(set_theory/game/domineering): extract repeated goal into lemma and golf ([#11298](https://github.com/leanprover-community/mathlib/pull/11298))
`fst_pred_mem_erase_of_mem_right` and `snd_pred_mem_erase_of_mem_left` were common subgoals that appeared in two lemmas each.
#### Estimated changes
Modified src/set_theory/game/domineering.lean
- \+ *lemma* mem_left
- \+ *lemma* mem_right
- \+ *lemma* fst_pred_mem_erase_of_mem_right
- \+ *lemma* snd_pred_mem_erase_of_mem_left
- \+/\- *def* shift_up
- \+/\- *def* shift_right
- \+/\- *def* shift_up
- \+/\- *def* shift_right



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
- \+ *lemma* _root_.affine_map.is_open_map
- \+ *lemma* interior_preimage
- \+ *lemma* closure_preimage
- \+ *lemma* frontier_preimage
- \- *lemma* open_mapping_affine
- \- *theorem* open_mapping



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
- \+/\- *lemma* sup_induction
- \+/\- *lemma* inf_induction
- \+/\- *lemma* sup'_induction
- \+/\- *lemma* inf'_induction
- \+/\- *lemma* sup_induction
- \+/\- *lemma* inf_induction
- \+/\- *lemma* sup'_induction
- \+/\- *lemma* inf'_induction

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
- \- *lemma* prime.pow_dvd_of_dvd_mul_right
- \- *lemma* prime.pow_dvd_of_dvd_mul_left



## [2022-01-08 16:29:05](https://github.com/leanprover-community/mathlib/commit/c76e113)
feat(ring_theory/laurent): coercion of R[x] to R((x)) lemmas ([#11295](https://github.com/leanprover-community/mathlib/pull/11295))
Make the coercion be `simp`-normal as opposed to `(algebra_map _ _)`.
Also generalize `of_power_series Γ R (power_series.C R r) = hahn_series.C r` and similarly for `X` to be true for any `[ordered semiring Γ]`, not just `ℤ`.
#### Estimated changes
Modified src/ring_theory/laurent_series.lean
- \+ *lemma* of_power_series_C
- \+ *lemma* coe_laurent
- \+ *lemma* coe_coe
- \+ *lemma* coe_laurent_zero
- \+ *lemma* coe_laurent_one
- \+ *lemma* coe_laurent_add
- \+ *lemma* coe_laurent_mul
- \+ *lemma* coeff_coe_laurent_coe
- \+ *lemma* coeff_coe_laurent
- \+ *lemma* coe_laurent_C
- \+ *lemma* coe_laurent_X
- \+ *lemma* coe_laurent_smul



## [2022-01-08 16:29:04](https://github.com/leanprover-community/mathlib/commit/1162509)
chore(data/fin/vec_notation): generalize smul_cons ([#11285](https://github.com/leanprover-community/mathlib/pull/11285))
#### Estimated changes
Modified src/data/complex/module.lean

Modified src/data/fin/vec_notation.lean
- \+/\- *lemma* smul_empty
- \+/\- *lemma* smul_cons
- \+/\- *lemma* smul_empty
- \+/\- *lemma* smul_cons



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
- \+/\- *lemma* induction_with_nat_degree_le
- \+/\- *lemma* induction_with_nat_degree_le



## [2022-01-08 16:28:59](https://github.com/leanprover-community/mathlib/commit/b181a12)
refactor(combinatorics/quiver): split into several files ([#11006](https://github.com/leanprover-community/mathlib/pull/11006))
This PR splits `combinatorics/quiver.lean` into several files. The main reason for this is to ensure that the category theory library only imports the necessary definitions (and not for example the stuff on arborescences).
Also adds some more documentation, and fixes a bug in the definition of weakly connected components.
#### Estimated changes
Modified src/category_theory/category/basic.lean

Modified src/category_theory/path_category.lean

Deleted src/combinatorics/quiver.lean
- \- *lemma* empty_arrow
- \- *lemma* length_nil
- \- *lemma* length_cons
- \- *lemma* comp_cons
- \- *lemma* comp_nil
- \- *lemma* nil_comp
- \- *lemma* comp_assoc
- \- *lemma* map_path_nil
- \- *lemma* map_path_cons
- \- *lemma* map_path_comp
- \- *lemma* shortest_path_spec
- \- *def* id
- \- *def* comp
- \- *def* wide_subquiver
- \- *def* wide_subquiver.to_Type
- \- *def* empty
- \- *def* hom.op
- \- *def* hom.unop
- \- *def* symmetrify
- \- *def* wide_subquiver_symmetrify
- \- *def* wide_subquiver_equiv_set_total
- \- *def* hom.to_path
- \- *def* length
- \- *def* comp
- \- *def* map_path
- \- *def* root
- \- *def* labelling
- \- *def* geodesic_subtree
- \- *def* reverse
- \- *def* path.reverse
- \- *def* zigzag_setoid
- \- *def* weakly_connected_component

Created src/combinatorics/quiver/arborescence.lean
- \+ *lemma* shortest_path_spec
- \+ *def* root
- \+ *def* geodesic_subtree

Created src/combinatorics/quiver/basic.lean
- \+ *lemma* empty_arrow
- \+ *def* id
- \+ *def* comp
- \+ *def* hom.op
- \+ *def* hom.unop
- \+ *def* empty

Created src/combinatorics/quiver/connected_component.lean
- \+ *def* symmetrify
- \+ *def* reverse
- \+ *def* path.reverse
- \+ *def* zigzag_setoid
- \+ *def* weakly_connected_component
- \+ *def* wide_subquiver_symmetrify

Created src/combinatorics/quiver/path.lean
- \+ *lemma* length_nil
- \+ *lemma* length_cons
- \+ *lemma* comp_cons
- \+ *lemma* comp_nil
- \+ *lemma* nil_comp
- \+ *lemma* comp_assoc
- \+ *lemma* map_path_nil
- \+ *lemma* map_path_cons
- \+ *lemma* map_path_comp
- \+ *def* hom.to_path
- \+ *def* length
- \+ *def* comp
- \+ *def* map_path

Created src/combinatorics/quiver/subquiver.lean
- \+ *def* wide_subquiver
- \+ *def* wide_subquiver.to_Type
- \+ *def* wide_subquiver_equiv_set_total
- \+ *def* labelling

Modified src/group_theory/nielsen_schreier.lean



## [2022-01-08 16:28:58](https://github.com/leanprover-community/mathlib/commit/9b3fec5)
feat(algebraic_geometry): Gamma-Spec adjunction ([#9802](https://github.com/leanprover-community/mathlib/pull/9802))
Define the adjunction between the functors Gamma (global sections) and Spec (to LocallyRingedSpace).
I'm currently working on a more general version in http://arxiv.org/pdf/1103.2139.pdf (Theorem 2), which may require refactoring `structure_sheaf` and `Spec`.
#### Estimated changes
Created src/algebraic_geometry/Gamma_Spec_adjunction.lean
- \+ *lemma* not_mem_prime_iff_unit_in_stalk
- \+ *lemma* to_Γ_Spec_preim_basic_open_eq
- \+ *lemma* to_Γ_Spec_continuous
- \+ *lemma* to_Γ_Spec_map_basic_open_eq
- \+ *lemma* is_unit_res_to_Γ_Spec_map_basic_open
- \+ *lemma* to_Γ_Spec_c_app_iff
- \+ *lemma* to_Γ_Spec_c_app_spec
- \+ *lemma* to_Γ_Spec_SheafedSpace_app_eq
- \+ *lemma* to_Γ_Spec_SheafedSpace_app_spec
- \+ *lemma* to_stalk_stalk_map_to_Γ_Spec
- \+ *lemma* comp_ring_hom_ext
- \+ *lemma* Γ_Spec_left_triangle
- \+ *lemma* left_triangle
- \+ *lemma* right_triangle
- \+ *lemma* adjunction_hom_equiv_apply
- \+ *lemma* adjunction_hom_equiv
- \+ *lemma* adjunction_hom_equiv_symm_apply
- \+ *lemma* adjunction_counit_app
- \+ *lemma* adjunction_unit_app
- \+ *def* Γ_to_stalk
- \+ *def* to_Γ_Spec_fun
- \+ *def* to_Γ_Spec_base
- \+ *def* to_Γ_Spec_c_app
- \+ *def* to_Γ_Spec_c_basic_opens
- \+ *def* to_Γ_Spec_SheafedSpace
- \+ *def* to_Γ_Spec
- \+ *def* identity_to_Γ_Spec
- \+ *def* LocallyRingedSpace_adjunction
- \+ *def* adjunction

Modified src/algebraic_geometry/Spec.lean

Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *lemma* stalk_algebra_map
- \+ *lemma* open_algebra_map
- \- *lemma* is_localization.to_stalk
- \- *lemma* is_localization.to_basic_open



## [2022-01-08 15:04:37](https://github.com/leanprover-community/mathlib/commit/b1955dc)
feat(data/matrix/basic): infix notation for matrix.dot_product in locale matrix ([#11289](https://github.com/leanprover-community/mathlib/pull/11289))
I created an infix notation for `matrix.dot_product` in locale `matrix`. The notation was consulted with @eric-wieser in [#11181](https://github.com/leanprover-community/mathlib/pull/11181).
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *lemma* dot_product_zero
- \+/\- *lemma* dot_product_zero'
- \+/\- *lemma* zero_dot_product
- \+/\- *lemma* zero_dot_product'
- \+/\- *lemma* add_dot_product
- \+/\- *lemma* dot_product_add
- \+/\- *lemma* diagonal_dot_product
- \+/\- *lemma* dot_product_diagonal
- \+/\- *lemma* dot_product_diagonal'
- \+/\- *lemma* single_dot_product
- \+/\- *lemma* dot_product_single
- \+/\- *lemma* neg_dot_product
- \+/\- *lemma* dot_product_neg
- \+/\- *lemma* sub_dot_product
- \+/\- *lemma* dot_product_sub
- \+/\- *lemma* star_dot_product_star
- \+/\- *lemma* star_dot_product
- \+/\- *lemma* dot_product_star
- \+/\- *lemma* dot_product_zero
- \+/\- *lemma* dot_product_zero'
- \+/\- *lemma* zero_dot_product
- \+/\- *lemma* zero_dot_product'
- \+/\- *lemma* add_dot_product
- \+/\- *lemma* dot_product_add
- \+/\- *lemma* diagonal_dot_product
- \+/\- *lemma* dot_product_diagonal
- \+/\- *lemma* dot_product_diagonal'
- \+/\- *lemma* single_dot_product
- \+/\- *lemma* dot_product_single
- \+/\- *lemma* neg_dot_product
- \+/\- *lemma* dot_product_neg
- \+/\- *lemma* sub_dot_product
- \+/\- *lemma* dot_product_sub
- \+/\- *lemma* star_dot_product_star
- \+/\- *lemma* star_dot_product
- \+/\- *lemma* dot_product_star



## [2022-01-08 15:04:36](https://github.com/leanprover-community/mathlib/commit/4304127)
feat(ring_theory/power_series): teach simp to simplify more coercions of polynomials  to power series ([#11287](https://github.com/leanprover-community/mathlib/pull/11287))
So that simp can prove that the polynomial `5 * X^2 + X + 1` coerced to a power series is the same thing with the power series generator `X`. Likewise for `mv_power_series`.
#### Estimated changes
Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* coe_bit0
- \+ *lemma* coe_bit1
- \+ *lemma* coe_pow
- \+ *lemma* coe_bit0
- \+ *lemma* coe_bit1
- \+ *lemma* coe_pow



## [2022-01-08 15:04:35](https://github.com/leanprover-community/mathlib/commit/e871386)
feat(number_theory/cyclotomic/basic): add lemmas ([#11264](https://github.com/leanprover-community/mathlib/pull/11264))
From flt-regular.
#### Estimated changes
Modified src/number_theory/cyclotomic/basic.lean
- \+ *lemma* integral
- \+ *lemma* finite_dimensional
- \+ *lemma* adjoin_roots_cyclotomic_eq_adjoin_nth_roots
- \+ *lemma* splits_X_pow_sub_one
- \+ *lemma* splits_cyclotomic
- \+ *lemma* splitting_field_X_pow_sub_one
- \+ *lemma* splitting_field_cyclotomic



## [2022-01-08 15:04:33](https://github.com/leanprover-community/mathlib/commit/c7fa66e)
feat(data/nat/prime): power to factor count divides natural ([#11226](https://github.com/leanprover-community/mathlib/pull/11226))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* pow_factors_count_dvd



## [2022-01-08 15:04:32](https://github.com/leanprover-community/mathlib/commit/4d79d5f)
chore(measure_theory/group/arithmetic): use implicit argument for measurable_space ([#11205](https://github.com/leanprover-community/mathlib/pull/11205))
The `measurable_space` argument is inferred from other arguments (like `measurable f` or a measure for example) instead of being a type class. This ensures that the lemmas are usable without `@` when several measurable space structures are used for the same type.
Also use more `variables`.
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean

Modified src/measure_theory/function/special_functions.lean
- \+/\- *lemma* measurable.inner
- \+/\- *lemma* ae_measurable.inner
- \+/\- *lemma* measurable.inner
- \+/\- *lemma* ae_measurable.inner

Modified src/measure_theory/group/arithmetic.lean
- \+/\- *lemma* measurable.const_mul
- \+/\- *lemma* ae_measurable.const_mul
- \+/\- *lemma* measurable.mul_const
- \+/\- *lemma* ae_measurable.mul_const
- \+/\- *lemma* measurable.mul'
- \+/\- *lemma* measurable.mul
- \+/\- *lemma* ae_measurable.mul'
- \+/\- *lemma* ae_measurable.mul
- \+/\- *lemma* measurable.pow
- \+/\- *lemma* ae_measurable.pow
- \+/\- *lemma* measurable.pow_const
- \+/\- *lemma* ae_measurable.pow_const
- \+/\- *lemma* measurable.const_pow
- \+/\- *lemma* ae_measurable.const_pow
- \+/\- *lemma* measurable.const_div
- \+/\- *lemma* ae_measurable.const_div
- \+/\- *lemma* measurable.div_const
- \+/\- *lemma* ae_measurable.div_const
- \+/\- *lemma* measurable.div'
- \+/\- *lemma* measurable.div
- \+/\- *lemma* ae_measurable.div'
- \+/\- *lemma* ae_measurable.div
- \+/\- *lemma* measurable_set_eq_fun
- \+/\- *lemma* measurable.inv
- \+/\- *lemma* ae_measurable.inv
- \+/\- *lemma* measurable_set.inv
- \+/\- *lemma* measurable.smul
- \+/\- *lemma* measurable.smul_const
- \+/\- *lemma* ae_measurable.smul_const
- \+/\- *lemma* measurable.const_smul'
- \+/\- *lemma* measurable.const_smul
- \+/\- *lemma* ae_measurable.const_smul'
- \+/\- *lemma* ae_measurable.const_smul
- \+/\- *lemma* list.ae_measurable_prod'
- \+/\- *lemma* list.ae_measurable_prod
- \+/\- *lemma* multiset.ae_measurable_prod'
- \+/\- *lemma* multiset.ae_measurable_prod
- \+/\- *lemma* finset.measurable_prod'
- \+/\- *lemma* finset.measurable_prod
- \+/\- *lemma* finset.ae_measurable_prod'
- \+/\- *lemma* finset.ae_measurable_prod
- \+/\- *lemma* measurable.const_mul
- \+/\- *lemma* ae_measurable.const_mul
- \+/\- *lemma* measurable.mul_const
- \+/\- *lemma* ae_measurable.mul_const
- \+/\- *lemma* measurable.mul'
- \+/\- *lemma* measurable.mul
- \+/\- *lemma* ae_measurable.mul'
- \+/\- *lemma* ae_measurable.mul
- \+/\- *lemma* measurable.pow
- \+/\- *lemma* ae_measurable.pow
- \+/\- *lemma* measurable.pow_const
- \+/\- *lemma* ae_measurable.pow_const
- \+/\- *lemma* measurable.const_pow
- \+/\- *lemma* ae_measurable.const_pow
- \+/\- *lemma* measurable.const_div
- \+/\- *lemma* ae_measurable.const_div
- \+/\- *lemma* measurable.div_const
- \+/\- *lemma* ae_measurable.div_const
- \+/\- *lemma* measurable.div'
- \+/\- *lemma* measurable.div
- \+/\- *lemma* ae_measurable.div'
- \+/\- *lemma* ae_measurable.div
- \+/\- *lemma* measurable_set_eq_fun
- \+/\- *lemma* measurable.inv
- \+/\- *lemma* ae_measurable.inv
- \+/\- *lemma* measurable_set.inv
- \+/\- *lemma* measurable.smul
- \+/\- *lemma* measurable.smul_const
- \+/\- *lemma* ae_measurable.smul_const
- \+/\- *lemma* measurable.const_smul'
- \+/\- *lemma* measurable.const_smul
- \+/\- *lemma* ae_measurable.const_smul'
- \+/\- *lemma* ae_measurable.const_smul
- \+/\- *lemma* list.ae_measurable_prod'
- \+/\- *lemma* list.ae_measurable_prod
- \+/\- *lemma* multiset.ae_measurable_prod'
- \+/\- *lemma* multiset.ae_measurable_prod
- \+/\- *lemma* finset.measurable_prod'
- \+/\- *lemma* finset.measurable_prod
- \+/\- *lemma* finset.ae_measurable_prod'
- \+/\- *lemma* finset.ae_measurable_prod



## [2022-01-08 14:24:00](https://github.com/leanprover-community/mathlib/commit/2231173)
feat(group_theory/commuting_probability): New file ([#11243](https://github.com/leanprover-community/mathlib/pull/11243))
This PR introduces commuting probabilities of finite groups.
#### Estimated changes
Created src/group_theory/commuting_probability.lean
- \+ *lemma* comm_prob_def
- \+ *lemma* comm_prob_pos
- \+ *lemma* comm_prob_le_one
- \+ *lemma* comm_prob_eq_one_iff
- \+ *lemma* card_comm_eq_card_conj_classes_mul_card
- \+ *lemma* comm_prob_def'
- \+ *def* comm_prob



## [2022-01-08 07:22:54](https://github.com/leanprover-community/mathlib/commit/07f9b8e)
feat(data/sum/order): Linear and disjoint sums of orders ([#11157](https://github.com/leanprover-community/mathlib/pull/11157))
This defines the disjoint sum of two orders on `α ⊕ β` and the linear (aka lexicographic) sum of two orders on `α ⊕ₗ β` (a type synonym of `α ⊕ β`) in a new file `data.sum.order`.
#### Estimated changes
Modified src/algebra/lie/classical.lean

Modified src/data/equiv/basic.lean
- \+ *lemma* sum_assoc_apply_inl_inl
- \+ *lemma* sum_assoc_apply_inl_inr
- \+ *lemma* sum_assoc_apply_inr
- \+ *lemma* sum_assoc_symm_apply_inl
- \+ *lemma* sum_assoc_symm_apply_inr_inl
- \+ *lemma* sum_assoc_symm_apply_inr_inr
- \- *theorem* sum_assoc_apply_in1
- \- *theorem* sum_assoc_apply_in2
- \- *theorem* sum_assoc_apply_in3
- \+/\- *def* sum_comm
- \+/\- *def* sum_assoc
- \+/\- *def* sum_comm
- \+/\- *def* sum_assoc

Modified src/data/sum/basic.lean
- \+ *lemma* get_left_eq_none_iff
- \+ *lemma* get_right_eq_none_iff
- \+ *lemma* lift_rel_inl_inl
- \+ *lemma* not_lift_rel_inl_inr
- \+ *lemma* not_lift_rel_inr_inl
- \+ *lemma* lift_rel_inr_inr
- \+ *lemma* lift_rel.mono
- \+ *lemma* lift_rel.mono_left
- \+ *lemma* lift_rel.mono_right
- \+ *lemma* lift_rel_swap_iff

Created src/data/sum/order.lean
- \+ *lemma* lift_rel.refl
- \+ *lemma* lift_rel.trans
- \+ *lemma* le_def
- \+ *lemma* lt_def
- \+ *lemma* inl_le_inl_iff
- \+ *lemma* inr_le_inr_iff
- \+ *lemma* inl_lt_inl_iff
- \+ *lemma* inr_lt_inr_iff
- \+ *lemma* not_inl_le_inr
- \+ *lemma* not_inl_lt_inr
- \+ *lemma* not_inr_le_inl
- \+ *lemma* not_inr_lt_inl
- \+ *lemma* inl_mono
- \+ *lemma* inr_mono
- \+ *lemma* inl_strict_mono
- \+ *lemma* inr_strict_mono
- \+ *lemma* no_bot_order_iff
- \+ *lemma* no_top_order_iff
- \+ *lemma* densely_ordered_iff
- \+ *lemma* swap_le_swap_iff
- \+ *lemma* swap_lt_swap_iff
- \+ *lemma* to_lex_le_to_lex
- \+ *lemma* to_lex_lt_to_lex
- \+ *lemma* le_def
- \+ *lemma* lt_def
- \+ *lemma* inl_le_inl_iff
- \+ *lemma* inr_le_inr_iff
- \+ *lemma* inl_lt_inl_iff
- \+ *lemma* inr_lt_inr_iff
- \+ *lemma* inl_le_inr
- \+ *lemma* inl_lt_inr
- \+ *lemma* not_inr_le_inl
- \+ *lemma* not_inr_lt_inl
- \+ *lemma* to_lex_mono
- \+ *lemma* to_lex_strict_mono
- \+ *lemma* inl_mono
- \+ *lemma* inr_mono
- \+ *lemma* inl_strict_mono
- \+ *lemma* inr_strict_mono
- \+ *lemma* inl_bot
- \+ *lemma* inr_top
- \+ *lemma* sum_comm_symm
- \+ *lemma* sum_assoc_apply_inl_inl
- \+ *lemma* sum_assoc_apply_inl_inr
- \+ *lemma* sum_assoc_apply_inr
- \+ *lemma* sum_assoc_symm_apply_inl
- \+ *lemma* sum_assoc_symm_apply_inr_inl
- \+ *lemma* sum_assoc_symm_apply_inr_inr
- \+ *lemma* sum_dual_distrib_inl
- \+ *lemma* sum_dual_distrib_inr
- \+ *lemma* sum_dual_distrib_symm_inl
- \+ *lemma* sum_dual_distrib_symm_inr
- \+ *lemma* sum_lex_assoc_apply_inl_inl
- \+ *lemma* sum_lex_assoc_apply_inl_inr
- \+ *lemma* sum_lex_assoc_apply_inr
- \+ *lemma* sum_lex_assoc_symm_apply_inl
- \+ *lemma* sum_lex_assoc_symm_apply_inr_inl
- \+ *lemma* sum_lex_assoc_symm_apply_inr_inr
- \+ *lemma* sum_lex_dual_antidistrib_inl
- \+ *lemma* sum_lex_dual_antidistrib_inr
- \+ *lemma* sum_lex_dual_antidistrib_symm_inl
- \+ *lemma* sum_lex_dual_antidistrib_symm_inr
- \+ *def* sum_comm
- \+ *def* sum_assoc
- \+ *def* sum_dual_distrib
- \+ *def* sum_lex_assoc
- \+ *def* sum_lex_dual_antidistrib

Modified src/logic/basic.lean
- \+ *lemma* or.imp3

Modified src/order/lexicographic.lean
- \+/\- *def* to_lex
- \+/\- *def* of_lex
- \+/\- *def* to_lex
- \+/\- *def* of_lex

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
- \+ *lemma* inf_edist_lt_iff
- \+ *lemma* inf_dist_lt_iff
- \- *lemma* exists_edist_lt_of_inf_edist_lt
- \- *lemma* exists_dist_lt_of_inf_dist_lt



## [2022-01-07 18:21:53](https://github.com/leanprover-community/mathlib/commit/5cbfddd)
feat(data/finset/sym): Symmetric powers of a finset ([#11142](https://github.com/leanprover-community/mathlib/pull/11142))
This defines `finset.sym` and `finset.sym2`, which are the `finset` analogs of `sym` and `sym2`, in a new file `data.finset.sym`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* disjoint_filter_filter_neg

Modified src/data/finset/prod.lean
- \+ *lemma* product_eq_empty
- \+ *lemma* diag_union_off_diag
- \+ *lemma* disjoint_diag_off_diag

Created src/data/finset/sym.lean
- \+ *lemma* is_diag_mk_of_mem_diag
- \+ *lemma* not_is_diag_mk_of_mem_off_diag
- \+ *lemma* mem_sym2_iff
- \+ *lemma* mk_mem_sym2_iff
- \+ *lemma* sym2_empty
- \+ *lemma* sym2_eq_empty
- \+ *lemma* sym2_nonempty
- \+ *lemma* sym2_univ
- \+ *lemma* sym2_singleton
- \+ *lemma* diag_mem_sym2_iff
- \+ *lemma* sym2_mono
- \+ *lemma* image_diag_union_image_off_diag
- \+ *lemma* sym_zero
- \+ *lemma* sym_succ
- \+ *lemma* mem_sym_iff
- \+ *lemma* sym_empty
- \+ *lemma* repeat_mem_sym
- \+ *lemma* sym_singleton
- \+ *lemma* eq_empty_of_sym_eq_empty
- \+ *lemma* sym_eq_empty
- \+ *lemma* sym_nonempty
- \+ *lemma* sym_univ
- \+ *lemma* sym_mono
- \+ *lemma* sym_inter
- \+ *lemma* sym_union

Modified src/data/sym/basic.lean
- \+ *lemma* coe_repeat
- \+ *lemma* mem_repeat
- \+ *lemma* eq_repeat_iff

Modified src/data/sym/card.lean
- \+/\- *lemma* card_image_diag
- \+ *lemma* _root_.finset.card_sym2
- \+/\- *lemma* card_image_diag

Modified src/data/sym/sym2.lean
- \+/\- *lemma* mem_iff
- \+ *lemma* out_fst_mem
- \+ *lemma* out_snd_mem
- \+ *lemma* ball
- \+/\- *lemma* mem_iff



## [2022-01-07 18:21:52](https://github.com/leanprover-community/mathlib/commit/a8d37c1)
feat(data/nat/factorization): Defining `factorization` ([#10540](https://github.com/leanprover-community/mathlib/pull/10540))
Defining `factorization` as a `finsupp`, as discussed in
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Prime.20factorizations
and 
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Proof.20of.20Euler's.20product.20formula.20for.20totient
This is the first of a series of PRs to build up the infrastructure needed for the proof of Euler's product formula for the totient function.
#### Estimated changes
Created src/data/nat/factorization.lean
- \+ *lemma* factorization_eq_count
- \+ *lemma* factorization_inj
- \+ *lemma* factorization_zero
- \+ *lemma* factorization_one
- \+ *lemma* support_factorization
- \+ *lemma* factor_iff_mem_factorization
- \+ *lemma* factorization_eq_zero_iff
- \+ *lemma* factorization_mul
- \+ *lemma* factorization_pow
- \+ *lemma* prime.factorization
- \+ *lemma* prime.factorization_pow

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* factorization_eq_count
- \+ *lemma* factorization_zero
- \+ *lemma* factorization_one
- \+ *lemma* support_factorization
- \+ *lemma* factorization_mul
- \+ *lemma* factorization_pow
- \+ *lemma* associated_of_factorization_eq



## [2022-01-07 18:21:50](https://github.com/leanprover-community/mathlib/commit/3b02ad7)
feat(topology/homotopy/equiv): Add homotopy equivalences between topological spaces ([#10529](https://github.com/leanprover-community/mathlib/pull/10529))
#### Estimated changes
Modified src/topology/continuous_function/basic.lean
- \+ *lemma* id_comp
- \+ *lemma* comp_id

Created src/topology/homotopy/equiv.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* continuous
- \+ *lemma* coe_to_homotopy_equiv
- \+ *lemma* coe_inv_fun
- \+ *lemma* symm_trans
- \+ *lemma* refl_to_homotopy_equiv
- \+ *lemma* symm_to_homotopy_equiv
- \+ *lemma* trans_to_homotopy_equiv
- \+ *def* to_homotopy_equiv
- \+ *def* symm
- \+ *def* simps.apply
- \+ *def* simps.symm_apply
- \+ *def* refl
- \+ *def* trans



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

Created src/category_theory/concrete_category/elementwise.lean

Modified src/category_theory/limits/concrete_category.lean

Modified src/category_theory/limits/shapes/concrete_category.lean

Modified src/logic/function/basic.lean
- \+ *lemma* inv_image.equivalence

Created src/topology/gluing.lean
- \+ *lemma* π_surjective
- \+ *lemma* is_open_iff
- \+ *lemma* ι_jointly_surjective
- \+ *lemma* rel_equiv
- \+ *lemma* eqv_gen_of_π_eq
- \+ *lemma* ι_eq_iff_rel
- \+ *lemma* ι_injective
- \+ *lemma* image_inter
- \+ *lemma* preimage_range
- \+ *lemma* preimage_image_eq_image
- \+ *lemma* preimage_image_eq_image'
- \+ *lemma* open_image_open
- \+ *lemma* ι_open_embedding
- \+ *lemma* mk_core.t_inv
- \+ *lemma* ι_from_open_subsets_glue
- \+ *lemma* from_open_subsets_glue_injective
- \+ *lemma* from_open_subsets_glue_is_open_map
- \+ *lemma* from_open_subsets_glue_open_embedding
- \+ *lemma* range_from_open_subsets_glue
- \+ *def* rel
- \+ *def* mk_core.t'
- \+ *def* mk'
- \+ *def* of_open_subsets
- \+ *def* from_open_subsets_glue
- \+ *def* open_cover_glue_homeo



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
- \+ *lemma* mul_support_nonempty_iff

Modified src/data/equiv/denumerable.lean
- \+ *lemma* of_nat_range
- \+ *lemma* coe_comp_of_nat_range

Modified src/data/set/countable.lean

Modified src/data/set/finite.lean
- \+ *lemma* finite_union
- \+ *lemma* finite.of_diff
- \+ *lemma* infinite_union
- \- *lemma* finite.union_iff
- \- *lemma* finite.diff

Modified src/number_theory/modular.lean

Modified src/order/order_iso_nat.lean
- \+ *lemma* coe_order_embedding_of_set
- \+/\- *lemma* order_embedding_of_set_apply
- \+/\- *lemma* order_embedding_of_set_apply
- \+ *theorem* exists_subseq_of_forall_mem_union

Modified src/ring_theory/hahn_series.lean
- \+ *lemma* coeff_injective
- \+ *lemma* coeff_inj
- \+/\- *lemma* zero_coeff
- \+ *lemma* coeff_fun_eq_zero_iff
- \+/\- *lemma* support_zero
- \+/\- *lemma* support_nonempty_iff
- \+ *lemma* support_eq_empty_iff
- \+/\- *lemma* zero_coeff
- \+/\- *lemma* support_zero
- \+/\- *lemma* support_nonempty_iff
- \+/\- *def* support
- \+/\- *def* support



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
- \- *def* free_non_unital_non_assoc_algebra

Modified src/algebra/lie/free.lean
- \+/\- *lemma* rel.add_left
- \+/\- *lemma* rel.neg
- \+ *lemma* rel.sub_left
- \+ *lemma* rel.sub_right
- \+ *lemma* rel.smul_of_tower
- \+/\- *lemma* rel.add_left
- \+/\- *lemma* rel.neg

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
- \+ *lemma* nat_degree_pow
- \+ *lemma* nat_degree_pow_X_add_C



## [2022-01-06 14:41:11](https://github.com/leanprover-community/mathlib/commit/9b39ab2)
feat(algebra/group/freiman): Freiman homomorphisms ([#10497](https://github.com/leanprover-community/mathlib/pull/10497))
This defines Freiman homomorphisms, which are maps preserving products of `n` elements (but only in the codomain. One can never get back to the domain).
This is useful in additive combinatorics.
#### Estimated changes
Created src/algebra/group/freiman.lean
- \+ *lemma* map_prod_eq_map_prod
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_mk
- \+ *lemma* mk_coe
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* cancel_right
- \+ *lemma* cancel_right_on
- \+ *lemma* cancel_left_on
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* const_apply
- \+ *lemma* const_comp
- \+ *lemma* one_apply
- \+ *lemma* one_comp
- \+ *lemma* mul_apply
- \+ *lemma* mul_comp
- \+ *lemma* inv_apply
- \+ *lemma* inv_comp
- \+ *lemma* div_apply
- \+ *lemma* div_comp
- \+ *lemma* monoid_hom.to_freiman_hom_coe
- \+ *lemma* monoid_hom.to_freiman_hom_injective
- \+ *lemma* map_prod_eq_map_prod_of_le
- \+ *lemma* freiman_hom.to_freiman_hom_coe
- \+ *lemma* freiman_hom.to_freiman_hom_injective
- \+ *def* const
- \+ *def* monoid_hom.to_freiman_hom
- \+ *def* freiman_hom.to_freiman_hom
- \+ *def* freiman_hom.freiman_hom_class_of_le

Modified src/data/fun_like.lean



## [2022-01-06 12:39:56](https://github.com/leanprover-community/mathlib/commit/d2428fa)
feat(ring_theory/localization): Localization is the localization of localization. ([#11145](https://github.com/leanprover-community/mathlib/pull/11145))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* exists_image_iff

Modified src/ring_theory/localization.lean
- \+ *lemma* localization_is_scalar_tower_of_submonoid_le
- \+ *lemma* is_localization_of_submonoid_le
- \+ *lemma* is_localization_of_is_exists_mul_mem
- \+ *def* localization_algebra_of_submonoid_le



## [2022-01-06 10:39:24](https://github.com/leanprover-community/mathlib/commit/54c2567)
feat(category_theory/sites): The pushforward pullback adjunction ([#11273](https://github.com/leanprover-community/mathlib/pull/11273))
#### Estimated changes
Modified src/category_theory/sites/cover_preserving.lean
- \+ *lemma* compatible_preserving_of_flat
- \+ *def* sites.pushforward
- \+ *def* sites.pullback_pushforward_adjunction



## [2022-01-06 10:39:23](https://github.com/leanprover-community/mathlib/commit/7af5e86)
feat(algebra/big_operators/multiset): Multiset product under some usual maps ([#10907](https://github.com/leanprover-community/mathlib/pull/10907))
Product of the image of a multiset under `λ a, (f a)⁻¹`, `λ a, f a / g a`, `λ a, f a ^ n` (for `n` in `ℕ` and `ℤ`).
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* prod_inv_distrib
- \+/\- *lemma* prod_inv_distrib

Modified src/algebra/big_operators/multiset.lean
- \+/\- *lemma* pow_count
- \+/\- *lemma* prod_hom
- \+ *lemma* prod_hom'
- \+ *lemma* prod_hom₂
- \+/\- *lemma* prod_hom_rel
- \+/\- *lemma* prod_map_one
- \+/\- *lemma* prod_map_mul
- \+ *lemma* prod_map_pow
- \+ *lemma* prod_map_inv'
- \+ *lemma* prod_map_div
- \+ *lemma* prod_map_zpow
- \+ *lemma* prod_map_inv₀
- \+ *lemma* prod_map_div₀
- \+ *lemma* prod_map_zpow₀
- \+/\- *lemma* pow_count
- \+/\- *lemma* prod_map_one
- \+/\- *lemma* prod_map_mul
- \+/\- *lemma* prod_hom
- \+/\- *lemma* prod_hom_rel

Modified src/algebra/group/prod.lean
- \+ *def* mul_mul_hom
- \+ *def* mul_monoid_hom
- \+ *def* mul_monoid_with_zero_hom
- \+ *def* div_monoid_hom
- \+ *def* div_monoid_with_zero_hom

Modified src/algebra/group_with_zero/basic.lean
- \+ *def* inv_monoid_with_zero_hom

Modified src/algebra/smul_with_zero.lean
- \+ *def* smul_monoid_with_zero_hom

Modified src/data/list/basic.lean
- \+ *lemma* foldl_hom₂
- \+ *lemma* foldr_hom₂

Modified src/data/list/big_operators.lean
- \+/\- *lemma* prod_hom_rel
- \+ *lemma* prod_hom₂
- \+/\- *lemma* prod_hom_rel

Modified src/group_theory/group_action/prod.lean
- \+ *def* smul_mul_hom
- \+ *def* smul_monoid_hom



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
- \+ *lemma* coe_def
- \+/\- *lemma* coeff_coe
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+ *lemma* coe_injective
- \+ *lemma* coe_inj
- \+ *lemma* coe_eq_zero_iff
- \+ *lemma* coe_eq_one_iff
- \+ *lemma* coe_to_mv_power_series.ring_hom_apply
- \+ *lemma* algebra_map_apply
- \+ *lemma* coe_to_mv_power_series.alg_hom_apply
- \+ *lemma* algebra_map_apply'
- \+ *lemma* algebra_map_apply''
- \+ *lemma* map_C
- \+ *lemma* map_X
- \+ *lemma* coe_def
- \+/\- *lemma* coeff_coe
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+ *lemma* coe_injective
- \+ *lemma* coe_inj
- \+ *lemma* coe_eq_zero_iff
- \+ *lemma* coe_eq_one_iff
- \+ *lemma* coe_to_power_series.ring_hom_apply
- \+ *lemma* coe_to_power_series.alg_hom_apply
- \+ *lemma* algebra_map_apply'
- \+ *lemma* algebra_map_apply''
- \+/\- *lemma* coeff_coe
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coeff_coe
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+ *def* coe_to_mv_power_series.alg_hom
- \+/\- *def* coe_to_power_series.ring_hom
- \+ *def* coe_to_power_series.alg_hom
- \+/\- *def* coe_to_power_series.ring_hom



## [2022-01-06 07:55:40](https://github.com/leanprover-community/mathlib/commit/6952172)
feat(data/nat/digits): digits_len ([#11187](https://github.com/leanprover-community/mathlib/pull/11187))
Via a new `data.nat.log` import.
Also unprivate `digits_eq_cons_digits_div`.
The file needs a refactor to make the names more mathlib-like,
otherwise I would have named it `length_digits`.
#### Estimated changes
Modified src/data/nat/digits.lean
- \+ *lemma* digits_eq_cons_digits_div
- \+ *lemma* digits_len



## [2022-01-06 07:05:28](https://github.com/leanprover-community/mathlib/commit/b3260f3)
feat(measure_theory/constructions/borel_space): new lemma tendsto_measure_cthickening ([#11009](https://github.com/leanprover-community/mathlib/pull/11009))
Prove that, when `r` tends to `0`, the measure of the `r`-thickening of a set `s` tends to the measure of `s`.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* tendsto_measure_cthickening
- \+ *lemma* tendsto_measure_cthickening_of_is_closed
- \+ *lemma* tendsto_measure_cthickening_of_is_compact

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* tendsto_measure_bInter_gt



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
- \+ *lemma* has_basis_compact_convergence_uniformity_of_compact
- \+ *lemma* tendsto_iff_tendsto_uniformly



## [2022-01-05 23:45:32](https://github.com/leanprover-community/mathlib/commit/a7611b2)
chore(*): notation for `units` ([#11236](https://github.com/leanprover-community/mathlib/pull/11236))
#### Estimated changes
Modified counterexamples/direct_sum_is_internal.lean
- \+/\- *lemma* units_int.one_ne_neg_one
- \+/\- *lemma* units_int.one_ne_neg_one
- \+/\- *def* with_sign
- \+/\- *def* with_sign

Modified src/algebra/algebra/basic.lean

Modified src/algebra/algebra/spectrum.lean
- \+/\- *lemma* smul_mem_smul_iff
- \+/\- *lemma* smul_mem_smul_iff
- \+/\- *theorem* unit_smul_eq_smul
- \+/\- *theorem* unit_mem_mul_iff_mem_swap_mul
- \+/\- *theorem* unit_smul_eq_smul
- \+/\- *theorem* unit_mem_mul_iff_mem_swap_mul

Modified src/algebra/associated.lean
- \+/\- *lemma* units_eq_one
- \+/\- *lemma* units_eq_one
- \+/\- *theorem* unit_associated_one
- \+/\- *theorem* units_eq_one
- \+/\- *theorem* coe_unit_eq_one
- \+/\- *theorem* unit_associated_one
- \+/\- *theorem* units_eq_one
- \+/\- *theorem* coe_unit_eq_one
- \+/\- *def* associated
- \+/\- *def* associated

Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* units.coe_prod
- \+/\- *lemma* units.coe_prod

Modified src/algebra/divisibility.lean

Modified src/algebra/field/basic.lean
- \+/\- *lemma* map_units_inv
- \+/\- *lemma* map_units_inv

Modified src/algebra/gcd_monoid/basic.lean
- \+/\- *lemma* normalize_coe_units
- \+/\- *lemma* normalize_coe_units
- \+/\- *theorem* exists_eq_pow_of_mul_eq_pow
- \+/\- *theorem* lcm_units_coe_left
- \+/\- *theorem* lcm_units_coe_right
- \+/\- *theorem* exists_eq_pow_of_mul_eq_pow
- \+/\- *theorem* lcm_units_coe_left
- \+/\- *theorem* lcm_units_coe_right

Modified src/algebra/group/commute.lean

Modified src/algebra/group/conj.lean
- \+/\- *def* is_conj
- \+/\- *def* is_conj

Modified src/algebra/group/opposite.lean
- \+/\- *lemma* units.coe_unop_op_equiv
- \+/\- *lemma* units.coe_op_equiv_symm
- \+/\- *lemma* units.coe_unop_op_equiv
- \+/\- *lemma* units.coe_op_equiv_symm
- \+/\- *def* units.op_equiv
- \+/\- *def* units.op_equiv

Modified src/algebra/group/prod.lean
- \+/\- *def* prod_units
- \+/\- *def* embed_product
- \+/\- *def* prod_units
- \+/\- *def* embed_product

Modified src/algebra/group/semiconj.lean
- \+/\- *lemma* units_inv_right
- \+/\- *lemma* units_inv_right_iff
- \+/\- *lemma* units_inv_symm_left
- \+/\- *lemma* units_inv_symm_left_iff
- \+/\- *lemma* units.mk_semiconj_by
- \+/\- *lemma* units_inv_right
- \+/\- *lemma* units_inv_right_iff
- \+/\- *lemma* units_inv_symm_left
- \+/\- *lemma* units_inv_symm_left_iff
- \+/\- *lemma* units.mk_semiconj_by
- \+/\- *theorem* units_coe
- \+/\- *theorem* units_of_coe
- \+/\- *theorem* units_coe_iff
- \+/\- *theorem* units_coe
- \+/\- *theorem* units_of_coe
- \+/\- *theorem* units_coe_iff

Modified src/algebra/group/units.lean
- \+/\- *lemma* copy_eq
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_eq_one
- \+/\- *lemma* inv_eq_coe_inv
- \+/\- *lemma* inv_mul_of_eq
- \+/\- *lemma* mul_inv_of_eq
- \+/\- *lemma* mul_inv_cancel_left
- \+/\- *lemma* inv_mul_cancel_left
- \+/\- *lemma* mul_inv_cancel_right
- \+/\- *lemma* inv_mul_cancel_right
- \+/\- *lemma* inv_eq_of_mul_eq_one
- \+/\- *lemma* inv_unique
- \+/\- *lemma* copy_eq
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_eq_one
- \+/\- *lemma* inv_eq_coe_inv
- \+/\- *lemma* inv_mul_of_eq
- \+/\- *lemma* mul_inv_of_eq
- \+/\- *lemma* mul_inv_cancel_left
- \+/\- *lemma* inv_mul_cancel_left
- \+/\- *lemma* mul_inv_cancel_right
- \+/\- *lemma* inv_mul_cancel_right
- \+/\- *lemma* inv_eq_of_mul_eq_one
- \+/\- *lemma* inv_unique
- \+/\- *theorem* eq_iff
- \+/\- *theorem* ext_iff
- \+/\- *theorem* mk_coe
- \+/\- *theorem* mul_right_inj
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* divp_self
- \+/\- *theorem* divp_assoc
- \+/\- *theorem* divp_inv
- \+/\- *theorem* divp_mul_cancel
- \+/\- *theorem* mul_divp_cancel
- \+/\- *theorem* divp_left_inj
- \+/\- *theorem* divp_divp_eq_divp_mul
- \+/\- *theorem* divp_eq_iff_mul_eq
- \+/\- *theorem* divp_eq_one_iff_eq
- \+/\- *theorem* one_divp
- \+/\- *theorem* divp_eq_divp_iff
- \+/\- *theorem* divp_mul_divp
- \+/\- *theorem* units.is_unit_mul_units
- \+/\- *theorem* units.is_unit_units_mul
- \+/\- *theorem* eq_iff
- \+/\- *theorem* ext_iff
- \+/\- *theorem* mk_coe
- \+/\- *theorem* mul_right_inj
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* divp_self
- \+/\- *theorem* divp_assoc
- \+/\- *theorem* divp_inv
- \+/\- *theorem* divp_mul_cancel
- \+/\- *theorem* mul_divp_cancel
- \+/\- *theorem* divp_left_inj
- \+/\- *theorem* divp_divp_eq_divp_mul
- \+/\- *theorem* divp_eq_iff_mul_eq
- \+/\- *theorem* divp_eq_one_iff_eq
- \+/\- *theorem* one_divp
- \+/\- *theorem* divp_eq_divp_iff
- \+/\- *theorem* divp_mul_divp
- \+/\- *theorem* units.is_unit_mul_units
- \+/\- *theorem* units.is_unit_units_mul
- \+/\- *def* simps.coe
- \+/\- *def* simps.coe_inv
- \+/\- *def* copy
- \+/\- *def* divp
- \+/\- *def* is_unit
- \+/\- *def* simps.coe
- \+/\- *def* simps.coe_inv
- \+/\- *def* copy
- \+/\- *def* divp
- \+/\- *def* is_unit

Modified src/algebra/group/units_hom.lean
- \+/\- *lemma* coe_map
- \+/\- *lemma* coe_map_inv
- \+/\- *lemma* map_id
- \+/\- *lemma* coe_hom_apply
- \+/\- *lemma* coe_lift_right
- \+/\- *lemma* mul_lift_right_inv
- \+/\- *lemma* lift_right_inv_mul
- \+/\- *lemma* coe_map
- \+/\- *lemma* coe_map_inv
- \+/\- *lemma* map_id
- \+/\- *lemma* coe_hom_apply
- \+/\- *lemma* coe_lift_right
- \+/\- *lemma* mul_lift_right_inv
- \+/\- *lemma* lift_right_inv_mul
- \+/\- *def* map
- \+/\- *def* coe_hom
- \+/\- *def* lift_right
- \+/\- *def* to_hom_units
- \+/\- *def* map
- \+/\- *def* coe_hom
- \+/\- *def* lift_right
- \+/\- *def* to_hom_units

Modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* units.coe_pow
- \+/\- *lemma* units.coe_zpow
- \+/\- *lemma* units_sq
- \+/\- *lemma* units_pow_eq_pow_mod_two
- \+/\- *lemma* units_zpow_right
- \+/\- *lemma* units_zpow_right
- \+/\- *lemma* units_zpow_left
- \+/\- *lemma* conj_pow
- \+/\- *lemma* conj_pow'
- \+/\- *lemma* units.coe_pow
- \+/\- *lemma* units.coe_zpow
- \+/\- *lemma* units_sq
- \+/\- *lemma* units_pow_eq_pow_mod_two
- \+/\- *lemma* units_zpow_right
- \+/\- *lemma* units_zpow_right
- \+/\- *lemma* units_zpow_left
- \+/\- *lemma* conj_pow
- \+/\- *lemma* conj_pow'

Modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* ne_zero
- \+/\- *lemma* mul_left_eq_zero
- \+/\- *lemma* mul_right_eq_zero
- \+/\- *lemma* inverse_unit
- \+/\- *lemma* mk0_coe
- \+/\- *lemma* coe_inv'
- \+/\- *lemma* mul_inv'
- \+/\- *lemma* inv_mul'
- \+/\- *lemma* exists_iff_ne_zero
- \+/\- *lemma* ne_zero
- \+/\- *lemma* mul_left_eq_zero
- \+/\- *lemma* mul_right_eq_zero
- \+/\- *lemma* inverse_unit
- \+/\- *lemma* mk0_coe
- \+/\- *lemma* coe_inv'
- \+/\- *lemma* mul_inv'
- \+/\- *lemma* inv_mul'
- \+/\- *lemma* exists_iff_ne_zero
- \+/\- *theorem* divp_eq_div
- \+/\- *theorem* divp_eq_div
- \+/\- *def* mk0
- \+/\- *def* mk0

Modified src/algebra/group_with_zero/power.lean
- \+/\- *lemma* units.coe_zpow₀
- \+/\- *lemma* units.coe_zpow₀

Modified src/algebra/invertible.lean
- \+/\- *lemma* inv_of_units
- \+/\- *lemma* inv_of_units
- \+/\- *def* unit_of_invertible
- \+/\- *def* units.invertible
- \+/\- *def* unit_of_invertible
- \+/\- *def* units.invertible

Modified src/algebra/lie/skew_adjoint.lean
- \+/\- *lemma* mem_skew_adjoint_matrices_lie_subalgebra_unit_smul
- \+/\- *lemma* mem_skew_adjoint_matrices_lie_subalgebra_unit_smul

Modified src/algebra/module/basic.lean
- \+/\- *theorem* units.neg_smul
- \+/\- *theorem* units.neg_smul

Modified src/algebra/module/linear_map.lean

Modified src/algebra/order/group.lean

Modified src/algebra/order/monoid.lean
- \+/\- *theorem* coe_le_coe
- \+/\- *theorem* coe_lt_coe
- \+/\- *theorem* max_coe
- \+/\- *theorem* min_coe
- \+/\- *theorem* coe_le_coe
- \+/\- *theorem* coe_lt_coe
- \+/\- *theorem* max_coe
- \+/\- *theorem* min_coe

Modified src/algebra/order/ring.lean
- \+/\- *lemma* units.inv_pos
- \+/\- *lemma* units.inv_neg
- \+/\- *lemma* units.inv_pos
- \+/\- *lemma* units.inv_neg

Modified src/algebra/order/with_zero.lean
- \+/\- *lemma* units.zero_lt
- \+/\- *lemma* units.zero_lt

Modified src/algebra/regular/basic.lean
- \+/\- *lemma* units.is_regular
- \+/\- *lemma* units.is_regular

Modified src/algebra/regular/smul.lean
- \+/\- *lemma* units.is_smul_regular
- \+/\- *lemma* units.is_smul_regular

Modified src/algebra/ring/basic.lean
- \+/\- *lemma* units.inv_eq_self_iff
- \+/\- *lemma* units.inv_eq_self_iff

Modified src/algebra/star/basic.lean
- \+/\- *lemma* coe_star
- \+/\- *lemma* coe_star_inv
- \+/\- *lemma* coe_star
- \+/\- *lemma* coe_star_inv

Modified src/algebraic_geometry/EllipticCurve.lean

Modified src/analysis/asymptotics/asymptotics.lean
- \+/\- *theorem* is_O_with_self_const_mul'
- \+/\- *theorem* is_O_with.const_mul_right'
- \+/\- *theorem* is_O_with_self_const_mul'
- \+/\- *theorem* is_O_with.const_mul_right'

Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* has_fderiv_at_ring_inverse
- \+/\- *lemma* differentiable_at_inverse
- \+/\- *lemma* fderiv_inverse
- \+/\- *lemma* has_fderiv_at_ring_inverse
- \+/\- *lemma* differentiable_at_inverse
- \+/\- *lemma* fderiv_inverse

Modified src/analysis/calculus/times_cont_diff.lean
- \+/\- *lemma* times_cont_diff_at_ring_inverse
- \+/\- *lemma* times_cont_diff_at_ring_inverse

Modified src/analysis/normed_space/add_torsor_bases.lean

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* units.norm_pos
- \+/\- *lemma* units.norm_pos

Modified src/analysis/normed_space/int.lean
- \+/\- *lemma* nnnorm_coe_units
- \+/\- *lemma* norm_coe_units
- \+/\- *lemma* nnnorm_coe_units
- \+/\- *lemma* norm_coe_units

Modified src/analysis/normed_space/units.lean
- \+/\- *lemma* inverse_add
- \+/\- *lemma* inverse_add_nth_order
- \+/\- *lemma* inverse_add_norm
- \+/\- *lemma* inverse_add_norm_diff_nth_order
- \+/\- *lemma* inverse_add_norm_diff_first_order
- \+/\- *lemma* inverse_add_norm_diff_second_order
- \+/\- *lemma* inverse_continuous_at
- \+/\- *lemma* is_open_map_coe
- \+/\- *lemma* open_embedding_coe
- \+/\- *lemma* inverse_add
- \+/\- *lemma* inverse_add_nth_order
- \+/\- *lemma* inverse_add_norm
- \+/\- *lemma* inverse_add_norm_diff_nth_order
- \+/\- *lemma* inverse_add_norm_diff_first_order
- \+/\- *lemma* inverse_add_norm_diff_second_order
- \+/\- *lemma* inverse_continuous_at
- \+/\- *lemma* is_open_map_coe
- \+/\- *lemma* open_embedding_coe
- \+/\- *def* one_sub
- \+/\- *def* add
- \+/\- *def* unit_of_nearby
- \+/\- *def* one_sub
- \+/\- *def* add
- \+/\- *def* unit_of_nearby

Modified src/category_theory/endomorphism.lean
- \+/\- *def* units_End_equiv_Aut
- \+/\- *def* units_End_equiv_Aut

Modified src/category_theory/single_obj.lean
- \+/\- *lemma* to_Aut_hom
- \+/\- *lemma* to_Aut_inv
- \+/\- *lemma* to_Aut_hom
- \+/\- *lemma* to_Aut_inv
- \+/\- *def* to_Aut
- \+/\- *def* to_Aut

Modified src/data/equiv/mul_add.lean
- \+/\- *lemma* coe_inv
- \+/\- *lemma* mul_left_symm
- \+/\- *lemma* mul_left_bijective
- \+/\- *lemma* mul_right_symm
- \+/\- *lemma* mul_right_bijective
- \+/\- *lemma* coe_inv
- \+/\- *lemma* mul_left_symm
- \+/\- *lemma* mul_left_bijective
- \+/\- *lemma* mul_right_symm
- \+/\- *lemma* mul_right_bijective
- \+/\- *def* to_units
- \+/\- *def* map_equiv
- \+/\- *def* mul_left
- \+/\- *def* mul_right
- \+/\- *def* to_units
- \+/\- *def* map_equiv
- \+/\- *def* mul_left
- \+/\- *def* mul_right

Modified src/data/fintype/basic.lean
- \+/\- *lemma* units_int.univ
- \+/\- *lemma* fintype.card_units
- \+/\- *lemma* units_int.univ
- \+/\- *lemma* fintype.card_units
- \+/\- *theorem* fintype.card_units_int
- \+/\- *theorem* fintype.card_units_int
- \+/\- *def* _root_.units_equiv_ne_zero
- \+/\- *def* _root_.units_equiv_ne_zero

Modified src/data/int/absolute_value.lean
- \+/\- *lemma* absolute_value.map_units_int
- \+/\- *lemma* absolute_value.map_units_int_cast
- \+/\- *lemma* absolute_value.map_units_int_smul
- \+/\- *lemma* absolute_value.map_units_int
- \+/\- *lemma* absolute_value.map_units_int_cast
- \+/\- *lemma* absolute_value.map_units_int_smul

Modified src/data/int/basic.lean
- \+/\- *lemma* units_inv_eq_self
- \+/\- *lemma* units_mul_self
- \+/\- *lemma* units_coe_mul_self
- \+/\- *lemma* units_inv_eq_self
- \+/\- *lemma* units_mul_self
- \+/\- *lemma* units_coe_mul_self
- \+/\- *theorem* units_nat_abs
- \+/\- *theorem* units_eq_one_or
- \+/\- *theorem* units_nat_abs
- \+/\- *theorem* units_eq_one_or

Modified src/data/matrix/rank.lean
- \+/\- *lemma* rank_unit
- \+/\- *lemma* rank_unit

Modified src/data/nat/basic.lean
- \+/\- *theorem* units_eq_one
- \+/\- *theorem* units_eq_one

Modified src/data/nat/totient.lean
- \+/\- *lemma* _root_.zmod.card_units_eq_totient
- \+/\- *lemma* card_units_zmod_lt_sub_one
- \+/\- *lemma* prime_iff_card_units
- \+/\- *lemma* _root_.zmod.card_units_eq_totient
- \+/\- *lemma* card_units_zmod_lt_sub_one
- \+/\- *lemma* prime_iff_card_units

Modified src/data/polynomial/field_division.lean
- \+/\- *lemma* coeff_inv_units
- \+/\- *lemma* coeff_inv_units

Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* degree_coe_units
- \+/\- *lemma* units_coeff_zero_smul
- \+/\- *lemma* nat_degree_coe_units
- \+/\- *lemma* coeff_coe_units_zero_ne_zero
- \+/\- *lemma* degree_coe_units
- \+/\- *lemma* units_coeff_zero_smul
- \+/\- *lemma* nat_degree_coe_units
- \+/\- *lemma* coeff_coe_units_zero_ne_zero

Modified src/data/real/ennreal.lean

Modified src/data/real/nnreal.lean

Modified src/data/real/sign.lean

Modified src/data/zmod/basic.lean
- \+/\- *lemma* val_coe_unit_coprime
- \+/\- *lemma* inv_coe_unit
- \+/\- *lemma* val_coe_unit_coprime
- \+/\- *lemma* inv_coe_unit
- \+/\- *def* unit_of_coprime
- \+/\- *def* unit_of_coprime

Modified src/deprecated/group.lean
- \+/\- *lemma* coe_map'
- \+/\- *lemma* coe_is_monoid_hom
- \+/\- *lemma* coe_map'
- \+/\- *lemma* coe_is_monoid_hom
- \+/\- *def* map'
- \+/\- *def* map'

Modified src/dynamics/circle/rotation_number/translation_number.lean
- \+/\- *lemma* units_coe
- \+/\- *lemma* units_inv_apply_apply
- \+/\- *lemma* units_apply_inv_apply
- \+/\- *lemma* coe_to_order_iso
- \+/\- *lemma* coe_to_order_iso_symm
- \+/\- *lemma* coe_to_order_iso_inv
- \+/\- *lemma* translation_number_units_inv
- \+/\- *lemma* translation_number_zpow
- \+/\- *lemma* translation_number_conj_eq
- \+/\- *lemma* translation_number_conj_eq'
- \+/\- *lemma* units_semiconj_of_translation_number_eq
- \+/\- *lemma* units_coe
- \+/\- *lemma* units_inv_apply_apply
- \+/\- *lemma* units_apply_inv_apply
- \+/\- *lemma* coe_to_order_iso
- \+/\- *lemma* coe_to_order_iso_symm
- \+/\- *lemma* coe_to_order_iso_inv
- \+/\- *lemma* translation_number_units_inv
- \+/\- *lemma* translation_number_zpow
- \+/\- *lemma* translation_number_conj_eq
- \+/\- *lemma* translation_number_conj_eq'
- \+/\- *lemma* units_semiconj_of_translation_number_eq
- \+/\- *def* to_order_iso
- \+/\- *def* translate
- \+/\- *def* to_order_iso
- \+/\- *def* translate

Modified src/field_theory/finite/basic.lean
- \+/\- *lemma* prod_univ_units_id_eq_neg_one
- \+/\- *lemma* sum_pow_units
- \+/\- *lemma* zmod.pow_totient
- \+/\- *lemma* card_units
- \+/\- *lemma* prod_univ_units_id_eq_neg_one
- \+/\- *lemma* sum_pow_units
- \+/\- *lemma* zmod.pow_totient
- \+/\- *lemma* card_units
- \+/\- *theorem* units_pow_card_sub_one_eq_one
- \+/\- *theorem* units_pow_card_sub_one_eq_one

Modified src/field_theory/separable.lean
- \+/\- *lemma* separable_X_pow_sub_C_unit
- \+/\- *lemma* separable_X_pow_sub_C_unit

Modified src/field_theory/splitting_field.lean

Modified src/geometry/manifold/instances/units_of_normed_algebra.lean
- \+/\- *lemma* chart_at_apply
- \+/\- *lemma* chart_at_source
- \+/\- *lemma* chart_at_apply
- \+/\- *lemma* chart_at_source

Modified src/group_theory/congruence.lean

Modified src/group_theory/group_action/units.lean
- \+/\- *lemma* smul_def
- \+/\- *lemma* smul_def

Modified src/group_theory/monoid_localization.lean

Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* order_of_units
- \+/\- *lemma* order_of_units

Modified src/group_theory/perm/cycle_type.lean

Modified src/group_theory/perm/sign.lean
- \+/\- *lemma* sign_surjective
- \+/\- *lemma* eq_sign_of_surjective_hom
- \+/\- *lemma* sign_surjective
- \+/\- *lemma* eq_sign_of_surjective_hom
- \+/\- *def* sign_aux
- \+/\- *def* sign_aux2
- \+/\- *def* sign_aux3
- \+/\- *def* sign
- \+/\- *def* sign_aux
- \+/\- *def* sign_aux2
- \+/\- *def* sign_aux3
- \+/\- *def* sign

Modified src/group_theory/specific_groups/quaternion.lean

Modified src/group_theory/submonoid/center.lean

Modified src/group_theory/submonoid/inverses.lean
- \+/\- *lemma* unit_mem_left_inv
- \+/\- *lemma* unit_mem_left_inv

Modified src/linear_algebra/affine_space/affine_equiv.lean
- \+/\- *lemma* coe_homothety_units_mul_hom_apply
- \+/\- *lemma* coe_homothety_units_mul_hom_apply_symm
- \+/\- *lemma* coe_homothety_units_mul_hom_apply
- \+/\- *lemma* coe_homothety_units_mul_hom_apply_symm
- \+/\- *def* equiv_units_affine_map
- \+/\- *def* homothety_units_mul_hom
- \+/\- *def* equiv_units_affine_map
- \+/\- *def* homothety_units_mul_hom

Modified src/linear_algebra/basic.lean
- \+/\- *def* smul_of_unit
- \+/\- *def* general_linear_group
- \+/\- *def* smul_of_unit
- \+/\- *def* general_linear_group

Modified src/linear_algebra/basis.lean
- \+/\- *lemma* units_smul_apply
- \+/\- *lemma* units_smul_apply
- \+/\- *def* units_smul
- \+/\- *def* units_smul

Modified src/linear_algebra/determinant.lean
- \+/\- *lemma* basis.det_units_smul
- \+/\- *lemma* basis.det_units_smul

Modified src/linear_algebra/eigenspace.lean

Modified src/linear_algebra/general_linear_group.lean
- \+/\- *def* det
- \+/\- *def* det

Modified src/linear_algebra/linear_independent.lean

Modified src/linear_algebra/matrix/basis.lean
- \+/\- *lemma* to_matrix_units_smul
- \+/\- *lemma* to_matrix_units_smul

Modified src/linear_algebra/matrix/determinant.lean
- \+/\- *lemma* det_units_conj
- \+/\- *lemma* det_units_conj'
- \+/\- *lemma* det_units_conj
- \+/\- *lemma* det_units_conj'

Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+/\- *lemma* inv_smul'
- \+/\- *lemma* inv_smul'
- \+/\- *def* unit_of_det_invertible
- \+/\- *def* unit_of_det_invertible

Modified src/linear_algebra/matrix/zpow.lean
- \+/\- *lemma* units.coe_inv''
- \+/\- *lemma* units.coe_zpow
- \+/\- *lemma* units.coe_inv''
- \+/\- *lemma* units.coe_zpow

Modified src/linear_algebra/orientation.lean
- \+/\- *lemma* units_smul_of_pos
- \+/\- *lemma* units_smul_of_neg
- \+/\- *lemma* units_inv_smul
- \+/\- *lemma* units_smul_eq_self_iff
- \+/\- *lemma* units_smul_eq_neg_iff
- \+/\- *lemma* units_smul_of_pos
- \+/\- *lemma* units_smul_of_neg
- \+/\- *lemma* units_inv_smul
- \+/\- *lemma* units_smul_eq_self_iff
- \+/\- *lemma* units_smul_eq_neg_iff

Modified src/linear_algebra/quadratic_form/basic.lean

Modified src/linear_algebra/quadratic_form/real.lean

Modified src/linear_algebra/tensor_product.lean

Modified src/linear_algebra/trace.lean
- \+/\- *theorem* trace_conj
- \+/\- *theorem* trace_conj

Modified src/measure_theory/group/arithmetic.lean

Modified src/number_theory/arithmetic_function.lean
- \+/\- *def* zeta_unit
- \+/\- *def* zeta_unit

Modified src/number_theory/lucas_lehmer.lean
- \+/\- *lemma* units_card
- \+/\- *lemma* units_card

Modified src/number_theory/lucas_primality.lean

Modified src/number_theory/padics/padic_integers.lean
- \+/\- *lemma* norm_units
- \+/\- *lemma* norm_units
- \+/\- *def* mk_units
- \+/\- *def* unit_coeff
- \+/\- *def* mk_units
- \+/\- *def* unit_coeff

Modified src/number_theory/quadratic_reciprocity.lean
- \+/\- *lemma* euler_criterion_units
- \+/\- *lemma* euler_criterion_units

Modified src/ring_theory/class_group.lean
- \+/\- *lemma* coe_to_principal_ideal
- \+/\- *lemma* to_principal_ideal_eq_iff
- \+/\- *lemma* coe_to_principal_ideal
- \+/\- *lemma* to_principal_ideal_eq_iff
- \+/\- *def* to_principal_ideal
- \+/\- *def* class_group
- \+/\- *def* to_principal_ideal
- \+/\- *def* class_group

Modified src/ring_theory/discrete_valuation_ring.lean
- \+/\- *lemma* unit_mul_pow_congr_unit
- \+/\- *lemma* add_val_def
- \+/\- *lemma* add_val_def'
- \+/\- *lemma* unit_mul_pow_congr_unit
- \+/\- *lemma* add_val_def
- \+/\- *lemma* add_val_def'

Modified src/ring_theory/fintype.lean

Modified src/ring_theory/fractional_ideal.lean
- \+/\- *lemma* fg_unit
- \+/\- *lemma* fg_unit

Modified src/ring_theory/ideal/operations.lean

Modified src/ring_theory/integral_domain.lean

Modified src/ring_theory/multiplicity.lean
- \+/\- *lemma* unit_left
- \+/\- *lemma* unit_right
- \+/\- *lemma* unit_left
- \+/\- *lemma* unit_right

Modified src/ring_theory/power_series/basic.lean
- \+/\- *lemma* coeff_inv_of_unit
- \+/\- *lemma* constant_coeff_inv_of_unit
- \+/\- *lemma* mul_inv_of_unit
- \+/\- *lemma* coeff_inv_of_unit
- \+/\- *lemma* constant_coeff_inv_of_unit
- \+/\- *lemma* mul_inv_of_unit
- \+/\- *lemma* coeff_inv_of_unit
- \+/\- *lemma* constant_coeff_inv_of_unit
- \+/\- *lemma* mul_inv_of_unit
- \+/\- *lemma* coeff_inv_of_unit
- \+/\- *lemma* constant_coeff_inv_of_unit
- \+/\- *lemma* mul_inv_of_unit
- \+/\- *def* inv_of_unit
- \+/\- *def* inv_of_unit
- \+/\- *def* inv_of_unit
- \+/\- *def* inv_of_unit

Modified src/ring_theory/power_series/well_known.lean
- \+/\- *lemma* coeff_inv_units_sub
- \+/\- *lemma* constant_coeff_inv_units_sub
- \+/\- *lemma* inv_units_sub_mul_X
- \+/\- *lemma* inv_units_sub_mul_sub
- \+/\- *lemma* map_inv_units_sub
- \+/\- *lemma* coeff_inv_units_sub
- \+/\- *lemma* constant_coeff_inv_units_sub
- \+/\- *lemma* inv_units_sub_mul_X
- \+/\- *lemma* inv_units_sub_mul_sub
- \+/\- *lemma* map_inv_units_sub
- \+/\- *def* inv_units_sub
- \+/\- *def* inv_units_sub

Modified src/ring_theory/principal_ideal_domain.lean

Modified src/ring_theory/roots_of_unity.lean
- \+/\- *lemma* mem_roots_of_unity
- \+/\- *lemma* map_roots_of_unity
- \+/\- *lemma* mem_roots_of_unity_iff_mem_nth_roots
- \+/\- *lemma* coe_units_iff
- \+/\- *lemma* zpowers_eq
- \+/\- *lemma* eq_pow_of_mem_roots_of_unity
- \+/\- *lemma* is_primitive_root_iff'
- \+/\- *lemma* mem_roots_of_unity
- \+/\- *lemma* map_roots_of_unity
- \+/\- *lemma* mem_roots_of_unity_iff_mem_nth_roots
- \+/\- *lemma* coe_units_iff
- \+/\- *lemma* zpowers_eq
- \+/\- *lemma* eq_pow_of_mem_roots_of_unity
- \+/\- *lemma* is_primitive_root_iff'
- \+/\- *def* roots_of_unity
- \+/\- *def* roots_of_unity

Modified src/ring_theory/subring/basic.lean

Modified src/ring_theory/subsemiring/basic.lean
- \+/\- *lemma* mem_pos_monoid
- \+/\- *lemma* mem_pos_monoid

Modified src/ring_theory/unique_factorization_domain.lean

Modified src/ring_theory/valuation/basic.lean
- \+/\- *lemma* map_units_inv
- \+/\- *lemma* map_units_inv
- \+/\- *lemma* map_units_inv
- \+/\- *lemma* map_units_inv
- \+/\- *theorem* unit_map_eq
- \+/\- *theorem* unit_map_eq
- \+/\- *def* lt_add_subgroup
- \+/\- *def* lt_add_subgroup

Modified src/ring_theory/valuation/integers.lean

Modified src/topology/algebra/field.lean
- \+/\- *lemma* induced_units.continuous_coe
- \+/\- *lemma* units_top_group
- \+/\- *lemma* continuous_units_inv
- \+/\- *lemma* induced_units.continuous_coe
- \+/\- *lemma* units_top_group
- \+/\- *lemma* continuous_units_inv
- \+/\- *def* topological_space_units
- \+/\- *def* topological_space_units

Modified src/topology/algebra/group.lean
- \+/\- *def* homeomorph.prod_units
- \+/\- *def* homeomorph.prod_units

Modified src/topology/algebra/module/basic.lean
- \+/\- *lemma* units_equiv_apply
- \+/\- *lemma* units_equiv_aut_apply
- \+/\- *lemma* units_equiv_aut_apply_symm
- \+/\- *lemma* units_equiv_apply
- \+/\- *lemma* units_equiv_aut_apply
- \+/\- *lemma* units_equiv_aut_apply_symm
- \+/\- *def* of_unit
- \+/\- *def* to_unit
- \+/\- *def* units_equiv
- \+/\- *def* units_equiv_aut
- \+/\- *def* of_unit
- \+/\- *def* to_unit
- \+/\- *def* units_equiv
- \+/\- *def* units_equiv_aut

Modified src/topology/algebra/monoid.lean
- \+/\- *lemma* continuous_coe
- \+/\- *lemma* continuous_coe

Modified src/topology/algebra/mul_action.lean

Modified src/topology/algebra/valuation.lean
- \+/\- *lemma* subgroups_basis
- \+/\- *lemma* subgroups_basis

Modified src/topology/algebra/valued_field.lean
- \+/\- *lemma* valuation.inversion_estimate
- \+/\- *lemma* valuation.inversion_estimate

Modified src/topology/algebra/with_zero_topology.lean
- \+/\- *lemma* directed_lt
- \+/\- *lemma* nhds_coe_units
- \+/\- *lemma* singleton_nhds_of_units
- \+/\- *lemma* nhds_zero_of_units
- \+/\- *lemma* has_basis_nhds_units
- \+/\- *lemma* tendsto_units
- \+/\- *lemma* directed_lt
- \+/\- *lemma* nhds_coe_units
- \+/\- *lemma* singleton_nhds_of_units
- \+/\- *lemma* nhds_zero_of_units
- \+/\- *lemma* has_basis_nhds_units
- \+/\- *lemma* tendsto_units

Modified test/instance_diamonds.lean



## [2022-01-05 23:45:31](https://github.com/leanprover-community/mathlib/commit/cac4e19)
feat(set_theory/ordinal_arithmetic): Proved characterization of `log` ([#11192](https://github.com/leanprover-community/mathlib/pull/11192))
As well as a few simple missing lemmas.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *lemma* power_mul_add_pos
- \+ *lemma* power_mul_add_lt_power_mul_succ
- \+ *lemma* power_mul_add_lt_power_succ
- \+ *theorem* lt_one_iff_zero
- \+ *theorem* le_mul_left
- \+ *theorem* le_mul_right
- \+ *theorem* log_one
- \+ *theorem* log_power_mul_add
- \+ *theorem* log_power



## [2022-01-05 23:45:29](https://github.com/leanprover-community/mathlib/commit/b67857e)
refactor(set_theory/ordinal_arithmetic): Reworked `sup` and `bsup` API ([#11048](https://github.com/leanprover-community/mathlib/pull/11048))
This PR does two things:
- It reworks and matches, for the most part, the API for `ordinal.sup` and `ordinal.bsup`.
- It introduces `ordinal.lsub` and `ordinal.blsub` for (bounded) least strict upper bounds, and proves the expected results.
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+/\- *theorem* typein_lt_type
- \+ *theorem* typein_lt_self
- \+ *theorem* succ_ne_self
- \+/\- *theorem* typein_lt_type

Modified src/set_theory/ordinal_arithmetic.lean
- \- *lemma* sup_succ
- \+ *theorem* lt_sup_of_ne_sup
- \+ *theorem* sup_not_succ_of_ne_sup
- \+/\- *theorem* le_bsup
- \+/\- *theorem* lt_bsup
- \+ *theorem* sup_eq_bsup
- \+ *theorem* bsup_eq_sup
- \+/\- *theorem* is_normal.bsup
- \+ *theorem* lt_bsup_of_ne_bsup
- \+ *theorem* bsup_not_succ_of_ne_bsup
- \+ *theorem* lt_bsup_of_limit
- \+/\- *theorem* bsup_id
- \+ *theorem* lsub_le_iff_lt
- \+ *theorem* lt_lsub
- \+ *theorem* sup_le_lsub
- \+ *theorem* lsub_le_sup_succ
- \+ *theorem* sup_succ_le_lsub
- \+ *theorem* sup_succ_eq_lsub
- \+ *theorem* sup_eq_lsub
- \+ *theorem* lsub_eq_blsub
- \+ *theorem* blsub_eq_lsub
- \+ *theorem* blsub_le_iff_lt
- \+ *theorem* lt_blsub
- \+ *theorem* bsup_le_blsub
- \+ *theorem* blsub_le_bsup_succ
- \+ *theorem* bsup_succ_le_blsub
- \+ *theorem* bsup_succ_eq_blsub
- \+ *theorem* bsup_eq_blsub
- \+ *theorem* blsub_type
- \+ *theorem* blsub_id
- \+/\- *theorem* le_bsup
- \+/\- *theorem* lt_bsup
- \+/\- *theorem* bsup_id
- \+/\- *theorem* is_normal.bsup
- \+ *def* lsub
- \+ *def* blsub



## [2022-01-05 22:31:56](https://github.com/leanprover-community/mathlib/commit/771d144)
feat(analysis/normed_space/lp_space): completeness of the lp space on `Π i, E i` ([#11094](https://github.com/leanprover-community/mathlib/pull/11094))
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *lemma* normed_group.uniformity_basis_dist

Modified src/analysis/normed/group/pointwise.lean
- \+ *lemma* metric.bounded.exists_pos_norm_le

Modified src/analysis/normed_space/lp_space.lean
- \+/\- *lemma* mem_ℓp_gen
- \+ *lemma* mem_ℓp_gen'
- \+ *lemma* norm_apply_le_norm
- \+ *lemma* sum_rpow_le_norm_rpow
- \+ *lemma* norm_le_of_forall_le'
- \+ *lemma* norm_le_of_forall_le
- \+ *lemma* norm_le_of_tsum_le
- \+ *lemma* norm_le_of_forall_sum_le
- \+ *lemma* uniform_continuous_coe
- \+ *lemma* norm_apply_le_of_tendsto
- \+ *lemma* sum_rpow_le_of_tendsto
- \+ *lemma* norm_le_of_tendsto
- \+ *lemma* mem_ℓp_of_tendsto
- \+ *lemma* tendsto_lp_of_tendsto_pi
- \+/\- *lemma* mem_ℓp_gen

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* eventually_at_top_curry
- \+ *lemma* eventually_at_bot_curry

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* finite_of_summable_const

Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy_seq.eventually_eventually



## [2022-01-05 19:08:16](https://github.com/leanprover-community/mathlib/commit/8b2d181)
feat(ring_theory/laurent_series): laurent_series is_fraction_ring over power_series ([#11220](https://github.com/leanprover-community/mathlib/pull/11220))
#### Estimated changes
Modified src/ring_theory/laurent_series.lean

Modified src/ring_theory/localization.lean
- \+ *lemma* of_le

Modified src/ring_theory/non_zero_divisors.lean
- \+ *lemma* is_unit_of_mem_non_zero_divisors

Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* X_ne_zero



## [2022-01-05 17:28:18](https://github.com/leanprover-community/mathlib/commit/f6dfea6)
feat(measure_theory/integral): Cauchy integral formula for a circle ([#10000](https://github.com/leanprover-community/mathlib/pull/10000))
#### Estimated changes
Modified src/analysis/box_integral/box/basic.lean
- \+ *lemma* monotone_face
- \+ *lemma* Ioo_subset_coe
- \+ *lemma* Union_Ioo_of_tendsto
- \+ *lemma* exists_seq_mono_tendsto
- \+/\- *def* face
- \+/\- *def* face

Modified src/analysis/box_integral/partition/measure.lean
- \+/\- *lemma* measure_Icc_lt_top
- \+/\- *lemma* measure_coe_lt_top
- \+/\- *lemma* measurable_set_coe
- \+/\- *lemma* measurable_set_Icc
- \+ *lemma* measurable_set_Ioo
- \+ *lemma* coe_ae_eq_Icc
- \+ *lemma* Ioo_ae_eq_Icc
- \+/\- *lemma* measurable_set_coe
- \+/\- *lemma* measurable_set_Icc
- \+/\- *lemma* measure_Icc_lt_top
- \+/\- *lemma* measure_coe_lt_top

Created src/analysis/complex/cauchy_integral.lean
- \+ *lemma* integral_boundary_rect_of_has_fderiv_within_at_real_off_countable
- \+ *lemma* integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
- \+ *lemma* circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
- \+ *lemma* circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
- \+ *lemma* circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable
- \+ *lemma* circle_integral_eq_zero_of_differentiable_on_off_countable
- \+ *lemma* circle_integral_sub_inv_smul_of_differentiable_on_off_countable_aux
- \+ *lemma* two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable
- \+ *lemma* circle_integral_sub_inv_smul_of_differentiable_on_off_countable
- \+ *lemma* circle_integral_div_sub_of_differentiable_on_off_countable
- \+ *lemma* has_fpower_series_on_ball_of_differentiable_off_countable

Modified src/measure_theory/constructions/pi.lean
- \+ *lemma* pi_Ioo_ae_eq_pi_Ioc

Modified src/measure_theory/integral/divergence_theorem.lean
- \+ *lemma* integral_divergence_of_has_fderiv_within_at_off_countable_aux₁
- \+ *lemma* integral_divergence_of_has_fderiv_within_at_off_countable_aux₂
- \+ *theorem* for

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
- \+ *lemma* degree_list_prod_le
- \+ *lemma* degree_multiset_prod_le
- \+ *lemma* degree_prod_le



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
Created src/category_theory/sites/left_exact.lean
- \+ *lemma* lift_to_plus_obj_limit_obj_fac
- \+ *def* cone_comp_evaluation_of_cone_comp_diagram_functor_comp_evaluation
- \+ *def* lift_to_plus_obj_limit_obj



## [2022-01-05 14:15:44](https://github.com/leanprover-community/mathlib/commit/a580727)
chore(topology/omega_complete_partial_order): golf ([#11250](https://github.com/leanprover-community/mathlib/pull/11250))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set_of_bijective

Modified src/order/omega_complete_partial_order.lean
- \+ *lemma* inf_continuous'

Modified src/topology/omega_complete_partial_order.lean
- \+/\- *theorem* is_open_sUnion
- \+/\- *theorem* is_open_sUnion



## [2022-01-05 14:15:40](https://github.com/leanprover-community/mathlib/commit/802f23c)
feat(data/fintype/basic): `set_fintype_card_eq_univ_iff` ([#11244](https://github.com/leanprover-community/mathlib/pull/11244))
Adds companion lemma to `set_fintype_card_le_univ`. This PR also moves several `set.to_finset` lemmas earlier in the file.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+/\- *lemma* set.to_finset_univ
- \+/\- *lemma* set.to_finset_eq_empty_iff
- \+/\- *lemma* set.to_finset_empty
- \+/\- *lemma* set.to_finset_range
- \+/\- *lemma* set_fintype_card_le_univ
- \+ *lemma* set_fintype_card_eq_univ_iff
- \+/\- *lemma* set_fintype_card_le_univ
- \+/\- *lemma* set.to_finset_univ
- \+/\- *lemma* set.to_finset_eq_empty_iff
- \+/\- *lemma* set.to_finset_empty
- \+/\- *lemma* set.to_finset_range
- \+/\- *def* set_fintype
- \+/\- *def* set_fintype



## [2022-01-05 14:15:39](https://github.com/leanprover-community/mathlib/commit/b27e33a)
feat(data/{fin/vec_notation, matrix/notation}): `cons_{add,sub,dot_product}_cons` ([#11241](https://github.com/leanprover-community/mathlib/pull/11241))
While these can be proved by `simp`, they are not rejected by the simp linter.
#### Estimated changes
Modified src/data/fin/vec_notation.lean
- \+ *lemma* cons_add_cons
- \+ *lemma* cons_sub_cons

Modified src/data/matrix/notation.lean
- \+ *lemma* cons_dot_product_cons



## [2022-01-05 14:15:38](https://github.com/leanprover-community/mathlib/commit/98b64f4)
feat(linear_algebra/orientation): bases from orientations ([#11234](https://github.com/leanprover-community/mathlib/pull/11234))
Add a lemma giving the orientation of a basis constructed with
`units_smul`, and thus definitions and lemmas to construct a basis
from an orientation.
#### Estimated changes
Modified src/linear_algebra/orientation.lean
- \+ *lemma* orientation_units_smul
- \+ *lemma* orientation_neg_single
- \+ *lemma* orientation_adjust_to_orientation
- \+ *lemma* adjust_to_orientation_apply_eq_or_eq_neg
- \+ *lemma* some_basis_orientation
- \+ *def* adjust_to_orientation
- \+ *def* some_basis



## [2022-01-05 14:15:37](https://github.com/leanprover-community/mathlib/commit/33b5d26)
feat(analysis/complex): `re`, `im`, and `closure`/`interior`/`frontier` ([#11215](https://github.com/leanprover-community/mathlib/pull/11215))
#### Estimated changes
Modified src/analysis/complex/basic.lean

Created src/analysis/complex/re_im_topology.lean
- \+ *lemma* is_trivial_topological_fiber_bundle_re
- \+ *lemma* is_trivial_topological_fiber_bundle_im
- \+ *lemma* is_topological_fiber_bundle_re
- \+ *lemma* is_topological_fiber_bundle_im
- \+ *lemma* is_open_map_re
- \+ *lemma* is_open_map_im
- \+ *lemma* quotient_map_re
- \+ *lemma* quotient_map_im
- \+ *lemma* interior_preimage_re
- \+ *lemma* interior_preimage_im
- \+ *lemma* closure_preimage_re
- \+ *lemma* closure_preimage_im
- \+ *lemma* frontier_preimage_re
- \+ *lemma* frontier_preimage_im
- \+ *lemma* interior_set_of_re_le
- \+ *lemma* interior_set_of_im_le
- \+ *lemma* interior_set_of_le_re
- \+ *lemma* interior_set_of_le_im
- \+ *lemma* closure_set_of_re_lt
- \+ *lemma* closure_set_of_im_lt
- \+ *lemma* closure_set_of_lt_re
- \+ *lemma* closure_set_of_lt_im
- \+ *lemma* frontier_set_of_re_le
- \+ *lemma* frontier_set_of_im_le
- \+ *lemma* frontier_set_of_le_re
- \+ *lemma* frontier_set_of_le_im
- \+ *lemma* frontier_set_of_re_lt
- \+ *lemma* frontier_set_of_im_lt
- \+ *lemma* frontier_set_of_lt_re
- \+ *lemma* frontier_set_of_lt_im
- \+ *lemma* closure_preimage_re_inter_preimage_im
- \+ *lemma* interior_preimage_re_inter_preimage_im
- \+ *lemma* frontier_preimage_re_inter_preimage_im
- \+ *lemma* frontier_set_of_le_re_and_le_im
- \+ *lemma* frontier_set_of_le_re_and_im_le

Modified src/data/complex/basic.lean
- \- *theorem* equiv_real_prod_apply
- \- *theorem* equiv_real_prod_symm_re
- \- *theorem* equiv_real_prod_symm_im
- \+/\- *def* equiv_real_prod
- \+/\- *def* equiv_real_prod

Modified src/topology/homeomorph.lean
- \+ *lemma* preimage_frontier



## [2022-01-05 14:15:35](https://github.com/leanprover-community/mathlib/commit/3115ced)
feat(ring_theory/non_zero_divisors): mul_{left,right}_cancel API ([#11211](https://github.com/leanprover-community/mathlib/pull/11211))
Not all `monoid_with_zero` are `cancel_monoid_with_zero`,
so we can't use `mul_right_cancel₀` everywhere. However, by definition,
multiplication by non-zero-divisors is 0 iff the multiplicand is 0.
In the context of a ring, that allows us to `mul_cancel_right`
#### Estimated changes
Modified src/ring_theory/non_zero_divisors.lean
- \+ *lemma* mem_non_zero_divisors_iff
- \+ *lemma* mul_right_mem_non_zero_divisors_eq_zero_iff
- \+ *lemma* mul_right_coe_non_zero_divisors_eq_zero_iff
- \+ *lemma* mul_left_mem_non_zero_divisors_eq_zero_iff
- \+ *lemma* mul_left_coe_non_zero_divisors_eq_zero_iff
- \+ *lemma* mul_cancel_right_mem_non_zero_divisor
- \+ *lemma* mul_cancel_right_coe_non_zero_divisor
- \+ *lemma* mul_cancel_left_mem_non_zero_divisor
- \+ *lemma* mul_cancel_left_coe_non_zero_divisor



## [2022-01-05 14:15:34](https://github.com/leanprover-community/mathlib/commit/3bd2044)
chore(data/nat/prime): reuse a result from algebra.big_operators.associated ([#11143](https://github.com/leanprover-community/mathlib/pull/11143))
#### Estimated changes
Modified src/algebra/big_operators/associated.lean
- \- *lemma* prime.dvd_prod_iff
- \- *lemma* nat.prime.dvd_finset_prod_iff
- \- *lemma* nat.prime.dvd_finsupp_prod_iff

Created src/data/list/prime.lean
- \+ *lemma* prime.dvd_prod_iff
- \+ *lemma* prime.not_dvd_prod
- \+ *lemma* prime_dvd_prime_iff_eq
- \+ *lemma* mem_list_primes_of_dvd_prod
- \+ *lemma* perm_of_prod_eq_prod

Modified src/data/nat/prime.lean
- \- *lemma* prime.dvd_prod_iff
- \- *lemma* prime.not_dvd_prod
- \- *lemma* mem_list_primes_of_dvd_prod
- \- *lemma* perm_of_prod_eq_prod



## [2022-01-05 14:15:33](https://github.com/leanprover-community/mathlib/commit/57a9f8b)
chore(group_theory/sub{monoid,group}, linear_algebra/basic): rename equivalences to mapped subobjects ([#11075](https://github.com/leanprover-community/mathlib/pull/11075))
This makes the names shorter and more uniform:
* `add_equiv.map_add_submonoid`
* `add_equiv.map_add_subgroup`
* `linear_equiv.map_submodule`
#### Estimated changes
Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* lie_subalgebra_map_apply
- \- *lemma* of_subalgebra_apply
- \+ *def* lie_subalgebra_map
- \- *def* of_subalgebra

Modified src/group_theory/group_action/basic.lean

Modified src/group_theory/subgroup/basic.lean
- \+ *def* subgroup_map
- \- *def* subgroup_equiv_map

Modified src/group_theory/subgroup/pointwise.lean

Modified src/group_theory/submonoid/operations.lean
- \+ *def* submonoid_map
- \- *def* submonoid_equiv_map

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule_map_apply
- \+ *lemma* submodule_map_symm_apply
- \- *lemma* of_submodule_apply
- \- *lemma* of_submodule_symm_apply
- \+ *def* submodule_map
- \- *def* of_submodule

Modified src/linear_algebra/dimension.lean

Modified src/linear_algebra/finite_dimensional.lean



## [2022-01-05 14:15:32](https://github.com/leanprover-community/mathlib/commit/7e5eebd)
feat(linear_algebra/clifford_algebra/equivs): There is a clifford algebra isomorphic to the dual numbers ([#10730](https://github.com/leanprover-community/mathlib/pull/10730))
This adds a brief file on the dual numbers, and then shows that they are equivalent to the clifford algebra with `Q = (0 : quadratic_form R R)`.
#### Estimated changes
Created src/algebra/dual_number.lean
- \+ *lemma* fst_eps
- \+ *lemma* snd_eps
- \+ *lemma* snd_mul
- \+ *lemma* eps_mul_eps
- \+ *lemma* inr_eq_smul_eps
- \+ *lemma* alg_hom_ext
- \+ *lemma* lift_apply_eps
- \+ *lemma* lift_eps
- \+ *def* dual_number.eps
- \+ *def* lift

Modified src/linear_algebra/clifford_algebra/equivs.lean
- \+ *lemma* ι_mul_ι
- \+ *lemma* equiv_ι
- \+ *lemma* equiv_symm_eps



## [2022-01-05 12:21:49](https://github.com/leanprover-community/mathlib/commit/cef3258)
chore(group_theory/group_action/defs): add instances to copy statements about left actions to right actions when the two are equal ([#10949](https://github.com/leanprover-community/mathlib/pull/10949))
While these instances are usually available elsewhere, these shortcuts can reduce the number of typeclass assumptions other lemmas needs.
Since the instances carry no data, the only harm they can cause is performance.
There were some typeclass loops brought on by some bad instance unification, similar to the ones removed by @Vierkantor in 9ee2a50aa439d092c8dea16c1f82f7f8e1f1ea2c. We turn these into `lemma`s and  duplicate the docstring explaining the problem. That commit has a much longer explanation of the problem.
#### Estimated changes
Modified src/group_theory/group_action/defs.lean
- \+ *lemma* comp.smul_comm_class
- \+ *lemma* comp.smul_comm_class'



## [2022-01-05 11:32:02](https://github.com/leanprover-community/mathlib/commit/8d5830e)
chore(measure_theory/measurable_space): use implicit measurable_space argument ([#11230](https://github.com/leanprover-community/mathlib/pull/11230))
The `measurable_space` argument is inferred from other arguments (like `measurable f` or a measure for example) instead of being a type class. This ensures that the lemmas are usable without `@` when several measurable space structures are used for the same type.
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable_from_top
- \+/\- *lemma* subsingleton.measurable
- \+/\- *lemma* measurable_of_subsingleton_codomain
- \+/\- *lemma* measurable_one
- \+/\- *lemma* measurable_of_empty
- \+/\- *lemma* measurable_of_empty_codomain
- \+/\- *lemma* measurable_const'
- \+/\- *lemma* measurable_of_fintype
- \+/\- *lemma* measurable_set_preimage
- \+/\- *lemma* measurable.piecewise
- \+/\- *lemma* measurable.ite
- \+/\- *lemma* measurable.indicator
- \+/\- *lemma* measurable_to_encodable
- \+/\- *lemma* measurable_unit
- \+/\- *lemma* measurable_fst
- \+/\- *lemma* measurable_snd
- \+/\- *lemma* measurable_prod
- \+/\- *lemma* measurable_swap
- \+/\- *lemma* measurable_swap_iff
- \+/\- *lemma* measurable_inl
- \+/\- *lemma* measurable_inr
- \+/\- *lemma* measurable_set_range_inl
- \+/\- *lemma* measurable_set_range_inr
- \+/\- *lemma* measurable_set.exists_measurable_proj
- \+/\- *lemma* measurable_from_top
- \+/\- *lemma* measurable_set_preimage
- \+/\- *lemma* subsingleton.measurable
- \+/\- *lemma* measurable_of_subsingleton_codomain
- \+/\- *lemma* measurable.piecewise
- \+/\- *lemma* measurable.ite
- \+/\- *lemma* measurable.indicator
- \+/\- *lemma* measurable_one
- \+/\- *lemma* measurable_of_empty
- \+/\- *lemma* measurable_of_empty_codomain
- \+/\- *lemma* measurable_const'
- \+/\- *lemma* measurable_of_fintype
- \+/\- *lemma* measurable_to_encodable
- \+/\- *lemma* measurable_unit
- \+/\- *lemma* measurable_fst
- \+/\- *lemma* measurable_snd
- \+/\- *lemma* measurable_prod
- \+/\- *lemma* measurable_swap
- \+/\- *lemma* measurable_swap_iff
- \+/\- *lemma* measurable_inl
- \+/\- *lemma* measurable_inr
- \+/\- *lemma* measurable_set_range_inl
- \+/\- *lemma* measurable_set_range_inr
- \+/\- *lemma* measurable_set.exists_measurable_proj

Modified src/measure_theory/measurable_space_def.lean
- \+/\- *lemma* measurable_set.empty
- \+/\- *lemma* measurable.comp
- \+/\- *lemma* measurable_set.empty
- \+/\- *lemma* measurable.comp
- \+/\- *def* measurable_set
- \+/\- *def* measurable_set

Modified src/probability_theory/stopping.lean



## [2022-01-05 08:10:47](https://github.com/leanprover-community/mathlib/commit/4912740)
chore(analysis/inner_product_space/basic): extract common `variables` ([#11214](https://github.com/leanprover-community/mathlib/pull/11214))
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+/\- *lemma* orthogonal_family.eq_ite
- \+/\- *lemma* orthogonal_family.inner_right_dfinsupp
- \+/\- *lemma* orthogonal_family.inner_right_fintype
- \+/\- *lemma* orthogonal_family.independent
- \+/\- *lemma* orthogonal_family.comp
- \+/\- *lemma* orthogonal_family.orthonormal_sigma_orthonormal
- \+/\- *lemma* direct_sum.submodule_is_internal.collected_basis_orthonormal
- \+/\- *lemma* orthogonal_family.eq_ite
- \+/\- *lemma* orthogonal_family.inner_right_dfinsupp
- \+/\- *lemma* orthogonal_family.inner_right_fintype
- \+/\- *lemma* orthogonal_family.independent
- \+/\- *lemma* orthogonal_family.comp
- \+/\- *lemma* orthogonal_family.orthonormal_sigma_orthonormal
- \+/\- *lemma* direct_sum.submodule_is_internal.collected_basis_orthonormal



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
- \+/\- *lemma* pow_apply
- \+/\- *lemma* pow_apply



## [2022-01-05 01:44:24](https://github.com/leanprover-community/mathlib/commit/4093834)
feat(measure_theory/measure/finite_measure_weak_convergence): add definition and lemmas of pairing measures with nonnegative continuous test functions. ([#9430](https://github.com/leanprover-community/mathlib/pull/9430))
Add definition and lemmas about pairing of `finite_measure`s and `probability_measure`s with nonnegative continuous test functions. These pairings will be used in the definition of the topology of weak convergence (convergence in distribution): the topology will be defined as an induced topology based on them.
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* _root_.is_finite_measure.lintegral_lt_top_of_bounded_to_ennreal

Modified src/measure_theory/measure/finite_measure_weak_convergence.lean
- \+ *lemma* _root_.bounded_continuous_function.nnreal.to_ennreal_comp_measurable
- \+ *lemma* lintegral_lt_top_of_bounded_continuous_to_nnreal
- \+ *lemma* test_against_nn_coe_eq
- \+ *lemma* test_against_nn_const
- \+ *lemma* test_against_nn_mono
- \+ *lemma* test_against_nn_add
- \+ *lemma* test_against_nn_smul
- \+ *lemma* test_against_nn_lipschitz_estimate
- \+ *lemma* test_against_nn_lipschitz
- \+ *lemma* lintegral_lt_top_of_bounded_continuous_to_nnreal
- \+ *lemma* test_against_nn_coe_eq
- \+ *lemma* to_finite_measure_test_against_nn_eq_test_against_nn
- \+ *lemma* test_against_nn_const
- \+ *lemma* test_against_nn_mono
- \+ *lemma* test_against_nn_lipschitz
- \+ *def* test_against_nn
- \+ *def* to_weak_dual_bounded_continuous_nnreal
- \+ *def* test_against_nn
- \+ *def* to_weak_dual_bounded_continuous_nnreal

Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* nnreal.upper_bound

Modified src/topology/metric_space/basic.lean
- \+ *lemma* nnreal.nndist_zero_eq_val
- \+ *lemma* nnreal.nndist_zero_eq_val'
- \+ *lemma* nnreal.le_add_nndist



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
- \+/\- *lemma* set.to_finset_univ

Modified src/group_theory/specific_groups/cyclic.lean



## [2022-01-04 18:47:56](https://github.com/leanprover-community/mathlib/commit/037147e)
feat(probability_theory/stopping): define stopped process ([#10851](https://github.com/leanprover-community/mathlib/pull/10851))
#### Estimated changes
Modified src/probability_theory/stopping.lean
- \+ *lemma* is_stopping_time.measurable_set_le
- \+/\- *lemma* is_stopping_time.measurable_set_eq
- \+ *lemma* is_stopping_time.measurable_set_ge
- \+ *lemma* stopped_process_eq_of_le
- \+ *lemma* stopped_process_eq_of_ge
- \+ *lemma* stopped_process_eq
- \+ *lemma* adapted.stopped_process
- \+ *lemma* measurable_stopped_process
- \+ *lemma* mem_ℒp_stopped_process
- \+ *lemma* integrable_stopped_process
- \+/\- *lemma* is_stopping_time.measurable_set_eq
- \+ *def* stopped_value
- \+ *def* stopped_process



## [2022-01-04 16:45:27](https://github.com/leanprover-community/mathlib/commit/5df2e7b)
chore(data/polynomial, data/finset/lattice): basic lemmas ([#11237](https://github.com/leanprover-community/mathlib/pull/11237))
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* coe_sup_of_nonempty
- \+ *lemma* coe_inf_of_nonempty

Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* degree_mono



## [2022-01-04 16:45:25](https://github.com/leanprover-community/mathlib/commit/5f3f01f)
feat(set_theory/ordinal_arithmetic): Proved `add_log_le_log_mul` ([#11228](https://github.com/leanprover-community/mathlib/pull/11228))
That is, `log b u + log b v ≤ log b (u * v)`. The other direction holds only when `b ≠ 2` and `b` is principal multiplicative, and will be added at a much later PR.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* add_log_le_log_mul



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
- \+ *theorem* dvd_of_mod_eq_zero
- \+ *theorem* mod_eq_zero_of_dvd
- \+ *theorem* dvd_iff_mod_eq_zero



## [2022-01-04 16:45:22](https://github.com/leanprover-community/mathlib/commit/7f244cf)
feat(category_theory/limits/filtered_colimits_commute_with_finite_limits): A curried variant of the fact that filtered colimits commute with finite limits. ([#11154](https://github.com/leanprover-community/mathlib/pull/11154))
#### Estimated changes
Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean
- \+ *lemma* ι_colimit_limit_iso_limit_π



## [2022-01-04 16:45:20](https://github.com/leanprover-community/mathlib/commit/06c3ab2)
feat(ring_theory/discriminant): add of_power_basis_eq_norm ([#11149](https://github.com/leanprover-community/mathlib/pull/11149))
From flt-regular.
#### Estimated changes
Modified src/data/fin/interval.lean
- \+ *lemma* prod_filter_lt_mul_neg_eq_prod_off_diag

Modified src/ring_theory/discriminant.lean
- \+ *lemma* of_power_basis_eq_prod'
- \+ *lemma* of_power_basis_eq_prod''
- \+ *lemma* of_power_basis_eq_norm



## [2022-01-04 16:45:19](https://github.com/leanprover-community/mathlib/commit/4a0e844)
feat(data/finset): to_finset empty iff ([#11088](https://github.com/leanprover-community/mathlib/pull/11088))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* to_finset_eq_empty_iff



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
- \+ *def* zero_default
- \+ *def* zero_default_supp
- \+ *def* apply_finsupp

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
- \+ *lemma* linear_order.to_lattice_eq_filter_germ_lattice
- \- *lemma* lattice_of_linear_order_eq_filter_germ_lattice

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
- \+ *lemma* proj_surj_on_base_set
- \+ *lemma* proj_surj_on_base_set
- \+ *lemma* is_topological_fiber_bundle.map_proj_nhds
- \+ *lemma* is_topological_fiber_bundle.surjective_proj
- \+ *lemma* is_topological_fiber_bundle.quotient_map_proj



## [2022-01-04 13:36:33](https://github.com/leanprover-community/mathlib/commit/aa82ba0)
feat(algebra/opposites): add `add_opposite` ([#11080](https://github.com/leanprover-community/mathlib/pull/11080))
Add `add_opposite`, add `to_additive` here and there. More `to_additive` can be added as needed later.
#### Estimated changes
Modified src/algebra/group/opposite.lean
- \+/\- *lemma* semiconj_by_op
- \+/\- *lemma* semiconj_by_unop
- \+ *lemma* _root_.semiconj_by.op
- \+ *lemma* _root_.semiconj_by.unop
- \+ *lemma* _root_.commute.op
- \+/\- *lemma* commute.unop
- \+/\- *lemma* commute_op
- \+/\- *lemma* commute_unop
- \+ *lemma* op_pow
- \+ *lemma* unop_pow
- \+ *lemma* op_mul_equiv_to_equiv
- \+/\- *lemma* units.coe_unop_op_equiv
- \+/\- *lemma* units.coe_op_equiv_symm
- \+ *lemma* add_monoid_hom.mul_op_ext
- \- *lemma* semiconj_by.op
- \- *lemma* semiconj_by.unop
- \+/\- *lemma* semiconj_by_op
- \+/\- *lemma* semiconj_by_unop
- \- *lemma* commute.op
- \+/\- *lemma* commute.unop
- \+/\- *lemma* commute_op
- \+/\- *lemma* commute_unop
- \+/\- *lemma* units.coe_unop_op_equiv
- \+/\- *lemma* units.coe_op_equiv_symm
- \- *lemma* add_monoid_hom.op_ext
- \+ *def* op_mul_equiv
- \+/\- *def* monoid_hom.to_opposite
- \+/\- *def* monoid_hom.from_opposite
- \+/\- *def* units.op_equiv
- \+/\- *def* monoid_hom.op
- \+/\- *def* monoid_hom.unop
- \+ *def* add_monoid_hom.mul_op
- \+ *def* add_monoid_hom.mul_unop
- \+ *def* add_equiv.mul_op
- \+ *def* add_equiv.mul_unop
- \+/\- *def* mul_equiv.unop
- \+/\- *def* monoid_hom.to_opposite
- \+/\- *def* monoid_hom.from_opposite
- \+/\- *def* units.op_equiv
- \+/\- *def* monoid_hom.op
- \+/\- *def* monoid_hom.unop
- \- *def* add_monoid_hom.op
- \- *def* add_monoid_hom.unop
- \- *def* add_equiv.op
- \- *def* add_equiv.unop
- \+/\- *def* mul_equiv.unop

Modified src/algebra/opposites.lean
- \+/\- *lemma* unop_op
- \+/\- *lemma* op_unop
- \+/\- *lemma* op_comp_unop
- \+/\- *lemma* unop_comp_op
- \+/\- *lemma* op_bijective
- \+/\- *lemma* unop_bijective
- \+/\- *lemma* op_injective
- \+/\- *lemma* op_surjective
- \+/\- *lemma* unop_injective
- \+/\- *lemma* unop_surjective
- \+/\- *lemma* op_inj
- \+/\- *lemma* unop_inj
- \+/\- *lemma* op_one
- \+/\- *lemma* unop_one
- \+/\- *lemma* op_mul
- \+/\- *lemma* unop_mul
- \+/\- *lemma* op_inv
- \+/\- *lemma* unop_inv
- \+/\- *lemma* op_smul
- \+/\- *lemma* unop_smul
- \+/\- *lemma* unop_eq_zero_iff
- \+/\- *lemma* op_eq_zero_iff
- \+/\- *lemma* unop_ne_zero_iff
- \+/\- *lemma* op_ne_zero_iff
- \+/\- *lemma* unop_eq_one_iff
- \+/\- *lemma* op_eq_one_iff
- \+/\- *lemma* op_one
- \+/\- *lemma* unop_one
- \+/\- *lemma* op_eq_one_iff
- \+/\- *lemma* unop_eq_one_iff
- \+/\- *lemma* op_mul
- \+/\- *lemma* unop_mul
- \+/\- *lemma* op_inv
- \+/\- *lemma* unop_inv
- \+ *lemma* op_div
- \+ *lemma* unop_div
- \+/\- *lemma* unop_op
- \+/\- *lemma* op_unop
- \+/\- *lemma* op_comp_unop
- \+/\- *lemma* unop_comp_op
- \+/\- *lemma* op_bijective
- \+/\- *lemma* unop_bijective
- \+/\- *lemma* op_injective
- \+/\- *lemma* op_surjective
- \+/\- *lemma* unop_injective
- \+/\- *lemma* unop_surjective
- \+/\- *lemma* op_inj
- \+/\- *lemma* unop_inj
- \+/\- *lemma* op_one
- \+/\- *lemma* unop_one
- \+/\- *lemma* op_mul
- \+/\- *lemma* unop_mul
- \+/\- *lemma* op_inv
- \+/\- *lemma* unop_inv
- \+/\- *lemma* op_smul
- \+/\- *lemma* unop_smul
- \+/\- *lemma* unop_eq_zero_iff
- \+/\- *lemma* op_eq_zero_iff
- \+/\- *lemma* unop_ne_zero_iff
- \+/\- *lemma* op_ne_zero_iff
- \+/\- *lemma* unop_eq_one_iff
- \+/\- *lemma* op_eq_one_iff

Modified src/algebra/ring/opposite.lean

Modified src/data/equiv/ring.lean

Modified src/group_theory/group_action/opposite.lean
- \+/\- *lemma* op_smul_eq_mul
- \+/\- *lemma* op_smul_eq_mul



## [2022-01-04 13:36:24](https://github.com/leanprover-community/mathlib/commit/a7aa2c8)
feat(data/finset/sigma): A way to lift `finset`-valued functions to a sigma type ([#10958](https://github.com/leanprover-community/mathlib/pull/10958))
This defines `finset.sigma_lift : (Π i, α i → β i → finset (γ i)) → Σ i, α i → Σ i, β i → finset (Σ i, γ i)` as the function which returns the finset corresponding to the first coordinate of `a b : Σ i, α i` if they have the same, or the empty set else.
#### Estimated changes
Modified src/data/finset/sigma.lean
- \+ *lemma* mem_sigma_lift
- \+ *lemma* mk_mem_sigma_lift
- \+ *lemma* not_mem_sigma_lift_of_ne_left
- \+ *lemma* not_mem_sigma_lift_of_ne_right
- \+ *lemma* sigma_lift_nonempty
- \+ *lemma* sigma_lift_eq_empty
- \+ *lemma* sigma_lift_mono
- \+ *lemma* card_sigma_lift
- \+ *def* sigma_lift



## [2022-01-04 13:36:16](https://github.com/leanprover-community/mathlib/commit/8bd2059)
feat(data/finset/slice): `r`-sets and slice ([#10685](https://github.com/leanprover-community/mathlib/pull/10685))
Two simple nonetheless useful definitions about set families. A family of `r`-sets is a set of finsets of cardinality `r`. The slice of a set family is its subset of `r`-sets.
#### Estimated changes
Modified src/combinatorics/set_family/shadow.lean

Created src/data/finset/slice.lean
- \+ *lemma* sized.mono
- \+ *lemma* sized_union
- \+ *lemma* subset_powerset_len_univ_iff
- \+ *lemma* _root_.set.sized.card_le
- \+ *lemma* mem_slice
- \+ *lemma* slice_subset
- \+ *lemma* sized_slice
- \+ *lemma* eq_of_mem_slice
- \+ *lemma* ne_of_mem_slice
- \+ *lemma* pairwise_disjoint_slice
- \+ *def* sized
- \+ *def* slice

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.mem_powerset_len_univ_iff



## [2022-01-04 12:08:44](https://github.com/leanprover-community/mathlib/commit/1aec9a1)
feat(analysis/inner_product_space/dual,adjoint): add some lemmas about extensionality with respect to a basis ([#11176](https://github.com/leanprover-community/mathlib/pull/11176))
This PR adds some lemmas about extensionality in inner product spaces with respect to a basis.
#### Estimated changes
Modified src/analysis/inner_product_space/adjoint.lean
- \+ *lemma* eq_adjoint_iff_basis
- \+ *lemma* eq_adjoint_iff_basis_left
- \+ *lemma* eq_adjoint_iff_basis_right

Modified src/analysis/inner_product_space/dual.lean
- \+ *lemma* ext_inner_left_basis
- \+ *lemma* ext_inner_right_basis



## [2022-01-04 09:44:51](https://github.com/leanprover-community/mathlib/commit/03872fd)
feat(*): Prerequisites for the Spec gamma adjunction ([#11209](https://github.com/leanprover-community/mathlib/pull/11209))
#### Estimated changes
Modified src/algebraic_geometry/Scheme.lean
- \+ *lemma* forget_to_LocallyRingedSpace_preimage

Modified src/algebraic_geometry/Spec.lean
- \+ *lemma* Spec.basic_open_hom_ext

Modified src/algebraic_geometry/locally_ringed_space.lean
- \+ *lemma* comp_val_c
- \+ *lemma* comp_val_c_app

Modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+ *lemma* comap_comp_apply
- \+ *lemma* is_local_ring_hom_iff_comap_closed_point
- \+ *lemma* comap_closed_point
- \- *lemma* local_hom_iff_comap_closed_point

Modified src/algebraic_geometry/ringed_space.lean
- \+ *lemma* mem_top_basic_open

Modified src/algebraic_geometry/stalks.lean
- \- *def* stalk

Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *lemma* is_localization.to_stalk
- \+ *lemma* is_localization.to_basic_open

Modified src/category_theory/adjunction/basic.lean
- \+ *lemma* hom_equiv_id
- \+ *lemma* hom_equiv_symm_id

Modified src/topology/sheaves/presheaf.lean
- \+ *lemma* pushforward_eq'_hom_app
- \+ *lemma* pushforward_map_app'



## [2022-01-04 09:44:50](https://github.com/leanprover-community/mathlib/commit/9a8e9fa)
chore(category_theory/limits): Generalize universes for `preserves/shapes/pullback.lean` ([#10780](https://github.com/leanprover-community/mathlib/pull/10780))
#### Estimated changes
Modified src/category_theory/limits/constructions/epi_mono.lean

Modified src/category_theory/limits/functor_category.lean
- \+/\- *def* preserves_limits_of_shape_of_evaluation
- \+ *def* {w'
- \+/\- *def* preserves_colimits_of_shape_of_evaluation
- \+ *def* {w'
- \+/\- *def* preserves_limits_of_shape_of_evaluation
- \- *def* preserves_limits_of_evaluation
- \+/\- *def* preserves_colimits_of_shape_of_evaluation
- \- *def* preserves_colimits_of_evaluation

Modified src/category_theory/limits/is_limit.lean
- \+ *def* of_whisker_equivalence
- \+ *def* whisker_equivalence_equiv
- \+ *def* of_whisker_equivalence
- \+ *def* whisker_equivalence_equiv

Modified src/category_theory/limits/preserves/limits.lean

Modified src/category_theory/limits/preserves/shapes/pullbacks.lean
- \+/\- *lemma* preserves_pullback.iso_hom
- \+/\- *lemma* preserves_pushout.iso_hom
- \+/\- *lemma* preserves_pullback.iso_hom
- \+/\- *lemma* preserves_pushout.iso_hom
- \+/\- *def* is_limit_of_has_pullback_of_preserves_limit
- \+/\- *def* preserves_pullback_symmetry
- \+/\- *def* is_colimit_of_has_pushout_of_preserves_colimit
- \+/\- *def* preserves_pushout_symmetry
- \+/\- *def* preserves_pullback.of_iso_comparison
- \+/\- *def* preserves_pushout.of_iso_comparison
- \+/\- *def* is_limit_of_has_pullback_of_preserves_limit
- \+/\- *def* preserves_pullback.of_iso_comparison
- \+/\- *def* preserves_pullback_symmetry
- \+/\- *def* is_colimit_of_has_pushout_of_preserves_colimit
- \+/\- *def* preserves_pushout.of_iso_comparison
- \+/\- *def* preserves_pushout_symmetry

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* walking_cospan_functor_one
- \+ *lemma* walking_cospan_functor_left
- \+ *lemma* walking_cospan_functor_right
- \+ *lemma* walking_cospan_functor_id
- \+ *lemma* walking_cospan_functor_inl
- \+ *lemma* walking_cospan_functor_inr
- \+ *lemma* walking_span_functor_zero
- \+ *lemma* walking_span_functor_left
- \+ *lemma* walking_span_functor_right
- \+ *lemma* walking_span_functor_id
- \+ *lemma* walking_span_functor_fst
- \+ *lemma* walking_span_functor_snd
- \+ *def* walking_cospan_functor
- \+ *def* walking_cospan_equiv
- \+ *def* walking_span_functor
- \+ *def* walking_span_equiv



## [2022-01-04 07:46:59](https://github.com/leanprover-community/mathlib/commit/044c1de)
feat(analysis/special_functions/trigonometric): a few lemmas ([#11217](https://github.com/leanprover-community/mathlib/pull/11217))
Add a few trivial lemmas about `arcsin`/`arccos`.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/inverse.lean
- \+ *lemma* pi_div_four_le_arcsin
- \+ *lemma* arccos_le_pi_div_two
- \+ *lemma* arccos_le_pi_div_four



## [2022-01-04 07:46:58](https://github.com/leanprover-community/mathlib/commit/3045014)
feat(algebra/order/ring): turn `mul_self_pos` into an `iff` ([#11216](https://github.com/leanprover-community/mathlib/pull/11216))
#### Estimated changes
Modified archive/imo/imo1998_q2.lean

Modified src/algebra/order/ring.lean
- \+/\- *lemma* mul_self_pos
- \+/\- *lemma* mul_self_pos

Modified src/analysis/inner_product_space/conformal_linear_map.lean

Modified src/linear_algebra/quadratic_form/basic.lean



## [2022-01-04 07:46:57](https://github.com/leanprover-community/mathlib/commit/85784b0)
feat(linear_algebra/determinant): `det_units_smul` and `det_is_unit_smul` ([#11206](https://github.com/leanprover-community/mathlib/pull/11206))
Add lemmas giving the determinant of a basis constructed with
`units_smul` or `is_unit_smul` with respect to the original basis.
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* basis.det_units_smul
- \+ *lemma* basis.det_is_unit_smul



## [2022-01-04 07:46:56](https://github.com/leanprover-community/mathlib/commit/1fc7a93)
chore(topology/metric_space/hausdorff_distance): slightly tidy some proofs ([#11203](https://github.com/leanprover-community/mathlib/pull/11203))
#### Estimated changes
Modified src/topology/metric_space/hausdorff_distance.lean



## [2022-01-04 07:46:55](https://github.com/leanprover-community/mathlib/commit/9d1503a)
feat(field_theory.intermediate_field): add intermediate_field.map_map ([#11020](https://github.com/leanprover-community/mathlib/pull/11020))
#### Estimated changes
Modified src/data/polynomial/eval.lean

Modified src/field_theory/intermediate_field.lean
- \+ *lemma* map_map

Modified src/field_theory/primitive_element.lean



## [2022-01-04 06:31:42](https://github.com/leanprover-community/mathlib/commit/71dc1ea)
feat(topology/maps): preimage of closure/frontier under an open map ([#11189](https://github.com/leanprover-community/mathlib/pull/11189))
We had lemmas about `interior`. Add versions about `frontier` and `closure`.
#### Estimated changes
Modified src/analysis/normed_space/add_torsor_bases.lean

Modified src/topology/maps.lean
- \+ *lemma* maps_to_interior
- \+ *lemma* of_sections
- \+/\- *lemma* interior_preimage_subset_preimage_interior
- \+/\- *lemma* preimage_interior_eq_interior_preimage
- \+ *lemma* preimage_closure_subset_closure_preimage
- \+ *lemma* preimage_closure_eq_closure_preimage
- \+ *lemma* preimage_frontier_subset_frontier_preimage
- \+ *lemma* preimage_frontier_eq_frontier_preimage
- \+/\- *lemma* interior_preimage_subset_preimage_interior
- \+/\- *lemma* preimage_interior_eq_interior_preimage



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
- \+ *lemma* coe_subtype
- \- *lemma* subtype_eq_val

Modified src/linear_algebra/basis.lean

Modified src/linear_algebra/finite_dimensional.lean



## [2022-01-04 01:48:54](https://github.com/leanprover-community/mathlib/commit/4daaff0)
feat(data/nat/prime): factors sublist of product ([#11104](https://github.com/leanprover-community/mathlib/pull/11104))
This PR changes the existing `factors_subset_right` to give a stronger sublist conclusion (which trivially can be used to reproduce the subst version).
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* factors_sublist_right
- \+ *lemma* factors_sublist_of_dvd
- \+/\- *lemma* factors_subset_right
- \+/\- *lemma* factors_subset_of_dvd
- \+/\- *lemma* factors_subset_right
- \+/\- *lemma* factors_subset_of_dvd



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
- \+/\- *def* graph
- \+/\- *def* graph

Modified src/order/basic.lean

Modified src/order/lexicographic.lean
- \+ *lemma* to_lex_symm_eq
- \+ *lemma* of_lex_symm_eq
- \+ *lemma* to_lex_of_lex
- \+ *lemma* of_lex_to_lex
- \+ *lemma* to_lex_inj
- \+ *lemma* of_lex_inj
- \+ *lemma* le_iff
- \+ *lemma* lt_iff
- \- *lemma* lex_le_iff
- \- *lemma* lex_lt_iff
- \+/\- *def* lex
- \+ *def* to_lex
- \+ *def* of_lex
- \+/\- *def* lex

Modified src/order/locally_finite.lean

Modified src/tactic/linarith/preprocessing.lean



## [2022-01-03 18:55:41](https://github.com/leanprover-community/mathlib/commit/9d0fd52)
feat(measure_theory/function/lp_space): use has_measurable_add2 instead of second_countable_topology ([#11202](https://github.com/leanprover-community/mathlib/pull/11202))
Use the weaker assumption `[has_measurable_add₂ E]` instead of `[second_countable_topology E]` in 4 lemmas.
#### Estimated changes
Modified src/measure_theory/function/lp_space.lean
- \+/\- *lemma* snorm'_sum_le
- \+/\- *lemma* snorm_sum_le
- \+/\- *lemma* snorm'_sum_le
- \+/\- *lemma* snorm_sum_le



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
- \+/\- *lemma* is_root_cyclotomic_iff
- \+/\- *lemma* is_root_cyclotomic_iff

Modified src/ring_theory/polynomial/cyclotomic/eval.lean



## [2022-01-03 14:30:17](https://github.com/leanprover-community/mathlib/commit/236d978)
feat(linear_algebra/matrix/basis): `to_matrix_units_smul` and `to_matrix_is_unit_smul` ([#11191](https://github.com/leanprover-community/mathlib/pull/11191))
Add lemmas that applying `to_matrix` to a basis constructed with
`units_smul` or `is_unit_smul` produces the corresponding diagonal
matrix.
#### Estimated changes
Modified src/linear_algebra/matrix/basis.lean
- \+ *lemma* to_matrix_units_smul
- \+ *lemma* to_matrix_is_unit_smul



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
- \+ *lemma* prime.dvd_finset_prod_iff
- \+ *lemma* prime.dvd_finsupp_prod_iff
- \+/\- *lemma* prime.dvd_prod_iff
- \+ *lemma* nat.prime.dvd_finset_prod_iff
- \+ *lemma* nat.prime.dvd_finsupp_prod_iff
- \+/\- *lemma* prime.dvd_prod_iff



## [2022-01-03 10:32:11](https://github.com/leanprover-community/mathlib/commit/a813cf5)
chore(algebra/algebra/spectrum): move `exists_spectrum_of_is_alg_closed_of_finite_dimensional` ([#10919](https://github.com/leanprover-community/mathlib/pull/10919))
Move a lemma from `field_theory/is_alg_closed/basic` into `algebra/algebra/spectrum` which belongs in this relatively new file. Also, rename (now in `spectrum` namespace) and refactor it slightly; and update the two references to it accordingly.
- [x] depends on: [#10783](https://github.com/leanprover-community/mathlib/pull/10783)
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean
- \+ *lemma* nonempty_of_is_alg_closed_of_finite_dimensional

Modified src/category_theory/preadditive/schur.lean

Modified src/field_theory/is_alg_closed/basic.lean
- \- *lemma* exists_spectrum_of_is_alg_closed_of_finite_dimensional

Modified src/linear_algebra/eigenspace.lean



## [2022-01-03 07:35:22](https://github.com/leanprover-community/mathlib/commit/49bf3d3)
feat(data/polynomial/taylor): taylor_mul ([#11193](https://github.com/leanprover-community/mathlib/pull/11193))
#### Estimated changes
Modified src/data/polynomial/taylor.lean
- \+ *lemma* taylor_mul



## [2022-01-03 07:35:21](https://github.com/leanprover-community/mathlib/commit/a49ee49)
feat(data/finset/functor): Functor structures for `finset` ([#10980](https://github.com/leanprover-community/mathlib/pull/10980))
This defines the monad, the commutative applicative and the (almost) traversable functor structures on `finset`.
It all goes in a new file `data.finset.functor` and picks up the `functor` instance that was stranded in `data.finset.basic` by Scott in [#2997](https://github.com/leanprover-community/mathlib/pull/2997).
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* mem_image
- \+ *lemma* mem_image_of_mem
- \+ *lemma* mem_image_const
- \+ *lemma* mem_image_const_self
- \- *theorem* mem_image
- \- *theorem* mem_image_of_mem

Created src/data/finset/functor.lean
- \+ *lemma* fmap_def
- \+ *lemma* pure_def
- \+ *lemma* seq_def
- \+ *lemma* seq_left_def
- \+ *lemma* seq_right_def
- \+ *lemma* bind_def
- \+ *lemma* id_traverse
- \+ *lemma* map_comp_coe
- \+ *lemma* map_traverse
- \+ *def* traverse

Modified src/data/finset/lattice.lean
- \+ *lemma* sup_bot
- \+ *lemma* inf_top
- \+ *lemma* sup_singleton''



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
- \+ *lemma* eventually_nhds_within_of_forall
- \- *lemma* eventually_nhds_with_of_forall



## [2022-01-02 17:21:44](https://github.com/leanprover-community/mathlib/commit/3f77761)
feat(ring_theory/algebraic): algebraic functions ([#11156](https://github.com/leanprover-community/mathlib/pull/11156))
Accessible via a new `algebra (polynomial R) (R → R)`
and a generalization that gives `algebra (polynomial R) (S → S)` when `[algebra R S]`.
#### Estimated changes
Modified src/ring_theory/algebraic.lean
- \+ *lemma* polynomial_smul_apply
- \+ *lemma* polynomial_smul_apply'
- \+ *lemma* polynomial.algebra_map_pi_eq_aeval
- \+ *lemma* polynomial.algebra_map_pi_self_eq_eval



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
- \+/\- *lemma* monotone.ge_of_tendsto
- \+/\- *lemma* monotone.le_of_tendsto
- \+ *lemma* is_lub_of_tendsto_at_top
- \+ *lemma* is_glb_of_tendsto_at_bot
- \+ *lemma* is_lub_of_tendsto_at_bot
- \+ *lemma* is_glb_of_tendsto_at_top
- \+/\- *lemma* monotone.ge_of_tendsto
- \+/\- *lemma* monotone.le_of_tendsto
- \- *lemma* is_lub_of_tendsto
- \- *lemma* is_glb_of_tendsto



## [2022-01-01 19:07:15](https://github.com/leanprover-community/mathlib/commit/02d02df)
chore(measure_theory): fix TC assumptions in 2 lemmas ([#11185](https://github.com/leanprover-community/mathlib/pull/11185))
With new assumptions, these lemmas work, e.g., for `β = ι → ℝ`.
#### Estimated changes
Modified src/measure_theory/integral/integrable_on.lean



## [2022-01-01 19:07:13](https://github.com/leanprover-community/mathlib/commit/c1b1041)
feat(topology/metric_space/basic): add `fin.dist_insert_nth_insert_nth` ([#11183](https://github.com/leanprover-community/mathlib/pull/11183))
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* nndist_pi_le_iff
- \+ *lemma* fin.nndist_insert_nth_insert_nth
- \+ *lemma* fin.dist_insert_nth_insert_nth



## [2022-01-01 17:09:52](https://github.com/leanprover-community/mathlib/commit/6486e9b)
chore(order/rel_classes): Removed unnecessary `classical` ([#11180](https://github.com/leanprover-community/mathlib/pull/11180))
Not sure what that was doing here.
#### Estimated changes
Modified src/order/rel_classes.lean



## [2022-01-01 15:44:59](https://github.com/leanprover-community/mathlib/commit/93cf56c)
feat(algebraic_geometry/*): The map `F.stalk y ⟶ F.stalk x` for `x ⤳ y` ([#11144](https://github.com/leanprover-community/mathlib/pull/11144))
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+ *lemma* le_iff_specializes
- \+ *def* localization_map_of_specializes

Modified src/algebraic_geometry/stalks.lean
- \+ *lemma* stalk_specializes_stalk_map

Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *lemma* stalk_to_fiber_ring_hom_localization_to_stalk
- \+ *lemma* localization_to_stalk_stalk_to_fiber_ring_hom
- \+ *lemma* to_stalk_stalk_specializes
- \+ *lemma* localization_to_stalk_stalk_specializes
- \+ *lemma* stalk_specializes_stalk_to_fiber

Modified src/topology/sheaves/stalks.lean
- \+ *lemma* germ_stalk_specializes
- \+ *lemma* germ_stalk_specializes'
- \+ *lemma* stalk_specializes_stalk_functor_map
- \+ *lemma* stalk_specializes_stalk_pushforward
- \+ *def* stalk_specializes



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
- \+ *lemma* has_lines.line_count_eq_point_count
- \+ *lemma* has_points.line_count_eq_point_count



## [2022-01-01 13:55:31](https://github.com/leanprover-community/mathlib/commit/a6c82af)
feat(group_theory/specific_groups/*): computes the exponents of the dihedral and generalised quaternion groups ([#11166](https://github.com/leanprover-community/mathlib/pull/11166))
This PR shows that the exponent of the dihedral group of order `2n` is equal to `lcm n 2` and that the exponent of the generalised quaternion group of order `4n` is `2 * lcm n 2`
#### Estimated changes
Modified src/group_theory/specific_groups/dihedral.lean
- \+ *lemma* exponent

Modified src/group_theory/specific_groups/quaternion.lean
- \+/\- *lemma* order_of_a_one
- \+ *lemma* exponent
- \+/\- *lemma* order_of_a_one



## [2022-01-01 13:55:30](https://github.com/leanprover-community/mathlib/commit/ad76a5e)
feat(data/nat/log): log_mul, log_div ([#11164](https://github.com/leanprover-community/mathlib/pull/11164))
Even with division over natural, the log "spec" holds.
#### Estimated changes
Modified src/data/nat/log.lean
- \+ *lemma* log_mul_base
- \+ *lemma* log_div_mul_self
- \+ *lemma* log_div_base



## [2022-01-01 11:59:04](https://github.com/leanprover-community/mathlib/commit/23b01cc)
feat(algebraic_geometry): The function field of an integral scheme ([#11147](https://github.com/leanprover-community/mathlib/pull/11147))
#### Estimated changes
Modified src/algebra/field/basic.lean

Created src/algebraic_geometry/function_field.lean
- \+ *lemma* germ_injective_of_is_integral
- \+ *lemma* Scheme.germ_to_function_field_injective

Modified src/algebraic_geometry/prime_spectrum/basic.lean

Modified src/algebraic_geometry/properties.lean
- \+ *lemma* affine_is_reduced_iff
- \+ *lemma* is_integral_of_is_irreducible_is_reduced
- \+ *lemma* is_integral_iff_is_irreducible_and_is_reduced
- \+ *lemma* is_integral_of_open_immersion
- \+ *lemma* affine_is_integral_iff
- \+ *lemma* map_injective_of_is_integral

Modified src/topology/opens.lean
- \+ *lemma* coe_top
- \+ *lemma* not_nonempty_iff_eq_bot
- \+ *lemma* ne_bot_iff_nonempty



## [2022-01-01 02:32:45](https://github.com/leanprover-community/mathlib/commit/1594b0c)
feat(normed_space/lp_space): Lp space for `Π i, E i` ([#11015](https://github.com/leanprover-community/mathlib/pull/11015))
For a family `Π i, E i` of normed spaces, define the subgroup with finite lp norm, and prove it is a `normed_group`.  Many parts adapted from the development of `measure_theory.Lp` by @RemyDegenne.
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Lp.20space
#### Estimated changes
Created src/analysis/normed_space/lp_space.lean
- \+ *lemma* mem_ℓp_zero_iff
- \+ *lemma* mem_ℓp_zero
- \+ *lemma* mem_ℓp_infty_iff
- \+ *lemma* mem_ℓp_infty
- \+ *lemma* mem_ℓp_gen_iff
- \+ *lemma* mem_ℓp_gen
- \+ *lemma* zero_mem_ℓp
- \+ *lemma* zero_mem_ℓp'
- \+ *lemma* finite_dsupport
- \+ *lemma* bdd_above
- \+ *lemma* summable
- \+ *lemma* neg
- \+ *lemma* neg_iff
- \+ *lemma* of_exponent_ge
- \+ *lemma* add
- \+ *lemma* sub
- \+ *lemma* finset_sum
- \+ *lemma* const_smul
- \+ *lemma* const_mul
- \+ *lemma* ext
- \+ *lemma* eq_zero'
- \+ *lemma* coe_fn_zero
- \+ *lemma* coe_fn_neg
- \+ *lemma* coe_fn_add
- \+ *lemma* coe_fn_sub
- \+ *lemma* norm_eq_card_dsupport
- \+ *lemma* norm_eq_csupr
- \+ *lemma* is_lub_norm
- \+ *lemma* norm_eq_tsum_rpow
- \+ *lemma* norm_rpow_eq_tsum
- \+ *lemma* has_sum_norm
- \+ *lemma* norm_nonneg'
- \+ *lemma* norm_zero
- \+ *lemma* norm_eq_zero_iff
- \+ *lemma* eq_zero_iff_coe_fn_eq_zero
- \+ *lemma* norm_neg
- \+ *lemma* mem_lp_const_smul
- \+ *lemma* coe_lp_submodule
- \+ *lemma* coe_fn_smul
- \+ *lemma* norm_const_smul
- \+ *def* mem_ℓp
- \+ *def* pre_lp
- \+ *def* lp
- \+ *def* lp_submodule

Modified src/analysis/normed_space/pi_Lp.lean

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* rpow_le_rpow_of_exponent_ge'
- \+ *lemma* rpow_left_inj_on

Modified src/data/set/basic.lean

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum_zero_iff_of_nonneg

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* eventually_lt_of_tendsto_lt
- \+ *lemma* eventually_gt_of_tendsto_gt



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
- \+ *lemma* Union_pi_of_monotone
- \+ *lemma* Union_univ_pi_of_monotone

Modified src/data/set/intervals/disjoint.lean
- \+/\- *lemma* Union_Ico_eq_Iio_self_iff
- \+/\- *lemma* Union_Ioc_eq_Ioi_self_iff
- \+/\- *lemma* bUnion_Ico_eq_Iio_self_iff
- \+/\- *lemma* bUnion_Ioc_eq_Ioi_self_iff
- \+ *lemma* is_glb.bUnion_Ioi_eq
- \+ *lemma* is_glb.Union_Ioi_eq
- \+ *lemma* is_lub.bUnion_Iio_eq
- \+ *lemma* is_lub.Union_Iio_eq
- \+/\- *lemma* Union_Ico_eq_Iio_self_iff
- \+/\- *lemma* Union_Ioc_eq_Ioi_self_iff
- \+/\- *lemma* bUnion_Ico_eq_Iio_self_iff
- \+/\- *lemma* bUnion_Ioc_eq_Ioi_self_iff

Modified src/data/set/intervals/monotone.lean
- \+ *lemma* antitone_Ici
- \+ *lemma* monotone_Iic
- \+ *lemma* antitone_Ioi
- \+ *lemma* monotone_Iio
- \+ *lemma* Union_Ioo_of_mono_of_is_glb_of_is_lub
- \+/\- *def* order_iso_Ioo_neg_one_one
- \+/\- *def* order_iso_Ioo_neg_one_one

Modified src/data/set/lattice.lean
- \+ *theorem* _root_.monotone.inter
- \+ *theorem* _root_.antitone.inter
- \+ *theorem* _root_.monotone.union
- \+ *theorem* _root_.antitone.union
- \+ *theorem* antitone_set_of
- \- *theorem* monotone_inter
- \- *theorem* monotone_union

Modified src/order/lattice.lean
- \+ *lemma* map_sup_le
- \+ *lemma* map_sup
- \+ *lemma* le_map_inf
- \+ *lemma* map_inf

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
- \+ *lemma* ne_of_adj_of_not_adj
- \+ *lemma* common_neighbors_top_eq
- \+ *lemma* neighbor_finset_def
- \+ *lemma* is_regular_of_degree.degree_eq
- \+ *lemma* is_regular_of_degree.compl
- \+ *lemma* neighbor_finset_compl
- \+ *lemma* bot_degree
- \+ *lemma* is_regular_of_degree.top
- \+ *lemma* card_common_neighbors_top
- \- *lemma* is_regular_of_degree_eq
- \- *lemma* is_regular_compl_of_is_regular
- \- *lemma* complete_graph_is_regular

Modified src/combinatorics/simple_graph/strongly_regular.lean
- \+ *lemma* bot_strongly_regular
- \+ *lemma* is_SRG_with.top
- \+ *lemma* is_SRG_with.card_neighbor_finset_union_eq
- \+ *lemma* is_SRG_with.card_neighbor_finset_union_of_not_adj
- \+ *lemma* is_SRG_with.card_neighbor_finset_union_of_adj
- \+ *lemma* compl_neighbor_finset_sdiff_inter_eq
- \+ *lemma* sdiff_compl_neighbor_finset_inter_eq
- \+ *lemma* is_SRG_with.compl_is_regular
- \+ *lemma* is_SRG_with.card_common_neighbors_eq_of_adj_compl
- \+ *lemma* is_SRG_with.card_common_neighbors_eq_of_not_adj_compl
- \+ *lemma* is_SRG_with.compl
- \- *lemma* complete_strongly_regular

Modified src/data/fintype/basic.lean
- \+/\- *lemma* union_compl
- \+ *lemma* inter_compl
- \+ *lemma* compl_union
- \+ *lemma* compl_inter
- \+/\- *lemma* union_compl

Modified src/data/set/finite.lean
- \+ *lemma* to_finset_singleton
- \+ *lemma* to_finset_sdiff

Modified src/measure_theory/measure/outer_measure.lean

