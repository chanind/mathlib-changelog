## [2020-12-31 19:17:29](https://github.com/leanprover-community/mathlib/commit/54bf708)
feat(logic/basic): exists_unique_false simp lemma ([#5544](https://github.com/leanprover-community/mathlib/pull/5544))
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* exists_unique_false



## [2020-12-31 16:30:28](https://github.com/leanprover-community/mathlib/commit/0830bfd)
refactor(analysis/analytic/basic): redefine `formal_multilinear_series.radius` ([#5349](https://github.com/leanprover-community/mathlib/pull/5349))
With the new definition, (a) some proofs get much shorter; (b) we
don't need `rpow` in `analytic/basic`.
#### Estimated changes
Modified src/algebra/big_operators/order.lean

Modified src/analysis/analytic/basic.lean
- \+/\- *lemma* le_radius_of_bound
- \+ *lemma* le_radius_of_bound_nnreal
- \+ *lemma* le_radius_of_is_O
- \+ *lemma* is_o_of_lt_radius
- \+ *lemma* is_o_one_of_lt_radius
- \+ *lemma* norm_mul_pow_le_mul_pow_of_lt_radius
- \+ *lemma* lt_radius_of_is_O
- \+ *lemma* norm_mul_pow_le_of_lt_radius
- \+ *lemma* nnnorm_mul_pow_le_of_lt_radius
- \+/\- *lemma* radius_neg
- \+/\- *lemma* le_radius_of_bound
- \- *lemma* bound_of_lt_radius
- \- *lemma* geometric_bound_of_lt_radius
- \+/\- *lemma* radius_neg
- \+/\- *def* change_origin
- \+/\- *def* change_origin

Modified src/analysis/analytic/composition.lean

Created src/analysis/analytic/radius_liminf.lean
- \+ *lemma* radius_eq_liminf

Modified src/analysis/specific_limits.lean



## [2020-12-31 10:07:03](https://github.com/leanprover-community/mathlib/commit/10f6c15)
chore(analysis/normed_space/inner_product): notation for orthogonal complement ([#5536](https://github.com/leanprover-community/mathlib/pull/5536))
Notation for `submodule.orthogonal`, so that one can write `Kᗮ` instead of `K.orthogonal`.
Simultaneous PR
https://github.com/leanprover/vscode-lean/pull/246
adds `\perp` as vscode shorthand for this symbol.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/New.20linear.20algebra.20notation)
#### Estimated changes
Modified src/analysis/normed_space/dual.lean

Modified src/analysis/normed_space/inner_product.lean
- \+/\- *lemma* submodule.mem_orthogonal
- \+/\- *lemma* submodule.mem_orthogonal'
- \+/\- *lemma* submodule.orthogonal_disjoint
- \+/\- *lemma* orthogonal_eq_inter
- \+/\- *lemma* submodule.is_closed_orthogonal
- \+/\- *lemma* submodule.orthogonal_le
- \+/\- *lemma* submodule.le_orthogonal_orthogonal
- \+/\- *lemma* submodule.inf_orthogonal
- \+/\- *lemma* submodule.infi_orthogonal
- \+/\- *lemma* submodule.Inf_orthogonal
- \+/\- *lemma* submodule.orthogonal_orthogonal
- \+/\- *lemma* submodule.top_orthogonal_eq_bot
- \+/\- *lemma* submodule.bot_orthogonal_eq_top
- \+/\- *lemma* submodule.mem_orthogonal
- \+/\- *lemma* submodule.mem_orthogonal'
- \+/\- *lemma* submodule.orthogonal_disjoint
- \+/\- *lemma* orthogonal_eq_inter
- \+/\- *lemma* submodule.is_closed_orthogonal
- \+/\- *lemma* submodule.orthogonal_le
- \+/\- *lemma* submodule.le_orthogonal_orthogonal
- \+/\- *lemma* submodule.inf_orthogonal
- \+/\- *lemma* submodule.infi_orthogonal
- \+/\- *lemma* submodule.Inf_orthogonal
- \+/\- *lemma* submodule.orthogonal_orthogonal
- \+/\- *lemma* submodule.top_orthogonal_eq_bot
- \+/\- *lemma* submodule.bot_orthogonal_eq_top

Modified src/geometry/euclidean/basic.lean

Modified src/geometry/euclidean/monge_point.lean



## [2020-12-31 08:49:08](https://github.com/leanprover-community/mathlib/commit/cca6365)
feat(field_theory/galois): is_galois.tfae ([#5542](https://github.com/leanprover-community/mathlib/pull/5542))
This is a TFAE theorem for is_galois
#### Estimated changes
Modified src/field_theory/galois.lean
- \+ *theorem* tfae



## [2020-12-31 06:04:17](https://github.com/leanprover-community/mathlib/commit/b04aeb5)
chore(algebra): move lemmas from ring_theory.algebra_tower to algebra.algebra.tower ([#5506](https://github.com/leanprover-community/mathlib/pull/5506))
Moved some basic lemmas from `ring_theory.algebra_tower` to `algebra.algebra.tower`.
#### Estimated changes
Created src/algebra/algebra/tower.lean
- \+ *lemma* lsmul_coe
- \+ *lemma* algebra.ext
- \+ *lemma* to_alg_hom_apply
- \+ *lemma* coe_to_alg_hom
- \+ *lemma* coe_to_alg_hom'
- \+ *lemma* restrict_base_apply
- \+ *lemma* coe_restrict_base
- \+ *lemma* coe_restrict_base'
- \+ *lemma* res_top
- \+ *lemma* mem_res
- \+ *lemma* res_inj
- \+ *theorem* algebra_map_smul
- \+ *theorem* of_algebra_map_eq
- \+ *theorem* of_algebra_map_eq'
- \+ *theorem* algebra_map_eq
- \+ *theorem* algebra_map_apply
- \+ *theorem* algebra_comap_eq
- \+ *theorem* range_under_adjoin
- \+ *theorem* smul_mem_span_smul_of_mem
- \+ *theorem* smul_mem_span_smul
- \+ *theorem* smul_mem_span_smul'
- \+ *theorem* span_smul
- \+ *def* lsmul
- \+ *def* to_alg_hom
- \+ *def* restrict_base
- \+ *def* res
- \+ *def* of_under

Modified src/ring_theory/algebra_tower.lean
- \- *lemma* algebra.ext
- \- *lemma* to_alg_hom_apply
- \- *lemma* restrict_base_apply
- \- *lemma* res_top
- \- *lemma* mem_res
- \- *lemma* res_inj
- \- *theorem* algebra_map_smul
- \- *theorem* smul_left_comm
- \- *theorem* of_algebra_map_eq
- \- *theorem* algebra_map_eq
- \- *theorem* algebra_map_apply
- \- *theorem* algebra_comap_eq
- \- *theorem* range_under_adjoin
- \- *theorem* smul_mem_span_smul_of_mem
- \- *theorem* smul_mem_span_smul
- \- *theorem* smul_mem_span_smul'
- \- *theorem* span_smul
- \- *def* to_alg_hom
- \- *def* restrict_base
- \- *def* res
- \- *def* of_under



## [2020-12-31 02:53:26](https://github.com/leanprover-community/mathlib/commit/a40f31f)
feat(data/tprod): finite products of types ([#5385](https://github.com/leanprover-community/mathlib/pull/5385))
This PR defined `list.tprod` as a finite product of types to transfer results from binary products to finitary products.
See module doc for more info.
#### Estimated changes
Created src/data/tprod.lean
- \+ *lemma* fst_mk
- \+ *lemma* snd_mk
- \+ *lemma* elim_self
- \+ *lemma* elim_of_ne
- \+ *lemma* elim_of_mem
- \+ *lemma* elim_mk
- \+ *lemma* ext
- \+ *lemma* mk_elim
- \+ *lemma* mk_preimage_tprod
- \+ *lemma* elim_preimage_pi
- \+ *def* tprod
- \+ *def* pi_equiv_tprod



## [2020-12-31 01:37:37](https://github.com/leanprover-community/mathlib/commit/611b73e)
chore(scripts): update nolints.txt ([#5540](https://github.com/leanprover-community/mathlib/pull/5540))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-30 23:15:52](https://github.com/leanprover-community/mathlib/commit/9c46cad)
feat(field_theory/algebraic_closure): algebraically closed fields have no nontrivial algebraic extensions ([#5537](https://github.com/leanprover-community/mathlib/pull/5537))
#### Estimated changes
Modified src/field_theory/algebraic_closure.lean
- \+ *lemma* algebra_map_surjective_of_is_integral
- \+ *lemma* algebra_map_surjective_of_is_algebraic

Modified src/ring_theory/algebraic.lean
- \+ *lemma* is_algebraic_iff_is_integral'



## [2020-12-30 20:43:17](https://github.com/leanprover-community/mathlib/commit/6e0d0fa)
chore(algebra/field): use `K` as a type variable ([#5535](https://github.com/leanprover-community/mathlib/pull/5535))
#### Estimated changes
Modified src/algebra/field.lean
- \+/\- *lemma* inverse_eq_has_inv
- \+/\- *lemma* mul_div_assoc'
- \+/\- *lemma* one_div_neg_one_eq_neg_one
- \+/\- *lemma* one_div_neg_eq_neg_one_div
- \+/\- *lemma* div_neg_eq_neg_div
- \+/\- *lemma* neg_div
- \+/\- *lemma* neg_div'
- \+/\- *lemma* neg_div_neg_eq
- \+/\- *lemma* div_add_div_same
- \+/\- *lemma* div_sub_div_same
- \+/\- *lemma* add_div
- \+/\- *lemma* sub_div
- \+/\- *lemma* div_neg
- \+/\- *lemma* add_div_eq_mul_add_div
- \+/\- *lemma* one_div_add_one_div
- \+/\- *lemma* div_add_div
- \+/\- *lemma* div_sub_div
- \+/\- *lemma* inv_add_inv
- \+/\- *lemma* inv_sub_inv
- \+/\- *lemma* add_div'
- \+/\- *lemma* sub_div'
- \+/\- *lemma* div_add'
- \+/\- *lemma* div_sub'
- \+/\- *lemma* inverse_eq_has_inv
- \+/\- *lemma* mul_div_assoc'
- \+/\- *lemma* one_div_neg_one_eq_neg_one
- \+/\- *lemma* one_div_neg_eq_neg_one_div
- \+/\- *lemma* div_neg_eq_neg_div
- \+/\- *lemma* neg_div
- \+/\- *lemma* neg_div'
- \+/\- *lemma* neg_div_neg_eq
- \+/\- *lemma* div_add_div_same
- \+/\- *lemma* div_sub_div_same
- \+/\- *lemma* add_div
- \+/\- *lemma* sub_div
- \+/\- *lemma* div_neg
- \+/\- *lemma* add_div_eq_mul_add_div
- \+/\- *lemma* one_div_add_one_div
- \+/\- *lemma* div_add_div
- \+/\- *lemma* div_sub_div
- \+/\- *lemma* inv_add_inv
- \+/\- *lemma* inv_sub_inv
- \+/\- *lemma* add_div'
- \+/\- *lemma* sub_div'
- \+/\- *lemma* div_add'
- \+/\- *lemma* div_sub'



## [2020-12-30 20:43:15](https://github.com/leanprover-community/mathlib/commit/9988193)
feat(measure_theory): various additions ([#5389](https://github.com/leanprover-community/mathlib/pull/5389))
Some computations of measures on non-measurable sets
Some more measurability lemmas for pi-types
Cleanup in `measure_space`
#### Estimated changes
Modified src/data/equiv/list.lean

Modified src/measure_theory/borel_space.lean

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* is_measurable.Union_fintype
- \+ *lemma* is_measurable.Inter_fintype
- \+ *lemma* nonempty_measurable_superset
- \+ *lemma* measurable_pi_iff
- \+ *lemma* measurable.eval
- \+ *lemma* measurable_update
- \+ *lemma* is_measurable.pi
- \+ *lemma* is_measurable.pi_univ
- \+ *lemma* is_measurable_pi_of_nonempty
- \+/\- *lemma* is_measurable_pi
- \+ *lemma* is_measurable.pi_fintype
- \+ *lemma* coe_mk
- \+ *lemma* coe_symm_mk
- \+/\- *lemma* is_measurable_pi
- \+ *def* Pi_congr_right

Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* of_measurable_apply
- \+/\- *lemma* to_outer_measure_injective
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* to_outer_measure_apply
- \+/\- *lemma* measure_eq_trim
- \+/\- *lemma* measure_eq_infi
- \+ *lemma* measure_eq_infi'
- \+/\- *lemma* exists_is_measurable_superset_of_measure_eq_zero
- \+/\- *lemma* exists_is_measurable_superset_iff_measure_eq_zero
- \+/\- *lemma* measure_Union_null
- \+/\- *lemma* measure_Union_null_iff
- \+/\- *lemma* measure_union_null
- \+/\- *lemma* measure_union_null_iff
- \+/\- *lemma* measure_Union
- \+/\- *lemma* measure_diff
- \+/\- *lemma* measure_compl
- \+/\- *lemma* measure_eq_inter_diff
- \+/\- *lemma* measure_union_add_inter
- \+/\- *lemma* tendsto_measure_Union
- \+/\- *lemma* tendsto_measure_Inter
- \+/\- *lemma* measure_if
- \+/\- *lemma* le_to_outer_measure_caratheodory
- \+/\- *lemma* to_measure_to_outer_measure
- \+/\- *lemma* to_measure_apply
- \+/\- *lemma* le_to_measure_apply
- \+/\- *lemma* to_outer_measure_to_measure
- \+/\- *lemma* Inf_apply
- \+/\- *lemma* measure_univ_eq_zero
- \+/\- *lemma* le_lift_linear_apply
- \+/\- *lemma* restrict_apply
- \+/\- *lemma* restrict_restrict
- \+/\- *lemma* restrict_apply_eq_zero
- \+/\- *lemma* restrict_apply_eq_zero'
- \+/\- *lemma* restrict_eq_zero
- \+/\- *lemma* restrict_union_apply
- \+/\- *lemma* restrict_union
- \+/\- *lemma* restrict_union_add_inter
- \+/\- *lemma* restrict_add_restrict_compl
- \+/\- *lemma* restrict_compl_add_restrict
- \+/\- *lemma* restrict_Union_apply
- \+/\- *lemma* restrict_Union_apply_eq_supr
- \+/\- *lemma* map_comap_subtype_coe
- \+/\- *lemma* restrict_le_self
- \+/\- *lemma* restrict_congr_meas
- \+/\- *lemma* restrict_congr_mono
- \+/\- *lemma* restrict_union_congr
- \+/\- *lemma* restrict_to_outer_measure_eq_to_outer_measure_restrict
- \+/\- *lemma* restrict_Inf_eq_Inf_restrict
- \+/\- *lemma* dirac_apply'
- \+/\- *lemma* dirac_apply
- \+/\- *lemma* dirac_apply_of_mem
- \+/\- *lemma* sum_apply
- \+/\- *lemma* le_sum
- \+/\- *lemma* restrict_Union
- \+/\- *lemma* restrict_Union_le
- \+/\- *lemma* restrict_sum
- \+/\- *lemma* count_apply
- \+/\- *lemma* count_apply_infinite
- \+/\- *lemma* count_apply_eq_top
- \+/\- *lemma* count_apply_lt_top
- \+/\- *lemma* mem_cofinite
- \+/\- *lemma* compl_mem_cofinite
- \+/\- *lemma* ae_of_all
- \+/\- *lemma* ae_all_iff
- \+/\- *lemma* ae_ball_iff
- \+/\- *lemma* ae_eq_refl
- \+/\- *lemma* ae_eq_symm
- \+/\- *lemma* ae_eq_trans
- \+/\- *lemma* ae_eq_empty
- \+/\- *lemma* ae_le_set
- \+/\- *lemma* union_ae_eq_right
- \+/\- *lemma* diff_ae_eq_self
- \+/\- *lemma* mem_ae_map_iff
- \+/\- *lemma* ae_map_iff
- \+/\- *lemma* ae_restrict_iff
- \+/\- *lemma* ae_restrict_eq
- \+/\- *lemma* mem_dirac_ae_iff
- \+/\- *lemma* eventually_eq_dirac
- \+/\- *lemma* eventually_eq_dirac'
- \+/\- *lemma* measure_mono_ae
- \+/\- *lemma* measure_congr
- \+/\- *lemma* restrict_mono_ae
- \+/\- *lemma* restrict_congr_set
- \+/\- *lemma* measure_countable
- \+/\- *lemma* measure_finite
- \+/\- *lemma* supr_restrict_spanning_sets
- \+/\- *lemma* finite_at_principal
- \+/\- *lemma* sub_apply
- \+/\- *lemma* metric.bounded.finite_measure
- \+/\- *lemma* of_measurable_apply
- \+/\- *lemma* to_outer_measure_injective
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* to_outer_measure_apply
- \+/\- *lemma* measure_eq_trim
- \+/\- *lemma* measure_eq_infi
- \+/\- *lemma* exists_is_measurable_superset_of_measure_eq_zero
- \+/\- *lemma* exists_is_measurable_superset_iff_measure_eq_zero
- \+/\- *lemma* measure_Union_null
- \+/\- *lemma* measure_Union_null_iff
- \+/\- *lemma* measure_union_null
- \+/\- *lemma* measure_union_null_iff
- \+/\- *lemma* measure_Union
- \+/\- *lemma* measure_diff
- \+/\- *lemma* measure_compl
- \+/\- *lemma* measure_eq_inter_diff
- \+/\- *lemma* measure_union_add_inter
- \+/\- *lemma* tendsto_measure_Union
- \+/\- *lemma* tendsto_measure_Inter
- \+/\- *lemma* measure_if
- \+/\- *lemma* le_to_outer_measure_caratheodory
- \+/\- *lemma* to_measure_to_outer_measure
- \+/\- *lemma* to_measure_apply
- \+/\- *lemma* le_to_measure_apply
- \+/\- *lemma* to_outer_measure_to_measure
- \+/\- *lemma* Inf_apply
- \+/\- *lemma* measure_univ_eq_zero
- \+/\- *lemma* le_lift_linear_apply
- \+/\- *lemma* restrict_apply
- \+/\- *lemma* restrict_restrict
- \+/\- *lemma* restrict_apply_eq_zero
- \+/\- *lemma* restrict_apply_eq_zero'
- \+/\- *lemma* restrict_eq_zero
- \+/\- *lemma* restrict_union_apply
- \+/\- *lemma* restrict_union
- \+/\- *lemma* restrict_union_add_inter
- \+/\- *lemma* restrict_add_restrict_compl
- \+/\- *lemma* restrict_compl_add_restrict
- \+/\- *lemma* restrict_Union_apply
- \+/\- *lemma* restrict_Union_apply_eq_supr
- \+/\- *lemma* map_comap_subtype_coe
- \+/\- *lemma* restrict_le_self
- \+/\- *lemma* restrict_congr_meas
- \+/\- *lemma* restrict_congr_mono
- \+/\- *lemma* restrict_union_congr
- \+/\- *lemma* restrict_to_outer_measure_eq_to_outer_measure_restrict
- \+/\- *lemma* restrict_Inf_eq_Inf_restrict
- \+/\- *lemma* dirac_apply'
- \+/\- *lemma* dirac_apply
- \+/\- *lemma* dirac_apply_of_mem
- \+/\- *lemma* sum_apply
- \+/\- *lemma* le_sum
- \+/\- *lemma* restrict_Union
- \+/\- *lemma* restrict_Union_le
- \+/\- *lemma* restrict_sum
- \+/\- *lemma* count_apply
- \+/\- *lemma* count_apply_infinite
- \+/\- *lemma* count_apply_eq_top
- \+/\- *lemma* count_apply_lt_top
- \+/\- *lemma* mem_cofinite
- \+/\- *lemma* compl_mem_cofinite
- \+/\- *lemma* ae_of_all
- \+/\- *lemma* ae_all_iff
- \+/\- *lemma* ae_ball_iff
- \+/\- *lemma* ae_eq_refl
- \+/\- *lemma* ae_eq_symm
- \+/\- *lemma* ae_eq_trans
- \+/\- *lemma* ae_eq_empty
- \+/\- *lemma* ae_le_set
- \+/\- *lemma* union_ae_eq_right
- \+/\- *lemma* diff_ae_eq_self
- \+/\- *lemma* mem_ae_map_iff
- \+/\- *lemma* ae_map_iff
- \+/\- *lemma* ae_restrict_iff
- \+/\- *lemma* ae_restrict_eq
- \+/\- *lemma* mem_dirac_ae_iff
- \+/\- *lemma* eventually_eq_dirac
- \+/\- *lemma* eventually_eq_dirac'
- \+/\- *lemma* measure_mono_ae
- \+/\- *lemma* measure_congr
- \+/\- *lemma* restrict_mono_ae
- \+/\- *lemma* restrict_congr_set
- \+/\- *lemma* measure_countable
- \+/\- *lemma* measure_finite
- \+/\- *lemma* supr_restrict_spanning_sets
- \+/\- *lemma* finite_at_principal
- \+/\- *lemma* sub_apply
- \+/\- *lemma* metric.bounded.finite_measure
- \+/\- *theorem* measure_Union_le
- \+/\- *theorem* add_apply
- \+/\- *theorem* coe_smul
- \+/\- *theorem* smul_apply
- \+ *theorem* le_map_apply
- \+/\- *theorem* is_null_measurable_iff
- \+/\- *theorem* is_null_measurable_measure_eq
- \+/\- *theorem* is_measurable.is_null_measurable
- \+/\- *theorem* is_null_measurable_of_complete
- \+/\- *theorem* is_null_measurable.union_null
- \+/\- *theorem* null_is_null_measurable
- \+/\- *theorem* is_null_measurable.Union_nat
- \+/\- *theorem* is_measurable.diff_null
- \+/\- *theorem* is_null_measurable.diff_null
- \+/\- *theorem* is_null_measurable.compl
- \+/\- *theorem* measure_Union_le
- \+/\- *theorem* add_apply
- \+/\- *theorem* coe_smul
- \+/\- *theorem* smul_apply
- \+/\- *theorem* is_null_measurable_iff
- \+/\- *theorem* is_null_measurable_measure_eq
- \+/\- *theorem* is_measurable.is_null_measurable
- \+/\- *theorem* is_null_measurable_of_complete
- \+/\- *theorem* is_null_measurable.union_null
- \+/\- *theorem* null_is_null_measurable
- \+/\- *theorem* is_null_measurable.Union_nat
- \+/\- *theorem* is_measurable.diff_null
- \+/\- *theorem* is_null_measurable.diff_null
- \+/\- *theorem* is_null_measurable.compl
- \+/\- *def* of_measurable
- \+/\- *def* outer_measure.to_measure
- \+/\- *def* sum
- \+/\- *def* measure_theory.measure.is_complete
- \+/\- *def* is_null_measurable
- \+/\- *def* null_measurable
- \+/\- *def* completion
- \+/\- *def* of_measurable
- \+/\- *def* outer_measure.to_measure
- \+/\- *def* sum
- \+/\- *def* measure_theory.measure.is_complete
- \+/\- *def* is_null_measurable
- \+/\- *def* null_measurable
- \+/\- *def* completion

Modified src/measure_theory/prod.lean
- \+ *lemma* prod_prod_le



## [2020-12-30 19:29:20](https://github.com/leanprover-community/mathlib/commit/f1d2bc6)
feat(order/lattice_intervals): lattice structures on intervals in lattices ([#5496](https://github.com/leanprover-community/mathlib/pull/5496))
Defines (semi-)lattice structures on intervals in lattices
#### Estimated changes
Created src/order/lattice_intervals.lean
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* coe_bot
- \+ *lemma* coe_top
- \+ *def* order_bot
- \+ *def* semilattice_inf_bot
- \+ *def* order_top
- \+ *def* semilattice_sup_top
- \+ *def* order_bot
- \+ *def* order_top
- \+ *def* semilattice_inf_bot
- \+ *def* semilattice_inf_top
- \+ *def* semilattice_sup_bot
- \+ *def* semilattice_sup_top
- \+ *def* bounded_lattice



## [2020-12-30 17:33:54](https://github.com/leanprover-community/mathlib/commit/16320e2)
chore(topology/algebra/infinite_sum): refactor `tsum_mul_left/right` ([#5533](https://github.com/leanprover-community/mathlib/pull/5533))
* move old lemmas to `summable` namespace;
* add new `tsum_mul_left` and `tsum_mul_right` that work in a `division_ring` without a `summable` assumption.
#### Estimated changes
Modified src/analysis/analytic/basic.lean

Modified src/analysis/normed_space/banach.lean

Modified src/data/real/cardinality.lean

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* summable.tsum_mul_left
- \+ *lemma* summable.tsum_mul_right
- \+/\- *lemma* tsum_mul_left
- \+/\- *lemma* tsum_mul_right
- \+ *lemma* has_sum.nonneg
- \+ *lemma* has_sum.nonpos
- \+/\- *lemma* tsum_mul_left
- \+/\- *lemma* tsum_mul_right

Modified src/topology/instances/nnreal.lean
- \+ *lemma* tsum_mul_left
- \+ *lemma* tsum_mul_right



## [2020-12-30 17:33:52](https://github.com/leanprover-community/mathlib/commit/958c407)
chore(analysis/normed_space/basic): a few lemmas about `nnnorm` ([#5532](https://github.com/leanprover-community/mathlib/pull/5532))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* coe_nnnorm
- \+ *lemma* mem_emetric_ball_0_iff
- \+ *lemma* nnnorm_mul
- \+ *lemma* nnnorm_pow
- \+ *lemma* nnnorm_prod
- \+ *lemma* nnnorm_div
- \+ *lemma* nnnorm_fpow
- \+/\- *lemma* coe_nnnorm
- \+ *def* nnnorm_hom



## [2020-12-30 15:51:17](https://github.com/leanprover-community/mathlib/commit/b15bb06)
feat(topology/instances/ennreal): a sufficient condition for `f : (Σ i, β i) → ℝ` to be summable ([#5531](https://github.com/leanprover-community/mathlib/pull/5531))
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+ *lemma* summable_sigma
- \+ *lemma* summable_sigma_of_nonneg



## [2020-12-30 15:51:13](https://github.com/leanprover-community/mathlib/commit/38ba6ba)
chore(data/real/{e,}nnreal): a few lemmas ([#5530](https://github.com/leanprover-community/mathlib/pull/5530))
* Rename `nnreal.le_of_forall_lt_one_mul_lt` to
  `nnreal.le_of_forall_lt_one_mul_le`, and similarly for `ennreal`.
* Move the proof of the latter lemma to `topology/instances/ennreal`,
  prove it using continuity of multiplication.
* Add `ennreal.le_of_forall_nnreal_lt`, `nnreal.lt_div_iff`, and
  `nnreal.mul_lt_of_lt_div`.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* le_of_forall_nnreal_lt
- \- *lemma* le_of_forall_lt_one_mul_lt

Modified src/data/real/nnreal.lean
- \+ *lemma* lt_div_iff
- \+ *lemma* mul_lt_of_lt_div
- \+ *lemma* le_of_forall_lt_one_mul_le
- \- *lemma* le_of_forall_lt_one_mul_lt

Modified src/measure_theory/integration.lean

Modified src/topology/instances/ennreal.lean
- \+ *lemma* le_of_forall_lt_one_mul_le



## [2020-12-30 15:51:11](https://github.com/leanprover-community/mathlib/commit/c82be35)
feat(analysis/normed_space/inner_product): orthogonal complement lemmas ([#5474](https://github.com/leanprover-community/mathlib/pull/5474))
The orthogonal complement of a subspace is closed.  The orthogonal complement of the orthogonal complement of a complete subspace is itself.
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* inner_right_coe
- \+ *lemma* inner_right_apply
- \+ *lemma* orthogonal_eq_inter
- \+ *lemma* submodule.is_closed_orthogonal
- \+ *lemma* submodule.sup_orthogonal_of_complete_space
- \+ *lemma* submodule.exists_sum_mem_mem_orthogonal
- \+ *lemma* submodule.orthogonal_orthogonal
- \+ *def* inner_right



## [2020-12-30 13:05:48](https://github.com/leanprover-community/mathlib/commit/7a03171)
chore(order/rel_iso): add some missing lemmas ([#5492](https://github.com/leanprover-community/mathlib/pull/5492))
Also define `order_iso.trans`.
#### Estimated changes
Modified src/order/rel_iso.lean
- \+ *lemma* coe_subtype
- \+ *lemma* default_def
- \+ *lemma* symm_symm
- \+ *lemma* symm_injective
- \+ *lemma* coe_trans
- \+ *lemma* trans_apply
- \+ *lemma* order_iso.map_bot'
- \+/\- *lemma* order_iso.map_bot
- \+ *lemma* order_iso.map_top'
- \+/\- *lemma* order_iso.map_top
- \+/\- *lemma* order_iso.map_bot
- \+/\- *lemma* order_iso.map_top
- \+/\- *theorem* trans_apply
- \+ *theorem* coe_trans
- \+ *theorem* symm_apply_eq
- \+/\- *theorem* trans_apply
- \+ *def* subtype
- \+ *def* trans
- \- *def* set_coe_embedding



## [2020-12-30 13:05:46](https://github.com/leanprover-community/mathlib/commit/8545aa6)
chore(topology/algebra/ordered): move code, add missing lemmas ([#5481](https://github.com/leanprover-community/mathlib/pull/5481))
* merge two sections about `linear_ordered_add_comm_group`;
* add missing lemmas about limits of `f * g` when one of `f`, `g` tends to `-∞`, and another tends to a positive or negative constant;
* drop `neg_preimage_closure` in favor of the new `neg_closure` in `topology/algebra/group`.
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *lemma* inv_closure

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* nhds_eq_infi_abs_sub
- \+/\- *lemma* order_topology_of_nhds_abs
- \+/\- *lemma* linear_ordered_add_comm_group.tendsto_nhds
- \+/\- *lemma* eventually_abs_sub_lt
- \+/\- *lemma* continuous_abs
- \+/\- *lemma* filter.tendsto.abs
- \+/\- *lemma* continuous.abs
- \+/\- *lemma* continuous_at.abs
- \+/\- *lemma* continuous_within_at.abs
- \+/\- *lemma* continuous_on.abs
- \+/\- *lemma* tendsto_abs_nhds_within_zero
- \+ *lemma* filter.tendsto.neg_mul_at_top
- \+ *lemma* filter.tendsto.at_bot_mul
- \+ *lemma* filter.tendsto.at_bot_mul_neg
- \+ *lemma* filter.tendsto.mul_at_bot
- \+ *lemma* filter.tendsto.neg_mul_at_bot
- \- *lemma* neg_preimage_closure
- \+/\- *lemma* nhds_eq_infi_abs_sub
- \+/\- *lemma* order_topology_of_nhds_abs
- \+/\- *lemma* linear_ordered_add_comm_group.tendsto_nhds
- \+/\- *lemma* eventually_abs_sub_lt
- \+/\- *lemma* continuous_abs
- \+/\- *lemma* filter.tendsto.abs
- \+/\- *lemma* continuous.abs
- \+/\- *lemma* continuous_at.abs
- \+/\- *lemma* continuous_within_at.abs
- \+/\- *lemma* continuous_on.abs
- \+/\- *lemma* tendsto_abs_nhds_within_zero



## [2020-12-30 10:07:47](https://github.com/leanprover-community/mathlib/commit/5e86589)
chore(data/nat/enat): some useful lemmas ([#5517](https://github.com/leanprover-community/mathlib/pull/5517))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *theorem* find_le

Modified src/data/nat/enat.lean
- \+ *lemma* dom_coe
- \+ *lemma* le_def
- \+/\- *lemma* get_coe
- \+ *lemma* get_coe'
- \+ *lemma* dom_of_le_of_dom
- \+/\- *lemma* dom_of_le_some
- \+ *lemma* lt_def
- \+/\- *lemma* get_le_get
- \+ *lemma* le_coe_iff
- \+ *lemma* lt_coe_iff
- \+ *lemma* coe_le_iff
- \+ *lemma* coe_lt_iff
- \+ *lemma* dom_of_lt
- \+ *lemma* eq_top_iff_forall_lt
- \+ *lemma* eq_top_iff_forall_le
- \+/\- *lemma* to_with_top_zero'
- \+ *lemma* find_get
- \+ *lemma* find_dom
- \+ *lemma* lt_find
- \+ *lemma* lt_find_iff
- \+ *lemma* find_le
- \+ *lemma* find_eq_top_iff
- \+/\- *lemma* get_coe
- \+/\- *lemma* dom_of_le_some
- \+/\- *lemma* get_le_get
- \+/\- *lemma* to_with_top_zero'
- \+/\- *def* to_with_top
- \+ *def* find
- \+/\- *def* to_with_top

Modified src/ring_theory/multiplicity.lean
- \- *theorem* nat.find_le

Modified src/ring_theory/power_series/basic.lean



## [2020-12-30 08:01:01](https://github.com/leanprover-community/mathlib/commit/1c110ad)
fix(tactic/linarith): elaborate and insert arguments before destructing hypotheses ([#5501](https://github.com/leanprover-community/mathlib/pull/5501))
closes [#5480](https://github.com/leanprover-community/mathlib/pull/5480)
Arguments to `linarith` can depend on hypotheses (e.g. conjunctions) that get destructed during preprocessing, after which the arguments will no longer elaborate or typecheck. This just moves the elaboration earlier and adds these arguments as hypotheses themselves.
#### Estimated changes
Modified src/tactic/linarith/frontend.lean

Modified test/linarith.lean
- \+ *lemma* bar



## [2020-12-30 01:38:14](https://github.com/leanprover-community/mathlib/commit/7c6020f)
chore(scripts): update nolints.txt ([#5526](https://github.com/leanprover-community/mathlib/pull/5526))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-29 19:06:07](https://github.com/leanprover-community/mathlib/commit/abffbaa)
feat(analysis/convex/specific_functions): log is concave ([#5508](https://github.com/leanprover-community/mathlib/pull/5508))
This PR proves that the real log is concave on `Ioi 0` and `Iio 0`, and adds lemmas about concavity of functions along the way.
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean
- \+ *theorem* concave_on_of_deriv_antimono
- \+ *theorem* concave_on_univ_of_deriv_antimono
- \+ *theorem* concave_on_of_deriv2_nonpos
- \+ *theorem* convex_on_open_of_deriv2_nonneg
- \+ *theorem* concave_on_open_of_deriv2_nonpos
- \+ *theorem* concave_on_univ_of_deriv2_nonpos

Modified src/analysis/convex/specific_functions.lean
- \+ *lemma* concave_on_log_Ioi
- \+ *lemma* concave_on_log_Iio



## [2020-12-29 07:47:35](https://github.com/leanprover-community/mathlib/commit/8e413eb)
feat(order/bounded_lattice): define atoms, coatoms, and simple lattices ([#5471](https://github.com/leanprover-community/mathlib/pull/5471))
Defines `is_atom`, `is_coatom`, and `is_simple_lattice`
Refactors `ideal.is_maximal` to use `is_coatom`, the new definition is definitionally equal to the old one
#### Estimated changes
Created src/order/atoms.lean
- \+ *lemma* eq_bot_or_eq_of_le_atom
- \+ *lemma* eq_top_or_eq_of_coatom_le
- \+ *lemma* is_atom_iff_is_coatom_dual
- \+ *lemma* is_coatom_iff_is_atom_dual
- \+ *lemma* is_atom_top
- \+ *lemma* is_coatom_bot
- \+ *theorem* is_simple_lattice_iff_is_simple_lattice_order_dual
- \+ *theorem* is_simple_lattice_iff_is_atom_top
- \+ *theorem* is_simple_lattice_iff_is_coatom_bot
- \+ *def* is_atom
- \+ *def* is_coatom

Modified src/order/bounded_lattice.lean
- \+ *lemma* bot_ne_top
- \+ *lemma* top_ne_bot

Modified src/order/order_dual.lean

Modified src/ring_theory/ideal/basic.lean
- \+/\- *def* is_maximal
- \+/\- *def* is_maximal



## [2020-12-29 03:00:40](https://github.com/leanprover-community/mathlib/commit/15ff865)
doc(localized): update documentation ([#5519](https://github.com/leanprover-community/mathlib/pull/5519))
remove old warning
remove duplicated documentation
rename notation namespace to locale
#### Estimated changes
Modified src/tactic/localized.lean



## [2020-12-29 01:33:07](https://github.com/leanprover-community/mathlib/commit/297d97e)
chore(scripts): update nolints.txt ([#5522](https://github.com/leanprover-community/mathlib/pull/5522))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-28 17:36:18](https://github.com/leanprover-community/mathlib/commit/41bad63)
feat(polynomial/degree/definitions): nat_degree_X_pow ([#5512](https://github.com/leanprover-community/mathlib/pull/5512))
Companion to degree_X_pow
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* nat_degree_X_pow



## [2020-12-28 15:03:21](https://github.com/leanprover-community/mathlib/commit/d245c4e)
feat(polynomial/algebra_map): aeval_comp ([#5511](https://github.com/leanprover-community/mathlib/pull/5511))
Basic lemma about aeval
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* aeval_comp



## [2020-12-28 13:55:13](https://github.com/leanprover-community/mathlib/commit/f1f2ca6)
feat(category_theory/limits): preserves limits of equivalent shape ([#5515](https://github.com/leanprover-community/mathlib/pull/5515))
#### Estimated changes
Modified src/category_theory/limits/preserves/basic.lean
- \+ *def* preserves_limits_of_shape_of_equiv
- \+ *def* preserves_colimits_of_shape_of_equiv



## [2020-12-28 03:40:12](https://github.com/leanprover-community/mathlib/commit/6d1d4c1)
chore(scripts): update nolints.txt ([#5514](https://github.com/leanprover-community/mathlib/pull/5514))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-28 00:38:46](https://github.com/leanprover-community/mathlib/commit/6d0b415)
feat(data/list/basic): nth_zero ([#5513](https://github.com/leanprover-community/mathlib/pull/5513))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* nth_zero



## [2020-12-27 16:40:59](https://github.com/leanprover-community/mathlib/commit/5c8c122)
chore(analysis/analytic/basic): speed up slow lemmas ([#5507](https://github.com/leanprover-community/mathlib/pull/5507))
Removes slow `tidy`s from `formal_multilinear_series.change_origin_radius` and `formal_multilinear_series.change_origin_has_sum`
#### Estimated changes
Modified src/analysis/analytic/basic.lean



## [2020-12-27 04:21:55](https://github.com/leanprover-community/mathlib/commit/1e75453)
feat(data/list/basic): filter_map retains prefix ([#5453](https://github.com/leanprover-community/mathlib/pull/5453))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* is_prefix.filter_map
- \+ *lemma* is_prefix.reduce_option



## [2020-12-26 22:54:39](https://github.com/leanprover-community/mathlib/commit/f7e728a)
feat(data/list/range): enum is a zip ([#5457](https://github.com/leanprover-community/mathlib/pull/5457))
#### Estimated changes
Modified src/data/list/range.lean
- \+ *lemma* enum_eq_zip_range
- \+ *lemma* unzip_enum_eq_prod
- \+ *lemma* enum_from_eq_zip_range'
- \+ *lemma* unzip_enum_from_eq_prod

Modified src/data/list/zip.lean
- \+ *lemma* zip_of_prod
- \+ *lemma* map_prod_left_eq_zip
- \+ *lemma* map_prod_right_eq_zip



## [2020-12-26 20:38:16](https://github.com/leanprover-community/mathlib/commit/ae60bb9)
chore(topology/algebra/order): add `continuous_on.surj_on_of_tendsto` ([#5502](https://github.com/leanprover-community/mathlib/pull/5502))
* rename `surjective_of_continuous` to `continuous.surjective` and `surjective_of_continuous'` to `continuous.surjective'`;
* add `continuous_on.surj_on_of_tendsto` and `continuous_on.surj_on_of_tendsto'`
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean

Modified src/data/real/sqrt.lean

Modified src/dynamics/circle/rotation_number/translation_number.lean

Modified src/topology/algebra/ordered.lean
- \+ *lemma* continuous.surjective
- \+ *lemma* continuous.surjective'
- \+ *lemma* continuous_on.surj_on_of_tendsto
- \+ *lemma* continuous_on.surj_on_of_tendsto'
- \- *lemma* surjective_of_continuous
- \- *lemma* surjective_of_continuous'



## [2020-12-26 09:47:44](https://github.com/leanprover-community/mathlib/commit/add100a)
feat(ring_theory/perfection): perfection.map ([#5503](https://github.com/leanprover-community/mathlib/pull/5503))
#### Estimated changes
Modified src/ring_theory/perfection.lean
- \+ *lemma* coeff_pow_p'
- \+ *lemma* hom_ext
- \+ *lemma* coeff_map
- \+ *lemma* equiv_apply
- \+ *lemma* comp_equiv
- \+ *lemma* comp_equiv'
- \+ *lemma* comp_symm_equiv
- \+ *lemma* comp_symm_equiv'
- \+ *lemma* hom_ext
- \+ *lemma* comp_map
- \+ *lemma* map_map
- \+ *lemma* map_eq_map
- \+ *def* map



## [2020-12-26 01:31:06](https://github.com/leanprover-community/mathlib/commit/768497c)
chore(scripts): update nolints.txt ([#5505](https://github.com/leanprover-community/mathlib/pull/5505))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-25 21:29:27](https://github.com/leanprover-community/mathlib/commit/666035f)
fix(algebra/big_operators/basic): add docstrings for `sum_bij` and `sum_bij'` ([#5497](https://github.com/leanprover-community/mathlib/pull/5497))
They don't seem to be there.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean



## [2020-12-25 21:29:26](https://github.com/leanprover-community/mathlib/commit/1a526b3)
chore(topology/homeomorph): a few more lemmas, golf ([#5467](https://github.com/leanprover-community/mathlib/pull/5467))
#### Estimated changes
Modified src/topology/homeomorph.lean
- \+ *lemma* image_preimage
- \+ *lemma* preimage_image
- \+/\- *lemma* induced_eq
- \+/\- *lemma* coinduced_eq
- \+/\- *lemma* is_open_preimage
- \+ *lemma* is_open_image
- \+ *lemma* is_closed_preimage
- \+ *lemma* is_closed_image
- \+ *lemma* preimage_closure
- \+ *lemma* image_closure
- \+ *lemma* map_nhds_eq
- \+ *lemma* comap_nhds_eq
- \+ *lemma* nhds_eq_comap
- \+/\- *lemma* induced_eq
- \+/\- *lemma* coinduced_eq
- \+/\- *lemma* is_open_preimage

Modified src/topology/maps.lean



## [2020-12-25 18:38:51](https://github.com/leanprover-community/mathlib/commit/726b7bf)
feat(analysis/specific_limits): a `tfae` about "`f` grows exponentially slower than `R ^ n`" ([#5488](https://github.com/leanprover-community/mathlib/pull/5488))
Also add supporting lemmas here and there.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *theorem* pow_bit0_nonneg
- \+/\- *theorem* pow_two_nonneg
- \+ *theorem* pow_bit0_pos
- \+/\- *theorem* pow_two_pos_of_ne_zero
- \+/\- *theorem* pow_two_nonneg
- \+/\- *theorem* pow_two_pos_of_ne_zero

Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* sign_cases_of_C_mul_pow_nonneg
- \+ *lemma* abs_pow
- \+ *lemma* strict_mono_pow_bit1
- \+ *theorem* pow_bit1_neg_iff
- \+ *theorem* pow_bit1_nonneg_iff
- \+ *theorem* pow_bit1_nonpos_iff
- \+ *theorem* pow_bit1_pos_iff
- \+/\- *theorem* one_add_mul_le_pow
- \+/\- *theorem* one_add_sub_mul_le_pow
- \+/\- *theorem* one_add_mul_le_pow
- \+/\- *theorem* one_add_sub_mul_le_pow

Modified src/analysis/asymptotics.lean
- \+/\- *theorem* is_O_with_zero_right_iff
- \+/\- *theorem* is_O_zero_right_iff
- \+/\- *theorem* is_o_zero_right_iff
- \+ *theorem* is_O_one_nat_at_top_iff
- \+/\- *theorem* is_O_with_zero_right_iff
- \+/\- *theorem* is_O_zero_right_iff
- \+/\- *theorem* is_o_zero_right_iff

Modified src/analysis/specific_limits.lean
- \+ *lemma* is_O_pow_pow_of_le_left
- \+ *lemma* tfae_exists_lt_is_o_pow

Modified src/data/real/nnreal.lean
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_pow

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* tendsto_bit0_at_top
- \+ *lemma* tendsto_bit0_at_bot
- \+ *lemma* tendsto_bit1_at_top
- \+ *lemma* zero_pow_eventually_eq
- \+ *lemma* nonneg_of_eventually_pow_nonneg



## [2020-12-25 17:10:05](https://github.com/leanprover-community/mathlib/commit/d968a61)
feat(category_theory/limits): yoneda reflects limits ([#5447](https://github.com/leanprover-community/mathlib/pull/5447))
yoneda and coyoneda jointly reflect limits
#### Estimated changes
Modified src/category_theory/limits/yoneda.lean
- \+ *def* yoneda_jointly_reflects_limits
- \+ *def* coyoneda_jointly_reflects_limits



## [2020-12-25 13:57:08](https://github.com/leanprover-community/mathlib/commit/f60fd08)
chore(logic/basic): +2 simp lemmas ([#5500](https://github.com/leanprover-community/mathlib/pull/5500))
* simplify `a ∨ b ↔ a` to `b → a`;
* simplify `a ∨ b ↔ b` to `a → b`.
#### Estimated changes
Modified src/data/ordmap/ordset.lean

Modified src/logic/basic.lean
- \+ *theorem* or_iff_left_iff_imp
- \+ *theorem* or_iff_right_iff_imp



## [2020-12-25 01:42:05](https://github.com/leanprover-community/mathlib/commit/1f0231d)
chore(scripts): update nolints.txt ([#5498](https://github.com/leanprover-community/mathlib/pull/5498))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-24 19:51:27](https://github.com/leanprover-community/mathlib/commit/feced76)
feat(algebra/*): Noncomputable `group` structures from `is_unit` ([#5427](https://github.com/leanprover-community/mathlib/pull/5427))
Noncomputably defines the following group structures given that all (nonzero) elements are units:
- `monoid` -> `group`
- `comm_monoid` -> `comm_group`
- `monoid_with_zero` -> `comm_group_with_zero`
- `comm_monoid_with_zero` -> `comm_group_with_zero`
- `ring` -> `division_ring`
- `comm_ring` -> `field`
#### Estimated changes
Modified src/algebra/field.lean

Modified src/algebra/group/units.lean

Modified src/algebra/group_with_zero/basic.lean



## [2020-12-24 16:50:39](https://github.com/leanprover-community/mathlib/commit/f300c75)
feat(data/list/basic): lemmas about reduce_option ([#5450](https://github.com/leanprover-community/mathlib/pull/5450))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* filter_map_append
- \+ *lemma* reduce_option_cons_of_some
- \+ *lemma* reduce_option_cons_of_none
- \+ *lemma* reduce_option_nil
- \+ *lemma* reduce_option_map
- \+ *lemma* reduce_option_append
- \+ *lemma* reduce_option_length_le
- \+ *lemma* reduce_option_length_eq_iff
- \+ *lemma* reduce_option_length_lt_iff
- \+ *lemma* reduce_option_singleton
- \+ *lemma* reduce_option_concat
- \+ *lemma* reduce_option_concat_of_some
- \+ *lemma* reduce_option_mem_iff
- \+ *lemma* reduce_option_nth_iff



## [2020-12-24 14:52:22](https://github.com/leanprover-community/mathlib/commit/3046436)
chore(linear_algebra/linear_independent): make a binding explicit in ne_zero ([#5494](https://github.com/leanprover-community/mathlib/pull/5494))
Resubmitting [#5479](https://github.com/leanprover-community/mathlib/pull/5479) from within the mathlib repo.
#### Estimated changes
Modified src/linear_algebra/affine_space/independent.lean

Modified src/linear_algebra/linear_independent.lean



## [2020-12-24 08:35:35](https://github.com/leanprover-community/mathlib/commit/46614b0)
chore(ring_theory/power_series/well_known): generalize ([#5491](https://github.com/leanprover-community/mathlib/pull/5491))
* generalize `power_series.exp`, `power_series.cos`, and `power_series.sin` to a `ℚ`-algebra;
* define `alg_hom.mk'`;
* rename `alg_hom_nat` to `ring_hom.to_nat_alg_hom`;
* drop `alg_hom_int` (was equal to `ring_hom.to_int_alg_hom`);
* add `ring_hom.to_rat_alg_hom`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* coe_mk'
- \+ *lemma* map_rat_algebra_map
- \+ *def* mk'
- \+ *def* to_nat_alg_hom
- \+ *def* to_int_alg_hom
- \+ *def* to_rat_alg_hom
- \- *def* alg_hom_nat
- \- *def* alg_hom_int
- \- *def* ring_hom.to_int_alg_hom

Modified src/ring_theory/power_series/well_known.lean
- \+/\- *lemma* coeff_exp
- \+/\- *lemma* map_exp
- \+/\- *lemma* map_sin
- \+/\- *lemma* map_cos
- \+/\- *lemma* coeff_exp
- \+/\- *lemma* map_exp
- \+/\- *lemma* map_sin
- \+/\- *lemma* map_cos
- \+/\- *def* exp
- \+/\- *def* sin
- \+/\- *def* cos
- \+/\- *def* exp
- \+/\- *def* sin
- \+/\- *def* cos



## [2020-12-24 08:35:33](https://github.com/leanprover-community/mathlib/commit/8a03839)
chore(scripts): update nolints.txt ([#5490](https://github.com/leanprover-community/mathlib/pull/5490))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-24 07:17:34](https://github.com/leanprover-community/mathlib/commit/2ae61be)
feat(field_theory/galois): is_galois.self ([#5486](https://github.com/leanprover-community/mathlib/pull/5486))
Some basic lemmas about is_separable, normal, and is_galois.
#### Estimated changes
Modified src/field_theory/galois.lean

Modified src/field_theory/normal.lean

Modified src/field_theory/separable.lean



## [2020-12-23 22:08:09](https://github.com/leanprover-community/mathlib/commit/63070ed)
feat(data/list/chain): relate chain to refl trans gen ([#5437](https://github.com/leanprover-community/mathlib/pull/5437))
Some golf and a new lemma to convert a list chain to a refl trans gen
#### Estimated changes
Modified src/category_theory/is_connected.lean

Modified src/data/list/chain.lean
- \+/\- *lemma* exists_chain_of_relation_refl_trans_gen
- \+/\- *lemma* chain.induction
- \+/\- *lemma* chain.induction_head
- \+ *lemma* relation_refl_trans_gen_of_exists_chain
- \+/\- *lemma* exists_chain_of_relation_refl_trans_gen
- \+/\- *lemma* chain.induction
- \+/\- *lemma* chain.induction_head



## [2020-12-23 22:08:07](https://github.com/leanprover-community/mathlib/commit/ceae529)
chore(group_theory/coset): Make `quotient_group.mk` an abbreviation ([#5377](https://github.com/leanprover-community/mathlib/pull/5377))
This allows simp lemmas about `quotient.mk'` to apply here, which currently do not apply.
The definition doesn't seem interesting enough to be semireducible.
#### Estimated changes
Modified src/group_theory/coset.lean
- \- *def* mk



## [2020-12-23 18:58:44](https://github.com/leanprover-community/mathlib/commit/2a5a0b0)
feat(group_theory/*): mark some lemmas as ext (about homs out of free constructions) ([#5484](https://github.com/leanprover-community/mathlib/pull/5484))
#### Estimated changes
Modified src/algebra/free_algebra.lean

Modified src/algebra/free_monoid.lean

Modified src/algebra/lie/universal_enveloping.lean

Modified src/algebra/monoid_algebra.lean

Modified src/data/dfinsupp.lean

Modified src/group_theory/abelianization.lean

Modified src/group_theory/free_abelian_group.lean

Modified src/group_theory/free_group.lean
- \+ *lemma* ext_hom

Modified src/linear_algebra/clifford_algebra.lean

Modified src/linear_algebra/dfinsupp.lean

Modified src/linear_algebra/exterior_algebra.lean

Modified src/linear_algebra/tensor_algebra.lean

Modified src/tactic/ext.lean



## [2020-12-23 18:58:42](https://github.com/leanprover-community/mathlib/commit/e2edba5)
chore(order/filter/basic): make `filter.univ_mem_sets` a `simp` lemma ([#5464](https://github.com/leanprover-community/mathlib/pull/5464))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* insert_nth_succ_nil

Modified src/data/rel.lean
- \+/\- *lemma* core_univ
- \+/\- *lemma* core_univ

Modified src/order/filter/basic.lean
- \+/\- *lemma* univ_mem_sets
- \+/\- *lemma* univ_mem_sets

Modified src/order/filter/partial.lean

Modified src/topology/list.lean
- \+/\- *lemma* nhds_nil
- \+/\- *lemma* nhds_nil



## [2020-12-23 18:58:38](https://github.com/leanprover-community/mathlib/commit/d3a5e06)
feat(data/dlist/basic): dlist singleton and of_list simp lemmas ([#5461](https://github.com/leanprover-community/mathlib/pull/5461))
#### Estimated changes
Modified src/data/dlist/basic.lean
- \+ *lemma* dlist_singleton
- \+ *lemma* dlist_lazy



## [2020-12-23 16:10:29](https://github.com/leanprover-community/mathlib/commit/fd9268c)
feat(data/list/basic): lemmas about scanl ([#5454](https://github.com/leanprover-community/mathlib/pull/5454))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* length_singleton
- \+/\- *lemma* length_scanl
- \+ *lemma* scanl_nil
- \+ *lemma* scanl_cons
- \+ *lemma* nth_zero_scanl
- \+ *lemma* nth_le_zero_scanl
- \+ *lemma* nth_succ_scanl
- \+ *lemma* nth_le_succ_scanl
- \+/\- *lemma* length_scanl



## [2020-12-23 12:11:42](https://github.com/leanprover-community/mathlib/commit/eb5cf25)
chore(analysis/asymptotics): a few more lemmas ([#5482](https://github.com/leanprover-community/mathlib/pull/5482))
* golf some proofs;
* `x ^ n = o (y ^ n)` as `n → ∞` provided that `0 ≤ x < y`;
* lemmas about `is_O _ _ ⊤` etc;
* if `is_O f g cofinite`, then for some `C>0` and any `x` such that `g x ≠ 0` we have `∥f x∥≤C*∥g x∥`.
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *lemma* is_O_with_top
- \+ *lemma* is_O_top
- \+ *lemma* is_o_top
- \+/\- *theorem* is_o_iff_tendsto'
- \+ *theorem* bound_of_is_O_cofinite
- \+ *theorem* is_O_cofinite_iff
- \+ *theorem* bound_of_is_O_nat_at_top
- \+ *theorem* is_O_nat_at_top_iff
- \+/\- *theorem* is_o_iff_tendsto'

Modified src/analysis/specific_limits.lean
- \+/\- *lemma* tendsto_pow_at_top_nhds_0_of_lt_1
- \+ *lemma* is_o_pow_pow_of_lt_left
- \+ *lemma* is_o_pow_pow_of_abs_lt_left
- \+/\- *lemma* tendsto_pow_at_top_nhds_0_of_lt_1

Modified src/order/filter/cofinite.lean
- \+ *lemma* eventually_cofinite



## [2020-12-23 09:41:22](https://github.com/leanprover-community/mathlib/commit/435b97a)
feat(ring_theory/witt_vector): the comparison between W(F_p) and Z_p ([#5164](https://github.com/leanprover-community/mathlib/pull/5164))
This PR is the culmination of the Witt vector project. We prove that the
ring of Witt vectors over `zmod p` is isomorphic to the ring of `p`-adic
numbers.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+ *lemma* to_ring_hom_comp_symm_to_ring_hom
- \+ *lemma* symm_to_ring_hom_comp_to_ring_hom

Created src/ring_theory/witt_vector/compare.lean
- \+ *lemma* eq_of_le_of_cast_pow_eq_zero
- \+ *lemma* card_zmod
- \+ *lemma* char_p_zmod
- \+ *lemma* zmod_equiv_trunc_apply
- \+ *lemma* commutes
- \+ *lemma* commutes'
- \+ *lemma* commutes_symm'
- \+ *lemma* commutes_symm
- \+ *lemma* to_zmod_pow_compat
- \+ *lemma* zmod_equiv_trunc_compat
- \+ *lemma* to_padic_int_comp_from_padic_int
- \+ *lemma* to_padic_int_comp_from_padic_int_ext
- \+ *lemma* from_padic_int_comp_to_padic_int
- \+ *lemma* from_padic_int_comp_to_padic_int_ext
- \+ *def* zmod_equiv_trunc
- \+ *def* to_zmod_pow
- \+ *def* to_padic_int
- \+ *def* from_padic_int
- \+ *def* equiv



## [2020-12-23 04:12:18](https://github.com/leanprover-community/mathlib/commit/d5adbde)
feat(data/list/basic): prefix simplifying iff lemmas ([#5452](https://github.com/leanprover-community/mathlib/pull/5452))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* prefix_take_le_iff
- \+ *lemma* cons_prefix_iff
- \+ *lemma* map_prefix



## [2020-12-23 01:30:34](https://github.com/leanprover-community/mathlib/commit/24f71d7)
chore(scripts): update nolints.txt ([#5483](https://github.com/leanprover-community/mathlib/pull/5483))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-22 20:56:38](https://github.com/leanprover-community/mathlib/commit/eba2a79)
feat(data/list/zip): length of zip_with, nth_le of zip ([#5455](https://github.com/leanprover-community/mathlib/pull/5455))
#### Estimated changes
Modified src/data/list/zip.lean
- \+ *lemma* lt_length_left_of_zip_with
- \+ *lemma* lt_length_right_of_zip_with
- \+ *lemma* lt_length_left_of_zip
- \+ *lemma* lt_length_right_of_zip
- \+ *lemma* nth_le_zip_with
- \+ *lemma* nth_le_zip
- \+ *theorem* zip_with_cons_cons
- \+ *theorem* zip_with_nil_left
- \+ *theorem* zip_with_nil_right
- \+ *theorem* length_zip_with
- \+/\- *theorem* length_zip
- \+/\- *theorem* length_zip



## [2020-12-22 17:05:18](https://github.com/leanprover-community/mathlib/commit/3fc60fc)
fix(number_theory/bernoulli): fix docstring ([#5478](https://github.com/leanprover-community/mathlib/pull/5478))
#### Estimated changes
Modified src/number_theory/bernoulli.lean



## [2020-12-22 17:05:16](https://github.com/leanprover-community/mathlib/commit/0f1362e)
chore(analysis/calculus/mean_value): use `𝓝[Ici x] x` instead of `𝓝[Ioi x] x` ([#5472](https://github.com/leanprover-community/mathlib/pull/5472))
In many parts of the library we prefer `𝓝[Ici x] x` to `𝓝[Ioi x]
x` (e.g., in assumptions line `continuous_within_at`). Fix MVT and
Gronwall's inequality to use it if possible.
Motivated by [#4945](https://github.com/leanprover-community/mathlib/pull/4945)
#### Estimated changes
Modified src/analysis/ODE/gronwall.lean

Modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* has_deriv_within_at_iff_tendsto_slope
- \+/\- *lemma* has_deriv_within_at_iff_tendsto_slope'
- \+/\- *lemma* has_deriv_at_iff_tendsto_slope
- \+ *lemma* has_deriv_within_at_diff_singleton
- \+ *lemma* has_deriv_within_at_Ioi_iff_Ici
- \+ *lemma* has_deriv_within_at_Iio_iff_Iic
- \+/\- *lemma* has_deriv_within_at_iff_tendsto_slope
- \+/\- *lemma* has_deriv_within_at_iff_tendsto_slope'
- \+/\- *lemma* has_deriv_at_iff_tendsto_slope

Modified src/analysis/calculus/mean_value.lean

Modified src/order/boolean_algebra.lean
- \+ *lemma* sdiff_idem_right



## [2020-12-22 17:05:14](https://github.com/leanprover-community/mathlib/commit/fb99440)
feat(data/complex/is_R_or_C): register some instances ([#5466](https://github.com/leanprover-community/mathlib/pull/5466))
Register a couple of facts which were previously known for `ℝ` and `ℂ` individually, but not for the typeclass `[is_R_or_C K]`:
- such a field `K` is finite-dimensional as a vector space over `ℝ`
- finite-dimensional normed spaces over `K` are proper.
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Instances.20for.20is_R_or_C
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean

Modified src/data/complex/is_R_or_C.lean



## [2020-12-22 17:05:12](https://github.com/leanprover-community/mathlib/commit/7c2f166)
chore(analysis/special_functions/trigonometric): review continuity of `tan` ([#5429](https://github.com/leanprover-community/mathlib/pull/5429))
* prove that `tan` is discontinuous at `x` whenever `cos x = 0`;
* turn `continuous_at_tan` and `differentiable_at_tan` into `iff` lemmas;
* reformulate various lemmas in terms of `cos x = 0` instead of `∃ k, x = ...`;
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* continuous_of_real

Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* tan_pi_div_two
- \+/\- *lemma* has_deriv_at_tan
- \+ *lemma* tendsto_abs_tan_of_cos_eq_zero
- \+ *lemma* tendsto_abs_tan_at_top
- \+ *lemma* continuous_at_tan
- \+/\- *lemma* differentiable_at_tan
- \+/\- *lemma* deriv_tan
- \+/\- *lemma* has_deriv_at_tan
- \+ *lemma* tendsto_abs_tan_of_cos_eq_zero
- \+ *lemma* tendsto_abs_tan_at_top
- \+ *lemma* continuous_at_tan
- \+/\- *lemma* differentiable_at_tan
- \+/\- *lemma* deriv_tan
- \+/\- *lemma* has_deriv_at_tan
- \+/\- *lemma* differentiable_at_tan
- \+/\- *lemma* deriv_tan
- \+/\- *lemma* has_deriv_at_tan
- \+/\- *lemma* differentiable_at_tan
- \+/\- *lemma* deriv_tan
- \- *lemma* continuous_tan
- \- *lemma* deriv_tan_of_mem_Ioo



## [2020-12-22 17:05:09](https://github.com/leanprover-community/mathlib/commit/d569d63)
refactor(analysis/inner_product_space, geometry/euclidean) range of orthogonal projection ([#5408](https://github.com/leanprover-community/mathlib/pull/5408))
Previously, the orthogonal projection was defined for all subspaces of an inner product space, with the junk value `id` if the space was not complete; then all nontrivial lemmas required a hypothesis of completeness (and nonemptiness for the affine orthogonal projection).  Change this to a definition only for subspaces `K` satisfying `[complete_space K]` (and `[nonempty K]` for the affine orthogonal projection).
Previously, the orthogonal projection was a linear map from `E` to `E`.  Redefine it to be a linear map from `E` to `K`.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Orthogonal.20projection)
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+/\- *lemma* orthogonal_projection_fn_mem
- \+/\- *lemma* orthogonal_projection_fn_inner_eq_zero
- \+/\- *lemma* eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
- \+/\- *lemma* orthogonal_projection_fn_eq
- \+/\- *lemma* orthogonal_projection_inner_eq_zero
- \+/\- *lemma* eq_orthogonal_projection_of_mem_of_inner_eq_zero
- \+ *lemma* eq_orthogonal_projection_of_eq_submodule
- \+/\- *lemma* orthogonal_projection_fn_mem
- \+/\- *lemma* orthogonal_projection_fn_inner_eq_zero
- \+/\- *lemma* eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
- \- *lemma* orthogonal_projection_def
- \+/\- *lemma* orthogonal_projection_fn_eq
- \- *lemma* orthogonal_projection_mem
- \+/\- *lemma* orthogonal_projection_inner_eq_zero
- \+/\- *lemma* eq_orthogonal_projection_of_mem_of_inner_eq_zero
- \+/\- *def* orthogonal_projection_fn
- \+/\- *def* orthogonal_projection
- \+/\- *def* orthogonal_projection_fn
- \- *def* orthogonal_projection_of_complete
- \+/\- *def* orthogonal_projection

Modified src/data/finset/basic.lean

Modified src/geometry/euclidean/basic.lean
- \+/\- *lemma* inter_eq_singleton_orthogonal_projection_fn
- \+/\- *lemma* orthogonal_projection_fn_mem
- \+/\- *lemma* orthogonal_projection_fn_mem_orthogonal
- \+/\- *lemma* orthogonal_projection_fn_vsub_mem_direction_orthogonal
- \+/\- *lemma* orthogonal_projection_fn_eq
- \+/\- *lemma* orthogonal_projection_linear
- \+/\- *lemma* inter_eq_singleton_orthogonal_projection
- \+/\- *lemma* orthogonal_projection_mem
- \+/\- *lemma* orthogonal_projection_mem_orthogonal
- \+/\- *lemma* orthogonal_projection_vsub_mem_direction
- \+/\- *lemma* vsub_orthogonal_projection_mem_direction
- \+/\- *lemma* orthogonal_projection_eq_self_iff
- \+/\- *lemma* orthogonal_projection_orthogonal_projection
- \+ *lemma* eq_orthogonal_projection_of_eq_subspace
- \+/\- *lemma* dist_orthogonal_projection_eq_zero_iff
- \+/\- *lemma* dist_orthogonal_projection_ne_zero_of_not_mem
- \+/\- *lemma* orthogonal_projection_vsub_mem_direction_orthogonal
- \+/\- *lemma* vsub_orthogonal_projection_mem_direction_orthogonal
- \+/\- *lemma* orthogonal_projection_vadd_eq_self
- \+/\- *lemma* reflection_apply
- \+ *lemma* eq_reflection_of_eq_subspace
- \+/\- *lemma* reflection_symm
- \+/\- *lemma* reflection_reflection
- \+/\- *lemma* reflection_involutive
- \+/\- *lemma* reflection_eq_self_iff
- \+/\- *lemma* reflection_eq_iff_orthogonal_projection_eq
- \+/\- *lemma* dist_reflection
- \+/\- *lemma* dist_reflection_eq_of_mem
- \+/\- *lemma* reflection_mem_of_le_of_mem
- \+/\- *lemma* reflection_orthogonal_vadd
- \+/\- *lemma* reflection_vadd_smul_vsub_orthogonal_projection
- \+/\- *lemma* inter_eq_singleton_orthogonal_projection_fn
- \+/\- *lemma* orthogonal_projection_fn_mem
- \+/\- *lemma* orthogonal_projection_fn_mem_orthogonal
- \+/\- *lemma* orthogonal_projection_fn_vsub_mem_direction_orthogonal
- \- *lemma* orthogonal_projection_def
- \+/\- *lemma* orthogonal_projection_fn_eq
- \+/\- *lemma* orthogonal_projection_linear
- \- *lemma* orthogonal_projection_of_nonempty_of_complete_eq
- \+/\- *lemma* inter_eq_singleton_orthogonal_projection
- \+/\- *lemma* orthogonal_projection_mem
- \+/\- *lemma* orthogonal_projection_mem_orthogonal
- \+/\- *lemma* orthogonal_projection_vsub_mem_direction
- \+/\- *lemma* vsub_orthogonal_projection_mem_direction
- \+/\- *lemma* orthogonal_projection_eq_self_iff
- \+/\- *lemma* orthogonal_projection_orthogonal_projection
- \+/\- *lemma* dist_orthogonal_projection_eq_zero_iff
- \+/\- *lemma* dist_orthogonal_projection_ne_zero_of_not_mem
- \+/\- *lemma* orthogonal_projection_vsub_mem_direction_orthogonal
- \+/\- *lemma* vsub_orthogonal_projection_mem_direction_orthogonal
- \+/\- *lemma* orthogonal_projection_vadd_eq_self
- \+/\- *lemma* reflection_apply
- \+/\- *lemma* reflection_symm
- \+/\- *lemma* reflection_reflection
- \+/\- *lemma* reflection_involutive
- \+/\- *lemma* reflection_eq_self_iff
- \+/\- *lemma* reflection_eq_iff_orthogonal_projection_eq
- \+/\- *lemma* dist_reflection
- \+/\- *lemma* dist_reflection_eq_of_mem
- \+/\- *lemma* reflection_mem_of_le_of_mem
- \+/\- *lemma* reflection_orthogonal_vadd
- \+/\- *lemma* reflection_vadd_smul_vsub_orthogonal_projection
- \+/\- *def* orthogonal_projection_fn
- \+/\- *def* orthogonal_projection
- \+/\- *def* reflection
- \+/\- *def* orthogonal_projection_fn
- \- *def* orthogonal_projection_of_nonempty_of_complete
- \+/\- *def* orthogonal_projection
- \+/\- *def* reflection

Modified src/geometry/euclidean/circumcenter.lean
- \+/\- *lemma* dist_eq_iff_dist_orthogonal_projection_eq
- \+/\- *lemma* dist_set_eq_iff_dist_orthogonal_projection_eq
- \+/\- *lemma* exists_dist_eq_iff_exists_dist_orthogonal_projection_eq
- \+/\- *lemma* dist_eq_iff_dist_orthogonal_projection_eq
- \+/\- *lemma* dist_set_eq_iff_dist_orthogonal_projection_eq
- \+/\- *lemma* exists_dist_eq_iff_exists_dist_orthogonal_projection_eq

Modified src/geometry/euclidean/monge_point.lean

Modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* coe_vsub
- \+ *lemma* coe_vadd



## [2020-12-22 17:05:07](https://github.com/leanprover-community/mathlib/commit/0ff9068)
feat(data/finset/basic, topology/separation): add induction_on_union, separate, and separate_finset_of_t2 ([#5332](https://github.com/leanprover-community/mathlib/pull/5332))
prove lemma disjoint_finsets_opens_of_t2 showing that in a t2_space disjoint finsets have disjoint open neighbourhoods, using auxiliary lemma not_mem_finset_opens_of_t2.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* induction_on_union

Modified src/topology/separation.lean
- \+ *lemma* symm
- \+ *lemma* comm
- \+ *lemma* empty_right
- \+ *lemma* empty_left
- \+ *lemma* union_left
- \+ *lemma* union_right
- \+ *lemma* finset_disjoint_finset_opens_of_t2
- \+ *lemma* point_disjoint_finset_opens_of_t2
- \+ *def* separated



## [2020-12-22 13:47:43](https://github.com/leanprover-community/mathlib/commit/02ab90c)
chore(*): split some long lines ([#5470](https://github.com/leanprover-community/mathlib/pull/5470))
#### Estimated changes
Modified src/algebra/category/CommRing/colimits.lean
- \+/\- *lemma* quot_neg
- \+/\- *lemma* quot_add
- \+/\- *lemma* quot_mul
- \+/\- *lemma* quot_neg
- \+/\- *lemma* quot_add
- \+/\- *lemma* quot_mul

Modified src/algebra/category/Group/limits.lean

Modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* ne_zero
- \+/\- *lemma* ne_zero

Modified src/algebra/ordered_group.lean

Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* uniform_space.core_eq
- \+/\- *lemma* nhds_basis_uniformity'
- \+/\- *lemma* filter.has_basis.uniform_continuous_on_iff
- \+/\- *lemma* uniform_continuous_on_iff_restrict
- \+/\- *lemma* mem_uniform_prod
- \+/\- *lemma* uniform_continuous_fst
- \+/\- *lemma* uniform_continuous_snd
- \+/\- *lemma* uniform_space.core_eq
- \+/\- *lemma* nhds_basis_uniformity'
- \+/\- *lemma* filter.has_basis.uniform_continuous_on_iff
- \+/\- *lemma* uniform_continuous_on_iff_restrict
- \+/\- *lemma* mem_uniform_prod
- \+/\- *lemma* uniform_continuous_fst
- \+/\- *lemma* uniform_continuous_snd

Modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* extension_coe
- \+/\- *lemma* extension_unique
- \+/\- *lemma* extension_coe
- \+/\- *lemma* extension_unique
- \+/\- *theorem* Cauchy_eq
- \+/\- *theorem* Cauchy_eq

Modified test/monotonicity/test_cases.lean



## [2020-12-22 07:50:26](https://github.com/leanprover-community/mathlib/commit/4ddae3d)
feat(ring_theory/power_series): define power series for `exp`, `sin`, `cos`, and `1 / (u - x)`. ([#5432](https://github.com/leanprover-community/mathlib/pull/5432))
This PR defines `power_series.exp` etc to be formal power series for the corresponding functions. Once we have a bridge to `is_analytic`, we should redefine `complex.exp` etc using these power series.
#### Estimated changes
Modified src/algebra/field.lean
- \+/\- *lemma* map_eq_zero
- \+/\- *lemma* map_eq_zero

Modified src/algebra/group/units_hom.lean
- \+ *lemma* coe_map_inv

Modified src/analysis/calculus/formal_multilinear_series.lean

Modified src/data/complex/is_R_or_C.lean
- \+/\- *lemma* conj_eq_zero
- \+/\- *lemma* conj_eq_zero

Renamed src/ring_theory/power_series.lean to src/ring_theory/power_series/basic.lean
- \+/\- *lemma* inv_of_unit_eq
- \+/\- *lemma* inv_of_unit_eq'
- \+/\- *lemma* inv_of_unit_eq
- \+/\- *lemma* inv_of_unit_eq'

Created src/ring_theory/power_series/well_known.lean
- \+ *lemma* coeff_inv_units_sub
- \+ *lemma* constant_coeff_inv_units_sub
- \+ *lemma* inv_units_sub_mul_X
- \+ *lemma* inv_units_sub_mul_sub
- \+ *lemma* map_inv_units_sub
- \+ *lemma* coeff_exp
- \+ *lemma* map_exp
- \+ *lemma* map_sin
- \+ *lemma* map_cos
- \+ *def* inv_units_sub
- \+ *def* exp
- \+ *def* sin
- \+ *def* cos



## [2020-12-22 03:10:44](https://github.com/leanprover-community/mathlib/commit/92dfdbc)
chore(scripts): update nolints.txt ([#5469](https://github.com/leanprover-community/mathlib/pull/5469))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-22 03:10:42](https://github.com/leanprover-community/mathlib/commit/3c7394f)
fix(group_theory/*, algebra/group): [to_additive, simp] doesn't work ([#5468](https://github.com/leanprover-community/mathlib/pull/5468))
As explained in `algebra/group/to_additive`, `@[to_additive, simp]` doesn't work (it doesn't attach a `simp` attribute to the additive lemma), but conversely `@[simps, to_additive]` is also wrong.
Along the way I also noticed that some `right_inv` (as in an inverse function) lemmas were being changed to `right_neg` by to_additive :D
#### Estimated changes
Modified src/algebra/category/Group/basic.lean

Modified src/algebra/group/hom.lean

Modified src/algebra/group/semiconj.lean
- \+/\- *lemma* mul_right
- \+/\- *lemma* mul_right

Modified src/algebra/ordered_monoid.lean

Modified src/group_theory/monoid_localization.lean
- \+/\- *lemma* mul_equiv_of_localizations_apply
- \+/\- *lemma* mul_equiv_of_localizations_symm_apply
- \+/\- *lemma* of_mul_equiv_of_localizations_apply
- \+/\- *lemma* mul_equiv_of_localizations_right_inv
- \+/\- *lemma* mul_equiv_of_localizations_right_inv_apply
- \+/\- *lemma* mul_equiv_of_localizations_left_inv_apply
- \+/\- *lemma* of_mul_equiv_of_dom_apply
- \+/\- *lemma* of_mul_equiv_of_mul_equiv_apply
- \+/\- *lemma* mul_equiv_of_localizations_apply
- \+/\- *lemma* mul_equiv_of_localizations_symm_apply
- \+/\- *lemma* of_mul_equiv_of_localizations_apply
- \+/\- *lemma* mul_equiv_of_localizations_right_inv
- \+/\- *lemma* mul_equiv_of_localizations_right_inv_apply
- \+/\- *lemma* mul_equiv_of_localizations_left_inv_apply
- \+/\- *lemma* of_mul_equiv_of_dom_apply
- \+/\- *lemma* of_mul_equiv_of_mul_equiv_apply

Modified src/group_theory/submonoid/operations.lean

Modified src/topology/algebra/monoid.lean



## [2020-12-21 23:51:24](https://github.com/leanprover-community/mathlib/commit/9ec2778)
chore(data/{equiv,set}/basic): image_preimage ([#5465](https://github.com/leanprover-community/mathlib/pull/5465))
* `equiv.symm_image_image`: add `@[simp]`;
* `equiv.image_preimage`, `equiv.preimage_image`: new `simp` lemmas;
* `set.image_preimage_eq`, `set.preimage_image_eq`: make `s : set _` an explicit argument;
* `function.injective.preimage_image`, `function.surjective.image_preimage`: new aliases for `set.preimage_image_eq`
  and `set.image_preimage_eq` with arguments reversed
Also golf a proof about `separated`.
#### Estimated changes
Modified src/analysis/convex/basic.lean

Modified src/data/equiv/basic.lean
- \+/\- *lemma* symm_image_image
- \+ *lemma* image_preimage
- \+ *lemma* preimage_image
- \+/\- *lemma* symm_image_image

Modified src/data/set/basic.lean
- \+/\- *lemma* preimage_eq_preimage
- \+ *lemma* injective.preimage_image
- \+ *lemma* surjective.image_preimage
- \+/\- *lemma* preimage_eq_preimage
- \+/\- *theorem* image_preimage_eq
- \+/\- *theorem* image_preimage_eq

Modified src/order/semiconj_Sup.lean

Modified src/topology/homeomorph.lean

Modified src/topology/maps.lean

Modified src/topology/uniform_space/separation.lean



## [2020-12-21 20:56:39](https://github.com/leanprover-community/mathlib/commit/d2ae43f)
feat(data/list/basic): lemmas about nth of take and append ([#5449](https://github.com/leanprover-community/mathlib/pull/5449))
#### Estimated changes
Modified src/data/list/basic.lean
- \+/\- *lemma* nth_append
- \+ *lemma* nth_append_right
- \+ *lemma* nth_take
- \+ *lemma* nth_take_of_succ
- \+ *lemma* take_succ
- \+/\- *lemma* nth_append



## [2020-12-21 20:56:37](https://github.com/leanprover-community/mathlib/commit/3b9cbdf)
feat(data/ordmap): Ordered maps (like rb_map but better) ([#5353](https://github.com/leanprover-community/mathlib/pull/5353))
This cleans up an old mathlib branch from 2 years ago, so it probably isn't in very modern style, but it would be best to get it merged and kept up to date rather than leaving it to rot.
It is an implementation of size balanced ordered maps based on Haskell's `Data.Map.Strict`. The `ordnode` structure can be used directly if one is only interested in using it for programming purposes, and the `ordset` structure bundles the proofs so that you can prove theorems about inserting and deleting doing what you expect.
#### Estimated changes
Modified docs/overview.yaml

Modified src/algebra/order.lean
- \+ *theorem* cmp_le_swap
- \+ *theorem* cmp_le_eq_cmp
- \+ *def* cmp_le

Modified src/data/nat/dist.lean
- \+ *theorem* dist_tri_left
- \+ *theorem* dist_tri_right
- \+ *theorem* dist_tri_left'
- \+ *theorem* dist_tri_right'

Modified src/data/nat/psub.lean
- \+/\- *theorem* psub_eq_none
- \+ *theorem* psub'_eq_psub
- \+/\- *theorem* psub_eq_none
- \+ *def* psub'

Created src/data/ordmap/ordnode.lean
- \+ *def* delta
- \+ *def* ratio
- \+ *def* size
- \+ *def* empty
- \+ *def* dual
- \+ *def* node'
- \+ *def* repr
- \+ *def* balance_l
- \+ *def* balance_r
- \+ *def* balance
- \+ *def* all
- \+ *def* any
- \+ *def* emem
- \+ *def* amem
- \+ *def* find_min'
- \+ *def* find_min
- \+ *def* find_max'
- \+ *def* find_max
- \+ *def* erase_min
- \+ *def* erase_max
- \+ *def* split_min'
- \+ *def* split_min
- \+ *def* split_max'
- \+ *def* split_max
- \+ *def* glue
- \+ *def* merge
- \+ *def* insert_max
- \+ *def* insert_min
- \+ *def* link
- \+ *def* filter
- \+ *def* partition
- \+ *def* map
- \+ *def* fold
- \+ *def* foldl
- \+ *def* foldr
- \+ *def* to_list
- \+ *def* to_rev_list
- \+ *def* equiv
- \+ *def* powerset
- \+ *def* pmap
- \+ *def* attach'
- \+ *def* nth
- \+ *def* remove_nth
- \+ *def* take_aux
- \+ *def* take
- \+ *def* drop_aux
- \+ *def* drop
- \+ *def* split_at_aux
- \+ *def* split_at
- \+ *def* take_while
- \+ *def* drop_while
- \+ *def* span
- \+ *def* of_asc_list_aux₁
- \+ *def* of_asc_list_aux₂
- \+ *def* of_asc_list
- \+ *def* mem
- \+ *def* find
- \+ *def* insert_with
- \+ *def* adjust_with
- \+ *def* update_with
- \+ *def* alter
- \+ *def* insert'
- \+ *def* split
- \+ *def* split3
- \+ *def* erase
- \+ *def* find_lt_aux
- \+ *def* find_lt
- \+ *def* find_gt_aux
- \+ *def* find_gt
- \+ *def* find_le_aux
- \+ *def* find_le
- \+ *def* find_ge_aux
- \+ *def* find_ge
- \+ *def* find_index_aux
- \+ *def* find_index
- \+ *def* is_subset_aux
- \+ *def* is_subset
- \+ *def* disjoint
- \+ *def* union
- \+ *def* diff
- \+ *def* inter
- \+ *def* of_list
- \+ *def* of_list'
- \+ *def* image

Created src/data/ordmap/ordset.lean
- \+ *theorem* will
- \+ *theorem* not_le_delta
- \+ *theorem* delta_lt_false
- \+ *theorem* sized.node'
- \+ *theorem* sized.eq_node'
- \+ *theorem* sized.size_eq
- \+ *theorem* sized.induction
- \+ *theorem* size_eq_real_size
- \+ *theorem* sized.size_eq_zero
- \+ *theorem* sized.pos
- \+ *theorem* dual_dual
- \+ *theorem* size_dual
- \+ *theorem* balanced_sz.symm
- \+ *theorem* balanced_sz_zero
- \+ *theorem* balanced_sz_up
- \+ *theorem* balanced_sz_down
- \+ *theorem* balanced.dual
- \+ *theorem* dual_node'
- \+ *theorem* dual_node3_l
- \+ *theorem* dual_node3_r
- \+ *theorem* dual_node4_l
- \+ *theorem* dual_node4_r
- \+ *theorem* dual_rotate_l
- \+ *theorem* dual_rotate_r
- \+ *theorem* dual_balance'
- \+ *theorem* dual_balance_l
- \+ *theorem* dual_balance_r
- \+ *theorem* sized.node3_l
- \+ *theorem* sized.node3_r
- \+ *theorem* sized.node4_l
- \+ *theorem* node3_l_size
- \+ *theorem* node3_r_size
- \+ *theorem* node4_l_size
- \+ *theorem* sized.dual
- \+ *theorem* sized.dual_iff
- \+ *theorem* sized.rotate_l
- \+ *theorem* sized.rotate_r
- \+ *theorem* sized.rotate_l_size
- \+ *theorem* sized.rotate_r_size
- \+ *theorem* sized.balance'
- \+ *theorem* size_balance'
- \+ *theorem* all.imp
- \+ *theorem* any.imp
- \+ *theorem* all_singleton
- \+ *theorem* any_singleton
- \+ *theorem* all_dual
- \+ *theorem* all_iff_forall
- \+ *theorem* any_iff_exists
- \+ *theorem* emem_iff_all
- \+ *theorem* all_node'
- \+ *theorem* all_node3_l
- \+ *theorem* all_node3_r
- \+ *theorem* all_node4_l
- \+ *theorem* all_node4_r
- \+ *theorem* all_rotate_l
- \+ *theorem* all_rotate_r
- \+ *theorem* all_balance'
- \+ *theorem* foldr_cons_eq_to_list
- \+ *theorem* to_list_nil
- \+ *theorem* to_list_node
- \+ *theorem* emem_iff_mem_to_list
- \+ *theorem* length_to_list'
- \+ *theorem* length_to_list
- \+ *theorem* equiv_iff
- \+ *theorem* find_min'_dual
- \+ *theorem* find_max'_dual
- \+ *theorem* find_min_dual
- \+ *theorem* find_max_dual
- \+ *theorem* dual_erase_min
- \+ *theorem* dual_erase_max
- \+ *theorem* split_min_eq
- \+ *theorem* split_max_eq
- \+ *theorem* find_min'_all
- \+ *theorem* find_max'_all
- \+ *theorem* merge_nil_left
- \+ *theorem* merge_nil_right
- \+ *theorem* merge_node
- \+ *theorem* dual_insert
- \+ *theorem* balance_eq_balance'
- \+ *theorem* balance_l_eq_balance
- \+ *theorem* raised_iff
- \+ *theorem* raised.dist_le
- \+ *theorem* raised.dist_le'
- \+ *theorem* raised.add_left
- \+ *theorem* raised.add_right
- \+ *theorem* raised.right
- \+ *theorem* balance_l_eq_balance'
- \+ *theorem* balance_sz_dual
- \+ *theorem* size_balance_l
- \+ *theorem* all_balance_l
- \+ *theorem* balance_r_eq_balance'
- \+ *theorem* size_balance_r
- \+ *theorem* all_balance_r
- \+ *theorem* bounded.dual
- \+ *theorem* bounded.dual_iff
- \+ *theorem* bounded.weak_left
- \+ *theorem* bounded.weak_right
- \+ *theorem* bounded.weak
- \+ *theorem* bounded.mono_left
- \+ *theorem* bounded.mono_right
- \+ *theorem* bounded.to_lt
- \+ *theorem* bounded.to_nil
- \+ *theorem* bounded.trans_left
- \+ *theorem* bounded.trans_right
- \+ *theorem* bounded.mem_lt
- \+ *theorem* bounded.mem_gt
- \+ *theorem* bounded.of_lt
- \+ *theorem* bounded.of_gt
- \+ *theorem* bounded.to_sep
- \+ *theorem* valid'.mono_left
- \+ *theorem* valid'.mono_right
- \+ *theorem* valid'.trans_left
- \+ *theorem* valid'.trans_right
- \+ *theorem* valid'.of_lt
- \+ *theorem* valid'.of_gt
- \+ *theorem* valid'.valid
- \+ *theorem* valid'_nil
- \+ *theorem* valid_nil
- \+ *theorem* valid'.node
- \+ *theorem* valid'.dual
- \+ *theorem* valid'.dual_iff
- \+ *theorem* valid.dual
- \+ *theorem* valid.dual_iff
- \+ *theorem* valid'.left
- \+ *theorem* valid'.right
- \+ *theorem* valid.left
- \+ *theorem* valid.right
- \+ *theorem* valid.size_eq
- \+ *theorem* valid'.node'
- \+ *theorem* valid'_singleton
- \+ *theorem* valid_singleton
- \+ *theorem* valid'.node3_l
- \+ *theorem* valid'.node3_r
- \+ *theorem* valid'.node4_l_lemma₁
- \+ *theorem* valid'.node4_l_lemma₂
- \+ *theorem* valid'.node4_l_lemma₃
- \+ *theorem* valid'.node4_l_lemma₄
- \+ *theorem* valid'.node4_l_lemma₅
- \+ *theorem* valid'.node4_l
- \+ *theorem* valid'.rotate_l_lemma₁
- \+ *theorem* valid'.rotate_l_lemma₂
- \+ *theorem* valid'.rotate_l_lemma₃
- \+ *theorem* valid'.rotate_l_lemma₄
- \+ *theorem* valid'.rotate_l
- \+ *theorem* valid'.rotate_r
- \+ *theorem* valid'.balance'_aux
- \+ *theorem* valid'.balance'_lemma
- \+ *theorem* valid'.balance'
- \+ *theorem* valid'.balance
- \+ *theorem* valid'.balance_l_aux
- \+ *theorem* valid'.balance_l
- \+ *theorem* valid'.balance_r_aux
- \+ *theorem* valid'.balance_r
- \+ *theorem* valid'.erase_max_aux
- \+ *theorem* valid'.erase_min_aux
- \+ *theorem* erase_min.valid
- \+ *theorem* erase_max.valid
- \+ *theorem* valid'.glue_aux
- \+ *theorem* valid'.glue
- \+ *theorem* valid'.merge_lemma
- \+ *theorem* valid'.merge_aux₁
- \+ *theorem* valid'.merge_aux
- \+ *theorem* valid.merge
- \+ *theorem* insert_with.valid_aux
- \+ *theorem* insert_with.valid
- \+ *theorem* insert_eq_insert_with
- \+ *theorem* insert.valid
- \+ *theorem* insert'_eq_insert_with
- \+ *theorem* insert'.valid
- \+ *theorem* empty_iff
- \+ *def* real_size
- \+ *def* sized
- \+ *def* balanced_sz
- \+ *def* balanced
- \+ *def* node3_l
- \+ *def* node3_r
- \+ *def* node4_l
- \+ *def* node4_r
- \+ *def* rotate_l
- \+ *def* rotate_r
- \+ *def* balance_l'
- \+ *def* balance_r'
- \+ *def* balance'
- \+ *def* raised
- \+ *def* bounded
- \+ *def* valid
- \+ *def* ordset
- \+ *def* nil
- \+ *def* size
- \+ *def* empty
- \+ *def* insert'

Modified src/order/basic.lean
- \+ *theorem* preorder.dual_dual
- \+ *theorem* partial_order.dual_dual
- \+ *theorem* linear_order.dual_dual
- \+ *theorem* cmp_le_flip



## [2020-12-21 17:48:50](https://github.com/leanprover-community/mathlib/commit/bc3ad25)
feat(linear_algebra/tensor_algebra): Add missing lemmas about subtraction ([#5428](https://github.com/leanprover-community/mathlib/pull/5428))
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean
- \+/\- *lemma* neg_tmul
- \+ *lemma* tmul_sub
- \+ *lemma* sub_tmul
- \+/\- *lemma* neg_tmul
- \+ *theorem* map_sub₂



## [2020-12-21 17:48:49](https://github.com/leanprover-community/mathlib/commit/34d5750)
feat(data/option/basic): lemmas on map of none and congr ([#5424](https://github.com/leanprover-community/mathlib/pull/5424))
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* map_eq_none
- \+ *lemma* map_eq_none'
- \+ *lemma* map_congr



## [2020-12-21 16:45:47](https://github.com/leanprover-community/mathlib/commit/0ed425f)
feat(ring_theory/perfection): define characteristic predicate of perfection ([#5386](https://github.com/leanprover-community/mathlib/pull/5386))
Name changes:
- `perfect_field` --> `perfect_ring` (generalization)
- `semiring.perfection` --> `ring.perfection`
- Original `ring.perfection` deleted.
#### Estimated changes
Modified src/field_theory/perfect_closure.lean
- \+/\- *lemma* coe_frobenius_equiv
- \+ *lemma* coe_frobenius_equiv_symm
- \+ *lemma* injective_pow_p
- \+/\- *lemma* coe_frobenius_equiv
- \+/\- *theorem* frobenius_pth_root
- \+ *theorem* pth_root_pow_p
- \+/\- *theorem* pth_root_frobenius
- \+ *theorem* pth_root_pow_p'
- \+/\- *theorem* left_inverse_pth_root_frobenius
- \+ *theorem* right_inverse_pth_root_frobenius
- \+ *theorem* commute_frobenius_pth_root
- \+/\- *theorem* eq_pth_root_iff
- \+/\- *theorem* pth_root_eq_iff
- \+/\- *theorem* monoid_hom.map_pth_root
- \+/\- *theorem* monoid_hom.map_iterate_pth_root
- \+/\- *theorem* ring_hom.map_pth_root
- \+/\- *theorem* ring_hom.map_iterate_pth_root
- \+/\- *theorem* frobenius_pth_root
- \+/\- *theorem* pth_root_frobenius
- \+/\- *theorem* left_inverse_pth_root_frobenius
- \+/\- *theorem* eq_pth_root_iff
- \+/\- *theorem* pth_root_eq_iff
- \+/\- *theorem* monoid_hom.map_pth_root
- \+/\- *theorem* monoid_hom.map_iterate_pth_root
- \+/\- *theorem* ring_hom.map_pth_root
- \+/\- *theorem* ring_hom.map_iterate_pth_root
- \+/\- *def* frobenius_equiv
- \+/\- *def* pth_root
- \+/\- *def* lift
- \+/\- *def* frobenius_equiv
- \+/\- *def* pth_root
- \+/\- *def* lift

Modified src/ring_theory/perfection.lean
- \+ *lemma* coeff_mk
- \+ *lemma* coeff_iterate_frobenius
- \+ *lemma* coeff_iterate_frobenius'
- \+ *lemma* mk'
- \+ *lemma* of
- \+ *lemma* id
- \+/\- *def* ring.perfection
- \+ *def* lift
- \- *def* semiring.perfection
- \+/\- *def* ring.perfection



## [2020-12-21 15:29:49](https://github.com/leanprover-community/mathlib/commit/96a2aa1)
feat(ring_theory/roots_of_unity): add minimal_polynomial_eq_pow ([#5444](https://github.com/leanprover-community/mathlib/pull/5444))
This is the main result about minimal polynomial of primitive roots of unity: `μ` and `μ ^ p` have the same minimal polynomial.
The proof is a little long, but I don't see how I can split it: it is entirely by contradiction, so any lemma extracted from it would start with a false assumption and at the end it would be used only in this proof.
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* minimal_polynomial_eq_pow



## [2020-12-21 14:00:44](https://github.com/leanprover-community/mathlib/commit/c5c02ec)
feat(category_theory/yoneda): add iso_comp_punit ([#5448](https://github.com/leanprover-community/mathlib/pull/5448))
A presheaf P : C^{op} -> Type v is isomorphic to the composition of P with the coyoneda functor Type v -> Type v associated to `punit`.
[This is useful for developing the theory of sheaves taking values in a general category]
#### Estimated changes
Modified src/category_theory/yoneda.lean
- \+ *def* iso_comp_punit



## [2020-12-21 09:07:54](https://github.com/leanprover-community/mathlib/commit/c98d5bb)
feat(category_theory/limits): yoneda preserves limits ([#5439](https://github.com/leanprover-community/mathlib/pull/5439))
yoneda and coyoneda preserve limits
#### Estimated changes
Modified src/category_theory/limits/preserves/limits.lean

Modified src/category_theory/limits/yoneda.lean



## [2020-12-21 07:48:53](https://github.com/leanprover-community/mathlib/commit/4778e16)
chore(category_theory/sites/sheaf): rename sheaf to sheaf_of_types ([#5458](https://github.com/leanprover-community/mathlib/pull/5458))
I wanted to add sheaves with values in general categories, so I moved sheaf.lean to sheaf_of_types.lean and then added a new file sheaf.lean. Github then produced an incomprehensible diff file because sheaf.lean had completely changed. Hence I propose first moving `sheaf.lean` to `sheaf_of_types.lean` and then adding a new `sheaf.lean` later. As well as moving the file, I also slightly change it.
#### Estimated changes
Modified src/category_theory/sites/canonical.lean

Renamed src/category_theory/sites/sheaf.lean to src/category_theory/sites/sheaf_of_types.lean
- \+ *def* SheafOfTypes
- \+ *def* SheafOfTypes_to_presheaf
- \- *def* Sheaf
- \- *def* Sheaf_to_presheaf

Modified src/category_theory/sites/types.lean
- \+/\- *lemma* eval_app
- \+/\- *lemma* eval_app
- \+/\- *def* yoneda'
- \+/\- *def* yoneda'



## [2020-12-21 01:32:14](https://github.com/leanprover-community/mathlib/commit/ca2e536)
chore(scripts): update nolints.txt ([#5459](https://github.com/leanprover-community/mathlib/pull/5459))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-20 11:33:02](https://github.com/leanprover-community/mathlib/commit/d79105e)
feat(tactic/field_simp): let field_simp use norm_num to prove numerals are nonzero ([#5418](https://github.com/leanprover-community/mathlib/pull/5418))
As suggested by @robertylewis in https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Solving.20simple.20%28in%29equalities.20gets.20frustrating/near/220278546, change the discharger in `field_simp` to try `assumption` on  goals `x ≠ 0` and `norm_num1` on these goals when `x` is a numeral.
#### Estimated changes
Modified archive/100-theorems-list/42_inverse_triangle_sum.lean

Modified archive/imo/imo1962_q4.lean

Modified src/algebra/continued_fractions/convergents_equiv.lean

Modified src/algebra/group_with_zero/basic.lean
- \+/\- *theorem* mul_ne_zero
- \+/\- *theorem* mul_ne_zero

Modified src/analysis/special_functions/trigonometric.lean

Modified src/data/rat/floor.lean

Modified src/data/real/golden_ratio.lean

Modified src/data/real/nnreal.lean
- \- *theorem* mul_ne_zero'

Modified src/field_theory/splitting_field.lean

Modified src/linear_algebra/affine_space/ordered.lean

Modified src/number_theory/pythagorean_triples.lean

Modified src/ring_theory/fractional_ideal.lean

Modified src/ring_theory/perfection.lean

Created src/tactic/field_simp.lean

Modified src/tactic/interactive.lean

Modified test/ring.lean

Modified test/ring_exp.lean



## [2020-12-20 09:21:32](https://github.com/leanprover-community/mathlib/commit/5010738)
feat(topology/algebra/ordered): continuity of `abs` ([#5412](https://github.com/leanprover-community/mathlib/pull/5412))
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean

Modified src/topology/algebra/ordered.lean
- \+ *lemma* continuous_abs
- \+ *lemma* filter.tendsto.abs
- \+ *lemma* continuous.abs
- \+ *lemma* continuous_at.abs
- \+ *lemma* continuous_within_at.abs
- \+ *lemma* continuous_on.abs
- \+ *lemma* tendsto_abs_nhds_within_zero

Modified src/topology/basic.lean
- \+/\- *lemma* continuous_const
- \+/\- *lemma* continuous_const

Modified src/topology/instances/real.lean
- \- *lemma* real.continuous_abs
- \- *lemma* rat.continuous_abs



## [2020-12-20 01:39:55](https://github.com/leanprover-community/mathlib/commit/a9fb069)
chore(scripts): update nolints.txt ([#5441](https://github.com/leanprover-community/mathlib/pull/5441))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-19 20:45:22](https://github.com/leanprover-community/mathlib/commit/1cb9727)
feat(field_theory/galois): Separable splitting field is Galois ([#5347](https://github.com/leanprover-community/mathlib/pull/5347))
Proves that a splitting field of a separable polynomial is Galois by showing that it has lots of automorphisms.
#### Estimated changes
Modified src/field_theory/galois.lean
- \+ *lemma* of_fixed_field_eq_bot
- \+ *lemma* of_card_aut_eq_findim
- \+ *lemma* of_separable_splitting_field_aux
- \+ *lemma* of_separable_splitting_field



## [2020-12-19 17:55:35](https://github.com/leanprover-community/mathlib/commit/e22fb94)
chore(data/nat/cast,algebra/ordered_group): 2 trivial lemmas ([#5436](https://github.com/leanprover-community/mathlib/pull/5436))
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* inv_lt_self

Modified src/data/nat/cast.lean
- \+ *lemma* one_le_iff_pos



## [2020-12-19 17:55:33](https://github.com/leanprover-community/mathlib/commit/5de6757)
chore(algebra/ordered_group): deduplicate ([#5403](https://github.com/leanprover-community/mathlib/pull/5403))
I deleted many `a_of_b` lemmas for which `a_iff_b` existed, then restored (most? all?) of them using `alias` command.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean

Modified src/algebra/ordered_group.lean
- \+/\- *lemma* sub_le_self_iff
- \+/\- *lemma* sub_lt_self_iff
- \+/\- *lemma* sub_le_sub_left
- \+/\- *lemma* sub_le_sub_right
- \+/\- *lemma* sub_lt_sub_left
- \+/\- *lemma* sub_lt_sub_right
- \+ *lemma* sub_le_of_abs_sub_le_left
- \+ *lemma* sub_le_of_abs_sub_le_right
- \+ *lemma* sub_lt_of_abs_sub_lt_left
- \+ *lemma* sub_lt_of_abs_sub_lt_right
- \+ *lemma* exists_zero_lt
- \- *lemma* sub_nonneg_of_le
- \- *lemma* le_of_sub_nonneg
- \- *lemma* sub_nonpos_of_le
- \- *lemma* le_of_sub_nonpos
- \- *lemma* sub_pos_of_lt
- \- *lemma* lt_of_sub_pos
- \- *lemma* sub_neg_of_lt
- \- *lemma* lt_of_sub_neg
- \- *lemma* add_le_of_le_sub_left
- \- *lemma* le_sub_left_of_add_le
- \- *lemma* add_le_of_le_sub_right
- \- *lemma* le_sub_right_of_add_le
- \- *lemma* le_add_of_sub_left_le
- \- *lemma* sub_left_le_of_le_add
- \- *lemma* le_add_of_sub_right_le
- \- *lemma* sub_right_le_of_le_add
- \- *lemma* le_add_of_neg_le_sub_left
- \- *lemma* neg_le_sub_left_of_le_add
- \- *lemma* le_add_of_neg_le_sub_right
- \- *lemma* neg_le_sub_right_of_le_add
- \- *lemma* sub_le_of_sub_le
- \+/\- *lemma* sub_le_sub_left
- \+/\- *lemma* sub_le_sub_right
- \- *lemma* add_lt_of_lt_sub_left
- \- *lemma* lt_sub_left_of_add_lt
- \- *lemma* add_lt_of_lt_sub_right
- \- *lemma* lt_sub_right_of_add_lt
- \- *lemma* lt_add_of_sub_left_lt
- \- *lemma* sub_left_lt_of_lt_add
- \- *lemma* lt_add_of_sub_right_lt
- \- *lemma* sub_right_lt_of_lt_add
- \- *lemma* lt_add_of_neg_lt_sub_left
- \- *lemma* neg_lt_sub_left_of_lt_add
- \- *lemma* lt_add_of_neg_lt_sub_right
- \- *lemma* neg_lt_sub_right_of_lt_add
- \- *lemma* sub_lt_of_sub_lt
- \+/\- *lemma* sub_lt_sub_left
- \+/\- *lemma* sub_lt_sub_right
- \- *lemma* sub_lt_sub_of_le_of_lt
- \- *lemma* sub_lt_sub_of_lt_of_le
- \- *lemma* sub_le_self
- \- *lemma* sub_lt_self
- \+/\- *lemma* sub_le_self_iff
- \+/\- *lemma* sub_lt_self_iff
- \- *lemma* exists_gt_zero

Modified src/algebra/ordered_ring.lean
- \- *lemma* sub_le_of_abs_sub_le_left
- \- *lemma* sub_le_of_abs_sub_le_right
- \- *lemma* sub_lt_of_abs_sub_lt_left
- \- *lemma* sub_lt_of_abs_sub_lt_right

Modified src/data/int/basic.lean

Modified src/data/real/basic.lean



## [2020-12-19 17:55:30](https://github.com/leanprover-community/mathlib/commit/63e7fc9)
feat(topology/algebra/ordered): a linear ordered additive group with order topology is a topological group ([#5402](https://github.com/leanprover-community/mathlib/pull/5402))
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* tendsto_abs_at_top_at_top
- \+ *lemma* tendsto_abs_at_bot_at_top

Modified src/topology/algebra/ordered.lean
- \+ *lemma* nhds_eq_infi_abs_sub
- \+/\- *lemma* order_topology_of_nhds_abs
- \+/\- *lemma* linear_ordered_add_comm_group.tendsto_nhds
- \+ *lemma* eventually_abs_sub_lt
- \+/\- *lemma* order_topology_of_nhds_abs
- \- *lemma* tendsto_abs_at_top_at_top
- \+/\- *lemma* linear_ordered_add_comm_group.tendsto_nhds



## [2020-12-19 17:55:28](https://github.com/leanprover-community/mathlib/commit/154a024)
feat(measure_theory/lp_space): add lemmas about the monotonicity of the Lp seminorm ([#5395](https://github.com/leanprover-community/mathlib/pull/5395))
Also add a lemma mem_Lp.const_smul for a normed space.
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *lemma* lintegral_Lp_mul_le_Lq_mul_Lr

Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm_le_snorm_mul_rpow_measure_univ
- \+ *lemma* snorm_le_snorm_of_exponent_le
- \+ *lemma* mem_ℒp.mem_ℒp_of_exponent_le
- \+ *lemma* mem_ℒp.integrable
- \+ *lemma* mem_ℒp.const_smul
- \+ *lemma* snorm_smul_le_mul_snorm



## [2020-12-19 17:55:27](https://github.com/leanprover-community/mathlib/commit/ce385a0)
feat(ring_theory/roots_of_unity): lemmas about minimal polynomial ([#5393](https://github.com/leanprover-community/mathlib/pull/5393))
Three results about the minimal polynomial of `μ` and `μ ^ p`, where `μ` is a primitive root of unity. These are preparatory lemmas to prove that the two minimal polynomials are equal.
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* pow_of_prime
- \+ *lemma* minimal_polynomial_dvd_expand
- \+ *lemma* minimal_polynomial_dvd_pow_mod
- \+ *lemma* minimal_polynomial_dvd_mod_p



## [2020-12-19 16:17:17](https://github.com/leanprover-community/mathlib/commit/c55721d)
chore(analysis/calculus/{fderiv,deriv}): `f x ≠ f a` for `x ≈ a`, `x ≠ a` if `∥z∥ ≤ C * ∥f' z∥` ([#5420](https://github.com/leanprover-community/mathlib/pull/5420))
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *lemma* is_O_with.eq_zero_imp
- \+ *lemma* is_O.eq_zero_imp

Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_at.eventually_ne

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_within_at.eventually_ne
- \+ *lemma* has_fderiv_at.eventually_ne

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* linear_map.bound_of_antilipschitz

Modified src/topology/local_homeomorph.lean
- \+ *lemma* eventually_ne_nhds_within



## [2020-12-19 14:59:26](https://github.com/leanprover-community/mathlib/commit/ff830d7)
feat(ring_theory/witt_vector): redefine subtraction using witt_sub polynomial ([#5405](https://github.com/leanprover-community/mathlib/pull/5405))
#### Estimated changes
Modified src/ring_theory/witt_vector/basic.lean
- \+ *lemma* sub

Modified src/ring_theory/witt_vector/defs.lean
- \+ *lemma* sub_coeff
- \+ *lemma* witt_sub_vars

Modified src/ring_theory/witt_vector/is_poly.lean
- \- *lemma* sub_eq
- \- *lemma* sub_coeff



## [2020-12-19 11:05:52](https://github.com/leanprover-community/mathlib/commit/656b1bb)
feat(category_theory): essential image of a functor ([#5352](https://github.com/leanprover-community/mathlib/pull/5352))
Define essential image of a functor as a predicate and use it to re-express essential surjectivity.
Construct the essential image as a subcategory of the target and use it to factorise an arbitrary functor into a fully faithful functor and an essentially surjective functor.
Also shuffles the import hierarchy a little so that essential image can import full subcategories.
#### Estimated changes
Modified src/algebra/category/Group/Z_Module_equivalence.lean

Modified src/category_theory/Fintype.lean

Modified src/category_theory/concrete_category/basic.lean

Modified src/category_theory/equivalence.lean
- \+/\- *lemma* functor_map_inj_iff
- \+/\- *lemma* inverse_map_inj_iff
- \+/\- *lemma* functor_map_inj_iff
- \+/\- *lemma* inverse_map_inj_iff

Created src/category_theory/essential_image.lean
- \+ *lemma* ess_image.of_iso
- \+ *lemma* ess_image.of_nat_iso
- \+ *lemma* ess_image_eq_of_nat_iso
- \+ *lemma* obj_mem_ess_image
- \+ *def* ess_image
- \+ *def* ess_image.witness
- \+ *def* ess_image.get_iso
- \+ *def* ess_image_inclusion
- \+ *def* to_ess_image
- \+ *def* to_ess_image_comp_essential_image_inclusion
- \+ *def* functor.obj_preimage
- \+ *def* functor.obj_obj_preimage_iso

Modified src/category_theory/full_subcategory.lean

Modified src/category_theory/groupoid.lean

Modified src/category_theory/limits/shapes/normal_mono.lean

Modified src/topology/category/Compactum.lean



## [2020-12-19 08:21:41](https://github.com/leanprover-community/mathlib/commit/0bb665c)
chore(ring_theory/power_series): review, golf ([#5431](https://github.com/leanprover-community/mathlib/pull/5431))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_sigma'
- \+ *lemma* prod_ite_index

Modified src/analysis/analytic/composition.lean

Modified src/data/complex/exponential.lean

Modified src/data/nat/enat.lean
- \+/\- *lemma* coe_lt_top
- \+/\- *lemma* coe_lt_top

Modified src/number_theory/arithmetic_function.lean

Modified src/ring_theory/power_series.lean
- \+ *lemma* coeff_monomial_same
- \+ *lemma* coeff_monomial_ne
- \+ *lemma* eq_of_coeff_monomial_ne_zero
- \+ *lemma* monomial_zero_one
- \+ *lemma* coeff_monomial_mul
- \+ *lemma* coeff_mul_monomial
- \+ *lemma* coeff_add_monomial_mul
- \+ *lemma* coeff_add_mul_monomial
- \+/\- *lemma* monomial_zero_eq_C
- \+ *lemma* map_monomial
- \+ *lemma* map_C
- \+ *lemma* map_X
- \+ *lemma* coeff_monomial_same
- \+/\- *lemma* monomial_zero_eq_C
- \+/\- *lemma* order_zero
- \+/\- *lemma* order_eq_top
- \- *lemma* coeff_monomial'
- \+/\- *lemma* monomial_zero_eq_C
- \- *lemma* coeff_monomial'
- \+/\- *lemma* monomial_zero_eq_C
- \+/\- *lemma* order_eq_top
- \+/\- *lemma* order_zero
- \+/\- *def* monomial
- \+/\- *def* coeff
- \+/\- *def* coeff
- \+/\- *def* monomial
- \+/\- *def* monomial
- \+/\- *def* coeff
- \+/\- *def* coeff
- \+/\- *def* monomial



## [2020-12-19 02:24:58](https://github.com/leanprover-community/mathlib/commit/53354e7)
chore(scripts): update nolints.txt ([#5433](https://github.com/leanprover-community/mathlib/pull/5433))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-19 02:24:56](https://github.com/leanprover-community/mathlib/commit/ec1b70e)
chore(linear_algebra/multilinear): Add map_update_zero ([#5417](https://github.com/leanprover-community/mathlib/pull/5417))
`map_coord_zero` isn't in a form that can be used by simp, so this introduces a form which can.
#### Estimated changes
Modified src/linear_algebra/multilinear.lean
- \+ *lemma* map_update_zero



## [2020-12-19 02:24:54](https://github.com/leanprover-community/mathlib/commit/5e057c9)
feat(data/fin): trans and id lemmas for fin.cast ([#5415](https://github.com/leanprover-community/mathlib/pull/5415))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* cast_trans
- \+ *lemma* cast_refl



## [2020-12-18 23:34:58](https://github.com/leanprover-community/mathlib/commit/0e9a77c)
feat(data/nat/basic): succ_lt_succ_iff ([#5422](https://github.com/leanprover-community/mathlib/pull/5422))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* succ_lt_succ_iff



## [2020-12-18 20:57:15](https://github.com/leanprover-community/mathlib/commit/33483a3)
chore(analysis/special_functions/trigonometric): golf a few more proofs ([#5423](https://github.com/leanprover-community/mathlib/pull/5423))
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* cos_eq_iff_quadratic

Modified src/data/complex/basic.lean
- \+ *lemma* int_cast_abs



## [2020-12-18 17:40:37](https://github.com/leanprover-community/mathlib/commit/0d140b1)
feat(data/set/basic): nonempty instances for subtypes ([#5409](https://github.com/leanprover-community/mathlib/pull/5409))
In [#5408](https://github.com/leanprover-community/mathlib/pull/5408), it is useful to be able to track the nonemptiness of a subset by typeclass inference.  These constructions allow one to do this.
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *lemma* nonempty_of_nonempty_subtype
- \+/\- *lemma* nonempty_of_nonempty_subtype



## [2020-12-18 15:15:14](https://github.com/leanprover-community/mathlib/commit/775edc6)
feat(linear_algebra/tensor_product): Inherit smul through is_scalar_tower ([#5317](https://github.com/leanprover-community/mathlib/pull/5317))
Most notably, this now means that the lemmas about `smul` and `tmul` can be used to prove `∀ z : Z, (z • a) ⊗ₜ[R] b = z • (a ⊗ₜ[R] b)`.
Hopefully these instances aren't dangerous - in particular, there's now a risk of a non-defeq-but-eq diamond for the `ℤ`- and `ℕ`-module structure.
However:
* this diamond already exists in other places anyway
* the diamond if it comes up can be solved with `subsingleton.elim`, since we have a proof that all Z-module and N-module structures must be equivalent.
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean
- \+/\- *lemma* smul_tmul
- \+/\- *lemma* tmul_smul
- \+/\- *lemma* smul_tmul
- \+/\- *lemma* tmul_smul
- \+/\- *theorem* smul.aux_of
- \+/\- *theorem* smul_tmul'
- \+/\- *theorem* smul.aux_of
- \+/\- *theorem* smul_tmul'
- \+/\- *def* smul.aux
- \+/\- *def* smul.aux

Modified src/ring_theory/tensor_product.lean



## [2020-12-18 12:03:56](https://github.com/leanprover-community/mathlib/commit/74b5839)
chore(topology/algebra/ordered): generalize `tendsto_at_top_add_left` etc ([#5398](https://github.com/leanprover-community/mathlib/pull/5398))
* generalize some lemmas from `linear_ordered_ring` to
  `linear_ordered_add_comm_group`;
* rename them to allow dot notation; the new names are
  `filter.tendsto.add_at_*` and `filter.tendsto.at_*_add`, where `*` is
  `top` or `bot`;
* generalize `infi_unit` and `supr_unit` to
  `conditionally_complete_lattice`, add `[unique α]` versions;
* in a `subsingleton`, both `at_top` and `at_bot` are equal to `⊤`;
  these lemmas are useful for the `nontriviality` tactic.
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean

Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* monic.coeff_nat_degree
- \+ *lemma* degree_of_subsingleton
- \+ *lemma* nat_degree_of_subsingleton

Modified src/data/polynomial/monic.lean
- \+/\- *lemma* degree_eq_zero_iff_eq_one
- \+/\- *lemma* nat_degree_mul
- \+/\- *lemma* next_coeff_mul
- \+ *lemma* monic.next_coeff_prod
- \- *lemma* coeff_nat_degree
- \+/\- *lemma* degree_eq_zero_iff_eq_one
- \+/\- *lemma* nat_degree_mul
- \+/\- *lemma* next_coeff_mul
- \- *lemma* next_coeff_prod

Modified src/data/polynomial/reverse.lean
- \+ *lemma* coeff_zero_reverse
- \+ *lemma* coeff_one_reverse

Modified src/order/basic.lean

Modified src/order/complete_lattice.lean
- \- *theorem* infi_unit
- \- *theorem* supr_unit

Modified src/order/conditionally_complete_lattice.lean
- \+ *theorem* infi_unique
- \+ *theorem* supr_unique
- \+ *theorem* infi_unit
- \+ *theorem* supr_unit

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* subsingleton.at_top_eq
- \+ *lemma* subsingleton.at_bot_eq

Modified src/topology/algebra/ordered.lean
- \+ *lemma* filter.tendsto.add_at_top
- \+ *lemma* filter.tendsto.add_at_bot
- \+ *lemma* filter.tendsto.at_top_add
- \+ *lemma* filter.tendsto.at_bot_add
- \+ *lemma* filter.tendsto.mul_at_top
- \- *lemma* tendsto_at_top_add_tendsto_left
- \- *lemma* tendsto_at_bot_add_tendsto_left
- \- *lemma* tendsto_at_top_add_tendsto_right
- \- *lemma* tendsto_at_bot_add_tendsto_right



## [2020-12-18 09:12:03](https://github.com/leanprover-community/mathlib/commit/c4f673c)
chore(analysis/normed_space/basic): `continuous_at.norm` etc ([#5411](https://github.com/leanprover-community/mathlib/pull/5411))
Add variants of the lemma that the norm is continuous.  Also rewrite a few proofs, and rename three lemmas:
* `lim_norm` -> `tendsto_norm_sub_self`
* `lim_norm_zero` -> `tendsto_norm_zero`
* `lim_norm_zero'` -> `tendsto_norm_zero'`
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* tendsto_norm_sub_self
- \+ *lemma* tendsto_norm
- \+ *lemma* tendsto_norm_zero
- \+/\- *lemma* continuous_norm
- \+ *lemma* tendsto_norm_nhds_within_zero
- \+/\- *lemma* filter.tendsto.norm
- \+/\- *lemma* filter.tendsto.nnnorm
- \+/\- *lemma* continuous.norm
- \+ *lemma* continuous.nnnorm
- \+ *lemma* continuous_at.norm
- \+ *lemma* continuous_at.nnnorm
- \+ *lemma* continuous_within_at.norm
- \+ *lemma* continuous_within_at.nnnorm
- \+ *lemma* continuous_on.norm
- \+ *lemma* continuous_on.nnnorm
- \- *lemma* lim_norm
- \- *lemma* lim_norm_zero
- \+/\- *lemma* continuous_norm
- \+/\- *lemma* filter.tendsto.norm
- \+/\- *lemma* continuous.norm
- \+/\- *lemma* filter.tendsto.nnnorm

Modified src/analysis/normed_space/bounded_linear_maps.lean

Modified src/analysis/specific_limits.lean
- \+ *lemma* tendsto_norm_zero'
- \- *lemma* lim_norm_zero'

Modified src/topology/basic.lean
- \+ *lemma* continuous.tendsto'



## [2020-12-18 01:44:51](https://github.com/leanprover-community/mathlib/commit/a4dd9e1)
chore(scripts): update nolints.txt ([#5413](https://github.com/leanprover-community/mathlib/pull/5413))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-18 01:44:49](https://github.com/leanprover-community/mathlib/commit/b1218f8)
chore(analysis/special_functions/trigonometric): review, golf ([#5392](https://github.com/leanprover-community/mathlib/pull/5392))
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* sin_pos_of_mem_Ioo
- \+ *lemma* sin_nonneg_of_mem_Icc
- \+/\- *lemma* sin_nonneg_of_nonneg_of_le_pi
- \+/\- *lemma* cos_pos_of_mem_Ioo
- \+/\- *lemma* cos_nonneg_of_mem_Icc
- \+/\- *lemma* cos_nonpos_of_pi_div_two_le_of_le
- \+/\- *lemma* cos_eq_one_iff_of_lt_of_lt
- \+ *lemma* strict_mono_decr_on_cos
- \+ *lemma* sin_lt_sin_of_lt_of_le_pi_div_two
- \+ *lemma* strict_mono_incr_on_sin
- \+ *lemma* inj_on_sin
- \+ *lemma* inj_on_cos
- \+ *lemma* surj_on_sin
- \+ *lemma* surj_on_cos
- \+ *lemma* sin_mem_Icc
- \+ *lemma* cos_mem_Icc
- \+ *lemma* maps_to_sin
- \+ *lemma* maps_to_cos
- \+ *lemma* bij_on_sin
- \+ *lemma* bij_on_cos
- \+/\- *lemma* range_cos
- \+/\- *lemma* range_sin
- \+/\- *lemma* sin_nonneg_of_nonneg_of_le_pi
- \+/\- *lemma* cos_pos_of_mem_Ioo
- \+/\- *lemma* cos_nonneg_of_mem_Icc
- \+/\- *lemma* cos_nonpos_of_pi_div_two_le_of_le
- \+/\- *lemma* cos_eq_one_iff_of_lt_of_lt
- \- *lemma* sin_lt_sin_of_le_of_le_pi_div_two
- \- *lemma* sin_inj_of_le_of_le_pi_div_two
- \- *lemma* cos_inj_of_nonneg_of_le_pi
- \- *lemma* exists_sin_eq
- \- *lemma* exists_cos_eq
- \+/\- *lemma* range_cos
- \+/\- *lemma* range_sin

Modified src/geometry/euclidean/triangle.lean



## [2020-12-17 16:32:00](https://github.com/leanprover-community/mathlib/commit/35f2789)
chore(algebra/module/basic): add `subsingleton (semimodule ℕ M)` ([#5396](https://github.com/leanprover-community/mathlib/pull/5396))
This can be used to resolve diamonds between different `semimodule ℕ` instances.
The implementation is copied from the `subsingleton (module ℤ M)` instance.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *lemma* semimodule_ext
- \- *lemma* module_ext



## [2020-12-17 13:27:40](https://github.com/leanprover-community/mathlib/commit/6f1351f)
chore(algebra/{group,ring}): more on pushing/pulling groups/rings along morphisms ([#5406](https://github.com/leanprover-community/mathlib/pull/5406))
#### Estimated changes
Modified src/algebra/group/inj_surj.lean

Modified src/algebra/ring/basic.lean



## [2020-12-17 13:27:39](https://github.com/leanprover-community/mathlib/commit/ff716d2)
chore(order/bounds): golf ([#5401](https://github.com/leanprover-community/mathlib/pull/5401))
#### Estimated changes
Modified src/order/bounds.lean
- \+ *lemma* is_lub.exists_between
- \+ *lemma* is_lub.exists_between'
- \+ *lemma* is_glb.exists_between
- \+ *lemma* is_glb.exists_between'
- \+/\- *lemma* is_glb.exists_between_self_add
- \+/\- *lemma* is_glb.exists_between_self_add'
- \+/\- *lemma* is_lub.exists_between_sub_self
- \+/\- *lemma* is_lub.exists_between_sub_self'
- \+/\- *lemma* is_glb.exists_between_self_add
- \+/\- *lemma* is_glb.exists_between_self_add'
- \+/\- *lemma* is_lub.exists_between_sub_self
- \+/\- *lemma* is_lub.exists_between_sub_self'

Modified src/topology/instances/real.lean



## [2020-12-17 13:27:36](https://github.com/leanprover-community/mathlib/commit/3685146)
chore(topology/algebra/ordered): deduplicate ([#5399](https://github.com/leanprover-community/mathlib/pull/5399))
* Drop `mem_nhds_unbounded` in favor of
  `mem_nhds_iff_exists_Ioo_subset'`.
* Use `(h : ∃ l, l < a)` instead of `{l} (hl : l < a)` in
  `mem_nhds_iff_exists_Ioo_subset'`. This way we can `apply` the
  theorem without generating non-`Prop` goals and we can get the
  arguments directly from `no_bot` / `no_top`.
* add `nhds_basis_Ioo'` and `nhds_basis_Ioo`.
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+ *lemma* inf_binfi

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* mem_nhds_iff_exists_Ioo_subset'
- \+ *lemma* nhds_basis_Ioo'
- \+ *lemma* nhds_basis_Ioo
- \- *lemma* mem_nhds_unbounded
- \+/\- *lemma* mem_nhds_iff_exists_Ioo_subset'

Modified src/topology/instances/real.lean



## [2020-12-17 13:27:34](https://github.com/leanprover-community/mathlib/commit/35a16a9)
feat(algebra/module/basic): Add symmetric smul_comm_class instances for int and nat ([#5369](https://github.com/leanprover-community/mathlib/pull/5369))
These can't be added globally for all types as they cause instance resolution loops, but are safe here as these definitions do not depend on an existing `smul_comm_class`.
Note that these instances already exist via `is_scalar_tower.to_smul_comm_class'` for algebras - this just makes sure the instances are still available in the presence of weaker typeclasses. There's no diamond concern here, as `smul_comm_class` is in `Prop`.
#### Estimated changes
Modified src/algebra/module/basic.lean

Modified src/linear_algebra/alternating.lean



## [2020-12-17 10:49:30](https://github.com/leanprover-community/mathlib/commit/ee6969c)
chore(linear_algebra/{alternating,multilinear}): Add a handful of trivial lemmas ([#5380](https://github.com/leanprover-community/mathlib/pull/5380))
Some of these are needed for a WIP PR, and some seem like generally nice things to have.
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *lemma* coe_add
- \+ *lemma* coe_zero
- \+ *lemma* coe_neg
- \+ *lemma* sub_apply
- \+ *lemma* coe_sub
- \+/\- *lemma* smul_apply
- \+ *lemma* coe_smul
- \+ *lemma* coe_alternatization
- \+/\- *lemma* smul_apply
- \- *lemma* to_multilinear_map_alternization

Modified src/linear_algebra/multilinear.lean
- \+ *lemma* dom_dom_congr_trans
- \+ *lemma* dom_dom_congr_mul
- \+ *lemma* dom_coprod'_apply
- \+ *lemma* dom_coprod_dom_dom_congr_sum_congr
- \+/\- *lemma* sub_apply
- \+/\- *lemma* sub_apply



## [2020-12-17 08:03:51](https://github.com/leanprover-community/mathlib/commit/6a99e9e)
chore(analysis/calculus/deriv): add `iff` versions of `differentiable_const_add` etc ([#5390](https://github.com/leanprover-community/mathlib/pull/5390))
Also drop some unneeded `differentiable` assumptions in lemmas like `deriv_const_add`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* deriv_within_add_const
- \+/\- *lemma* deriv_add_const
- \+/\- *lemma* deriv_within_const_add
- \+/\- *lemma* deriv_const_add
- \+/\- *lemma* deriv_within.neg
- \+/\- *lemma* deriv_within_sub_const
- \+/\- *lemma* deriv_sub_const
- \+/\- *lemma* deriv_within_const_sub
- \+/\- *lemma* deriv_const_sub
- \+/\- *lemma* deriv_within_add_const
- \+/\- *lemma* deriv_add_const
- \+/\- *lemma* deriv_within_const_add
- \+/\- *lemma* deriv_const_add
- \+/\- *lemma* deriv_within.neg
- \+/\- *lemma* deriv_within_sub_const
- \+/\- *lemma* deriv_sub_const
- \+/\- *lemma* deriv_within_const_sub
- \+/\- *lemma* deriv_const_sub

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable_within_at_add_const_iff
- \+ *lemma* differentiable_at_add_const_iff
- \+ *lemma* differentiable_on_add_const_iff
- \+ *lemma* differentiable_add_const_iff
- \+/\- *lemma* fderiv_within_add_const
- \+/\- *lemma* fderiv_add_const
- \+ *lemma* differentiable_within_at_const_add_iff
- \+ *lemma* differentiable_at_const_add_iff
- \+/\- *lemma* differentiable_on.const_add
- \+ *lemma* differentiable_on_const_add_iff
- \+/\- *lemma* differentiable.const_add
- \+ *lemma* differentiable_const_add_iff
- \+/\- *lemma* fderiv_within_const_add
- \+/\- *lemma* fderiv_const_add
- \+ *lemma* differentiable_within_at_neg_iff
- \+/\- *lemma* differentiable_at.neg
- \+ *lemma* differentiable_at_neg_iff
- \+ *lemma* differentiable_on_neg_iff
- \+/\- *lemma* differentiable.neg
- \+ *lemma* differentiable_neg_iff
- \+/\- *lemma* fderiv_within_neg
- \+/\- *lemma* fderiv_neg
- \+ *lemma* differentiable_within_at_sub_const_iff
- \+/\- *lemma* differentiable_at.sub_const
- \+ *lemma* differentiable_at_sub_const_iff
- \+/\- *lemma* differentiable_on.sub_const
- \+ *lemma* differentiable_on_sub_const_iff
- \+/\- *lemma* differentiable.sub_const
- \+ *lemma* differentiable_sub_const_iff
- \+/\- *lemma* fderiv_within_sub_const
- \+/\- *lemma* fderiv_sub_const
- \+ *lemma* differentiable_within_at_const_sub_iff
- \+ *lemma* differentiable_at_const_sub_iff
- \+/\- *lemma* differentiable_on.const_sub
- \+ *lemma* differentiable_on_const_sub_iff
- \+/\- *lemma* differentiable.const_sub
- \+ *lemma* differentiable_const_sub_iff
- \+/\- *lemma* fderiv_within_const_sub
- \+/\- *lemma* fderiv_const_sub
- \+/\- *lemma* fderiv_within_add_const
- \+/\- *lemma* fderiv_add_const
- \+/\- *lemma* differentiable_on.const_add
- \+/\- *lemma* differentiable.const_add
- \+/\- *lemma* fderiv_within_const_add
- \+/\- *lemma* fderiv_const_add
- \+/\- *lemma* differentiable_at.neg
- \+/\- *lemma* differentiable.neg
- \+/\- *lemma* fderiv_within_neg
- \+/\- *lemma* fderiv_neg
- \+/\- *lemma* differentiable_at.sub_const
- \+/\- *lemma* differentiable_on.sub_const
- \+/\- *lemma* differentiable.sub_const
- \+/\- *lemma* fderiv_within_sub_const
- \+/\- *lemma* fderiv_sub_const
- \+/\- *lemma* differentiable_on.const_sub
- \+/\- *lemma* differentiable.const_sub
- \+/\- *lemma* fderiv_within_const_sub
- \+/\- *lemma* fderiv_const_sub
- \+/\- *theorem* has_fderiv_at.add_const
- \+/\- *theorem* has_fderiv_at.add_const



## [2020-12-17 01:31:27](https://github.com/leanprover-community/mathlib/commit/e8fc373)
chore(scripts): update nolints.txt ([#5400](https://github.com/leanprover-community/mathlib/pull/5400))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt

Modified scripts/nolints.txt



## [2020-12-16 21:52:40](https://github.com/leanprover-community/mathlib/commit/01a77ad)
chore(analysis/analytic/basic.lean): fix latex in doc ([#5397](https://github.com/leanprover-community/mathlib/pull/5397))
Doc in the file `analytic/basic.lean` is broken, since I used a latex command `\choose` which doesn't exist. Replace it with `\binom`.
#### Estimated changes
Modified src/analysis/analytic/basic.lean



## [2020-12-16 21:52:38](https://github.com/leanprover-community/mathlib/commit/8fa10af)
feat(ring_theory/algebra_tower): alg_hom_equiv_sigma ([#5345](https://github.com/leanprover-community/mathlib/pull/5345))
Proves that algebra homomorphisms from the top of an is_scalar_tower are the same as a pair of algebra homomorphisms.
This is useful for counting algebra homomorphisms.
#### Estimated changes
Modified src/ring_theory/algebra_tower.lean
- \+ *def* alg_hom.restrict_domain
- \+ *def* alg_hom.extend_scalars
- \+ *def* alg_hom_equiv_sigma



## [2020-12-16 18:35:22](https://github.com/leanprover-community/mathlib/commit/c5a2ff4)
chore(script/copy-mod-doc) Specify an encoding for files when opening ([#5394](https://github.com/leanprover-community/mathlib/pull/5394))
This was necessary for the script to run locally on windows.
#### Estimated changes
Modified scripts/lint-copy-mod-doc.py



## [2020-12-16 18:35:20](https://github.com/leanprover-community/mathlib/commit/9282f6c)
feat(finset): two simple lemmas ([#5387](https://github.com/leanprover-community/mathlib/pull/5387))
also open function namespace
#### Estimated changes
Modified src/data/finset/basic.lean
- \+/\- *lemma* coe_injective
- \+ *lemma* mem_insert_coe
- \+ *lemma* to_finset_surj_on
- \+/\- *lemma* coe_injective
- \+/\- *theorem* to_finset_surjective
- \+/\- *theorem* to_finset_surjective



## [2020-12-16 15:31:36](https://github.com/leanprover-community/mathlib/commit/39ecd1a)
chore(group_theory/group_action/basic): Add a simp lemma about smul on quotient groups ([#5374](https://github.com/leanprover-community/mathlib/pull/5374))
By pushing `mk` to the outside, this increases the chance they can cancel with an outer `lift`
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \+ *lemma* quotient.smul_mk
- \+ *lemma* quotient.smul_coe



## [2020-12-16 15:31:34](https://github.com/leanprover-community/mathlib/commit/1221ab6)
chore(*): add a `div`/`sub` field to (`add_`)`group`(`_with_zero`) ([#5303](https://github.com/leanprover-community/mathlib/pull/5303))
This PR is intended to fix the following kind of diamonds:
Let `foo X` be a type with a `∀ X, has_div (foo X)` instance but no `∀ X, has_inv (foo X)`, e.g. when `foo X` is a `euclidean_domain`. Suppose we also have an instance `∀ X [cromulent X], group_with_zero (foo X)`. Then the `(/)` coming from `group_with_zero_has_div` cannot be defeq to the `(/)` coming from `foo.has_div`.
As a consequence of making the `has_div` instances defeq, we can no longer assume that `(div_eq_mul_inv a b : a / b = a * b⁻¹) = rfl` for all groups. The previous preparation PR [#5302](https://github.com/leanprover-community/mathlib/pull/5302) should have changed all places in mathlib that assumed defeqness, to rewrite explicitly instead.
#### Estimated changes
Modified src/algebra/field.lean
- \- *lemma* inv_eq_one_div
- \- *lemma* mul_one_div

Modified src/algebra/group/basic.lean
- \+ *lemma* inv_eq_one_div
- \+ *lemma* mul_one_div
- \- *lemma* group.inv_eq_one_div
- \- *lemma* group.mul_one_div

Modified src/algebra/group/defs.lean
- \+ *lemma* div_eq_mul_inv
- \- *lemma* group.div_eq_mul_inv
- \- *lemma* sub_eq_add_neg
- \+ *def* group.to_monoid

Modified src/algebra/group/hom.lean
- \+ *lemma* div_apply
- \- *lemma* sub_apply

Modified src/algebra/group/inj_surj.lean

Modified src/algebra/group/pi.lean
- \- *lemma* sub_apply

Modified src/algebra/group/prod.lean
- \+/\- *lemma* fst_sub
- \+/\- *lemma* snd_sub
- \+/\- *lemma* mk_sub_mk
- \+/\- *lemma* fst_sub
- \+/\- *lemma* snd_sub
- \+/\- *lemma* mk_sub_mk

Modified src/algebra/group/type_tags.lean
- \+ *lemma* of_add_sub
- \+ *lemma* to_add_div
- \+ *lemma* of_mul_div
- \+ *lemma* to_mul_sub

Modified src/algebra/group/ulift.lean
- \+ *lemma* div_down
- \- *lemma* sub_down

Modified src/algebra/group_with_zero/basic.lean

Modified src/algebra/group_with_zero/defs.lean
- \- *lemma* div_eq_mul_inv

Modified src/algebra/monoid_algebra.lean

Modified src/algebra/opposites.lean

Modified src/algebra/ordered_group.lean

Modified src/algebra/punit_instances.lean
- \+ *lemma* div_eq

Modified src/algebra/quandle.lean

Modified src/algebra/ring/ulift.lean

Modified src/analysis/asymptotic_equivalent.lean

Modified src/analysis/hofer.lean

Modified src/analysis/special_functions/trigonometric.lean

Modified src/category_theory/endomorphism.lean

Modified src/data/complex/basic.lean

Modified src/data/equiv/mul_add_aut.lean

Modified src/data/equiv/ring_aut.lean

Modified src/data/equiv/transfer_instance.lean
- \+ *lemma* div_def

Modified src/data/finsupp/basic.lean

Modified src/data/int/basic.lean

Modified src/data/matrix/basic.lean
- \+/\- *theorem* zero_apply
- \+/\- *theorem* neg_apply
- \+/\- *theorem* sub_apply
- \+/\- *theorem* zero_apply
- \+/\- *theorem* neg_apply
- \+/\- *theorem* sub_apply

Modified src/data/padics/padic_integers.lean
- \+/\- *lemma* coe_sub
- \+ *lemma* coe_pow
- \+/\- *lemma* coe_sub
- \- *lemma* coet_pow

Modified src/data/pi.lean
- \+/\- *lemma* div_apply
- \+/\- *lemma* div_apply

Modified src/data/quaternion.lean
- \+/\- *lemma* mk_sub_mk
- \+/\- *lemma* mk_sub_mk

Modified src/data/real/cau_seq.lean
- \+/\- *theorem* sub_apply
- \+/\- *theorem* const_sub
- \+/\- *theorem* const_sub
- \+/\- *theorem* sub_apply

Modified src/data/real/cau_seq_completion.lean
- \+ *theorem* mk_sub

Modified src/data/real/hyperreal.lean

Modified src/data/zsqrtd/basic.lean

Modified src/deprecated/subgroup.lean
- \+ *lemma* is_subgroup.div_mem
- \- *theorem* is_add_subgroup.sub_mem

Modified src/dynamics/circle/rotation_number/translation_number.lean

Modified src/field_theory/perfect_closure.lean

Modified src/group_theory/congruence.lean

Modified src/group_theory/perm/basic.lean

Modified src/group_theory/quotient_group.lean

Modified src/group_theory/subgroup.lean
- \- *lemma* sub_mem
- \+ *theorem* div_mem

Modified src/group_theory/sylow.lean

Modified src/linear_algebra/basic.lean
- \+ *theorem* mk_sub

Modified src/linear_algebra/char_poly/basic.lean

Modified src/linear_algebra/multilinear.lean
- \+ *lemma* sub_apply

Modified src/linear_algebra/tensor_product.lean

Modified src/measure_theory/integration.lean
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_sub

Modified src/number_theory/dioph.lean

Modified src/order/filter/filter_product.lean

Modified src/order/filter/germ.lean
- \+ *lemma* coe_div
- \- *lemma* coe_sub

Modified src/ring_theory/derivation.lean

Modified src/ring_theory/localization.lean

Modified src/tactic/norm_num.lean
- \- *theorem* int_sub_hack

Modified src/tactic/ring.lean

Modified src/topology/algebra/group_completion.lean
- \+ *lemma* coe_sub

Modified src/topology/algebra/module.lean

Modified src/topology/algebra/multilinear.lean

Modified src/topology/bounded_continuous_function.lean

Modified test/refine_struct.lean



## [2020-12-16 13:55:21](https://github.com/leanprover-community/mathlib/commit/461865b)
refactor(data/real): move `real.sqrt` to `data.real.sqrt`, more dependencies ([#5359](https://github.com/leanprover-community/mathlib/pull/5359))
* define `nnreal.sqrt`;
* use general theory to prove that the inverse exists, and is an `order_iso`;
* deduce continuity of `sqrt` from continuity of `order_iso`.
#### Estimated changes
Modified archive/sensitivity.lean

Modified src/analysis/special_functions/arsinh.lean

Modified src/analysis/special_functions/pow.lean
- \- *lemma* continuous_sqrt

Modified src/analysis/special_functions/trigonometric.lean

Modified src/data/complex/basic.lean

Modified src/data/real/basic.lean
- \- *lemma* sqrt_le_sqrt
- \- *lemma* sqrt_le_left
- \- *lemma* le_sqrt
- \- *lemma* le_sqrt'
- \- *lemma* le_sqrt_of_sqr_le
- \- *theorem* sqrt_exists
- \- *theorem* sqrt_aux_nonneg
- \- *theorem* sqrt_aux_converges
- \- *theorem* sqrt_prop
- \- *theorem* sqrt_eq_zero_of_nonpos
- \- *theorem* sqrt_nonneg
- \- *theorem* mul_self_sqrt
- \- *theorem* sqrt_mul_self
- \- *theorem* sqrt_eq_iff_mul_self_eq
- \- *theorem* sqr_sqrt
- \- *theorem* sqrt_sqr
- \- *theorem* sqrt_eq_iff_sqr_eq
- \- *theorem* sqrt_mul_self_eq_abs
- \- *theorem* sqrt_sqr_eq_abs
- \- *theorem* sqrt_zero
- \- *theorem* sqrt_one
- \- *theorem* sqrt_le
- \- *theorem* sqrt_lt
- \- *theorem* sqrt_inj
- \- *theorem* sqrt_eq_zero
- \- *theorem* sqrt_eq_zero'
- \- *theorem* sqrt_pos
- \- *theorem* sqrt_mul'
- \- *theorem* sqrt_mul
- \- *theorem* sqrt_inv
- \- *theorem* sqrt_div
- \- *def* sqrt_aux

Modified src/data/real/irrational.lean

Modified src/data/real/nnreal.lean
- \+ *lemma* le_of_real_iff_coe_le'

Created src/data/real/sqrt.lean
- \+ *lemma* sqrt_eq_iff_sqr_eq
- \+ *lemma* sqrt_le_iff
- \+ *lemma* le_sqrt_iff
- \+ *lemma* sqrt_eq_zero
- \+ *lemma* sqrt_zero
- \+ *lemma* sqrt_one
- \+ *lemma* mul_sqrt_self
- \+ *lemma* sqrt_mul_self
- \+ *lemma* sqrt_mul
- \+ *lemma* sqrt_inv
- \+ *lemma* sqrt_div
- \+ *lemma* continuous_sqrt
- \+ *lemma* continuous_sqrt
- \+ *lemma* sqrt_le_sqrt
- \+ *lemma* sqrt_le_left
- \+ *lemma* sqrt_le_iff
- \+ *lemma* le_sqrt
- \+ *lemma* le_sqrt'
- \+ *lemma* le_sqrt_of_sqr_le
- \+ *lemma* filter.tendsto.sqrt
- \+ *lemma* continuous_within_at.sqrt
- \+ *lemma* continuous_at.sqrt
- \+ *lemma* continuous_on.sqrt
- \+ *lemma* continuous.sqrt
- \+ *theorem* sqrt_aux_nonneg
- \+ *theorem* sqrt_aux_converges
- \+ *theorem* sqrt_eq_zero_of_nonpos
- \+ *theorem* sqrt_nonneg
- \+ *theorem* mul_self_sqrt
- \+ *theorem* sqrt_mul_self
- \+ *theorem* sqrt_eq_iff_mul_self_eq
- \+ *theorem* sqr_sqrt
- \+ *theorem* sqrt_sqr
- \+ *theorem* sqrt_eq_iff_sqr_eq
- \+ *theorem* sqrt_mul_self_eq_abs
- \+ *theorem* sqrt_sqr_eq_abs
- \+ *theorem* sqrt_zero
- \+ *theorem* sqrt_one
- \+ *theorem* sqrt_le
- \+ *theorem* sqrt_lt
- \+ *theorem* sqrt_inj
- \+ *theorem* sqrt_eq_zero
- \+ *theorem* sqrt_eq_zero'
- \+ *theorem* sqrt_pos
- \+ *theorem* sqrt_mul
- \+ *theorem* sqrt_mul'
- \+ *theorem* sqrt_inv
- \+ *theorem* sqrt_div
- \+ *def* sqrt_aux



## [2020-12-16 13:55:19](https://github.com/leanprover-community/mathlib/commit/1b01068)
feat(ring_theory/witt_vector): Witt vectors are proj. limit of truncated Witt vectors ([#5163](https://github.com/leanprover-community/mathlib/pull/5163))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/ring_theory/witt_vector/truncated.lean
- \+ *lemma* truncate_surjective
- \+ *lemma* coeff_truncate
- \+ *lemma* mem_ker_truncate
- \+ *lemma* truncate_mk
- \+ *lemma* truncate_comp_witt_vector_truncate
- \+ *lemma* truncate_witt_vector_truncate
- \+ *lemma* truncate_truncate
- \+ *lemma* truncate_comp
- \+ *lemma* truncate_surjective
- \+ *lemma* coeff_truncate
- \+ *lemma* card
- \+ *lemma* infi_ker_truncate
- \+ *lemma* truncate_lift_fun
- \+ *lemma* truncate_lift
- \+ *lemma* truncate_comp_lift
- \+ *lemma* lift_unique
- \+ *lemma* hom_ext
- \+ *def* truncate
- \+ *def* truncate
- \+ *def* lift_fun
- \+ *def* lift
- \+ *def* lift_equiv



## [2020-12-16 10:00:13](https://github.com/leanprover-community/mathlib/commit/6548be4)
chore(data/quot): Add missing simp lemmas ([#5372](https://github.com/leanprover-community/mathlib/pull/5372))
These are called `lift_on'_beta` for consistency with `lift_on_beta`; even though we also have `map_mk'` etc in the same file.
#### Estimated changes
Modified src/data/quot.lean



## [2020-12-16 07:31:15](https://github.com/leanprover-community/mathlib/commit/78940f4)
chore(*): use notation `ℝ≥0`  ([#5391](https://github.com/leanprover-community/mathlib/pull/5391))
#### Estimated changes
Modified src/analysis/ODE/gronwall.lean

Modified src/analysis/analytic/basic.lean
- \+/\- *lemma* le_radius_of_bound
- \+/\- *lemma* bound_of_lt_radius
- \+/\- *lemma* geometric_bound_of_lt_radius
- \+/\- *lemma* has_fpower_series_on_ball.uniform_geometric_approx
- \+/\- *lemma* has_fpower_series_on_ball.tendsto_uniformly_on
- \+/\- *lemma* has_fpower_series_on_ball.tendsto_uniformly_on'
- \+/\- *lemma* le_radius_of_bound
- \+/\- *lemma* bound_of_lt_radius
- \+/\- *lemma* geometric_bound_of_lt_radius
- \+/\- *lemma* has_fpower_series_on_ball.uniform_geometric_approx
- \+/\- *lemma* has_fpower_series_on_ball.tendsto_uniformly_on
- \+/\- *lemma* has_fpower_series_on_ball.tendsto_uniformly_on'

Modified src/analysis/analytic/composition.lean

Modified src/analysis/mean_inequalities.lean

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* lipschitz_with.neg
- \+/\- *lemma* lipschitz_with.add
- \+/\- *lemma* lipschitz_with.sub
- \+/\- *lemma* antilipschitz_with.add_lipschitz_with
- \+/\- *lemma* continuous_nnnorm
- \+/\- *lemma* summable_of_nnnorm_bounded
- \+/\- *lemma* lipschitz_with.neg
- \+/\- *lemma* lipschitz_with.add
- \+/\- *lemma* lipschitz_with.sub
- \+/\- *lemma* antilipschitz_with.add_lipschitz_with
- \+/\- *lemma* continuous_nnnorm
- \+/\- *lemma* summable_of_nnnorm_bounded

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *theorem* linear_map.antilipschitz_of_bound
- \+/\- *theorem* op_norm_le_of_lipschitz
- \+/\- *theorem* uniform_embedding_of_bound
- \+/\- *theorem* linear_map.antilipschitz_of_bound
- \+/\- *theorem* op_norm_le_of_lipschitz
- \+/\- *theorem* uniform_embedding_of_bound

Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* nnreal.measurable_rpow
- \+/\- *lemma* measurable.nnreal_rpow
- \+/\- *lemma* nnreal.measurable_rpow_const
- \+/\- *lemma* measurable.nnreal_rpow_const
- \+/\- *lemma* nnreal.measurable_rpow
- \+/\- *lemma* measurable.nnreal_rpow
- \+/\- *lemma* nnreal.measurable_rpow_const
- \+/\- *lemma* measurable.nnreal_rpow_const

Modified src/analysis/specific_limits.lean
- \+/\- *lemma* nnreal.tendsto_inverse_at_top_nhds_0_nat
- \+/\- *lemma* nnreal.tendsto_const_div_at_top_nhds_0_nat
- \+/\- *lemma* nnreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \+/\- *lemma* nnreal.has_sum_geometric
- \+/\- *lemma* nnreal.summable_geometric
- \+/\- *lemma* tsum_geometric_nnreal
- \+/\- *lemma* nnreal.tendsto_inverse_at_top_nhds_0_nat
- \+/\- *lemma* nnreal.tendsto_const_div_at_top_nhds_0_nat
- \+/\- *lemma* nnreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \+/\- *lemma* nnreal.has_sum_geometric
- \+/\- *lemma* nnreal.summable_geometric
- \+/\- *lemma* tsum_geometric_nnreal
- \+/\- *theorem* exists_pos_sum_of_encodable
- \+/\- *theorem* exists_pos_sum_of_encodable

Modified src/data/real/ennreal.lean

Modified src/data/real/nnreal.lean
- \+/\- *lemma* val_eq_coe
- \+/\- *lemma* coe_nonneg
- \+/\- *lemma* bdd_above_coe
- \+/\- *lemma* bdd_below_coe
- \+/\- *lemma* coe_Sup
- \+/\- *lemma* coe_Inf
- \+/\- *lemma* le_of_forall_epsilon_le
- \+/\- *lemma* lt_iff_exists_rat_btwn
- \+/\- *lemma* bot_eq_zero
- \+/\- *lemma* coe_max
- \+/\- *lemma* coe_min
- \+/\- *lemma* zero_le_coe
- \+/\- *lemma* of_real_le_iff_le_coe
- \+/\- *lemma* le_of_real_iff_coe_le
- \+/\- *lemma* of_real_lt_iff_lt_coe
- \+/\- *lemma* lt_of_real_iff_coe_lt
- \+/\- *lemma* mul_eq_mul_left
- \+/\- *lemma* sub_le_iff_le_add
- \+/\- *lemma* add_sub_cancel
- \+/\- *lemma* add_sub_cancel'
- \+/\- *lemma* sub_add_cancel_of_le
- \+/\- *lemma* lt_sub_iff_add_lt
- \+/\- *lemma* sub_lt_iff_lt_add
- \+/\- *lemma* sub_eq_iff_eq_add
- \+/\- *lemma* div_def
- \+/\- *lemma* inv_zero
- \+/\- *lemma* inv_eq_zero
- \+/\- *lemma* inv_pos
- \+/\- *lemma* val_eq_coe
- \+/\- *lemma* coe_nonneg
- \+/\- *lemma* bdd_above_coe
- \+/\- *lemma* bdd_below_coe
- \+/\- *lemma* coe_Sup
- \+/\- *lemma* coe_Inf
- \+/\- *lemma* le_of_forall_epsilon_le
- \+/\- *lemma* lt_iff_exists_rat_btwn
- \+/\- *lemma* bot_eq_zero
- \+/\- *lemma* coe_max
- \+/\- *lemma* coe_min
- \+/\- *lemma* zero_le_coe
- \+/\- *lemma* of_real_le_iff_le_coe
- \+/\- *lemma* le_of_real_iff_coe_le
- \+/\- *lemma* of_real_lt_iff_lt_coe
- \+/\- *lemma* lt_of_real_iff_coe_lt
- \+/\- *lemma* mul_eq_mul_left
- \+/\- *lemma* sub_le_iff_le_add
- \+/\- *lemma* add_sub_cancel
- \+/\- *lemma* add_sub_cancel'
- \+/\- *lemma* sub_add_cancel_of_le
- \+/\- *lemma* lt_sub_iff_add_lt
- \+/\- *lemma* sub_lt_iff_lt_add
- \+/\- *lemma* sub_eq_iff_eq_add
- \+/\- *lemma* div_def
- \+/\- *lemma* inv_zero
- \+/\- *lemma* inv_eq_zero
- \+/\- *lemma* inv_pos
- \+/\- *theorem* mul_ne_zero'
- \+/\- *theorem* mul_ne_zero'

Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* lintegral_coe_eq_integral
- \+/\- *lemma* lintegral_coe_eq_integral

Modified src/measure_theory/content.lean
- \+/\- *lemma* of_content_exists_compact
- \+/\- *lemma* of_content_exists_open
- \+/\- *lemma* of_content_exists_compact
- \+/\- *lemma* of_content_exists_open

Modified src/measure_theory/decomposition.lean

Modified src/measure_theory/integration.lean
- \+/\- *lemma* lintegral_mono_nnreal
- \+/\- *lemma* lintegral_mono_nnreal
- \+/\- *theorem* map_coe_ennreal_restrict
- \+/\- *theorem* map_coe_nnreal_restrict
- \+/\- *theorem* map_coe_ennreal_restrict
- \+/\- *theorem* map_coe_nnreal_restrict

Modified src/measure_theory/outer_measure.lean

Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* cauchy_seq_of_edist_le_of_summable
- \+/\- *lemma* cauchy_seq_of_edist_le_of_summable

Modified src/topology/bounded_continuous_function.lean
- \+/\- *lemma* lipschitz_comp
- \+/\- *lemma* uniform_continuous_comp
- \+/\- *lemma* continuous_comp
- \+/\- *lemma* lipschitz_comp
- \+/\- *lemma* uniform_continuous_comp
- \+/\- *lemma* continuous_comp
- \+/\- *def* comp
- \+/\- *def* comp

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* embedding_coe
- \+/\- *lemma* coe_range_mem_nhds
- \+/\- *lemma* tendsto_coe
- \+/\- *lemma* continuous_coe
- \+/\- *lemma* continuous_coe_iff
- \+/\- *lemma* nhds_coe
- \+/\- *lemma* nhds_coe_coe
- \+/\- *lemma* embedding_coe
- \+/\- *lemma* coe_range_mem_nhds
- \+/\- *lemma* tendsto_coe
- \+/\- *lemma* continuous_coe
- \+/\- *lemma* continuous_coe_iff
- \+/\- *lemma* nhds_coe
- \+/\- *lemma* nhds_coe_coe
- \+/\- *def* ne_top_homeomorph_nnreal
- \+/\- *def* lt_top_homeomorph_nnreal
- \+/\- *def* ne_top_homeomorph_nnreal
- \+/\- *def* lt_top_homeomorph_nnreal

Modified src/topology/metric_space/antilipschitz.lean

Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* edist_lt_coe
- \+/\- *lemma* edist_le_coe
- \+/\- *lemma* dist_lt_coe
- \+/\- *lemma* dist_le_coe
- \+/\- *lemma* metric.emetric_ball_nnreal
- \+/\- *lemma* metric.emetric_closed_ball_nnreal
- \+/\- *lemma* nnreal.dist_eq
- \+/\- *lemma* nnreal.nndist_eq
- \+/\- *lemma* edist_lt_coe
- \+/\- *lemma* edist_le_coe
- \+/\- *lemma* dist_lt_coe
- \+/\- *lemma* dist_le_coe
- \+/\- *lemma* metric.emetric_ball_nnreal
- \+/\- *lemma* metric.emetric_closed_ball_nnreal
- \+/\- *lemma* nnreal.dist_eq
- \+/\- *lemma* nnreal.nndist_eq
- \+/\- *def* nndist
- \+/\- *def* nndist

Modified src/topology/metric_space/emetric_space.lean

Modified src/topology/metric_space/gromov_hausdorff_realized.lean

Modified src/topology/metric_space/hausdorff_distance.lean

Modified src/topology/metric_space/lipschitz.lean

Modified src/topology/metric_space/pi_Lp.lean



## [2020-12-16 07:31:13](https://github.com/leanprover-community/mathlib/commit/47b3c4b)
feat(algebra/lie/basic): nilpotent and solvable Lie algebras ([#5382](https://github.com/leanprover-community/mathlib/pull/5382))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* trivial_lie_zero
- \+ *lemma* trivial_lie_oper_zero
- \+/\- *lemma* trivial_iff_derived_eq_bot
- \+ *lemma* derived_series_le_lower_central_series
- \+/\- *lemma* trivial_iff_derived_eq_bot
- \+ *def* derived_series
- \+ *def* lower_central_series
- \- *def* derived_lie_submodule



## [2020-12-16 04:20:19](https://github.com/leanprover-community/mathlib/commit/79e9aee)
feat(equiv/basic): add true_arrow_equiv ([#5388](https://github.com/leanprover-community/mathlib/pull/5388))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* true_arrow_equiv



## [2020-12-16 01:15:14](https://github.com/leanprover-community/mathlib/commit/26f8b28)
chore(scripts): update nolints.txt ([#5384](https://github.com/leanprover-community/mathlib/pull/5384))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-16 01:15:12](https://github.com/leanprover-community/mathlib/commit/e264e5f)
feat(tactic/ext): `ext?` displays applied lemmas ([#5375](https://github.com/leanprover-community/mathlib/pull/5375))
refactor using `state_t` instead of state passing style
#### Estimated changes
Modified src/control/monad/basic.lean

Modified src/tactic/congr.lean

Modified src/tactic/ext.lean

Modified test/ext.lean



## [2020-12-15 22:23:52](https://github.com/leanprover-community/mathlib/commit/2ee0f1e)
feat(category_theory/isomorphism): is_iso versions ([#5355](https://github.com/leanprover-community/mathlib/pull/5355))
add `is_iso` versions of some existing `iso` lemmas
#### Estimated changes
Modified src/category_theory/isomorphism.lean
- \+ *lemma* hom_comp_eq_id
- \+ *lemma* comp_hom_eq_id



## [2020-12-15 22:23:50](https://github.com/leanprover-community/mathlib/commit/dbb6b04)
feat(topology/separation): add lemma connected_component_eq_clopen_Inter ([#5335](https://github.com/leanprover-community/mathlib/pull/5335))
Prove the lemma that in a t2 and compact space, the connected component of a point equals the intersection of all its clopen neighbourhoods. Will be useful for work on Profinite sets. The proof that a Profinite set is a limit of finite discrete spaces found at: https://stacks.math.columbia.edu/tag/08ZY uses this lemma. Also some proofs that the category Profinite is reflective in CompactHausdorff uses this lemma.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* subset_iff_inter_eq_self

Modified src/order/bounded_lattice.lean
- \+ *lemma* disjoint.left_le_of_le_sup_right
- \+ *lemma* disjoint.left_le_of_le_sup_left

Modified src/topology/separation.lean
- \+ *lemma* connected_component_eq_Inter_clopen

Modified src/topology/subset_properties.lean
- \+ *lemma* is_clopen_Inter
- \+ *lemma* is_clopen_bInter
- \+ *lemma* continuous_on.preimage_clopen_of_clopen
- \+ *lemma* connected_component_subset_Inter_clopen
- \+ *theorem* is_clopen_inter_of_disjoint_cover_clopen
- \+ *theorem* subset_or_disjoint_of_clopen
- \+ *theorem* is_preconnected_iff_subset_of_disjoint_closed
- \+ *theorem* is_preconnected_iff_subset_of_fully_disjoint_closed



## [2020-12-15 21:09:34](https://github.com/leanprover-community/mathlib/commit/66eddd8)
chore(algebra/category/Module/monoidal): Speed up the elaboration ([#5383](https://github.com/leanprover-community/mathlib/pull/5383))
This takes the elaboration time from ~5s to ~2.5s for associator_naturality, from ~90s to 5s for pentagon, and from ~14s to ~8s for `triangle`.
#### Estimated changes
Modified src/algebra/category/Module/monoidal.lean
- \+/\- *lemma* associator_naturality
- \+/\- *lemma* pentagon
- \+/\- *lemma* associator_naturality
- \+/\- *lemma* pentagon



## [2020-12-15 21:09:32](https://github.com/leanprover-community/mathlib/commit/b702408)
feat(ring_theory/roots_of_unity): add squarefreeness mod p of minimal polynomial ([#5381](https://github.com/leanprover-community/mathlib/pull/5381))
Two easy results about the reduction `mod p` of the minimal polynomial over `ℤ` of a primitive root of unity: it is separable and hence squarefree.
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* separable_minimal_polynomial_mod
- \+ *lemma* squarefree_minimal_polynomial_mod



## [2020-12-15 17:57:30](https://github.com/leanprover-community/mathlib/commit/78e48c0)
ci(lint-copy-mod-doc.py): add reserved notation and set_option linters, enable small_alpha_vrachy_check linter ([#5330](https://github.com/leanprover-community/mathlib/pull/5330))
[As requested on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/the.20word.20.22to.22/near/219370843), the reserved notation linter checks for `reserve` or `precedence` at the start of a non-comment, non-string literal line in any file other than `tactic.core`.
The new set_option linter disallows `set_option pp`, `set_option profiler` and `set_option trace` at the start of a non-comment, non-string literal line.
I also noticed that the `small_alpha_vrachy_check` linter added in [#4802](https://github.com/leanprover-community/mathlib/pull/4802) wasn't actually called, so I added it to the main `lint` function.
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt

Modified scripts/lint-copy-mod-doc.py
- \+ *def* skip_comments(enumerate_lines):
- \+ *def* skip_string(enumerate_lines):
- \+ *def* reserved_notation_check(lines,
- \+ *def* set_option_check(lines,

Modified src/algebra/module/linear_map.lean

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* submodule.sup_eq_range
- \+/\- *lemma* submodule.sup_eq_range
- \+/\- *def* congr_right
- \+/\- *def* congr_right

Modified src/logic/basic.lean
- \+/\- *theorem* forall_prop_of_false
- \+/\- *theorem* forall_prop_of_false

Modified src/logic/relator.lean

Modified src/order/lattice.lean

Modified src/tactic/core.lean

Modified src/tactic/lift.lean

Modified src/tactic/lint/frontend.lean

Modified src/tactic/localized.lean

Modified src/tactic/rcases.lean

Created src/tactic/reserved_notation.lean

Modified src/tactic/simps.lean

Modified src/tactic/where.lean
- \+/\- *def* select_for_which
- \+/\- *def* select_for_which



## [2020-12-15 16:43:44](https://github.com/leanprover-community/mathlib/commit/c208a65)
feat(analysis/mean_inequalities): add Minkowski's inequality for the Lebesgue integral of ennreal functions ([#5379](https://github.com/leanprover-community/mathlib/pull/5379))
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *lemma* lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
- \+ *lemma* lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add
- \+ *theorem* lintegral_Lp_add_le



## [2020-12-15 13:31:21](https://github.com/leanprover-community/mathlib/commit/3a997b1)
fix(group_theory/subgroup): Fix doubly-namespaced instance ([#5378](https://github.com/leanprover-community/mathlib/pull/5378))
Not sure why the linter missed this.
#### Estimated changes
Modified src/group_theory/subgroup.lean



## [2020-12-15 13:31:19](https://github.com/leanprover-community/mathlib/commit/75130b3)
feat(data/set/basic): nonempty set of nonempty subtype ([#5373](https://github.com/leanprover-community/mathlib/pull/5373))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* nonempty_of_nonempty_subtype



## [2020-12-15 13:31:17](https://github.com/leanprover-community/mathlib/commit/d21d17b)
feat(ring_theory/roots_of_unity): minimal polynomial of primitive roots ([#5322](https://github.com/leanprover-community/mathlib/pull/5322))
I've added some simple results about the minimal polynomial of a primitive root of unity. The next step will be to prove that any two primitive roots have the same minimal polynomial.
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* is_integral
- \+ *lemma* minimal_polynomial_dvd_X_pow_sub_one



## [2020-12-15 10:30:21](https://github.com/leanprover-community/mathlib/commit/0f4ac1b)
feat(category_theory/limits): product comparison simp lemmas ([#5351](https://github.com/leanprover-community/mathlib/pull/5351))
This adds two new simp lemmas to reduce the prod comparison morphism and uses them to golf some proofs
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* prod_comparison_fst
- \+ *lemma* prod_comparison_snd



## [2020-12-15 10:30:19](https://github.com/leanprover-community/mathlib/commit/9ba9a98)
chore(category_theory/sites): improve naming ([#5350](https://github.com/leanprover-community/mathlib/pull/5350))
- Improve naming of some lemmas to be more descriptive
- Golf some proofs
- Add some convenience deconstructors which are useful in practice
#### Estimated changes
Modified src/category_theory/sites/canonical.lean

Modified src/category_theory/sites/sheaf.lean
- \+ *lemma* is_sheaf_for_iff_yoneda_sheaf_condition
- \+ *lemma* is_sheaf_for.functor_inclusion_comp_extend
- \+ *lemma* is_sheaf_for.unique_extend
- \+ *lemma* is_sheaf_for.hom_ext
- \+/\- *lemma* is_sheaf_for_iff_generate
- \+ *lemma* is_sheaf_of_le
- \+ *lemma* is_separated_of_is_sheaf
- \+ *lemma* is_sheaf_of_yoneda
- \- *lemma* yoneda_condition_iff_sheaf_condition
- \+/\- *lemma* is_sheaf_for_iff_generate
- \- *lemma* is_sheaf_for_coarser_topology
- \- *lemma* separated_of_sheaf
- \- *lemma* is_sheaf_yoneda



## [2020-12-15 10:30:17](https://github.com/leanprover-community/mathlib/commit/dd72a98)
feat(group_theory/perm/basic): Bundle sigma_congr_right and sum_congr into monoid_homs ([#5301](https://github.com/leanprover-community/mathlib/pull/5301))
This makes the corresponding subgroups available as `monoid_hom.range`.
As a result, the old subgroup definitions can be removed.
This also adds injectivity and cardinality lemmas.
#### Estimated changes
Modified src/group_theory/perm/basic.lean
- \+ *lemma* sum_congr_hom_injective
- \+/\- *lemma* sigma_congr_right_mul
- \+/\- *lemma* sigma_congr_right_inv
- \+/\- *lemma* sigma_congr_right_one
- \+ *lemma* sigma_congr_right_hom_injective
- \+/\- *lemma* sigma_congr_right_mul
- \+/\- *lemma* sigma_congr_right_inv
- \+/\- *lemma* sigma_congr_right_one
- \+ *def* sum_congr_hom
- \+ *def* sigma_congr_right_hom

Modified src/group_theory/perm/subgroup.lean
- \+ *lemma* sum_congr_hom.card_range
- \+ *lemma* sigma_congr_right_hom.card_range
- \- *def* sum_congr_subgroup
- \- *def* sigma_congr_right_subgroup



## [2020-12-15 10:30:14](https://github.com/leanprover-community/mathlib/commit/8041945)
feat(category_theory/monad): monadicity theorems ([#5137](https://github.com/leanprover-community/mathlib/pull/5137))
This is a proof of the reflexive (or crude) monadicity theorem along with a complete proof of Beck's monadicity theorem.
Also renames the prefix for special monad coequalizers to `free_coequalizer` rather than `coequalizer`, to avoid name-clashes when both `monad` and `limits` are imported.
#### Estimated changes
Modified src/category_theory/monad/adjunction.lean

Modified src/category_theory/monad/coequalizer.lean
- \+ *lemma* free_coequalizer.condition
- \- *lemma* coequalizer.condition
- \+ *def* free_coequalizer.top_map
- \+ *def* free_coequalizer.bottom_map
- \+ *def* free_coequalizer.π
- \+/\- *def* beck_algebra_cofork
- \- *def* coequalizer.top_map
- \- *def* coequalizer.bottom_map
- \- *def* coequalizer.π
- \+/\- *def* beck_algebra_cofork

Created src/category_theory/monad/monadicity.lean
- \+ *lemma* comparison_adjunction_unit_f_aux
- \+ *lemma* comparison_adjunction_unit_f
- \+ *lemma* comparison_adjunction_counit_app
- \+ *def* comparison_left_adjoint_obj
- \+ *def* comparison_left_adjoint_hom_equiv
- \+ *def* left_adjoint_comparison
- \+ *def* comparison_adjunction
- \+ *def* unit_cofork
- \+ *def* counit_cofork
- \+ *def* unit_colimit_of_preserves_coequalizer
- \+ *def* counit_coequalizer_of_reflects_coequalizer
- \+ *def* creates_G_split_coequalizers_of_monadic
- \+ *def* monadic_of_has_preserves_reflects_G_split_coequalizers
- \+ *def* monadic_of_creates_G_split_coequalizers
- \+ *def* monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms
- \+ *def* monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms



## [2020-12-15 10:30:11](https://github.com/leanprover-community/mathlib/commit/407d138)
chore(category_theory/equivalence): weaken essential surjectivity ([#3821](https://github.com/leanprover-community/mathlib/pull/3821))
Weaken essential surjectivity to be a Prop, rather than the data of the inverse.
#### Estimated changes
Modified src/algebra/category/Group/Z_Module_equivalence.lean

Modified src/category_theory/Fintype.lean

Modified src/category_theory/equivalence.lean
- \+ *lemma* ess_surj_of_equivalence
- \- *def* obj_preimage
- \- *def* fun_obj_preimage_iso
- \- *def* ess_surj_of_equivalence
- \- *def* equivalence_of_fully_faithfully_ess_surj

Modified src/category_theory/monad/adjunction.lean

Modified src/topology/category/Compactum.lean
- \+ *lemma* ess_surj



## [2020-12-15 07:29:57](https://github.com/leanprover-community/mathlib/commit/a1aa511)
feat(simps): interaction between simps and to_additive ([#5331](https://github.com/leanprover-community/mathlib/pull/5331))
If a definition is both marked `to_additive` and `simps` (in that order), `simps` will from also apply the `to_additive` attribute to its generated lemmas (which creates the additive counterparts of the simp-lemmas).
This also generalizes `set_attribute` to use the default parameter if possible.
This implements half of [#1639](https://github.com/leanprover-community/mathlib/pull/1639).
#### Estimated changes
Modified src/algebra/category/Group/basic.lean

Modified src/algebra/group/to_additive.lean

Modified src/logic/embedding.lean

Modified src/tactic/core.lean

Modified src/tactic/simps.lean

Modified test/simps.lean

Modified test/tactics.lean



## [2020-12-15 03:52:57](https://github.com/leanprover-community/mathlib/commit/a959718)
chore(algebra/quadratic_discriminant): golf proofs using limits ([#5339](https://github.com/leanprover-community/mathlib/pull/5339))
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \- *lemma* exists_lt_mul_self
- \- *lemma* exists_le_mul_self

Modified src/algebra/quadratic_discriminant.lean

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* exists_lt_mul_self
- \+ *lemma* exists_le_mul_self



## [2020-12-15 01:31:40](https://github.com/leanprover-community/mathlib/commit/ff13cde)
chore(scripts): update nolints.txt ([#5376](https://github.com/leanprover-community/mathlib/pull/5376))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-15 01:31:38](https://github.com/leanprover-community/mathlib/commit/cadaa44)
feat(group_theory/subgroup): Add decidable_mem_range ([#5371](https://github.com/leanprover-community/mathlib/pull/5371))
This means that `fintype (quotient_group.quotient f.range)` can be found by type-class resolution.
#### Estimated changes
Modified src/group_theory/subgroup.lean



## [2020-12-15 01:31:36](https://github.com/leanprover-community/mathlib/commit/b2ab94f)
fix(group_theory): Remove a duplicate fintype instance on quotient_group.quotient ([#5368](https://github.com/leanprover-community/mathlib/pull/5368))
This noncomputable instance was annoying, and can easy be recovered by passing in a classical decidable_pred instance instead.
#### Estimated changes
Modified src/group_theory/coset.lean

Modified src/group_theory/order_of_element.lean

Modified src/group_theory/perm/subgroup.lean

Modified src/group_theory/sylow.lean



## [2020-12-15 01:31:34](https://github.com/leanprover-community/mathlib/commit/b364d33)
chore(topology/instances/ennreal): remove summability assumption in tendsto_sum_nat_add ([#5366](https://github.com/leanprover-community/mathlib/pull/5366))
We have currently
```lean
lemma tendsto_sum_nat_add (f : ℕ → ℝ≥0) (hf : summable f) : tendsto (λ i, ∑' k, f (k + i)) at_top (𝓝 0)
```
However, the summability assumption is not necessary as otherwise all sums are zero, and the statement still holds. The PR removes the assumption.
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* tendsto_sum_nat_add

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* tendsto_sum_nat_add
- \+/\- *lemma* tendsto_sum_nat_add

Modified src/topology/instances/nnreal.lean
- \+ *lemma* summable_nat_add_iff



## [2020-12-15 01:31:32](https://github.com/leanprover-community/mathlib/commit/4dbb3e2)
chore(data/finsupp/basic): more lemmas about `α →₀ ℕ` ([#5362](https://github.com/leanprover-community/mathlib/pull/5362))
* define `canonically_ordered_add_monoid` instance;
* add a few simp lemmas;
* more lemmas about product over `finsupp.antidiagonal n`;
* define `finsupp.Iic_finset`, use it for `finite_le_nat`.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+/\- *lemma* single_eq_zero
- \+ *lemma* nat_zero_sub
- \+ *lemma* nat_add_sub_cancel
- \+ *lemma* nat_add_sub_cancel_left
- \+ *lemma* nat_add_sub_of_le
- \+ *lemma* nat_sub_add_cancel
- \+/\- *lemma* swap_mem_antidiagonal_support
- \+ *lemma* antidiagonal_support_filter_fst_eq
- \+ *lemma* antidiagonal_support_filter_snd_eq
- \+ *lemma* prod_antidiagonal_support_swap
- \+ *lemma* mem_Iic_finset
- \+ *lemma* coe_Iic_finset
- \+/\- *lemma* single_eq_zero
- \+/\- *lemma* swap_mem_antidiagonal_support
- \+ *def* Iic_finset

Modified src/ring_theory/power_series.lean



## [2020-12-15 01:31:30](https://github.com/leanprover-community/mathlib/commit/8de08f7)
chore(order/iterate): generalize lemmas about inequalities and iterations ([#5357](https://github.com/leanprover-community/mathlib/pull/5357))
If `f : α → α` is a monotone function and `x y : ℕ → α` are two
sequences such that `x 0 ≤ y 0`, `x (n + 1) ≤ f (x n)`, and
`f (y n) ≤ y (n + 1)`, then `x n ≤ y n`. This lemma (and its versions
for `<`) generalize `geom_le` as well as `iterate_le_of_map_le`.
#### Estimated changes
Modified src/analysis/hofer.lean

Modified src/analysis/specific_limits.lean
- \+/\- *lemma* geom_lt
- \+ *lemma* geom_le
- \+ *lemma* tendsto_at_top_of_geom_le
- \+/\- *lemma* geom_lt
- \- *lemma* tendsto_at_top_of_geom_lt

Modified src/order/iterate.lean
- \+ *lemma* seq_le_seq
- \+ *lemma* seq_pos_lt_seq_of_lt_of_le
- \+ *lemma* seq_pos_lt_seq_of_le_of_lt
- \+ *lemma* seq_lt_seq_of_lt_of_le
- \+ *lemma* seq_lt_seq_of_le_of_lt



## [2020-12-14 23:07:26](https://github.com/leanprover-community/mathlib/commit/d1904fc)
refactor(measure_theory/lp_space): move most of the proof of mem_Lp.add to a new lemma in analysis/mean_inequalities ([#5370](https://github.com/leanprover-community/mathlib/pull/5370))
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *lemma* lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top

Modified src/measure_theory/lp_space.lean



## [2020-12-14 23:07:24](https://github.com/leanprover-community/mathlib/commit/dc719a9)
feat(algebra/lie/basic): define ideal operations for Lie modules ([#5337](https://github.com/leanprover-community/mathlib/pull/5337))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* coe_to_set_mk
- \+ *lemma* coe_to_submodule_mk
- \+/\- *lemma* le_def
- \+ *lemma* coe_submodule_le_coe_submodule
- \+/\- *lemma* add_eq_sup
- \+ *lemma* coe_sup
- \+ *lemma* mem_sup
- \+ *lemma* eq_bot_iff
- \+ *lemma* lie_ideal_oper_eq_span
- \+ *lemma* lie_mem_lie
- \+ *lemma* lie_comm
- \+ *lemma* lie_le_right
- \+ *lemma* lie_le_left
- \+ *lemma* lie_le_inf
- \+ *lemma* lie_bot
- \+ *lemma* bot_lie
- \+ *lemma* mono_lie
- \+ *lemma* mono_lie_left
- \+ *lemma* mono_lie_right
- \+ *lemma* lie_sup
- \+ *lemma* sup_lie
- \+ *lemma* trivial_iff_derived_eq_bot
- \+/\- *lemma* le_def
- \+/\- *lemma* add_eq_sup
- \+ *def* derived_lie_submodule

Modified src/algebra/module/submodule.lean
- \+ *lemma* mk_coe

Modified src/linear_algebra/finite_dimensional.lean



## [2020-12-14 21:52:23](https://github.com/leanprover-community/mathlib/commit/a649c59)
feat(field_theory/intermediate_field): lift2_alg_equiv ([#5344](https://github.com/leanprover-community/mathlib/pull/5344))
Proves that lift2 is isomorphic as an algebra over the base field
#### Estimated changes
Modified src/field_theory/intermediate_field.lean
- \+ *def* lift2_alg_equiv



## [2020-12-14 19:54:21](https://github.com/leanprover-community/mathlib/commit/4415dc0)
feat(algebra/algebra/basic): arrow_congr for alg_equiv ([#5346](https://github.com/leanprover-community/mathlib/pull/5346))
This is a copy of equiv.arrow_congr
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* arrow_congr_comp
- \+ *lemma* arrow_congr_refl
- \+ *lemma* arrow_congr_trans
- \+ *lemma* arrow_congr_symm
- \+ *def* arrow_congr



## [2020-12-14 16:39:30](https://github.com/leanprover-community/mathlib/commit/07b5618)
chore(linear_algebra/{multilinear,alternating}): Generalize smul and neg instance ([#5364](https://github.com/leanprover-community/mathlib/pull/5364))
This brings the generality in line with that of `linear_map`. Notably:
* `has_neg` now exists when only the codomain has negation
* `has_scalar` now exists for the weaker condition of `smul_comm_class` rather than `has_scalar_tower`
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *lemma* map_neg
- \+/\- *lemma* neg_apply
- \+/\- *lemma* alternatization_apply
- \+/\- *lemma* to_multilinear_map_alternization
- \+/\- *lemma* neg_apply
- \+/\- *lemma* alternatization_apply
- \+/\- *lemma* to_multilinear_map_alternization
- \+/\- *def* alternatization
- \+/\- *def* alternatization

Modified src/linear_algebra/multilinear.lean
- \+ *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_sub



## [2020-12-14 16:39:28](https://github.com/leanprover-community/mathlib/commit/b1c56b1)
feat(field_theory.minimal_polynomial): add results for GCD domains ([#5336](https://github.com/leanprover-community/mathlib/pull/5336))
I have added `gcd_domain_dvd`: for GCD domains, the minimal polynomial divides any primitive polynomial that has the integral
element as root.
For `gcd_domain_eq_field_fractions` and `gcd_domain_dvd` I have also added explicit versions for `ℤ`. Unfortunately, it seems impossible (to me at least) to apply the general lemmas and I had to redo the proofs, see [Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Minimal.20polynomial.20over.20.E2.84.9A.20vs.20over.20.E2.84.A4) for more details. (The basic reason seems to be that it's hard to convince lean that `is_scalar_tower ℤ ℚ α` holds using the localization map).
#### Estimated changes
Modified src/field_theory/minimal_polynomial.lean
- \+ *lemma* over_int_eq_over_rat
- \+ *lemma* gcd_domain_dvd
- \+ *lemma* integer_dvd



## [2020-12-14 16:39:26](https://github.com/leanprover-community/mathlib/commit/f443792)
feat(topology/subset_properties): add instances for totally_disconnected_spaces ([#5334](https://github.com/leanprover-community/mathlib/pull/5334))
Add the instances subtype.totally_disconnected_space and pi.totally_disconnected_space.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* subsingleton_of_image

Modified src/topology/subset_properties.lean



## [2020-12-14 16:39:24](https://github.com/leanprover-community/mathlib/commit/d36af18)
feat(tactic/induction): add induction'/cases'/eliminate_hyp/eliminate_expr tactics ([#5027](https://github.com/leanprover-community/mathlib/pull/5027))
This PR adds interactive tactics `induction'` and `cases'` as well as
non-interactive variants `eliminate_hyp` and `eliminate_expr`. The tactics are
similar to standard `induction` and `cases`, but they feature several
improvements:
- `induction'` performs 'dependent induction', which means it takes the indices
  of indexed inductive types fully into account. This is convenient, for example,
  for programming language or logic formalisations, which tend to rely heavily on
  indexed types.
- `induction'` by default generalises everything that can be generalised. This
  is to support beginners, who often struggle to identify that a proof requires
  a generalised induction hypothesis. In cases where this feature hinders more
  than it helps, it can easily be turned off.
- `induction'` and `cases'` generate much more human-friendly names than their
  standard counterparts. This is, again, mostly to support beginners. Experts
  should usually supply explicit names to make proof scripts more robust.
- `cases'` works for some rare goals which `cases` does not support, but should
  otherwise be mostly a drop-in replacement (except for the generated names).
#### Estimated changes
Modified src/data/list/defs.lean
- \+ *def* all_some
- \+ *def* fill_nones
- \+ *def* take_list
- \+ *def* to_rbmap

Modified src/tactic/binder_matching.lean

Modified src/tactic/core.lean

Created src/tactic/induction.lean

Created test/induction.lean
- \+ *lemma* fraction.ext
- \+ *lemma* nonempty_node_elim
- \+ *lemma* head
- \+ *lemma* head_induction_on
- \+ *lemma* accufact_1_eq_fact
- \+ *lemma* subst_Var
- \+ *lemma* lt_lte
- \+ *lemma* not_sorted_17_13
- \+ *lemma* rev_palindrome
- \+ *lemma* tc_pets₁
- \+ *lemma* tc_pets₂
- \+ *lemma* tc_trans
- \+ *lemma* tc_trans'
- \+ *lemma* not_even_2_mul_add_1
- \+ *lemma* not_big_step_while_true
- \+ *lemma* not_curried_big_step_while_true
- \+ *lemma* small_step_if_equal_states
- \+ *lemma* trans
- \+ *lemma* single
- \+ *lemma* trans_induction_on
- \+ *lemma* lift
- \+ *lemma* big_step_deterministic
- \+ *lemma* big_step_skip_iff
- \+ *lemma* big_step_assign_iff
- \+ *lemma* big_step_seq_iff
- \+ *lemma* big_step_ite_iff
- \+ *lemma* big_step_while_iff
- \+ *lemma* big_step_while_true_iff
- \+ *lemma* big_step_while_false_iff
- \+ *lemma* small_step_final
- \+ *lemma* small_step_deterministic
- \+ *lemma* small_step_skip
- \+ *lemma* small_step_seq_iff
- \+ *lemma* small_step_ite_iff
- \+ *lemma* star_small_step_seq
- \+ *lemma* star_small_step_of_big_step
- \+ *lemma* big_step_of_small_step_of_big_step
- \+ *lemma* big_step_of_star_small_step
- \+ *def* append
- \+ *def* plus
- \+ *def* accufact
- \+ *def* subst
- \+ *def* state
- \+ *def* state.update



## [2020-12-14 13:16:21](https://github.com/leanprover-community/mathlib/commit/a65de99)
feat(data/equiv): Add `congr_arg`, `congr_fun`, and `ext_iff` lemmas to equivs ([#5367](https://github.com/leanprover-community/mathlib/pull/5367))
These members already exist on the corresponding homs
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* ext_iff

Modified src/algebra/module/linear_map.lean
- \+ *lemma* ext_iff

Modified src/data/equiv/basic.lean
- \+/\- *lemma* perm.ext
- \+/\- *lemma* perm.ext

Modified src/data/equiv/mul_add.lean
- \+ *lemma* ext_iff

Modified src/data/equiv/ring.lean
- \+ *lemma* ext_iff



## [2020-12-14 13:16:18](https://github.com/leanprover-community/mathlib/commit/dad88d8)
feat(field_theory/splitting_field): add splits_X theorem ([#5343](https://github.com/leanprover-community/mathlib/pull/5343))
This is a handy result and isn't definitionally a special case of splits_X_sub_C
#### Estimated changes
Modified src/field_theory/splitting_field.lean
- \+ *theorem* splits_X



## [2020-12-14 13:16:15](https://github.com/leanprover-community/mathlib/commit/cf7377a)
chore(field_theory/adjoin): move dim/findim lemmas ([#5342](https://github.com/leanprover-community/mathlib/pull/5342))
adjoin.lean has some dim/findim lemmas, some of which could be moved to intermediate_field.lean
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* dim_eq_one_iff
- \+ *lemma* findim_eq_one_iff
- \- *lemma* dim_intermediate_field_eq_dim_subalgebra
- \- *lemma* findim_intermediate_field_eq_findim_subalgebra
- \- *lemma* to_subalgebra_eq_iff

Modified src/field_theory/intermediate_field.lean
- \+ *lemma* dim_eq_dim_subalgebra
- \+ *lemma* findim_eq_findim_subalgebra
- \+ *lemma* to_subalgebra_eq_iff
- \+/\- *lemma* eq_of_le_of_findim_le
- \+/\- *lemma* eq_of_le_of_findim_eq
- \+/\- *lemma* eq_of_le_of_findim_le'
- \+/\- *lemma* eq_of_le_of_findim_eq'
- \+/\- *lemma* eq_of_le_of_findim_le
- \+/\- *lemma* eq_of_le_of_findim_eq
- \+/\- *lemma* eq_of_le_of_findim_le'
- \+/\- *lemma* eq_of_le_of_findim_eq'



## [2020-12-14 13:16:14](https://github.com/leanprover-community/mathlib/commit/0d7ddf1)
chore(order/filter/at_top_bot): add/rename lemmas about limits like `±∞*c` ([#5333](https://github.com/leanprover-community/mathlib/pull/5333))
### New lemmas
* `filter.tendsto.nsmul_at_top` and `filter.tendsto.nsmul_at_bot`;
* `filter.tendsto_mul_self_at_top`;
* `filter.tendsto.at_top_mul_at_bot`, `filter.tendsto.at_bot_mul_at_top`,
  `filter.tendsto.at_bot_mul_at_bot`;
* `filter.tendsto.at_top_of_const_mul`, `filter.tendsto.at_top_of_mul_const`;
* `filter.tendsto.at_top_div_const`, `filter.tendsto.neg_const_mul_at_top`,
  `filter.tendsto.at_top_mul_neg_const`, `filter.tendsto.const_mul_at_bot`,
  `filter.tendsto.at_bot_mul_const`, `filer.tendsto.at_bot_div_const`,
  `filter.tendsto.neg_const_mul_at_bot`, `filter.tendsto.at_bot_mul_neg_const`.
### Renamed lemmas
* `tendsto_pow_at_top` → `filter.tendsto_pow_at_top`;
* `tendsto_at_top_mul_left` → `filter.tendsto.const_mul_at_top'`;
* `tendsto_at_top_mul_right` → `filter.tendsto.at_top_mul_const'`;
* `tendsto_at_top_mul_left'` → `filter.tendsto.const_mul_at_top`;
* `tendsto_at_top_mul_right'` → `filer.tendsto.at_top_mul_const`;
* `tendsto_mul_at_top` → `filter.tendsto.at_top_mul`;
* `tendsto_mul_at_bot` → `filter.tendsto.at_top_mul_neg`;
* `tendsto_at_top_mul_at_top` → `filter.tendsto.at_top_mul_at_top`.
#### Estimated changes
Modified src/analysis/asymptotic_equivalent.lean

Modified src/analysis/special_functions/exp_log.lean

Modified src/analysis/special_functions/trigonometric.lean

Modified src/analysis/specific_limits.lean

Modified src/order/filter/archimedean.lean
- \+ *lemma* filter.tendsto.const_mul_at_top'
- \+ *lemma* filter.tendsto.at_top_mul_const'

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* tendsto.nsmul_at_top
- \+ *lemma* tendsto.nsmul_at_bot
- \+/\- *lemma* tendsto_neg_at_top_at_bot
- \+/\- *lemma* tendsto_neg_at_bot_at_top
- \+ *lemma* tendsto.at_top_mul_at_top
- \+ *lemma* tendsto_mul_self_at_top
- \+ *lemma* tendsto_pow_at_top
- \+ *lemma* tendsto.at_top_mul_at_bot
- \+ *lemma* tendsto.at_bot_mul_at_top
- \+ *lemma* tendsto.at_bot_mul_at_bot
- \+ *lemma* tendsto.at_top_of_const_mul
- \+ *lemma* tendsto.at_top_of_mul_const
- \+ *lemma* tendsto.const_mul_at_top
- \+ *lemma* tendsto.at_top_mul_const
- \+ *lemma* tendsto.at_top_div_const
- \+ *lemma* tendsto.neg_const_mul_at_top
- \+ *lemma* tendsto.at_top_mul_neg_const
- \+ *lemma* tendsto.const_mul_at_bot
- \+ *lemma* tendsto.at_bot_mul_const
- \+ *lemma* tendsto.at_bot_div_const
- \+ *lemma* tendsto.neg_const_mul_at_bot
- \+ *lemma* tendsto.at_bot_mul_neg_const
- \- *lemma* tendsto_at_top_mul_at_top
- \+/\- *lemma* tendsto_neg_at_top_at_bot
- \+/\- *lemma* tendsto_neg_at_bot_at_top

Modified src/topology/algebra/ordered.lean
- \+ *lemma* filter.tendsto.at_top_mul
- \+ *lemma* filter.tendsto.at_top_mul_neg
- \- *lemma* tendsto_pow_at_top
- \- *lemma* tendsto_at_top_mul_left
- \- *lemma* tendsto_at_top_mul_right
- \- *lemma* tendsto_at_top_mul_left'
- \- *lemma* tendsto_at_top_mul_right'
- \- *lemma* tendsto_at_top_div
- \- *lemma* tendsto_mul_at_top
- \- *lemma* tendsto_mul_at_bot

Modified src/topology/algebra/polynomial.lean



## [2020-12-14 13:16:12](https://github.com/leanprover-community/mathlib/commit/1d37ff1)
feat(analysis/mean_inequalities): add weighted generalized mean inequality for ennreal ([#5316](https://github.com/leanprover-community/mathlib/pull/5316))
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *theorem* rpow_arith_mean_le_arith_mean_rpow
- \+ *theorem* rpow_arith_mean_le_arith_mean2_rpow

Modified src/data/real/ennreal.lean
- \+ *lemma* le_of_top_imp_top_of_to_nnreal_le
- \+ *lemma* to_nnreal_mul
- \+ *lemma* to_nnreal_pow
- \+ *lemma* to_nnreal_prod



## [2020-12-14 13:16:10](https://github.com/leanprover-community/mathlib/commit/cecab59)
feat(group_theory/congruence): Add inv and neg ([#5304](https://github.com/leanprover-community/mathlib/pull/5304))
#### Estimated changes
Modified src/group_theory/congruence.lean



## [2020-12-14 13:16:08](https://github.com/leanprover-community/mathlib/commit/6dc5000)
feat(computability/language): define formal languages ([#5291](https://github.com/leanprover-community/mathlib/pull/5291))
Lifted from [#5036](https://github.com/leanprover-community/mathlib/pull/5036) in order to include in [#5038](https://github.com/leanprover-community/mathlib/pull/5038) as well.
#### Estimated changes
Created src/computability/language.lean
- \+ *lemma* zero_def
- \+ *lemma* one_def
- \+ *lemma* add_def
- \+ *lemma* mul_def
- \+ *lemma* star_def
- \+ *lemma* add_self
- \+ *lemma* star_def_nonempty
- \+ *def* language
- \+ *def* star



## [2020-12-14 13:16:05](https://github.com/leanprover-community/mathlib/commit/67b5ff6)
feat(algebra/direct_sum): constructor for morphisms into direct sums ([#5204](https://github.com/leanprover-community/mathlib/pull/5204))
#### Estimated changes
Modified src/algebra/direct_sum.lean
- \+ *lemma* from_add_monoid_of
- \+ *lemma* from_add_monoid_of_apply
- \+ *def* from_add_monoid

Modified src/algebra/group/hom.lean



## [2020-12-14 11:45:59](https://github.com/leanprover-community/mathlib/commit/c722b96)
feat (topology/instances/ennreal): summability from finite sum control ([#5363](https://github.com/leanprover-community/mathlib/pull/5363))
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+ *lemma* summable_iff_not_tendsto_nat_at_top
- \+ *lemma* summable_of_sum_range_le
- \+ *lemma* tsum_le_of_sum_range_le
- \+ *lemma* summable_iff_not_tendsto_nat_at_top_of_nonneg
- \+ *lemma* summable_of_sum_range_le
- \+ *lemma* tsum_le_of_sum_range_le



## [2020-12-14 10:02:51](https://github.com/leanprover-community/mathlib/commit/91e5b8a)
chore(analysis/normed_space/ordered): minor golfing ([#5356](https://github.com/leanprover-community/mathlib/pull/5356))
#### Estimated changes
Modified src/analysis/normed_space/ordered.lean



## [2020-12-14 10:02:48](https://github.com/leanprover-community/mathlib/commit/2245cfb)
feat(measurable_space): infix notation for measurable_equiv ([#5329](https://github.com/leanprover-community/mathlib/pull/5329))
We use `≃ᵐ` as notation. Note: `≃ₘ` is already used for diffeomorphisms.
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+/\- *def* homemorph.to_measurable_equiv
- \+/\- *def* measurable_equiv.ennreal_equiv_nnreal
- \+/\- *def* ennreal_equiv_sum
- \+/\- *def* homemorph.to_measurable_equiv
- \+/\- *def* measurable_equiv.ennreal_equiv_nnreal
- \+/\- *def* ennreal_equiv_sum

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* coe_eq
- \+/\- *lemma* coe_eq
- \+/\- *def* refl
- \+/\- *def* trans
- \+/\- *def* symm
- \+/\- *def* prod_congr
- \+/\- *def* prod_comm
- \+/\- *def* prod_assoc
- \+/\- *def* sum_congr
- \+/\- *def* set.prod
- \+/\- *def* set.univ
- \+/\- *def* set.singleton
- \+/\- *def* set.range_inl
- \+/\- *def* set.range_inr
- \+/\- *def* refl
- \+/\- *def* trans
- \+/\- *def* symm
- \+/\- *def* prod_congr
- \+/\- *def* prod_comm
- \+/\- *def* prod_assoc
- \+/\- *def* sum_congr
- \+/\- *def* set.prod
- \+/\- *def* set.univ
- \+/\- *def* set.singleton
- \+/\- *def* set.range_inl
- \+/\- *def* set.range_inr



## [2020-12-14 08:35:30](https://github.com/leanprover-community/mathlib/commit/6f69741)
chore(analysis/calculus/*): rename `*.of_local_homeomorph` to `local_homeomorph.*_symm` ([#5358](https://github.com/leanprover-community/mathlib/pull/5358))
Rename some lemmas, and make `(f : local_homeomorph _ _)` an explicit argument:
* `has_fderiv_at.of_local_homeomorph` → `local_homeomorph.has_fderiv_at_symm`;
* `times_cont_diff_at.of_local_homeomorph` → `local_homeomorph.times_cont_diff_at_symm`.
If we want to apply one of these lemmas to prove smoothness of, e.g., `arctan`, `log`, or `arcsin`, then the goal
has no `local_homeomorph.symm`, and we need to explicitly supply a `local_homeomorph` with an appropriate `inv_fun`.
Also add some lemmas that help to prove that the inverse function is **not** differentiable at a point.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_within_at.congr_of_eventually_eq_of_mem
- \+ *lemma* local_homeomorph.has_deriv_at_symm
- \+ *theorem* not_differentiable_within_at_of_local_left_inverse_has_deriv_within_at_zero
- \+ *theorem* not_differentiable_at_of_local_left_inverse_has_deriv_at_zero

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* local_homeomorph.has_strict_fderiv_at_symm
- \+ *lemma* local_homeomorph.has_fderiv_at_symm
- \- *lemma* has_fderiv_at.of_local_homeomorph

Modified src/analysis/calculus/inverse.lean
- \+ *lemma* local_inverse_def
- \+/\- *lemma* local_inverse_apply_image
- \+/\- *lemma* local_inverse_apply_image

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *theorem* local_homeomorph.times_cont_diff_at_symm
- \- *theorem* times_cont_diff_at.of_local_homeomorph



## [2020-12-14 02:41:32](https://github.com/leanprover-community/mathlib/commit/714bc15)
feat(category_theory/adjunction): adjoint lifting theorems ([#5118](https://github.com/leanprover-community/mathlib/pull/5118))
Proves the [adjoint lifting theorem](https://ncatlab.org/nlab/show/adjoint+lifting+theorem) and the [adjoint triangle theorem](https://ncatlab.org/nlab/show/adjoint+triangle+theorem).
The intent here is for all but the last four statements in the file to be implementation.
#### Estimated changes
Created src/category_theory/adjunction/lifting.lean
- \+ *theorem* +*
- \+ *theorem* +*
- \+ *theorem* +-/
- \+ *theorem* +-/
- \+ *theorem* +-/
- \+ *def* counit_coequalises
- \+ *def* other_map
- \+ *def* construct_left_adjoint_equiv



## [2020-12-14 01:26:51](https://github.com/leanprover-community/mathlib/commit/b7a9615)
chore(scripts): update nolints.txt ([#5360](https://github.com/leanprover-community/mathlib/pull/5360))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-13 09:58:12](https://github.com/leanprover-community/mathlib/commit/88fb7ca)
chore(analysis/calculus): move the definition of `formal_multilinear_series` to a new file ([#5348](https://github.com/leanprover-community/mathlib/pull/5348))
#### Estimated changes
Created src/analysis/calculus/formal_multilinear_series.lean
- \+ *lemma* congr
- \+ *def* formal_multilinear_series
- \+ *def* shift
- \+ *def* unshift

Modified src/analysis/calculus/times_cont_diff.lean
- \- *lemma* congr
- \- *def* formal_multilinear_series
- \- *def* shift
- \- *def* unshift
- \- *def* formal_multilinear_series.restrict_scalars



## [2020-12-13 01:29:56](https://github.com/leanprover-community/mathlib/commit/36eec1a)
chore(scripts): update nolints.txt ([#5341](https://github.com/leanprover-community/mathlib/pull/5341))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-12 23:59:14](https://github.com/leanprover-community/mathlib/commit/eb9164b)
feat(category_theory/sites): naming and attributes ([#5340](https://github.com/leanprover-community/mathlib/pull/5340))
Adds simps projections for sieve arrows and makes the names consistent (some used `mem_` and others used `_apply`, now they only use the latter).
#### Estimated changes
Modified src/category_theory/sites/canonical.lean

Modified src/category_theory/sites/pretopology.lean

Modified src/category_theory/sites/sieves.lean
- \+ *lemma* Inf_apply
- \+ *lemma* Sup_apply
- \+ *lemma* inter_apply
- \+ *lemma* union_apply
- \+ *lemma* top_apply
- \+ *lemma* pushforward_apply_comp
- \- *lemma* mem_Inf
- \- *lemma* mem_Sup
- \- *lemma* mem_inter
- \- *lemma* mem_union
- \- *lemma* mem_top
- \- *lemma* mem_generate
- \- *lemma* mem_pullback
- \- *lemma* mem_pushforward_of_comp
- \- *lemma* sieve_of_subfunctor_apply



## [2020-12-12 22:41:29](https://github.com/leanprover-community/mathlib/commit/68818b3)
feat(field_theory/galois): Is_galois iff is_galois top ([#5285](https://github.com/leanprover-community/mathlib/pull/5285))
Proves that E/F is Galois iff top/F is Galois.
#### Estimated changes
Modified src/field_theory/galois.lean
- \+ *lemma* is_galois.of_alg_equiv
- \+ *lemma* alg_equiv.transfer_galois
- \+ *lemma* is_galois_iff_is_galois_top



## [2020-12-12 17:17:36](https://github.com/leanprover-community/mathlib/commit/5ced4dd)
feat(ring_theory/finiteness): add iff_quotient_mv_polynomial ([#5321](https://github.com/leanprover-community/mathlib/pull/5321))
Add characterizations of finite type algebra as quotient of polynomials rings. There are three version of the same lemma, using a `finset`, a `fintype` and `fin n`.
#### Estimated changes
Modified src/data/mv_polynomial/equiv.lean
- \+ *def* alg_equiv_of_equiv

Modified src/ring_theory/finiteness.lean
- \+ *lemma* iff_quotient_mv_polynomial
- \+ *lemma* iff_quotient_mv_polynomial'
- \+ *lemma* iff_quotient_mv_polynomial''



## [2020-12-12 09:03:27](https://github.com/leanprover-community/mathlib/commit/3afdf41)
chore(*): generalize some lemmas from `linear_ordered_semiring` to `ordered_semiring` ([#5327](https://github.com/leanprover-community/mathlib/pull/5327))
API changes:
* Many lemmas now have weaker typeclass assumptions. Sometimes this means that `@myname _ _ _` needs one more `_`.
* Drop `eq_one_of_mul_self_left_cancel` etc in favor of the new `mul_eq_left_iff` etc.
* A few new lemmas that state `monotone` or `strict_mono_incr_on`.
#### Estimated changes
Modified archive/imo/imo1998_q2.lean

Modified src/algebra/archimedean.lean
- \+/\- *lemma* add_one_pow_unbounded_of_pos
- \+/\- *lemma* add_one_pow_unbounded_of_pos
- \+/\- *theorem* exists_nat_gt
- \+/\- *theorem* exists_nat_ge
- \+/\- *theorem* exists_nat_gt
- \+/\- *theorem* exists_nat_ge

Modified src/algebra/char_zero.lean
- \+/\- *lemma* two_ne_zero'
- \+/\- *lemma* two_ne_zero'

Modified src/algebra/group/basic.lean
- \+ *lemma* mul_eq_left_iff
- \+ *lemma* left_eq_mul_iff
- \+ *lemma* mul_eq_right_iff
- \+ *lemma* right_eq_mul_iff
- \- *lemma* eq_one_of_mul_self_left_cancel
- \- *lemma* eq_one_of_left_cancel_mul_self
- \- *lemma* eq_one_of_mul_self_right_cancel
- \- *lemma* eq_one_of_right_cancel_mul_self

Modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_mono
- \+ *lemma* strict_mono_pow
- \+ *theorem* strict_mono_incr_on_pow
- \+/\- *theorem* pow_left_inj
- \+/\- *theorem* pow_left_inj

Modified src/algebra/group_power/lemmas.lean

Modified src/data/int/cast.lean
- \+ *theorem* cast_mono
- \+/\- *theorem* cast_nonneg
- \+/\- *theorem* cast_le
- \+ *theorem* cast_strict_mono
- \+/\- *theorem* cast_lt
- \+/\- *theorem* cast_nonpos
- \+/\- *theorem* cast_pos
- \+/\- *theorem* cast_lt_zero
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* cast_abs
- \+/\- *theorem* cast_nonneg
- \+/\- *theorem* cast_le
- \+/\- *theorem* cast_lt
- \+/\- *theorem* cast_nonpos
- \+/\- *theorem* cast_pos
- \+/\- *theorem* cast_lt_zero
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* cast_abs

Modified src/data/nat/cast.lean
- \+/\- *lemma* cast_two
- \+/\- *lemma* cast_add_one_pos
- \+/\- *lemma* cast_two
- \+/\- *lemma* cast_add_one_pos
- \+/\- *theorem* cast_nonneg
- \+ *theorem* mono_cast
- \+/\- *theorem* strict_mono_cast
- \+/\- *theorem* cast_le
- \+/\- *theorem* cast_lt
- \+/\- *theorem* cast_pos
- \+/\- *theorem* one_lt_cast
- \+/\- *theorem* one_le_cast
- \+/\- *theorem* cast_lt_one
- \+/\- *theorem* cast_le_one
- \+/\- *theorem* abs_cast
- \+/\- *theorem* cast_nonneg
- \+/\- *theorem* strict_mono_cast
- \+/\- *theorem* cast_le
- \+/\- *theorem* cast_lt
- \+/\- *theorem* cast_pos
- \+/\- *theorem* one_lt_cast
- \+/\- *theorem* one_le_cast
- \+/\- *theorem* cast_lt_one
- \+/\- *theorem* cast_le_one
- \+/\- *theorem* abs_cast

Modified src/data/zsqrtd/gaussian_int.lean

Modified src/order/filter/archimedean.lean
- \+/\- *lemma* tendsto_coe_nat_at_top_iff
- \+/\- *lemma* tendsto_coe_nat_at_top_at_top
- \+/\- *lemma* tendsto_coe_int_at_top_iff
- \+/\- *lemma* tendsto_coe_int_at_top_at_top
- \+/\- *lemma* tendsto_coe_nat_at_top_iff
- \+/\- *lemma* tendsto_coe_nat_at_top_at_top
- \+/\- *lemma* tendsto_coe_int_at_top_iff
- \+/\- *lemma* tendsto_coe_int_at_top_at_top

Modified src/ring_theory/derivation.lean



## [2020-12-12 07:17:02](https://github.com/leanprover-community/mathlib/commit/dad5aab)
refactor(ring_theory/polynomial/homogeneous): redefine `mv_polynomial.homogeneous_component` ([#5294](https://github.com/leanprover-community/mathlib/pull/5294))
* redefine `homogeneous_component` using `finsupp.restrict_dom`,
  “upgrade” it to a `linear_map`;
* add `coeff_homogeneous_component` and use it to golf some proofs.
#### Estimated changes
Modified src/ring_theory/polynomial/homogeneous.lean
- \+ *lemma* coeff_homogeneous_component



## [2020-12-12 07:17:00](https://github.com/leanprover-community/mathlib/commit/9cc8835)
feat(group_theory/perm/subgroup): Add some simple subgroups of permutations ([#5279](https://github.com/leanprover-community/mathlib/pull/5279))
#### Estimated changes
Created src/group_theory/perm/subgroup.lean
- \+ *def* sum_congr_subgroup
- \+ *def* sigma_congr_right_subgroup



## [2020-12-12 07:16:58](https://github.com/leanprover-community/mathlib/commit/84f9938)
feat(category_theory/sites): sheaves on types ([#5259](https://github.com/leanprover-community/mathlib/pull/5259))
#### Estimated changes
Modified src/category_theory/sites/sheaf.lean
- \+ *lemma* is_sheaf.is_sheaf_for

Created src/category_theory/sites/types.lean
- \+ *lemma* discrete_sieve_mem
- \+ *lemma* generate_discrete_presieve_mem
- \+ *lemma* yoneda'_comp
- \+ *lemma* eval_types_glue
- \+ *lemma* types_glue_eval
- \+ *lemma* eval_map
- \+ *lemma* eval_app
- \+ *lemma* subcanonical_types_grothendieck_topology
- \+ *lemma* types_grothendieck_topology_eq_canonical
- \+ *theorem* is_sheaf_yoneda'
- \+ *def* types_grothendieck_topology
- \+ *def* discrete_sieve
- \+ *def* discrete_presieve
- \+ *def* yoneda'
- \+ *def* eval



## [2020-12-12 07:16:56](https://github.com/leanprover-community/mathlib/commit/0344aee)
feat(ring_theory/*): various lemmas about quotients, localizations, and polynomials ([#5249](https://github.com/leanprover-community/mathlib/pull/5249))
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* quotient_map_comp_mk
- \+ *lemma* quotient_map_surjective

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* ring_hom.is_integral_elem_of_is_integral_elem_comp
- \+ *lemma* ring_hom.is_integral_tower_top_of_is_integral
- \+ *lemma* is_integral_quotient_map_iff

Modified src/ring_theory/jacobson.lean
- \+/\- *lemma* radical_eq_jacobson
- \+/\- *lemma* radical_eq_jacobson

Modified src/ring_theory/localization.lean
- \+ *lemma* localization_map_bijective_of_field
- \+ *lemma* map_injective_of_injective
- \+/\- *lemma* localization_algebra_injective
- \+/\- *lemma* localization_algebra_injective

Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* polynomial_not_is_field
- \+ *lemma* eq_zero_of_constant_mem_of_maximal



## [2020-12-12 07:16:53](https://github.com/leanprover-community/mathlib/commit/d032380)
feat(field_theory/normal): normal_of_alg_equiv ([#5225](https://github.com/leanprover-community/mathlib/pull/5225))
Proves that normal is preserved by an alg_equiv
#### Estimated changes
Modified src/field_theory/normal.lean
- \+ *lemma* normal.of_alg_equiv
- \+ *lemma* alg_equiv.transfer_normal



## [2020-12-12 04:38:13](https://github.com/leanprover-community/mathlib/commit/f51fe7b)
chore(data/fin): Improve docstrings, rename `coe_sub_nat`, add `nat_add_zero` ([#5290](https://github.com/leanprover-community/mathlib/pull/5290))
These are cherry-picked from the tuple PR, [#4406](https://github.com/leanprover-community/mathlib/pull/4406).
`coe_sub_nat` was previously named `sub_nat_coe`, but this didn't match `coe_nat_add` and `coe_add_nat`.
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* coe_sub_nat
- \+ *lemma* nat_add_zero
- \+/\- *def* sub_nat
- \+/\- *def* sub_nat



## [2020-12-12 01:48:20](https://github.com/leanprover-community/mathlib/commit/2609428)
chore(scripts): update nolints.txt ([#5328](https://github.com/leanprover-community/mathlib/pull/5328))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-12 01:48:18](https://github.com/leanprover-community/mathlib/commit/b02c529)
feat(category_theory/limits): strengthen simp lemma ([#5326](https://github.com/leanprover-community/mathlib/pull/5326))
Makes a simp lemma slightly stronger
#### Estimated changes
Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* limit.cone_π
- \+/\- *lemma* limit.cone_π



## [2020-12-12 01:48:17](https://github.com/leanprover-community/mathlib/commit/e7ca801)
feat(data/list/chain): induction up the chain ([#5325](https://github.com/leanprover-community/mathlib/pull/5325))
Slightly strengthen statements that were there before
#### Estimated changes
Modified src/category_theory/is_connected.lean

Modified src/data/list/chain.lean
- \+ *lemma* chain.induction_head



## [2020-12-12 01:48:13](https://github.com/leanprover-community/mathlib/commit/f0c8a15)
chore(algebra/ordered_ring): golf some proofs using `strict_mono_incr_on` ([#5323](https://github.com/leanprover-community/mathlib/pull/5323))
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* strict_mono_incr_on_mul_self
- \+/\- *lemma* mul_self_le_mul_self
- \+/\- *lemma* mul_self_le_mul_self



## [2020-12-12 01:48:10](https://github.com/leanprover-community/mathlib/commit/01746f8)
feat(outer_measure): define bounded_by ([#5314](https://github.com/leanprover-community/mathlib/pull/5314))
`bounded_by` wrapper around `of_function` that drops the condition that `m ∅ = 0`. 
Refactor `Inf_gen` to use `bounded_by`.
I am also planning to use `bounded_by` for finitary products of measures.
Also add some complete lattice lemmas
#### Estimated changes
Modified src/measure_theory/measure_space.lean

Modified src/measure_theory/outer_measure.lean
- \+ *lemma* bounded_by_caratheodory
- \+ *lemma* Inf_gen_def
- \+ *lemma* Inf_eq_bounded_by_Inf_gen
- \+ *lemma* supr_Inf_gen_nonempty
- \- *lemma* Inf_gen_empty
- \- *lemma* Inf_gen_nonempty1
- \- *lemma* Inf_gen_nonempty2
- \- *lemma* Inf_eq_of_function_Inf_gen
- \+ *theorem* bounded_by_le
- \+ *theorem* bounded_by_eq_of_function
- \+ *theorem* bounded_by_apply
- \+ *theorem* bounded_by_eq
- \+ *theorem* le_bounded_by
- \+ *theorem* le_bounded_by'
- \+ *def* bounded_by

Modified src/order/complete_lattice.lean
- \+ *lemma* supr_const_le
- \+ *lemma* le_infi_const
- \+ *theorem* le_bsupr_of_le
- \+ *theorem* binfi_le_of_le



## [2020-12-12 01:48:08](https://github.com/leanprover-community/mathlib/commit/3782acf)
feat(topology/algebra/*): Criterion to ensure topological monoids and groups ([#5284](https://github.com/leanprover-community/mathlib/pull/5284))
This is old stuff from the perfectoid project that was never PRed and is useful for the liquid tensor experiment.
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* prod_map_map_eq'

Modified src/topology/algebra/group.lean
- \+ *lemma* topological_group.of_nhds_aux
- \+ *lemma* topological_group.of_nhds_one'
- \+ *lemma* topological_group.of_nhds_one
- \+ *lemma* topological_group.of_comm_of_nhds_one

Modified src/topology/algebra/monoid.lean
- \+ *lemma* has_continuous_mul.of_nhds_one
- \+ *lemma* has_continuous_mul_of_comm_of_nhds_one



## [2020-12-11 22:54:52](https://github.com/leanprover-community/mathlib/commit/846ee3f)
feat(data/equiv): symm_symm_apply ([#5324](https://github.com/leanprover-community/mathlib/pull/5324))
A little dsimp lemma that's often helpful
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *theorem* symm_symm_apply



## [2020-12-11 20:26:08](https://github.com/leanprover-community/mathlib/commit/63e1ad4)
chore(group_theory/perm/basic): Add missing lemmas ([#5320](https://github.com/leanprover-community/mathlib/pull/5320))
These lemmas existed for left multiplication but not right multiplication
#### Estimated changes
Modified src/group_theory/perm/basic.lean
- \+ *lemma* mul_swap_mul_self
- \+ *lemma* mul_swap_involutive
- \+ *lemma* mul_swap_eq_iff

Modified src/linear_algebra/determinant.lean



## [2020-12-11 20:26:06](https://github.com/leanprover-community/mathlib/commit/90aa66b)
chore(algebra/big_operators/basic): Rename hypotheses for clarity ([#5318](https://github.com/leanprover-community/mathlib/pull/5318))
This makes them somewhat more consistent with `prod_bij`
#### Estimated changes
Modified src/algebra/big_operators/basic.lean



## [2020-12-11 16:44:08](https://github.com/leanprover-community/mathlib/commit/3a88a9e)
chore(data/subtype): Add coind_bijective and map_involutive ([#5319](https://github.com/leanprover-community/mathlib/pull/5319))
#### Estimated changes
Modified src/data/subtype.lean
- \+ *lemma* map_involutive
- \+ *theorem* coind_surjective
- \+ *theorem* coind_bijective



## [2020-12-11 16:44:06](https://github.com/leanprover-community/mathlib/commit/029b258)
chore(linear_algebra/tensor_product): Actually relax the requirements for add_comm_group ([#5315](https://github.com/leanprover-community/mathlib/pull/5315))
A previous commit ([#5305](https://github.com/leanprover-community/mathlib/pull/5305)) changed the definition to not need these, but forgot to actually change these.
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean



## [2020-12-11 16:44:04](https://github.com/leanprover-community/mathlib/commit/db712d5)
chore(*): simp lemmas for `tendsto`, `Ixx`, and `coe` ([#5296](https://github.com/leanprover-community/mathlib/pull/5296))
* For `(f : α → β) (l : filter β)`, simplify `tendsto (λ a : Ixx*, f x) at_top l`
  to `tendsto f _ l`, and similarly for `at_bot`.
* For `(f : α → Ixx*) (l : filter α)`, simplify
  `tendsto f l at_top` to `tendsto (λ x, (f x : β)) l _`, and
  similarly for `at_bot`.
Here `Ixx*` is one of the intervals `Ici a`, `Ioi a`, `Ioo a b` etc,
and `_` is a filter that depends on the choice of `Ixx` and
`at_top`/`at_bot`.
* Drop some “nontriviality” assumptions like `no_top_order` for lemmas
about `Ioi a`.
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+/\- *lemma* tendsto_exp_at_bot_nhds_within
- \+/\- *lemma* range_exp
- \+/\- *lemma* map_exp_at_bot
- \+/\- *lemma* comap_exp_nhds_within_Ioi_zero
- \+/\- *lemma* surj_on_log
- \+/\- *lemma* log_surjective
- \+/\- *lemma* range_log
- \+/\- *lemma* log_zero
- \+/\- *lemma* surj_on_log'
- \+/\- *lemma* tendsto_exp_at_bot_nhds_within
- \+/\- *lemma* range_exp
- \+/\- *lemma* map_exp_at_bot
- \+/\- *lemma* comap_exp_nhds_within_Ioi_zero
- \+/\- *lemma* surj_on_log
- \+/\- *lemma* log_surjective
- \+/\- *lemma* range_log
- \+/\- *lemma* log_zero
- \+/\- *lemma* surj_on_log'
- \+/\- *def* exp_order_iso
- \+/\- *def* exp_order_iso

Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* at_top_Ioi_eq
- \+/\- *lemma* at_bot_Iio_eq
- \+ *lemma* tendsto_Ioi_at_top
- \+ *lemma* tendsto_Iio_at_bot
- \+ *lemma* tendsto_Ici_at_top
- \+ *lemma* tendsto_Iic_at_bot
- \+ *lemma* tendsto_comp_coe_Ioi_at_top
- \+ *lemma* tendsto_comp_coe_Ici_at_top
- \+ *lemma* tendsto_comp_coe_Iio_at_bot
- \+ *lemma* tendsto_comp_coe_Iic_at_bot
- \+/\- *lemma* at_top_Ioi_eq
- \+/\- *lemma* at_bot_Iio_eq

Modified src/order/filter/basic.lean
- \+ *lemma* nontrivial_iff_nonempty

Modified src/order/rel_iso.lean
- \+ *lemma* range_eq
- \+ *lemma* range_eq

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* comap_coe_nhds_within_Iio_of_Ioo_subset
- \+/\- *lemma* comap_coe_nhds_within_Ioi_of_Ioo_subset
- \+/\- *lemma* map_coe_at_top_of_Ioo_subset
- \+/\- *lemma* map_coe_at_bot_of_Ioo_subset
- \+/\- *lemma* comap_coe_Ioo_nhds_within_Iio
- \+/\- *lemma* comap_coe_Ioo_nhds_within_Ioi
- \+/\- *lemma* comap_coe_Ioi_nhds_within_Ioi
- \+/\- *lemma* comap_coe_Iio_nhds_within_Iio
- \+/\- *lemma* map_coe_Ioi_at_bot
- \+/\- *lemma* map_coe_Iio_at_top
- \+ *lemma* tendsto_comp_coe_Ioo_at_top
- \+ *lemma* tendsto_comp_coe_Ioo_at_bot
- \+ *lemma* tendsto_comp_coe_Ioi_at_bot
- \+ *lemma* tendsto_comp_coe_Iio_at_top
- \+ *lemma* tendsto_Ioo_at_top
- \+ *lemma* tendsto_Ioo_at_bot
- \+ *lemma* tendsto_Ioi_at_bot
- \+ *lemma* tendsto_Iio_at_top
- \+/\- *lemma* comap_coe_nhds_within_Iio_of_Ioo_subset
- \+/\- *lemma* comap_coe_nhds_within_Ioi_of_Ioo_subset
- \+/\- *lemma* map_coe_at_top_of_Ioo_subset
- \+/\- *lemma* map_coe_at_bot_of_Ioo_subset
- \+/\- *lemma* comap_coe_Ioo_nhds_within_Ioi
- \+/\- *lemma* comap_coe_Ioo_nhds_within_Iio
- \+/\- *lemma* comap_coe_Ioi_nhds_within_Ioi
- \+/\- *lemma* comap_coe_Iio_nhds_within_Iio
- \+/\- *lemma* map_coe_Ioi_at_bot
- \+/\- *lemma* map_coe_Iio_at_top

Modified src/topology/instances/nnreal.lean



## [2020-12-11 13:45:51](https://github.com/leanprover-community/mathlib/commit/a372dfc)
chore(*): don't assume `sub_eq_add_neg` and `div_eq_mul_inv` are defeq ([#5302](https://github.com/leanprover-community/mathlib/pull/5302))
This PR prepares for a follow-up PR ([#5303](https://github.com/leanprover-community/mathlib/pull/5303)) that adds `div` and `sub` fields to (`add_`)`group`(`_with_zero`). That follow-up PR is intended to fix the following kind of diamonds:
Let `foo X` be a type with a `∀ X, has_div (foo X)` instance but no `∀ X, has_inv (foo X)`, e.g. when `foo X` is a `euclidean_domain`. Suppose we also have an instance `∀ X [cromulent X], group_with_zero (foo X)`. Then the `(/)` coming from `group_with_zero_has_div` cannot be defeq to the `(/)` coming from `foo.has_div`.
As a consequence of making the `has_div` instances defeq, we can no longer assume that `(div_eq_mul_inv a b : a / b = a * b⁻¹) = rfl` for all groups. This preparation PR should have changed all places in mathlib that assumed defeqness, to rewrite explicitly instead.
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60div.60.20as.20a.20field.20in.20.60group(_with_zero).60
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean

Modified src/algebra/big_operators/basic.lean

Modified src/algebra/big_operators/intervals.lean

Modified src/algebra/field.lean
- \+ *lemma* mul_one_div

Modified src/algebra/floor.lean

Modified src/algebra/group/basic.lean
- \+ *lemma* group.inv_eq_one_div
- \+ *lemma* group.mul_one_div
- \+ *lemma* div_left_injective
- \+ *lemma* div_right_injective
- \- *lemma* sub_right_injective
- \- *lemma* sub_left_injective
- \+/\- *theorem* neg_add'
- \+/\- *theorem* neg_add'

Modified src/algebra/group/defs.lean
- \+ *lemma* group.div_eq_mul_inv
- \+/\- *lemma* sub_eq_add_neg
- \+/\- *lemma* sub_eq_add_neg

Modified src/algebra/group/hom.lean
- \+/\- *theorem* map_sub
- \+/\- *theorem* map_sub

Modified src/algebra/group/pi.lean
- \+/\- *lemma* sub_apply
- \+/\- *lemma* sub_apply

Modified src/algebra/group/to_additive.lean

Modified src/algebra/group_power/basic.lean

Modified src/algebra/group_power/lemmas.lean

Modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* div_self
- \+/\- *lemma* div_one
- \+/\- *lemma* one_div
- \+/\- *lemma* zero_div
- \+/\- *lemma* div_eq_inv_mul
- \- *lemma* div_eq_mul_inv
- \+/\- *lemma* div_self
- \+/\- *lemma* div_one
- \+/\- *lemma* one_div
- \+/\- *lemma* zero_div
- \+/\- *lemma* div_eq_inv_mul

Modified src/algebra/group_with_zero/defs.lean
- \+ *lemma* div_eq_mul_inv

Modified src/algebra/group_with_zero/power.lean

Modified src/algebra/module/basic.lean

Modified src/algebra/ordered_group.lean
- \+/\- *lemma* sub_le_sub_iff
- \+/\- *lemma* sub_le_sub_iff

Modified src/algebra/ring/basic.lean

Modified src/analysis/analytic/basic.lean

Modified src/analysis/asymptotics.lean

Modified src/analysis/calculus/deriv.lean

Modified src/analysis/calculus/fderiv.lean

Modified src/analysis/calculus/tangent_cone.lean

Modified src/analysis/calculus/times_cont_diff.lean

Modified src/analysis/convex/cone.lean

Modified src/analysis/hofer.lean

Modified src/analysis/normed_space/basic.lean

Modified src/analysis/normed_space/bounded_linear_maps.lean

Modified src/analysis/normed_space/enorm.lean

Modified src/analysis/normed_space/mazur_ulam.lean

Modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* continuous_multilinear_curry_right_equiv_apply'
- \+ *lemma* continuous_multilinear_curry_right_equiv_symm_apply'
- \+ *def* continuous_multilinear_curry_right_equiv'

Modified src/analysis/special_functions/pow.lean

Modified src/analysis/special_functions/trigonometric.lean
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_sub

Modified src/data/complex/exponential.lean

Modified src/data/fintype/card.lean

Modified src/data/int/cast.lean

Modified src/data/list/basic.lean

Modified src/data/matrix/basic.lean
- \+/\- *theorem* zero_apply
- \+/\- *theorem* neg_apply
- \+/\- *theorem* add_apply
- \+ *theorem* sub_apply
- \+/\- *theorem* zero_apply
- \+/\- *theorem* neg_apply
- \+/\- *theorem* add_apply

Modified src/data/mv_polynomial/comm_ring.lean

Modified src/data/num/lemmas.lean

Modified src/data/padics/hensel.lean

Modified src/data/polynomial/degree/definitions.lean

Modified src/data/polynomial/div.lean

Modified src/data/polynomial/monic.lean
- \+ *lemma* monic_sub_of_left
- \+ *lemma* monic_sub_of_right

Modified src/data/rat/basic.lean

Modified src/data/rat/cast.lean

Modified src/data/rat/order.lean

Modified src/data/real/cau_seq.lean

Modified src/data/real/cau_seq_completion.lean

Modified src/data/real/hyperreal.lean

Modified src/data/real/irrational.lean

Modified src/deprecated/group.lean

Modified src/deprecated/subgroup.lean
- \+/\- *theorem* is_add_subgroup.sub_mem
- \+/\- *theorem* is_add_subgroup.sub_mem

Modified src/dynamics/circle/rotation_number/translation_number.lean

Modified src/field_theory/separable.lean

Modified src/linear_algebra/affine_space/affine_subspace.lean

Modified src/linear_algebra/eigenspace.lean

Modified src/linear_algebra/finite_dimensional.lean

Modified src/linear_algebra/quadratic_form.lean

Modified src/linear_algebra/sesquilinear_form.lean

Modified src/measure_theory/ae_eq_fun.lean

Modified src/measure_theory/bochner_integration.lean

Modified src/measure_theory/borel_space.lean

Modified src/measure_theory/interval_integral.lean

Modified src/measure_theory/l1_space.lean

Modified src/order/filter/basic.lean

Modified src/order/filter/extr.lean

Modified src/ring_theory/free_comm_ring.lean

Modified src/ring_theory/ideal/basic.lean

Modified src/ring_theory/integral_closure.lean

Modified src/ring_theory/localization.lean

Modified src/ring_theory/power_basis.lean

Modified src/tactic/abel.lean

Modified src/tactic/monotonicity/interactive.lean

Modified src/tactic/norm_num.lean

Modified src/tactic/ring.lean
- \+/\- *theorem* add_neg_eq_sub
- \+/\- *theorem* add_neg_eq_sub

Modified src/tactic/ring_exp.lean
- \+/\- *lemma* sub_pf
- \+/\- *lemma* div_pf
- \+/\- *lemma* sub_pf
- \+/\- *lemma* div_pf

Modified src/topology/algebra/group.lean
- \+ *lemma* is_open_map_div_right
- \+ *lemma* is_closed_map_div_right

Modified src/topology/algebra/group_with_zero.lean

Modified src/topology/algebra/ordered.lean

Modified src/topology/algebra/uniform_group.lean

Modified src/topology/metric_space/gromov_hausdorff_realized.lean

Modified src/topology/metric_space/pi_Lp.lean



## [2020-12-11 12:35:50](https://github.com/leanprover-community/mathlib/commit/d2ae4e2)
feat(ring_theory/witt_vector): truncated Witt vectors, definition and ring structure ([#5162](https://github.com/leanprover-community/mathlib/pull/5162))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Created src/ring_theory/witt_vector/truncated.lean
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* coeff_mk
- \+ *lemma* mk_coeff
- \+ *lemma* coeff_out
- \+ *lemma* out_injective
- \+ *lemma* coeff_truncate_fun
- \+ *lemma* out_truncate_fun
- \+ *lemma* truncate_fun_out
- \+ *lemma* coeff_zero
- \+ *lemma* truncate_fun_surjective
- \+ *lemma* truncate_fun_zero
- \+ *lemma* truncate_fun_one
- \+ *lemma* truncate_fun_add
- \+ *lemma* truncate_fun_mul
- \+ *lemma* truncate_fun_neg
- \+ *def* truncated_witt_vector
- \+ *def* mk
- \+ *def* coeff
- \+ *def* out
- \+ *def* truncate_fun



## [2020-12-11 10:57:57](https://github.com/leanprover-community/mathlib/commit/6288eed)
feat(linear_algebra/alternating): Add alternatization of multilinear_map ([#5187](https://github.com/leanprover-community/mathlib/pull/5187))
This adds:
* `def multilinear_map.alternatize`
* `lemma alternating_map.to_multilinear_map_alternize`
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *lemma* alternatization_apply
- \+ *lemma* to_multilinear_map_alternization
- \+ *def* alternatization



## [2020-12-11 01:46:47](https://github.com/leanprover-community/mathlib/commit/dbdba55)
chore(scripts): update nolints.txt ([#5313](https://github.com/leanprover-community/mathlib/pull/5313))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-11 01:46:45](https://github.com/leanprover-community/mathlib/commit/8817c3e)
chore(linear_algebra/tensor_product): Relax the ring requirement to semiring for the group instance ([#5305](https://github.com/leanprover-community/mathlib/pull/5305))
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean
- \+/\- *lemma* neg_tmul
- \+/\- *lemma* neg_tmul
- \+/\- *theorem* map_neg₂
- \+ *theorem* neg.aux_of
- \+/\- *theorem* map_neg₂
- \+ *def* neg.aux



## [2020-12-11 01:46:44](https://github.com/leanprover-community/mathlib/commit/9e550f2)
feat(topology/separation): finite t1 spaces are discrete ([#5298](https://github.com/leanprover-community/mathlib/pull/5298))
These lemmas should simplify the arguments of [#4301](https://github.com/leanprover-community/mathlib/pull/4301)
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/discrete_topology/near/218932564 
<!--
put comments you want to keep out of the PR commit here.
If this PR depends on other PRs, please list them below this comment,
using the following format:
- [ ] depends on: #abc [optional extra text]
- [ ] depends on: #xyz [optional extra text]
-->
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* subset_singleton_iff

Modified src/topology/metric_space/basic.lean
- \+ *lemma* is_open_singleton_iff

Modified src/topology/order.lean
- \+ *lemma* forall_open_iff_discrete
- \+ *lemma* singletons_open_iff_discrete

Modified src/topology/separation.lean
- \+ *lemma* discrete_of_t1_of_finite



## [2020-12-11 01:46:41](https://github.com/leanprover-community/mathlib/commit/2c0b43d)
feat(combinatorics/simple_graph/degree_sum): degree-sum formula and handshake lemma ([#5263](https://github.com/leanprover-community/mathlib/pull/5263))
Adds the theorem that the sum of the degrees of the vertices of a simple graph is twice the number of edges.  Also adds corollaries like the handshake lemma, which is that the number of odd-degree vertices is even.
The corollary `exists_ne_odd_degree_if_exists_odd` is in anticipation of Sperner's lemma.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* edge_mem_other_incident_set

Created src/combinatorics/simple_graph/degree_sum.lean
- \+ *lemma* dart.edge_mem
- \+ *lemma* dart.rev_edge
- \+ *lemma* dart.rev_rev
- \+ *lemma* dart.rev_involutive
- \+ *lemma* dart.rev_ne
- \+ *lemma* dart_edge_eq_iff
- \+ *lemma* dart_of_neighbor_set_injective
- \+ *lemma* dart_fst_fiber
- \+ *lemma* dart_fst_fiber_card_eq_degree
- \+ *lemma* dart_card_eq_sum_degrees
- \+ *lemma* dart.edge_fiber
- \+ *lemma* dart_edge_fiber_card
- \+ *lemma* dart_card_eq_twice_card_edges
- \+ *lemma* odd_card_odd_degree_vertices_ne
- \+ *lemma* exists_ne_odd_degree_of_exists_odd_degree
- \+ *theorem* sum_degrees_eq_twice_card_edges
- \+ *theorem* even_card_odd_degree_vertices
- \+ *def* dart.edge
- \+ *def* dart.rev
- \+ *def* dart_of_neighbor_set

Modified src/data/sym2.lean

Created src/data/zmod/parity.lean
- \+ *lemma* eq_zero_iff_even
- \+ *lemma* eq_one_iff_odd
- \+ *lemma* ne_zero_iff_odd



## [2020-12-10 23:19:05](https://github.com/leanprover-community/mathlib/commit/918d5a9)
chore(data/finsupp/basic): redefine `finsupp.filter` ([#5310](https://github.com/leanprover-community/mathlib/pull/5310))
Also use lemmas about `indicator_function` and `function.update` to
golf some proofs about `finsupp.single`.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* fun_support_eq
- \+ *lemma* coe_fn_injective
- \+/\- *lemma* ext
- \+/\- *lemma* single_apply
- \+ *lemma* single_eq_indicator
- \+ *lemma* single_eq_update
- \+ *lemma* single_apply_eq_zero
- \+ *lemma* coe_add
- \+/\- *lemma* add_apply
- \+ *lemma* filter_apply
- \+ *lemma* filter_eq_indicator
- \+/\- *lemma* support_filter
- \+/\- *lemma* filter_add
- \+ *lemma* filter_eq_sum
- \- *lemma* injective_coe_fn
- \+/\- *lemma* ext
- \+/\- *lemma* single_apply
- \+/\- *lemma* add_apply
- \+/\- *lemma* support_filter
- \+/\- *lemma* filter_add
- \+ *def* filter_add_hom

Modified src/data/polynomial/degree/trailing_degree.lean



## [2020-12-10 23:19:03](https://github.com/leanprover-community/mathlib/commit/c295873)
feat(algebra/module/basic): {nat,int}_smul_apply ([#5308](https://github.com/leanprover-community/mathlib/pull/5308))
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *lemma* map_int_module_smul
- \+ *lemma* map_int_cast_smul
- \+ *lemma* map_nat_cast_smul
- \+ *lemma* map_rat_cast_smul
- \+ *lemma* map_rat_module_smul
- \+ *lemma* nat_smul_apply
- \+ *lemma* int_smul_apply
- \- *lemma* add_monoid_hom.map_int_module_smul
- \- *lemma* add_monoid_hom.map_int_cast_smul
- \- *lemma* add_monoid_hom.map_nat_cast_smul
- \- *lemma* add_monoid_hom.map_rat_cast_smul
- \- *lemma* add_monoid_hom.map_rat_module_smul



## [2020-12-10 21:44:19](https://github.com/leanprover-community/mathlib/commit/c9793b5)
chore(data/mv_polynomial): delete stray comments ([#5312](https://github.com/leanprover-community/mathlib/pull/5312))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean



## [2020-12-10 21:44:16](https://github.com/leanprover-community/mathlib/commit/f72734a)
chore(data/complex/exponential): add `inv_one_add_tan_sq` etc ([#5299](https://github.com/leanprover-community/mathlib/pull/5299))
* mark `cos_sq_add_sin_sq` and `sin_sq_add_cos_sq` as `@[simp]`;
* add lemmas representing `sin x` and `cos x` as functions of `tan x`.
#### Estimated changes
Modified src/data/complex/exponential.lean
- \+ *lemma* tan_mul_cos
- \+/\- *lemma* sin_sq_add_cos_sq
- \+ *lemma* cos_sq_add_sin_sq
- \+ *lemma* inv_one_add_tan_sq
- \+ *lemma* tan_sq_div_one_add_tan_sq
- \+ *lemma* tan_mul_cos
- \+/\- *lemma* sin_sq_add_cos_sq
- \+ *lemma* cos_sq_add_sin_sq
- \+ *lemma* inv_one_add_tan_sq
- \+ *lemma* tan_sq_div_one_add_tan_sq
- \+ *lemma* inv_sqrt_one_add_tan_sq
- \+ *lemma* tan_div_sqrt_one_add_tan_sq
- \+/\- *lemma* sin_sq_add_cos_sq
- \+/\- *lemma* sin_sq_add_cos_sq

Modified test/differentiable.lean



## [2020-12-10 21:44:14](https://github.com/leanprover-community/mathlib/commit/32b2e30)
feat(category_theory/monad): special coequalizers for a monad ([#5239](https://github.com/leanprover-community/mathlib/pull/5239))
Two important coequalizer diagrams related to a monad
#### Estimated changes
Created src/category_theory/monad/coequalizer.lean
- \+ *lemma* coequalizer.condition
- \+ *def* coequalizer.top_map
- \+ *def* coequalizer.bottom_map
- \+ *def* coequalizer.π
- \+ *def* beck_algebra_cofork
- \+ *def* beck_algebra_coequalizer
- \+ *def* beck_split_coequalizer
- \+ *def* beck_cofork
- \+ *def* beck_coequalizer



## [2020-12-10 18:39:41](https://github.com/leanprover-community/mathlib/commit/4e8486b)
feat(algebra/group/hom): add_monoid_hom.sub_apply ([#5307](https://github.com/leanprover-community/mathlib/pull/5307))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* sub_apply



## [2020-12-10 18:39:39](https://github.com/leanprover-community/mathlib/commit/be6c37c)
feat(algebra/big_operators/finsupp): rename variables, and move to top of file ([#5306](https://github.com/leanprover-community/mathlib/pull/5306))
#### Estimated changes
Modified src/algebra/big_operators/finsupp.lean



## [2020-12-10 17:02:36](https://github.com/leanprover-community/mathlib/commit/f3c9d20)
chore(linear_algebra/determinant): Golf a proof ([#5309](https://github.com/leanprover-community/mathlib/pull/5309))
#### Estimated changes
Modified src/linear_algebra/determinant.lean



## [2020-12-10 17:02:33](https://github.com/leanprover-community/mathlib/commit/cdb1398)
feat(category_theory/limits): any functor preserves split coequalizers ([#5246](https://github.com/leanprover-community/mathlib/pull/5246))
Once [#5230](https://github.com/leanprover-community/mathlib/pull/5230) merges, the only diff in this PR should be in `src/category_theory/limits/preserves/shapes/equalizers.lean`
#### Estimated changes
Modified src/category_theory/limits/preserves/shapes/equalizers.lean



## [2020-12-10 13:59:01](https://github.com/leanprover-community/mathlib/commit/12d097e)
feat(category_theory/sites/sieves): change presieve operation defs ([#5295](https://github.com/leanprover-community/mathlib/pull/5295))
change the definitions of operations on presieves to avoid `eq_to_hom` and use inductive types instead, which makes proofs a lot nicer
#### Estimated changes
Modified src/category_theory/sites/pretopology.lean
- \- *def* pullback_arrows

Modified src/category_theory/sites/sieves.lean
- \+/\- *lemma* singleton_self
- \+/\- *lemma* singleton_self
- \- *def* singleton

Modified src/category_theory/sites/spaces.lean



## [2020-12-10 13:58:58](https://github.com/leanprover-community/mathlib/commit/3f42fb4)
feat(group_theory/perm/sign): Add sign_sum_congr ([#5266](https://github.com/leanprover-community/mathlib/pull/5266))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* sum_congr_swap_refl
- \+ *lemma* sum_congr_refl_swap

Modified src/group_theory/perm/basic.lean
- \+ *lemma* sum_congr_swap_one
- \+ *lemma* sum_congr_one_swap

Modified src/group_theory/perm/sign.lean
- \+ *lemma* sign_sum_congr



## [2020-12-10 13:58:56](https://github.com/leanprover-community/mathlib/commit/90755c3)
refactor(order/filter/ultrafilter): drop `filter.is_ultrafilter` ([#5264](https://github.com/leanprover-community/mathlib/pull/5264))
Use bundled `ultrafilter`s instead.
#### Estimated changes
Modified src/data/real/hyperreal.lean
- \+/\- *lemma* coe_lt_coe
- \+/\- *lemma* coe_abs
- \+/\- *lemma* coe_max
- \+/\- *lemma* coe_min
- \+/\- *lemma* coe_lt_coe
- \+/\- *lemma* coe_abs
- \+/\- *lemma* coe_max
- \+/\- *lemma* coe_min
- \+/\- *def* hyperreal
- \+/\- *def* hyperreal

Modified src/data/set/basic.lean
- \+ *lemma* preimage_coe_eq_empty
- \+ *lemma* preimage_coe_compl
- \+ *lemma* preimage_coe_compl'

Modified src/order/filter/basic.lean
- \+ *lemma* empty_nmem_sets
- \+ *lemma* compl_not_mem_sets
- \+/\- *lemma* principal_ne_bot_iff
- \+ *lemma* comap_ne_bot_iff_frequently
- \+ *lemma* comap_ne_bot_iff_compl_range
- \+/\- *lemma* principal_ne_bot_iff

Modified src/order/filter/filter_product.lean
- \+/\- *lemma* const_div
- \+/\- *lemma* coe_lt
- \+/\- *lemma* coe_pos
- \+/\- *lemma* const_lt
- \+/\- *lemma* lt_def
- \+/\- *lemma* max_def
- \+/\- *lemma* min_def
- \+/\- *lemma* abs_def
- \+/\- *lemma* const_max
- \+/\- *lemma* const_min
- \+/\- *lemma* const_abs
- \+/\- *lemma* const_div
- \+/\- *lemma* coe_lt
- \+/\- *lemma* coe_pos
- \+/\- *lemma* const_lt
- \+/\- *lemma* lt_def
- \- *lemma* le_def
- \+/\- *lemma* max_def
- \+/\- *lemma* min_def
- \+/\- *lemma* abs_def
- \+/\- *lemma* const_max
- \+/\- *lemma* const_min
- \+/\- *lemma* const_abs

Modified src/order/filter/germ.lean
- \+ *lemma* le_def

Modified src/order/filter/ultrafilter.lean
- \+ *lemma* unique
- \+ *lemma* mem_coe
- \+ *lemma* coe_injective
- \+ *lemma* coe_le_coe
- \+ *lemma* coe_inj
- \+ *lemma* ext
- \+ *lemma* le_of_inf_ne_bot
- \+ *lemma* le_of_inf_ne_bot'
- \+ *lemma* compl_not_mem_iff
- \+ *lemma* frequently_iff_eventually
- \+ *lemma* compl_mem_iff_not_mem
- \+ *lemma* nonempty_of_mem
- \+ *lemma* ne_empty_of_mem
- \+ *lemma* empty_not_mem
- \+ *lemma* mem_or_compl_mem
- \+ *lemma* eventually_or
- \+ *lemma* union_mem_iff
- \+ *lemma* eventually_not
- \+ *lemma* eventually_imp
- \+ *lemma* finite_sUnion_mem_iff
- \+ *lemma* finite_bUnion_mem_iff
- \+ *lemma* coe_map
- \+ *lemma* mem_map
- \+ *lemma* mem_pure_sets
- \+ *lemma* exists_le
- \+ *lemma* of_le
- \+ *lemma* of_coe
- \+/\- *lemma* exists_ultrafilter_of_finite_inter_nonempty
- \+/\- *lemma* mem_iff_ultrafilter
- \+/\- *lemma* le_iff_ultrafilter
- \+ *lemma* supr_ultrafilter_le_eq
- \+/\- *lemma* exists_ultrafilter_iff
- \+ *lemma* forall_ne_bot_le_iff
- \+/\- *lemma* hyperfilter_le_cofinite
- \+/\- *lemma* bot_ne_hyperfilter
- \- *lemma* is_ultrafilter.unique
- \- *lemma* le_of_ultrafilter
- \- *lemma* ultrafilter_iff_compl_mem_iff_not_mem
- \- *lemma* ultrafilter_iff_compl_mem_iff_not_mem'
- \- *lemma* nonempty_of_mem_ultrafilter
- \- *lemma* ne_empty_of_mem_ultrafilter
- \- *lemma* mem_or_compl_mem_of_ultrafilter
- \- *lemma* mem_or_mem_of_ultrafilter
- \- *lemma* is_ultrafilter.em
- \- *lemma* is_ultrafilter.eventually_or
- \- *lemma* is_ultrafilter.eventually_not
- \- *lemma* is_ultrafilter.eventually_imp
- \- *lemma* mem_of_finite_sUnion_ultrafilter
- \- *lemma* mem_of_finite_Union_ultrafilter
- \- *lemma* ultrafilter_map
- \- *lemma* ultrafilter_pure
- \- *lemma* ultrafilter_bind
- \- *lemma* exists_ultrafilter
- \+/\- *lemma* exists_ultrafilter_of_finite_inter_nonempty
- \- *lemma* ultrafilter_of_spec
- \- *lemma* ultrafilter_of_le
- \- *lemma* ultrafilter_ultrafilter_of
- \- *lemma* ultrafilter_ultrafilter_of'
- \- *lemma* ultrafilter_of_ultrafilter
- \- *lemma* sup_of_ultrafilters
- \+/\- *lemma* le_iff_ultrafilter
- \+/\- *lemma* mem_iff_ultrafilter
- \+/\- *lemma* hyperfilter_le_cofinite
- \- *lemma* is_ultrafilter_hyperfilter
- \- *lemma* hyperfilter_ne_bot
- \+/\- *lemma* bot_ne_hyperfilter
- \- *lemma* ultrafilter.eq_iff_val_le_val
- \+/\- *lemma* exists_ultrafilter_iff
- \+/\- *theorem* nmem_hyperfilter_of_finite
- \+/\- *theorem* compl_mem_hyperfilter_of_finite
- \+/\- *theorem* mem_hyperfilter_of_finite_compl
- \+/\- *theorem* nmem_hyperfilter_of_finite
- \+/\- *theorem* compl_mem_hyperfilter_of_finite
- \+/\- *theorem* mem_hyperfilter_of_finite_compl
- \+ *def* of_compl_not_mem_iff
- \+ *def* map
- \+ *def* comap
- \+ *def* bind
- \- *def* is_ultrafilter
- \- *def* ultrafilter
- \- *def* ultrafilter.map
- \- *def* ultrafilter.pure
- \- *def* ultrafilter.bind
- \- *def* ultrafilter.comap

Modified src/topology/basic.lean
- \+ *lemma* ultrafilter.cluster_pt_iff
- \+/\- *lemma* continuous_at_iff_ultrafilter
- \+/\- *lemma* continuous_at_iff_ultrafilter
- \+ *def* ultrafilter.Lim
- \- *def* filter.ultrafilter.Lim

Modified src/topology/category/Compactum.lean

Modified src/topology/separation.lean
- \+ *lemma* ultrafilter.Lim_eq_iff_le_nhds
- \- *lemma* is_ultrafilter.Lim_eq_iff_le_nhds

Modified src/topology/stone_cech.lean
- \+/\- *lemma* ultrafilter_comap_pure_nhds
- \+/\- *lemma* convergent_eqv_pure
- \+/\- *lemma* ultrafilter_comap_pure_nhds
- \+/\- *lemma* convergent_eqv_pure

Modified src/topology/subset_properties.lean
- \+ *lemma* ultrafilter.le_nhds_Lim
- \- *lemma* is_ultrafilter.le_nhds_Lim

Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* ultrafilter.cauchy_of_totally_bounded
- \- *lemma* cauchy_of_totally_bounded_of_ultrafilter



## [2020-12-10 13:58:54](https://github.com/leanprover-community/mathlib/commit/2bf0c2e)
feat(group_theory/group_action/sub_mul_action): add a has_zero instance ([#5216](https://github.com/leanprover-community/mathlib/pull/5216))
#### Estimated changes
Modified src/group_theory/group_action/sub_mul_action.lean
- \+ *lemma* zero_mem



## [2020-12-10 10:51:03](https://github.com/leanprover-community/mathlib/commit/702b1e8)
refactor(data/finsupp/basic): merge `finsupp.of_multiset` and `multiset.to_finsupp` ([#5237](https://github.com/leanprover-community/mathlib/pull/5237))
* redefine `finsupp.to_multiset` as an `add_equiv`;
* drop `finsupp.equiv_multiset` and `finsupp.of_multiset`;
* define `multiset.to_finsupp` as `finsupp.to_multiset.symm`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* to_finset_sum_count_smul_eq
- \+/\- *lemma* to_finset_sum_count_smul_eq

Modified src/data/finsupp/basic.lean
- \+/\- *lemma* mul_equiv.map_finsupp_prod
- \+/\- *lemma* monoid_hom.map_finsupp_prod
- \+/\- *lemma* ring_hom.map_finsupp_sum
- \+/\- *lemma* ring_hom.map_finsupp_prod
- \+ *lemma* to_multiset_apply
- \+/\- *lemma* to_multiset_single
- \+/\- *lemma* prod_to_multiset
- \+/\- *lemma* to_finset_to_multiset
- \+/\- *lemma* to_finsupp_zero
- \+/\- *lemma* to_finsupp_add
- \+/\- *lemma* to_finsupp_singleton
- \+ *lemma* to_finsupp_eq_iff
- \+ *lemma* finsupp.to_multiset_to_finsupp
- \+ *lemma* le_def
- \+ *lemma* coe_order_iso_multiset
- \+ *lemma* coe_order_iso_multiset_symm
- \+/\- *lemma* mem_antidiagonal_support
- \+ *lemma* to_finsuppstrict_mono
- \+/\- *lemma* to_multiset_single
- \+/\- *lemma* prod_to_multiset
- \+/\- *lemma* to_finset_to_multiset
- \- *lemma* of_multiset_apply
- \+/\- *lemma* mul_equiv.map_finsupp_prod
- \+/\- *lemma* monoid_hom.map_finsupp_prod
- \+/\- *lemma* ring_hom.map_finsupp_sum
- \+/\- *lemma* ring_hom.map_finsupp_prod
- \+/\- *lemma* to_finsupp_zero
- \+/\- *lemma* to_finsupp_add
- \+/\- *lemma* to_finsupp_singleton
- \- *lemma* to_multiset_to_finsupp
- \+/\- *lemma* mem_antidiagonal_support
- \+/\- *def* to_multiset
- \+/\- *def* to_finsupp
- \+ *def* order_iso_multiset
- \+/\- *def* to_multiset
- \- *def* of_multiset
- \- *def* equiv_multiset
- \+/\- *def* to_finsupp

Modified src/data/finsupp/lattice.lean
- \- *lemma* le_def
- \- *lemma* of_multiset_strict_mono
- \- *lemma* order_iso_multiset_apply
- \- *lemma* order_iso_multiset_symm_apply
- \- *def* order_iso_multiset

Modified src/logic/function/basic.lean
- \+ *lemma* id_def



## [2020-12-10 08:44:55](https://github.com/leanprover-community/mathlib/commit/ac669c7)
chore(category_theory/limits/preserves): cleanup ([#4163](https://github.com/leanprover-community/mathlib/pull/4163))
(edited to update).
This PR entirely re-does the construction of limits from products and equalizers in a shorter way. With the new preserves limits machinery this new construction also shows that a functor which preserves products and equalizers preserves all limits, which previously was *really* annoying to do
#### Estimated changes
Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean
- \+ *lemma* has_limit_of_equalizer_and_product
- \+ *def* build_limit
- \+ *def* build_is_limit
- \+ *def* preserves_limit_of_preserves_equalizers_and_product
- \+ *def* preserves_finite_limits_of_preserves_equalizers_and_finite_products
- \+ *def* preserves_limits_of_preserves_equalizers_and_products
- \- *def* diagram
- \- *def* cones_hom
- \- *def* cones_inv
- \- *def* cones_iso



## [2020-12-10 07:39:19](https://github.com/leanprover-community/mathlib/commit/e68d2d7)
feat(category_theory/sites): category of sheaves ([#5255](https://github.com/leanprover-community/mathlib/pull/5255))
Category of sheaves on a grothendieck topology
(cc: @kckennylau)
#### Estimated changes
Modified src/category_theory/sites/grothendieck.lean

Modified src/category_theory/sites/pretopology.lean

Modified src/category_theory/sites/sheaf.lean
- \+ *def* Sheaf
- \+ *def* Sheaf_to_presheaf



## [2020-12-10 01:25:50](https://github.com/leanprover-community/mathlib/commit/ba568a6)
chore(scripts): update nolints.txt ([#5297](https://github.com/leanprover-community/mathlib/pull/5297))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-09 19:09:52](https://github.com/leanprover-community/mathlib/commit/84c0132)
chore(data/indicator_function): a few more `simp` lemmas ([#5293](https://github.com/leanprover-community/mathlib/pull/5293))
* drop `indicator_of_support_subset` in favor of the new `indicator_eq_self`;
* add a few more lemmas: `indicator_apply_eq_self`,
 `indicator_apply_eq_zero`, `indicator_eq_zero`, `indicator_eq_zero'`
#### Estimated changes
Modified src/data/indicator_function.lean
- \+ *lemma* indicator_apply_eq_self
- \+ *lemma* indicator_eq_self
- \+ *lemma* indicator_apply_eq_zero
- \+ *lemma* indicator_eq_zero
- \+ *lemma* indicator_eq_zero'
- \+/\- *lemma* indicator_indicator
- \- *lemma* indicator_of_support_subset
- \+/\- *lemma* indicator_indicator

Modified src/data/set/function.lean
- \+ *lemma* piecewise_singleton

Modified src/measure_theory/interval_integral.lean

Modified src/measure_theory/set_integral.lean



## [2020-12-09 17:36:09](https://github.com/leanprover-community/mathlib/commit/bf25d26)
chore(data/set/intervals/proj_Icc): add `strict_mono_incr_on` ([#5292](https://github.com/leanprover-community/mathlib/pull/5292))
* rename `set.Icc_extend_monotone` to `monotone.Icc_extend`;
* add `set.strict_mono_incr_on_proj_Icc` and `strict_mono.strict_mono_incr_on_Icc_extend`.
#### Estimated changes
Modified src/data/set/intervals/proj_Icc.lean
- \+ *lemma* strict_mono_incr_on_proj_Icc
- \+ *lemma* monotone.Icc_extend
- \+ *lemma* strict_mono.strict_mono_incr_on_Icc_extend
- \- *lemma* Icc_extend_monotone



## [2020-12-09 17:36:06](https://github.com/leanprover-community/mathlib/commit/efe18d5)
feat(measure_theory/interval_integral): continuous implies interval_integrable ([#5288](https://github.com/leanprover-community/mathlib/pull/5288))
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* continuous_on.interval_integrable
- \+ *lemma* continuous.interval_integrable



## [2020-12-09 17:36:04](https://github.com/leanprover-community/mathlib/commit/e357a33)
chore(linear_algebra/multilinear): Add `linear_map.comp_multilinear_map_dom_dom_congr` ([#5270](https://github.com/leanprover-community/mathlib/pull/5270))
#### Estimated changes
Modified src/linear_algebra/multilinear.lean
- \+ *lemma* comp_multilinear_map_dom_dom_congr



## [2020-12-09 17:36:02](https://github.com/leanprover-community/mathlib/commit/698d6b7)
ci(.github/workflows/dependent-issues.yml): automation for "blocked-by-other-PR" label ([#5261](https://github.com/leanprover-community/mathlib/pull/5261))
When a PR or issue is updated, the [dependent-issues](https://github.com/z0al/dependent-issues) action will do the following on all PRs which are marked as dependent on it (with the text `- [ ] depends on: #blah` that we're already using):
- add / remove the "blocked-by-other-PR" label
- post / edit a comment with the current status of its dependencies (this is slightly redundant, given that we have another action which checks off the dependent PRs in the PR comments, but the extra notifications might be useful).
- it also adds a new status check which is pending (yellow) until all dependencies are closed.
#### Estimated changes
Created .github/workflows/dependent-issues.yml



## [2020-12-09 16:13:00](https://github.com/leanprover-community/mathlib/commit/a87f62b)
feat(category_theory/limits/preserves): preserving binary products ([#5061](https://github.com/leanprover-community/mathlib/pull/5061))
This moves and re-does my old file about preserving binary products to match the new API and framework for preservation of special shapes, and also cleans up some existing API. 
(I can split this up if necessary but they're all pretty minor changes, so hope this is okay!)
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean

Modified src/category_theory/limits/preserves/functor_category.lean

Created src/category_theory/limits/preserves/shapes/binary_products.lean
- \+ *lemma* preserves_pair.iso_hom
- \+ *def* is_limit_map_cone_binary_fan_equiv
- \+ *def* map_is_limit_of_preserves_of_is_limit
- \+ *def* is_limit_of_reflects_of_map_is_limit
- \+ *def* is_limit_of_has_binary_product_of_preserves_limit
- \+ *def* preserves_pair.of_iso_comparison
- \+ *def* preserves_pair.iso

Modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *def* map_pair
- \+/\- *def* diagram_iso_pair
- \+ *def* prod_is_prod
- \+ *def* coprod_is_coprod
- \+/\- *def* prod_comparison
- \+/\- *def* map_pair
- \+/\- *def* diagram_iso_pair
- \+/\- *def* prod_comparison

Deleted src/category_theory/limits/shapes/constructions/preserve_binary_products.lean
- \- *def* alternative_cone
- \- *def* alternative_cone_is_limit
- \- *def* preserves_binary_prod_of_prod_comparison_iso



## [2020-12-09 09:24:04](https://github.com/leanprover-community/mathlib/commit/d12a731)
chore(data/mv_polynomial): mark `mv_polynomial.ext` as `@[ext]` ([#5289](https://github.com/leanprover-community/mathlib/pull/5289))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext



## [2020-12-09 04:36:44](https://github.com/leanprover-community/mathlib/commit/1f309c5)
feat(analysis/special_functions): `real.log` is infinitely smooth away from zero ([#5116](https://github.com/leanprover-community/mathlib/pull/5116))
Also redefine it using `order_iso.to_homeomorph` and prove more lemmas about limits of `exp`/`log`.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_on_inv

Modified src/analysis/special_functions/exp_log.lean
- \+/\- *lemma* tendsto_exp_at_top
- \+/\- *lemma* tendsto_exp_neg_at_top_nhds_0
- \+/\- *lemma* tendsto_exp_nhds_0_nhds_1
- \+ *lemma* tendsto_exp_at_bot
- \+ *lemma* tendsto_exp_at_bot_nhds_within
- \+/\- *lemma* range_exp
- \+ *lemma* coe_exp_order_iso_apply
- \+ *lemma* coe_comp_exp_order_iso
- \+ *lemma* map_exp_at_top
- \+ *lemma* comap_exp_at_top
- \+ *lemma* tendsto_exp_comp_at_top
- \+ *lemma* tendsto_comp_exp_at_top
- \+ *lemma* map_exp_at_bot
- \+ *lemma* comap_exp_nhds_within_Ioi_zero
- \+ *lemma* tendsto_comp_exp_at_bot
- \+ *lemma* log_of_ne_zero
- \+ *lemma* log_of_pos
- \+ *lemma* surj_on_log
- \+ *lemma* surj_on_log'
- \+ *lemma* strict_mono_incr_on_log
- \+ *lemma* strict_mono_decr_on_log
- \+/\- *lemma* tendsto_log_at_top
- \+ *lemma* tendsto_log_nhds_within_zero
- \+ *lemma* continuous_on_log
- \+/\- *lemma* continuous_log'
- \+/\- *lemma* continuous_at_log
- \+ *lemma* continuous_at_log_iff
- \+ *lemma* differentiable_at_log
- \+ *lemma* differentiable_on_log
- \+ *lemma* differentiable_at_log_iff
- \+ *lemma* deriv_log
- \+/\- *lemma* deriv_log'
- \+ *lemma* times_cont_diff_on_log
- \+ *lemma* times_cont_diff_at_log
- \+ *lemma* filter.tendsto.log
- \+ *lemma* continuous.log
- \+ *lemma* continuous_at.log
- \+ *lemma* continuous_within_at.log
- \+ *lemma* continuous_on.log
- \+/\- *lemma* measurable.log
- \+ *lemma* deriv_within.log
- \+ *lemma* deriv.log
- \+ *lemma* has_fderiv_within_at.log
- \+ *lemma* has_fderiv_at.log
- \+ *lemma* fderiv_within.log
- \+ *lemma* fderiv.log
- \- *lemma* exists_exp_eq_of_pos
- \+/\- *lemma* range_exp
- \- *lemma* tendsto_log_one_zero
- \+/\- *lemma* continuous_log'
- \+/\- *lemma* continuous_at_log
- \- *lemma* continuous_log
- \+/\- *lemma* measurable.log
- \- *lemma* deriv_within_log'
- \+/\- *lemma* deriv_log'
- \+/\- *lemma* tendsto_exp_at_top
- \+/\- *lemma* tendsto_exp_neg_at_top_nhds_0
- \+/\- *lemma* tendsto_exp_nhds_0_nhds_1
- \+/\- *lemma* tendsto_log_at_top
- \+ *def* exp_order_iso

Modified src/data/complex/exponential.lean
- \+/\- *lemma* exp_lt_exp
- \+/\- *lemma* exp_le_exp
- \+ *lemma* exp_eq_exp
- \+/\- *lemma* exp_lt_exp
- \+/\- *lemma* exp_le_exp

Modified src/data/set/function.lean
- \+ *lemma* strict_mono.cod_restrict

Modified src/order/rel_iso.lean
- \+ *def* set_congr
- \+ *def* set.univ

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* nhds_within_Ici_self_ne_bot
- \+/\- *lemma* nhds_within_Iic_self_ne_bot
- \+/\- *lemma* intermediate_value_univ₂
- \+/\- *lemma* is_preconnected.intermediate_value₂
- \+/\- *lemma* is_preconnected.intermediate_value
- \+/\- *lemma* intermediate_value_univ
- \+/\- *lemma* mem_range_of_exists_le_of_exists_ge
- \+/\- *lemma* nhds_within_Ici_self_ne_bot
- \+/\- *lemma* nhds_within_Iic_self_ne_bot
- \+/\- *lemma* intermediate_value_univ₂
- \+/\- *lemma* is_preconnected.intermediate_value₂
- \+/\- *lemma* is_preconnected.intermediate_value
- \+/\- *lemma* intermediate_value_univ
- \+/\- *lemma* mem_range_of_exists_le_of_exists_ge

Modified src/topology/separation.lean
- \+ *lemma* is_open_compl_singleton



## [2020-12-09 01:42:58](https://github.com/leanprover-community/mathlib/commit/2032f7b)
chore(scripts): update nolints.txt ([#5287](https://github.com/leanprover-community/mathlib/pull/5287))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-09 01:42:56](https://github.com/leanprover-community/mathlib/commit/7ae1165)
chore(data/pi): Express `single` in terms of `function.update` ([#5283](https://github.com/leanprover-community/mathlib/pull/5283))
These were originally introduced in [#3513](https://github.com/leanprover-community/mathlib/pull/3513).
Perhaps `function.update` wasn't as well developed back then.
#### Estimated changes
Modified src/data/pi.lean



## [2020-12-08 22:41:41](https://github.com/leanprover-community/mathlib/commit/1e3447b)
chore(data/equiv/mul_add): Split out the group structure on automorphisms ([#5281](https://github.com/leanprover-community/mathlib/pull/5281))
This prevents `group_theory.perm.basic` being imported into lots of files that don't care about permutations.
The argument here is that `add_aut` is to `add_equiv` as `perm` is to `equiv`: `perm` gets its group structure in a separate file to where `equiv` is defined, so `add_aut`, `mul_aut`, and `ring_aut` should too.
This adds back imports of `group_theory.perm.basic` to downstream files that inherited them through `data.equiv.mul_add`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean

Modified src/data/equiv/mul_add.lean
- \- *lemma* coe_mul
- \- *lemma* coe_one
- \- *lemma* mul_def
- \- *lemma* one_def
- \- *lemma* inv_def
- \- *lemma* mul_apply
- \- *lemma* one_apply
- \- *lemma* apply_inv_self
- \- *lemma* inv_apply_self
- \- *lemma* conj_apply
- \- *lemma* conj_symm_apply
- \- *lemma* conj_inv_apply
- \- *lemma* coe_mul
- \- *lemma* coe_one
- \- *lemma* mul_def
- \- *lemma* one_def
- \- *lemma* inv_def
- \- *lemma* mul_apply
- \- *lemma* one_apply
- \- *lemma* apply_inv_self
- \- *lemma* inv_apply_self
- \- *def* mul_aut
- \- *def* to_perm
- \- *def* conj
- \- *def* to_perm

Created src/data/equiv/mul_add_aut.lean
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* mul_def
- \+ *lemma* one_def
- \+ *lemma* inv_def
- \+ *lemma* mul_apply
- \+ *lemma* one_apply
- \+ *lemma* apply_inv_self
- \+ *lemma* inv_apply_self
- \+ *lemma* conj_apply
- \+ *lemma* conj_symm_apply
- \+ *lemma* conj_inv_apply
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* mul_def
- \+ *lemma* one_def
- \+ *lemma* inv_def
- \+ *lemma* mul_apply
- \+ *lemma* one_apply
- \+ *lemma* apply_inv_self
- \+ *lemma* inv_apply_self
- \+ *def* mul_aut
- \+ *def* to_perm
- \+ *def* conj
- \+ *def* to_perm

Modified src/data/equiv/ring.lean
- \- *def* ring_aut
- \- *def* to_add_aut
- \- *def* to_mul_aut
- \- *def* to_perm

Created src/data/equiv/ring_aut.lean
- \+ *def* ring_aut
- \+ *def* to_add_aut
- \+ *def* to_mul_aut
- \+ *def* to_perm

Modified src/data/fintype/basic.lean

Modified src/group_theory/group_action/group.lean

Modified src/group_theory/semidirect_product.lean



## [2020-12-08 18:18:54](https://github.com/leanprover-community/mathlib/commit/4c9499f)
chore(algebra/group/pi): Split into multiple files ([#5280](https://github.com/leanprover-community/mathlib/pull/5280))
This allows files that appear before `ordered_group` to still use `pi.monoid` etc.
#### Estimated changes
Modified src/algebra/group/pi.lean
- \- *lemma* one_apply
- \- *lemma* mul_apply
- \- *lemma* inv_apply
- \- *lemma* div_apply

Modified src/algebra/module/ordered.lean

Created src/algebra/ordered_pi.lean

Modified src/data/pi.lean
- \+ *lemma* one_apply
- \+ *lemma* mul_apply
- \+ *lemma* inv_apply
- \+ *lemma* div_apply

Modified src/order/pilex.lean



## [2020-12-08 16:34:05](https://github.com/leanprover-community/mathlib/commit/b5ab2f7)
feat(topology/algebra/ordered): add lemmas about `map coe at_top/at_bot` ([#5238](https://github.com/leanprover-community/mathlib/pull/5238))
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+ *lemma* comap_coe_nhds_within_Iio_of_Ioo_subset
- \+ *lemma* comap_coe_nhds_within_Ioi_of_Ioo_subset
- \+ *lemma* map_coe_at_top_of_Ioo_subset
- \+ *lemma* map_coe_at_bot_of_Ioo_subset
- \+ *lemma* comap_coe_Ioo_nhds_within_Ioi
- \+ *lemma* comap_coe_Ioo_nhds_within_Iio
- \+ *lemma* comap_coe_Ioi_nhds_within_Ioi
- \+ *lemma* comap_coe_Iio_nhds_within_Iio
- \+ *lemma* map_coe_Ioo_at_top
- \+ *lemma* map_coe_Ioo_at_bot
- \+ *lemma* map_coe_Ioi_at_bot
- \+ *lemma* map_coe_Iio_at_top
- \- *lemma* Ioo_at_top_eq_nhds_within
- \- *lemma* Ioo_at_bot_eq_nhds_within



## [2020-12-08 15:28:08](https://github.com/leanprover-community/mathlib/commit/7f5a5dd)
feat(category_theory/limits): split coequalizers ([#5230](https://github.com/leanprover-community/mathlib/pull/5230))
Define what it means for a triple of morphisms `f g : X ⟶ Y`, `π : Y ⟶ Z` to be a split coequalizer, and show that every split coequalizer is a coequalizer and absolute.
Define split pairs and `G`-split pairs.
These definitions and constructions are useful in particular for the monadicity theorems.
#### Estimated changes
Created src/category_theory/limits/shapes/split_coequalizer.lean
- \+ *def* is_split_coequalizer.map
- \+ *def* is_split_coequalizer.as_cofork
- \+ *def* is_split_coequalizer.is_coequalizer



## [2020-12-08 13:47:48](https://github.com/leanprover-community/mathlib/commit/64ddb12)
feat(analysis/mean_inequalities): add Hölder's inequality for the Lebesgue integral of ennreal and nnreal functions ([#5267](https://github.com/leanprover-community/mathlib/pull/5267))
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *lemma* lintegral_mul_le_one_of_lintegral_rpow_eq_one
- \+ *lemma* fun_eq_fun_mul_inv_snorm_mul_snorm
- \+ *lemma* fun_mul_inv_snorm_rpow
- \+ *lemma* lintegral_rpow_fun_mul_inv_snorm_eq_one
- \+ *lemma* lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top
- \+ *lemma* ae_eq_zero_of_lintegral_rpow_eq_zero
- \+ *lemma* lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero
- \+ *lemma* lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top
- \+ *theorem* lintegral_mul_le_Lp_mul_Lq
- \+ *theorem* nnreal.lintegral_mul_le_Lp_mul_Lq
- \+ *def* fun_mul_inv_snorm

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* of_real_rpow_of_nonneg
- \+ *lemma* inv_rpow_of_pos

Modified src/data/real/conjugate_exponents.lean
- \+ *lemma* inv_add_inv_conj_ennreal

Modified src/data/real/ennreal.lean
- \+ *lemma* of_real_inv_of_pos
- \+ *lemma* of_real_div_of_pos

Modified src/measure_theory/integration.lean
- \+ *lemma* lintegral_zero_fun



## [2020-12-08 10:43:05](https://github.com/leanprover-community/mathlib/commit/3996bd4)
chore(logic/basic): add a few `simp` lemmas ([#5278](https://github.com/leanprover-community/mathlib/pull/5278))
Also add `fintype.prod_eq_single`.
#### Estimated changes
Modified archive/arithcc.lean

Modified src/data/fintype/card.lean
- \+ *lemma* prod_eq_single

Modified src/data/matrix/basic.lean

Modified src/logic/basic.lean
- \+ *lemma* ite_eq_left_iff
- \+ *lemma* ite_eq_right_iff
- \+ *theorem* imp_not_self
- \+ *theorem* decidable.not_imp_self
- \+ *theorem* not_imp_self

Modified src/ring_theory/power_series.lean



## [2020-12-08 10:43:02](https://github.com/leanprover-community/mathlib/commit/d3bbaeb)
chore(combinatorics/composition): use `order_embedding` ([#5276](https://github.com/leanprover-community/mathlib/pull/5276))
* use `order_embedding` for `composition.boundary`
* use `order_embedding` for `composition.embedding`
* add `max_eq_right_iff` etc
* golf some proofs
#### Estimated changes
Modified src/algebra/order_functions.lean
- \+ *lemma* min_eq_left_iff
- \+ *lemma* min_eq_right_iff
- \+ *lemma* max_eq_left_iff
- \+ *lemma* max_eq_right_iff

Modified src/analysis/analytic/composition.lean

Modified src/combinatorics/composition.lean
- \+ *lemma* coe_embedding
- \+ *lemma* coe_inv_embedding
- \+/\- *lemma* ones_blocks
- \+/\- *lemma* single_length
- \+/\- *lemma* single_blocks
- \- *lemma* strict_mono_boundary
- \- *lemma* embedding_injective
- \+/\- *lemma* ones_blocks
- \+/\- *lemma* single_length
- \+/\- *lemma* single_blocks
- \+/\- *def* boundary
- \+/\- *def* embedding
- \+/\- *def* boundary
- \+/\- *def* embedding



## [2020-12-08 10:43:00](https://github.com/leanprover-community/mathlib/commit/51f5ca3)
chore(group_theory/perm): Add alternate formulation of (sum|sigma)_congr lemmas ([#5260](https://github.com/leanprover-community/mathlib/pull/5260))
These lemmas existed already for `equiv`, but not for `perm` or for `perm` via group structures.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *lemma* sum_congr_symm
- \+ *lemma* sum_congr_apply
- \+ *lemma* sum_congr_trans
- \+/\- *lemma* sum_congr_symm
- \+ *lemma* sum_congr_refl
- \+ *lemma* sigma_congr_right_trans
- \+ *lemma* sigma_congr_right_symm
- \+ *lemma* sigma_congr_right_refl
- \+/\- *lemma* sum_congr_symm
- \+ *def* sum_congr
- \+ *def* sigma_congr_right

Modified src/group_theory/perm/basic.lean
- \+ *lemma* sum_congr_mul
- \+ *lemma* sum_congr_inv
- \+ *lemma* sum_congr_one
- \+ *lemma* sigma_congr_right_mul
- \+ *lemma* sigma_congr_right_inv
- \+ *lemma* sigma_congr_right_one



## [2020-12-08 07:36:20](https://github.com/leanprover-community/mathlib/commit/ac6fc38)
chore(*): move/add lemmas about `disjoint` ([#5277](https://github.com/leanprover-community/mathlib/pull/5277))
* `set.disjoint_compl_left` and `set.disjoint_compl_right`:
  - generalize to any `boolean_algebra`,
  - move to `order/boolean_algebra`,
  - drop `set.` prefix,
  - make the argument implicit to follow the style of other lemmas in `order/boolean_algebra`
* add `set.disjoint_empty` and `set.empty_disjoint`
* add `disjoint_top` and `top_disjoint`, use in `set.disjoint_univ`and `set.univ_disjoint`.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *theorem* disjoint_empty
- \+ *theorem* empty_disjoint
- \- *theorem* disjoint_compl_left
- \- *theorem* disjoint_compl_right

Modified src/linear_algebra/basic.lean

Modified src/linear_algebra/finsupp.lean

Modified src/linear_algebra/matrix.lean

Modified src/measure_theory/measure_space.lean

Modified src/measure_theory/set_integral.lean

Modified src/order/boolean_algebra.lean
- \+ *theorem* disjoint_compl_right
- \+ *theorem* disjoint_compl_left

Modified src/order/bounded_lattice.lean
- \+/\- *theorem* disjoint_bot_left
- \+/\- *theorem* disjoint_bot_right
- \+ *theorem* disjoint_top
- \+ *theorem* top_disjoint
- \+/\- *theorem* disjoint_bot_left
- \+/\- *theorem* disjoint_bot_right

Modified src/ring_theory/localization.lean



## [2020-12-08 07:36:17](https://github.com/leanprover-community/mathlib/commit/ef377a9)
chore(data/list/sort): docs, add a few lemmas ([#5274](https://github.com/leanprover-community/mathlib/pull/5274))
 * Add a module docstring and section headers.
* Rename `list.eq_of_sorted_of_perm` to `list.eq_of_perm_of_sorted`;
  the new name reflects the order of arguments.
* Add a few lemmas.
#### Estimated changes
Modified src/data/list/sort.lean
- \+ *lemma* ordered_insert_eq_take_drop
- \+ *lemma* insertion_sort_cons_eq_take_drop
- \+ *lemma* sorted.insertion_sort_eq
- \+/\- *lemma* length_merge_sort
- \+/\- *lemma* length_merge_sort
- \+ *theorem* eq_of_perm_of_sorted
- \+/\- *theorem* perm_ordered_insert
- \+/\- *theorem* perm_insertion_sort
- \+ *theorem* sorted.ordered_insert
- \+/\- *theorem* sorted_insertion_sort
- \+/\- *theorem* perm_merge
- \+/\- *theorem* perm_merge_sort
- \+ *theorem* sorted.merge
- \+/\- *theorem* sorted_merge_sort
- \+/\- *theorem* merge_sort_eq_self
- \+ *theorem* merge_sort_eq_insertion_sort
- \- *theorem* eq_of_sorted_of_perm
- \+/\- *theorem* perm_ordered_insert
- \+/\- *theorem* perm_insertion_sort
- \- *theorem* sorted_ordered_insert
- \+/\- *theorem* sorted_insertion_sort
- \+/\- *theorem* perm_merge
- \+/\- *theorem* perm_merge_sort
- \- *theorem* sorted_merge
- \+/\- *theorem* sorted_merge_sort
- \+/\- *theorem* merge_sort_eq_self

Modified src/data/multiset/sort.lean



## [2020-12-08 07:36:15](https://github.com/leanprover-community/mathlib/commit/aec64b1)
feat(category_theory/monad): generalise algebra colimits ([#5234](https://github.com/leanprover-community/mathlib/pull/5234))
Assumption generalisations and universe generalisations
#### Estimated changes
Modified src/category_theory/monad/limits.lean
- \+ *def* monadic_creates_colimit_of_preserves_colimit

Modified src/topology/category/UniformSpace.lean



## [2020-12-08 07:36:13](https://github.com/leanprover-community/mathlib/commit/7360178)
feat(category_theory/closed/types): presheaf category is cartesian closed ([#4897](https://github.com/leanprover-community/mathlib/pull/4897))
#### Estimated changes
Created src/category_theory/closed/types.lean

Modified src/category_theory/limits/preserves/limits.lean



## [2020-12-08 05:05:55](https://github.com/leanprover-community/mathlib/commit/8f42d73)
chore(data/list/pairwise): add `list.pairwise_pmap` and `list.pairwise.pmap` ([#5273](https://github.com/leanprover-community/mathlib/pull/5273))
Also add `list.pairwise.tail` and use it in the proof of `list.sorted.tail`.
#### Estimated changes
Modified src/data/list/pairwise.lean
- \+ *theorem* pairwise.tail
- \+ *theorem* pairwise_pmap
- \+ *theorem* pairwise.pmap

Modified src/data/list/sort.lean
- \+/\- *theorem* sorted.tail
- \+/\- *theorem* sorted.tail



## [2020-12-08 03:20:13](https://github.com/leanprover-community/mathlib/commit/3f4829c)
chore(data/support): zero function has empty support ([#5275](https://github.com/leanprover-community/mathlib/pull/5275))
#### Estimated changes
Modified src/data/support.lean
- \+ *lemma* support_zero'
- \+ *lemma* support_zero



## [2020-12-08 01:21:19](https://github.com/leanprover-community/mathlib/commit/35f0862)
chore(scripts): update nolints.txt ([#5272](https://github.com/leanprover-community/mathlib/pull/5272))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-07 20:04:10](https://github.com/leanprover-community/mathlib/commit/b173925)
refactor(data/fin): use `order_embedding` for many maps ([#5251](https://github.com/leanprover-community/mathlib/pull/5251))
Also swap `data.fin` with `order.rel_iso` in the import tree.
#### Estimated changes
Modified src/analysis/analytic/composition.lean

Modified src/data/fin.lean
- \+ *lemma* coe_succ_embedding
- \+/\- *lemma* coe_last
- \+/\- *lemma* coe_cast_lt
- \+/\- *lemma* coe_cast_le
- \+ *lemma* symm_cast
- \+/\- *lemma* coe_cast
- \+/\- *lemma* coe_cast_add
- \+/\- *lemma* coe_cast_succ
- \+/\- *lemma* cast_succ_lt_succ
- \+ *lemma* succ_above_aux
- \+/\- *lemma* coe_add_nat
- \+ *lemma* coe_nat_add
- \+/\- *lemma* cast_lt_cast_succ
- \+/\- *lemma* cast_succ_inj
- \+/\- *lemma* succ_above_zero
- \+ *lemma* succ_above_last_apply
- \+/\- *lemma* coe_cast
- \+/\- *lemma* coe_cast_succ
- \+/\- *lemma* coe_cast_lt
- \+/\- *lemma* coe_cast_le
- \+/\- *lemma* coe_cast_add
- \+/\- *lemma* coe_last
- \+/\- *lemma* cast_lt_cast_succ
- \- *lemma* coe_sub_nat
- \+/\- *lemma* coe_add_nat
- \+/\- *lemma* cast_succ_inj
- \+/\- *lemma* cast_succ_lt_succ
- \- *lemma* cast_le_injective
- \+/\- *lemma* succ_above_zero
- \+ *def* succ_embedding
- \+ *def* coe_embedding
- \+/\- *def* cast_le
- \+/\- *def* cast
- \+/\- *def* cast_add
- \+/\- *def* cast_succ
- \+/\- *def* succ_above
- \+/\- *def* sub_nat
- \+/\- *def* add_nat
- \+/\- *def* nat_add
- \+/\- *def* cast_le
- \+/\- *def* cast
- \+/\- *def* cast_add
- \+/\- *def* cast_succ
- \+/\- *def* succ_above
- \+/\- *def* sub_nat
- \+/\- *def* add_nat
- \+/\- *def* nat_add

Modified src/order/basic.lean

Modified src/order/rel_iso.lean
- \+ *lemma* apply_le_apply
- \+ *lemma* apply_lt_apply
- \+ *lemma* apply_eq_apply
- \+ *lemma* coe_of_strict_mono
- \- *def* fin.val.rel_embedding
- \- *def* fin_fin.rel_embedding



## [2020-12-07 20:04:08](https://github.com/leanprover-community/mathlib/commit/b9689bd)
feat(topology/algebra/infinite_sum): add lemmas about continuous linear maps ([#5243](https://github.com/leanprover-community/mathlib/pull/5243))
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_equiv.tsum_eq_iff

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum.smul
- \+ *lemma* summable.smul
- \+ *lemma* tsum_smul



## [2020-12-07 17:05:50](https://github.com/leanprover-community/mathlib/commit/f730137)
chore(logic/basic): add `and.congr_left_iff` and `@[simp]` attrs ([#5268](https://github.com/leanprover-community/mathlib/pull/5268))
#### Estimated changes
Modified src/data/pfun.lean

Modified src/logic/basic.lean
- \+/\- *lemma* and.congr_right_iff
- \+ *lemma* and.congr_left_iff
- \+/\- *lemma* and.congr_right_iff

Modified src/measure_theory/borel_space.lean

Modified src/topology/uniform_space/uniform_embedding.lean



## [2020-12-07 10:37:13](https://github.com/leanprover-community/mathlib/commit/44400c9)
feat(dynamics/circle/rotation_number): translation numbers define a group action up to a semiconjugacy ([#5138](https://github.com/leanprover-community/mathlib/pull/5138))
Formalize a theorem by Étienne Ghys: given two lifts `f₁`, `f₂` of
actions of a group `G` on the circle by orientation preserving
homeomorphisms to the real line, assume that for each `g : G` the
translation numbers of `f₁ g` and `f₂ g` are equal. Then the actions
are semiconjugate by a (possibly discontinuous) circle map.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* of_bijective_apply_symm_apply
- \+ *lemma* of_bijective_symm_apply_apply

Modified src/dynamics/circle/rotation_number/translation_number.lean
- \+ *lemma* strict_mono_iff_injective
- \+ *lemma* units_inv_apply_apply
- \+ *lemma* units_apply_inv_apply
- \+ *lemma* coe_to_order_iso
- \+ *lemma* coe_to_order_iso_symm
- \+ *lemma* coe_to_order_iso_inv
- \+ *lemma* is_unit_iff_bijective
- \+ *lemma* continuous_iff_surjective
- \+ *lemma* translation_number_one
- \+ *lemma* translation_number_units_inv
- \+ *lemma* translation_number_gpow
- \+ *lemma* map_lt_add_floor_translation_number_add_one
- \+ *lemma* map_lt_add_translation_number_add_one
- \+ *lemma* semiconj_of_group_action_of_forall_translation_number_eq
- \+ *lemma* units_semiconj_of_translation_number_eq
- \+ *lemma* semiconj_of_is_unit_of_translation_number_eq
- \+ *lemma* semiconj_of_bijective_of_translation_number_eq
- \- *lemma* translation_number_map_id
- \+ *def* to_order_iso

Modified src/order/basic.lean
- \+ *lemma* monotone.strict_mono_iff_injective



## [2020-12-07 08:45:14](https://github.com/leanprover-community/mathlib/commit/f0ceb6b)
feat(analysis/mean_inequalities): add young_inequality for nnreal and ennreal with real exponents ([#5242](https://github.com/leanprover-community/mathlib/pull/5242))
The existing young_inequality for nnreal has nnreal exponents. This adds a version with real exponents with the is_conjugate_exponent property, and a similar version for ennreal with real exponents.
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *theorem* young_inequality_real
- \+ *theorem* young_inequality

Modified src/data/real/conjugate_exponents.lean
- \+ *lemma* one_lt_nnreal
- \+ *lemma* inv_add_inv_conj_nnreal

Modified src/data/real/nnreal.lean
- \+ *lemma* of_real_inv
- \+ *lemma* of_real_div
- \+ *lemma* of_real_div'



## [2020-12-07 06:49:09](https://github.com/leanprover-community/mathlib/commit/914d2b1)
chore(topology/category/Profinite): Fix docstring ([#5265](https://github.com/leanprover-community/mathlib/pull/5265))
#### Estimated changes
Modified src/topology/category/Profinite.lean



## [2020-12-07 03:33:52](https://github.com/leanprover-community/mathlib/commit/b2427d5)
feat(order/filter/ultrafilter): Restriction of ultrafilters along large embeddings ([#5195](https://github.com/leanprover-community/mathlib/pull/5195))
This PR adds the fact that the `comap` of an ultrafilter along a "large" embedding (meaning the image is large w.r.t. the ultrafilter) is again an ultrafilter.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* range_diff_image_subset
- \+ *lemma* range_diff_image

Modified src/order/filter/basic.lean
- \+ *lemma* image_mem_map_iff
- \+ *lemma* mem_comap_iff

Modified src/order/filter/ultrafilter.lean
- \+ *def* ultrafilter.comap



## [2020-12-07 01:24:27](https://github.com/leanprover-community/mathlib/commit/67eb675)
chore(scripts): update nolints.txt ([#5262](https://github.com/leanprover-community/mathlib/pull/5262))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-06 20:08:34](https://github.com/leanprover-community/mathlib/commit/8d54d52)
chore(topology/algebra/ordered): generalize `intermediate_value_Icc` etc ([#5235](https://github.com/leanprover-community/mathlib/pull/5235))
Several lemmas assumed that the codomain is a conditionally complete
linear order while actually the statements are true for a linear
order. Also introduce `mem_range_of_exists_le_of_exists_ge` and use it
in `surjective_of_continuous`.
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+ *lemma* mem_range_of_exists_le_of_exists_ge
- \+/\- *lemma* intermediate_value_Icc
- \+/\- *lemma* intermediate_value_Icc'
- \+/\- *lemma* surjective_of_continuous
- \+/\- *lemma* surjective_of_continuous'
- \+/\- *lemma* intermediate_value_Icc
- \+/\- *lemma* intermediate_value_Icc'
- \+/\- *lemma* surjective_of_continuous
- \+/\- *lemma* surjective_of_continuous'



## [2020-12-06 20:08:32](https://github.com/leanprover-community/mathlib/commit/9cb27c9)
chore(ring_theory/algebra_tower): generalize `is_scalar_tower.right` ([#5224](https://github.com/leanprover-community/mathlib/pull/5224))
The old instance for `[is_scalar_tower R S S]` assumed
[comm_semiring S]` instead of `[semiring S]`.
#### Estimated changes
Modified src/ring_theory/algebra_tower.lean



## [2020-12-06 20:08:30](https://github.com/leanprover-community/mathlib/commit/128b316)
feat(number_theory/primes_congruent_one): infinitely many primes congruent to 1 ([#5217](https://github.com/leanprover-community/mathlib/pull/5217))
I prove that, for any positive `k : ℕ`, there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`.
 I am not sure that `p ≡ 1 [MOD k]` is the recommended way of stating this in mathlib (instead of using `nat.cast_ring_hom `), I can change it if needed. Also, I don't know if it is appropriate to create a new file, but I didn't see any reasonable location.
#### Estimated changes
Created src/number_theory/primes_congruent_one.lean
- \+ *lemma* exists_prime_ge_modeq_one
- \+ *lemma* frequently_at_top_modeq_one
- \+ *lemma* infinite_set_of_prime_modeq_one

Modified src/order/filter/cofinite.lean
- \+ *lemma* nat.frequently_at_top_iff_infinite

Modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* degree_cyclotomic_pos



## [2020-12-06 18:56:25](https://github.com/leanprover-community/mathlib/commit/b3aa052)
feat(combinatorics/simple_graph/basic): introduce incidence sets, graph construction from relation ([#5191](https://github.com/leanprover-community/mathlib/pull/5191))
Add incidence sets and some lemmas, including a proof of equivalence between the neighbor set of a vertex and its incidence set. Add a graph construction from a given relation.
Definitions and lemmas adapted from [simple_graphs2](https://github.com/leanprover-community/mathlib/blob/simple_graphs2/src/combinatorics/simple_graph/basic.lean#L317)
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* simple_graph.from_rel_adj
- \+ *lemma* incidence_set_subset
- \+ *lemma* edge_set_univ_card
- \+ *lemma* mem_incidence_set
- \+ *lemma* mem_incidence_iff_neighbor
- \+ *lemma* adj_incidence_set_inter
- \+ *lemma* incidence_other_prop
- \+ *lemma* incidence_other_neighbor_edge
- \+ *lemma* degree_pos_iff_exists_adj
- \+ *lemma* card_incidence_set_eq_degree
- \+ *lemma* mem_incidence_finset
- \+ *def* simple_graph.from_rel
- \+ *def* incidence_set
- \+ *def* other_vertex_of_incident
- \+ *def* incidence_set_equiv_neighbor_set
- \+ *def* incidence_finset
- \+ *def* min_degree
- \+ *def* max_degree



## [2020-12-06 11:43:56](https://github.com/leanprover-community/mathlib/commit/c88e8f3)
refactor(*): drop `topology/instances/complex` ([#5208](https://github.com/leanprover-community/mathlib/pull/5208))
* drop `topology/instances/complex`, deduce topology from `normed_space` instead;
* generalize continuity of `polynomial.eval` to any `topological_ring`; add versions for `eval₂` and `aeval`;
* replace `polynomial.tendsto_infinity` with `tendsto_abv_at_top`, add versions for `eval₂`, `aeval`, as well as `norm` instead of `abv`.
* generalize `complex.exists_forall_abs_polynomial_eval_le` to any `[normed_ring R] [proper_space R]` such that norm
  is multiplicative, rename to `polynomial.exists_forall_norm_le`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean

Modified src/analysis/calculus/specific_functions.lean

Modified src/analysis/complex/basic.lean
- \+ *lemma* dist_eq
- \+/\- *def* continuous_linear_map.re
- \+/\- *def* continuous_linear_map.im
- \+/\- *def* continuous_linear_map.of_real
- \+/\- *def* continuous_linear_map.re
- \+/\- *def* continuous_linear_map.im
- \+/\- *def* continuous_linear_map.of_real

Modified src/analysis/complex/polynomial.lean
- \- *lemma* exists_forall_abs_polynomial_eval_le

Modified src/analysis/normed_space/basic.lean

Modified src/data/padics/hensel.lean

Modified src/measure_theory/borel_space.lean

Modified src/topology/algebra/polynomial.lean
- \+ *lemma* tendsto_abv_eval₂_at_top
- \+ *lemma* tendsto_abv_at_top
- \+ *lemma* tendsto_abv_aeval_at_top
- \+ *lemma* tendsto_norm_at_top
- \+ *lemma* exists_forall_norm_le
- \- *lemma* polynomial.tendsto_infinity
- \- *lemma* polynomial.continuous_eval

Deleted src/topology/instances/complex.lean
- \- *lemma* uniform_continuous_inv
- \- *lemma* uniform_continuous_abs
- \- *lemma* continuous_abs
- \- *lemma* tendsto_inv
- \- *lemma* continuous_inv
- \- *lemma* continuous.inv
- \- *lemma* uniform_continuous_mul_const
- \- *lemma* uniform_continuous_mul
- \- *lemma* uniform_continuous_re
- \- *lemma* continuous_re
- \- *lemma* uniform_continuous_im
- \- *lemma* continuous_im
- \- *lemma* uniform_continuous_of_real
- \- *lemma* continuous_of_real
- \- *theorem* dist_eq
- \- *theorem* uniform_continuous_add
- \- *theorem* uniform_continuous_neg
- \- *def* real_prod_homeo



## [2020-12-06 10:31:29](https://github.com/leanprover-community/mathlib/commit/29a1731)
feat(ring_theory/witt_vector): common identities between operators on Witt vectors ([#5161](https://github.com/leanprover-community/mathlib/pull/5161))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Created src/ring_theory/witt_vector/identities.lean
- \+ *lemma* frobenius_verschiebung
- \+ *lemma* verschiebung_zmod
- \+ *lemma* coeff_p_pow
- \+ *lemma* verschiebung_mul_frobenius



## [2020-12-06 07:55:26](https://github.com/leanprover-community/mathlib/commit/339bd9a)
chore(*): clean up several unnecessary let statements ([#5257](https://github.com/leanprover-community/mathlib/pull/5257))
Cleans up a few `let`s and `letI`s and a `have` and a `set` that have made it into some proofs in the library but do not seem to do anything for the proof.
#### Estimated changes
Modified src/analysis/analytic/basic.lean

Modified src/analysis/calculus/tangent_cone.lean

Modified src/data/padics/padic_numbers.lean

Modified src/data/pnat/xgcd.lean

Modified src/ring_theory/algebraic.lean

Modified src/ring_theory/jacobson.lean

Modified src/ring_theory/noetherian.lean

Modified src/ring_theory/polynomial/basic.lean

Modified src/ring_theory/power_series.lean

Modified src/topology/constructions.lean

Modified src/topology/metric_space/gromov_hausdorff.lean



## [2020-12-06 07:55:24](https://github.com/leanprover-community/mathlib/commit/12a8361)
feat(data/polynomial): simp lemmas about polynomial derivatives ([#5256](https://github.com/leanprover-community/mathlib/pull/5256))
Add simp lemmas derivative_bit0 derivative_bit1 and derivative_X_pow
#### Estimated changes
Modified src/data/polynomial/derivative.lean
- \+ *lemma* derivative_X_pow
- \+ *lemma* derivative_bit0
- \+ *lemma* derivative_bit1

Modified test/differentiable.lean



## [2020-12-06 07:55:21](https://github.com/leanprover-community/mathlib/commit/c6de6e4)
chore(algebra/group_power): mark `map_pow` etc as `@[simp]` ([#5253](https://github.com/leanprover-community/mathlib/pull/5253))
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+/\- *theorem* monoid_hom.map_pow
- \+/\- *theorem* add_monoid_hom.map_nsmul
- \+/\- *theorem* monoid_hom.map_pow
- \+/\- *theorem* add_monoid_hom.map_nsmul

Modified src/algebra/group_power/lemmas.lean
- \+/\- *theorem* monoid_hom.map_gpow
- \+/\- *theorem* add_monoid_hom.map_gsmul
- \+/\- *theorem* monoid_hom.map_gpow
- \+/\- *theorem* add_monoid_hom.map_gsmul



## [2020-12-06 04:52:54](https://github.com/leanprover-community/mathlib/commit/8538071)
doc(data/list): fix `erasep` doc string ([#5254](https://github.com/leanprover-community/mathlib/pull/5254))
closes [#5252](https://github.com/leanprover-community/mathlib/pull/5252)
#### Estimated changes
Modified src/data/list/defs.lean



## [2020-12-06 01:24:31](https://github.com/leanprover-community/mathlib/commit/065bd5f)
chore(scripts): update nolints.txt ([#5250](https://github.com/leanprover-community/mathlib/pull/5250))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt

Modified scripts/nolints.txt



## [2020-12-05 20:21:10](https://github.com/leanprover-community/mathlib/commit/7e8e174)
style(combinatorics/simple_graph/basic): edit proof of lemma to match style guidelines ([#5245](https://github.com/leanprover-community/mathlib/pull/5245))
Rewrite proof of `adj_iff_exists_edge` to match style guidelines.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean



## [2020-12-05 20:21:06](https://github.com/leanprover-community/mathlib/commit/ae99c76)
feat(field_theory/galois): Is_galois iff is_galois bot ([#5231](https://github.com/leanprover-community/mathlib/pull/5231))
Proves that E/F is Galois iff E/bot is Galois.
This is useful in Galois theory because it gives a new way of showing that E/F is Galois:
1) Show that bot is the fixed field of some subgroup
2) Apply `is_galois.of_fixed_field`
3) Apply `is_galois_iff_is_galois_bot`
More to be added later (once [#5225](https://github.com/leanprover-community/mathlib/pull/5225) is merged): Galois is preserved by alg_equiv, is_galois_iff_galois_top
#### Estimated changes
Modified src/field_theory/adjoin.lean

Modified src/field_theory/galois.lean
- \+ *lemma* is_galois.tower_top_of_is_galois
- \+ *lemma* is_galois_iff_is_galois_bot



## [2020-12-05 20:21:04](https://github.com/leanprover-community/mathlib/commit/ddfba42)
chore(data/multiset/basic): make `card` a bundled `add_monoid_hom` ([#5228](https://github.com/leanprover-community/mathlib/pull/5228))
Other changes:
* use `/-! ###` in section headers;
* move `add_monoid` section above `card`;
* fix docstrings of `multiset.choose_x` and `multiset.choose`.
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+/\- *lemma* card_smul
- \+/\- *lemma* card_smul
- \+/\- *theorem* coe_add
- \+/\- *theorem* singleton_add
- \+/\- *theorem* le_add_right
- \+/\- *theorem* le_add_left
- \+/\- *theorem* le_iff_exists_add
- \+/\- *theorem* cons_add
- \+/\- *theorem* add_cons
- \+/\- *theorem* mem_add
- \+/\- *theorem* card_add
- \+/\- *theorem* count_eq_zero
- \+/\- *theorem* coe_add
- \+/\- *theorem* singleton_add
- \+/\- *theorem* cons_add
- \+/\- *theorem* add_cons
- \+/\- *theorem* le_add_right
- \+/\- *theorem* le_add_left
- \+/\- *theorem* card_add
- \+/\- *theorem* mem_add
- \+/\- *theorem* le_iff_exists_add
- \+/\- *theorem* count_eq_zero
- \+/\- *def* card
- \+/\- *def* card



## [2020-12-05 20:21:02](https://github.com/leanprover-community/mathlib/commit/1f64814)
chore(data/equiv/ring): add `symm_symm` and `coe_symm_mk` ([#5227](https://github.com/leanprover-community/mathlib/pull/5227))
Also generalize `map_mul` and `map_add` to `[has_mul R] [has_add R]`
instead of `[semiring R]`.
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_add
- \+ *lemma* symm_symm
- \+ *lemma* coe_symm_mk
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_add



## [2020-12-05 18:53:49](https://github.com/leanprover-community/mathlib/commit/d4bd4cd)
fix(topology/algebra/infinite_sum): fix docstring typos and add example ([#5159](https://github.com/leanprover-community/mathlib/pull/5159))
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean



## [2020-12-05 16:59:01](https://github.com/leanprover-community/mathlib/commit/83b13d1)
feat(category_theory/limits): morphisms to equalizer ([#5233](https://github.com/leanprover-community/mathlib/pull/5233))
The natural bijection for morphisms to an equalizer and the dual.
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* fork.is_limit.hom_iso_natural
- \+ *lemma* cofork.is_colimit.hom_iso_natural
- \+ *def* fork.is_limit.hom_iso
- \+ *def* cofork.is_colimit.hom_iso



## [2020-12-05 16:58:59](https://github.com/leanprover-community/mathlib/commit/dd11498)
chore(linear_algebra/basic): redefine `restrict` ([#5229](https://github.com/leanprover-community/mathlib/pull/5229))
Use `dom_restrict` and `cod_restrict`
#### Estimated changes
Modified src/linear_algebra/basic.lean



## [2020-12-05 13:48:51](https://github.com/leanprover-community/mathlib/commit/481f5e0)
chore(data/prod): `prod.swap` is `bijective` ([#5226](https://github.com/leanprover-community/mathlib/pull/5226))
#### Estimated changes
Modified src/data/prod.lean
- \+ *lemma* swap_injective
- \+ *lemma* swap_surjective
- \+ *lemma* swap_bijective
- \+ *lemma* swap_inj



## [2020-12-05 09:58:53](https://github.com/leanprover-community/mathlib/commit/c5009dd)
chore(data/equiv/basic): Add missing refl/trans/symm simp lemmas ([#5223](https://github.com/leanprover-community/mathlib/pull/5223))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* sum_congr_trans
- \+ *lemma* sum_congr_refl
- \+ *lemma* sigma_congr_right_trans
- \+ *lemma* sigma_congr_right_symm
- \+ *lemma* sigma_congr_right_refl



## [2020-12-05 07:50:28](https://github.com/leanprover-community/mathlib/commit/3972da8)
chore(category_theory/limits/preserves): make names consistent ([#5240](https://github.com/leanprover-community/mathlib/pull/5240))
adjusted names and namespaces to match [#5044](https://github.com/leanprover-community/mathlib/pull/5044)
#### Estimated changes
Modified src/category_theory/limits/preserves/shapes/products.lean
- \+ *lemma* preserves_product.iso_hom
- \- *lemma* preserves_products_iso_hom
- \+ *def* is_limit_map_cone_fan_mk_equiv
- \+ *def* is_limit_fan_mk_obj_of_is_limit
- \+ *def* is_limit_of_is_limit_fan_mk_obj
- \+ *def* preserves_product.of_iso_comparison
- \+ *def* preserves_product.iso
- \- *def* fan_map_cone_limit
- \- *def* map_is_limit_of_preserves_of_is_limit
- \- *def* is_limit_of_reflects_of_map_is_limit
- \- *def* preserves_product_of_iso_comparison
- \- *def* preserves_products_iso

Modified src/topology/sheaves/forget.lean



## [2020-12-05 07:50:26](https://github.com/leanprover-community/mathlib/commit/39a3b58)
feat(order/filter/at_top_bot): `order_iso` maps `at_top` to `at_top` ([#5236](https://github.com/leanprover-community/mathlib/pull/5236))
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* comap_at_top
- \+ *lemma* comap_at_bot
- \+ *lemma* map_at_top
- \+ *lemma* map_at_bot
- \+ *lemma* tendsto_at_top
- \+ *lemma* tendsto_at_bot
- \+ *lemma* tendsto_at_top_iff
- \+ *lemma* tendsto_at_bot_iff



## [2020-12-05 07:50:24](https://github.com/leanprover-community/mathlib/commit/147a81a)
chore(category_theory/limits): preserving coequalizers ([#5212](https://github.com/leanprover-community/mathlib/pull/5212))
dualise stuff from before
#### Estimated changes
Modified src/category_theory/limits/preserves/shapes/equalizers.lean
- \+ *lemma* preserves_coequalizer.iso_hom
- \+ *def* is_colimit_map_cocone_cofork_equiv
- \+ *def* is_colimit_cofork_map_of_is_colimit
- \+ *def* is_colimit_of_is_colimit_cofork_map
- \+ *def* is_colimit_of_has_coequalizer_of_preserves_colimit
- \+ *def* of_iso_comparison
- \+ *def* preserves_coequalizer.iso

Modified src/category_theory/limits/shapes/equalizers.lean



## [2020-12-05 07:50:22](https://github.com/leanprover-community/mathlib/commit/b82eb7a)
refactor(combinatorics/simple_graph/matching): change definition of matching ([#5210](https://github.com/leanprover-community/mathlib/pull/5210))
Refactored definition of matching per @eric-wieser's [suggestion](https://github.com/leanprover-community/mathlib/pull/5156#discussion_r535102524) and @kmill's [suggestion](https://github.com/leanprover-community/mathlib/pull/5156#discussion_r535745112), for the purpose of using `matching.sub_edges` instead of `matching.prop.sub_edges`
#### Estimated changes
Modified src/combinatorics/simple_graph/matching.lean
- \- *def* matching



## [2020-12-05 07:50:19](https://github.com/leanprover-community/mathlib/commit/dc08f4d)
feat(analysis): define asymptotic equivalence of two functions ([#4979](https://github.com/leanprover-community/mathlib/pull/4979))
This defines the relation `is_equivalent u v l`, which means that `u-v` is little o of
`v` along the filter `l`. It is required to state, for example, Stirling's formula, or the prime number theorem
#### Estimated changes
Created src/analysis/asymptotic_equivalent.lean
- \+ *lemma* is_equivalent.is_o
- \+ *lemma* is_equivalent.is_O
- \+ *lemma* is_equivalent.is_O_symm
- \+ *lemma* is_equivalent.refl
- \+ *lemma* is_equivalent.symm
- \+ *lemma* is_equivalent.trans
- \+ *lemma* is_equivalent_zero_iff_eventually_zero
- \+ *lemma* is_equivalent_const_iff_tendsto
- \+ *lemma* is_equivalent.tendsto_const
- \+ *lemma* is_equivalent.tendsto_nhds
- \+ *lemma* is_equivalent.tendsto_nhds_iff
- \+ *lemma* is_equivalent_iff_exists_eq_mul
- \+ *lemma* is_equivalent.exists_eq_mul
- \+ *lemma* is_equivalent_of_tendsto_one
- \+ *lemma* is_equivalent_of_tendsto_one'
- \+ *lemma* is_equivalent_iff_tendsto_one
- \+ *lemma* is_equivalent.smul
- \+ *lemma* is_equivalent.mul
- \+ *lemma* is_equivalent.inv
- \+ *lemma* is_equivalent.div
- \+ *lemma* is_equivalent.tendsto_at_top
- \+ *lemma* is_equivalent.tendsto_at_top_iff
- \+ *def* is_equivalent

Modified src/analysis/asymptotics.lean
- \+ *theorem* is_o_iff_tendsto'

Created src/analysis/normed_space/ordered.lean
- \+ *lemma* tendsto_pow_div_pow_at_top_of_lt
- \+ *lemma* is_o_pow_pow_at_top_of_lt



## [2020-12-05 04:54:08](https://github.com/leanprover-community/mathlib/commit/de7dbbb)
feat(algebra/group): composition of monoid homs as "bilinear" monoid hom ([#5202](https://github.com/leanprover-community/mathlib/pull/5202))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* one_hom.one_comp
- \+ *lemma* one_hom.comp_one
- \+ *lemma* one_comp
- \+ *lemma* comp_one
- \+ *lemma* mul_comp
- \+ *lemma* comp_mul
- \+ *def* comp_hom

Modified src/category_theory/preadditive/default.lean



## [2020-12-05 01:27:37](https://github.com/leanprover-community/mathlib/commit/56c4e73)
chore(scripts): update nolints.txt ([#5232](https://github.com/leanprover-community/mathlib/pull/5232))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-04 21:26:40](https://github.com/leanprover-community/mathlib/commit/0afd3a0)
chore(data/finsupp/basic): Add single_of_single_apply ([#5219](https://github.com/leanprover-community/mathlib/pull/5219))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* single_of_single_apply



## [2020-12-04 21:26:38](https://github.com/leanprover-community/mathlib/commit/8a9a5d3)
feat(dynamics): (semi-)flows, omega limits ([#4843](https://github.com/leanprover-community/mathlib/pull/4843))
This code has gone through a couple of iterations since it was first written in summer, when the ambition was 'Morse decompositions in Lean' rather than 'mildly generalise some results from a first course in differential equations'. Nevertheless there's much in here I'm not confident about & would appreciate help with.
#### Estimated changes
Created src/dynamics/flow.lean
- \+ *lemma* is_invariant_iff_image
- \+ *lemma* is_invariant.is_fw_invariant
- \+ *lemma* is_fw_invariant.is_invariant
- \+ *lemma* is_fw_invariant_iff_is_invariant
- \+ *lemma* ext
- \+ *lemma* map_add
- \+ *lemma* map_zero
- \+ *lemma* map_zero_apply
- \+ *lemma* is_invariant_iff_image_eq
- \+ *lemma* image_eq_preimage
- \+ *def* is_invariant
- \+ *def* is_fw_invariant
- \+ *def* from_iter
- \+ *def* restrict
- \+ *def* reverse
- \+ *def* to_homeomorph

Created src/dynamics/omega_limit.lean
- \+ *lemma* omega_limit_def
- \+ *lemma* omega_limit_subset_of_tendsto
- \+ *lemma* omega_limit_mono_left
- \+ *lemma* omega_limit_mono_right
- \+ *lemma* is_closed_omega_limit
- \+ *lemma* maps_to_omega_limit'
- \+ *lemma* maps_to_omega_limit
- \+ *lemma* omega_limit_image_eq
- \+ *lemma* omega_limit_preimage_subset
- \+ *lemma* mem_omega_limit_iff_frequently
- \+ *lemma* mem_omega_limit_iff_frequently₂
- \+ *lemma* mem_omega_limit_singleton_iff_map_cluster_point
- \+ *lemma* omega_limit_inter
- \+ *lemma* omega_limit_Inter
- \+ *lemma* omega_limit_union
- \+ *lemma* omega_limit_Union
- \+ *lemma* omega_limit_eq_Inter
- \+ *lemma* omega_limit_eq_bInter_inter
- \+ *lemma* omega_limit_eq_Inter_inter
- \+ *lemma* omega_limit_subset_closure_fw_image
- \+ *lemma* eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset'
- \+ *lemma* eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset
- \+ *lemma* eventually_maps_to_of_is_compact_absorbing_of_is_open_of_omega_limit_subset
- \+ *lemma* eventually_closure_subset_of_is_open_of_omega_limit_subset
- \+ *lemma* eventually_maps_to_of_is_open_of_omega_limit_subset
- \+ *lemma* nonempty_omega_limit_of_is_compact_absorbing
- \+ *lemma* nonempty_omega_limit
- \+ *lemma* is_invariant_omega_limit
- \+ *lemma* omega_limit_image_subset
- \+ *lemma* omega_limit_image_eq
- \+ *lemma* omega_limit_omega_limit
- \+ *def* omega_limit

Modified src/topology/algebra/monoid.lean

Modified src/topology/constructions.lean
- \+ *lemma* continuous_uncurry_left
- \+ *lemma* continuous_uncurry_right
- \+ *lemma* continuous_curry
- \+ *lemma* continuous_uncurry_of_discrete_topology_left



## [2020-12-04 15:57:38](https://github.com/leanprover-community/mathlib/commit/5f43079)
doc(data/quot): Fix typo ([#5221](https://github.com/leanprover-community/mathlib/pull/5221))
#### Estimated changes
Modified src/data/quot.lean



## [2020-12-04 15:57:35](https://github.com/leanprover-community/mathlib/commit/4ea2e68)
chore(algebra/big_operators/basic): Split prod_cancels_of_partition_cancels in two and add a docstring ([#5218](https://github.com/leanprover-community/mathlib/pull/5218))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_partition



## [2020-12-04 15:57:31](https://github.com/leanprover-community/mathlib/commit/5ea96f9)
feat(linear_algebra/multilinear): Add `multilinear_map.coprod` ([#5182](https://github.com/leanprover-community/mathlib/pull/5182))
#### Estimated changes
Modified src/linear_algebra/multilinear.lean
- \+ *def* dom_coprod
- \+ *def* dom_coprod'



## [2020-12-04 15:57:29](https://github.com/leanprover-community/mathlib/commit/cb7effa)
feat(ring_theory/discrete_valuation_ring): add additive valuation ([#5094](https://github.com/leanprover-community/mathlib/pull/5094))
Following the approach used for p-adic numbers, we define an additive valuation on a DVR R as a bare function v: R -> nat, with the convention that v(0)=0 instead of +infinity for convenience. Note that we have no `hom` structure (like `monoid_hom` or `add_monoid_hom`) for v(a*b)=v(a)+v(b) and anyway this doesn't even hold if ab=0. We prove all the usual axioms.
#### Estimated changes
Modified src/ring_theory/discrete_valuation_ring.lean
- \+ *lemma* eq_unit_mul_pow_irreducible
- \+ *lemma* add_val_def
- \+ *lemma* add_val_def'
- \+ *lemma* add_val_zero
- \+ *lemma* add_val_one
- \+ *lemma* add_val_uniformizer
- \+ *lemma* add_val_mul
- \+ *lemma* add_val_pow
- \+ *lemma* add_val_le_iff_dvd
- \+ *lemma* add_val_add
- \+ *theorem* add_val_spec



## [2020-12-04 14:48:23](https://github.com/leanprover-community/mathlib/commit/f1d30f6)
doc(data/typevec): Fix broken markdown rendering ([#5220](https://github.com/leanprover-community/mathlib/pull/5220))
#### Estimated changes
Modified src/data/typevec.lean



## [2020-12-04 13:34:38](https://github.com/leanprover-community/mathlib/commit/54c13bd)
docs(data/fp): Move title comment so that it appears in the markdown ([#5222](https://github.com/leanprover-community/mathlib/pull/5222))
#### Estimated changes
Modified src/data/fp/basic.lean



## [2020-12-04 10:35:26](https://github.com/leanprover-community/mathlib/commit/30467f4)
feat(field_theory/adjoin): induction on adjoin ([#5173](https://github.com/leanprover-community/mathlib/pull/5173))
This is another adjoin induction lemma that will be used in an upcoming PR.
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* induction_on_adjoin_finset
- \+ *lemma* induction_on_adjoin_fg
- \+/\- *lemma* induction_on_adjoin
- \+/\- *lemma* induction_on_adjoin



## [2020-12-04 07:43:02](https://github.com/leanprover-community/mathlib/commit/7e307bc)
chore(algebra/ring): delete a duplicate instance ([#5215](https://github.com/leanprover-community/mathlib/pull/5215))
In [#3303](https://github.com/leanprover-community/mathlib/pull/3303) and [#3296](https://github.com/leanprover-community/mathlib/pull/3296) which were merged 1 day apart two versions of the instance comm_monoid_with_zero from a comm_semiring were added 5 lines apart in the file, delete one.
#### Estimated changes
Modified src/algebra/ring/basic.lean



## [2020-12-04 07:43:00](https://github.com/leanprover-community/mathlib/commit/2d00ba4)
feat(category_theory/limits): cleanup equalizers ([#5214](https://github.com/leanprover-community/mathlib/pull/5214))
golf and make simp more powerful
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+/\- *lemma* fork.ι_eq_app_zero
- \+/\- *lemma* cofork.π_eq_app_one
- \+/\- *lemma* fork.ι_of_ι
- \+/\- *lemma* cofork.π_of_π
- \+/\- *lemma* fork.condition
- \+/\- *lemma* cofork.condition
- \+/\- *lemma* fork.ι_of_ι
- \+/\- *lemma* cofork.π_of_π
- \+/\- *lemma* fork.ι_eq_app_zero
- \+/\- *lemma* cofork.π_eq_app_one
- \+/\- *lemma* fork.condition
- \+/\- *lemma* cofork.condition
- \- *lemma* cone_of_split_mono_π_app_zero
- \- *lemma* cone_of_split_mono_π_app_one
- \- *lemma* cocone_of_split_epi_ι_app_one
- \- *lemma* cocone_of_split_epi_ι_app_zero
- \+/\- *def* split_epi_coequalizes
- \+/\- *def* split_epi_coequalizes



## [2020-12-04 07:42:59](https://github.com/leanprover-community/mathlib/commit/b2f8c4c)
feat(category_theory/limits): reflects limit if reflects iso and preserves ([#5213](https://github.com/leanprover-community/mathlib/pull/5213))
#### Estimated changes
Modified src/category_theory/limits/preserves/basic.lean
- \+ *def* reflects_limit_of_reflects_isomorphisms
- \+ *def* reflects_limits_of_shape_of_reflects_isomorphisms
- \+ *def* reflects_limits_of_reflects_isomorphisms
- \+ *def* reflects_colimit_of_reflects_isomorphisms
- \+ *def* reflects_colimits_of_shape_of_reflects_isomorphisms
- \+ *def* reflects_colimits_of_reflects_isomorphisms



## [2020-12-04 07:42:57](https://github.com/leanprover-community/mathlib/commit/cfd01f9)
chore(topology/continuous_on): change type of `continuous_on.comp_continuous` ([#5209](https://github.com/leanprover-community/mathlib/pull/5209))
Use `∀ x, f x ∈ s` instead of `range f ⊆ s`.
#### Estimated changes
Modified src/topology/continuous_on.lean

Modified src/topology/path_connected.lean



## [2020-12-04 07:42:55](https://github.com/leanprover-community/mathlib/commit/ad25cac)
refactor(data/polynomial/derivative): change `polynomial.derivative` to be a `linear_map` ([#5198](https://github.com/leanprover-community/mathlib/pull/5198))
Refactors polynomial.derivative to be a linear_map by default
#### Estimated changes
Modified src/data/polynomial/derivative.lean
- \+ *lemma* derivative_apply
- \+/\- *lemma* derivative_zero
- \+ *lemma* derivative_eval
- \+/\- *lemma* derivative_zero
- \+/\- *def* derivative
- \+/\- *def* derivative
- \- *def* derivative_hom
- \- *def* derivative_lhom

Modified src/data/polynomial/identities.lean
- \- *lemma* derivative_eval



## [2020-12-04 07:42:52](https://github.com/leanprover-community/mathlib/commit/240f6eb)
feat(category_theory/monad): cleanups in monad algebra ([#5193](https://github.com/leanprover-community/mathlib/pull/5193))
- Converts the simp normal form for composition of algebra homs to use category notation. 
- Adds simps where appropriate
- Golfs proofs, remove some erw and nonterminal simps
- Remove some redundant brackets
#### Estimated changes
Modified src/category_theory/monad/algebra.lean
- \+ *lemma* comp_eq_comp
- \+ *lemma* id_eq_id
- \+ *lemma* id_f
- \+ *lemma* comp_f
- \+ *lemma* comp_eq_comp
- \+ *lemma* id_eq_id
- \+ *lemma* id_f
- \+ *lemma* comp_f
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* id
- \+/\- *def* comp



## [2020-12-04 07:42:50](https://github.com/leanprover-community/mathlib/commit/c10d1b1)
feat(ring_theory/polynomial/cyclotomic):  add  order_of_root_cyclotomic ([#5151](https://github.com/leanprover-community/mathlib/pull/5151))
Two lemmas about roots of cyclotomic polynomials modulo `p`.
`order_of_root_cyclotomic` is the main algebraic tool to prove the existence of infinitely many primes congruent to `1` modulo `n`.
#### Estimated changes
Modified src/number_theory/divisors.lean
- \+ *lemma* divisors_subset_of_dvd
- \+ *lemma* divisors_subset_proper_divisors

Modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* X_pow_sub_one_dvd_prod_cyclotomic
- \+/\- *lemma* cyclotomic_coeff_zero
- \+ *lemma* coprime_of_root_cyclotomic
- \+ *lemma* order_of_root_cyclotomic_dvd
- \+ *lemma* order_of_root_cyclotomic
- \+/\- *lemma* cyclotomic_coeff_zero



## [2020-12-04 07:42:48](https://github.com/leanprover-community/mathlib/commit/c939c9e)
feat(category_theory/limits/preserves): preserving terminal objects ([#5060](https://github.com/leanprover-community/mathlib/pull/5060))
Another part of [#4716](https://github.com/leanprover-community/mathlib/pull/4716).
#### Estimated changes
Created src/category_theory/limits/preserves/shapes/terminal.lean
- \+ *lemma* has_terminal_of_has_terminal_of_preserves_limit
- \+ *lemma* preserves_terminal.iso_hom
- \+ *def* is_limit_map_cone_empty_cone_equiv
- \+ *def* is_terminal_obj_of_is_terminal
- \+ *def* is_terminal_of_is_terminal_obj
- \+ *def* is_limit_of_has_terminal_of_preserves_limit
- \+ *def* preserves_terminal.of_iso_comparison
- \+ *def* preserves_terminal_of_is_iso
- \+ *def* preserves_terminal_of_iso
- \+ *def* preserves_terminal.iso



## [2020-12-04 06:35:18](https://github.com/leanprover-community/mathlib/commit/4f5046d)
feat(ring_theory/polynomial/cyclotomic): Möbius inversion formula for cyclotomic polynomials ([#5192](https://github.com/leanprover-community/mathlib/pull/5192))
Proves Möbius inversion for functions to a `comm_group_with_zero`
Proves the Möbius inversion formula for cyclotomic polynomials
#### Estimated changes
Modified src/number_theory/arithmetic_function.lean
- \+ *theorem* prod_eq_iff_prod_pow_moebius_eq_of_nonzero

Modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* cyclotomic_eq_prod_X_pow_sub_one_pow_moebius



## [2020-12-04 01:20:37](https://github.com/leanprover-community/mathlib/commit/57dd302)
chore(scripts): update nolints.txt ([#5211](https://github.com/leanprover-community/mathlib/pull/5211))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-03 22:25:01](https://github.com/leanprover-community/mathlib/commit/20cc59d)
feat(algebra/lie/basic): define missing inclusion maps ([#5207](https://github.com/leanprover-community/mathlib/pull/5207))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* incl_apply
- \+ *lemma* incl_eq_val
- \+ *lemma* coe_hom_of_le
- \+ *lemma* hom_of_le_apply
- \+ *lemma* incl_apply
- \+ *def* incl
- \+ *def* hom_of_le
- \+ *def* incl

Modified src/algebra/lie/classical.lean



## [2020-12-03 22:24:59](https://github.com/leanprover-community/mathlib/commit/ec839ef)
feat(topology/algebra/order): continuity of monotone functions ([#5199](https://github.com/leanprover-community/mathlib/pull/5199))
Add local versions of `order_iso.continuous`.
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+ *lemma* strict_mono_incr_on.continuous_at_right_of_exists_between
- \+ *lemma* continuous_at_right_of_mono_incr_on_of_exists_between
- \+ *lemma* continuous_at_right_of_mono_incr_on_of_closure_image_mem_nhds_within
- \+ *lemma* continuous_at_right_of_mono_incr_on_of_image_mem_nhds_within
- \+ *lemma* strict_mono_incr_on.continuous_at_right_of_closure_image_mem_nhds_within
- \+ *lemma* strict_mono_incr_on.continuous_at_right_of_image_mem_nhds_within
- \+ *lemma* strict_mono_incr_on.continuous_at_right_of_surj_on
- \+ *lemma* strict_mono_incr_on.continuous_at_left_of_exists_between
- \+ *lemma* continuous_at_left_of_mono_incr_on_of_exists_between
- \+ *lemma* continuous_at_left_of_mono_incr_on_of_closure_image_mem_nhds_within
- \+ *lemma* continuous_at_left_of_mono_incr_on_of_image_mem_nhds_within
- \+ *lemma* strict_mono_incr_on.continuous_at_left_of_closure_image_mem_nhds_within
- \+ *lemma* strict_mono_incr_on.continuous_at_left_of_image_mem_nhds_within
- \+ *lemma* strict_mono_incr_on.continuous_at_left_of_surj_on
- \+ *lemma* strict_mono_incr_on.continuous_at_of_exists_between
- \+ *lemma* strict_mono_incr_on.continuous_at_of_closure_image_mem_nhds
- \+ *lemma* strict_mono_incr_on.continuous_at_of_image_mem_nhds
- \+ *lemma* continuous_at_of_mono_incr_on_of_exists_between
- \+ *lemma* continuous_at_of_mono_incr_on_of_closure_image_mem_nhds
- \+ *lemma* continuous_at_of_mono_incr_on_of_image_mem_nhds
- \+ *lemma* monotone.continuous_of_dense_range
- \+ *lemma* monotone.continuous_of_surjective



## [2020-12-03 19:30:25](https://github.com/leanprover-community/mathlib/commit/3894503)
doc(tactic/library_search): use more detailed doc string in docs ([#5206](https://github.com/leanprover-community/mathlib/pull/5206))
The doc string for `tactic.interactive.library_search` is better than the tactic doc entry.
The latter is missing details like `library_search!`
#### Estimated changes
Modified src/tactic/suggest.lean



## [2020-12-03 19:30:23](https://github.com/leanprover-community/mathlib/commit/d416ad6)
feat(topology/category/Profinite): add category of profinite top. spaces ([#5147](https://github.com/leanprover-community/mathlib/pull/5147))
#### Estimated changes
Modified src/topology/category/CompHaus.lean
- \+ *lemma* coe_to_Top
- \+/\- *def* CompHaus_to_Top
- \+/\- *def* CompHaus_to_Top

Created src/topology/category/Profinite.lean
- \+ *lemma* coe_to_Top
- \+ *lemma* Profinite_to_CompHaus_to_Top
- \+ *def* Profinite_to_Top
- \+ *def* Profinite_to_CompHaus



## [2020-12-03 19:30:20](https://github.com/leanprover-community/mathlib/commit/6f38a50)
feat(field_theory/minimal_polynomial): add algebra_map_inj ([#5062](https://github.com/leanprover-community/mathlib/pull/5062))
I have added `algebra_map_inj` that computes the minimal polynomial of an element of the base ring. It generalizes `algebra_map` that assumes the base ring to be a field. I left `algebra_map` since I think it is reasonable to have a lemma that works without proving explicitly that the algebra map is injective.
#### Estimated changes
Modified src/field_theory/minimal_polynomial.lean
- \+ *lemma* degree_le_of_monic
- \+ *lemma* eq_X_sub_C_of_algebra_map_inj
- \+/\- *lemma* gcd_domain_eq_field_fractions
- \+ *lemma* eq_X_sub_C
- \+/\- *lemma* gcd_domain_eq_field_fractions
- \- *lemma* algebra_map'



## [2020-12-03 16:31:34](https://github.com/leanprover-community/mathlib/commit/986cabf)
fix(linear_algebra/multilinear): Fix incorrect type constraints on `dom_dom_congr` ([#5203](https://github.com/leanprover-community/mathlib/pull/5203))
In the last PR, I accidentally put this in a section with `[comm_semiring R]`, but this only actually requires `[semiring R]`
#### Estimated changes
Modified src/linear_algebra/multilinear.lean
- \+/\- *def* dom_dom_congr
- \+/\- *def* dom_dom_congr_equiv
- \+/\- *def* dom_dom_congr
- \+/\- *def* dom_dom_congr_equiv



## [2020-12-03 16:31:32](https://github.com/leanprover-community/mathlib/commit/5269717)
chore(linear_algebra/determinant): Move some lemmas about swaps to better files ([#5201](https://github.com/leanprover-community/mathlib/pull/5201))
These lemmas are not specific to determinants, and I need them in another file imported by `determinant`.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *lemma* comp_swap_eq_update
- \+/\- *lemma* swap_apply_self
- \+ *lemma* apply_swap_eq_self
- \+/\- *lemma* comp_swap_eq_update
- \+/\- *lemma* swap_apply_self

Modified src/group_theory/perm/sign.lean
- \+ *def* mod_swap

Modified src/linear_algebra/determinant.lean
- \- *def* mod_swap



## [2020-12-03 16:31:30](https://github.com/leanprover-community/mathlib/commit/8ff9c0e)
feat(group_theory/order_of_element): add is_cyclic_of_prime_card ([#5172](https://github.com/leanprover-community/mathlib/pull/5172))
Add `is_cyclic_of_prime_card`, which says if a group has prime order, then it is cyclic. I also added `eq_top_of_card_eq` which says a subgroup is `top` when it has the same size as the group, not sure where that should be in the file.
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* is_cyclic_of_prime_card

Modified src/group_theory/subgroup.lean
- \+ *lemma* eq_top_of_card_eq



## [2020-12-03 14:04:40](https://github.com/leanprover-community/mathlib/commit/f1b387f)
feat(algebra/module/basic): Add smul_comm_class instances ([#5205](https://github.com/leanprover-community/mathlib/pull/5205))
#### Estimated changes
Modified src/algebra/module/basic.lean



## [2020-12-03 14:04:38](https://github.com/leanprover-community/mathlib/commit/a4b6c41)
feat(field_theory/separable): is_separable_of_alg_hom_is_separable ([#5175](https://github.com/leanprover-community/mathlib/pull/5175))
Proves that is_separable pulls back along an alg_hom
#### Estimated changes
Modified src/field_theory/separable.lean
- \+ *lemma* is_separable.of_alg_hom



## [2020-12-03 14:04:36](https://github.com/leanprover-community/mathlib/commit/b978f36)
refactor(field_theory/fixed): Generalize alg_hom lemmas ([#5174](https://github.com/leanprover-community/mathlib/pull/5174))
This PR generalizes some alg_hom lemmas to not require equality of the domain and codomain.
#### Estimated changes
Modified src/field_theory/fixed.lean
- \+/\- *lemma* linear_independent_to_linear_map
- \+/\- *lemma* cardinal_mk_alg_hom
- \+/\- *lemma* linear_independent_to_linear_map
- \+/\- *lemma* cardinal_mk_alg_hom



## [2020-12-03 14:04:33](https://github.com/leanprover-community/mathlib/commit/e7c2bba)
feat(ring_theory/witt_vector/frobenius): the frobenius endomorphism of witt vectors ([#4838](https://github.com/leanprover-community/mathlib/pull/4838))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Created src/ring_theory/witt_vector/frobenius.lean
- \+ *lemma* bind₁_frobenius_poly_rat_witt_polynomial
- \+ *lemma* frobenius_poly_aux_eq
- \+ *lemma* map_frobenius_poly
- \+ *lemma* map_frobenius_poly.key₁
- \+ *lemma* map_frobenius_poly.key₂
- \+ *lemma* map_frobenius_poly
- \+ *lemma* frobenius_poly_zmod
- \+ *lemma* bind₁_frobenius_poly_witt_polynomial
- \+ *lemma* coeff_frobenius_fun
- \+ *lemma* frobenius_fun_is_poly
- \+ *lemma* ghost_component_frobenius_fun
- \+ *lemma* coeff_frobenius
- \+ *lemma* ghost_component_frobenius
- \+ *lemma* frobenius_is_poly
- \+ *lemma* coeff_frobenius_char_p
- \+ *lemma* frobenius_eq_map_frobenius
- \+ *lemma* frobenius_zmodp
- \+ *def* frobenius_poly_rat
- \+ *def* frobenius_poly
- \+ *def* frobenius_fun
- \+ *def* frobenius



## [2020-12-03 12:03:20](https://github.com/leanprover-community/mathlib/commit/f1531ea)
feat(ring_theory/witt_vector): witt_sub, a demonstration of is_poly techniques ([#5165](https://github.com/leanprover-community/mathlib/pull/5165))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/ring_theory/witt_vector/is_poly.lean
- \+ *lemma* sub_eq
- \+ *lemma* sub_coeff



## [2020-12-03 12:03:18](https://github.com/leanprover-community/mathlib/commit/f6273d4)
feat(group_theory/group_action/sub_mul_action): Add an object for bundled sets closed under a mul action ([#4996](https://github.com/leanprover-community/mathlib/pull/4996))
This adds `sub_mul_action` as a base class for `submodule`, and copies across the relevant lemmas.
This also weakens the type class requires for `A →[R] B`, to allow it to be used when only `has_scalar` is available.
#### Estimated changes
Modified src/algebra/group_action_hom.lean
- \+/\- *lemma* map_smul
- \+/\- *lemma* id_apply
- \+/\- *lemma* comp_apply
- \+/\- *lemma* id_comp
- \+/\- *lemma* comp_id
- \+/\- *lemma* map_smul
- \+/\- *lemma* id_apply
- \+/\- *lemma* comp_apply
- \+/\- *lemma* id_comp
- \+/\- *lemma* comp_id
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+/\- *def* comp
- \+/\- *def* comp

Modified src/algebra/module/submodule.lean
- \+/\- *lemma* neg_mem
- \+/\- *lemma* neg_mem
- \+ *theorem* to_sub_mul_action_injective
- \+ *theorem* to_sub_mul_action_eq

Created src/group_theory/group_action/sub_mul_action.lean
- \+ *lemma* smul_mem
- \+ *lemma* coe_eq_coe
- \+ *lemma* coe_smul
- \+ *lemma* coe_mk
- \+ *lemma* coe_mem
- \+ *lemma* subtype_eq_val
- \+ *lemma* smul_mem_iff'
- \+ *lemma* neg_mem
- \+ *lemma* neg_mem_iff
- \+ *lemma* coe_neg
- \+ *theorem* coe_sort_coe
- \+ *theorem* coe_injective
- \+ *theorem* coe_set_eq
- \+ *theorem* ext'_iff
- \+ *theorem* ext
- \+ *theorem* mem_coe
- \+ *theorem* subtype_apply
- \+ *theorem* smul_mem_iff



## [2020-12-03 10:55:59](https://github.com/leanprover-community/mathlib/commit/98a20c2)
feat(combinatorics/simple_graph/matching): introduce matchings and perfect matchings of graphs ([#5156](https://github.com/leanprover-community/mathlib/pull/5156))
Introduce definitions of matchings and perfect matchings of graphs. This is with the goal of eventually proving Hall's Marriage Theorem and Tutte's Theorem.
#### Estimated changes
Created src/combinatorics/simple_graph/matching.lean
- \+ *lemma* matching.is_perfect_iff
- \+ *def* matching
- \+ *def* matching.support
- \+ *def* matching.is_perfect



## [2020-12-03 02:41:41](https://github.com/leanprover-community/mathlib/commit/61e76c4)
chore(scripts): update nolints.txt ([#5197](https://github.com/leanprover-community/mathlib/pull/5197))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-03 01:03:53](https://github.com/leanprover-community/mathlib/commit/d9a7d05)
chore(topology/algebra/ordered): add `order_iso.to_homeomorph` ([#5111](https://github.com/leanprover-community/mathlib/pull/5111))
* Replace `homeomorph_of_strict_mono_surjective` with `order_iso.to_homeomorph` and `order_iso.continuous`.
* Drop `continuous_at_of_strict_mono_surjective` in favor of `order_iso.to_homeomorph`.
* Use notation for `nhds_within` here and there.
#### Estimated changes
Modified docs/undergrad.yaml

Modified src/topology/algebra/ordered.lean
- \+ *lemma* coe_to_homeomorph
- \+ *lemma* coe_to_homeomorph_symm
- \- *lemma* continuous_right_of_strict_mono_surjective
- \- *lemma* continuous_left_of_strict_mono_surjective
- \- *lemma* continuous_at_of_strict_mono_surjective
- \- *lemma* continuous_of_strict_mono_surjective
- \- *lemma* continuous_inv_of_strict_mono_equiv
- \- *lemma* coe_homeomorph_of_strict_mono_surjective
- \+ *def* to_homeomorph



## [2020-12-02 21:22:19](https://github.com/leanprover-community/mathlib/commit/3f61e54)
feat(category_theory/monad): mark monad lemmas as reassoc ([#5190](https://github.com/leanprover-community/mathlib/pull/5190))
#### Estimated changes
Modified src/category_theory/monad/basic.lean



## [2020-12-02 21:22:16](https://github.com/leanprover-community/mathlib/commit/a84d7a7)
feat(category_theory/adjunction): adjunction to equivalence ([#5189](https://github.com/leanprover-community/mathlib/pull/5189))
Raise an adjunction to an equivalence
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean
- \+ *def* to_equivalence
- \+ *def* is_right_adjoint_to_is_equivalence



## [2020-12-02 21:22:13](https://github.com/leanprover-community/mathlib/commit/ed6eab0)
feat(category_theory/adjunction): simp adjunction defs ([#5188](https://github.com/leanprover-community/mathlib/pull/5188))
Mark adjunction defs as `simps` and use the new lemmas to simplify some proofs
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean
- \- *lemma* equiv_homset_left_of_nat_iso_apply
- \- *lemma* equiv_homset_left_of_nat_iso_symm_apply
- \- *lemma* equiv_homset_right_of_nat_iso_apply
- \- *lemma* equiv_homset_right_of_nat_iso_symm_apply

Modified src/category_theory/adjunction/fully_faithful.lean



## [2020-12-02 21:22:11](https://github.com/leanprover-community/mathlib/commit/9be829e)
feat(order/bounds): add basic lemmas about bdd_below ([#5186](https://github.com/leanprover-community/mathlib/pull/5186))
Lemmas for bounded intervals (`Icc`, `Ico`, `Ioc` and `Ioo`). There were lemmas for `bdd_above` but the ones for `bdd_below` were missing.
#### Estimated changes
Modified src/order/bounds.lean
- \+ *lemma* bdd_below_Icc
- \+ *lemma* bdd_below_Ico
- \+ *lemma* bdd_below_Ioc
- \+ *lemma* bdd_below_Ioo



## [2020-12-02 21:22:09](https://github.com/leanprover-community/mathlib/commit/e5befed)
chore(data/polynomial/degree): golf some proofs, add simple lemmas ([#5185](https://github.com/leanprover-community/mathlib/pull/5185))
* drop `polynomial.nat_degree_C_mul_X_pow_of_nonzero`; was a duplicate
  of `polynomial.nat_degree_C_mul_X_pow`;
* golf the proof of `nat_degree_C_mul_X_pow_le`;
* add more `simp` lemmas.
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* nat_degree_C_mul_X
- \+/\- *lemma* leading_coeff_monomial
- \+ *lemma* leading_coeff_C_mul_X_pow
- \+/\- *lemma* leading_coeff_X_pow
- \+ *lemma* monic_X_pow
- \+ *lemma* degree_mul_monic
- \+ *lemma* degree_mul_X
- \+ *lemma* degree_mul_X_pow
- \- *lemma* nat_degree_C_mul_X_pow_of_nonzero
- \+/\- *lemma* leading_coeff_monomial
- \- *lemma* leading_coeff_monomial'
- \+/\- *lemma* leading_coeff_X_pow
- \+ *theorem* leading_coeff_mul_monic
- \+/\- *theorem* leading_coeff_mul_X_pow
- \+ *theorem* leading_coeff_mul_X
- \+/\- *theorem* leading_coeff_mul_X_pow

Modified src/data/polynomial/div.lean



## [2020-12-02 21:22:07](https://github.com/leanprover-community/mathlib/commit/64fd9f8)
feat(order/rel_iso): preimages of intervals under an `order_iso` ([#5183](https://github.com/leanprover-community/mathlib/pull/5183))
#### Estimated changes
Modified src/order/rel_iso.lean
- \+ *lemma* preimage_Iic
- \+ *lemma* preimage_Ici
- \+ *lemma* preimage_Iio
- \+ *lemma* preimage_Ioi
- \+ *lemma* preimage_Icc
- \+ *lemma* preimage_Ico
- \+ *lemma* preimage_Ioc
- \+ *lemma* preimage_Ioo



## [2020-12-02 21:22:05](https://github.com/leanprover-community/mathlib/commit/725fb8b)
feat(algebra/lie/basic): define `map` and `comap` for Lie ideals, submodules ([#5181](https://github.com/leanprover-community/mathlib/pull/5181))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* mem_lie_span
- \+ *lemma* subset_lie_span
- \+ *lemma* lie_span_le
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* gc_map_comap
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* gc_map_comap
- \+ *def* lie_span
- \+ *def* map
- \+ *def* comap
- \+ *def* map
- \+ *def* comap



## [2020-12-02 21:22:03](https://github.com/leanprover-community/mathlib/commit/5e93545)
feat(linear_algebra/multilinear): Generalize dom_dom_congr for equivalences between types ([#5180](https://github.com/leanprover-community/mathlib/pull/5180))
This also bundles the operation into an equivalence.
#### Estimated changes
Modified src/linear_algebra/multilinear.lean
- \+/\- *def* dom_dom_congr
- \+ *def* dom_dom_congr_equiv
- \+/\- *def* dom_dom_congr



## [2020-12-02 21:22:01](https://github.com/leanprover-community/mathlib/commit/8da5f23)
feat(data/set/function): Extend `update_comp` lemmas to work on dependent functions ([#5178](https://github.com/leanprover-community/mathlib/pull/5178))
Also extends them to `Sort`
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* update_comp_eq_of_not_mem_range'
- \+/\- *lemma* update_comp_eq_of_not_mem_range
- \+ *lemma* update_comp_eq_of_injective'
- \+/\- *lemma* update_comp_eq_of_injective
- \+/\- *lemma* update_comp_eq_of_not_mem_range
- \+/\- *lemma* update_comp_eq_of_injective



## [2020-12-02 21:21:58](https://github.com/leanprover-community/mathlib/commit/2189c7a)
feat(data/option/basic): map_map functor-like lemmas ([#5030](https://github.com/leanprover-community/mathlib/pull/5030))
New lemmas:
`map_eq_map`
`map_map`
`comp_map`
`map_comp_map`
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* map_eq_map
- \+ *lemma* map_map
- \+ *lemma* comp_map
- \+ *lemma* map_comp_map
- \+/\- *theorem* map_none
- \+/\- *theorem* map_some
- \+/\- *theorem* map_eq_some
- \+/\- *theorem* map_none
- \+/\- *theorem* map_some
- \+/\- *theorem* map_eq_some

Modified src/data/seq/seq.lean



## [2020-12-02 19:13:28](https://github.com/leanprover-community/mathlib/commit/0bb8809)
feat(category_theory/limits): left adjoint if preserves colimits ([#4942](https://github.com/leanprover-community/mathlib/pull/4942))
A slight generalisation of a construction from before. Maybe this is the dual version you were talking about @jcommelin - if so my mistake! I think the advantage of doing it this way is that you definitionally get the old version but also the new version too.
#### Estimated changes
Modified src/category_theory/equivalence.lean

Modified src/category_theory/limits/presheaf.lean
- \+ *def* is_left_adjoint_of_preserves_colimits_aux
- \+/\- *def* is_left_adjoint_of_preserves_colimits
- \+/\- *def* is_left_adjoint_of_preserves_colimits



## [2020-12-02 17:38:03](https://github.com/leanprover-community/mathlib/commit/e5ea200)
chore(analysis/normed_space): golf 2 proofs ([#5184](https://github.com/leanprover-community/mathlib/pull/5184))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean



## [2020-12-02 15:07:43](https://github.com/leanprover-community/mathlib/commit/a8ddd7b)
feat(algebra/module/basic): generalize `is_scalar_tower` instances ([#5135](https://github.com/leanprover-community/mathlib/pull/5135))
#### Estimated changes
Modified src/algebra/module/basic.lean

Modified src/ring_theory/algebra_tower.lean



## [2020-12-02 13:32:27](https://github.com/leanprover-community/mathlib/commit/d6241cb)
feat(linear_algebra/*): Use alternating maps for wedge and determinant ([#5124](https://github.com/leanprover-community/mathlib/pull/5124))
This :
* Adds `exterior_algebra.ι_multi`, where `ι_multi ![a, b ,c]` = `ι a * ι b * ι c`
* Makes `det_row_multilinear` an `alternating_map`
* Makes `is_basis.det` an `alternating_map`
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+/\- *def* det_row_multilinear
- \+/\- *def* det_row_multilinear

Modified src/linear_algebra/exterior_algebra.lean
- \+ *lemma* ι_add_mul_swap
- \+ *lemma* ι_mul_prod_list
- \+ *lemma* ι_multi_apply
- \+ *def* ι_multi

Modified src/linear_algebra/matrix.lean
- \+ *lemma* linear_map.to_matrix_transpose_apply
- \+ *lemma* linear_map.to_matrix_transpose_apply'
- \+ *lemma* to_matrix_transpose_apply
- \+/\- *def* is_basis.det
- \+/\- *def* is_basis.det



## [2020-12-02 07:25:31](https://github.com/leanprover-community/mathlib/commit/61f6364)
feat(number_theory/arithmetic_function): Möbius inversion for `add_comm_group`s, `comm_group`s ([#5115](https://github.com/leanprover-community/mathlib/pull/5115))
Adds scalar multiplication for `arithmetic_function`s
Generalizes Möbius inversion to work with `(add_)comm_group`s
#### Estimated changes
Modified src/number_theory/arithmetic_function.lean
- \+ *lemma* smul_apply
- \+/\- *lemma* mul_apply
- \+ *lemma* mul_smul'
- \+ *lemma* one_smul'
- \+/\- *lemma* mul_apply
- \+ *theorem* coe_zeta_smul_apply
- \+ *theorem* sum_eq_iff_sum_smul_moebius_eq
- \+ *theorem* sum_eq_iff_sum_mul_moebius_eq
- \+ *theorem* prod_eq_iff_prod_pow_moebius_eq
- \- *theorem* sum_eq_iff_sum_moebius_eq



## [2020-12-02 02:00:39](https://github.com/leanprover-community/mathlib/commit/f7e1806)
chore(scripts): update nolints.txt ([#5176](https://github.com/leanprover-community/mathlib/pull/5176))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt



## [2020-12-01 23:23:57](https://github.com/leanprover-community/mathlib/commit/c2c7afe)
feat(data/nat/sqrt): add simple inequality lemmas and "no middle square" ([#5155](https://github.com/leanprover-community/mathlib/pull/5155))
The first two theorems are useful when one needs the biggest perfect square strictly less than a number, whereas `no_middle_square` can be used to easily prove that a given number is not a square.
#### Estimated changes
Modified src/data/nat/sqrt.lean
- \+ *theorem* sqrt_mul_sqrt_lt_succ
- \+ *theorem* succ_le_succ_sqrt
- \+ *theorem* not_exists_sq



## [2020-12-01 23:23:54](https://github.com/leanprover-community/mathlib/commit/9a4ed2a)
refactor(*): Add `_injective` alongside `_inj` lemmas ([#5150](https://github.com/leanprover-community/mathlib/pull/5150))
This adds four new `injective` lemmas:
* `list.append_right_injective`
* `list.append_left_injective`
* `sub_right_injective`
* `sub_left_injective`
It also replaces as many `*_inj` lemmas as possible with an implementation of `*_injective.eq_iff`, to make it clear that the lemmas are just aliases of each other.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* sub_right_injective
- \+ *lemma* sub_left_injective

Modified src/algebra/group/defs.lean

Modified src/data/fin.lean
- \+/\- *lemma* succ_inj
- \+/\- *lemma* cast_succ_injective
- \+/\- *lemma* succ_above_right_injective
- \+/\- *lemma* succ_above_right_inj
- \+/\- *lemma* succ_above_left_injective
- \+/\- *lemma* succ_above_left_inj
- \+/\- *lemma* succ_inj
- \+/\- *lemma* cast_succ_injective
- \+/\- *lemma* succ_above_right_inj
- \+/\- *lemma* succ_above_right_injective
- \+/\- *lemma* succ_above_left_inj
- \+/\- *lemma* succ_above_left_injective

Modified src/data/list/basic.lean
- \+ *theorem* append_right_injective
- \+ *theorem* append_left_injective



## [2020-12-01 23:23:52](https://github.com/leanprover-community/mathlib/commit/c2b7d23)
chore(category_theory/limits): separate regular and normal monos ([#5149](https://github.com/leanprover-community/mathlib/pull/5149))
This separates the file `regular_mono` into `regular_mono` and `normal_mono`: mostly this simplifies the import graph, but also this has the advantage that to use things about kernel pairs it's no longer necessary to import things about zero objects (I kept changing equalizers and using the changes in a file about monads which imported kernel pairs, and it was very slow because of zero objects)
#### Estimated changes
Modified src/category_theory/abelian/basic.lean

Modified src/category_theory/abelian/non_preadditive.lean

Created src/category_theory/limits/shapes/normal_mono.lean
- \+ *def* equivalence_reflects_normal_mono
- \+ *def* normal_mono.lift'
- \+ *def* normal_of_is_pullback_snd_of_normal
- \+ *def* normal_of_is_pullback_fst_of_normal
- \+ *def* equivalence_reflects_normal_epi
- \+ *def* normal_epi.desc'
- \+ *def* normal_of_is_pushout_snd_of_normal
- \+ *def* normal_of_is_pushout_fst_of_normal

Modified src/category_theory/limits/shapes/regular_mono.lean
- \- *def* equivalence_reflects_normal_mono
- \- *def* normal_mono.lift'
- \- *def* normal_of_is_pullback_snd_of_normal
- \- *def* normal_of_is_pullback_fst_of_normal
- \- *def* equivalence_reflects_normal_epi
- \- *def* normal_epi.desc'
- \- *def* normal_of_is_pushout_snd_of_normal
- \- *def* normal_of_is_pushout_fst_of_normal



## [2020-12-01 20:05:02](https://github.com/leanprover-community/mathlib/commit/6c456e3)
feat(linear_algebra/multilinear): Add dom_dom_congr ([#5136](https://github.com/leanprover-community/mathlib/pull/5136))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* update_comp_equiv
- \+ *lemma* update_apply_equiv_apply
- \+/\- *lemma* dite_comp_equiv_update
- \+/\- *lemma* dite_comp_equiv_update

Modified src/linear_algebra/multilinear.lean
- \+ *def* dom_dom_congr



## [2020-12-01 20:05:00](https://github.com/leanprover-community/mathlib/commit/41e0903)
feat(category_theory/limits/preserves): preserving equalizers ([#5044](https://github.com/leanprover-community/mathlib/pull/5044))
Constructions and lemmas about preserving equalizers
#### Estimated changes
Created src/category_theory/limits/preserves/shapes/equalizers.lean
- \+ *lemma* preserves_equalizer.iso_hom
- \+ *def* is_limit_map_cone_fork_equiv
- \+ *def* is_limit_fork_map_of_is_limit
- \+ *def* is_limit_of_is_limit_fork_map
- \+ *def* is_limit_of_has_equalizer_of_preserves_limit
- \+ *def* preserves_equalizer.of_iso_comparison
- \+ *def* preserves_equalizer.iso

Modified src/category_theory/limits/shapes/equalizers.lean



## [2020-12-01 16:14:24](https://github.com/leanprover-community/mathlib/commit/2a68477)
chore(algebra/group/basic): Add eq_one_iff_eq_one_of_mul_eq_one ([#5169](https://github.com/leanprover-community/mathlib/pull/5169))
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* eq_one_iff_eq_one_of_mul_eq_one



## [2020-12-01 16:14:22](https://github.com/leanprover-community/mathlib/commit/24596ca)
feat(tactic/ring_exp): handle `nat.succ p` as `p + 1` ([#5166](https://github.com/leanprover-community/mathlib/pull/5166))
Fixes: [#5157](https://github.com/leanprover-community/mathlib/pull/5157) 
This PR adds a `rewrite` operation to `ring_exp`, which takes a normalized `p' : ex sum` and a proof that `p = p'.orig`, and shows `p` also normalizes to `p'.pretty`. The only use currently is `nat.succ`. If we still had `nat.has_pow`, the same function could have handled rewriting from `nat.has_pow` to `monoid.has_pow`.
#### Estimated changes
Modified src/tactic/ring_exp.lean

Modified test/ring_exp.lean



## [2020-12-01 16:14:20](https://github.com/leanprover-community/mathlib/commit/9e78823)
feat(ring_theory/perfection): perfection and tilt ([#5032](https://github.com/leanprover-community/mathlib/pull/5032))
- [x] depends on: [#5132](https://github.com/leanprover-community/mathlib/pull/5132)
#### Estimated changes
Modified docs/references.bib

Created src/ring_theory/perfection.lean
- \+ *lemma* ext
- \+ *lemma* coeff_pth_root
- \+ *lemma* coeff_pow_p
- \+ *lemma* coeff_frobenius
- \+ *lemma* pth_root_frobenius
- \+ *lemma* frobenius_pth_root
- \+ *lemma* coeff_add_ne_zero
- \+ *lemma* coeff_ne_zero_of_le
- \+ *lemma* pre_val_mk
- \+ *lemma* pre_val_zero
- \+ *lemma* pre_val_mul
- \+ *lemma* pre_val_add
- \+ *lemma* v_p_lt_pre_val
- \+ *lemma* pre_val_eq_zero
- \+ *lemma* v_p_lt_val
- \+ *lemma* mul_ne_zero_of_pow_p_ne_zero
- \+ *lemma* coeff_nat_find_add_ne_zero
- \+ *lemma* val_aux_eq
- \+ *lemma* val_aux_zero
- \+ *lemma* val_aux_one
- \+ *lemma* val_aux_mul
- \+ *lemma* val_aux_add
- \+ *lemma* map_eq_zero
- \+ *def* monoid.perfection
- \+ *def* semiring.perfection
- \+ *def* ring.perfection
- \+ *def* coeff
- \+ *def* pth_root
- \+ *def* mod_p
- \+ *def* pre_tilt
- \+ *def* tilt



## [2020-12-01 13:25:41](https://github.com/leanprover-community/mathlib/commit/b7649bc)
doc(linear_algebra/determinant): Add a reference to is_basis.det ([#5167](https://github.com/leanprover-community/mathlib/pull/5167))
#### Estimated changes
Modified src/linear_algebra/determinant.lean



## [2020-12-01 13:25:39](https://github.com/leanprover-community/mathlib/commit/c088f65)
chore(data/equiv/perm): Move around lemmas about perm and swap ([#5153](https://github.com/leanprover-community/mathlib/pull/5153))
Only a very small fraction of `data/equiv/basic` needs knowledge of groups, moving out `perm_group` lets us cut the dependency.
The new `perm_group` file is then a good place for some of the lemmas in `group_theory/perm/sign`, especially those which just restate `equiv` lemmas in terms of `*` and `⁻¹` instead of `.trans` and `.symm`.
This moves a few lemmas about swap out of the `equiv.perm` namespace and into `equiv`, since `equiv.swap` is also in that namespace.
#### Estimated changes
Modified src/category_theory/graded_object.lean

Modified src/data/equiv/basic.lean
- \- *lemma* inv_apply_self
- \- *lemma* apply_inv_self
- \- *lemma* one_def
- \- *lemma* mul_def
- \- *lemma* inv_def
- \- *lemma* coe_mul
- \- *lemma* coe_one
- \- *lemma* swap_inv
- \- *lemma* swap_mul_self
- \- *theorem* mul_apply
- \- *theorem* one_apply

Modified src/data/equiv/mul_add.lean

Created src/group_theory/perm/basic.lean
- \+ *lemma* inv_apply_self
- \+ *lemma* apply_inv_self
- \+ *lemma* one_def
- \+ *lemma* mul_def
- \+ *lemma* inv_def
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* eq_inv_iff_eq
- \+ *lemma* inv_eq_iff_eq
- \+ *lemma* swap_inv
- \+ *lemma* swap_mul_self
- \+ *lemma* swap_mul_eq_mul_swap
- \+ *lemma* mul_swap_eq_swap_mul
- \+ *lemma* swap_mul_self_mul
- \+ *lemma* swap_mul_involutive
- \+ *lemma* swap_mul_eq_iff
- \+ *lemma* swap_mul_swap_mul_swap
- \+ *theorem* mul_apply
- \+ *theorem* one_apply

Modified src/group_theory/perm/sign.lean
- \- *lemma* eq_inv_iff_eq
- \- *lemma* inv_eq_iff_eq
- \- *lemma* swap_mul_eq_mul_swap
- \- *lemma* mul_swap_eq_swap_mul
- \- *lemma* swap_mul_self_mul
- \- *lemma* swap_mul_involutive
- \- *lemma* swap_mul_eq_iff
- \- *lemma* swap_mul_swap_mul_swap

Modified src/logic/embedding.lean



## [2020-12-01 13:25:37](https://github.com/leanprover-community/mathlib/commit/7188eae)
feat(linear_algebra): Add alternating multilinear maps ([#5102](https://github.com/leanprover-community/mathlib/pull/5102))
#### Estimated changes
Created src/linear_algebra/alternating.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_mk
- \+ *lemma* coe_multilinear_map
- \+ *lemma* to_multilinear_map_eq_coe
- \+ *lemma* coe_multilinear_map_mk
- \+ *lemma* map_add
- \+ *lemma* map_sub
- \+ *lemma* map_smul
- \+ *lemma* map_eq_zero_of_eq
- \+ *lemma* add_apply
- \+ *lemma* zero_apply
- \+ *lemma* neg_apply
- \+ *lemma* smul_apply
- \+ *lemma* map_update_self
- \+ *lemma* map_update_update
- \+ *lemma* map_swap_add
- \+ *lemma* map_add_swap
- \+ *lemma* map_swap
- \+ *lemma* map_perm
- \+ *lemma* map_congr_perm
- \+ *theorem* congr_fun
- \+ *theorem* congr_arg
- \+ *theorem* coe_inj
- \+ *theorem* ext
- \+ *theorem* ext_iff



## [2020-12-01 10:59:06](https://github.com/leanprover-community/mathlib/commit/ca3351f)
feat(rat/{basic,floor}) add floor lemmas ([#5148](https://github.com/leanprover-community/mathlib/pull/5148))
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *lemma* exists_eq_mul_div_num_and_eq_mul_div_denom

Modified src/data/rat/floor.lean
- \+ *lemma* floor_int_div_nat_eq_div
- \+ *lemma* int.mod_nat_eq_sub_mul_floor_rat_div
- \+ *lemma* nat.coprime_sub_mul_floor_rat_div_of_coprime
- \+ *lemma* num_lt_succ_floor_mul_denom
- \+ *lemma* fract_inv_num_lt_num_of_pos



## [2020-12-01 08:49:42](https://github.com/leanprover-community/mathlib/commit/2b074be)
feat(algebra/lie/basic): Define lattice structure for `lie_submodule`s ([#5146](https://github.com/leanprover-community/mathlib/pull/5146))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* coe_to_submodule
- \+ *lemma* mem_carrier
- \+ *lemma* ext
- \+ *lemma* coe_injective
- \+ *lemma* le_def
- \+ *lemma* bot_coe
- \+ *lemma* mem_bot
- \+ *lemma* top_coe
- \+ *lemma* mem_top
- \+ *lemma* Inf_coe_to_submodule
- \+ *lemma* Inf_coe
- \+ *lemma* Inf_glb
- \+ *lemma* add_eq_sup

Modified src/algebra/module/submodule.lean
- \+ *lemma* mem_carrier



## [2020-12-01 05:46:04](https://github.com/leanprover-community/mathlib/commit/a883152)
doc(data/mv_polynomial/basic): Fix documentation of mv_polynomial.monomial ([#5160](https://github.com/leanprover-community/mathlib/pull/5160))
The documenting comment for this function was obviously lifted from the single variable polynomial version, and did not make sense.
I'm not sure if this is the right comment, but it is at least better to what it was before.
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean



## [2020-12-01 01:20:08](https://github.com/leanprover-community/mathlib/commit/b846aa5)
chore(scripts): update nolints.txt ([#5158](https://github.com/leanprover-community/mathlib/pull/5158))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt

