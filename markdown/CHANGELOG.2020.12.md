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
- \- *lemma* formal_multilinear_series.bound_of_lt_radius
- \+/\- *def* formal_multilinear_series.change_origin
- \- *lemma* formal_multilinear_series.geometric_bound_of_lt_radius
- \+ *lemma* formal_multilinear_series.is_o_of_lt_radius
- \+ *lemma* formal_multilinear_series.is_o_one_of_lt_radius
- \+/\- *lemma* formal_multilinear_series.le_radius_of_bound
- \+ *lemma* formal_multilinear_series.le_radius_of_bound_nnreal
- \+ *lemma* formal_multilinear_series.le_radius_of_is_O
- \+ *lemma* formal_multilinear_series.lt_radius_of_is_O
- \+ *lemma* formal_multilinear_series.nnnorm_mul_pow_le_of_lt_radius
- \+ *lemma* formal_multilinear_series.norm_mul_pow_le_mul_pow_of_lt_radius
- \+ *lemma* formal_multilinear_series.norm_mul_pow_le_of_lt_radius
- \+/\- *lemma* formal_multilinear_series.radius_neg

Modified src/analysis/analytic/composition.lean


Added src/analysis/analytic/radius_liminf.lean
- \+ *lemma* formal_multilinear_series.radius_eq_liminf

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
- \+/\- *lemma* orthogonal_eq_inter
- \+/\- *lemma* submodule.Inf_orthogonal
- \+/\- *lemma* submodule.bot_orthogonal_eq_top
- \+/\- *lemma* submodule.inf_orthogonal
- \+/\- *lemma* submodule.infi_orthogonal
- \+/\- *lemma* submodule.is_closed_orthogonal
- \+/\- *lemma* submodule.le_orthogonal_orthogonal
- \+/\- *lemma* submodule.mem_orthogonal'
- \+/\- *lemma* submodule.mem_orthogonal
- \+/\- *lemma* submodule.orthogonal_disjoint
- \+/\- *lemma* submodule.orthogonal_le
- \+/\- *lemma* submodule.orthogonal_orthogonal
- \+/\- *lemma* submodule.top_orthogonal_eq_bot

Modified src/geometry/euclidean/basic.lean


Modified src/geometry/euclidean/monge_point.lean




## [2020-12-31 08:49:08](https://github.com/leanprover-community/mathlib/commit/cca6365)
feat(field_theory/galois): is_galois.tfae ([#5542](https://github.com/leanprover-community/mathlib/pull/5542))
This is a TFAE theorem for is_galois
#### Estimated changes
Modified src/field_theory/galois.lean
- \+ *theorem* is_galois.tfae



## [2020-12-31 06:04:17](https://github.com/leanprover-community/mathlib/commit/b04aeb5)
chore(algebra): move lemmas from ring_theory.algebra_tower to algebra.algebra.tower ([#5506](https://github.com/leanprover-community/mathlib/pull/5506))
Moved some basic lemmas from `ring_theory.algebra_tower` to `algebra.algebra.tower`.
#### Estimated changes
Added src/algebra/algebra/tower.lean
- \+ *def* algebra.lsmul
- \+ *lemma* algebra.lsmul_coe
- \+ *lemma* is_scalar_tower.algebra.ext
- \+ *theorem* is_scalar_tower.algebra_comap_eq
- \+ *theorem* is_scalar_tower.algebra_map_apply
- \+ *theorem* is_scalar_tower.algebra_map_eq
- \+ *theorem* is_scalar_tower.algebra_map_smul
- \+ *lemma* is_scalar_tower.coe_restrict_base'
- \+ *lemma* is_scalar_tower.coe_restrict_base
- \+ *lemma* is_scalar_tower.coe_to_alg_hom'
- \+ *lemma* is_scalar_tower.coe_to_alg_hom
- \+ *theorem* is_scalar_tower.of_algebra_map_eq'
- \+ *theorem* is_scalar_tower.of_algebra_map_eq
- \+ *theorem* is_scalar_tower.range_under_adjoin
- \+ *def* is_scalar_tower.restrict_base
- \+ *lemma* is_scalar_tower.restrict_base_apply
- \+ *def* is_scalar_tower.to_alg_hom
- \+ *lemma* is_scalar_tower.to_alg_hom_apply
- \+ *lemma* subalgebra.mem_res
- \+ *def* subalgebra.of_under
- \+ *def* subalgebra.res
- \+ *lemma* subalgebra.res_inj
- \+ *lemma* subalgebra.res_top
- \+ *theorem* submodule.smul_mem_span_smul'
- \+ *theorem* submodule.smul_mem_span_smul
- \+ *theorem* submodule.smul_mem_span_smul_of_mem
- \+ *theorem* submodule.span_smul

Modified src/ring_theory/algebra_tower.lean
- \- *lemma* is_scalar_tower.algebra.ext
- \- *theorem* is_scalar_tower.algebra_comap_eq
- \- *theorem* is_scalar_tower.algebra_map_apply
- \- *theorem* is_scalar_tower.algebra_map_eq
- \- *theorem* is_scalar_tower.algebra_map_smul
- \- *theorem* is_scalar_tower.of_algebra_map_eq
- \- *theorem* is_scalar_tower.range_under_adjoin
- \- *def* is_scalar_tower.restrict_base
- \- *lemma* is_scalar_tower.restrict_base_apply
- \- *theorem* is_scalar_tower.smul_left_comm
- \- *def* is_scalar_tower.to_alg_hom
- \- *lemma* is_scalar_tower.to_alg_hom_apply
- \- *lemma* subalgebra.mem_res
- \- *def* subalgebra.of_under
- \- *def* subalgebra.res
- \- *lemma* subalgebra.res_inj
- \- *lemma* subalgebra.res_top
- \- *theorem* submodule.smul_mem_span_smul'
- \- *theorem* submodule.smul_mem_span_smul
- \- *theorem* submodule.smul_mem_span_smul_of_mem
- \- *theorem* submodule.span_smul



## [2020-12-31 02:53:26](https://github.com/leanprover-community/mathlib/commit/a40f31f)
feat(data/tprod): finite products of types ([#5385](https://github.com/leanprover-community/mathlib/pull/5385))
This PR defined `list.tprod` as a finite product of types to transfer results from binary products to finitary products.
See module doc for more info.
#### Estimated changes
Added src/data/tprod.lean
- \+ *lemma* list.tprod.elim_mk
- \+ *lemma* list.tprod.elim_of_mem
- \+ *lemma* list.tprod.elim_of_ne
- \+ *lemma* list.tprod.elim_self
- \+ *lemma* list.tprod.ext
- \+ *lemma* list.tprod.fst_mk
- \+ *lemma* list.tprod.mk_elim
- \+ *def* list.tprod.pi_equiv_tprod
- \+ *lemma* list.tprod.snd_mk
- \+ *def* list.tprod
- \+ *lemma* set.elim_preimage_pi
- \+ *lemma* set.mk_preimage_tprod



## [2020-12-31 01:37:37](https://github.com/leanprover-community/mathlib/commit/611b73e)
chore(scripts): update nolints.txt ([#5540](https://github.com/leanprover-community/mathlib/pull/5540))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-12-30 23:15:52](https://github.com/leanprover-community/mathlib/commit/9c46cad)
feat(field_theory/algebraic_closure): algebraically closed fields have no nontrivial algebraic extensions ([#5537](https://github.com/leanprover-community/mathlib/pull/5537))
#### Estimated changes
Modified src/field_theory/algebraic_closure.lean
- \+ *lemma* is_alg_closed.algebra_map_surjective_of_is_algebraic
- \+ *lemma* is_alg_closed.algebra_map_surjective_of_is_integral

Modified src/ring_theory/algebraic.lean
- \+ *lemma* is_algebraic_iff_is_integral'



## [2020-12-30 20:43:17](https://github.com/leanprover-community/mathlib/commit/6e0d0fa)
chore(algebra/field): use `K` as a type variable ([#5535](https://github.com/leanprover-community/mathlib/pull/5535))
#### Estimated changes
Modified src/algebra/field.lean
- \+/\- *lemma* add_div'
- \+/\- *lemma* add_div
- \+/\- *lemma* add_div_eq_mul_add_div
- \+/\- *lemma* div_add'
- \+/\- *lemma* div_add_div
- \+/\- *lemma* div_add_div_same
- \+/\- *lemma* div_neg
- \+/\- *lemma* div_neg_eq_neg_div
- \+/\- *lemma* div_sub'
- \+/\- *lemma* div_sub_div
- \+/\- *lemma* div_sub_div_same
- \+/\- *lemma* inv_add_inv
- \+/\- *lemma* inv_sub_inv
- \+/\- *lemma* inverse_eq_has_inv
- \+/\- *lemma* mul_div_assoc'
- \+/\- *lemma* neg_div'
- \+/\- *lemma* neg_div
- \+/\- *lemma* neg_div_neg_eq
- \+/\- *lemma* one_div_add_one_div
- \+/\- *lemma* one_div_neg_eq_neg_one_div
- \+/\- *lemma* one_div_neg_one_eq_neg_one
- \+/\- *lemma* sub_div'
- \+/\- *lemma* sub_div



## [2020-12-30 20:43:15](https://github.com/leanprover-community/mathlib/commit/9988193)
feat(measure_theory): various additions ([#5389](https://github.com/leanprover-community/mathlib/pull/5389))
Some computations of measures on non-measurable sets
Some more measurability lemmas for pi-types
Cleanup in `measure_space`
#### Estimated changes
Modified src/data/equiv/list.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/measurable_space.lean
- \+ *lemma* is_measurable.Inter_fintype
- \+ *lemma* is_measurable.Union_fintype
- \+ *lemma* is_measurable.pi
- \+ *lemma* is_measurable.pi_fintype
- \+ *lemma* is_measurable.pi_univ
- \+/\- *lemma* is_measurable_pi
- \+ *lemma* is_measurable_pi_of_nonempty
- \+ *lemma* measurable.eval
- \+ *def* measurable_equiv.Pi_congr_right
- \+ *lemma* measurable_equiv.coe_mk
- \+ *lemma* measurable_equiv.coe_symm_mk
- \+ *lemma* measurable_pi_iff
- \+ *lemma* measurable_update
- \+ *lemma* nonempty_measurable_superset

Modified src/measure_theory/measure_space.lean
- \+/\- *def* completion
- \+/\- *theorem* is_measurable.diff_null
- \+/\- *theorem* is_measurable.is_null_measurable
- \+/\- *theorem* is_null_measurable.Union_nat
- \+/\- *theorem* is_null_measurable.compl
- \+/\- *theorem* is_null_measurable.diff_null
- \+/\- *theorem* is_null_measurable.union_null
- \+/\- *def* is_null_measurable
- \+/\- *theorem* is_null_measurable_iff
- \+/\- *theorem* is_null_measurable_measure_eq
- \+/\- *theorem* is_null_measurable_of_complete
- \+/\- *lemma* measure_theory.ae_all_iff
- \+/\- *lemma* measure_theory.ae_ball_iff
- \+/\- *lemma* measure_theory.ae_eq_empty
- \+/\- *lemma* measure_theory.ae_eq_refl
- \+/\- *lemma* measure_theory.ae_eq_symm
- \+/\- *lemma* measure_theory.ae_eq_trans
- \+/\- *lemma* measure_theory.ae_le_set
- \+/\- *lemma* measure_theory.ae_map_iff
- \+/\- *lemma* measure_theory.ae_of_all
- \+/\- *lemma* measure_theory.ae_restrict_eq
- \+/\- *lemma* measure_theory.ae_restrict_iff
- \+/\- *lemma* measure_theory.diff_ae_eq_self
- \+/\- *lemma* measure_theory.eventually_eq_dirac'
- \+/\- *lemma* measure_theory.eventually_eq_dirac
- \+/\- *lemma* measure_theory.exists_is_measurable_superset_iff_measure_eq_zero
- \+/\- *lemma* measure_theory.exists_is_measurable_superset_of_measure_eq_zero
- \+/\- *lemma* measure_theory.le_to_measure_apply
- \+/\- *lemma* measure_theory.le_to_outer_measure_caratheodory
- \+/\- *lemma* measure_theory.measure.Inf_apply
- \+/\- *theorem* measure_theory.measure.add_apply
- \+/\- *theorem* measure_theory.measure.coe_smul
- \+/\- *lemma* measure_theory.measure.compl_mem_cofinite
- \+/\- *lemma* measure_theory.measure.count_apply
- \+/\- *lemma* measure_theory.measure.count_apply_eq_top
- \+/\- *lemma* measure_theory.measure.count_apply_infinite
- \+/\- *lemma* measure_theory.measure.count_apply_lt_top
- \+/\- *lemma* measure_theory.measure.dirac_apply'
- \+/\- *lemma* measure_theory.measure.dirac_apply
- \+/\- *lemma* measure_theory.measure.dirac_apply_of_mem
- \+/\- *lemma* measure_theory.measure.ext
- \+/\- *lemma* measure_theory.measure.ext_iff
- \+/\- *lemma* measure_theory.measure.finite_at_principal
- \+/\- *def* measure_theory.measure.is_complete
- \+/\- *lemma* measure_theory.measure.le_lift_linear_apply
- \+ *theorem* measure_theory.measure.le_map_apply
- \+/\- *lemma* measure_theory.measure.le_sum
- \+/\- *lemma* measure_theory.measure.map_comap_subtype_coe
- \+/\- *lemma* measure_theory.measure.measure_univ_eq_zero
- \+/\- *lemma* measure_theory.measure.mem_cofinite
- \+/\- *def* measure_theory.measure.of_measurable
- \+/\- *lemma* measure_theory.measure.of_measurable_apply
- \+/\- *lemma* measure_theory.measure.restrict_Inf_eq_Inf_restrict
- \+/\- *lemma* measure_theory.measure.restrict_Union
- \+/\- *lemma* measure_theory.measure.restrict_Union_apply
- \+/\- *lemma* measure_theory.measure.restrict_Union_apply_eq_supr
- \+/\- *lemma* measure_theory.measure.restrict_Union_le
- \+/\- *lemma* measure_theory.measure.restrict_add_restrict_compl
- \+/\- *lemma* measure_theory.measure.restrict_apply
- \+/\- *lemma* measure_theory.measure.restrict_apply_eq_zero'
- \+/\- *lemma* measure_theory.measure.restrict_apply_eq_zero
- \+/\- *lemma* measure_theory.measure.restrict_compl_add_restrict
- \+/\- *lemma* measure_theory.measure.restrict_congr_meas
- \+/\- *lemma* measure_theory.measure.restrict_congr_mono
- \+/\- *lemma* measure_theory.measure.restrict_eq_zero
- \+/\- *lemma* measure_theory.measure.restrict_le_self
- \+/\- *lemma* measure_theory.measure.restrict_restrict
- \+/\- *lemma* measure_theory.measure.restrict_sum
- \+/\- *lemma* measure_theory.measure.restrict_to_outer_measure_eq_to_outer_measure_restrict
- \+/\- *lemma* measure_theory.measure.restrict_union
- \+/\- *lemma* measure_theory.measure.restrict_union_add_inter
- \+/\- *lemma* measure_theory.measure.restrict_union_apply
- \+/\- *lemma* measure_theory.measure.restrict_union_congr
- \+/\- *theorem* measure_theory.measure.smul_apply
- \+/\- *lemma* measure_theory.measure.sub_apply
- \+/\- *def* measure_theory.measure.sum
- \+/\- *lemma* measure_theory.measure.sum_apply
- \+/\- *lemma* measure_theory.measure.supr_restrict_spanning_sets
- \+/\- *lemma* measure_theory.measure.to_outer_measure_injective
- \+/\- *lemma* measure_theory.measure_Union
- \+/\- *theorem* measure_theory.measure_Union_le
- \+/\- *lemma* measure_theory.measure_Union_null
- \+/\- *lemma* measure_theory.measure_Union_null_iff
- \+/\- *lemma* measure_theory.measure_compl
- \+/\- *lemma* measure_theory.measure_congr
- \+/\- *lemma* measure_theory.measure_countable
- \+/\- *lemma* measure_theory.measure_diff
- \+ *lemma* measure_theory.measure_eq_infi'
- \+/\- *lemma* measure_theory.measure_eq_infi
- \+/\- *lemma* measure_theory.measure_eq_inter_diff
- \+/\- *lemma* measure_theory.measure_eq_trim
- \+/\- *lemma* measure_theory.measure_finite
- \+/\- *lemma* measure_theory.measure_if
- \+/\- *lemma* measure_theory.measure_mono_ae
- \+/\- *lemma* measure_theory.measure_union_add_inter
- \+/\- *lemma* measure_theory.measure_union_null
- \+/\- *lemma* measure_theory.measure_union_null_iff
- \+/\- *lemma* measure_theory.mem_ae_map_iff
- \+/\- *lemma* measure_theory.mem_dirac_ae_iff
- \+/\- *def* measure_theory.outer_measure.to_measure
- \+/\- *lemma* measure_theory.restrict_congr_set
- \+/\- *lemma* measure_theory.restrict_mono_ae
- \+/\- *lemma* measure_theory.tendsto_measure_Inter
- \+/\- *lemma* measure_theory.tendsto_measure_Union
- \+/\- *lemma* measure_theory.to_measure_apply
- \+/\- *lemma* measure_theory.to_measure_to_outer_measure
- \+/\- *lemma* measure_theory.to_outer_measure_apply
- \+/\- *lemma* measure_theory.to_outer_measure_to_measure
- \+/\- *lemma* measure_theory.union_ae_eq_right
- \+/\- *lemma* metric.bounded.finite_measure
- \+/\- *theorem* null_is_null_measurable
- \+/\- *def* null_measurable

Modified src/measure_theory/prod.lean
- \+ *lemma* measure_theory.measure.prod_prod_le



## [2020-12-30 19:29:20](https://github.com/leanprover-community/mathlib/commit/f1d2bc6)
feat(order/lattice_intervals): lattice structures on intervals in lattices ([#5496](https://github.com/leanprover-community/mathlib/pull/5496))
Defines (semi-)lattice structures on intervals in lattices
#### Estimated changes
Added src/order/lattice_intervals.lean
- \+ *def* set.Icc.bounded_lattice
- \+ *def* set.Icc.order_bot
- \+ *def* set.Icc.order_top
- \+ *def* set.Icc.semilattice_inf_bot
- \+ *def* set.Icc.semilattice_inf_top
- \+ *def* set.Icc.semilattice_sup_bot
- \+ *def* set.Icc.semilattice_sup_top
- \+ *lemma* set.Ici.coe_bot
- \+ *lemma* set.Ici.coe_top
- \+ *def* set.Ico.order_bot
- \+ *def* set.Ico.semilattice_inf_bot
- \+ *lemma* set.Iic.coe_bot
- \+ *lemma* set.Iic.coe_top
- \+ *def* set.Ioc.order_top
- \+ *def* set.Ioc.semilattice_sup_top



## [2020-12-30 17:33:54](https://github.com/leanprover-community/mathlib/commit/16320e2)
chore(topology/algebra/infinite_sum): refactor `tsum_mul_left/right` ([#5533](https://github.com/leanprover-community/mathlib/pull/5533))
* move old lemmas to `summable` namespace;
* add new `tsum_mul_left` and `tsum_mul_right` that work in a `division_ring` without a `summable` assumption.
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/analysis/normed_space/banach.lean


Modified src/data/real/cardinality.lean


Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum.nonneg
- \+ *lemma* has_sum.nonpos
- \+ *lemma* summable.tsum_mul_left
- \+ *lemma* summable.tsum_mul_right
- \+/\- *lemma* tsum_mul_left
- \+/\- *lemma* tsum_mul_right

Modified src/topology/instances/nnreal.lean
- \+ *lemma* nnreal.tsum_mul_left
- \+ *lemma* nnreal.tsum_mul_right



## [2020-12-30 17:33:52](https://github.com/leanprover-community/mathlib/commit/958c407)
chore(analysis/normed_space/basic): a few lemmas about `nnnorm` ([#5532](https://github.com/leanprover-community/mathlib/pull/5532))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* coe_nnnorm
- \+ *lemma* mem_emetric_ball_0_iff
- \+ *lemma* normed_field.nnnorm_div
- \+ *lemma* normed_field.nnnorm_fpow
- \+ *def* normed_field.nnnorm_hom
- \+ *lemma* normed_field.nnnorm_mul
- \+ *lemma* normed_field.nnnorm_pow
- \+ *lemma* normed_field.nnnorm_prod



## [2020-12-30 15:51:17](https://github.com/leanprover-community/mathlib/commit/b15bb06)
feat(topology/instances/ennreal): a sufficient condition for `f : (Σ i, β i) → ℝ` to be summable ([#5531](https://github.com/leanprover-community/mathlib/pull/5531))
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+ *lemma* nnreal.summable_sigma
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
- \- *lemma* ennreal.le_of_forall_lt_one_mul_lt
- \+ *lemma* ennreal.le_of_forall_nnreal_lt

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.le_of_forall_lt_one_mul_le
- \- *lemma* nnreal.le_of_forall_lt_one_mul_lt
- \+ *lemma* nnreal.lt_div_iff
- \+ *lemma* nnreal.mul_lt_of_lt_div

Modified src/measure_theory/integration.lean


Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.le_of_forall_lt_one_mul_le



## [2020-12-30 15:51:11](https://github.com/leanprover-community/mathlib/commit/c82be35)
feat(analysis/normed_space/inner_product): orthogonal complement lemmas ([#5474](https://github.com/leanprover-community/mathlib/pull/5474))
The orthogonal complement of a subspace is closed.  The orthogonal complement of the orthogonal complement of a complete subspace is itself.
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *def* inner_right
- \+ *lemma* inner_right_apply
- \+ *lemma* inner_right_coe
- \+ *lemma* orthogonal_eq_inter
- \+ *lemma* submodule.exists_sum_mem_mem_orthogonal
- \+ *lemma* submodule.is_closed_orthogonal
- \+ *lemma* submodule.orthogonal_orthogonal
- \+ *lemma* submodule.sup_orthogonal_of_complete_space



## [2020-12-30 13:05:48](https://github.com/leanprover-community/mathlib/commit/7a03171)
chore(order/rel_iso): add some missing lemmas ([#5492](https://github.com/leanprover-community/mathlib/pull/5492))
Also define `order_iso.trans`.
#### Estimated changes
Modified src/order/rel_iso.lean
- \+ *lemma* order_embedding.coe_subtype
- \+ *def* order_embedding.subtype
- \+ *lemma* order_iso.coe_trans
- \+ *lemma* order_iso.map_bot'
- \+/\- *lemma* order_iso.map_bot
- \+ *lemma* order_iso.map_top'
- \+/\- *lemma* order_iso.map_top
- \+ *theorem* order_iso.symm_apply_eq
- \+ *lemma* order_iso.symm_injective
- \+ *lemma* order_iso.symm_symm
- \+ *def* order_iso.trans
- \+ *lemma* order_iso.trans_apply
- \+ *theorem* rel_embedding.coe_trans
- \+/\- *theorem* rel_embedding.trans_apply
- \+ *lemma* rel_iso.default_def
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
- \+ *lemma* filter.tendsto.at_bot_mul
- \+ *lemma* filter.tendsto.at_bot_mul_neg
- \+ *lemma* filter.tendsto.mul_at_bot
- \+ *lemma* filter.tendsto.neg_mul_at_bot
- \+ *lemma* filter.tendsto.neg_mul_at_top
- \+/\- *lemma* linear_ordered_add_comm_group.tendsto_nhds
- \- *lemma* neg_preimage_closure
- \+/\- *lemma* nhds_eq_infi_abs_sub
- \+/\- *lemma* order_topology_of_nhds_abs



## [2020-12-30 10:07:47](https://github.com/leanprover-community/mathlib/commit/5e86589)
chore(data/nat/enat): some useful lemmas ([#5517](https://github.com/leanprover-community/mathlib/pull/5517))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *theorem* nat.find_le

Modified src/data/nat/enat.lean
- \+ *lemma* enat.coe_le_iff
- \+ *lemma* enat.coe_lt_iff
- \+ *lemma* enat.dom_coe
- \+ *lemma* enat.dom_of_le_of_dom
- \+/\- *lemma* enat.dom_of_le_some
- \+ *lemma* enat.dom_of_lt
- \+ *lemma* enat.eq_top_iff_forall_le
- \+ *lemma* enat.eq_top_iff_forall_lt
- \+ *def* enat.find
- \+ *lemma* enat.find_dom
- \+ *lemma* enat.find_eq_top_iff
- \+ *lemma* enat.find_get
- \+ *lemma* enat.find_le
- \+ *lemma* enat.get_coe'
- \+/\- *lemma* enat.get_coe
- \+/\- *lemma* enat.get_le_get
- \+ *lemma* enat.le_coe_iff
- \+ *lemma* enat.le_def
- \+ *lemma* enat.lt_coe_iff
- \+ *lemma* enat.lt_def
- \+ *lemma* enat.lt_find
- \+ *lemma* enat.lt_find_iff
- \+/\- *def* enat.to_with_top
- \+/\- *lemma* enat.to_with_top_zero'

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
- \+ *theorem* concave_on_of_deriv2_nonpos
- \+ *theorem* concave_on_of_deriv_antimono
- \+ *theorem* concave_on_open_of_deriv2_nonpos
- \+ *theorem* concave_on_univ_of_deriv2_nonpos
- \+ *theorem* concave_on_univ_of_deriv_antimono
- \+ *theorem* convex_on_open_of_deriv2_nonneg

Modified src/analysis/convex/specific_functions.lean
- \+ *lemma* concave_on_log_Iio
- \+ *lemma* concave_on_log_Ioi



## [2020-12-29 07:47:35](https://github.com/leanprover-community/mathlib/commit/8e413eb)
feat(order/bounded_lattice): define atoms, coatoms, and simple lattices ([#5471](https://github.com/leanprover-community/mathlib/pull/5471))
Defines `is_atom`, `is_coatom`, and `is_simple_lattice`
Refactors `ideal.is_maximal` to use `is_coatom`, the new definition is definitionally equal to the old one
#### Estimated changes
Added src/order/atoms.lean
- \+ *lemma* eq_bot_or_eq_of_le_atom
- \+ *lemma* eq_top_or_eq_of_coatom_le
- \+ *def* is_atom
- \+ *lemma* is_atom_iff_is_coatom_dual
- \+ *lemma* is_atom_top
- \+ *def* is_coatom
- \+ *lemma* is_coatom_bot
- \+ *lemma* is_coatom_iff_is_atom_dual
- \+ *theorem* is_simple_lattice_iff_is_atom_top
- \+ *theorem* is_simple_lattice_iff_is_coatom_bot
- \+ *theorem* is_simple_lattice_iff_is_simple_lattice_order_dual

Modified src/order/bounded_lattice.lean
- \+ *lemma* bot_ne_top
- \+ *lemma* top_ne_bot

Modified src/order/order_dual.lean


Modified src/ring_theory/ideal/basic.lean
- \+/\- *def* ideal.is_maximal



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
- \+ *lemma* polynomial.nat_degree_X_pow



## [2020-12-28 15:03:21](https://github.com/leanprover-community/mathlib/commit/d245c4e)
feat(polynomial/algebra_map): aeval_comp ([#5511](https://github.com/leanprover-community/mathlib/pull/5511))
Basic lemma about aeval
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* polynomial.aeval_comp



## [2020-12-28 13:55:13](https://github.com/leanprover-community/mathlib/commit/f1f2ca6)
feat(category_theory/limits): preserves limits of equivalent shape ([#5515](https://github.com/leanprover-community/mathlib/pull/5515))
#### Estimated changes
Modified src/category_theory/limits/preserves/basic.lean
- \+ *def* category_theory.limits.preserves_colimits_of_shape_of_equiv
- \+ *def* category_theory.limits.preserves_limits_of_shape_of_equiv



## [2020-12-28 03:40:12](https://github.com/leanprover-community/mathlib/commit/6d1d4c1)
chore(scripts): update nolints.txt ([#5514](https://github.com/leanprover-community/mathlib/pull/5514))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-12-28 00:38:46](https://github.com/leanprover-community/mathlib/commit/6d0b415)
feat(data/list/basic): nth_zero ([#5513](https://github.com/leanprover-community/mathlib/pull/5513))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.nth_zero



## [2020-12-27 16:40:59](https://github.com/leanprover-community/mathlib/commit/5c8c122)
chore(analysis/analytic/basic): speed up slow lemmas ([#5507](https://github.com/leanprover-community/mathlib/pull/5507))
Removes slow `tidy`s from `formal_multilinear_series.change_origin_radius` and `formal_multilinear_series.change_origin_has_sum`
#### Estimated changes
Modified src/analysis/analytic/basic.lean




## [2020-12-27 04:21:55](https://github.com/leanprover-community/mathlib/commit/1e75453)
feat(data/list/basic): filter_map retains prefix ([#5453](https://github.com/leanprover-community/mathlib/pull/5453))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.is_prefix.filter_map
- \+ *lemma* list.is_prefix.reduce_option



## [2020-12-26 22:54:39](https://github.com/leanprover-community/mathlib/commit/f7e728a)
feat(data/list/range): enum is a zip ([#5457](https://github.com/leanprover-community/mathlib/pull/5457))
#### Estimated changes
Modified src/data/list/range.lean
- \+ *lemma* list.enum_eq_zip_range
- \+ *lemma* list.enum_from_eq_zip_range'
- \+ *lemma* list.unzip_enum_eq_prod
- \+ *lemma* list.unzip_enum_from_eq_prod

Modified src/data/list/zip.lean
- \+ *lemma* list.map_prod_left_eq_zip
- \+ *lemma* list.map_prod_right_eq_zip
- \+ *lemma* list.zip_of_prod



## [2020-12-26 20:38:16](https://github.com/leanprover-community/mathlib/commit/ae60bb9)
chore(topology/algebra/order): add `continuous_on.surj_on_of_tendsto` ([#5502](https://github.com/leanprover-community/mathlib/pull/5502))
* rename `surjective_of_continuous` to `continuous.surjective` and `surjective_of_continuous'` to `continuous.surjective'`;
* add `continuous_on.surj_on_of_tendsto` and `continuous_on.surj_on_of_tendsto'`
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean


Modified src/data/real/sqrt.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* continuous.surjective'
- \+ *lemma* continuous.surjective
- \+ *lemma* continuous_on.surj_on_of_tendsto'
- \+ *lemma* continuous_on.surj_on_of_tendsto
- \- *lemma* surjective_of_continuous'
- \- *lemma* surjective_of_continuous



## [2020-12-26 09:47:44](https://github.com/leanprover-community/mathlib/commit/add100a)
feat(ring_theory/perfection): perfection.map ([#5503](https://github.com/leanprover-community/mathlib/pull/5503))
#### Estimated changes
Modified src/ring_theory/perfection.lean
- \+ *lemma* perfection.coeff_map
- \+ *lemma* perfection.coeff_pow_p'
- \+ *lemma* perfection.hom_ext
- \+ *def* perfection.map
- \+ *lemma* perfection_map.comp_equiv'
- \+ *lemma* perfection_map.comp_equiv
- \+ *lemma* perfection_map.comp_map
- \+ *lemma* perfection_map.comp_symm_equiv'
- \+ *lemma* perfection_map.comp_symm_equiv
- \+ *lemma* perfection_map.equiv_apply
- \+ *lemma* perfection_map.hom_ext
- \+ *lemma* perfection_map.map_eq_map
- \+ *lemma* perfection_map.map_map



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
- \+/\- *lemma* homeomorph.coinduced_eq
- \+ *lemma* homeomorph.comap_nhds_eq
- \+ *lemma* homeomorph.image_closure
- \+ *lemma* homeomorph.image_preimage
- \+/\- *lemma* homeomorph.induced_eq
- \+ *lemma* homeomorph.is_closed_image
- \+ *lemma* homeomorph.is_closed_preimage
- \+ *lemma* homeomorph.is_open_image
- \+ *lemma* homeomorph.map_nhds_eq
- \+ *lemma* homeomorph.nhds_eq_comap
- \+ *lemma* homeomorph.preimage_closure
- \+ *lemma* homeomorph.preimage_image

Modified src/topology/maps.lean




## [2020-12-25 18:38:51](https://github.com/leanprover-community/mathlib/commit/726b7bf)
feat(analysis/specific_limits): a `tfae` about "`f` grows exponentially slower than `R ^ n`" ([#5488](https://github.com/leanprover-community/mathlib/pull/5488))
Also add supporting lemmas here and there.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *theorem* pow_bit0_nonneg
- \+ *theorem* pow_bit0_pos
- \+/\- *theorem* pow_two_nonneg
- \+/\- *theorem* pow_two_pos_of_ne_zero

Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* abs_pow
- \+/\- *theorem* one_add_mul_le_pow
- \+/\- *theorem* one_add_sub_mul_le_pow
- \+ *theorem* pow_bit1_neg_iff
- \+ *theorem* pow_bit1_nonneg_iff
- \+ *theorem* pow_bit1_nonpos_iff
- \+ *theorem* pow_bit1_pos_iff
- \+ *lemma* sign_cases_of_C_mul_pow_nonneg
- \+ *lemma* strict_mono_pow_bit1

Modified src/analysis/asymptotics.lean
- \+ *theorem* asymptotics.is_O_one_nat_at_top_iff
- \+/\- *theorem* asymptotics.is_O_with_zero_right_iff
- \+/\- *theorem* asymptotics.is_O_zero_right_iff
- \+/\- *theorem* asymptotics.is_o_zero_right_iff

Modified src/analysis/specific_limits.lean
- \+ *lemma* is_O_pow_pow_of_le_left
- \+ *lemma* tfae_exists_lt_is_o_pow

Modified src/data/real/nnreal.lean
- \+/\- *lemma* nnreal.coe_pow

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.nonneg_of_eventually_pow_nonneg
- \+ *lemma* filter.tendsto_bit0_at_bot
- \+ *lemma* filter.tendsto_bit0_at_top
- \+ *lemma* filter.tendsto_bit1_at_top
- \+ *lemma* filter.zero_pow_eventually_eq



## [2020-12-25 17:10:05](https://github.com/leanprover-community/mathlib/commit/d968a61)
feat(category_theory/limits): yoneda reflects limits ([#5447](https://github.com/leanprover-community/mathlib/pull/5447))
yoneda and coyoneda jointly reflect limits
#### Estimated changes
Modified src/category_theory/limits/yoneda.lean
- \+ *def* category_theory.coyoneda_jointly_reflects_limits
- \+ *def* category_theory.yoneda_jointly_reflects_limits



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
- \+ *lemma* list.filter_map_append
- \+ *lemma* list.reduce_option_append
- \+ *lemma* list.reduce_option_concat
- \+ *lemma* list.reduce_option_concat_of_some
- \+ *lemma* list.reduce_option_cons_of_none
- \+ *lemma* list.reduce_option_cons_of_some
- \+ *lemma* list.reduce_option_length_eq_iff
- \+ *lemma* list.reduce_option_length_le
- \+ *lemma* list.reduce_option_length_lt_iff
- \+ *lemma* list.reduce_option_map
- \+ *lemma* list.reduce_option_mem_iff
- \+ *lemma* list.reduce_option_nil
- \+ *lemma* list.reduce_option_nth_iff
- \+ *lemma* list.reduce_option_singleton



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
- \+ *lemma* alg_hom.coe_mk'
- \+ *def* alg_hom.mk'
- \- *def* alg_hom_int
- \- *def* alg_hom_nat
- \+ *lemma* ring_hom.map_rat_algebra_map
- \+/\- *def* ring_hom.to_int_alg_hom
- \+ *def* ring_hom.to_nat_alg_hom
- \+ *def* ring_hom.to_rat_alg_hom

Modified src/ring_theory/power_series/well_known.lean
- \+/\- *lemma* power_series.coeff_exp
- \+/\- *def* power_series.cos
- \+/\- *def* power_series.exp
- \+/\- *lemma* power_series.map_cos
- \+/\- *lemma* power_series.map_exp
- \+/\- *lemma* power_series.map_sin
- \+/\- *def* power_series.sin



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
- \+/\- *lemma* list.chain.induction
- \+/\- *lemma* list.chain.induction_head
- \+/\- *lemma* list.exists_chain_of_relation_refl_trans_gen
- \+ *lemma* list.relation_refl_trans_gen_of_exists_chain



## [2020-12-23 22:08:07](https://github.com/leanprover-community/mathlib/commit/ceae529)
chore(group_theory/coset): Make `quotient_group.mk` an abbreviation ([#5377](https://github.com/leanprover-community/mathlib/pull/5377))
This allows simp lemmas about `quotient.mk'` to apply here, which currently do not apply.
The definition doesn't seem interesting enough to be semireducible.
#### Estimated changes
Modified src/group_theory/coset.lean
- \- *def* quotient_group.mk



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
- \+ *lemma* free_group.ext_hom

Modified src/linear_algebra/clifford_algebra.lean


Modified src/linear_algebra/dfinsupp.lean


Modified src/linear_algebra/exterior_algebra.lean


Modified src/linear_algebra/tensor_algebra.lean


Modified src/tactic/ext.lean




## [2020-12-23 18:58:42](https://github.com/leanprover-community/mathlib/commit/e2edba5)
chore(order/filter/basic): make `filter.univ_mem_sets` a `simp` lemma ([#5464](https://github.com/leanprover-community/mathlib/pull/5464))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.insert_nth_succ_nil

Modified src/data/rel.lean
- \+/\- *lemma* rel.core_univ

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.univ_mem_sets

Modified src/order/filter/partial.lean


Modified src/topology/list.lean
- \+/\- *lemma* nhds_nil



## [2020-12-23 18:58:38](https://github.com/leanprover-community/mathlib/commit/d3a5e06)
feat(data/dlist/basic): dlist singleton and of_list simp lemmas ([#5461](https://github.com/leanprover-community/mathlib/pull/5461))
#### Estimated changes
Modified src/data/dlist/basic.lean
- \+ *lemma* dlist_lazy
- \+ *lemma* dlist_singleton



## [2020-12-23 16:10:29](https://github.com/leanprover-community/mathlib/commit/fd9268c)
feat(data/list/basic): lemmas about scanl ([#5454](https://github.com/leanprover-community/mathlib/pull/5454))
#### Estimated changes
Modified src/data/list/basic.lean
- \+/\- *lemma* list.length_scanl
- \+ *lemma* list.length_singleton
- \+ *lemma* list.nth_le_succ_scanl
- \+ *lemma* list.nth_le_zero_scanl
- \+ *lemma* list.nth_succ_scanl
- \+ *lemma* list.nth_zero_scanl
- \+ *lemma* list.scanl_cons
- \+ *lemma* list.scanl_nil



## [2020-12-23 12:11:42](https://github.com/leanprover-community/mathlib/commit/eb5cf25)
chore(analysis/asymptotics): a few more lemmas ([#5482](https://github.com/leanprover-community/mathlib/pull/5482))
* golf some proofs;
* `x ^ n = o (y ^ n)` as `n → ∞` provided that `0 ≤ x < y`;
* lemmas about `is_O _ _ ⊤` etc;
* if `is_O f g cofinite`, then for some `C>0` and any `x` such that `g x ≠ 0` we have `∥f x∥≤C*∥g x∥`.
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *theorem* asymptotics.bound_of_is_O_cofinite
- \+ *theorem* asymptotics.bound_of_is_O_nat_at_top
- \+ *theorem* asymptotics.is_O_cofinite_iff
- \+ *theorem* asymptotics.is_O_nat_at_top_iff
- \+ *lemma* asymptotics.is_O_top
- \+ *lemma* asymptotics.is_O_with_top
- \+ *lemma* asymptotics.is_o_top

Modified src/analysis/specific_limits.lean
- \+ *lemma* is_o_pow_pow_of_abs_lt_left
- \+ *lemma* is_o_pow_pow_of_lt_left
- \+/\- *lemma* tendsto_pow_at_top_nhds_0_of_lt_1

Modified src/order/filter/cofinite.lean
- \+ *lemma* filter.eventually_cofinite



## [2020-12-23 09:41:22](https://github.com/leanprover-community/mathlib/commit/435b97a)
feat(ring_theory/witt_vector): the comparison between W(F_p) and Z_p ([#5164](https://github.com/leanprover-community/mathlib/pull/5164))
This PR is the culmination of the Witt vector project. We prove that the
ring of Witt vectors over `zmod p` is isomorphic to the ring of `p`-adic
numbers.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.symm_to_ring_hom_comp_to_ring_hom
- \+ *lemma* ring_equiv.to_ring_hom_comp_symm_to_ring_hom

Added src/ring_theory/witt_vector/compare.lean
- \+ *lemma* truncated_witt_vector.card_zmod
- \+ *lemma* truncated_witt_vector.char_p_zmod
- \+ *lemma* truncated_witt_vector.commutes'
- \+ *lemma* truncated_witt_vector.commutes
- \+ *lemma* truncated_witt_vector.commutes_symm'
- \+ *lemma* truncated_witt_vector.commutes_symm
- \+ *lemma* truncated_witt_vector.eq_of_le_of_cast_pow_eq_zero
- \+ *def* truncated_witt_vector.zmod_equiv_trunc
- \+ *lemma* truncated_witt_vector.zmod_equiv_trunc_apply
- \+ *def* witt_vector.equiv
- \+ *def* witt_vector.from_padic_int
- \+ *lemma* witt_vector.from_padic_int_comp_to_padic_int
- \+ *lemma* witt_vector.from_padic_int_comp_to_padic_int_ext
- \+ *def* witt_vector.to_padic_int
- \+ *lemma* witt_vector.to_padic_int_comp_from_padic_int
- \+ *lemma* witt_vector.to_padic_int_comp_from_padic_int_ext
- \+ *def* witt_vector.to_zmod_pow
- \+ *lemma* witt_vector.to_zmod_pow_compat
- \+ *lemma* witt_vector.zmod_equiv_trunc_compat



## [2020-12-23 04:12:18](https://github.com/leanprover-community/mathlib/commit/d5adbde)
feat(data/list/basic): prefix simplifying iff lemmas ([#5452](https://github.com/leanprover-community/mathlib/pull/5452))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.cons_prefix_iff
- \+ *lemma* list.map_prefix
- \+ *lemma* list.prefix_take_le_iff



## [2020-12-23 01:30:34](https://github.com/leanprover-community/mathlib/commit/24f71d7)
chore(scripts): update nolints.txt ([#5483](https://github.com/leanprover-community/mathlib/pull/5483))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-12-22 20:56:38](https://github.com/leanprover-community/mathlib/commit/eba2a79)
feat(data/list/zip): length of zip_with, nth_le of zip ([#5455](https://github.com/leanprover-community/mathlib/pull/5455))
#### Estimated changes
Modified src/data/list/zip.lean
- \+ *theorem* list.length_zip_with
- \+ *lemma* list.lt_length_left_of_zip
- \+ *lemma* list.lt_length_left_of_zip_with
- \+ *lemma* list.lt_length_right_of_zip
- \+ *lemma* list.lt_length_right_of_zip_with
- \+ *lemma* list.nth_le_zip
- \+ *lemma* list.nth_le_zip_with
- \+ *theorem* list.zip_with_cons_cons
- \+ *theorem* list.zip_with_nil_left
- \+ *theorem* list.zip_with_nil_right



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
- \+/\- *lemma* has_deriv_at_iff_tendsto_slope
- \+ *lemma* has_deriv_within_at_Iio_iff_Iic
- \+ *lemma* has_deriv_within_at_Ioi_iff_Ici
- \+ *lemma* has_deriv_within_at_diff_singleton
- \+/\- *lemma* has_deriv_within_at_iff_tendsto_slope'
- \+/\- *lemma* has_deriv_within_at_iff_tendsto_slope

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
- \+ *lemma* complex.continuous_of_real

Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* complex.continuous_at_tan
- \+/\- *lemma* complex.deriv_tan
- \+/\- *lemma* complex.differentiable_at_tan
- \+/\- *lemma* complex.has_deriv_at_tan
- \+ *lemma* complex.tendsto_abs_tan_at_top
- \+ *lemma* complex.tendsto_abs_tan_of_cos_eq_zero
- \+ *lemma* real.continuous_at_tan
- \- *lemma* real.continuous_tan
- \+/\- *lemma* real.deriv_tan
- \- *lemma* real.deriv_tan_of_mem_Ioo
- \+/\- *lemma* real.differentiable_at_tan
- \+/\- *lemma* real.has_deriv_at_tan
- \+ *lemma* real.tan_pi_div_two
- \+ *lemma* real.tendsto_abs_tan_at_top
- \+ *lemma* real.tendsto_abs_tan_of_cos_eq_zero



## [2020-12-22 17:05:09](https://github.com/leanprover-community/mathlib/commit/d569d63)
refactor(analysis/inner_product_space, geometry/euclidean) range of orthogonal projection ([#5408](https://github.com/leanprover-community/mathlib/pull/5408))
Previously, the orthogonal projection was defined for all subspaces of an inner product space, with the junk value `id` if the space was not complete; then all nontrivial lemmas required a hypothesis of completeness (and nonemptiness for the affine orthogonal projection).  Change this to a definition only for subspaces `K` satisfying `[complete_space K]` (and `[nonempty K]` for the affine orthogonal projection).
Previously, the orthogonal projection was a linear map from `E` to `E`.  Redefine it to be a linear map from `E` to `K`.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Orthogonal.20projection)
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+/\- *lemma* eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
- \+ *lemma* eq_orthogonal_projection_of_eq_submodule
- \+/\- *lemma* eq_orthogonal_projection_of_mem_of_inner_eq_zero
- \+/\- *def* orthogonal_projection
- \- *lemma* orthogonal_projection_def
- \+/\- *def* orthogonal_projection_fn
- \+/\- *lemma* orthogonal_projection_fn_eq
- \+/\- *lemma* orthogonal_projection_fn_inner_eq_zero
- \+/\- *lemma* orthogonal_projection_fn_mem
- \+/\- *lemma* orthogonal_projection_inner_eq_zero
- \- *lemma* orthogonal_projection_mem
- \- *def* orthogonal_projection_of_complete

Modified src/data/finset/basic.lean


Modified src/geometry/euclidean/basic.lean
- \+/\- *lemma* euclidean_geometry.dist_orthogonal_projection_eq_zero_iff
- \+/\- *lemma* euclidean_geometry.dist_orthogonal_projection_ne_zero_of_not_mem
- \+/\- *lemma* euclidean_geometry.dist_reflection
- \+/\- *lemma* euclidean_geometry.dist_reflection_eq_of_mem
- \+ *lemma* euclidean_geometry.eq_orthogonal_projection_of_eq_subspace
- \+ *lemma* euclidean_geometry.eq_reflection_of_eq_subspace
- \+/\- *lemma* euclidean_geometry.inter_eq_singleton_orthogonal_projection
- \+/\- *lemma* euclidean_geometry.inter_eq_singleton_orthogonal_projection_fn
- \+/\- *def* euclidean_geometry.orthogonal_projection
- \- *lemma* euclidean_geometry.orthogonal_projection_def
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_eq_self_iff
- \+/\- *def* euclidean_geometry.orthogonal_projection_fn
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_fn_eq
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_fn_mem
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_fn_mem_orthogonal
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_fn_vsub_mem_direction_orthogonal
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_linear
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_mem
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_mem_orthogonal
- \- *def* euclidean_geometry.orthogonal_projection_of_nonempty_of_complete
- \- *lemma* euclidean_geometry.orthogonal_projection_of_nonempty_of_complete_eq
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_orthogonal_projection
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_vadd_eq_self
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_vsub_mem_direction
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_vsub_mem_direction_orthogonal
- \+/\- *def* euclidean_geometry.reflection
- \+/\- *lemma* euclidean_geometry.reflection_apply
- \+/\- *lemma* euclidean_geometry.reflection_eq_iff_orthogonal_projection_eq
- \+/\- *lemma* euclidean_geometry.reflection_eq_self_iff
- \+/\- *lemma* euclidean_geometry.reflection_involutive
- \+/\- *lemma* euclidean_geometry.reflection_mem_of_le_of_mem
- \+/\- *lemma* euclidean_geometry.reflection_orthogonal_vadd
- \+/\- *lemma* euclidean_geometry.reflection_reflection
- \+/\- *lemma* euclidean_geometry.reflection_symm
- \+/\- *lemma* euclidean_geometry.reflection_vadd_smul_vsub_orthogonal_projection
- \+/\- *lemma* euclidean_geometry.vsub_orthogonal_projection_mem_direction
- \+/\- *lemma* euclidean_geometry.vsub_orthogonal_projection_mem_direction_orthogonal

Modified src/geometry/euclidean/circumcenter.lean
- \+/\- *lemma* euclidean_geometry.dist_eq_iff_dist_orthogonal_projection_eq
- \+/\- *lemma* euclidean_geometry.dist_set_eq_iff_dist_orthogonal_projection_eq
- \+/\- *lemma* euclidean_geometry.exists_dist_eq_iff_exists_dist_orthogonal_projection_eq

Modified src/geometry/euclidean/monge_point.lean


Modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* affine_subspace.coe_vadd
- \+ *lemma* affine_subspace.coe_vsub



## [2020-12-22 17:05:07](https://github.com/leanprover-community/mathlib/commit/0ff9068)
feat(data/finset/basic, topology/separation): add induction_on_union, separate, and separate_finset_of_t2 ([#5332](https://github.com/leanprover-community/mathlib/pull/5332))
prove lemma disjoint_finsets_opens_of_t2 showing that in a t2_space disjoint finsets have disjoint open neighbourhoods, using auxiliary lemma not_mem_finset_opens_of_t2.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.induction_on_union

Modified src/topology/separation.lean
- \+ *lemma* finset_disjoint_finset_opens_of_t2
- \+ *lemma* point_disjoint_finset_opens_of_t2
- \+ *lemma* separated.comm
- \+ *lemma* separated.empty_left
- \+ *lemma* separated.empty_right
- \+ *lemma* separated.symm
- \+ *lemma* separated.union_left
- \+ *lemma* separated.union_right
- \+ *def* separated



## [2020-12-22 13:47:43](https://github.com/leanprover-community/mathlib/commit/02ab90c)
chore(*): split some long lines ([#5470](https://github.com/leanprover-community/mathlib/pull/5470))
#### Estimated changes
Modified src/algebra/category/CommRing/colimits.lean
- \+/\- *lemma* CommRing.colimits.quot_add
- \+/\- *lemma* CommRing.colimits.quot_mul
- \+/\- *lemma* CommRing.colimits.quot_neg

Modified src/algebra/category/Group/limits.lean


Modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* is_unit.ne_zero

Modified src/algebra/ordered_group.lean


Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* filter.has_basis.uniform_continuous_on_iff
- \+/\- *lemma* mem_uniform_prod
- \+/\- *lemma* nhds_basis_uniformity'
- \+/\- *lemma* uniform_continuous_fst
- \+/\- *lemma* uniform_continuous_on_iff_restrict
- \+/\- *lemma* uniform_continuous_snd
- \+/\- *lemma* uniform_space.core_eq

Modified src/topology/uniform_space/completion.lean
- \+/\- *theorem* Cauchy.Cauchy_eq
- \+/\- *lemma* uniform_space.completion.extension_coe
- \+/\- *lemma* uniform_space.completion.extension_unique

Modified test/monotonicity/test_cases.lean




## [2020-12-22 07:50:26](https://github.com/leanprover-community/mathlib/commit/4ddae3d)
feat(ring_theory/power_series): define power series for `exp`, `sin`, `cos`, and `1 / (u - x)`. ([#5432](https://github.com/leanprover-community/mathlib/pull/5432))
This PR defines `power_series.exp` etc to be formal power series for the corresponding functions. Once we have a bridge to `is_analytic`, we should redefine `complex.exp` etc using these power series.
#### Estimated changes
Modified src/algebra/field.lean
- \+/\- *lemma* ring_hom.map_eq_zero

Modified src/algebra/group/units_hom.lean
- \+ *lemma* units.coe_map_inv

Modified src/analysis/calculus/formal_multilinear_series.lean


Modified src/data/complex/is_R_or_C.lean
- \+/\- *lemma* is_R_or_C.conj_eq_zero

Renamed src/ring_theory/power_series.lean to src/ring_theory/power_series/basic.lean
- \+/\- *lemma* mv_power_series.inv_of_unit_eq'
- \+/\- *lemma* mv_power_series.inv_of_unit_eq

Added src/ring_theory/power_series/well_known.lean
- \+ *lemma* power_series.coeff_exp
- \+ *lemma* power_series.coeff_inv_units_sub
- \+ *lemma* power_series.constant_coeff_inv_units_sub
- \+ *def* power_series.cos
- \+ *def* power_series.exp
- \+ *def* power_series.inv_units_sub
- \+ *lemma* power_series.inv_units_sub_mul_X
- \+ *lemma* power_series.inv_units_sub_mul_sub
- \+ *lemma* power_series.map_cos
- \+ *lemma* power_series.map_exp
- \+ *lemma* power_series.map_inv_units_sub
- \+ *lemma* power_series.map_sin
- \+ *def* power_series.sin



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
- \+/\- *lemma* semiconj_by.mul_right

Modified src/algebra/ordered_monoid.lean


Modified src/group_theory/monoid_localization.lean
- \+/\- *lemma* submonoid.localization_map.mul_equiv_of_localizations_apply
- \+/\- *lemma* submonoid.localization_map.mul_equiv_of_localizations_left_inv_apply
- \+/\- *lemma* submonoid.localization_map.mul_equiv_of_localizations_right_inv
- \+/\- *lemma* submonoid.localization_map.mul_equiv_of_localizations_right_inv_apply
- \+/\- *lemma* submonoid.localization_map.mul_equiv_of_localizations_symm_apply
- \+/\- *lemma* submonoid.localization_map.of_mul_equiv_of_dom_apply
- \+/\- *lemma* submonoid.localization_map.of_mul_equiv_of_localizations_apply
- \+/\- *lemma* submonoid.localization_map.of_mul_equiv_of_mul_equiv_apply

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
- \+ *lemma* equiv.image_preimage
- \+ *lemma* equiv.preimage_image
- \+/\- *lemma* equiv.symm_image_image

Modified src/data/set/basic.lean
- \+ *lemma* function.injective.preimage_image
- \+ *lemma* function.surjective.image_preimage
- \+/\- *theorem* set.image_preimage_eq
- \+/\- *lemma* set.preimage_eq_preimage

Modified src/order/semiconj_Sup.lean


Modified src/topology/homeomorph.lean


Modified src/topology/maps.lean


Modified src/topology/uniform_space/separation.lean




## [2020-12-21 20:56:39](https://github.com/leanprover-community/mathlib/commit/d2ae43f)
feat(data/list/basic): lemmas about nth of take and append ([#5449](https://github.com/leanprover-community/mathlib/pull/5449))
#### Estimated changes
Modified src/data/list/basic.lean
- \+/\- *lemma* list.nth_append
- \+ *lemma* list.nth_append_right
- \+ *lemma* list.nth_take
- \+ *lemma* list.nth_take_of_succ
- \+ *lemma* list.take_succ



## [2020-12-21 20:56:37](https://github.com/leanprover-community/mathlib/commit/3b9cbdf)
feat(data/ordmap): Ordered maps (like rb_map but better) ([#5353](https://github.com/leanprover-community/mathlib/pull/5353))
This cleans up an old mathlib branch from 2 years ago, so it probably isn't in very modern style, but it would be best to get it merged and kept up to date rather than leaving it to rot.
It is an implementation of size balanced ordered maps based on Haskell's `Data.Map.Strict`. The `ordnode` structure can be used directly if one is only interested in using it for programming purposes, and the `ordset` structure bundles the proofs so that you can prove theorems about inserting and deleting doing what you expect.
#### Estimated changes
Modified docs/overview.yaml


Modified src/algebra/order.lean
- \+ *def* cmp_le
- \+ *theorem* cmp_le_eq_cmp
- \+ *theorem* cmp_le_swap

Modified src/data/nat/dist.lean
- \+ *theorem* nat.dist_tri_left'
- \+ *theorem* nat.dist_tri_left
- \+ *theorem* nat.dist_tri_right'
- \+ *theorem* nat.dist_tri_right

Modified src/data/nat/psub.lean
- \+ *def* nat.psub'
- \+ *theorem* nat.psub'_eq_psub
- \+/\- *theorem* nat.psub_eq_none

Added src/data/ordmap/ordnode.lean
- \+ *def* ordnode.adjust_with
- \+ *def* ordnode.all
- \+ *def* ordnode.alter
- \+ *def* ordnode.amem
- \+ *def* ordnode.any
- \+ *def* ordnode.attach'
- \+ *def* ordnode.balance
- \+ *def* ordnode.balance_l
- \+ *def* ordnode.balance_r
- \+ *def* ordnode.delta
- \+ *def* ordnode.diff
- \+ *def* ordnode.disjoint
- \+ *def* ordnode.drop
- \+ *def* ordnode.drop_aux
- \+ *def* ordnode.drop_while
- \+ *def* ordnode.dual
- \+ *def* ordnode.emem
- \+ *def* ordnode.empty
- \+ *def* ordnode.equiv
- \+ *def* ordnode.erase
- \+ *def* ordnode.erase_max
- \+ *def* ordnode.erase_min
- \+ *def* ordnode.filter
- \+ *def* ordnode.find
- \+ *def* ordnode.find_ge
- \+ *def* ordnode.find_ge_aux
- \+ *def* ordnode.find_gt
- \+ *def* ordnode.find_gt_aux
- \+ *def* ordnode.find_index
- \+ *def* ordnode.find_index_aux
- \+ *def* ordnode.find_le
- \+ *def* ordnode.find_le_aux
- \+ *def* ordnode.find_lt
- \+ *def* ordnode.find_lt_aux
- \+ *def* ordnode.find_max'
- \+ *def* ordnode.find_max
- \+ *def* ordnode.find_min'
- \+ *def* ordnode.find_min
- \+ *def* ordnode.fold
- \+ *def* ordnode.foldl
- \+ *def* ordnode.foldr
- \+ *def* ordnode.glue
- \+ *def* ordnode.image
- \+ *def* ordnode.insert'
- \+ *def* ordnode.insert_max
- \+ *def* ordnode.insert_min
- \+ *def* ordnode.insert_with
- \+ *def* ordnode.inter
- \+ *def* ordnode.is_subset
- \+ *def* ordnode.is_subset_aux
- \+ *def* ordnode.link
- \+ *def* ordnode.map
- \+ *def* ordnode.mem
- \+ *def* ordnode.merge
- \+ *def* ordnode.node'
- \+ *def* ordnode.nth
- \+ *def* ordnode.of_asc_list
- \+ *def* ordnode.of_asc_list_aux₁
- \+ *def* ordnode.of_asc_list_aux₂
- \+ *def* ordnode.of_list'
- \+ *def* ordnode.of_list
- \+ *def* ordnode.partition
- \+ *def* ordnode.pmap
- \+ *def* ordnode.powerset
- \+ *def* ordnode.ratio
- \+ *def* ordnode.remove_nth
- \+ *def* ordnode.repr
- \+ *def* ordnode.size
- \+ *def* ordnode.span
- \+ *def* ordnode.split3
- \+ *def* ordnode.split
- \+ *def* ordnode.split_at
- \+ *def* ordnode.split_at_aux
- \+ *def* ordnode.split_max'
- \+ *def* ordnode.split_max
- \+ *def* ordnode.split_min'
- \+ *def* ordnode.split_min
- \+ *def* ordnode.take
- \+ *def* ordnode.take_aux
- \+ *def* ordnode.take_while
- \+ *def* ordnode.to_list
- \+ *def* ordnode.to_rev_list
- \+ *def* ordnode.union
- \+ *def* ordnode.update_with

Added src/data/ordmap/ordset.lean
- \+ *theorem* ordnode.all.imp
- \+ *theorem* ordnode.all_balance'
- \+ *theorem* ordnode.all_balance_l
- \+ *theorem* ordnode.all_balance_r
- \+ *theorem* ordnode.all_dual
- \+ *theorem* ordnode.all_iff_forall
- \+ *theorem* ordnode.all_node'
- \+ *theorem* ordnode.all_node3_l
- \+ *theorem* ordnode.all_node3_r
- \+ *theorem* ordnode.all_node4_l
- \+ *theorem* ordnode.all_node4_r
- \+ *theorem* ordnode.all_rotate_l
- \+ *theorem* ordnode.all_rotate_r
- \+ *theorem* ordnode.all_singleton
- \+ *theorem* ordnode.any.imp
- \+ *theorem* ordnode.any_iff_exists
- \+ *theorem* ordnode.any_singleton
- \+ *def* ordnode.balance'
- \+ *theorem* ordnode.balance_eq_balance'
- \+ *def* ordnode.balance_l'
- \+ *theorem* ordnode.balance_l_eq_balance'
- \+ *theorem* ordnode.balance_l_eq_balance
- \+ *def* ordnode.balance_r'
- \+ *theorem* ordnode.balance_r_eq_balance'
- \+ *theorem* ordnode.balance_sz_dual
- \+ *theorem* ordnode.balanced.dual
- \+ *def* ordnode.balanced
- \+ *theorem* ordnode.balanced_sz.symm
- \+ *def* ordnode.balanced_sz
- \+ *theorem* ordnode.balanced_sz_down
- \+ *theorem* ordnode.balanced_sz_up
- \+ *theorem* ordnode.balanced_sz_zero
- \+ *theorem* ordnode.bounded.dual
- \+ *theorem* ordnode.bounded.dual_iff
- \+ *theorem* ordnode.bounded.mem_gt
- \+ *theorem* ordnode.bounded.mem_lt
- \+ *theorem* ordnode.bounded.mono_left
- \+ *theorem* ordnode.bounded.mono_right
- \+ *theorem* ordnode.bounded.of_gt
- \+ *theorem* ordnode.bounded.of_lt
- \+ *theorem* ordnode.bounded.to_lt
- \+ *theorem* ordnode.bounded.to_nil
- \+ *theorem* ordnode.bounded.to_sep
- \+ *theorem* ordnode.bounded.trans_left
- \+ *theorem* ordnode.bounded.trans_right
- \+ *theorem* ordnode.bounded.weak
- \+ *theorem* ordnode.bounded.weak_left
- \+ *theorem* ordnode.bounded.weak_right
- \+ *def* ordnode.bounded
- \+ *theorem* ordnode.delta_lt_false
- \+ *theorem* ordnode.dual_balance'
- \+ *theorem* ordnode.dual_balance_l
- \+ *theorem* ordnode.dual_balance_r
- \+ *theorem* ordnode.dual_dual
- \+ *theorem* ordnode.dual_erase_max
- \+ *theorem* ordnode.dual_erase_min
- \+ *theorem* ordnode.dual_insert
- \+ *theorem* ordnode.dual_node'
- \+ *theorem* ordnode.dual_node3_l
- \+ *theorem* ordnode.dual_node3_r
- \+ *theorem* ordnode.dual_node4_l
- \+ *theorem* ordnode.dual_node4_r
- \+ *theorem* ordnode.dual_rotate_l
- \+ *theorem* ordnode.dual_rotate_r
- \+ *theorem* ordnode.emem_iff_all
- \+ *theorem* ordnode.emem_iff_mem_to_list
- \+ *theorem* ordnode.equiv_iff
- \+ *theorem* ordnode.erase_max.valid
- \+ *theorem* ordnode.erase_min.valid
- \+ *theorem* ordnode.find_max'_all
- \+ *theorem* ordnode.find_max'_dual
- \+ *theorem* ordnode.find_max_dual
- \+ *theorem* ordnode.find_min'_all
- \+ *theorem* ordnode.find_min'_dual
- \+ *theorem* ordnode.find_min_dual
- \+ *theorem* ordnode.foldr_cons_eq_to_list
- \+ *theorem* ordnode.insert'.valid
- \+ *theorem* ordnode.insert'_eq_insert_with
- \+ *theorem* ordnode.insert.valid
- \+ *theorem* ordnode.insert_eq_insert_with
- \+ *theorem* ordnode.insert_with.valid
- \+ *theorem* ordnode.insert_with.valid_aux
- \+ *theorem* ordnode.length_to_list'
- \+ *theorem* ordnode.length_to_list
- \+ *theorem* ordnode.merge_nil_left
- \+ *theorem* ordnode.merge_nil_right
- \+ *theorem* ordnode.merge_node
- \+ *def* ordnode.node3_l
- \+ *theorem* ordnode.node3_l_size
- \+ *def* ordnode.node3_r
- \+ *theorem* ordnode.node3_r_size
- \+ *def* ordnode.node4_l
- \+ *theorem* ordnode.node4_l_size
- \+ *def* ordnode.node4_r
- \+ *theorem* ordnode.not_le_delta
- \+ *theorem* ordnode.raised.add_left
- \+ *theorem* ordnode.raised.add_right
- \+ *theorem* ordnode.raised.dist_le'
- \+ *theorem* ordnode.raised.dist_le
- \+ *theorem* ordnode.raised.right
- \+ *def* ordnode.raised
- \+ *theorem* ordnode.raised_iff
- \+ *def* ordnode.real_size
- \+ *def* ordnode.rotate_l
- \+ *def* ordnode.rotate_r
- \+ *theorem* ordnode.size_balance'
- \+ *theorem* ordnode.size_balance_l
- \+ *theorem* ordnode.size_balance_r
- \+ *theorem* ordnode.size_dual
- \+ *theorem* ordnode.size_eq_real_size
- \+ *theorem* ordnode.sized.balance'
- \+ *theorem* ordnode.sized.dual
- \+ *theorem* ordnode.sized.dual_iff
- \+ *theorem* ordnode.sized.eq_node'
- \+ *theorem* ordnode.sized.induction
- \+ *theorem* ordnode.sized.node'
- \+ *theorem* ordnode.sized.node3_l
- \+ *theorem* ordnode.sized.node3_r
- \+ *theorem* ordnode.sized.node4_l
- \+ *theorem* ordnode.sized.pos
- \+ *theorem* ordnode.sized.rotate_l
- \+ *theorem* ordnode.sized.rotate_l_size
- \+ *theorem* ordnode.sized.rotate_r
- \+ *theorem* ordnode.sized.rotate_r_size
- \+ *theorem* ordnode.sized.size_eq
- \+ *theorem* ordnode.sized.size_eq_zero
- \+ *def* ordnode.sized
- \+ *theorem* ordnode.split_max_eq
- \+ *theorem* ordnode.split_min_eq
- \+ *theorem* ordnode.to_list_nil
- \+ *theorem* ordnode.to_list_node
- \+ *theorem* ordnode.valid'.balance'
- \+ *theorem* ordnode.valid'.balance'_aux
- \+ *theorem* ordnode.valid'.balance'_lemma
- \+ *theorem* ordnode.valid'.balance
- \+ *theorem* ordnode.valid'.balance_l
- \+ *theorem* ordnode.valid'.balance_l_aux
- \+ *theorem* ordnode.valid'.balance_r
- \+ *theorem* ordnode.valid'.balance_r_aux
- \+ *theorem* ordnode.valid'.dual
- \+ *theorem* ordnode.valid'.dual_iff
- \+ *theorem* ordnode.valid'.erase_max_aux
- \+ *theorem* ordnode.valid'.erase_min_aux
- \+ *theorem* ordnode.valid'.glue
- \+ *theorem* ordnode.valid'.glue_aux
- \+ *theorem* ordnode.valid'.left
- \+ *theorem* ordnode.valid'.merge_aux
- \+ *theorem* ordnode.valid'.merge_aux₁
- \+ *theorem* ordnode.valid'.merge_lemma
- \+ *theorem* ordnode.valid'.mono_left
- \+ *theorem* ordnode.valid'.mono_right
- \+ *theorem* ordnode.valid'.node'
- \+ *theorem* ordnode.valid'.node3_l
- \+ *theorem* ordnode.valid'.node3_r
- \+ *theorem* ordnode.valid'.node4_l
- \+ *theorem* ordnode.valid'.node4_l_lemma₁
- \+ *theorem* ordnode.valid'.node4_l_lemma₂
- \+ *theorem* ordnode.valid'.node4_l_lemma₃
- \+ *theorem* ordnode.valid'.node4_l_lemma₄
- \+ *theorem* ordnode.valid'.node4_l_lemma₅
- \+ *theorem* ordnode.valid'.node
- \+ *theorem* ordnode.valid'.of_gt
- \+ *theorem* ordnode.valid'.of_lt
- \+ *theorem* ordnode.valid'.right
- \+ *theorem* ordnode.valid'.rotate_l
- \+ *theorem* ordnode.valid'.rotate_l_lemma₁
- \+ *theorem* ordnode.valid'.rotate_l_lemma₂
- \+ *theorem* ordnode.valid'.rotate_l_lemma₃
- \+ *theorem* ordnode.valid'.rotate_l_lemma₄
- \+ *theorem* ordnode.valid'.rotate_r
- \+ *theorem* ordnode.valid'.trans_left
- \+ *theorem* ordnode.valid'.trans_right
- \+ *theorem* ordnode.valid'.valid
- \+ *theorem* ordnode.valid'_nil
- \+ *theorem* ordnode.valid'_singleton
- \+ *theorem* ordnode.valid.dual
- \+ *theorem* ordnode.valid.dual_iff
- \+ *theorem* ordnode.valid.left
- \+ *theorem* ordnode.valid.merge
- \+ *theorem* ordnode.valid.right
- \+ *theorem* ordnode.valid.size_eq
- \+ *def* ordnode.valid
- \+ *theorem* ordnode.valid_nil
- \+ *theorem* ordnode.valid_singleton
- \+ *def* ordset.empty
- \+ *theorem* ordset.empty_iff
- \+ *def* ordset.insert'
- \+ *def* ordset.nil
- \+ *def* ordset.size
- \+ *def* ordset

Modified src/order/basic.lean
- \+ *theorem* order_dual.cmp_le_flip
- \+ *theorem* order_dual.linear_order.dual_dual
- \+ *theorem* order_dual.partial_order.dual_dual
- \+ *theorem* order_dual.preorder.dual_dual



## [2020-12-21 17:48:50](https://github.com/leanprover-community/mathlib/commit/bc3ad25)
feat(linear_algebra/tensor_algebra): Add missing lemmas about subtraction ([#5428](https://github.com/leanprover-community/mathlib/pull/5428))
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean
- \+ *theorem* linear_map.map_sub₂
- \+ *lemma* tensor_product.sub_tmul
- \+ *lemma* tensor_product.tmul_sub



## [2020-12-21 17:48:49](https://github.com/leanprover-community/mathlib/commit/34d5750)
feat(data/option/basic): lemmas on map of none and congr ([#5424](https://github.com/leanprover-community/mathlib/pull/5424))
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* option.map_congr
- \+ *lemma* option.map_eq_none'
- \+ *lemma* option.map_eq_none



## [2020-12-21 16:45:47](https://github.com/leanprover-community/mathlib/commit/0ed425f)
feat(ring_theory/perfection): define characteristic predicate of perfection ([#5386](https://github.com/leanprover-community/mathlib/pull/5386))
Name changes:
- `perfect_field` --> `perfect_ring` (generalization)
- `semiring.perfection` --> `ring.perfection`
- Original `ring.perfection` deleted.
#### Estimated changes
Modified src/field_theory/perfect_closure.lean
- \+/\- *lemma* coe_frobenius_equiv
- \+/\- *lemma* coe_frobenius_equiv_symm
- \+ *theorem* commute_frobenius_pth_root
- \+/\- *theorem* eq_pth_root_iff
- \+/\- *def* frobenius_equiv
- \+/\- *theorem* frobenius_pth_root
- \+ *lemma* injective_pow_p
- \+/\- *theorem* left_inverse_pth_root_frobenius
- \+/\- *theorem* monoid_hom.map_iterate_pth_root
- \+/\- *theorem* monoid_hom.map_pth_root
- \+/\- *def* perfect_closure.lift
- \+/\- *def* pth_root
- \+/\- *theorem* pth_root_eq_iff
- \+/\- *theorem* pth_root_frobenius
- \+ *theorem* pth_root_pow_p'
- \+ *theorem* pth_root_pow_p
- \+ *theorem* right_inverse_pth_root_frobenius
- \+/\- *theorem* ring_hom.map_iterate_pth_root
- \+/\- *theorem* ring_hom.map_pth_root

Modified src/ring_theory/perfection.lean
- \+ *def* perfection.coeff
- \+ *lemma* perfection.coeff_add_ne_zero
- \+ *lemma* perfection.coeff_frobenius
- \+ *lemma* perfection.coeff_iterate_frobenius'
- \+ *lemma* perfection.coeff_iterate_frobenius
- \+ *lemma* perfection.coeff_mk
- \+ *lemma* perfection.coeff_ne_zero_of_le
- \+ *lemma* perfection.coeff_pow_p
- \+ *lemma* perfection.coeff_pth_root
- \+ *lemma* perfection.ext
- \+ *lemma* perfection.frobenius_pth_root
- \+ *def* perfection.lift
- \+ *def* perfection.pth_root
- \+ *lemma* perfection.pth_root_frobenius
- \+ *lemma* perfection_map.id
- \+ *lemma* perfection_map.mk'
- \+ *lemma* perfection_map.of
- \- *def* ring.perfection.coeff
- \- *lemma* ring.perfection.coeff_add_ne_zero
- \- *lemma* ring.perfection.coeff_frobenius
- \- *lemma* ring.perfection.coeff_ne_zero_of_le
- \- *lemma* ring.perfection.coeff_pow_p
- \- *lemma* ring.perfection.coeff_pth_root
- \- *lemma* ring.perfection.ext
- \- *lemma* ring.perfection.frobenius_pth_root
- \- *def* ring.perfection.pth_root
- \- *lemma* ring.perfection.pth_root_frobenius
- \+/\- *def* ring.perfection
- \- *def* semiring.perfection



## [2020-12-21 15:29:49](https://github.com/leanprover-community/mathlib/commit/96a2aa1)
feat(ring_theory/roots_of_unity): add minimal_polynomial_eq_pow ([#5444](https://github.com/leanprover-community/mathlib/pull/5444))
This is the main result about minimal polynomial of primitive roots of unity: `μ` and `μ ^ p` have the same minimal polynomial.
The proof is a little long, but I don't see how I can split it: it is entirely by contradiction, so any lemma extracted from it would start with a false assumption and at the end it would be used only in this proof.
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* is_primitive_root.minimal_polynomial_eq_pow



## [2020-12-21 14:00:44](https://github.com/leanprover-community/mathlib/commit/c5c02ec)
feat(category_theory/yoneda): add iso_comp_punit ([#5448](https://github.com/leanprover-community/mathlib/pull/5448))
A presheaf P : C^{op} -> Type v is isomorphic to the composition of P with the coyoneda functor Type v -> Type v associated to `punit`.
[This is useful for developing the theory of sheaves taking values in a general category]
#### Estimated changes
Modified src/category_theory/yoneda.lean
- \+ *def* category_theory.coyoneda.iso_comp_punit



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
- \- *def* category_theory.Sheaf
- \+ *def* category_theory.SheafOfTypes
- \+ *def* category_theory.SheafOfTypes_to_presheaf
- \- *def* category_theory.Sheaf_to_presheaf

Modified src/category_theory/sites/types.lean
- \+/\- *lemma* category_theory.eval_app
- \+/\- *def* category_theory.yoneda'



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

Modified src/analysis/special_functions/trigonometric.lean


Modified src/data/rat/floor.lean


Modified src/data/real/golden_ratio.lean


Modified src/data/real/nnreal.lean
- \- *theorem* nnreal.mul_ne_zero'

Modified src/field_theory/splitting_field.lean


Modified src/linear_algebra/affine_space/ordered.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/perfection.lean


Added src/tactic/field_simp.lean


Modified src/tactic/interactive.lean


Modified test/ring.lean


Modified test/ring_exp.lean




## [2020-12-20 09:21:32](https://github.com/leanprover-community/mathlib/commit/5010738)
feat(topology/algebra/ordered): continuity of `abs` ([#5412](https://github.com/leanprover-community/mathlib/pull/5412))
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* continuous.abs
- \+ *lemma* continuous_abs
- \+ *lemma* continuous_at.abs
- \+ *lemma* continuous_on.abs
- \+ *lemma* continuous_within_at.abs
- \+ *lemma* filter.tendsto.abs
- \+ *lemma* tendsto_abs_nhds_within_zero

Modified src/topology/basic.lean


Modified src/topology/instances/real.lean
- \- *lemma* rat.continuous_abs
- \- *lemma* real.continuous_abs



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
- \+ *lemma* is_galois.of_card_aut_eq_findim
- \+ *lemma* is_galois.of_fixed_field_eq_bot
- \+ *lemma* is_galois.of_separable_splitting_field
- \+ *lemma* is_galois.of_separable_splitting_field_aux



## [2020-12-19 17:55:35](https://github.com/leanprover-community/mathlib/commit/e22fb94)
chore(data/nat/cast,algebra/ordered_group): 2 trivial lemmas ([#5436](https://github.com/leanprover-community/mathlib/pull/5436))
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* inv_lt_self

Modified src/data/nat/cast.lean
- \+ *lemma* with_top.one_le_iff_pos



## [2020-12-19 17:55:33](https://github.com/leanprover-community/mathlib/commit/5de6757)
chore(algebra/ordered_group): deduplicate ([#5403](https://github.com/leanprover-community/mathlib/pull/5403))
I deleted many `a_of_b` lemmas for which `a_iff_b` existed, then restored (most? all?) of them using `alias` command.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/ordered_group.lean
- \- *lemma* add_le_of_le_sub_left
- \- *lemma* add_le_of_le_sub_right
- \- *lemma* add_lt_of_lt_sub_left
- \- *lemma* add_lt_of_lt_sub_right
- \- *lemma* exists_gt_zero
- \+ *lemma* exists_zero_lt
- \- *lemma* le_add_of_neg_le_sub_left
- \- *lemma* le_add_of_neg_le_sub_right
- \- *lemma* le_add_of_sub_left_le
- \- *lemma* le_add_of_sub_right_le
- \- *lemma* le_of_sub_nonneg
- \- *lemma* le_of_sub_nonpos
- \- *lemma* le_sub_left_of_add_le
- \- *lemma* le_sub_right_of_add_le
- \- *lemma* lt_add_of_neg_lt_sub_left
- \- *lemma* lt_add_of_neg_lt_sub_right
- \- *lemma* lt_add_of_sub_left_lt
- \- *lemma* lt_add_of_sub_right_lt
- \- *lemma* lt_of_sub_neg
- \- *lemma* lt_of_sub_pos
- \- *lemma* lt_sub_left_of_add_lt
- \- *lemma* lt_sub_right_of_add_lt
- \- *lemma* neg_le_sub_left_of_le_add
- \- *lemma* neg_le_sub_right_of_le_add
- \- *lemma* neg_lt_sub_left_of_lt_add
- \- *lemma* neg_lt_sub_right_of_lt_add
- \+ *lemma* sub_le_of_abs_sub_le_left
- \+ *lemma* sub_le_of_abs_sub_le_right
- \- *lemma* sub_le_of_sub_le
- \- *lemma* sub_le_self
- \+/\- *lemma* sub_le_self_iff
- \- *lemma* sub_left_le_of_le_add
- \- *lemma* sub_left_lt_of_lt_add
- \+ *lemma* sub_lt_of_abs_sub_lt_left
- \+ *lemma* sub_lt_of_abs_sub_lt_right
- \- *lemma* sub_lt_of_sub_lt
- \- *lemma* sub_lt_self
- \+/\- *lemma* sub_lt_self_iff
- \- *lemma* sub_lt_sub_of_le_of_lt
- \- *lemma* sub_lt_sub_of_lt_of_le
- \- *lemma* sub_neg_of_lt
- \- *lemma* sub_nonneg_of_le
- \- *lemma* sub_nonpos_of_le
- \- *lemma* sub_pos_of_lt
- \- *lemma* sub_right_le_of_le_add
- \- *lemma* sub_right_lt_of_lt_add

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
- \+ *lemma* filter.tendsto_abs_at_bot_at_top
- \+ *lemma* filter.tendsto_abs_at_top_at_top

Modified src/topology/algebra/ordered.lean
- \+ *lemma* eventually_abs_sub_lt
- \+/\- *lemma* linear_ordered_add_comm_group.tendsto_nhds
- \+ *lemma* nhds_eq_infi_abs_sub
- \+/\- *lemma* order_topology_of_nhds_abs
- \- *lemma* tendsto_abs_at_top_at_top



## [2020-12-19 17:55:28](https://github.com/leanprover-community/mathlib/commit/154a024)
feat(measure_theory/lp_space): add lemmas about the monotonicity of the Lp seminorm ([#5395](https://github.com/leanprover-community/mathlib/pull/5395))
Also add a lemma mem_Lp.const_smul for a normed space.
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *lemma* ennreal.lintegral_Lp_mul_le_Lq_mul_Lr

Modified src/measure_theory/lp_space.lean
- \+ *lemma* ℒp_space.mem_ℒp.const_smul
- \+ *lemma* ℒp_space.mem_ℒp.integrable
- \+ *lemma* ℒp_space.mem_ℒp.mem_ℒp_of_exponent_le
- \+ *lemma* ℒp_space.snorm_le_snorm_mul_rpow_measure_univ
- \+ *lemma* ℒp_space.snorm_le_snorm_of_exponent_le
- \+ *lemma* ℒp_space.snorm_smul_le_mul_snorm



## [2020-12-19 17:55:27](https://github.com/leanprover-community/mathlib/commit/ce385a0)
feat(ring_theory/roots_of_unity): lemmas about minimal polynomial ([#5393](https://github.com/leanprover-community/mathlib/pull/5393))
Three results about the minimal polynomial of `μ` and `μ ^ p`, where `μ` is a primitive root of unity. These are preparatory lemmas to prove that the two minimal polynomials are equal.
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* is_primitive_root.minimal_polynomial_dvd_expand
- \+ *lemma* is_primitive_root.minimal_polynomial_dvd_mod_p
- \+ *lemma* is_primitive_root.minimal_polynomial_dvd_pow_mod
- \+ *lemma* is_primitive_root.pow_of_prime



## [2020-12-19 16:17:17](https://github.com/leanprover-community/mathlib/commit/c55721d)
chore(analysis/calculus/{fderiv,deriv}): `f x ≠ f a` for `x ≈ a`, `x ≠ a` if `∥z∥ ≤ C * ∥f' z∥` ([#5420](https://github.com/leanprover-community/mathlib/pull/5420))
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *lemma* asymptotics.is_O.eq_zero_imp
- \+ *lemma* asymptotics.is_O_with.eq_zero_imp

Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_at.eventually_ne

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_at.eventually_ne
- \+ *lemma* has_fderiv_within_at.eventually_ne

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* linear_map.bound_of_antilipschitz

Modified src/topology/local_homeomorph.lean
- \+ *lemma* local_homeomorph.eventually_ne_nhds_within



## [2020-12-19 14:59:26](https://github.com/leanprover-community/mathlib/commit/ff830d7)
feat(ring_theory/witt_vector): redefine subtraction using witt_sub polynomial ([#5405](https://github.com/leanprover-community/mathlib/pull/5405))
#### Estimated changes
Modified src/ring_theory/witt_vector/basic.lean
- \+ *lemma* witt_vector.map_fun.sub

Modified src/ring_theory/witt_vector/defs.lean
- \+ *lemma* witt_vector.sub_coeff
- \+ *lemma* witt_vector.witt_sub_vars

Modified src/ring_theory/witt_vector/is_poly.lean
- \- *lemma* witt_vector.sub_coeff
- \- *lemma* witt_vector.sub_eq



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
- \+/\- *lemma* category_theory.equivalence.functor_map_inj_iff
- \+/\- *lemma* category_theory.equivalence.inverse_map_inj_iff

Added src/category_theory/essential_image.lean
- \+ *def* category_theory.functor.ess_image.get_iso
- \+ *lemma* category_theory.functor.ess_image.of_iso
- \+ *lemma* category_theory.functor.ess_image.of_nat_iso
- \+ *def* category_theory.functor.ess_image.witness
- \+ *def* category_theory.functor.ess_image
- \+ *lemma* category_theory.functor.ess_image_eq_of_nat_iso
- \+ *def* category_theory.functor.ess_image_inclusion
- \+ *lemma* category_theory.functor.obj_mem_ess_image
- \+ *def* category_theory.functor.obj_obj_preimage_iso
- \+ *def* category_theory.functor.obj_preimage
- \+ *def* category_theory.functor.to_ess_image
- \+ *def* category_theory.functor.to_ess_image_comp_essential_image_inclusion

Modified src/category_theory/full_subcategory.lean


Modified src/category_theory/groupoid.lean


Modified src/category_theory/limits/shapes/normal_mono.lean


Modified src/topology/category/Compactum.lean




## [2020-12-19 08:21:41](https://github.com/leanprover-community/mathlib/commit/0bb665c)
chore(ring_theory/power_series): review, golf ([#5431](https://github.com/leanprover-community/mathlib/pull/5431))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_ite_index
- \+ *lemma* finset.prod_sigma'

Modified src/analysis/analytic/composition.lean


Modified src/data/complex/exponential.lean


Modified src/data/nat/enat.lean
- \+/\- *lemma* enat.coe_lt_top

Modified src/number_theory/arithmetic_function.lean


Modified src/ring_theory/power_series.lean
- \+/\- *def* mv_power_series.coeff
- \+ *lemma* mv_power_series.coeff_add_monomial_mul
- \+ *lemma* mv_power_series.coeff_add_mul_monomial
- \- *lemma* mv_power_series.coeff_monomial'
- \+ *lemma* mv_power_series.coeff_monomial_mul
- \+ *lemma* mv_power_series.coeff_monomial_ne
- \+ *lemma* mv_power_series.coeff_monomial_same
- \+ *lemma* mv_power_series.coeff_mul_monomial
- \+ *lemma* mv_power_series.eq_of_coeff_monomial_ne_zero
- \+ *lemma* mv_power_series.map_C
- \+ *lemma* mv_power_series.map_X
- \+ *lemma* mv_power_series.map_monomial
- \+/\- *def* mv_power_series.monomial
- \+/\- *lemma* mv_power_series.monomial_zero_eq_C
- \+ *lemma* mv_power_series.monomial_zero_one
- \+/\- *def* power_series.coeff
- \- *lemma* power_series.coeff_monomial'
- \+ *lemma* power_series.coeff_monomial_same
- \+/\- *def* power_series.monomial
- \+/\- *lemma* power_series.monomial_zero_eq_C
- \+/\- *lemma* power_series.order_eq_top



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
- \+ *lemma* multilinear_map.map_update_zero



## [2020-12-19 02:24:54](https://github.com/leanprover-community/mathlib/commit/5e057c9)
feat(data/fin): trans and id lemmas for fin.cast ([#5415](https://github.com/leanprover-community/mathlib/pull/5415))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.cast_refl
- \+ *lemma* fin.cast_trans



## [2020-12-18 23:34:58](https://github.com/leanprover-community/mathlib/commit/0e9a77c)
feat(data/nat/basic): succ_lt_succ_iff ([#5422](https://github.com/leanprover-community/mathlib/pull/5422))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.succ_lt_succ_iff



## [2020-12-18 20:57:15](https://github.com/leanprover-community/mathlib/commit/33483a3)
chore(analysis/special_functions/trigonometric): golf a few more proofs ([#5423](https://github.com/leanprover-community/mathlib/pull/5423))
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* complex.cos_eq_iff_quadratic

Modified src/data/complex/basic.lean
- \+ *lemma* complex.int_cast_abs



## [2020-12-18 17:40:37](https://github.com/leanprover-community/mathlib/commit/0d140b1)
feat(data/set/basic): nonempty instances for subtypes ([#5409](https://github.com/leanprover-community/mathlib/pull/5409))
In [#5408](https://github.com/leanprover-community/mathlib/pull/5408), it is useful to be able to track the nonemptiness of a subset by typeclass inference.  These constructions allow one to do this.
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *lemma* set.nonempty_of_nonempty_subtype



## [2020-12-18 15:15:14](https://github.com/leanprover-community/mathlib/commit/775edc6)
feat(linear_algebra/tensor_product): Inherit smul through is_scalar_tower ([#5317](https://github.com/leanprover-community/mathlib/pull/5317))
Most notably, this now means that the lemmas about `smul` and `tmul` can be used to prove `∀ z : Z, (z • a) ⊗ₜ[R] b = z • (a ⊗ₜ[R] b)`.
Hopefully these instances aren't dangerous - in particular, there's now a risk of a non-defeq-but-eq diamond for the `ℤ`- and `ℕ`-module structure.
However:
* this diamond already exists in other places anyway
* the diamond if it comes up can be solved with `subsingleton.elim`, since we have a proof that all Z-module and N-module structures must be equivalent.
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean
- \+/\- *def* tensor_product.smul.aux
- \+/\- *theorem* tensor_product.smul.aux_of
- \+/\- *theorem* tensor_product.smul_tmul'
- \+/\- *lemma* tensor_product.smul_tmul
- \+/\- *lemma* tensor_product.tmul_smul

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
- \+ *lemma* polynomial.degree_of_subsingleton
- \+ *lemma* polynomial.monic.coeff_nat_degree
- \+ *lemma* polynomial.nat_degree_of_subsingleton

Modified src/data/polynomial/monic.lean
- \- *lemma* polynomial.monic.coeff_nat_degree
- \+/\- *lemma* polynomial.monic.nat_degree_mul
- \+/\- *lemma* polynomial.monic.next_coeff_prod

Modified src/data/polynomial/reverse.lean
- \+ *lemma* polynomial.coeff_one_reverse
- \+ *lemma* polynomial.coeff_zero_reverse

Modified src/order/basic.lean


Modified src/order/complete_lattice.lean
- \- *theorem* infi_unit
- \- *theorem* supr_unit

Modified src/order/conditionally_complete_lattice.lean
- \+ *theorem* infi_unique
- \+ *theorem* infi_unit
- \+ *theorem* supr_unique
- \+ *theorem* supr_unit

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.subsingleton.at_bot_eq
- \+ *lemma* filter.subsingleton.at_top_eq

Modified src/topology/algebra/ordered.lean
- \+ *lemma* filter.tendsto.add_at_bot
- \+ *lemma* filter.tendsto.add_at_top
- \+ *lemma* filter.tendsto.at_bot_add
- \+ *lemma* filter.tendsto.at_top_add
- \+ *lemma* filter.tendsto.mul_at_top
- \- *lemma* tendsto_at_bot_add_tendsto_left
- \- *lemma* tendsto_at_bot_add_tendsto_right
- \- *lemma* tendsto_at_top_add_tendsto_left
- \- *lemma* tendsto_at_top_add_tendsto_right



## [2020-12-18 09:12:03](https://github.com/leanprover-community/mathlib/commit/c4f673c)
chore(analysis/normed_space/basic): `continuous_at.norm` etc ([#5411](https://github.com/leanprover-community/mathlib/pull/5411))
Add variants of the lemma that the norm is continuous.  Also rewrite a few proofs, and rename three lemmas:
* `lim_norm` -> `tendsto_norm_sub_self`
* `lim_norm_zero` -> `tendsto_norm_zero`
* `lim_norm_zero'` -> `tendsto_norm_zero'`
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* continuous.nnnorm
- \+/\- *lemma* continuous.norm
- \+ *lemma* continuous_at.nnnorm
- \+ *lemma* continuous_at.norm
- \+ *lemma* continuous_on.nnnorm
- \+ *lemma* continuous_on.norm
- \+ *lemma* continuous_within_at.nnnorm
- \+ *lemma* continuous_within_at.norm
- \+/\- *lemma* filter.tendsto.nnnorm
- \+/\- *lemma* filter.tendsto.norm
- \- *lemma* lim_norm
- \- *lemma* lim_norm_zero
- \+ *lemma* tendsto_norm
- \+ *lemma* tendsto_norm_nhds_within_zero
- \+ *lemma* tendsto_norm_sub_self
- \+ *lemma* tendsto_norm_zero

Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/specific_limits.lean
- \- *lemma* lim_norm_zero'
- \+ *lemma* tendsto_norm_zero'

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
- \+ *lemma* real.bij_on_cos
- \+ *lemma* real.bij_on_sin
- \+/\- *lemma* real.cos_eq_one_iff_of_lt_of_lt
- \- *lemma* real.cos_inj_of_nonneg_of_le_pi
- \+ *lemma* real.cos_mem_Icc
- \+/\- *lemma* real.cos_nonneg_of_mem_Icc
- \+/\- *lemma* real.cos_nonpos_of_pi_div_two_le_of_le
- \+/\- *lemma* real.cos_pos_of_mem_Ioo
- \- *lemma* real.exists_cos_eq
- \- *lemma* real.exists_sin_eq
- \+ *lemma* real.inj_on_cos
- \+ *lemma* real.inj_on_sin
- \+ *lemma* real.maps_to_cos
- \+ *lemma* real.maps_to_sin
- \+/\- *lemma* real.range_cos
- \+/\- *lemma* real.range_sin
- \- *lemma* real.sin_inj_of_le_of_le_pi_div_two
- \- *lemma* real.sin_lt_sin_of_le_of_le_pi_div_two
- \+ *lemma* real.sin_lt_sin_of_lt_of_le_pi_div_two
- \+ *lemma* real.sin_mem_Icc
- \+ *lemma* real.sin_nonneg_of_mem_Icc
- \+ *lemma* real.sin_pos_of_mem_Ioo
- \+ *lemma* real.strict_mono_decr_on_cos
- \+ *lemma* real.strict_mono_incr_on_sin
- \+ *lemma* real.surj_on_cos
- \+ *lemma* real.surj_on_sin

Modified src/geometry/euclidean/triangle.lean




## [2020-12-17 16:32:00](https://github.com/leanprover-community/mathlib/commit/35f2789)
chore(algebra/module/basic): add `subsingleton (semimodule ℕ M)` ([#5396](https://github.com/leanprover-community/mathlib/pull/5396))
This can be used to resolve diamonds between different `semimodule ℕ` instances.
The implementation is copied from the `subsingleton (module ℤ M)` instance.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \- *lemma* module_ext
- \+ *lemma* semimodule_ext



## [2020-12-17 13:27:40](https://github.com/leanprover-community/mathlib/commit/6f1351f)
chore(algebra/{group,ring}): more on pushing/pulling groups/rings along morphisms ([#5406](https://github.com/leanprover-community/mathlib/pull/5406))
#### Estimated changes
Modified src/algebra/group/inj_surj.lean


Modified src/algebra/ring/basic.lean




## [2020-12-17 13:27:39](https://github.com/leanprover-community/mathlib/commit/ff716d2)
chore(order/bounds): golf ([#5401](https://github.com/leanprover-community/mathlib/pull/5401))
#### Estimated changes
Modified src/order/bounds.lean
- \+ *lemma* is_glb.exists_between'
- \+ *lemma* is_glb.exists_between
- \+/\- *lemma* is_glb.exists_between_self_add'
- \+/\- *lemma* is_glb.exists_between_self_add
- \+ *lemma* is_lub.exists_between'
- \+ *lemma* is_lub.exists_between
- \+/\- *lemma* is_lub.exists_between_sub_self'
- \+/\- *lemma* is_lub.exists_between_sub_self

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
- \- *lemma* mem_nhds_unbounded
- \+ *lemma* nhds_basis_Ioo'
- \+ *lemma* nhds_basis_Ioo

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
- \+ *lemma* alternating_map.coe_add
- \+ *lemma* alternating_map.coe_alternatization
- \+ *lemma* alternating_map.coe_neg
- \+ *lemma* alternating_map.coe_smul
- \+ *lemma* alternating_map.coe_sub
- \+ *lemma* alternating_map.coe_zero
- \+/\- *lemma* alternating_map.smul_apply
- \+ *lemma* alternating_map.sub_apply
- \- *lemma* alternating_map.to_multilinear_map_alternization

Modified src/linear_algebra/multilinear.lean
- \+ *lemma* multilinear_map.dom_coprod'_apply
- \+ *lemma* multilinear_map.dom_coprod_dom_dom_congr_sum_congr
- \+ *lemma* multilinear_map.dom_dom_congr_mul
- \+ *lemma* multilinear_map.dom_dom_congr_trans
- \+/\- *lemma* multilinear_map.sub_apply



## [2020-12-17 08:03:51](https://github.com/leanprover-community/mathlib/commit/6a99e9e)
chore(analysis/calculus/deriv): add `iff` versions of `differentiable_const_add` etc ([#5390](https://github.com/leanprover-community/mathlib/pull/5390))
Also drop some unneeded `differentiable` assumptions in lemmas like `deriv_const_add`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* deriv_add_const
- \+/\- *lemma* deriv_const_add
- \+/\- *lemma* deriv_const_sub
- \+/\- *lemma* deriv_sub_const
- \+/\- *lemma* deriv_within.neg
- \+/\- *lemma* deriv_within_add_const
- \+/\- *lemma* deriv_within_const_add
- \+/\- *lemma* deriv_within_const_sub
- \+/\- *lemma* deriv_within_sub_const

Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* differentiable.const_add
- \+/\- *lemma* differentiable.const_sub
- \+/\- *lemma* differentiable.neg
- \+/\- *lemma* differentiable.sub_const
- \+ *lemma* differentiable_add_const_iff
- \+/\- *lemma* differentiable_at.neg
- \+/\- *lemma* differentiable_at.sub_const
- \+ *lemma* differentiable_at_add_const_iff
- \+ *lemma* differentiable_at_const_add_iff
- \+ *lemma* differentiable_at_const_sub_iff
- \+ *lemma* differentiable_at_neg_iff
- \+ *lemma* differentiable_at_sub_const_iff
- \+ *lemma* differentiable_const_add_iff
- \+ *lemma* differentiable_const_sub_iff
- \+ *lemma* differentiable_neg_iff
- \+/\- *lemma* differentiable_on.const_add
- \+/\- *lemma* differentiable_on.const_sub
- \+/\- *lemma* differentiable_on.sub_const
- \+ *lemma* differentiable_on_add_const_iff
- \+ *lemma* differentiable_on_const_add_iff
- \+ *lemma* differentiable_on_const_sub_iff
- \+ *lemma* differentiable_on_neg_iff
- \+ *lemma* differentiable_on_sub_const_iff
- \+ *lemma* differentiable_sub_const_iff
- \+ *lemma* differentiable_within_at_add_const_iff
- \+ *lemma* differentiable_within_at_const_add_iff
- \+ *lemma* differentiable_within_at_const_sub_iff
- \+ *lemma* differentiable_within_at_neg_iff
- \+ *lemma* differentiable_within_at_sub_const_iff
- \+/\- *lemma* fderiv_add_const
- \+/\- *lemma* fderiv_const_add
- \+/\- *lemma* fderiv_const_sub
- \+/\- *lemma* fderiv_neg
- \+/\- *lemma* fderiv_sub_const
- \+/\- *lemma* fderiv_within_add_const
- \+/\- *lemma* fderiv_within_const_add
- \+/\- *lemma* fderiv_within_const_sub
- \+/\- *lemma* fderiv_within_neg
- \+/\- *lemma* fderiv_within_sub_const
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
- \+ *def* alg_hom.extend_scalars
- \+ *def* alg_hom.restrict_domain
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
- \+/\- *lemma* finset.coe_injective
- \+ *lemma* finset.mem_insert_coe
- \+ *lemma* list.to_finset_surj_on
- \+/\- *theorem* list.to_finset_surjective



## [2020-12-16 15:31:36](https://github.com/leanprover-community/mathlib/commit/39ecd1a)
chore(group_theory/group_action/basic): Add a simp lemma about smul on quotient groups ([#5374](https://github.com/leanprover-community/mathlib/pull/5374))
By pushing `mk` to the outside, this increases the chance they can cancel with an outer `lift`
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \+ *lemma* mul_action.quotient.smul_coe
- \+ *lemma* mul_action.quotient.smul_mk



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
- \- *lemma* group.inv_eq_one_div
- \- *lemma* group.mul_one_div
- \+ *lemma* inv_eq_one_div
- \+ *lemma* mul_one_div

Modified src/algebra/group/defs.lean
- \+ *lemma* div_eq_mul_inv
- \- *lemma* group.div_eq_mul_inv
- \+ *def* group.to_monoid
- \- *lemma* sub_eq_add_neg

Modified src/algebra/group/hom.lean
- \- *lemma* add_monoid_hom.sub_apply
- \+ *lemma* monoid_hom.div_apply

Modified src/algebra/group/inj_surj.lean


Modified src/algebra/group/pi.lean
- \- *lemma* pi.sub_apply

Modified src/algebra/group/prod.lean


Modified src/algebra/group/type_tags.lean
- \+ *lemma* of_add_sub
- \+ *lemma* of_mul_div
- \+ *lemma* to_add_div
- \+ *lemma* to_mul_sub

Modified src/algebra/group/ulift.lean
- \+ *lemma* ulift.div_down
- \- *lemma* ulift.sub_down

Modified src/algebra/group_with_zero/basic.lean


Modified src/algebra/group_with_zero/defs.lean
- \- *lemma* div_eq_mul_inv

Modified src/algebra/monoid_algebra.lean


Modified src/algebra/opposites.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/punit_instances.lean
- \+ *lemma* punit.div_eq

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
- \+ *lemma* equiv.div_def

Modified src/data/finsupp/basic.lean


Modified src/data/int/basic.lean


Modified src/data/matrix/basic.lean
- \+/\- *theorem* matrix.neg_apply
- \+/\- *theorem* matrix.sub_apply
- \+/\- *theorem* matrix.zero_apply

Modified src/data/padics/padic_integers.lean
- \+ *lemma* padic_int.coe_pow
- \+/\- *lemma* padic_int.coe_sub
- \- *lemma* padic_int.coet_pow

Modified src/data/pi.lean
- \+/\- *lemma* pi.div_apply

Modified src/data/quaternion.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/cau_seq_completion.lean
- \+ *theorem* cau_seq.completion.mk_sub

Modified src/data/real/hyperreal.lean


Modified src/data/zsqrtd/basic.lean


Modified src/deprecated/subgroup.lean
- \- *theorem* is_add_subgroup.sub_mem
- \+ *lemma* is_subgroup.div_mem

Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/field_theory/perfect_closure.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/perm/basic.lean


Modified src/group_theory/quotient_group.lean


Modified src/group_theory/subgroup.lean
- \- *lemma* add_subgroup.sub_mem
- \+ *theorem* subgroup.div_mem

Modified src/group_theory/sylow.lean


Modified src/linear_algebra/basic.lean
- \+ *theorem* submodule.quotient.mk_sub

Modified src/linear_algebra/char_poly/basic.lean


Modified src/linear_algebra/multilinear.lean
- \+ *lemma* multilinear_map.sub_apply

Modified src/linear_algebra/tensor_product.lean


Modified src/measure_theory/integration.lean
- \+/\- *lemma* measure_theory.simple_func.coe_sub

Modified src/number_theory/dioph.lean


Modified src/order/filter/filter_product.lean


Modified src/order/filter/germ.lean
- \+ *lemma* filter.germ.coe_div
- \- *lemma* filter.germ.coe_sub

Modified src/ring_theory/derivation.lean


Modified src/ring_theory/localization.lean


Modified src/tactic/norm_num.lean
- \- *theorem* norm_num.int_sub_hack

Modified src/tactic/ring.lean


Modified src/topology/algebra/group_completion.lean
- \+ *lemma* uniform_space.completion.coe_sub

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
- \- *lemma* real.continuous_sqrt

Modified src/analysis/special_functions/trigonometric.lean


Modified src/data/complex/basic.lean


Modified src/data/real/basic.lean
- \- *lemma* real.le_sqrt'
- \- *lemma* real.le_sqrt
- \- *lemma* real.le_sqrt_of_sqr_le
- \- *theorem* real.mul_self_sqrt
- \- *theorem* real.sqr_sqrt
- \- *def* real.sqrt_aux
- \- *theorem* real.sqrt_aux_nonneg
- \- *theorem* real.sqrt_div
- \- *theorem* real.sqrt_eq_iff_mul_self_eq
- \- *theorem* real.sqrt_eq_iff_sqr_eq
- \- *theorem* real.sqrt_eq_zero'
- \- *theorem* real.sqrt_eq_zero
- \- *theorem* real.sqrt_eq_zero_of_nonpos
- \- *theorem* real.sqrt_exists
- \- *theorem* real.sqrt_inj
- \- *theorem* real.sqrt_inv
- \- *theorem* real.sqrt_le
- \- *lemma* real.sqrt_le_left
- \- *lemma* real.sqrt_le_sqrt
- \- *theorem* real.sqrt_lt
- \- *theorem* real.sqrt_mul'
- \- *theorem* real.sqrt_mul
- \- *theorem* real.sqrt_mul_self
- \- *theorem* real.sqrt_mul_self_eq_abs
- \- *theorem* real.sqrt_nonneg
- \- *theorem* real.sqrt_one
- \- *theorem* real.sqrt_pos
- \- *theorem* real.sqrt_prop
- \- *theorem* real.sqrt_sqr
- \- *theorem* real.sqrt_sqr_eq_abs
- \- *theorem* real.sqrt_zero

Modified src/data/real/irrational.lean


Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.le_of_real_iff_coe_le'

Added src/data/real/sqrt.lean
- \+ *lemma* continuous.sqrt
- \+ *lemma* continuous_at.sqrt
- \+ *lemma* continuous_on.sqrt
- \+ *lemma* continuous_within_at.sqrt
- \+ *lemma* filter.tendsto.sqrt
- \+ *lemma* nnreal.continuous_sqrt
- \+ *lemma* nnreal.le_sqrt_iff
- \+ *lemma* nnreal.mul_sqrt_self
- \+ *lemma* nnreal.sqrt_div
- \+ *lemma* nnreal.sqrt_eq_iff_sqr_eq
- \+ *lemma* nnreal.sqrt_eq_zero
- \+ *lemma* nnreal.sqrt_inv
- \+ *lemma* nnreal.sqrt_le_iff
- \+ *lemma* nnreal.sqrt_mul
- \+ *lemma* nnreal.sqrt_mul_self
- \+ *lemma* nnreal.sqrt_one
- \+ *lemma* nnreal.sqrt_zero
- \+ *lemma* real.continuous_sqrt
- \+ *lemma* real.le_sqrt'
- \+ *lemma* real.le_sqrt
- \+ *lemma* real.le_sqrt_of_sqr_le
- \+ *theorem* real.mul_self_sqrt
- \+ *theorem* real.sqr_sqrt
- \+ *def* real.sqrt_aux
- \+ *theorem* real.sqrt_aux_nonneg
- \+ *theorem* real.sqrt_div
- \+ *theorem* real.sqrt_eq_iff_mul_self_eq
- \+ *theorem* real.sqrt_eq_iff_sqr_eq
- \+ *theorem* real.sqrt_eq_zero'
- \+ *theorem* real.sqrt_eq_zero
- \+ *theorem* real.sqrt_eq_zero_of_nonpos
- \+ *theorem* real.sqrt_inj
- \+ *theorem* real.sqrt_inv
- \+ *theorem* real.sqrt_le
- \+ *lemma* real.sqrt_le_iff
- \+ *lemma* real.sqrt_le_left
- \+ *lemma* real.sqrt_le_sqrt
- \+ *theorem* real.sqrt_lt
- \+ *theorem* real.sqrt_mul'
- \+ *theorem* real.sqrt_mul
- \+ *theorem* real.sqrt_mul_self
- \+ *theorem* real.sqrt_mul_self_eq_abs
- \+ *theorem* real.sqrt_nonneg
- \+ *theorem* real.sqrt_one
- \+ *theorem* real.sqrt_pos
- \+ *theorem* real.sqrt_sqr
- \+ *theorem* real.sqrt_sqr_eq_abs
- \+ *theorem* real.sqrt_zero



## [2020-12-16 13:55:19](https://github.com/leanprover-community/mathlib/commit/1b01068)
feat(ring_theory/witt_vector): Witt vectors are proj. limit of truncated Witt vectors ([#5163](https://github.com/leanprover-community/mathlib/pull/5163))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/ring_theory/witt_vector/truncated.lean
- \+ *lemma* truncated_witt_vector.card
- \+ *lemma* truncated_witt_vector.coeff_truncate
- \+ *lemma* truncated_witt_vector.infi_ker_truncate
- \+ *def* truncated_witt_vector.truncate
- \+ *lemma* truncated_witt_vector.truncate_comp
- \+ *lemma* truncated_witt_vector.truncate_comp_witt_vector_truncate
- \+ *lemma* truncated_witt_vector.truncate_surjective
- \+ *lemma* truncated_witt_vector.truncate_truncate
- \+ *lemma* truncated_witt_vector.truncate_witt_vector_truncate
- \+ *lemma* witt_vector.coeff_truncate
- \+ *lemma* witt_vector.hom_ext
- \+ *def* witt_vector.lift
- \+ *def* witt_vector.lift_equiv
- \+ *def* witt_vector.lift_fun
- \+ *lemma* witt_vector.lift_unique
- \+ *lemma* witt_vector.mem_ker_truncate
- \+ *def* witt_vector.truncate
- \+ *lemma* witt_vector.truncate_comp_lift
- \+ *lemma* witt_vector.truncate_lift
- \+ *lemma* witt_vector.truncate_lift_fun
- \+ *lemma* witt_vector.truncate_mk
- \+ *lemma* witt_vector.truncate_surjective



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
- \+/\- *lemma* formal_multilinear_series.bound_of_lt_radius
- \+/\- *lemma* formal_multilinear_series.geometric_bound_of_lt_radius
- \+/\- *lemma* formal_multilinear_series.le_radius_of_bound
- \+/\- *lemma* has_fpower_series_on_ball.tendsto_uniformly_on'
- \+/\- *lemma* has_fpower_series_on_ball.tendsto_uniformly_on
- \+/\- *lemma* has_fpower_series_on_ball.uniform_geometric_approx

Modified src/analysis/analytic/composition.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* antilipschitz_with.add_lipschitz_with
- \+/\- *lemma* continuous_nnnorm
- \+/\- *lemma* lipschitz_with.add
- \+/\- *lemma* lipschitz_with.neg
- \+/\- *lemma* lipschitz_with.sub
- \+/\- *lemma* summable_of_nnnorm_bounded

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *theorem* continuous_linear_map.op_norm_le_of_lipschitz
- \+/\- *theorem* continuous_linear_map.uniform_embedding_of_bound
- \+/\- *theorem* linear_map.antilipschitz_of_bound

Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* measurable.nnreal_rpow
- \+/\- *lemma* measurable.nnreal_rpow_const
- \+/\- *lemma* nnreal.measurable_rpow
- \+/\- *lemma* nnreal.measurable_rpow_const

Modified src/analysis/specific_limits.lean
- \+/\- *theorem* nnreal.exists_pos_sum_of_encodable
- \+/\- *lemma* nnreal.has_sum_geometric
- \+/\- *lemma* nnreal.summable_geometric
- \+/\- *lemma* nnreal.tendsto_const_div_at_top_nhds_0_nat
- \+/\- *lemma* nnreal.tendsto_inverse_at_top_nhds_0_nat
- \+/\- *lemma* nnreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \+/\- *lemma* tsum_geometric_nnreal

Modified src/data/real/ennreal.lean


Modified src/data/real/nnreal.lean
- \+/\- *lemma* nnreal.add_sub_cancel'
- \+/\- *lemma* nnreal.add_sub_cancel
- \+/\- *lemma* nnreal.bdd_above_coe
- \+/\- *lemma* nnreal.bdd_below_coe
- \+/\- *lemma* nnreal.bot_eq_zero
- \+/\- *lemma* nnreal.coe_Inf
- \+/\- *lemma* nnreal.coe_Sup
- \+/\- *lemma* nnreal.coe_max
- \+/\- *lemma* nnreal.coe_min
- \+/\- *lemma* nnreal.coe_nonneg
- \+/\- *lemma* nnreal.div_def
- \+/\- *lemma* nnreal.inv_eq_zero
- \+/\- *lemma* nnreal.inv_pos
- \+/\- *lemma* nnreal.inv_zero
- \+/\- *lemma* nnreal.le_of_forall_epsilon_le
- \+/\- *lemma* nnreal.le_of_real_iff_coe_le
- \+/\- *lemma* nnreal.lt_iff_exists_rat_btwn
- \+/\- *lemma* nnreal.lt_of_real_iff_coe_lt
- \+/\- *lemma* nnreal.lt_sub_iff_add_lt
- \+/\- *lemma* nnreal.mul_eq_mul_left
- \+/\- *theorem* nnreal.mul_ne_zero'
- \+/\- *lemma* nnreal.of_real_le_iff_le_coe
- \+/\- *lemma* nnreal.of_real_lt_iff_lt_coe
- \+/\- *lemma* nnreal.sub_add_cancel_of_le
- \+/\- *lemma* nnreal.sub_eq_iff_eq_add
- \+/\- *lemma* nnreal.sub_le_iff_le_add
- \+/\- *lemma* nnreal.sub_lt_iff_lt_add
- \+/\- *lemma* nnreal.val_eq_coe
- \+/\- *lemma* nnreal.zero_le_coe

Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* measure_theory.lintegral_coe_eq_integral

Modified src/measure_theory/content.lean
- \+/\- *lemma* measure_theory.outer_measure.of_content_exists_compact
- \+/\- *lemma* measure_theory.outer_measure.of_content_exists_open

Modified src/measure_theory/decomposition.lean


Modified src/measure_theory/integration.lean
- \+/\- *lemma* measure_theory.lintegral_mono_nnreal
- \+/\- *theorem* measure_theory.simple_func.map_coe_ennreal_restrict
- \+/\- *theorem* measure_theory.simple_func.map_coe_nnreal_restrict

Modified src/measure_theory/outer_measure.lean


Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* cauchy_seq_of_edist_le_of_summable

Modified src/topology/bounded_continuous_function.lean
- \+/\- *def* bounded_continuous_function.comp
- \+/\- *lemma* bounded_continuous_function.continuous_comp
- \+/\- *lemma* bounded_continuous_function.lipschitz_comp
- \+/\- *lemma* bounded_continuous_function.uniform_continuous_comp

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* ennreal.coe_range_mem_nhds
- \+/\- *lemma* ennreal.continuous_coe
- \+/\- *lemma* ennreal.continuous_coe_iff
- \+/\- *lemma* ennreal.embedding_coe
- \+/\- *def* ennreal.lt_top_homeomorph_nnreal
- \+/\- *def* ennreal.ne_top_homeomorph_nnreal
- \+/\- *lemma* ennreal.nhds_coe
- \+/\- *lemma* ennreal.nhds_coe_coe
- \+/\- *lemma* ennreal.tendsto_coe

Modified src/topology/metric_space/antilipschitz.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* dist_le_coe
- \+/\- *lemma* dist_lt_coe
- \+/\- *lemma* edist_le_coe
- \+/\- *lemma* edist_lt_coe
- \+/\- *lemma* metric.emetric_ball_nnreal
- \+/\- *lemma* metric.emetric_closed_ball_nnreal
- \+/\- *def* nndist
- \+/\- *lemma* nnreal.dist_eq
- \+/\- *lemma* nnreal.nndist_eq

Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/lipschitz.lean


Modified src/topology/metric_space/pi_Lp.lean




## [2020-12-16 07:31:13](https://github.com/leanprover-community/mathlib/commit/47b3c4b)
feat(algebra/lie/basic): nilpotent and solvable Lie algebras ([#5382](https://github.com/leanprover-community/mathlib/pull/5382))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \- *def* derived_lie_submodule
- \+ *def* lie_algebra.derived_series
- \+ *lemma* lie_module.derived_series_le_lower_central_series
- \+ *def* lie_module.lower_central_series
- \+ *lemma* lie_module.trivial_iff_derived_eq_bot
- \+ *lemma* lie_submodule.trivial_lie_oper_zero
- \- *lemma* trivial_iff_derived_eq_bot
- \+ *lemma* trivial_lie_zero



## [2020-12-16 04:20:19](https://github.com/leanprover-community/mathlib/commit/79e9aee)
feat(equiv/basic): add true_arrow_equiv ([#5388](https://github.com/leanprover-community/mathlib/pull/5388))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.true_arrow_equiv



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
- \+ *lemma* category_theory.comp_hom_eq_id
- \+ *lemma* category_theory.hom_comp_eq_id



## [2020-12-15 22:23:50](https://github.com/leanprover-community/mathlib/commit/dbb6b04)
feat(topology/separation): add lemma connected_component_eq_clopen_Inter ([#5335](https://github.com/leanprover-community/mathlib/pull/5335))
Prove the lemma that in a t2 and compact space, the connected component of a point equals the intersection of all its clopen neighbourhoods. Will be useful for work on Profinite sets. The proof that a Profinite set is a limit of finite discrete spaces found at: https://stacks.math.columbia.edu/tag/08ZY uses this lemma. Also some proofs that the category Profinite is reflective in CompactHausdorff uses this lemma.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.subset_iff_inter_eq_self

Modified src/order/bounded_lattice.lean
- \+ *lemma* disjoint.left_le_of_le_sup_left
- \+ *lemma* disjoint.left_le_of_le_sup_right

Modified src/topology/separation.lean
- \+ *lemma* connected_component_eq_Inter_clopen

Modified src/topology/subset_properties.lean
- \+ *lemma* connected_component_subset_Inter_clopen
- \+ *lemma* continuous_on.preimage_clopen_of_clopen
- \+ *lemma* is_clopen_Inter
- \+ *lemma* is_clopen_bInter
- \+ *theorem* is_clopen_inter_of_disjoint_cover_clopen
- \+ *theorem* is_preconnected_iff_subset_of_disjoint_closed
- \+ *theorem* is_preconnected_iff_subset_of_fully_disjoint_closed
- \+ *theorem* subset_or_disjoint_of_clopen



## [2020-12-15 21:09:34](https://github.com/leanprover-community/mathlib/commit/66eddd8)
chore(algebra/category/Module/monoidal): Speed up the elaboration ([#5383](https://github.com/leanprover-community/mathlib/pull/5383))
This takes the elaboration time from ~5s to ~2.5s for associator_naturality, from ~90s to 5s for pentagon, and from ~14s to ~8s for `triangle`.
#### Estimated changes
Modified src/algebra/category/Module/monoidal.lean




## [2020-12-15 21:09:32](https://github.com/leanprover-community/mathlib/commit/b702408)
feat(ring_theory/roots_of_unity): add squarefreeness mod p of minimal polynomial ([#5381](https://github.com/leanprover-community/mathlib/pull/5381))
Two easy results about the reduction `mod p` of the minimal polynomial over `ℤ` of a primitive root of unity: it is separable and hence squarefree.
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* is_primitive_root.separable_minimal_polynomial_mod
- \+ *lemma* is_primitive_root.squarefree_minimal_polynomial_mod



## [2020-12-15 17:57:30](https://github.com/leanprover-community/mathlib/commit/78e48c0)
ci(lint-copy-mod-doc.py): add reserved notation and set_option linters, enable small_alpha_vrachy_check linter ([#5330](https://github.com/leanprover-community/mathlib/pull/5330))
[As requested on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/the.20word.20.22to.22/near/219370843), the reserved notation linter checks for `reserve` or `precedence` at the start of a non-comment, non-string literal line in any file other than `tactic.core`.
The new set_option linter disallows `set_option pp`, `set_option profiler` and `set_option trace` at the start of a non-comment, non-string literal line.
I also noticed that the `small_alpha_vrachy_check` linter added in [#4802](https://github.com/leanprover-community/mathlib/pull/4802) wasn't actually called, so I added it to the main `lint` function.
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt


Modified scripts/lint-copy-mod-doc.py


Modified src/algebra/module/linear_map.lean


Modified src/linear_algebra/basic.lean
- \+/\- *def* linear_equiv.congr_right
- \+/\- *lemma* submodule.sup_eq_range

Modified src/logic/basic.lean
- \+/\- *theorem* forall_prop_of_false

Modified src/logic/relator.lean


Modified src/order/lattice.lean


Modified src/tactic/core.lean


Modified src/tactic/lift.lean


Modified src/tactic/lint/frontend.lean


Modified src/tactic/localized.lean


Modified src/tactic/rcases.lean


Added src/tactic/reserved_notation.lean


Modified src/tactic/simps.lean


Modified src/tactic/where.lean
- \+/\- *def* where.select_for_which



## [2020-12-15 16:43:44](https://github.com/leanprover-community/mathlib/commit/c208a65)
feat(analysis/mean_inequalities): add Minkowski's inequality for the Lebesgue integral of ennreal functions ([#5379](https://github.com/leanprover-community/mathlib/pull/5379))
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *theorem* ennreal.lintegral_Lp_add_le
- \+ *lemma* ennreal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
- \+ *lemma* ennreal.lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add



## [2020-12-15 13:31:21](https://github.com/leanprover-community/mathlib/commit/3a997b1)
fix(group_theory/subgroup): Fix doubly-namespaced instance ([#5378](https://github.com/leanprover-community/mathlib/pull/5378))
Not sure why the linter missed this.
#### Estimated changes
Modified src/group_theory/subgroup.lean




## [2020-12-15 13:31:19](https://github.com/leanprover-community/mathlib/commit/75130b3)
feat(data/set/basic): nonempty set of nonempty subtype ([#5373](https://github.com/leanprover-community/mathlib/pull/5373))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.nonempty_of_nonempty_subtype



## [2020-12-15 13:31:17](https://github.com/leanprover-community/mathlib/commit/d21d17b)
feat(ring_theory/roots_of_unity): minimal polynomial of primitive roots ([#5322](https://github.com/leanprover-community/mathlib/pull/5322))
I've added some simple results about the minimal polynomial of a primitive root of unity. The next step will be to prove that any two primitive roots have the same minimal polynomial.
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* is_primitive_root.is_integral
- \+ *lemma* is_primitive_root.minimal_polynomial_dvd_X_pow_sub_one



## [2020-12-15 10:30:21](https://github.com/leanprover-community/mathlib/commit/0f4ac1b)
feat(category_theory/limits): product comparison simp lemmas ([#5351](https://github.com/leanprover-community/mathlib/pull/5351))
This adds two new simp lemmas to reduce the prod comparison morphism and uses them to golf some proofs
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* category_theory.limits.prod_comparison_fst
- \+ *lemma* category_theory.limits.prod_comparison_snd



## [2020-12-15 10:30:19](https://github.com/leanprover-community/mathlib/commit/9ba9a98)
chore(category_theory/sites): improve naming ([#5350](https://github.com/leanprover-community/mathlib/pull/5350))
- Improve naming of some lemmas to be more descriptive
- Golf some proofs
- Add some convenience deconstructors which are useful in practice
#### Estimated changes
Modified src/category_theory/sites/canonical.lean


Modified src/category_theory/sites/sheaf.lean
- \+ *lemma* category_theory.presieve.is_separated_of_is_sheaf
- \+ *lemma* category_theory.presieve.is_sheaf_for.functor_inclusion_comp_extend
- \+ *lemma* category_theory.presieve.is_sheaf_for.hom_ext
- \+ *lemma* category_theory.presieve.is_sheaf_for.unique_extend
- \- *lemma* category_theory.presieve.is_sheaf_for_coarser_topology
- \+/\- *lemma* category_theory.presieve.is_sheaf_for_iff_generate
- \+ *lemma* category_theory.presieve.is_sheaf_for_iff_yoneda_sheaf_condition
- \+ *lemma* category_theory.presieve.is_sheaf_of_le
- \+ *lemma* category_theory.presieve.is_sheaf_of_yoneda
- \- *lemma* category_theory.presieve.is_sheaf_yoneda
- \- *lemma* category_theory.presieve.separated_of_sheaf
- \- *lemma* category_theory.presieve.yoneda_condition_iff_sheaf_condition



## [2020-12-15 10:30:17](https://github.com/leanprover-community/mathlib/commit/dd72a98)
feat(group_theory/perm/basic): Bundle sigma_congr_right and sum_congr into monoid_homs ([#5301](https://github.com/leanprover-community/mathlib/pull/5301))
This makes the corresponding subgroups available as `monoid_hom.range`.
As a result, the old subgroup definitions can be removed.
This also adds injectivity and cardinality lemmas.
#### Estimated changes
Modified src/group_theory/perm/basic.lean
- \+ *def* equiv.perm.sigma_congr_right_hom
- \+ *lemma* equiv.perm.sigma_congr_right_hom_injective
- \+/\- *lemma* equiv.perm.sigma_congr_right_inv
- \+/\- *lemma* equiv.perm.sigma_congr_right_mul
- \+/\- *lemma* equiv.perm.sigma_congr_right_one
- \+ *def* equiv.perm.sum_congr_hom
- \+ *lemma* equiv.perm.sum_congr_hom_injective

Modified src/group_theory/perm/subgroup.lean
- \+ *lemma* equiv.perm.sigma_congr_right_hom.card_range
- \- *def* equiv.perm.sigma_congr_right_subgroup
- \+ *lemma* equiv.perm.sum_congr_hom.card_range
- \- *def* equiv.perm.sum_congr_subgroup



## [2020-12-15 10:30:14](https://github.com/leanprover-community/mathlib/commit/8041945)
feat(category_theory/monad): monadicity theorems ([#5137](https://github.com/leanprover-community/mathlib/pull/5137))
This is a proof of the reflexive (or crude) monadicity theorem along with a complete proof of Beck's monadicity theorem.
Also renames the prefix for special monad coequalizers to `free_coequalizer` rather than `coequalizer`, to avoid name-clashes when both `monad` and `limits` are imported.
#### Estimated changes
Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monad/coequalizer.lean
- \+/\- *def* category_theory.monad.beck_algebra_cofork
- \- *def* category_theory.monad.coequalizer.bottom_map
- \- *lemma* category_theory.monad.coequalizer.condition
- \- *def* category_theory.monad.coequalizer.top_map
- \- *def* category_theory.monad.coequalizer.π
- \+ *def* category_theory.monad.free_coequalizer.bottom_map
- \+ *lemma* category_theory.monad.free_coequalizer.condition
- \+ *def* category_theory.monad.free_coequalizer.top_map
- \+ *def* category_theory.monad.free_coequalizer.π

Added src/category_theory/monad/monadicity.lean
- \+ *def* category_theory.monad.creates_G_split_coequalizers_of_monadic
- \+ *def* category_theory.monad.monadic_of_creates_G_split_coequalizers
- \+ *def* category_theory.monad.monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms
- \+ *def* category_theory.monad.monadic_of_has_preserves_reflects_G_split_coequalizers
- \+ *def* category_theory.monad.monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms
- \+ *def* category_theory.monad.monadicity_internal.comparison_adjunction
- \+ *lemma* category_theory.monad.monadicity_internal.comparison_adjunction_counit_app
- \+ *lemma* category_theory.monad.monadicity_internal.comparison_adjunction_unit_f
- \+ *lemma* category_theory.monad.monadicity_internal.comparison_adjunction_unit_f_aux
- \+ *def* category_theory.monad.monadicity_internal.comparison_left_adjoint_hom_equiv
- \+ *def* category_theory.monad.monadicity_internal.comparison_left_adjoint_obj
- \+ *def* category_theory.monad.monadicity_internal.counit_coequalizer_of_reflects_coequalizer
- \+ *def* category_theory.monad.monadicity_internal.counit_cofork
- \+ *def* category_theory.monad.monadicity_internal.left_adjoint_comparison
- \+ *def* category_theory.monad.monadicity_internal.unit_cofork
- \+ *def* category_theory.monad.monadicity_internal.unit_colimit_of_preserves_coequalizer



## [2020-12-15 10:30:11](https://github.com/leanprover-community/mathlib/commit/407d138)
chore(category_theory/equivalence): weaken essential surjectivity ([#3821](https://github.com/leanprover-community/mathlib/pull/3821))
Weaken essential surjectivity to be a Prop, rather than the data of the inverse.
#### Estimated changes
Modified src/algebra/category/Group/Z_Module_equivalence.lean


Modified src/category_theory/Fintype.lean


Modified src/category_theory/equivalence.lean
- \- *def* category_theory.equivalence.equivalence_of_fully_faithfully_ess_surj
- \+ *lemma* category_theory.equivalence.ess_surj_of_equivalence
- \- *def* category_theory.equivalence.ess_surj_of_equivalence
- \- *def* category_theory.functor.fun_obj_preimage_iso
- \- *def* category_theory.functor.obj_preimage

Modified src/category_theory/monad/adjunction.lean


Modified src/topology/category/Compactum.lean
- \+ *lemma* Compactum_to_CompHaus.ess_surj



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
- \- *lemma* exists_le_mul_self
- \- *lemma* exists_lt_mul_self

Modified src/algebra/quadratic_discriminant.lean


Modified src/order/filter/at_top_bot.lean
- \+ *lemma* exists_le_mul_self
- \+ *lemma* exists_lt_mul_self



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
- \+/\- *lemma* nnreal.tendsto_sum_nat_add

Modified src/topology/instances/nnreal.lean
- \+ *lemma* nnreal.summable_nat_add_iff



## [2020-12-15 01:31:32](https://github.com/leanprover-community/mathlib/commit/4dbb3e2)
chore(data/finsupp/basic): more lemmas about `α →₀ ℕ` ([#5362](https://github.com/leanprover-community/mathlib/pull/5362))
* define `canonically_ordered_add_monoid` instance;
* add a few simp lemmas;
* more lemmas about product over `finsupp.antidiagonal n`;
* define `finsupp.Iic_finset`, use it for `finite_le_nat`.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *def* finsupp.Iic_finset
- \+ *lemma* finsupp.antidiagonal_support_filter_fst_eq
- \+ *lemma* finsupp.antidiagonal_support_filter_snd_eq
- \+ *lemma* finsupp.coe_Iic_finset
- \+ *lemma* finsupp.mem_Iic_finset
- \+ *lemma* finsupp.nat_add_sub_cancel
- \+ *lemma* finsupp.nat_add_sub_cancel_left
- \+ *lemma* finsupp.nat_add_sub_of_le
- \+ *lemma* finsupp.nat_sub_add_cancel
- \+ *lemma* finsupp.nat_zero_sub
- \+ *lemma* finsupp.prod_antidiagonal_support_swap
- \+/\- *lemma* finsupp.single_eq_zero
- \+/\- *lemma* finsupp.swap_mem_antidiagonal_support

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
- \+ *lemma* geom_le
- \+/\- *lemma* geom_lt
- \+ *lemma* tendsto_at_top_of_geom_le
- \- *lemma* tendsto_at_top_of_geom_lt

Modified src/order/iterate.lean
- \+ *lemma* monotone.seq_le_seq
- \+ *lemma* monotone.seq_lt_seq_of_le_of_lt
- \+ *lemma* monotone.seq_lt_seq_of_lt_of_le
- \+ *lemma* monotone.seq_pos_lt_seq_of_le_of_lt
- \+ *lemma* monotone.seq_pos_lt_seq_of_lt_of_le



## [2020-12-14 23:07:26](https://github.com/leanprover-community/mathlib/commit/d1904fc)
refactor(measure_theory/lp_space): move most of the proof of mem_Lp.add to a new lemma in analysis/mean_inequalities ([#5370](https://github.com/leanprover-community/mathlib/pull/5370))
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *lemma* ennreal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top

Modified src/measure_theory/lp_space.lean




## [2020-12-14 23:07:24](https://github.com/leanprover-community/mathlib/commit/dc719a9)
feat(algebra/lie/basic): define ideal operations for Lie modules ([#5337](https://github.com/leanprover-community/mathlib/pull/5337))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *def* derived_lie_submodule
- \+/\- *lemma* lie_submodule.add_eq_sup
- \+ *lemma* lie_submodule.bot_lie
- \+ *lemma* lie_submodule.coe_submodule_le_coe_submodule
- \+ *lemma* lie_submodule.coe_sup
- \+ *lemma* lie_submodule.coe_to_set_mk
- \+ *lemma* lie_submodule.coe_to_submodule_mk
- \+ *lemma* lie_submodule.eq_bot_iff
- \+/\- *lemma* lie_submodule.le_def
- \+ *lemma* lie_submodule.lie_bot
- \+ *lemma* lie_submodule.lie_comm
- \+ *lemma* lie_submodule.lie_ideal_oper_eq_span
- \+ *lemma* lie_submodule.lie_le_inf
- \+ *lemma* lie_submodule.lie_le_left
- \+ *lemma* lie_submodule.lie_le_right
- \+ *lemma* lie_submodule.lie_mem_lie
- \+ *lemma* lie_submodule.lie_sup
- \+ *lemma* lie_submodule.mem_sup
- \+ *lemma* lie_submodule.mono_lie
- \+ *lemma* lie_submodule.mono_lie_left
- \+ *lemma* lie_submodule.mono_lie_right
- \+ *lemma* lie_submodule.sup_lie
- \+ *lemma* trivial_iff_derived_eq_bot

Modified src/algebra/module/submodule.lean
- \+ *lemma* submodule.mk_coe

Modified src/linear_algebra/finite_dimensional.lean




## [2020-12-14 21:52:23](https://github.com/leanprover-community/mathlib/commit/a649c59)
feat(field_theory/intermediate_field): lift2_alg_equiv ([#5344](https://github.com/leanprover-community/mathlib/pull/5344))
Proves that lift2 is isomorphic as an algebra over the base field
#### Estimated changes
Modified src/field_theory/intermediate_field.lean
- \+ *def* intermediate_field.lift2_alg_equiv



## [2020-12-14 19:54:21](https://github.com/leanprover-community/mathlib/commit/4415dc0)
feat(algebra/algebra/basic): arrow_congr for alg_equiv ([#5346](https://github.com/leanprover-community/mathlib/pull/5346))
This is a copy of equiv.arrow_congr
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* alg_equiv.arrow_congr
- \+ *lemma* alg_equiv.arrow_congr_comp
- \+ *lemma* alg_equiv.arrow_congr_refl
- \+ *lemma* alg_equiv.arrow_congr_symm
- \+ *lemma* alg_equiv.arrow_congr_trans



## [2020-12-14 16:39:30](https://github.com/leanprover-community/mathlib/commit/07b5618)
chore(linear_algebra/{multilinear,alternating}): Generalize smul and neg instance ([#5364](https://github.com/leanprover-community/mathlib/pull/5364))
This brings the generality in line with that of `linear_map`. Notably:
* `has_neg` now exists when only the codomain has negation
* `has_scalar` now exists for the weaker condition of `smul_comm_class` rather than `has_scalar_tower`
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *lemma* alternating_map.map_neg
- \+/\- *lemma* alternating_map.neg_apply
- \+/\- *lemma* alternating_map.to_multilinear_map_alternization
- \+/\- *def* multilinear_map.alternatization
- \+/\- *lemma* multilinear_map.alternatization_apply

Modified src/linear_algebra/multilinear.lean
- \+ *lemma* multilinear_map.map_neg



## [2020-12-14 16:39:28](https://github.com/leanprover-community/mathlib/commit/b1c56b1)
feat(field_theory.minimal_polynomial): add results for GCD domains ([#5336](https://github.com/leanprover-community/mathlib/pull/5336))
I have added `gcd_domain_dvd`: for GCD domains, the minimal polynomial divides any primitive polynomial that has the integral
element as root.
For `gcd_domain_eq_field_fractions` and `gcd_domain_dvd` I have also added explicit versions for `ℤ`. Unfortunately, it seems impossible (to me at least) to apply the general lemmas and I had to redo the proofs, see [Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Minimal.20polynomial.20over.20.E2.84.9A.20vs.20over.20.E2.84.A4) for more details. (The basic reason seems to be that it's hard to convince lean that `is_scalar_tower ℤ ℚ α` holds using the localization map).
#### Estimated changes
Modified src/field_theory/minimal_polynomial.lean
- \+ *lemma* minimal_polynomial.gcd_domain_dvd
- \+ *lemma* minimal_polynomial.integer_dvd
- \+ *lemma* minimal_polynomial.over_int_eq_over_rat



## [2020-12-14 16:39:26](https://github.com/leanprover-community/mathlib/commit/f443792)
feat(topology/subset_properties): add instances for totally_disconnected_spaces ([#5334](https://github.com/leanprover-community/mathlib/pull/5334))
Add the instances subtype.totally_disconnected_space and pi.totally_disconnected_space.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.subsingleton_of_image

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
- \+ *def* list.all_some
- \+ *def* list.fill_nones
- \+ *def* list.take_list
- \+ *def* list.to_rbmap

Modified src/tactic/binder_matching.lean


Modified src/tactic/core.lean


Added src/tactic/induction.lean


Added test/induction.lean
- \+ *def* List.append
- \+ *def* accufact
- \+ *lemma* accufact_1_eq_fact
- \+ *def* expressions.subst
- \+ *lemma* expressions.subst_Var
- \+ *lemma* fraction.ext
- \+ *lemma* less_than.lt_lte
- \+ *lemma* not_even_2_mul_add_1
- \+ *lemma* not_sorted_17_13
- \+ *lemma* palindrome.rev_palindrome
- \+ *lemma* rose.nonempty_node_elim
- \+ *lemma* semantics.big_step_assign_iff
- \+ *lemma* semantics.big_step_deterministic
- \+ *lemma* semantics.big_step_ite_iff
- \+ *lemma* semantics.big_step_of_small_step_of_big_step
- \+ *lemma* semantics.big_step_of_star_small_step
- \+ *lemma* semantics.big_step_seq_iff
- \+ *lemma* semantics.big_step_skip_iff
- \+ *lemma* semantics.big_step_while_false_iff
- \+ *lemma* semantics.big_step_while_iff
- \+ *lemma* semantics.big_step_while_true_iff
- \+ *lemma* semantics.not_big_step_while_true
- \+ *lemma* semantics.not_curried_big_step_while_true
- \+ *lemma* semantics.small_step_deterministic
- \+ *lemma* semantics.small_step_final
- \+ *lemma* semantics.small_step_if_equal_states
- \+ *lemma* semantics.small_step_ite_iff
- \+ *lemma* semantics.small_step_seq_iff
- \+ *lemma* semantics.small_step_skip
- \+ *lemma* semantics.star.lift
- \+ *lemma* semantics.star.single
- \+ *lemma* semantics.star.trans
- \+ *lemma* semantics.star.trans_induction_on
- \+ *lemma* semantics.star_small_step_of_big_step
- \+ *lemma* semantics.star_small_step_seq
- \+ *def* semantics.state.update
- \+ *def* semantics.state
- \+ *lemma* star.head
- \+ *lemma* star.head_induction_on
- \+ *lemma* transitive_closure.tc_pets₁
- \+ *lemma* transitive_closure.tc_pets₂
- \+ *lemma* transitive_closure.tc_trans'
- \+ *lemma* transitive_closure.tc_trans
- \+ *def* ℕ₂.plus



## [2020-12-14 13:16:21](https://github.com/leanprover-community/mathlib/commit/a65de99)
feat(data/equiv): Add `congr_arg`, `congr_fun`, and `ext_iff` lemmas to equivs ([#5367](https://github.com/leanprover-community/mathlib/pull/5367))
These members already exist on the corresponding homs
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_equiv.ext_iff

Modified src/algebra/module/linear_map.lean
- \+ *lemma* linear_equiv.ext_iff

Modified src/data/equiv/basic.lean


Modified src/data/equiv/mul_add.lean
- \+ *lemma* mul_equiv.ext_iff

Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.ext_iff



## [2020-12-14 13:16:18](https://github.com/leanprover-community/mathlib/commit/dad88d8)
feat(field_theory/splitting_field): add splits_X theorem ([#5343](https://github.com/leanprover-community/mathlib/pull/5343))
This is a handy result and isn't definitionally a special case of splits_X_sub_C
#### Estimated changes
Modified src/field_theory/splitting_field.lean
- \+ *theorem* polynomial.splits_X



## [2020-12-14 13:16:15](https://github.com/leanprover-community/mathlib/commit/cf7377a)
chore(field_theory/adjoin): move dim/findim lemmas ([#5342](https://github.com/leanprover-community/mathlib/pull/5342))
adjoin.lean has some dim/findim lemmas, some of which could be moved to intermediate_field.lean
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* intermediate_field.dim_eq_one_iff
- \- *lemma* intermediate_field.dim_intermediate_field_eq_dim_subalgebra
- \+ *lemma* intermediate_field.findim_eq_one_iff
- \- *lemma* intermediate_field.findim_intermediate_field_eq_findim_subalgebra
- \- *lemma* intermediate_field.to_subalgebra_eq_iff

Modified src/field_theory/intermediate_field.lean
- \+ *lemma* intermediate_field.dim_eq_dim_subalgebra
- \+/\- *lemma* intermediate_field.eq_of_le_of_findim_eq'
- \+/\- *lemma* intermediate_field.eq_of_le_of_findim_eq
- \+/\- *lemma* intermediate_field.eq_of_le_of_findim_le'
- \+/\- *lemma* intermediate_field.eq_of_le_of_findim_le
- \+ *lemma* intermediate_field.findim_eq_findim_subalgebra
- \+ *lemma* intermediate_field.to_subalgebra_eq_iff



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
- \+ *lemma* filter.tendsto.at_top_mul_const'
- \+ *lemma* filter.tendsto.const_mul_at_top'

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.tendsto.at_bot_div_const
- \+ *lemma* filter.tendsto.at_bot_mul_at_bot
- \+ *lemma* filter.tendsto.at_bot_mul_at_top
- \+ *lemma* filter.tendsto.at_bot_mul_const
- \+ *lemma* filter.tendsto.at_bot_mul_neg_const
- \+ *lemma* filter.tendsto.at_top_div_const
- \+ *lemma* filter.tendsto.at_top_mul_at_bot
- \+ *lemma* filter.tendsto.at_top_mul_at_top
- \+ *lemma* filter.tendsto.at_top_mul_const
- \+ *lemma* filter.tendsto.at_top_mul_neg_const
- \+ *lemma* filter.tendsto.at_top_of_const_mul
- \+ *lemma* filter.tendsto.at_top_of_mul_const
- \+ *lemma* filter.tendsto.const_mul_at_bot
- \+ *lemma* filter.tendsto.const_mul_at_top
- \+ *lemma* filter.tendsto.neg_const_mul_at_bot
- \+ *lemma* filter.tendsto.neg_const_mul_at_top
- \+ *lemma* filter.tendsto.nsmul_at_bot
- \+ *lemma* filter.tendsto.nsmul_at_top
- \- *lemma* filter.tendsto_at_top_mul_at_top
- \+ *lemma* filter.tendsto_mul_self_at_top
- \+/\- *lemma* filter.tendsto_neg_at_bot_at_top
- \+/\- *lemma* filter.tendsto_neg_at_top_at_bot
- \+ *lemma* filter.tendsto_pow_at_top

Modified src/topology/algebra/ordered.lean
- \+ *lemma* filter.tendsto.at_top_mul
- \+ *lemma* filter.tendsto.at_top_mul_neg
- \- *lemma* tendsto_at_top_div
- \- *lemma* tendsto_at_top_mul_left'
- \- *lemma* tendsto_at_top_mul_left
- \- *lemma* tendsto_at_top_mul_right'
- \- *lemma* tendsto_at_top_mul_right
- \- *lemma* tendsto_mul_at_bot
- \- *lemma* tendsto_mul_at_top
- \- *lemma* tendsto_pow_at_top

Modified src/topology/algebra/polynomial.lean




## [2020-12-14 13:16:12](https://github.com/leanprover-community/mathlib/commit/1d37ff1)
feat(analysis/mean_inequalities): add weighted generalized mean inequality for ennreal ([#5316](https://github.com/leanprover-community/mathlib/pull/5316))
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *theorem* ennreal.rpow_arith_mean_le_arith_mean2_rpow
- \+ *theorem* ennreal.rpow_arith_mean_le_arith_mean_rpow

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.le_of_top_imp_top_of_to_nnreal_le
- \+ *lemma* ennreal.to_nnreal_mul
- \+ *lemma* ennreal.to_nnreal_pow
- \+ *lemma* ennreal.to_nnreal_prod



## [2020-12-14 13:16:10](https://github.com/leanprover-community/mathlib/commit/cecab59)
feat(group_theory/congruence): Add inv and neg ([#5304](https://github.com/leanprover-community/mathlib/pull/5304))
#### Estimated changes
Modified src/group_theory/congruence.lean




## [2020-12-14 13:16:08](https://github.com/leanprover-community/mathlib/commit/6dc5000)
feat(computability/language): define formal languages ([#5291](https://github.com/leanprover-community/mathlib/pull/5291))
Lifted from [#5036](https://github.com/leanprover-community/mathlib/pull/5036) in order to include in [#5038](https://github.com/leanprover-community/mathlib/pull/5038) as well.
#### Estimated changes
Added src/computability/language.lean
- \+ *lemma* language.add_def
- \+ *lemma* language.add_self
- \+ *lemma* language.mul_def
- \+ *lemma* language.one_def
- \+ *def* language.star
- \+ *lemma* language.star_def
- \+ *lemma* language.star_def_nonempty
- \+ *lemma* language.zero_def
- \+ *def* language



## [2020-12-14 13:16:05](https://github.com/leanprover-community/mathlib/commit/67b5ff6)
feat(algebra/direct_sum): constructor for morphisms into direct sums ([#5204](https://github.com/leanprover-community/mathlib/pull/5204))
#### Estimated changes
Modified src/algebra/direct_sum.lean
- \+ *def* direct_sum.from_add_monoid
- \+ *lemma* direct_sum.from_add_monoid_of
- \+ *lemma* direct_sum.from_add_monoid_of_apply

Modified src/algebra/group/hom.lean




## [2020-12-14 11:45:59](https://github.com/leanprover-community/mathlib/commit/c722b96)
feat (topology/instances/ennreal): summability from finite sum control ([#5363](https://github.com/leanprover-community/mathlib/pull/5363))
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+ *lemma* nnreal.summable_iff_not_tendsto_nat_at_top
- \+ *lemma* nnreal.summable_of_sum_range_le
- \+ *lemma* nnreal.tsum_le_of_sum_range_le
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
- \+/\- *def* ennreal.ennreal_equiv_sum
- \+/\- *def* homemorph.to_measurable_equiv
- \+/\- *def* measurable_equiv.ennreal_equiv_nnreal

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable_equiv.coe_eq
- \+/\- *def* measurable_equiv.prod_assoc
- \+/\- *def* measurable_equiv.prod_comm
- \+/\- *def* measurable_equiv.prod_congr
- \+/\- *def* measurable_equiv.refl
- \+/\- *def* measurable_equiv.set.prod
- \+/\- *def* measurable_equiv.set.range_inl
- \+/\- *def* measurable_equiv.set.range_inr
- \+/\- *def* measurable_equiv.set.singleton
- \+/\- *def* measurable_equiv.set.univ
- \+/\- *def* measurable_equiv.sum_congr
- \+/\- *def* measurable_equiv.symm
- \+/\- *def* measurable_equiv.trans



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
- \+ *theorem* not_differentiable_at_of_local_left_inverse_has_deriv_at_zero
- \+ *theorem* not_differentiable_within_at_of_local_left_inverse_has_deriv_within_at_zero

Modified src/analysis/calculus/fderiv.lean
- \- *lemma* has_fderiv_at.of_local_homeomorph
- \+ *lemma* local_homeomorph.has_fderiv_at_symm
- \+ *lemma* local_homeomorph.has_strict_fderiv_at_symm

Modified src/analysis/calculus/inverse.lean
- \+/\- *lemma* has_strict_fderiv_at.local_inverse_apply_image
- \+ *lemma* has_strict_fderiv_at.local_inverse_def

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *theorem* local_homeomorph.times_cont_diff_at_symm
- \- *theorem* times_cont_diff_at.of_local_homeomorph



## [2020-12-14 02:41:32](https://github.com/leanprover-community/mathlib/commit/714bc15)
feat(category_theory/adjunction): adjoint lifting theorems ([#5118](https://github.com/leanprover-community/mathlib/pull/5118))
Proves the [adjoint lifting theorem](https://ncatlab.org/nlab/show/adjoint+lifting+theorem) and the [adjoint triangle theorem](https://ncatlab.org/nlab/show/adjoint+triangle+theorem).
The intent here is for all but the last four statements in the file to be implementation.
#### Estimated changes
Added src/category_theory/adjunction/lifting.lean
- \+ *def* category_theory.lift_adjoint.construct_left_adjoint_equiv
- \+ *def* category_theory.lift_adjoint.counit_coequalises
- \+ *def* category_theory.lift_adjoint.other_map



## [2020-12-14 01:26:51](https://github.com/leanprover-community/mathlib/commit/b7a9615)
chore(scripts): update nolints.txt ([#5360](https://github.com/leanprover-community/mathlib/pull/5360))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-12-13 09:58:12](https://github.com/leanprover-community/mathlib/commit/88fb7ca)
chore(analysis/calculus): move the definition of `formal_multilinear_series` to a new file ([#5348](https://github.com/leanprover-community/mathlib/pull/5348))
#### Estimated changes
Added src/analysis/calculus/formal_multilinear_series.lean
- \+ *lemma* formal_multilinear_series.congr
- \+ *def* formal_multilinear_series.shift
- \+ *def* formal_multilinear_series.unshift
- \+ *def* formal_multilinear_series

Modified src/analysis/calculus/times_cont_diff.lean
- \- *lemma* formal_multilinear_series.congr
- \- *def* formal_multilinear_series.restrict_scalars
- \- *def* formal_multilinear_series.shift
- \- *def* formal_multilinear_series.unshift
- \- *def* formal_multilinear_series



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
- \+ *lemma* category_theory.sieve.Inf_apply
- \+ *lemma* category_theory.sieve.Sup_apply
- \+ *lemma* category_theory.sieve.inter_apply
- \- *lemma* category_theory.sieve.mem_Inf
- \- *lemma* category_theory.sieve.mem_Sup
- \- *lemma* category_theory.sieve.mem_generate
- \- *lemma* category_theory.sieve.mem_inter
- \- *lemma* category_theory.sieve.mem_pullback
- \- *lemma* category_theory.sieve.mem_pushforward_of_comp
- \- *lemma* category_theory.sieve.mem_top
- \- *lemma* category_theory.sieve.mem_union
- \+ *lemma* category_theory.sieve.pushforward_apply_comp
- \- *lemma* category_theory.sieve.sieve_of_subfunctor_apply
- \+ *lemma* category_theory.sieve.top_apply
- \+ *lemma* category_theory.sieve.union_apply



## [2020-12-12 22:41:29](https://github.com/leanprover-community/mathlib/commit/68818b3)
feat(field_theory/galois): Is_galois iff is_galois top ([#5285](https://github.com/leanprover-community/mathlib/pull/5285))
Proves that E/F is Galois iff top/F is Galois.
#### Estimated changes
Modified src/field_theory/galois.lean
- \+ *lemma* alg_equiv.transfer_galois
- \+ *lemma* is_galois.of_alg_equiv
- \+ *lemma* is_galois_iff_is_galois_top



## [2020-12-12 17:17:36](https://github.com/leanprover-community/mathlib/commit/5ced4dd)
feat(ring_theory/finiteness): add iff_quotient_mv_polynomial ([#5321](https://github.com/leanprover-community/mathlib/pull/5321))
Add characterizations of finite type algebra as quotient of polynomials rings. There are three version of the same lemma, using a `finset`, a `fintype` and `fin n`.
#### Estimated changes
Modified src/data/mv_polynomial/equiv.lean
- \+ *def* mv_polynomial.alg_equiv_of_equiv

Modified src/ring_theory/finiteness.lean
- \+ *lemma* algebra.finite_type.iff_quotient_mv_polynomial''
- \+ *lemma* algebra.finite_type.iff_quotient_mv_polynomial'
- \+ *lemma* algebra.finite_type.iff_quotient_mv_polynomial



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
- \+/\- *theorem* exists_nat_ge
- \+/\- *theorem* exists_nat_gt

Modified src/algebra/char_zero.lean
- \+/\- *lemma* two_ne_zero'

Modified src/algebra/group/basic.lean
- \- *lemma* eq_one_of_left_cancel_mul_self
- \- *lemma* eq_one_of_mul_self_left_cancel
- \- *lemma* eq_one_of_mul_self_right_cancel
- \- *lemma* eq_one_of_right_cancel_mul_self
- \+ *lemma* left_eq_mul_iff
- \+ *lemma* mul_eq_left_iff
- \+ *lemma* mul_eq_right_iff
- \+ *lemma* right_eq_mul_iff

Modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_mono
- \+ *theorem* strict_mono_incr_on_pow
- \+ *lemma* strict_mono_pow

Modified src/algebra/group_power/lemmas.lean


Modified src/data/int/cast.lean
- \+/\- *theorem* int.cast_abs
- \+/\- *theorem* int.cast_le
- \+/\- *theorem* int.cast_lt
- \+/\- *theorem* int.cast_lt_zero
- \+/\- *theorem* int.cast_max
- \+/\- *theorem* int.cast_min
- \+ *theorem* int.cast_mono
- \+/\- *theorem* int.cast_nonneg
- \+/\- *theorem* int.cast_nonpos
- \+/\- *theorem* int.cast_pos
- \+ *theorem* int.cast_strict_mono

Modified src/data/nat/cast.lean
- \+/\- *theorem* nat.abs_cast
- \+/\- *lemma* nat.cast_add_one_pos
- \+/\- *theorem* nat.cast_le
- \+/\- *theorem* nat.cast_le_one
- \+/\- *theorem* nat.cast_lt
- \+/\- *theorem* nat.cast_lt_one
- \+/\- *theorem* nat.cast_nonneg
- \+/\- *theorem* nat.cast_pos
- \+/\- *lemma* nat.cast_two
- \+ *theorem* nat.mono_cast
- \+/\- *theorem* nat.one_le_cast
- \+/\- *theorem* nat.one_lt_cast
- \+/\- *theorem* nat.strict_mono_cast

Modified src/data/zsqrtd/gaussian_int.lean


Modified src/order/filter/archimedean.lean
- \+/\- *lemma* tendsto_coe_int_at_top_at_top
- \+/\- *lemma* tendsto_coe_int_at_top_iff
- \+/\- *lemma* tendsto_coe_nat_at_top_at_top
- \+/\- *lemma* tendsto_coe_nat_at_top_iff

Modified src/ring_theory/derivation.lean




## [2020-12-12 07:17:02](https://github.com/leanprover-community/mathlib/commit/dad5aab)
refactor(ring_theory/polynomial/homogeneous): redefine `mv_polynomial.homogeneous_component` ([#5294](https://github.com/leanprover-community/mathlib/pull/5294))
* redefine `homogeneous_component` using `finsupp.restrict_dom`,
  “upgrade” it to a `linear_map`;
* add `coeff_homogeneous_component` and use it to golf some proofs.
#### Estimated changes
Modified src/ring_theory/polynomial/homogeneous.lean
- \+ *lemma* mv_polynomial.coeff_homogeneous_component



## [2020-12-12 07:17:00](https://github.com/leanprover-community/mathlib/commit/9cc8835)
feat(group_theory/perm/subgroup): Add some simple subgroups of permutations ([#5279](https://github.com/leanprover-community/mathlib/pull/5279))
#### Estimated changes
Added src/group_theory/perm/subgroup.lean
- \+ *def* equiv.perm.sigma_congr_right_subgroup
- \+ *def* equiv.perm.sum_congr_subgroup



## [2020-12-12 07:16:58](https://github.com/leanprover-community/mathlib/commit/84f9938)
feat(category_theory/sites): sheaves on types ([#5259](https://github.com/leanprover-community/mathlib/pull/5259))
#### Estimated changes
Modified src/category_theory/sites/sheaf.lean
- \+ *lemma* category_theory.presieve.is_sheaf.is_sheaf_for

Added src/category_theory/sites/types.lean
- \+ *def* category_theory.discrete_presieve
- \+ *def* category_theory.discrete_sieve
- \+ *lemma* category_theory.discrete_sieve_mem
- \+ *def* category_theory.eval
- \+ *lemma* category_theory.eval_app
- \+ *lemma* category_theory.eval_map
- \+ *lemma* category_theory.eval_types_glue
- \+ *lemma* category_theory.generate_discrete_presieve_mem
- \+ *theorem* category_theory.is_sheaf_yoneda'
- \+ *lemma* category_theory.subcanonical_types_grothendieck_topology
- \+ *lemma* category_theory.types_glue_eval
- \+ *def* category_theory.types_grothendieck_topology
- \+ *lemma* category_theory.types_grothendieck_topology_eq_canonical
- \+ *def* category_theory.yoneda'
- \+ *lemma* category_theory.yoneda'_comp



## [2020-12-12 07:16:56](https://github.com/leanprover-community/mathlib/commit/0344aee)
feat(ring_theory/*): various lemmas about quotients, localizations, and polynomials ([#5249](https://github.com/leanprover-community/mathlib/pull/5249))
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.quotient_map_comp_mk
- \+ *lemma* ideal.quotient_map_surjective

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_integral_quotient_map_iff
- \+ *lemma* ring_hom.is_integral_elem_of_is_integral_elem_comp
- \+ *lemma* ring_hom.is_integral_tower_top_of_is_integral

Modified src/ring_theory/jacobson.lean
- \+/\- *lemma* ideal.radical_eq_jacobson

Modified src/ring_theory/localization.lean
- \+ *lemma* localization_map_bijective_of_field
- \+ *lemma* map_injective_of_injective

Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* ideal.eq_zero_of_constant_mem_of_maximal
- \+ *lemma* ideal.polynomial_not_is_field



## [2020-12-12 07:16:53](https://github.com/leanprover-community/mathlib/commit/d032380)
feat(field_theory/normal): normal_of_alg_equiv ([#5225](https://github.com/leanprover-community/mathlib/pull/5225))
Proves that normal is preserved by an alg_equiv
#### Estimated changes
Modified src/field_theory/normal.lean
- \+ *lemma* alg_equiv.transfer_normal
- \+ *lemma* normal.of_alg_equiv



## [2020-12-12 04:38:13](https://github.com/leanprover-community/mathlib/commit/f51fe7b)
chore(data/fin): Improve docstrings, rename `coe_sub_nat`, add `nat_add_zero` ([#5290](https://github.com/leanprover-community/mathlib/pull/5290))
These are cherry-picked from the tuple PR, [#4406](https://github.com/leanprover-community/mathlib/pull/4406).
`coe_sub_nat` was previously named `sub_nat_coe`, but this didn't match `coe_nat_add` and `coe_add_nat`.
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.coe_sub_nat
- \+ *lemma* fin.nat_add_zero
- \+/\- *def* fin.sub_nat



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
- \+/\- *lemma* category_theory.limits.limit.cone_π



## [2020-12-12 01:48:17](https://github.com/leanprover-community/mathlib/commit/e7ca801)
feat(data/list/chain): induction up the chain ([#5325](https://github.com/leanprover-community/mathlib/pull/5325))
Slightly strengthen statements that were there before
#### Estimated changes
Modified src/category_theory/is_connected.lean


Modified src/data/list/chain.lean
- \+ *lemma* list.chain.induction_head



## [2020-12-12 01:48:13](https://github.com/leanprover-community/mathlib/commit/f0c8a15)
chore(algebra/ordered_ring): golf some proofs using `strict_mono_incr_on` ([#5323](https://github.com/leanprover-community/mathlib/pull/5323))
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* strict_mono_incr_on_mul_self



## [2020-12-12 01:48:10](https://github.com/leanprover-community/mathlib/commit/01746f8)
feat(outer_measure): define bounded_by ([#5314](https://github.com/leanprover-community/mathlib/pull/5314))
`bounded_by` wrapper around `of_function` that drops the condition that `m ∅ = 0`. 
Refactor `Inf_gen` to use `bounded_by`.
I am also planning to use `bounded_by` for finitary products of measures.
Also add some complete lattice lemmas
#### Estimated changes
Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean
- \+ *lemma* measure_theory.outer_measure.Inf_eq_bounded_by_Inf_gen
- \- *lemma* measure_theory.outer_measure.Inf_eq_of_function_Inf_gen
- \+ *lemma* measure_theory.outer_measure.Inf_gen_def
- \- *lemma* measure_theory.outer_measure.Inf_gen_empty
- \- *lemma* measure_theory.outer_measure.Inf_gen_nonempty1
- \- *lemma* measure_theory.outer_measure.Inf_gen_nonempty2
- \+ *def* measure_theory.outer_measure.bounded_by
- \+ *theorem* measure_theory.outer_measure.bounded_by_apply
- \+ *lemma* measure_theory.outer_measure.bounded_by_caratheodory
- \+ *theorem* measure_theory.outer_measure.bounded_by_eq
- \+ *theorem* measure_theory.outer_measure.bounded_by_eq_of_function
- \+ *theorem* measure_theory.outer_measure.bounded_by_le
- \+ *theorem* measure_theory.outer_measure.le_bounded_by'
- \+ *theorem* measure_theory.outer_measure.le_bounded_by
- \+ *lemma* measure_theory.outer_measure.supr_Inf_gen_nonempty

Modified src/order/complete_lattice.lean
- \+ *theorem* binfi_le_of_le
- \+ *theorem* le_bsupr_of_le
- \+ *lemma* le_infi_const
- \+ *lemma* supr_const_le



## [2020-12-12 01:48:08](https://github.com/leanprover-community/mathlib/commit/3782acf)
feat(topology/algebra/*): Criterion to ensure topological monoids and groups ([#5284](https://github.com/leanprover-community/mathlib/pull/5284))
This is old stuff from the perfectoid project that was never PRed and is useful for the liquid tensor experiment.
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.prod_map_map_eq'

Modified src/topology/algebra/group.lean
- \+ *lemma* topological_group.of_comm_of_nhds_one
- \+ *lemma* topological_group.of_nhds_aux
- \+ *lemma* topological_group.of_nhds_one'
- \+ *lemma* topological_group.of_nhds_one

Modified src/topology/algebra/monoid.lean
- \+ *lemma* has_continuous_mul.of_nhds_one
- \+ *lemma* has_continuous_mul_of_comm_of_nhds_one



## [2020-12-11 22:54:52](https://github.com/leanprover-community/mathlib/commit/846ee3f)
feat(data/equiv): symm_symm_apply ([#5324](https://github.com/leanprover-community/mathlib/pull/5324))
A little dsimp lemma that's often helpful
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *theorem* equiv.symm_symm_apply



## [2020-12-11 20:26:08](https://github.com/leanprover-community/mathlib/commit/63e1ad4)
chore(group_theory/perm/basic): Add missing lemmas ([#5320](https://github.com/leanprover-community/mathlib/pull/5320))
These lemmas existed for left multiplication but not right multiplication
#### Estimated changes
Modified src/group_theory/perm/basic.lean
- \+ *lemma* equiv.mul_swap_eq_iff
- \+ *lemma* equiv.mul_swap_involutive
- \+ *lemma* equiv.mul_swap_mul_self

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
- \+ *theorem* subtype.coind_bijective
- \+ *theorem* subtype.coind_surjective
- \+ *lemma* subtype.map_involutive



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
- \+/\- *lemma* real.comap_exp_nhds_within_Ioi_zero
- \+/\- *def* real.exp_order_iso
- \+/\- *lemma* real.log_surjective
- \+/\- *lemma* real.log_zero
- \+/\- *lemma* real.map_exp_at_bot
- \+/\- *lemma* real.range_exp
- \+/\- *lemma* real.range_log
- \+/\- *lemma* real.surj_on_log'
- \+/\- *lemma* real.surj_on_log
- \+/\- *lemma* real.tendsto_exp_at_bot_nhds_within

Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* filter.at_bot_Iio_eq
- \+/\- *lemma* filter.at_top_Ioi_eq
- \+ *lemma* filter.tendsto_Ici_at_top
- \+ *lemma* filter.tendsto_Iic_at_bot
- \+ *lemma* filter.tendsto_Iio_at_bot
- \+ *lemma* filter.tendsto_Ioi_at_top
- \+ *lemma* filter.tendsto_comp_coe_Ici_at_top
- \+ *lemma* filter.tendsto_comp_coe_Iic_at_bot
- \+ *lemma* filter.tendsto_comp_coe_Iio_at_bot
- \+ *lemma* filter.tendsto_comp_coe_Ioi_at_top

Modified src/order/filter/basic.lean
- \+ *lemma* filter.nontrivial_iff_nonempty

Modified src/order/rel_iso.lean
- \+ *lemma* order_iso.range_eq
- \+ *lemma* rel_iso.range_eq

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* comap_coe_Iio_nhds_within_Iio
- \+/\- *lemma* comap_coe_Ioi_nhds_within_Ioi
- \+/\- *lemma* comap_coe_Ioo_nhds_within_Iio
- \+/\- *lemma* comap_coe_Ioo_nhds_within_Ioi
- \+/\- *lemma* comap_coe_nhds_within_Iio_of_Ioo_subset
- \+/\- *lemma* comap_coe_nhds_within_Ioi_of_Ioo_subset
- \+/\- *lemma* map_coe_Iio_at_top
- \+/\- *lemma* map_coe_Ioi_at_bot
- \+/\- *lemma* map_coe_at_bot_of_Ioo_subset
- \+/\- *lemma* map_coe_at_top_of_Ioo_subset
- \+ *lemma* tendsto_Iio_at_top
- \+ *lemma* tendsto_Ioi_at_bot
- \+ *lemma* tendsto_Ioo_at_bot
- \+ *lemma* tendsto_Ioo_at_top
- \+ *lemma* tendsto_comp_coe_Iio_at_top
- \+ *lemma* tendsto_comp_coe_Ioi_at_bot
- \+ *lemma* tendsto_comp_coe_Ioo_at_bot
- \+ *lemma* tendsto_comp_coe_Ioo_at_top

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
- \+ *lemma* div_left_injective
- \+ *lemma* div_right_injective
- \+ *lemma* group.inv_eq_one_div
- \+ *lemma* group.mul_one_div
- \+/\- *theorem* neg_add'
- \- *lemma* sub_left_injective
- \- *lemma* sub_right_injective

Modified src/algebra/group/defs.lean
- \+ *lemma* group.div_eq_mul_inv
- \+/\- *lemma* sub_eq_add_neg

Modified src/algebra/group/hom.lean
- \+/\- *theorem* add_monoid_hom.map_sub

Modified src/algebra/group/pi.lean
- \+/\- *lemma* pi.sub_apply

Modified src/algebra/group/to_additive.lean


Modified src/algebra/group_power/basic.lean


Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* div_eq_inv_mul
- \- *lemma* div_eq_mul_inv
- \+/\- *lemma* div_one
- \+/\- *lemma* div_self
- \+/\- *lemma* one_div
- \+/\- *lemma* zero_div

Modified src/algebra/group_with_zero/defs.lean
- \+ *lemma* div_eq_mul_inv

Modified src/algebra/group_with_zero/power.lean


Modified src/algebra/module/basic.lean


Modified src/algebra/ordered_group.lean
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
- \+ *def* continuous_multilinear_curry_right_equiv'
- \+ *lemma* continuous_multilinear_curry_right_equiv_apply'
- \+ *lemma* continuous_multilinear_curry_right_equiv_symm_apply'

Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/trigonometric.lean
- \+/\- *lemma* real.angle.coe_sub

Modified src/data/complex/exponential.lean


Modified src/data/fintype/card.lean


Modified src/data/int/cast.lean


Modified src/data/list/basic.lean


Modified src/data/matrix/basic.lean
- \+/\- *theorem* matrix.add_apply
- \+/\- *theorem* matrix.neg_apply
- \+ *theorem* matrix.sub_apply
- \+/\- *theorem* matrix.zero_apply

Modified src/data/mv_polynomial/comm_ring.lean


Modified src/data/num/lemmas.lean


Modified src/data/padics/hensel.lean


Modified src/data/polynomial/degree/definitions.lean


Modified src/data/polynomial/div.lean


Modified src/data/polynomial/monic.lean
- \+ *lemma* polynomial.monic_sub_of_left
- \+ *lemma* polynomial.monic_sub_of_right

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
- \+/\- *theorem* tactic.ring.add_neg_eq_sub

Modified src/tactic/ring_exp.lean
- \+/\- *lemma* tactic.ring_exp.div_pf
- \+/\- *lemma* tactic.ring_exp.sub_pf

Modified src/topology/algebra/group.lean
- \+ *lemma* is_closed_map_div_right
- \+ *lemma* is_open_map_div_right

Modified src/topology/algebra/group_with_zero.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/pi_Lp.lean




## [2020-12-11 12:35:50](https://github.com/leanprover-community/mathlib/commit/d2ae4e2)
feat(ring_theory/witt_vector): truncated Witt vectors, definition and ring structure ([#5162](https://github.com/leanprover-community/mathlib/pull/5162))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Added src/ring_theory/witt_vector/truncated.lean
- \+ *def* truncated_witt_vector.coeff
- \+ *lemma* truncated_witt_vector.coeff_mk
- \+ *lemma* truncated_witt_vector.coeff_out
- \+ *lemma* truncated_witt_vector.coeff_zero
- \+ *lemma* truncated_witt_vector.ext
- \+ *lemma* truncated_witt_vector.ext_iff
- \+ *def* truncated_witt_vector.mk
- \+ *lemma* truncated_witt_vector.mk_coeff
- \+ *def* truncated_witt_vector.out
- \+ *lemma* truncated_witt_vector.out_injective
- \+ *lemma* truncated_witt_vector.truncate_fun_out
- \+ *def* truncated_witt_vector
- \+ *lemma* witt_vector.coeff_truncate_fun
- \+ *lemma* witt_vector.out_truncate_fun
- \+ *def* witt_vector.truncate_fun
- \+ *lemma* witt_vector.truncate_fun_add
- \+ *lemma* witt_vector.truncate_fun_mul
- \+ *lemma* witt_vector.truncate_fun_neg
- \+ *lemma* witt_vector.truncate_fun_one
- \+ *lemma* witt_vector.truncate_fun_surjective
- \+ *lemma* witt_vector.truncate_fun_zero



## [2020-12-11 10:57:57](https://github.com/leanprover-community/mathlib/commit/6288eed)
feat(linear_algebra/alternating): Add alternatization of multilinear_map ([#5187](https://github.com/leanprover-community/mathlib/pull/5187))
This adds:
* `def multilinear_map.alternatize`
* `lemma alternating_map.to_multilinear_map_alternize`
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *lemma* alternating_map.to_multilinear_map_alternization
- \+ *def* multilinear_map.alternatization
- \+ *lemma* multilinear_map.alternatization_apply



## [2020-12-11 01:46:47](https://github.com/leanprover-community/mathlib/commit/dbdba55)
chore(scripts): update nolints.txt ([#5313](https://github.com/leanprover-community/mathlib/pull/5313))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-12-11 01:46:45](https://github.com/leanprover-community/mathlib/commit/8817c3e)
chore(linear_algebra/tensor_product): Relax the ring requirement to semiring for the group instance ([#5305](https://github.com/leanprover-community/mathlib/pull/5305))
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean
- \+/\- *theorem* linear_map.map_neg₂
- \+ *def* tensor_product.neg.aux
- \+ *theorem* tensor_product.neg.aux_of
- \+/\- *lemma* tensor_product.neg_tmul



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
- \+ *lemma* set.subset_singleton_iff

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.is_open_singleton_iff

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
- \+ *lemma* simple_graph.edge_mem_other_incident_set

Added src/combinatorics/simple_graph/degree_sum.lean
- \+ *def* simple_graph.dart.edge
- \+ *lemma* simple_graph.dart.edge_fiber
- \+ *lemma* simple_graph.dart.edge_mem
- \+ *def* simple_graph.dart.rev
- \+ *lemma* simple_graph.dart.rev_edge
- \+ *lemma* simple_graph.dart.rev_involutive
- \+ *lemma* simple_graph.dart.rev_ne
- \+ *lemma* simple_graph.dart.rev_rev
- \+ *lemma* simple_graph.dart_card_eq_sum_degrees
- \+ *lemma* simple_graph.dart_card_eq_twice_card_edges
- \+ *lemma* simple_graph.dart_edge_eq_iff
- \+ *lemma* simple_graph.dart_edge_fiber_card
- \+ *lemma* simple_graph.dart_fst_fiber
- \+ *lemma* simple_graph.dart_fst_fiber_card_eq_degree
- \+ *def* simple_graph.dart_of_neighbor_set
- \+ *lemma* simple_graph.dart_of_neighbor_set_injective
- \+ *theorem* simple_graph.even_card_odd_degree_vertices
- \+ *lemma* simple_graph.exists_ne_odd_degree_of_exists_odd_degree
- \+ *lemma* simple_graph.odd_card_odd_degree_vertices_ne
- \+ *theorem* simple_graph.sum_degrees_eq_twice_card_edges

Modified src/data/sym2.lean


Added src/data/zmod/parity.lean
- \+ *lemma* zmod.eq_one_iff_odd
- \+ *lemma* zmod.eq_zero_iff_even
- \+ *lemma* zmod.ne_zero_iff_odd



## [2020-12-10 23:19:05](https://github.com/leanprover-community/mathlib/commit/918d5a9)
chore(data/finsupp/basic): redefine `finsupp.filter` ([#5310](https://github.com/leanprover-community/mathlib/pull/5310))
Also use lemmas about `indicator_function` and `function.update` to
golf some proofs about `finsupp.single`.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.add_apply
- \+ *lemma* finsupp.coe_add
- \+ *lemma* finsupp.coe_fn_injective
- \+/\- *lemma* finsupp.ext
- \+/\- *lemma* finsupp.filter_add
- \+ *def* finsupp.filter_add_hom
- \+ *lemma* finsupp.filter_apply
- \+ *lemma* finsupp.filter_eq_indicator
- \+ *lemma* finsupp.filter_eq_sum
- \+ *lemma* finsupp.fun_support_eq
- \- *lemma* finsupp.injective_coe_fn
- \+/\- *lemma* finsupp.single_apply
- \+ *lemma* finsupp.single_apply_eq_zero
- \+ *lemma* finsupp.single_eq_indicator
- \+ *lemma* finsupp.single_eq_update
- \+/\- *lemma* finsupp.support_filter

Modified src/data/polynomial/degree/trailing_degree.lean




## [2020-12-10 23:19:03](https://github.com/leanprover-community/mathlib/commit/c295873)
feat(algebra/module/basic): {nat,int}_smul_apply ([#5308](https://github.com/leanprover-community/mathlib/pull/5308))
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *lemma* add_monoid_hom.int_smul_apply
- \+/\- *lemma* add_monoid_hom.map_int_cast_smul
- \+/\- *lemma* add_monoid_hom.map_int_module_smul
- \+/\- *lemma* add_monoid_hom.map_nat_cast_smul
- \+/\- *lemma* add_monoid_hom.map_rat_cast_smul
- \+/\- *lemma* add_monoid_hom.map_rat_module_smul
- \+ *lemma* add_monoid_hom.nat_smul_apply



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
- \+ *lemma* complex.cos_sq_add_sin_sq
- \+ *lemma* complex.inv_one_add_tan_sq
- \+/\- *lemma* complex.sin_sq_add_cos_sq
- \+ *lemma* complex.tan_mul_cos
- \+ *lemma* complex.tan_sq_div_one_add_tan_sq
- \+ *lemma* real.cos_sq_add_sin_sq
- \+ *lemma* real.inv_one_add_tan_sq
- \+ *lemma* real.inv_sqrt_one_add_tan_sq
- \+/\- *lemma* real.sin_sq_add_cos_sq
- \+ *lemma* real.tan_div_sqrt_one_add_tan_sq
- \+ *lemma* real.tan_mul_cos
- \+ *lemma* real.tan_sq_div_one_add_tan_sq

Modified test/differentiable.lean




## [2020-12-10 21:44:14](https://github.com/leanprover-community/mathlib/commit/32b2e30)
feat(category_theory/monad): special coequalizers for a monad ([#5239](https://github.com/leanprover-community/mathlib/pull/5239))
Two important coequalizer diagrams related to a monad
#### Estimated changes
Added src/category_theory/monad/coequalizer.lean
- \+ *def* category_theory.monad.beck_algebra_coequalizer
- \+ *def* category_theory.monad.beck_algebra_cofork
- \+ *def* category_theory.monad.beck_coequalizer
- \+ *def* category_theory.monad.beck_cofork
- \+ *def* category_theory.monad.beck_split_coequalizer
- \+ *def* category_theory.monad.coequalizer.bottom_map
- \+ *lemma* category_theory.monad.coequalizer.condition
- \+ *def* category_theory.monad.coequalizer.top_map
- \+ *def* category_theory.monad.coequalizer.π



## [2020-12-10 18:39:41](https://github.com/leanprover-community/mathlib/commit/4e8486b)
feat(algebra/group/hom): add_monoid_hom.sub_apply ([#5307](https://github.com/leanprover-community/mathlib/pull/5307))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* add_monoid_hom.sub_apply



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
- \- *def* category_theory.pullback_arrows

Modified src/category_theory/sites/sieves.lean
- \- *def* category_theory.presieve.singleton
- \+/\- *lemma* category_theory.presieve.singleton_self

Modified src/category_theory/sites/spaces.lean




## [2020-12-10 13:58:58](https://github.com/leanprover-community/mathlib/commit/3f42fb4)
feat(group_theory/perm/sign): Add sign_sum_congr ([#5266](https://github.com/leanprover-community/mathlib/pull/5266))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.perm.sum_congr_refl_swap
- \+ *lemma* equiv.perm.sum_congr_swap_refl

Modified src/group_theory/perm/basic.lean
- \+ *lemma* equiv.perm.sum_congr_one_swap
- \+ *lemma* equiv.perm.sum_congr_swap_one

Modified src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.sign_sum_congr



## [2020-12-10 13:58:56](https://github.com/leanprover-community/mathlib/commit/90755c3)
refactor(order/filter/ultrafilter): drop `filter.is_ultrafilter` ([#5264](https://github.com/leanprover-community/mathlib/pull/5264))
Use bundled `ultrafilter`s instead.
#### Estimated changes
Modified src/data/real/hyperreal.lean
- \+/\- *lemma* hyperreal.coe_abs
- \+/\- *lemma* hyperreal.coe_lt_coe
- \+/\- *lemma* hyperreal.coe_max
- \+/\- *lemma* hyperreal.coe_min
- \+/\- *def* hyperreal

Modified src/data/set/basic.lean
- \+ *lemma* subtype.preimage_coe_compl'
- \+ *lemma* subtype.preimage_coe_compl
- \+ *lemma* subtype.preimage_coe_eq_empty

Modified src/order/filter/basic.lean
- \+ *lemma* filter.comap_ne_bot_iff_compl_range
- \+ *lemma* filter.comap_ne_bot_iff_frequently
- \+ *lemma* filter.compl_not_mem_sets
- \+ *lemma* filter.empty_nmem_sets
- \+/\- *lemma* filter.principal_ne_bot_iff

Modified src/order/filter/filter_product.lean
- \+/\- *lemma* filter.germ.abs_def
- \+/\- *lemma* filter.germ.coe_lt
- \+/\- *lemma* filter.germ.coe_pos
- \+/\- *lemma* filter.germ.const_abs
- \+/\- *lemma* filter.germ.const_div
- \+/\- *lemma* filter.germ.const_lt
- \+/\- *lemma* filter.germ.const_max
- \+/\- *lemma* filter.germ.const_min
- \- *lemma* filter.germ.le_def
- \+/\- *lemma* filter.germ.lt_def
- \+/\- *lemma* filter.germ.max_def
- \+/\- *lemma* filter.germ.min_def

Modified src/order/filter/germ.lean
- \+ *lemma* filter.germ.le_def

Modified src/order/filter/ultrafilter.lean
- \+/\- *lemma* filter.bot_ne_hyperfilter
- \+/\- *theorem* filter.compl_mem_hyperfilter_of_finite
- \- *lemma* filter.exists_ultrafilter
- \+/\- *lemma* filter.exists_ultrafilter_iff
- \- *lemma* filter.exists_ultrafilter_of_finite_inter_nonempty
- \+ *lemma* filter.forall_ne_bot_le_iff
- \+/\- *lemma* filter.hyperfilter_le_cofinite
- \- *lemma* filter.hyperfilter_ne_bot
- \- *lemma* filter.is_ultrafilter.em
- \- *lemma* filter.is_ultrafilter.eventually_imp
- \- *lemma* filter.is_ultrafilter.eventually_not
- \- *lemma* filter.is_ultrafilter.eventually_or
- \- *lemma* filter.is_ultrafilter.unique
- \- *def* filter.is_ultrafilter
- \- *lemma* filter.is_ultrafilter_hyperfilter
- \+/\- *lemma* filter.le_iff_ultrafilter
- \- *lemma* filter.le_of_ultrafilter
- \+/\- *theorem* filter.mem_hyperfilter_of_finite_compl
- \+/\- *lemma* filter.mem_iff_ultrafilter
- \- *lemma* filter.mem_of_finite_Union_ultrafilter
- \- *lemma* filter.mem_of_finite_sUnion_ultrafilter
- \- *lemma* filter.mem_or_compl_mem_of_ultrafilter
- \- *lemma* filter.mem_or_mem_of_ultrafilter
- \- *lemma* filter.ne_empty_of_mem_ultrafilter
- \+/\- *theorem* filter.nmem_hyperfilter_of_finite
- \- *lemma* filter.nonempty_of_mem_ultrafilter
- \- *lemma* filter.sup_of_ultrafilters
- \+ *lemma* filter.supr_ultrafilter_le_eq
- \- *def* filter.ultrafilter.bind
- \- *def* filter.ultrafilter.comap
- \- *lemma* filter.ultrafilter.eq_iff_val_le_val
- \- *def* filter.ultrafilter.map
- \- *def* filter.ultrafilter.pure
- \- *def* filter.ultrafilter
- \- *lemma* filter.ultrafilter_bind
- \- *lemma* filter.ultrafilter_iff_compl_mem_iff_not_mem'
- \- *lemma* filter.ultrafilter_iff_compl_mem_iff_not_mem
- \- *lemma* filter.ultrafilter_map
- \- *lemma* filter.ultrafilter_of_le
- \- *lemma* filter.ultrafilter_of_spec
- \- *lemma* filter.ultrafilter_of_ultrafilter
- \- *lemma* filter.ultrafilter_pure
- \- *lemma* filter.ultrafilter_ultrafilter_of'
- \- *lemma* filter.ultrafilter_ultrafilter_of
- \+ *def* ultrafilter.bind
- \+ *lemma* ultrafilter.coe_inj
- \+ *lemma* ultrafilter.coe_injective
- \+ *lemma* ultrafilter.coe_le_coe
- \+ *lemma* ultrafilter.coe_map
- \+ *def* ultrafilter.comap
- \+ *lemma* ultrafilter.compl_mem_iff_not_mem
- \+ *lemma* ultrafilter.compl_not_mem_iff
- \+ *lemma* ultrafilter.empty_not_mem
- \+ *lemma* ultrafilter.eventually_imp
- \+ *lemma* ultrafilter.eventually_not
- \+ *lemma* ultrafilter.eventually_or
- \+ *lemma* ultrafilter.exists_le
- \+ *lemma* ultrafilter.exists_ultrafilter_of_finite_inter_nonempty
- \+ *lemma* ultrafilter.ext
- \+ *lemma* ultrafilter.finite_bUnion_mem_iff
- \+ *lemma* ultrafilter.finite_sUnion_mem_iff
- \+ *lemma* ultrafilter.frequently_iff_eventually
- \+ *lemma* ultrafilter.le_of_inf_ne_bot'
- \+ *lemma* ultrafilter.le_of_inf_ne_bot
- \+ *def* ultrafilter.map
- \+ *lemma* ultrafilter.mem_coe
- \+ *lemma* ultrafilter.mem_map
- \+ *lemma* ultrafilter.mem_or_compl_mem
- \+ *lemma* ultrafilter.mem_pure_sets
- \+ *lemma* ultrafilter.ne_empty_of_mem
- \+ *lemma* ultrafilter.nonempty_of_mem
- \+ *lemma* ultrafilter.of_coe
- \+ *def* ultrafilter.of_compl_not_mem_iff
- \+ *lemma* ultrafilter.of_le
- \+ *lemma* ultrafilter.union_mem_iff
- \+ *lemma* ultrafilter.unique

Modified src/topology/basic.lean
- \+/\- *lemma* continuous_at_iff_ultrafilter
- \- *def* filter.ultrafilter.Lim
- \+ *def* ultrafilter.Lim
- \+ *lemma* ultrafilter.cluster_pt_iff

Modified src/topology/category/Compactum.lean


Modified src/topology/separation.lean
- \- *lemma* is_ultrafilter.Lim_eq_iff_le_nhds
- \+ *lemma* ultrafilter.Lim_eq_iff_le_nhds

Modified src/topology/stone_cech.lean
- \+/\- *lemma* convergent_eqv_pure
- \+/\- *lemma* ultrafilter_comap_pure_nhds

Modified src/topology/subset_properties.lean
- \- *lemma* is_ultrafilter.le_nhds_Lim
- \+ *lemma* ultrafilter.le_nhds_Lim

Modified src/topology/uniform_space/cauchy.lean
- \- *lemma* cauchy_of_totally_bounded_of_ultrafilter
- \+ *lemma* ultrafilter.cauchy_of_totally_bounded



## [2020-12-10 13:58:54](https://github.com/leanprover-community/mathlib/commit/2bf0c2e)
feat(group_theory/group_action/sub_mul_action): add a has_zero instance ([#5216](https://github.com/leanprover-community/mathlib/pull/5216))
#### Estimated changes
Modified src/group_theory/group_action/sub_mul_action.lean
- \+ *lemma* sub_mul_action.zero_mem



## [2020-12-10 10:51:03](https://github.com/leanprover-community/mathlib/commit/702b1e8)
refactor(data/finsupp/basic): merge `finsupp.of_multiset` and `multiset.to_finsupp` ([#5237](https://github.com/leanprover-community/mathlib/pull/5237))
* redefine `finsupp.to_multiset` as an `add_equiv`;
* drop `finsupp.equiv_multiset` and `finsupp.of_multiset`;
* define `multiset.to_finsupp` as `finsupp.to_multiset.symm`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* multiset.to_finset_sum_count_smul_eq

Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.coe_order_iso_multiset
- \+ *lemma* finsupp.coe_order_iso_multiset_symm
- \- *def* finsupp.equiv_multiset
- \+ *lemma* finsupp.le_def
- \+/\- *lemma* finsupp.mem_antidiagonal_support
- \- *def* finsupp.of_multiset
- \- *lemma* finsupp.of_multiset_apply
- \+ *def* finsupp.order_iso_multiset
- \+/\- *lemma* finsupp.prod_to_multiset
- \+/\- *lemma* finsupp.to_finset_to_multiset
- \+/\- *def* finsupp.to_multiset
- \+ *lemma* finsupp.to_multiset_apply
- \+/\- *lemma* finsupp.to_multiset_single
- \+/\- *lemma* finsupp.to_multiset_to_finsupp
- \+/\- *def* multiset.to_finsupp
- \+/\- *lemma* multiset.to_finsupp_add
- \+ *lemma* multiset.to_finsupp_eq_iff
- \+/\- *lemma* multiset.to_finsupp_singleton
- \+/\- *lemma* multiset.to_finsupp_zero
- \+ *lemma* multiset.to_finsuppstrict_mono

Modified src/data/finsupp/lattice.lean
- \- *lemma* finsupp.le_def
- \- *lemma* finsupp.of_multiset_strict_mono
- \- *def* finsupp.order_iso_multiset
- \- *lemma* finsupp.order_iso_multiset_apply
- \- *lemma* finsupp.order_iso_multiset_symm_apply

Modified src/logic/function/basic.lean
- \+ *lemma* function.id_def



## [2020-12-10 08:44:55](https://github.com/leanprover-community/mathlib/commit/ac669c7)
chore(category_theory/limits/preserves): cleanup ([#4163](https://github.com/leanprover-community/mathlib/pull/4163))
(edited to update).
This PR entirely re-does the construction of limits from products and equalizers in a shorter way. With the new preserves limits machinery this new construction also shows that a functor which preserves products and equalizers preserves all limits, which previously was *really* annoying to do
#### Estimated changes
Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean
- \+ *lemma* category_theory.limits.has_limit_of_equalizer_and_product
- \+ *def* category_theory.limits.has_limit_of_has_products_of_has_equalizers.build_is_limit
- \+ *def* category_theory.limits.has_limit_of_has_products_of_has_equalizers.build_limit
- \- *def* category_theory.limits.has_limit_of_has_products_of_has_equalizers.cones_hom
- \- *def* category_theory.limits.has_limit_of_has_products_of_has_equalizers.cones_inv
- \- *def* category_theory.limits.has_limit_of_has_products_of_has_equalizers.cones_iso
- \- *def* category_theory.limits.has_limit_of_has_products_of_has_equalizers.diagram
- \+ *def* category_theory.limits.preserves_finite_limits_of_preserves_equalizers_and_finite_products
- \+ *def* category_theory.limits.preserves_limit_of_preserves_equalizers_and_product
- \+ *def* category_theory.limits.preserves_limits_of_preserves_equalizers_and_products



## [2020-12-10 07:39:19](https://github.com/leanprover-community/mathlib/commit/e68d2d7)
feat(category_theory/sites): category of sheaves ([#5255](https://github.com/leanprover-community/mathlib/pull/5255))
Category of sheaves on a grothendieck topology
(cc: @kckennylau)
#### Estimated changes
Modified src/category_theory/sites/grothendieck.lean


Modified src/category_theory/sites/pretopology.lean


Modified src/category_theory/sites/sheaf.lean
- \+ *def* category_theory.Sheaf
- \+ *def* category_theory.Sheaf_to_presheaf



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
- \+ *lemma* set.indicator_apply_eq_self
- \+ *lemma* set.indicator_apply_eq_zero
- \+ *lemma* set.indicator_eq_self
- \+ *lemma* set.indicator_eq_zero'
- \+ *lemma* set.indicator_eq_zero
- \+/\- *lemma* set.indicator_indicator
- \- *lemma* set.indicator_of_support_subset

Modified src/data/set/function.lean
- \+ *lemma* set.piecewise_singleton

Modified src/measure_theory/interval_integral.lean


Modified src/measure_theory/set_integral.lean




## [2020-12-09 17:36:09](https://github.com/leanprover-community/mathlib/commit/bf25d26)
chore(data/set/intervals/proj_Icc): add `strict_mono_incr_on` ([#5292](https://github.com/leanprover-community/mathlib/pull/5292))
* rename `set.Icc_extend_monotone` to `monotone.Icc_extend`;
* add `set.strict_mono_incr_on_proj_Icc` and `strict_mono.strict_mono_incr_on_Icc_extend`.
#### Estimated changes
Modified src/data/set/intervals/proj_Icc.lean
- \+ *lemma* monotone.Icc_extend
- \- *lemma* set.Icc_extend_monotone
- \+ *lemma* set.strict_mono_incr_on_proj_Icc
- \+ *lemma* strict_mono.strict_mono_incr_on_Icc_extend



## [2020-12-09 17:36:06](https://github.com/leanprover-community/mathlib/commit/efe18d5)
feat(measure_theory/interval_integral): continuous implies interval_integrable ([#5288](https://github.com/leanprover-community/mathlib/pull/5288))
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* continuous.interval_integrable
- \+ *lemma* continuous_on.interval_integrable



## [2020-12-09 17:36:04](https://github.com/leanprover-community/mathlib/commit/e357a33)
chore(linear_algebra/multilinear): Add `linear_map.comp_multilinear_map_dom_dom_congr` ([#5270](https://github.com/leanprover-community/mathlib/pull/5270))
#### Estimated changes
Modified src/linear_algebra/multilinear.lean
- \+ *lemma* linear_map.comp_multilinear_map_dom_dom_congr



## [2020-12-09 17:36:02](https://github.com/leanprover-community/mathlib/commit/698d6b7)
ci(.github/workflows/dependent-issues.yml): automation for "blocked-by-other-PR" label ([#5261](https://github.com/leanprover-community/mathlib/pull/5261))
When a PR or issue is updated, the [dependent-issues](https://github.com/z0al/dependent-issues) action will do the following on all PRs which are marked as dependent on it (with the text `- [ ] depends on: #blah` that we're already using):
- add / remove the "blocked-by-other-PR" label
- post / edit a comment with the current status of its dependencies (this is slightly redundant, given that we have another action which checks off the dependent PRs in the PR comments, but the extra notifications might be useful).
- it also adds a new status check which is pending (yellow) until all dependencies are closed.
#### Estimated changes
Added .github/workflows/dependent-issues.yml




## [2020-12-09 16:13:00](https://github.com/leanprover-community/mathlib/commit/a87f62b)
feat(category_theory/limits/preserves): preserving binary products ([#5061](https://github.com/leanprover-community/mathlib/pull/5061))
This moves and re-does my old file about preserving binary products to match the new API and framework for preservation of special shapes, and also cleans up some existing API. 
(I can split this up if necessary but they're all pretty minor changes, so hope this is okay!)
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean


Modified src/category_theory/limits/preserves/functor_category.lean


Added src/category_theory/limits/preserves/shapes/binary_products.lean
- \+ *def* category_theory.limits.is_limit_map_cone_binary_fan_equiv
- \+ *def* category_theory.limits.is_limit_of_has_binary_product_of_preserves_limit
- \+ *def* category_theory.limits.is_limit_of_reflects_of_map_is_limit
- \+ *def* category_theory.limits.map_is_limit_of_preserves_of_is_limit
- \+ *def* category_theory.limits.preserves_pair.iso
- \+ *lemma* category_theory.limits.preserves_pair.iso_hom
- \+ *def* category_theory.limits.preserves_pair.of_iso_comparison

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *def* category_theory.limits.coprod_is_coprod
- \+/\- *def* category_theory.limits.map_pair
- \+/\- *def* category_theory.limits.prod_comparison
- \+ *def* category_theory.limits.prod_is_prod

Deleted src/category_theory/limits/shapes/constructions/preserve_binary_products.lean
- \- *def* category_theory.limits.alternative_cone
- \- *def* category_theory.limits.alternative_cone_is_limit
- \- *def* category_theory.limits.preserves_binary_prod_of_prod_comparison_iso



## [2020-12-09 09:24:04](https://github.com/leanprover-community/mathlib/commit/d12a731)
chore(data/mv_polynomial): mark `mv_polynomial.ext` as `@[ext]` ([#5289](https://github.com/leanprover-community/mathlib/pull/5289))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* mv_polynomial.ext



## [2020-12-09 04:36:44](https://github.com/leanprover-community/mathlib/commit/1f309c5)
feat(analysis/special_functions): `real.log` is infinitely smooth away from zero ([#5116](https://github.com/leanprover-community/mathlib/pull/5116))
Also redefine it using `order_iso.to_homeomorph` and prove more lemmas about limits of `exp`/`log`.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_on_inv

Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* continuous.log
- \+ *lemma* continuous_at.log
- \+ *lemma* continuous_on.log
- \+ *lemma* continuous_within_at.log
- \+ *lemma* deriv.log
- \- *lemma* deriv_log'
- \+ *lemma* deriv_within.log
- \- *lemma* deriv_within_log'
- \+ *lemma* fderiv.log
- \+ *lemma* fderiv_within.log
- \+ *lemma* filter.tendsto.log
- \+ *lemma* has_fderiv_at.log
- \+ *lemma* has_fderiv_within_at.log
- \+/\- *lemma* measurable.log
- \+ *lemma* real.coe_comp_exp_order_iso
- \+ *lemma* real.coe_exp_order_iso_apply
- \+ *lemma* real.comap_exp_at_top
- \+ *lemma* real.comap_exp_nhds_within_Ioi_zero
- \+/\- *lemma* real.continuous_at_log
- \+ *lemma* real.continuous_at_log_iff
- \+/\- *lemma* real.continuous_log'
- \- *lemma* real.continuous_log
- \+ *lemma* real.continuous_on_log
- \+ *lemma* real.deriv_log'
- \+ *lemma* real.deriv_log
- \+ *lemma* real.differentiable_at_log
- \+ *lemma* real.differentiable_at_log_iff
- \+ *lemma* real.differentiable_on_log
- \- *lemma* real.exists_exp_eq_of_pos
- \+ *def* real.exp_order_iso
- \+ *lemma* real.log_of_ne_zero
- \+ *lemma* real.log_of_pos
- \+ *lemma* real.map_exp_at_bot
- \+ *lemma* real.map_exp_at_top
- \+/\- *lemma* real.range_exp
- \+ *lemma* real.strict_mono_decr_on_log
- \+ *lemma* real.strict_mono_incr_on_log
- \+ *lemma* real.surj_on_log'
- \+ *lemma* real.surj_on_log
- \+ *lemma* real.tendsto_comp_exp_at_bot
- \+ *lemma* real.tendsto_comp_exp_at_top
- \+ *lemma* real.tendsto_exp_at_bot
- \+ *lemma* real.tendsto_exp_at_bot_nhds_within
- \+ *lemma* real.tendsto_exp_comp_at_top
- \+ *lemma* real.tendsto_log_nhds_within_zero
- \- *lemma* real.tendsto_log_one_zero
- \+ *lemma* real.times_cont_diff_at_log
- \+ *lemma* real.times_cont_diff_on_log

Modified src/data/complex/exponential.lean
- \+ *lemma* real.exp_eq_exp
- \+/\- *lemma* real.exp_le_exp
- \+/\- *lemma* real.exp_lt_exp

Modified src/data/set/function.lean
- \+ *lemma* strict_mono.cod_restrict

Modified src/order/rel_iso.lean
- \+ *def* order_iso.set.univ
- \+ *def* order_iso.set_congr

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* intermediate_value_univ
- \+/\- *lemma* intermediate_value_univ₂
- \+/\- *lemma* is_preconnected.intermediate_value
- \+/\- *lemma* is_preconnected.intermediate_value₂
- \+/\- *lemma* mem_range_of_exists_le_of_exists_ge
- \+/\- *lemma* nhds_within_Ici_self_ne_bot
- \+/\- *lemma* nhds_within_Iic_self_ne_bot

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
- \- *lemma* add_aut.apply_inv_self
- \- *lemma* add_aut.coe_mul
- \- *lemma* add_aut.coe_one
- \- *lemma* add_aut.inv_apply_self
- \- *lemma* add_aut.inv_def
- \- *lemma* add_aut.mul_apply
- \- *lemma* add_aut.mul_def
- \- *lemma* add_aut.one_apply
- \- *lemma* add_aut.one_def
- \- *def* add_aut.to_perm
- \- *lemma* mul_aut.apply_inv_self
- \- *lemma* mul_aut.coe_mul
- \- *lemma* mul_aut.coe_one
- \- *def* mul_aut.conj
- \- *lemma* mul_aut.conj_apply
- \- *lemma* mul_aut.conj_inv_apply
- \- *lemma* mul_aut.conj_symm_apply
- \- *lemma* mul_aut.inv_apply_self
- \- *lemma* mul_aut.inv_def
- \- *lemma* mul_aut.mul_apply
- \- *lemma* mul_aut.mul_def
- \- *lemma* mul_aut.one_apply
- \- *lemma* mul_aut.one_def
- \- *def* mul_aut.to_perm
- \- *def* mul_aut

Added src/data/equiv/mul_add_aut.lean
- \+ *lemma* add_aut.apply_inv_self
- \+ *lemma* add_aut.coe_mul
- \+ *lemma* add_aut.coe_one
- \+ *lemma* add_aut.inv_apply_self
- \+ *lemma* add_aut.inv_def
- \+ *lemma* add_aut.mul_apply
- \+ *lemma* add_aut.mul_def
- \+ *lemma* add_aut.one_apply
- \+ *lemma* add_aut.one_def
- \+ *def* add_aut.to_perm
- \+ *lemma* mul_aut.apply_inv_self
- \+ *lemma* mul_aut.coe_mul
- \+ *lemma* mul_aut.coe_one
- \+ *def* mul_aut.conj
- \+ *lemma* mul_aut.conj_apply
- \+ *lemma* mul_aut.conj_inv_apply
- \+ *lemma* mul_aut.conj_symm_apply
- \+ *lemma* mul_aut.inv_apply_self
- \+ *lemma* mul_aut.inv_def
- \+ *lemma* mul_aut.mul_apply
- \+ *lemma* mul_aut.mul_def
- \+ *lemma* mul_aut.one_apply
- \+ *lemma* mul_aut.one_def
- \+ *def* mul_aut.to_perm
- \+ *def* mul_aut

Modified src/data/equiv/ring.lean
- \- *def* ring_aut.to_add_aut
- \- *def* ring_aut.to_mul_aut
- \- *def* ring_aut.to_perm
- \- *def* ring_aut

Added src/data/equiv/ring_aut.lean
- \+ *def* ring_aut.to_add_aut
- \+ *def* ring_aut.to_mul_aut
- \+ *def* ring_aut.to_perm
- \+ *def* ring_aut

Modified src/data/fintype/basic.lean


Modified src/group_theory/group_action/group.lean


Modified src/group_theory/semidirect_product.lean




## [2020-12-08 18:18:54](https://github.com/leanprover-community/mathlib/commit/4c9499f)
chore(algebra/group/pi): Split into multiple files ([#5280](https://github.com/leanprover-community/mathlib/pull/5280))
This allows files that appear before `ordered_group` to still use `pi.monoid` etc.
#### Estimated changes
Modified src/algebra/group/pi.lean
- \- *lemma* pi.div_apply
- \- *lemma* pi.inv_apply
- \- *lemma* pi.mul_apply
- \- *lemma* pi.one_apply

Modified src/algebra/module/ordered.lean


Added src/algebra/ordered_pi.lean


Modified src/data/pi.lean
- \+ *lemma* pi.div_apply
- \+ *lemma* pi.inv_apply
- \+ *lemma* pi.mul_apply
- \+ *lemma* pi.one_apply

Modified src/order/pilex.lean




## [2020-12-08 16:34:05](https://github.com/leanprover-community/mathlib/commit/b5ab2f7)
feat(topology/algebra/ordered): add lemmas about `map coe at_top/at_bot` ([#5238](https://github.com/leanprover-community/mathlib/pull/5238))
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \- *lemma* Ioo_at_bot_eq_nhds_within
- \- *lemma* Ioo_at_top_eq_nhds_within
- \+ *lemma* comap_coe_Iio_nhds_within_Iio
- \+ *lemma* comap_coe_Ioi_nhds_within_Ioi
- \+ *lemma* comap_coe_Ioo_nhds_within_Iio
- \+ *lemma* comap_coe_Ioo_nhds_within_Ioi
- \+ *lemma* comap_coe_nhds_within_Iio_of_Ioo_subset
- \+ *lemma* comap_coe_nhds_within_Ioi_of_Ioo_subset
- \+ *lemma* map_coe_Iio_at_top
- \+ *lemma* map_coe_Ioi_at_bot
- \+ *lemma* map_coe_Ioo_at_bot
- \+ *lemma* map_coe_Ioo_at_top
- \+ *lemma* map_coe_at_bot_of_Ioo_subset
- \+ *lemma* map_coe_at_top_of_Ioo_subset



## [2020-12-08 15:28:08](https://github.com/leanprover-community/mathlib/commit/7f5a5dd)
feat(category_theory/limits): split coequalizers ([#5230](https://github.com/leanprover-community/mathlib/pull/5230))
Define what it means for a triple of morphisms `f g : X ⟶ Y`, `π : Y ⟶ Z` to be a split coequalizer, and show that every split coequalizer is a coequalizer and absolute.
Define split pairs and `G`-split pairs.
These definitions and constructions are useful in particular for the monadicity theorems.
#### Estimated changes
Added src/category_theory/limits/shapes/split_coequalizer.lean
- \+ *def* category_theory.is_split_coequalizer.as_cofork
- \+ *def* category_theory.is_split_coequalizer.is_coequalizer
- \+ *def* category_theory.is_split_coequalizer.map



## [2020-12-08 13:47:48](https://github.com/leanprover-community/mathlib/commit/64ddb12)
feat(analysis/mean_inequalities): add Hölder's inequality for the Lebesgue integral of ennreal and nnreal functions ([#5267](https://github.com/leanprover-community/mathlib/pull/5267))
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *lemma* ennreal.ae_eq_zero_of_lintegral_rpow_eq_zero
- \+ *lemma* ennreal.fun_eq_fun_mul_inv_snorm_mul_snorm
- \+ *def* ennreal.fun_mul_inv_snorm
- \+ *lemma* ennreal.fun_mul_inv_snorm_rpow
- \+ *lemma* ennreal.lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero
- \+ *theorem* ennreal.lintegral_mul_le_Lp_mul_Lq
- \+ *lemma* ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top
- \+ *lemma* ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top
- \+ *lemma* ennreal.lintegral_mul_le_one_of_lintegral_rpow_eq_one
- \+ *lemma* ennreal.lintegral_rpow_fun_mul_inv_snorm_eq_one
- \+ *theorem* nnreal.lintegral_mul_le_Lp_mul_Lq

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* ennreal.inv_rpow_of_pos
- \+ *lemma* nnreal.of_real_rpow_of_nonneg

Modified src/data/real/conjugate_exponents.lean
- \+ *lemma* real.is_conjugate_exponent.inv_add_inv_conj_ennreal

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.of_real_div_of_pos
- \+ *lemma* ennreal.of_real_inv_of_pos

Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.lintegral_zero_fun



## [2020-12-08 10:43:05](https://github.com/leanprover-community/mathlib/commit/3996bd4)
chore(logic/basic): add a few `simp` lemmas ([#5278](https://github.com/leanprover-community/mathlib/pull/5278))
Also add `fintype.prod_eq_single`.
#### Estimated changes
Modified archive/arithcc.lean


Modified src/data/fintype/card.lean
- \+ *lemma* fintype.prod_eq_single

Modified src/data/matrix/basic.lean


Modified src/logic/basic.lean
- \+ *theorem* decidable.not_imp_self
- \+ *theorem* imp_not_self
- \+ *lemma* ite_eq_left_iff
- \+ *lemma* ite_eq_right_iff
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
- \+ *lemma* max_eq_left_iff
- \+ *lemma* max_eq_right_iff
- \+ *lemma* min_eq_left_iff
- \+ *lemma* min_eq_right_iff

Modified src/analysis/analytic/composition.lean


Modified src/combinatorics/composition.lean
- \+/\- *def* composition.boundary
- \+ *lemma* composition.coe_embedding
- \+ *lemma* composition.coe_inv_embedding
- \+/\- *def* composition.embedding
- \- *lemma* composition.embedding_injective
- \+/\- *lemma* composition.ones_blocks
- \+/\- *lemma* composition.single_blocks
- \+/\- *lemma* composition.single_length
- \- *lemma* composition.strict_mono_boundary



## [2020-12-08 10:43:00](https://github.com/leanprover-community/mathlib/commit/51f5ca3)
chore(group_theory/perm): Add alternate formulation of (sum|sigma)_congr lemmas ([#5260](https://github.com/leanprover-community/mathlib/pull/5260))
These lemmas existed already for `equiv`, but not for `perm` or for `perm` via group structures.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.perm.sigma_congr_right
- \+ *lemma* equiv.perm.sigma_congr_right_refl
- \+ *lemma* equiv.perm.sigma_congr_right_symm
- \+ *lemma* equiv.perm.sigma_congr_right_trans
- \+ *def* equiv.perm.sum_congr
- \+ *lemma* equiv.perm.sum_congr_apply
- \+ *lemma* equiv.perm.sum_congr_refl
- \+ *lemma* equiv.perm.sum_congr_symm
- \+ *lemma* equiv.perm.sum_congr_trans
- \+/\- *lemma* equiv.sum_congr_symm

Modified src/group_theory/perm/basic.lean
- \+ *lemma* equiv.perm.sigma_congr_right_inv
- \+ *lemma* equiv.perm.sigma_congr_right_mul
- \+ *lemma* equiv.perm.sigma_congr_right_one
- \+ *lemma* equiv.perm.sum_congr_inv
- \+ *lemma* equiv.perm.sum_congr_mul
- \+ *lemma* equiv.perm.sum_congr_one



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
- \- *theorem* set.disjoint_compl_left
- \- *theorem* set.disjoint_compl_right
- \+ *theorem* set.disjoint_empty
- \+ *theorem* set.empty_disjoint

Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/matrix.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/set_integral.lean


Modified src/order/boolean_algebra.lean
- \+ *theorem* disjoint_compl_left
- \+ *theorem* disjoint_compl_right

Modified src/order/bounded_lattice.lean
- \+/\- *theorem* disjoint_bot_left
- \+/\- *theorem* disjoint_bot_right
- \+ *theorem* disjoint_top
- \+ *theorem* top_disjoint

Modified src/ring_theory/localization.lean




## [2020-12-08 07:36:17](https://github.com/leanprover-community/mathlib/commit/ef377a9)
chore(data/list/sort): docs, add a few lemmas ([#5274](https://github.com/leanprover-community/mathlib/pull/5274))
 * Add a module docstring and section headers.
* Rename `list.eq_of_sorted_of_perm` to `list.eq_of_perm_of_sorted`;
  the new name reflects the order of arguments.
* Add a few lemmas.
#### Estimated changes
Modified src/data/list/sort.lean
- \+ *theorem* list.eq_of_perm_of_sorted
- \- *theorem* list.eq_of_sorted_of_perm
- \+ *lemma* list.insertion_sort_cons_eq_take_drop
- \+/\- *lemma* list.length_merge_sort
- \+ *theorem* list.merge_sort_eq_insertion_sort
- \+/\- *theorem* list.merge_sort_eq_self
- \+ *lemma* list.ordered_insert_eq_take_drop
- \+/\- *theorem* list.perm_insertion_sort
- \+/\- *theorem* list.perm_merge
- \+/\- *theorem* list.perm_merge_sort
- \+/\- *theorem* list.perm_ordered_insert
- \+ *lemma* list.sorted.insertion_sort_eq
- \+ *theorem* list.sorted.merge
- \+ *theorem* list.sorted.ordered_insert
- \+/\- *theorem* list.sorted_insertion_sort
- \- *theorem* list.sorted_merge
- \+/\- *theorem* list.sorted_merge_sort
- \- *theorem* list.sorted_ordered_insert

Modified src/data/multiset/sort.lean




## [2020-12-08 07:36:15](https://github.com/leanprover-community/mathlib/commit/aec64b1)
feat(category_theory/monad): generalise algebra colimits ([#5234](https://github.com/leanprover-community/mathlib/pull/5234))
Assumption generalisations and universe generalisations
#### Estimated changes
Modified src/category_theory/monad/limits.lean
- \+ *def* category_theory.monadic_creates_colimit_of_preserves_colimit

Modified src/topology/category/UniformSpace.lean




## [2020-12-08 07:36:13](https://github.com/leanprover-community/mathlib/commit/7360178)
feat(category_theory/closed/types): presheaf category is cartesian closed ([#4897](https://github.com/leanprover-community/mathlib/pull/4897))
#### Estimated changes
Added src/category_theory/closed/types.lean


Modified src/category_theory/limits/preserves/limits.lean
- \+ *lemma* category_theory.lift_comp_preserves_limits_iso_hom
- \+ *def* category_theory.preserves_colimit_iso
- \+ *lemma* category_theory.preserves_colimits_iso_inv_comp_desc
- \+ *lemma* category_theory.preserves_desc_map_cocone
- \+ *lemma* category_theory.preserves_lift_map_cone
- \+ *def* category_theory.preserves_limit_iso
- \+ *lemma* category_theory.preserves_limits_iso_hom_π
- \+ *lemma* category_theory.preserves_limits_iso_inv_π
- \+ *lemma* category_theory.ι_preserves_colimits_iso_hom
- \+ *lemma* category_theory.ι_preserves_colimits_iso_inv
- \- *lemma* lift_comp_preserves_limits_iso_hom
- \- *def* preserves_colimit_iso
- \- *lemma* preserves_colimits_iso_inv_comp_desc
- \- *lemma* preserves_desc_map_cocone
- \- *lemma* preserves_lift_map_cone
- \- *def* preserves_limit_iso
- \- *lemma* preserves_limits_iso_hom_π
- \- *lemma* preserves_limits_iso_inv_π
- \- *lemma* ι_preserves_colimits_iso_hom
- \- *lemma* ι_preserves_colimits_iso_inv



## [2020-12-08 05:05:55](https://github.com/leanprover-community/mathlib/commit/8f42d73)
chore(data/list/pairwise): add `list.pairwise_pmap` and `list.pairwise.pmap` ([#5273](https://github.com/leanprover-community/mathlib/pull/5273))
Also add `list.pairwise.tail` and use it in the proof of `list.sorted.tail`.
#### Estimated changes
Modified src/data/list/pairwise.lean
- \+ *theorem* list.pairwise.pmap
- \+ *theorem* list.pairwise.tail
- \+ *theorem* list.pairwise_pmap

Modified src/data/list/sort.lean
- \+/\- *theorem* list.sorted.tail



## [2020-12-08 03:20:13](https://github.com/leanprover-community/mathlib/commit/3f4829c)
chore(data/support): zero function has empty support ([#5275](https://github.com/leanprover-community/mathlib/pull/5275))
#### Estimated changes
Modified src/data/support.lean
- \+ *lemma* function.support_zero'
- \+ *lemma* function.support_zero



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
- \+/\- *def* fin.add_nat
- \+/\- *def* fin.cast
- \+/\- *def* fin.cast_add
- \+/\- *def* fin.cast_le
- \- *lemma* fin.cast_le_injective
- \+/\- *lemma* fin.cast_lt_cast_succ
- \+/\- *def* fin.cast_succ
- \+/\- *lemma* fin.cast_succ_inj
- \+/\- *lemma* fin.coe_add_nat
- \+/\- *lemma* fin.coe_cast
- \+/\- *lemma* fin.coe_cast_add
- \+/\- *lemma* fin.coe_cast_le
- \+/\- *lemma* fin.coe_cast_lt
- \+/\- *lemma* fin.coe_cast_succ
- \+ *def* fin.coe_embedding
- \+/\- *lemma* fin.coe_last
- \+ *lemma* fin.coe_nat_add
- \- *lemma* fin.coe_sub_nat
- \+ *lemma* fin.coe_succ_embedding
- \+/\- *def* fin.nat_add
- \+/\- *def* fin.sub_nat
- \+/\- *def* fin.succ_above
- \+ *lemma* fin.succ_above_aux
- \+ *lemma* fin.succ_above_last_apply
- \+/\- *lemma* fin.succ_above_zero
- \+ *def* fin.succ_embedding
- \+ *lemma* fin.symm_cast

Modified src/order/basic.lean


Modified src/order/rel_iso.lean
- \- *def* fin.val.rel_embedding
- \- *def* fin_fin.rel_embedding
- \+ *lemma* order_embedding.apply_eq_apply
- \+ *lemma* order_embedding.apply_le_apply
- \+ *lemma* order_embedding.apply_lt_apply
- \+ *lemma* order_embedding.coe_of_strict_mono



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
- \+ *lemma* equiv.of_bijective_apply_symm_apply
- \+ *lemma* equiv.of_bijective_symm_apply_apply

Modified src/dynamics/circle/rotation_number/translation_number.lean
- \+ *lemma* circle_deg1_lift.coe_to_order_iso
- \+ *lemma* circle_deg1_lift.coe_to_order_iso_inv
- \+ *lemma* circle_deg1_lift.coe_to_order_iso_symm
- \+ *lemma* circle_deg1_lift.continuous_iff_surjective
- \+ *lemma* circle_deg1_lift.is_unit_iff_bijective
- \+ *lemma* circle_deg1_lift.map_lt_add_floor_translation_number_add_one
- \+ *lemma* circle_deg1_lift.map_lt_add_translation_number_add_one
- \+ *lemma* circle_deg1_lift.semiconj_of_bijective_of_translation_number_eq
- \+ *lemma* circle_deg1_lift.semiconj_of_group_action_of_forall_translation_number_eq
- \+ *lemma* circle_deg1_lift.semiconj_of_is_unit_of_translation_number_eq
- \+ *lemma* circle_deg1_lift.strict_mono_iff_injective
- \+ *def* circle_deg1_lift.to_order_iso
- \+ *lemma* circle_deg1_lift.translation_number_gpow
- \- *lemma* circle_deg1_lift.translation_number_map_id
- \+ *lemma* circle_deg1_lift.translation_number_one
- \+ *lemma* circle_deg1_lift.translation_number_units_inv
- \+ *lemma* circle_deg1_lift.units_apply_inv_apply
- \+ *lemma* circle_deg1_lift.units_inv_apply_apply
- \+ *lemma* circle_deg1_lift.units_semiconj_of_translation_number_eq

Modified src/order/basic.lean
- \+ *lemma* monotone.strict_mono_iff_injective



## [2020-12-07 08:45:14](https://github.com/leanprover-community/mathlib/commit/f0ceb6b)
feat(analysis/mean_inequalities): add young_inequality for nnreal and ennreal with real exponents ([#5242](https://github.com/leanprover-community/mathlib/pull/5242))
The existing young_inequality for nnreal has nnreal exponents. This adds a version with real exponents with the is_conjugate_exponent property, and a similar version for ennreal with real exponents.
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *theorem* ennreal.young_inequality
- \+ *theorem* nnreal.young_inequality_real

Modified src/data/real/conjugate_exponents.lean
- \+ *lemma* real.is_conjugate_exponent.inv_add_inv_conj_nnreal
- \+ *lemma* real.is_conjugate_exponent.one_lt_nnreal

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.of_real_div'
- \+ *lemma* nnreal.of_real_div
- \+ *lemma* nnreal.of_real_inv



## [2020-12-07 06:49:09](https://github.com/leanprover-community/mathlib/commit/914d2b1)
chore(topology/category/Profinite): Fix docstring ([#5265](https://github.com/leanprover-community/mathlib/pull/5265))
#### Estimated changes
Modified src/topology/category/Profinite.lean




## [2020-12-07 03:33:52](https://github.com/leanprover-community/mathlib/commit/b2427d5)
feat(order/filter/ultrafilter): Restriction of ultrafilters along large embeddings ([#5195](https://github.com/leanprover-community/mathlib/pull/5195))
This PR adds the fact that the `comap` of an ultrafilter along a "large" embedding (meaning the image is large w.r.t. the ultrafilter) is again an ultrafilter.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.range_diff_image
- \+ *lemma* set.range_diff_image_subset

Modified src/order/filter/basic.lean
- \+ *lemma* filter.image_mem_map_iff
- \+ *lemma* filter.mem_comap_iff

Modified src/order/filter/ultrafilter.lean
- \+ *def* filter.ultrafilter.comap



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
- \+/\- *lemma* intermediate_value_Icc'
- \+/\- *lemma* intermediate_value_Icc
- \+ *lemma* mem_range_of_exists_le_of_exists_ge
- \+/\- *lemma* surjective_of_continuous'
- \+/\- *lemma* surjective_of_continuous



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
Added src/number_theory/primes_congruent_one.lean
- \+ *lemma* nat.exists_prime_ge_modeq_one
- \+ *lemma* nat.frequently_at_top_modeq_one
- \+ *lemma* nat.infinite_set_of_prime_modeq_one

Modified src/order/filter/cofinite.lean
- \+ *lemma* nat.frequently_at_top_iff_infinite

Modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* polynomial.degree_cyclotomic_pos



## [2020-12-06 18:56:25](https://github.com/leanprover-community/mathlib/commit/b3aa052)
feat(combinatorics/simple_graph/basic): introduce incidence sets, graph construction from relation ([#5191](https://github.com/leanprover-community/mathlib/pull/5191))
Add incidence sets and some lemmas, including a proof of equivalence between the neighbor set of a vertex and its incidence set. Add a graph construction from a given relation.
Definitions and lemmas adapted from [simple_graphs2](https://github.com/leanprover-community/mathlib/blob/simple_graphs2/src/combinatorics/simple_graph/basic.lean#L317)
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* simple_graph.adj_incidence_set_inter
- \+ *lemma* simple_graph.card_incidence_set_eq_degree
- \+ *lemma* simple_graph.degree_pos_iff_exists_adj
- \+ *lemma* simple_graph.edge_set_univ_card
- \+ *def* simple_graph.from_rel
- \+ *lemma* simple_graph.from_rel_adj
- \+ *def* simple_graph.incidence_finset
- \+ *lemma* simple_graph.incidence_other_neighbor_edge
- \+ *lemma* simple_graph.incidence_other_prop
- \+ *def* simple_graph.incidence_set
- \+ *def* simple_graph.incidence_set_equiv_neighbor_set
- \+ *lemma* simple_graph.incidence_set_subset
- \+ *def* simple_graph.max_degree
- \+ *lemma* simple_graph.mem_incidence_finset
- \+ *lemma* simple_graph.mem_incidence_iff_neighbor
- \+ *lemma* simple_graph.mem_incidence_set
- \+ *def* simple_graph.min_degree
- \+ *def* simple_graph.other_vertex_of_incident



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
- \+/\- *def* complex.continuous_linear_map.im
- \+/\- *def* complex.continuous_linear_map.of_real
- \+/\- *def* complex.continuous_linear_map.re
- \+ *lemma* complex.dist_eq

Modified src/analysis/complex/polynomial.lean
- \- *lemma* complex.exists_forall_abs_polynomial_eval_le

Modified src/analysis/normed_space/basic.lean


Modified src/data/padics/hensel.lean


Modified src/measure_theory/borel_space.lean


Modified src/topology/algebra/polynomial.lean
- \- *lemma* polynomial.continuous_eval
- \+ *lemma* polynomial.exists_forall_norm_le
- \+ *lemma* polynomial.tendsto_abv_aeval_at_top
- \+ *lemma* polynomial.tendsto_abv_at_top
- \+ *lemma* polynomial.tendsto_abv_eval₂_at_top
- \- *lemma* polynomial.tendsto_infinity
- \+ *lemma* polynomial.tendsto_norm_at_top

Deleted src/topology/instances/complex.lean
- \- *lemma* complex.continuous.inv
- \- *lemma* complex.continuous_abs
- \- *lemma* complex.continuous_im
- \- *lemma* complex.continuous_inv
- \- *lemma* complex.continuous_of_real
- \- *lemma* complex.continuous_re
- \- *theorem* complex.dist_eq
- \- *def* complex.real_prod_homeo
- \- *lemma* complex.tendsto_inv
- \- *lemma* complex.uniform_continuous_abs
- \- *theorem* complex.uniform_continuous_add
- \- *lemma* complex.uniform_continuous_im
- \- *lemma* complex.uniform_continuous_inv
- \- *lemma* complex.uniform_continuous_mul
- \- *lemma* complex.uniform_continuous_mul_const
- \- *theorem* complex.uniform_continuous_neg
- \- *lemma* complex.uniform_continuous_of_real
- \- *lemma* complex.uniform_continuous_re



## [2020-12-06 10:31:29](https://github.com/leanprover-community/mathlib/commit/29a1731)
feat(ring_theory/witt_vector): common identities between operators on Witt vectors ([#5161](https://github.com/leanprover-community/mathlib/pull/5161))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Added src/ring_theory/witt_vector/identities.lean
- \+ *lemma* witt_vector.coeff_p_pow
- \+ *lemma* witt_vector.frobenius_verschiebung
- \+ *lemma* witt_vector.verschiebung_mul_frobenius
- \+ *lemma* witt_vector.verschiebung_zmod



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
- \+ *lemma* polynomial.derivative_X_pow
- \+ *lemma* polynomial.derivative_bit0
- \+ *lemma* polynomial.derivative_bit1

Modified test/differentiable.lean




## [2020-12-06 07:55:21](https://github.com/leanprover-community/mathlib/commit/c6de6e4)
chore(algebra/group_power): mark `map_pow` etc as `@[simp]` ([#5253](https://github.com/leanprover-community/mathlib/pull/5253))
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+/\- *theorem* add_monoid_hom.map_nsmul
- \+/\- *theorem* monoid_hom.map_pow

Modified src/algebra/group_power/lemmas.lean
- \+/\- *theorem* add_monoid_hom.map_gsmul
- \+/\- *theorem* monoid_hom.map_gpow



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
- \+/\- *def* multiset.card
- \+/\- *theorem* multiset.card_add
- \+/\- *theorem* multiset.count_eq_zero



## [2020-12-05 20:21:02](https://github.com/leanprover-community/mathlib/commit/1f64814)
chore(data/equiv/ring): add `symm_symm` and `coe_symm_mk` ([#5227](https://github.com/leanprover-community/mathlib/pull/5227))
Also generalize `map_mul` and `map_add` to `[has_mul R] [has_add R]`
instead of `[semiring R]`.
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.coe_symm_mk
- \+/\- *lemma* ring_equiv.map_add
- \+/\- *lemma* ring_equiv.map_mul
- \+ *lemma* ring_equiv.symm_symm



## [2020-12-05 18:53:49](https://github.com/leanprover-community/mathlib/commit/d4bd4cd)
fix(topology/algebra/infinite_sum): fix docstring typos and add example ([#5159](https://github.com/leanprover-community/mathlib/pull/5159))
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean




## [2020-12-05 16:59:01](https://github.com/leanprover-community/mathlib/commit/83b13d1)
feat(category_theory/limits): morphisms to equalizer ([#5233](https://github.com/leanprover-community/mathlib/pull/5233))
The natural bijection for morphisms to an equalizer and the dual.
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* category_theory.limits.cofork.is_colimit.hom_iso
- \+ *lemma* category_theory.limits.cofork.is_colimit.hom_iso_natural
- \+ *def* category_theory.limits.fork.is_limit.hom_iso
- \+ *lemma* category_theory.limits.fork.is_limit.hom_iso_natural



## [2020-12-05 16:58:59](https://github.com/leanprover-community/mathlib/commit/dd11498)
chore(linear_algebra/basic): redefine `restrict` ([#5229](https://github.com/leanprover-community/mathlib/pull/5229))
Use `dom_restrict` and `cod_restrict`
#### Estimated changes
Modified src/linear_algebra/basic.lean




## [2020-12-05 13:48:51](https://github.com/leanprover-community/mathlib/commit/481f5e0)
chore(data/prod): `prod.swap` is `bijective` ([#5226](https://github.com/leanprover-community/mathlib/pull/5226))
#### Estimated changes
Modified src/data/prod.lean
- \+ *lemma* prod.swap_bijective
- \+ *lemma* prod.swap_inj
- \+ *lemma* prod.swap_injective
- \+ *lemma* prod.swap_surjective



## [2020-12-05 09:58:53](https://github.com/leanprover-community/mathlib/commit/c5009dd)
chore(data/equiv/basic): Add missing refl/trans/symm simp lemmas ([#5223](https://github.com/leanprover-community/mathlib/pull/5223))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.sigma_congr_right_refl
- \+ *lemma* equiv.sigma_congr_right_symm
- \+ *lemma* equiv.sigma_congr_right_trans
- \+ *lemma* equiv.sum_congr_refl
- \+ *lemma* equiv.sum_congr_trans



## [2020-12-05 07:50:28](https://github.com/leanprover-community/mathlib/commit/3972da8)
chore(category_theory/limits/preserves): make names consistent ([#5240](https://github.com/leanprover-community/mathlib/pull/5240))
adjusted names and namespaces to match [#5044](https://github.com/leanprover-community/mathlib/pull/5044)
#### Estimated changes
Modified src/category_theory/limits/preserves/shapes/products.lean
- \+ *def* category_theory.limits.is_limit_fan_mk_obj_of_is_limit
- \+ *def* category_theory.limits.is_limit_map_cone_fan_mk_equiv
- \+ *def* category_theory.limits.is_limit_of_has_product_of_preserves_limit
- \+ *def* category_theory.limits.is_limit_of_is_limit_fan_mk_obj
- \+ *def* category_theory.limits.preserves_product.iso
- \+ *lemma* category_theory.limits.preserves_product.iso_hom
- \+ *def* category_theory.limits.preserves_product.of_iso_comparison
- \- *def* preserves.fan_map_cone_limit
- \- *def* preserves.is_limit_of_has_product_of_preserves_limit
- \- *def* preserves.is_limit_of_reflects_of_map_is_limit
- \- *def* preserves.map_is_limit_of_preserves_of_is_limit
- \- *def* preserves.preserves_product_of_iso_comparison
- \- *def* preserves.preserves_products_iso
- \- *lemma* preserves.preserves_products_iso_hom

Modified src/topology/sheaves/forget.lean




## [2020-12-05 07:50:26](https://github.com/leanprover-community/mathlib/commit/39a3b58)
feat(order/filter/at_top_bot): `order_iso` maps `at_top` to `at_top` ([#5236](https://github.com/leanprover-community/mathlib/pull/5236))
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* order_iso.comap_at_bot
- \+ *lemma* order_iso.comap_at_top
- \+ *lemma* order_iso.map_at_bot
- \+ *lemma* order_iso.map_at_top
- \+ *lemma* order_iso.tendsto_at_bot
- \+ *lemma* order_iso.tendsto_at_bot_iff
- \+ *lemma* order_iso.tendsto_at_top
- \+ *lemma* order_iso.tendsto_at_top_iff



## [2020-12-05 07:50:24](https://github.com/leanprover-community/mathlib/commit/147a81a)
chore(category_theory/limits): preserving coequalizers ([#5212](https://github.com/leanprover-community/mathlib/pull/5212))
dualise stuff from before
#### Estimated changes
Modified src/category_theory/limits/preserves/shapes/equalizers.lean
- \+ *def* category_theory.limits.is_colimit_cofork_map_of_is_colimit
- \+ *def* category_theory.limits.is_colimit_map_cocone_cofork_equiv
- \+ *def* category_theory.limits.is_colimit_of_has_coequalizer_of_preserves_colimit
- \+ *def* category_theory.limits.is_colimit_of_is_colimit_cofork_map
- \+ *def* category_theory.limits.of_iso_comparison
- \+ *def* category_theory.limits.preserves_coequalizer.iso
- \+ *lemma* category_theory.limits.preserves_coequalizer.iso_hom

Modified src/category_theory/limits/shapes/equalizers.lean




## [2020-12-05 07:50:22](https://github.com/leanprover-community/mathlib/commit/b82eb7a)
refactor(combinatorics/simple_graph/matching): change definition of matching ([#5210](https://github.com/leanprover-community/mathlib/pull/5210))
Refactored definition of matching per @eric-wieser's [suggestion](https://github.com/leanprover-community/mathlib/pull/5156#discussion_r535102524) and @kmill's [suggestion](https://github.com/leanprover-community/mathlib/pull/5156#discussion_r535745112), for the purpose of using `matching.sub_edges` instead of `matching.prop.sub_edges`
#### Estimated changes
Modified src/combinatorics/simple_graph/matching.lean
- \- *def* simple_graph.matching



## [2020-12-05 07:50:19](https://github.com/leanprover-community/mathlib/commit/dc08f4d)
feat(analysis): define asymptotic equivalence of two functions ([#4979](https://github.com/leanprover-community/mathlib/pull/4979))
This defines the relation `is_equivalent u v l`, which means that `u-v` is little o of
`v` along the filter `l`. It is required to state, for example, Stirling's formula, or the prime number theorem
#### Estimated changes
Added src/analysis/asymptotic_equivalent.lean
- \+ *lemma* asymptotics.is_equivalent.div
- \+ *lemma* asymptotics.is_equivalent.exists_eq_mul
- \+ *lemma* asymptotics.is_equivalent.inv
- \+ *lemma* asymptotics.is_equivalent.is_O
- \+ *lemma* asymptotics.is_equivalent.is_O_symm
- \+ *lemma* asymptotics.is_equivalent.is_o
- \+ *lemma* asymptotics.is_equivalent.mul
- \+ *lemma* asymptotics.is_equivalent.refl
- \+ *lemma* asymptotics.is_equivalent.smul
- \+ *lemma* asymptotics.is_equivalent.symm
- \+ *lemma* asymptotics.is_equivalent.tendsto_at_top
- \+ *lemma* asymptotics.is_equivalent.tendsto_at_top_iff
- \+ *lemma* asymptotics.is_equivalent.tendsto_const
- \+ *lemma* asymptotics.is_equivalent.tendsto_nhds
- \+ *lemma* asymptotics.is_equivalent.tendsto_nhds_iff
- \+ *lemma* asymptotics.is_equivalent.trans
- \+ *def* asymptotics.is_equivalent
- \+ *lemma* asymptotics.is_equivalent_const_iff_tendsto
- \+ *lemma* asymptotics.is_equivalent_iff_exists_eq_mul
- \+ *lemma* asymptotics.is_equivalent_iff_tendsto_one
- \+ *lemma* asymptotics.is_equivalent_of_tendsto_one'
- \+ *lemma* asymptotics.is_equivalent_of_tendsto_one
- \+ *lemma* asymptotics.is_equivalent_zero_iff_eventually_zero

Modified src/analysis/asymptotics.lean
- \+ *theorem* asymptotics.is_o_iff_tendsto'

Added src/analysis/normed_space/ordered.lean
- \+ *lemma* is_o_pow_pow_at_top_of_lt
- \+ *lemma* tendsto_pow_div_pow_at_top_of_lt



## [2020-12-05 04:54:08](https://github.com/leanprover-community/mathlib/commit/de7dbbb)
feat(algebra/group): composition of monoid homs as "bilinear" monoid hom ([#5202](https://github.com/leanprover-community/mathlib/pull/5202))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *def* monoid_hom.comp_hom
- \+ *lemma* monoid_hom.comp_mul
- \+ *lemma* monoid_hom.comp_one
- \+ *lemma* monoid_hom.mul_comp
- \+ *lemma* monoid_hom.one_comp
- \+ *lemma* one_hom.comp_one
- \+ *lemma* one_hom.one_comp

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
- \+ *lemma* finsupp.single_of_single_apply



## [2020-12-04 21:26:38](https://github.com/leanprover-community/mathlib/commit/8a9a5d3)
feat(dynamics): (semi-)flows, omega limits ([#4843](https://github.com/leanprover-community/mathlib/pull/4843))
This code has gone through a couple of iterations since it was first written in summer, when the ambition was 'Morse decompositions in Lean' rather than 'mildly generalise some results from a first course in differential equations'. Nevertheless there's much in here I'm not confident about & would appreciate help with.
#### Estimated changes
Added src/dynamics/flow.lean
- \+ *lemma* flow.ext
- \+ *def* flow.from_iter
- \+ *lemma* flow.image_eq_preimage
- \+ *lemma* flow.is_invariant_iff_image_eq
- \+ *lemma* flow.map_add
- \+ *lemma* flow.map_zero
- \+ *lemma* flow.map_zero_apply
- \+ *def* flow.restrict
- \+ *def* flow.reverse
- \+ *def* flow.to_homeomorph
- \+ *lemma* is_fw_invariant.is_invariant
- \+ *def* is_fw_invariant
- \+ *lemma* is_fw_invariant_iff_is_invariant
- \+ *lemma* is_invariant.is_fw_invariant
- \+ *def* is_invariant
- \+ *lemma* is_invariant_iff_image

Added src/dynamics/omega_limit.lean
- \+ *lemma* eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset'
- \+ *lemma* eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset
- \+ *lemma* eventually_closure_subset_of_is_open_of_omega_limit_subset
- \+ *lemma* eventually_maps_to_of_is_compact_absorbing_of_is_open_of_omega_limit_subset
- \+ *lemma* eventually_maps_to_of_is_open_of_omega_limit_subset
- \+ *lemma* flow.is_invariant_omega_limit
- \+ *lemma* flow.omega_limit_image_eq
- \+ *lemma* flow.omega_limit_image_subset
- \+ *lemma* flow.omega_limit_omega_limit
- \+ *lemma* is_closed_omega_limit
- \+ *lemma* maps_to_omega_limit'
- \+ *lemma* maps_to_omega_limit
- \+ *lemma* mem_omega_limit_iff_frequently
- \+ *lemma* mem_omega_limit_iff_frequently₂
- \+ *lemma* mem_omega_limit_singleton_iff_map_cluster_point
- \+ *lemma* nonempty_omega_limit
- \+ *lemma* nonempty_omega_limit_of_is_compact_absorbing
- \+ *def* omega_limit
- \+ *lemma* omega_limit_Inter
- \+ *lemma* omega_limit_Union
- \+ *lemma* omega_limit_def
- \+ *lemma* omega_limit_eq_Inter
- \+ *lemma* omega_limit_eq_Inter_inter
- \+ *lemma* omega_limit_eq_bInter_inter
- \+ *lemma* omega_limit_image_eq
- \+ *lemma* omega_limit_inter
- \+ *lemma* omega_limit_mono_left
- \+ *lemma* omega_limit_mono_right
- \+ *lemma* omega_limit_preimage_subset
- \+ *lemma* omega_limit_subset_closure_fw_image
- \+ *lemma* omega_limit_subset_of_tendsto
- \+ *lemma* omega_limit_union

Modified src/topology/algebra/monoid.lean


Modified src/topology/constructions.lean
- \+ *lemma* continuous_curry
- \+ *lemma* continuous_uncurry_left
- \+ *lemma* continuous_uncurry_of_discrete_topology_left
- \+ *lemma* continuous_uncurry_right



## [2020-12-04 15:57:38](https://github.com/leanprover-community/mathlib/commit/5f43079)
doc(data/quot): Fix typo ([#5221](https://github.com/leanprover-community/mathlib/pull/5221))
#### Estimated changes
Modified src/data/quot.lean




## [2020-12-04 15:57:35](https://github.com/leanprover-community/mathlib/commit/4ea2e68)
chore(algebra/big_operators/basic): Split prod_cancels_of_partition_cancels in two and add a docstring ([#5218](https://github.com/leanprover-community/mathlib/pull/5218))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_partition



## [2020-12-04 15:57:31](https://github.com/leanprover-community/mathlib/commit/5ea96f9)
feat(linear_algebra/multilinear): Add `multilinear_map.coprod` ([#5182](https://github.com/leanprover-community/mathlib/pull/5182))
#### Estimated changes
Modified src/linear_algebra/multilinear.lean
- \+ *def* multilinear_map.dom_coprod'
- \+ *def* multilinear_map.dom_coprod



## [2020-12-04 15:57:29](https://github.com/leanprover-community/mathlib/commit/cb7effa)
feat(ring_theory/discrete_valuation_ring): add additive valuation ([#5094](https://github.com/leanprover-community/mathlib/pull/5094))
Following the approach used for p-adic numbers, we define an additive valuation on a DVR R as a bare function v: R -> nat, with the convention that v(0)=0 instead of +infinity for convenience. Note that we have no `hom` structure (like `monoid_hom` or `add_monoid_hom`) for v(a*b)=v(a)+v(b) and anyway this doesn't even hold if ab=0. We prove all the usual axioms.
#### Estimated changes
Modified src/ring_theory/discrete_valuation_ring.lean
- \+ *lemma* discrete_valuation_ring.add_val_add
- \+ *lemma* discrete_valuation_ring.add_val_def'
- \+ *lemma* discrete_valuation_ring.add_val_def
- \+ *lemma* discrete_valuation_ring.add_val_le_iff_dvd
- \+ *lemma* discrete_valuation_ring.add_val_mul
- \+ *lemma* discrete_valuation_ring.add_val_one
- \+ *lemma* discrete_valuation_ring.add_val_pow
- \+ *theorem* discrete_valuation_ring.add_val_spec
- \+ *lemma* discrete_valuation_ring.add_val_uniformizer
- \+ *lemma* discrete_valuation_ring.add_val_zero
- \+ *lemma* discrete_valuation_ring.eq_unit_mul_pow_irreducible



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
- \+ *lemma* intermediate_field.induction_on_adjoin_fg
- \+ *lemma* intermediate_field.induction_on_adjoin_finset



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
- \- *lemma* category_theory.limits.cocone_of_split_epi_ι_app_one
- \- *lemma* category_theory.limits.cocone_of_split_epi_ι_app_zero
- \+/\- *lemma* category_theory.limits.cofork.condition
- \+/\- *lemma* category_theory.limits.cofork.π_eq_app_one
- \+/\- *lemma* category_theory.limits.cofork.π_of_π
- \- *lemma* category_theory.limits.cone_of_split_mono_π_app_one
- \- *lemma* category_theory.limits.cone_of_split_mono_π_app_zero
- \+/\- *lemma* category_theory.limits.fork.condition
- \+/\- *lemma* category_theory.limits.fork.ι_eq_app_zero
- \+/\- *lemma* category_theory.limits.fork.ι_of_ι
- \+/\- *def* category_theory.limits.split_epi_coequalizes



## [2020-12-04 07:42:59](https://github.com/leanprover-community/mathlib/commit/b2f8c4c)
feat(category_theory/limits): reflects limit if reflects iso and preserves ([#5213](https://github.com/leanprover-community/mathlib/pull/5213))
#### Estimated changes
Modified src/category_theory/limits/preserves/basic.lean
- \+ *def* category_theory.limits.reflects_colimit_of_reflects_isomorphisms
- \+ *def* category_theory.limits.reflects_colimits_of_reflects_isomorphisms
- \+ *def* category_theory.limits.reflects_colimits_of_shape_of_reflects_isomorphisms
- \+ *def* category_theory.limits.reflects_limit_of_reflects_isomorphisms
- \+ *def* category_theory.limits.reflects_limits_of_reflects_isomorphisms
- \+ *def* category_theory.limits.reflects_limits_of_shape_of_reflects_isomorphisms



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
- \+/\- *def* polynomial.derivative
- \+ *lemma* polynomial.derivative_apply
- \+ *lemma* polynomial.derivative_eval
- \- *def* polynomial.derivative_hom
- \- *def* polynomial.derivative_lhom
- \+/\- *lemma* polynomial.derivative_zero

Modified src/data/polynomial/identities.lean
- \- *lemma* polynomial.derivative_eval



## [2020-12-04 07:42:52](https://github.com/leanprover-community/mathlib/commit/240f6eb)
feat(category_theory/monad): cleanups in monad algebra ([#5193](https://github.com/leanprover-community/mathlib/pull/5193))
- Converts the simp normal form for composition of algebra homs to use category notation. 
- Adds simps where appropriate
- Golfs proofs, remove some erw and nonterminal simps
- Remove some redundant brackets
#### Estimated changes
Modified src/category_theory/monad/algebra.lean
- \+ *lemma* category_theory.comonad.coalgebra.comp_eq_comp
- \+ *lemma* category_theory.comonad.coalgebra.comp_f
- \+/\- *def* category_theory.comonad.coalgebra.hom.comp
- \+/\- *def* category_theory.comonad.coalgebra.hom.id
- \+ *lemma* category_theory.comonad.coalgebra.id_eq_id
- \+ *lemma* category_theory.comonad.coalgebra.id_f
- \+ *lemma* category_theory.monad.algebra.comp_eq_comp
- \+ *lemma* category_theory.monad.algebra.comp_f
- \+/\- *def* category_theory.monad.algebra.hom.comp
- \+/\- *def* category_theory.monad.algebra.hom.id
- \+ *lemma* category_theory.monad.algebra.id_eq_id
- \+ *lemma* category_theory.monad.algebra.id_f



## [2020-12-04 07:42:50](https://github.com/leanprover-community/mathlib/commit/c10d1b1)
feat(ring_theory/polynomial/cyclotomic):  add  order_of_root_cyclotomic ([#5151](https://github.com/leanprover-community/mathlib/pull/5151))
Two lemmas about roots of cyclotomic polynomials modulo `p`.
`order_of_root_cyclotomic` is the main algebraic tool to prove the existence of infinitely many primes congruent to `1` modulo `n`.
#### Estimated changes
Modified src/number_theory/divisors.lean
- \+ *lemma* nat.divisors_subset_of_dvd
- \+ *lemma* nat.divisors_subset_proper_divisors

Modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* polynomial.X_pow_sub_one_dvd_prod_cyclotomic
- \+ *lemma* polynomial.coprime_of_root_cyclotomic
- \+/\- *lemma* polynomial.cyclotomic_coeff_zero
- \+ *lemma* polynomial.order_of_root_cyclotomic
- \+ *lemma* polynomial.order_of_root_cyclotomic_dvd



## [2020-12-04 07:42:48](https://github.com/leanprover-community/mathlib/commit/c939c9e)
feat(category_theory/limits/preserves): preserving terminal objects ([#5060](https://github.com/leanprover-community/mathlib/pull/5060))
Another part of [#4716](https://github.com/leanprover-community/mathlib/pull/4716).
#### Estimated changes
Added src/category_theory/limits/preserves/shapes/terminal.lean
- \+ *lemma* category_theory.limits.has_terminal_of_has_terminal_of_preserves_limit
- \+ *def* category_theory.limits.is_limit_map_cone_empty_cone_equiv
- \+ *def* category_theory.limits.is_limit_of_has_terminal_of_preserves_limit
- \+ *def* category_theory.limits.is_terminal_obj_of_is_terminal
- \+ *def* category_theory.limits.is_terminal_of_is_terminal_obj
- \+ *def* category_theory.limits.preserves_terminal.iso
- \+ *lemma* category_theory.limits.preserves_terminal.iso_hom
- \+ *def* category_theory.limits.preserves_terminal.of_iso_comparison
- \+ *def* category_theory.limits.preserves_terminal_of_is_iso
- \+ *def* category_theory.limits.preserves_terminal_of_iso



## [2020-12-04 06:35:18](https://github.com/leanprover-community/mathlib/commit/4f5046d)
feat(ring_theory/polynomial/cyclotomic): Möbius inversion formula for cyclotomic polynomials ([#5192](https://github.com/leanprover-community/mathlib/pull/5192))
Proves Möbius inversion for functions to a `comm_group_with_zero`
Proves the Möbius inversion formula for cyclotomic polynomials
#### Estimated changes
Modified src/number_theory/arithmetic_function.lean
- \+ *theorem* nat.arithmetic_function.prod_eq_iff_prod_pow_moebius_eq_of_nonzero

Modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* polynomial.cyclotomic_eq_prod_X_pow_sub_one_pow_moebius



## [2020-12-04 01:20:37](https://github.com/leanprover-community/mathlib/commit/57dd302)
chore(scripts): update nolints.txt ([#5211](https://github.com/leanprover-community/mathlib/pull/5211))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-12-03 22:25:01](https://github.com/leanprover-community/mathlib/commit/20cc59d)
feat(algebra/lie/basic): define missing inclusion maps ([#5207](https://github.com/leanprover-community/mathlib/pull/5207))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *def* lie_ideal.incl
- \+ *lemma* lie_ideal.incl_apply
- \+ *lemma* lie_submodule.coe_hom_of_le
- \+ *def* lie_submodule.hom_of_le
- \+ *lemma* lie_submodule.hom_of_le_apply
- \+ *def* lie_submodule.incl
- \+ *lemma* lie_submodule.incl_apply
- \+ *lemma* lie_submodule.incl_eq_val

Modified src/algebra/lie/classical.lean




## [2020-12-03 22:24:59](https://github.com/leanprover-community/mathlib/commit/ec839ef)
feat(topology/algebra/order): continuity of monotone functions ([#5199](https://github.com/leanprover-community/mathlib/pull/5199))
Add local versions of `order_iso.continuous`.
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+ *lemma* continuous_at_left_of_mono_incr_on_of_closure_image_mem_nhds_within
- \+ *lemma* continuous_at_left_of_mono_incr_on_of_exists_between
- \+ *lemma* continuous_at_left_of_mono_incr_on_of_image_mem_nhds_within
- \+ *lemma* continuous_at_of_mono_incr_on_of_closure_image_mem_nhds
- \+ *lemma* continuous_at_of_mono_incr_on_of_exists_between
- \+ *lemma* continuous_at_of_mono_incr_on_of_image_mem_nhds
- \+ *lemma* continuous_at_right_of_mono_incr_on_of_closure_image_mem_nhds_within
- \+ *lemma* continuous_at_right_of_mono_incr_on_of_exists_between
- \+ *lemma* continuous_at_right_of_mono_incr_on_of_image_mem_nhds_within
- \+ *lemma* monotone.continuous_of_dense_range
- \+ *lemma* monotone.continuous_of_surjective
- \+ *lemma* strict_mono_incr_on.continuous_at_left_of_closure_image_mem_nhds_within
- \+ *lemma* strict_mono_incr_on.continuous_at_left_of_exists_between
- \+ *lemma* strict_mono_incr_on.continuous_at_left_of_image_mem_nhds_within
- \+ *lemma* strict_mono_incr_on.continuous_at_left_of_surj_on
- \+ *lemma* strict_mono_incr_on.continuous_at_of_closure_image_mem_nhds
- \+ *lemma* strict_mono_incr_on.continuous_at_of_exists_between
- \+ *lemma* strict_mono_incr_on.continuous_at_of_image_mem_nhds
- \+ *lemma* strict_mono_incr_on.continuous_at_right_of_closure_image_mem_nhds_within
- \+ *lemma* strict_mono_incr_on.continuous_at_right_of_exists_between
- \+ *lemma* strict_mono_incr_on.continuous_at_right_of_image_mem_nhds_within
- \+ *lemma* strict_mono_incr_on.continuous_at_right_of_surj_on



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
- \+ *lemma* CompHaus.coe_to_Top
- \+/\- *def* CompHaus_to_Top

Added src/topology/category/Profinite.lean
- \+ *lemma* Profinite.coe_to_Top
- \+ *def* Profinite_to_CompHaus
- \+ *lemma* Profinite_to_CompHaus_to_Top
- \+ *def* Profinite_to_Top



## [2020-12-03 19:30:20](https://github.com/leanprover-community/mathlib/commit/6f38a50)
feat(field_theory/minimal_polynomial): add algebra_map_inj ([#5062](https://github.com/leanprover-community/mathlib/pull/5062))
I have added `algebra_map_inj` that computes the minimal polynomial of an element of the base ring. It generalizes `algebra_map` that assumes the base ring to be a field. I left `algebra_map` since I think it is reasonable to have a lemma that works without proving explicitly that the algebra map is injective.
#### Estimated changes
Modified src/field_theory/minimal_polynomial.lean
- \- *lemma* minimal_polynomial.algebra_map'
- \+ *lemma* minimal_polynomial.degree_le_of_monic
- \+ *lemma* minimal_polynomial.eq_X_sub_C
- \+ *lemma* minimal_polynomial.eq_X_sub_C_of_algebra_map_inj
- \+/\- *lemma* minimal_polynomial.gcd_domain_eq_field_fractions



## [2020-12-03 16:31:34](https://github.com/leanprover-community/mathlib/commit/986cabf)
fix(linear_algebra/multilinear): Fix incorrect type constraints on `dom_dom_congr` ([#5203](https://github.com/leanprover-community/mathlib/pull/5203))
In the last PR, I accidentally put this in a section with `[comm_semiring R]`, but this only actually requires `[semiring R]`
#### Estimated changes
Modified src/linear_algebra/multilinear.lean




## [2020-12-03 16:31:32](https://github.com/leanprover-community/mathlib/commit/5269717)
chore(linear_algebra/determinant): Move some lemmas about swaps to better files ([#5201](https://github.com/leanprover-community/mathlib/pull/5201))
These lemmas are not specific to determinants, and I need them in another file imported by `determinant`.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.apply_swap_eq_self
- \+/\- *lemma* equiv.comp_swap_eq_update
- \+/\- *lemma* equiv.swap_apply_self

Modified src/group_theory/perm/sign.lean
- \+ *def* equiv.perm.mod_swap

Modified src/linear_algebra/determinant.lean
- \- *def* matrix.mod_swap



## [2020-12-03 16:31:30](https://github.com/leanprover-community/mathlib/commit/8ff9c0e)
feat(group_theory/order_of_element): add is_cyclic_of_prime_card ([#5172](https://github.com/leanprover-community/mathlib/pull/5172))
Add `is_cyclic_of_prime_card`, which says if a group has prime order, then it is cyclic. I also added `eq_top_of_card_eq` which says a subgroup is `top` when it has the same size as the group, not sure where that should be in the file.
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* is_cyclic_of_prime_card

Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.eq_top_of_card_eq



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
- \+/\- *lemma* cardinal_mk_alg_hom
- \+/\- *lemma* linear_independent_to_linear_map



## [2020-12-03 14:04:33](https://github.com/leanprover-community/mathlib/commit/e7c2bba)
feat(ring_theory/witt_vector/frobenius): the frobenius endomorphism of witt vectors ([#4838](https://github.com/leanprover-community/mathlib/pull/4838))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Added src/ring_theory/witt_vector/frobenius.lean
- \+ *lemma* witt_vector.bind₁_frobenius_poly_rat_witt_polynomial
- \+ *lemma* witt_vector.bind₁_frobenius_poly_witt_polynomial
- \+ *lemma* witt_vector.coeff_frobenius
- \+ *lemma* witt_vector.coeff_frobenius_char_p
- \+ *lemma* witt_vector.coeff_frobenius_fun
- \+ *def* witt_vector.frobenius
- \+ *lemma* witt_vector.frobenius_eq_map_frobenius
- \+ *def* witt_vector.frobenius_fun
- \+ *lemma* witt_vector.frobenius_fun_is_poly
- \+ *lemma* witt_vector.frobenius_is_poly
- \+ *def* witt_vector.frobenius_poly
- \+ *lemma* witt_vector.frobenius_poly_aux_eq
- \+ *def* witt_vector.frobenius_poly_rat
- \+ *lemma* witt_vector.frobenius_poly_zmod
- \+ *lemma* witt_vector.frobenius_zmodp
- \+ *lemma* witt_vector.ghost_component_frobenius
- \+ *lemma* witt_vector.ghost_component_frobenius_fun
- \+ *lemma* witt_vector.map_frobenius_poly.key₁
- \+ *lemma* witt_vector.map_frobenius_poly.key₂
- \+ *lemma* witt_vector.map_frobenius_poly



## [2020-12-03 12:03:20](https://github.com/leanprover-community/mathlib/commit/f1531ea)
feat(ring_theory/witt_vector): witt_sub, a demonstration of is_poly techniques ([#5165](https://github.com/leanprover-community/mathlib/pull/5165))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/ring_theory/witt_vector/is_poly.lean
- \+ *lemma* witt_vector.sub_coeff
- \+ *lemma* witt_vector.sub_eq



## [2020-12-03 12:03:18](https://github.com/leanprover-community/mathlib/commit/f6273d4)
feat(group_theory/group_action/sub_mul_action): Add an object for bundled sets closed under a mul action ([#4996](https://github.com/leanprover-community/mathlib/pull/4996))
This adds `sub_mul_action` as a base class for `submodule`, and copies across the relevant lemmas.
This also weakens the type class requires for `A →[R] B`, to allow it to be used when only `has_scalar` is available.
#### Estimated changes
Modified src/algebra/group_action_hom.lean
- \+/\- *def* mul_action_hom.comp
- \+/\- *lemma* mul_action_hom.comp_apply
- \+/\- *lemma* mul_action_hom.comp_id
- \+/\- *theorem* mul_action_hom.ext
- \+/\- *theorem* mul_action_hom.ext_iff
- \+/\- *lemma* mul_action_hom.id_apply
- \+/\- *lemma* mul_action_hom.id_comp
- \+/\- *lemma* mul_action_hom.map_smul

Modified src/algebra/module/submodule.lean
- \+/\- *lemma* submodule.neg_mem
- \+ *theorem* submodule.to_sub_mul_action_eq
- \+ *theorem* submodule.to_sub_mul_action_injective

Added src/group_theory/group_action/sub_mul_action.lean
- \+ *lemma* sub_mul_action.coe_eq_coe
- \+ *theorem* sub_mul_action.coe_injective
- \+ *lemma* sub_mul_action.coe_mem
- \+ *lemma* sub_mul_action.coe_mk
- \+ *lemma* sub_mul_action.coe_neg
- \+ *theorem* sub_mul_action.coe_set_eq
- \+ *lemma* sub_mul_action.coe_smul
- \+ *theorem* sub_mul_action.coe_sort_coe
- \+ *theorem* sub_mul_action.ext'_iff
- \+ *theorem* sub_mul_action.ext
- \+ *theorem* sub_mul_action.mem_coe
- \+ *lemma* sub_mul_action.neg_mem
- \+ *lemma* sub_mul_action.neg_mem_iff
- \+ *lemma* sub_mul_action.smul_mem
- \+ *lemma* sub_mul_action.smul_mem_iff'
- \+ *theorem* sub_mul_action.smul_mem_iff
- \+ *theorem* sub_mul_action.subtype_apply
- \+ *lemma* sub_mul_action.subtype_eq_val



## [2020-12-03 10:55:59](https://github.com/leanprover-community/mathlib/commit/98a20c2)
feat(combinatorics/simple_graph/matching): introduce matchings and perfect matchings of graphs ([#5156](https://github.com/leanprover-community/mathlib/pull/5156))
Introduce definitions of matchings and perfect matchings of graphs. This is with the goal of eventually proving Hall's Marriage Theorem and Tutte's Theorem.
#### Estimated changes
Added src/combinatorics/simple_graph/matching.lean
- \+ *def* simple_graph.matching.is_perfect
- \+ *lemma* simple_graph.matching.is_perfect_iff
- \+ *def* simple_graph.matching.support
- \+ *def* simple_graph.matching



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
- \- *lemma* coe_homeomorph_of_strict_mono_surjective
- \- *lemma* continuous_at_of_strict_mono_surjective
- \- *lemma* continuous_inv_of_strict_mono_equiv
- \- *lemma* continuous_left_of_strict_mono_surjective
- \- *lemma* continuous_of_strict_mono_surjective
- \- *lemma* continuous_right_of_strict_mono_surjective
- \+ *lemma* order_iso.coe_to_homeomorph
- \+ *lemma* order_iso.coe_to_homeomorph_symm
- \+ *def* order_iso.to_homeomorph



## [2020-12-02 21:22:19](https://github.com/leanprover-community/mathlib/commit/3f61e54)
feat(category_theory/monad): mark monad lemmas as reassoc ([#5190](https://github.com/leanprover-community/mathlib/pull/5190))
#### Estimated changes
Modified src/category_theory/monad/basic.lean




## [2020-12-02 21:22:16](https://github.com/leanprover-community/mathlib/commit/a84d7a7)
feat(category_theory/adjunction): adjunction to equivalence ([#5189](https://github.com/leanprover-community/mathlib/pull/5189))
Raise an adjunction to an equivalence
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean
- \+ *def* category_theory.adjunction.is_right_adjoint_to_is_equivalence
- \+ *def* category_theory.adjunction.to_equivalence



## [2020-12-02 21:22:13](https://github.com/leanprover-community/mathlib/commit/ed6eab0)
feat(category_theory/adjunction): simp adjunction defs ([#5188](https://github.com/leanprover-community/mathlib/pull/5188))
Mark adjunction defs as `simps` and use the new lemmas to simplify some proofs
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean
- \- *lemma* category_theory.adjunction.equiv_homset_left_of_nat_iso_apply
- \- *lemma* category_theory.adjunction.equiv_homset_left_of_nat_iso_symm_apply
- \- *lemma* category_theory.adjunction.equiv_homset_right_of_nat_iso_apply
- \- *lemma* category_theory.adjunction.equiv_homset_right_of_nat_iso_symm_apply

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
- \+ *lemma* polynomial.degree_mul_X
- \+ *lemma* polynomial.degree_mul_X_pow
- \+ *lemma* polynomial.degree_mul_monic
- \+ *lemma* polynomial.leading_coeff_C_mul_X_pow
- \+/\- *lemma* polynomial.leading_coeff_X_pow
- \- *lemma* polynomial.leading_coeff_monomial'
- \+/\- *lemma* polynomial.leading_coeff_monomial
- \+ *theorem* polynomial.leading_coeff_mul_X
- \+/\- *theorem* polynomial.leading_coeff_mul_X_pow
- \+ *theorem* polynomial.leading_coeff_mul_monic
- \+ *lemma* polynomial.monic_X_pow
- \+ *lemma* polynomial.nat_degree_C_mul_X
- \- *lemma* polynomial.nat_degree_C_mul_X_pow_of_nonzero

Modified src/data/polynomial/div.lean




## [2020-12-02 21:22:07](https://github.com/leanprover-community/mathlib/commit/64fd9f8)
feat(order/rel_iso): preimages of intervals under an `order_iso` ([#5183](https://github.com/leanprover-community/mathlib/pull/5183))
#### Estimated changes
Modified src/order/rel_iso.lean
- \+ *lemma* order_iso.preimage_Icc
- \+ *lemma* order_iso.preimage_Ici
- \+ *lemma* order_iso.preimage_Ico
- \+ *lemma* order_iso.preimage_Iic
- \+ *lemma* order_iso.preimage_Iio
- \+ *lemma* order_iso.preimage_Ioc
- \+ *lemma* order_iso.preimage_Ioi
- \+ *lemma* order_iso.preimage_Ioo



## [2020-12-02 21:22:05](https://github.com/leanprover-community/mathlib/commit/725fb8b)
feat(algebra/lie/basic): define `map` and `comap` for Lie ideals, submodules ([#5181](https://github.com/leanprover-community/mathlib/pull/5181))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *def* lie_ideal.comap
- \+ *lemma* lie_ideal.gc_map_comap
- \+ *def* lie_ideal.map
- \+ *lemma* lie_ideal.map_le_iff_le_comap
- \+ *def* lie_submodule.comap
- \+ *lemma* lie_submodule.gc_map_comap
- \+ *def* lie_submodule.lie_span
- \+ *lemma* lie_submodule.lie_span_le
- \+ *def* lie_submodule.map
- \+ *lemma* lie_submodule.map_le_iff_le_comap
- \+ *lemma* lie_submodule.mem_lie_span
- \+ *lemma* lie_submodule.subset_lie_span



## [2020-12-02 21:22:03](https://github.com/leanprover-community/mathlib/commit/5e93545)
feat(linear_algebra/multilinear): Generalize dom_dom_congr for equivalences between types ([#5180](https://github.com/leanprover-community/mathlib/pull/5180))
This also bundles the operation into an equivalence.
#### Estimated changes
Modified src/linear_algebra/multilinear.lean
- \+/\- *def* multilinear_map.dom_dom_congr
- \+ *def* multilinear_map.dom_dom_congr_equiv



## [2020-12-02 21:22:01](https://github.com/leanprover-community/mathlib/commit/8da5f23)
feat(data/set/function): Extend `update_comp` lemmas to work on dependent functions ([#5178](https://github.com/leanprover-community/mathlib/pull/5178))
Also extends them to `Sort`
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* function.update_comp_eq_of_injective'
- \+/\- *lemma* function.update_comp_eq_of_injective
- \+ *lemma* function.update_comp_eq_of_not_mem_range'
- \+/\- *lemma* function.update_comp_eq_of_not_mem_range



## [2020-12-02 21:21:58](https://github.com/leanprover-community/mathlib/commit/2189c7a)
feat(data/option/basic): map_map functor-like lemmas ([#5030](https://github.com/leanprover-community/mathlib/pull/5030))
New lemmas:
`map_eq_map`
`map_map`
`comp_map`
`map_comp_map`
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* option.comp_map
- \+ *lemma* option.map_comp_map
- \+ *lemma* option.map_eq_map
- \+/\- *theorem* option.map_eq_some
- \+ *lemma* option.map_map
- \+/\- *theorem* option.map_none
- \+/\- *theorem* option.map_some

Modified src/data/seq/seq.lean




## [2020-12-02 19:13:28](https://github.com/leanprover-community/mathlib/commit/0bb8809)
feat(category_theory/limits): left adjoint if preserves colimits ([#4942](https://github.com/leanprover-community/mathlib/pull/4942))
A slight generalisation of a construction from before. Maybe this is the dual version you were talking about @jcommelin - if so my mistake! I think the advantage of doing it this way is that you definitionally get the old version but also the new version too.
#### Estimated changes
Modified src/category_theory/equivalence.lean


Modified src/category_theory/limits/presheaf.lean
- \+/\- *def* category_theory.is_left_adjoint_of_preserves_colimits
- \+ *def* category_theory.is_left_adjoint_of_preserves_colimits_aux



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
- \+/\- *def* matrix.det_row_multilinear

Modified src/linear_algebra/exterior_algebra.lean
- \+ *lemma* exterior_algebra.ι_add_mul_swap
- \+ *lemma* exterior_algebra.ι_mul_prod_list
- \+ *def* exterior_algebra.ι_multi
- \+ *lemma* exterior_algebra.ι_multi_apply

Modified src/linear_algebra/matrix.lean
- \+/\- *def* is_basis.det
- \+ *lemma* is_basis.to_matrix_transpose_apply
- \+ *lemma* linear_map.to_matrix_transpose_apply'
- \+ *lemma* linear_map.to_matrix_transpose_apply



## [2020-12-02 07:25:31](https://github.com/leanprover-community/mathlib/commit/61f6364)
feat(number_theory/arithmetic_function): Möbius inversion for `add_comm_group`s, `comm_group`s ([#5115](https://github.com/leanprover-community/mathlib/pull/5115))
Adds scalar multiplication for `arithmetic_function`s
Generalizes Möbius inversion to work with `(add_)comm_group`s
#### Estimated changes
Modified src/number_theory/arithmetic_function.lean
- \+ *theorem* nat.arithmetic_function.coe_zeta_smul_apply
- \+/\- *lemma* nat.arithmetic_function.mul_apply
- \+ *lemma* nat.arithmetic_function.mul_smul'
- \+ *lemma* nat.arithmetic_function.one_smul'
- \+ *theorem* nat.arithmetic_function.prod_eq_iff_prod_pow_moebius_eq
- \+ *lemma* nat.arithmetic_function.smul_apply
- \- *theorem* nat.arithmetic_function.sum_eq_iff_sum_moebius_eq
- \+ *theorem* nat.arithmetic_function.sum_eq_iff_sum_mul_moebius_eq
- \+ *theorem* nat.arithmetic_function.sum_eq_iff_sum_smul_moebius_eq



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
- \+ *theorem* nat.not_exists_sq
- \+ *theorem* nat.sqrt_mul_sqrt_lt_succ
- \+ *theorem* nat.succ_le_succ_sqrt



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
- \+ *lemma* sub_left_injective
- \+ *lemma* sub_right_injective

Modified src/algebra/group/defs.lean


Modified src/data/fin.lean


Modified src/data/list/basic.lean
- \+ *theorem* list.append_left_injective
- \+ *theorem* list.append_right_injective



## [2020-12-01 23:23:52](https://github.com/leanprover-community/mathlib/commit/c2b7d23)
chore(category_theory/limits): separate regular and normal monos ([#5149](https://github.com/leanprover-community/mathlib/pull/5149))
This separates the file `regular_mono` into `regular_mono` and `normal_mono`: mostly this simplifies the import graph, but also this has the advantage that to use things about kernel pairs it's no longer necessary to import things about zero objects (I kept changing equalizers and using the changes in a file about monads which imported kernel pairs, and it was very slow because of zero objects)
#### Estimated changes
Modified src/category_theory/abelian/basic.lean


Modified src/category_theory/abelian/non_preadditive.lean


Added src/category_theory/limits/shapes/normal_mono.lean
- \+ *def* category_theory.equivalence_reflects_normal_epi
- \+ *def* category_theory.equivalence_reflects_normal_mono
- \+ *def* category_theory.normal_epi.desc'
- \+ *def* category_theory.normal_mono.lift'
- \+ *def* category_theory.normal_of_is_pullback_fst_of_normal
- \+ *def* category_theory.normal_of_is_pullback_snd_of_normal
- \+ *def* category_theory.normal_of_is_pushout_fst_of_normal
- \+ *def* category_theory.normal_of_is_pushout_snd_of_normal

Modified src/category_theory/limits/shapes/regular_mono.lean
- \- *def* category_theory.equivalence_reflects_normal_epi
- \- *def* category_theory.equivalence_reflects_normal_mono
- \- *def* category_theory.normal_epi.desc'
- \- *def* category_theory.normal_mono.lift'
- \- *def* category_theory.normal_of_is_pullback_fst_of_normal
- \- *def* category_theory.normal_of_is_pullback_snd_of_normal
- \- *def* category_theory.normal_of_is_pushout_fst_of_normal
- \- *def* category_theory.normal_of_is_pushout_snd_of_normal



## [2020-12-01 20:05:02](https://github.com/leanprover-community/mathlib/commit/6c456e3)
feat(linear_algebra/multilinear): Add dom_dom_congr ([#5136](https://github.com/leanprover-community/mathlib/pull/5136))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *lemma* dite_comp_equiv_update
- \+ *lemma* function.update_apply_equiv_apply
- \+ *lemma* function.update_comp_equiv

Modified src/linear_algebra/multilinear.lean
- \+ *def* multilinear_map.dom_dom_congr



## [2020-12-01 20:05:00](https://github.com/leanprover-community/mathlib/commit/41e0903)
feat(category_theory/limits/preserves): preserving equalizers ([#5044](https://github.com/leanprover-community/mathlib/pull/5044))
Constructions and lemmas about preserving equalizers
#### Estimated changes
Added src/category_theory/limits/preserves/shapes/equalizers.lean
- \+ *def* category_theory.limits.is_limit_fork_map_of_is_limit
- \+ *def* category_theory.limits.is_limit_map_cone_fork_equiv
- \+ *def* category_theory.limits.is_limit_of_has_equalizer_of_preserves_limit
- \+ *def* category_theory.limits.is_limit_of_is_limit_fork_map
- \+ *def* category_theory.limits.preserves_equalizer.iso
- \+ *lemma* category_theory.limits.preserves_equalizer.iso_hom
- \+ *def* category_theory.limits.preserves_equalizer.of_iso_comparison

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


Added src/ring_theory/perfection.lean
- \+ *lemma* mod_p.mul_ne_zero_of_pow_p_ne_zero
- \+ *lemma* mod_p.pre_val_add
- \+ *lemma* mod_p.pre_val_eq_zero
- \+ *lemma* mod_p.pre_val_mk
- \+ *lemma* mod_p.pre_val_mul
- \+ *lemma* mod_p.pre_val_zero
- \+ *lemma* mod_p.v_p_lt_pre_val
- \+ *lemma* mod_p.v_p_lt_val
- \+ *def* mod_p
- \+ *def* monoid.perfection
- \+ *lemma* pre_tilt.coeff_nat_find_add_ne_zero
- \+ *lemma* pre_tilt.map_eq_zero
- \+ *lemma* pre_tilt.val_aux_add
- \+ *lemma* pre_tilt.val_aux_eq
- \+ *lemma* pre_tilt.val_aux_mul
- \+ *lemma* pre_tilt.val_aux_one
- \+ *lemma* pre_tilt.val_aux_zero
- \+ *def* pre_tilt
- \+ *def* ring.perfection.coeff
- \+ *lemma* ring.perfection.coeff_add_ne_zero
- \+ *lemma* ring.perfection.coeff_frobenius
- \+ *lemma* ring.perfection.coeff_ne_zero_of_le
- \+ *lemma* ring.perfection.coeff_pow_p
- \+ *lemma* ring.perfection.coeff_pth_root
- \+ *lemma* ring.perfection.ext
- \+ *lemma* ring.perfection.frobenius_pth_root
- \+ *def* ring.perfection.pth_root
- \+ *lemma* ring.perfection.pth_root_frobenius
- \+ *def* ring.perfection
- \+ *def* semiring.perfection
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
- \- *lemma* equiv.perm.apply_inv_self
- \- *lemma* equiv.perm.coe_mul
- \- *lemma* equiv.perm.coe_one
- \- *lemma* equiv.perm.inv_apply_self
- \- *lemma* equiv.perm.inv_def
- \- *theorem* equiv.perm.mul_apply
- \- *lemma* equiv.perm.mul_def
- \- *theorem* equiv.perm.one_apply
- \- *lemma* equiv.perm.one_def
- \- *lemma* equiv.swap_inv
- \- *lemma* equiv.swap_mul_self

Modified src/data/equiv/mul_add.lean


Added src/group_theory/perm/basic.lean
- \+ *lemma* equiv.mul_swap_eq_swap_mul
- \+ *lemma* equiv.perm.apply_inv_self
- \+ *lemma* equiv.perm.coe_mul
- \+ *lemma* equiv.perm.coe_one
- \+ *lemma* equiv.perm.eq_inv_iff_eq
- \+ *lemma* equiv.perm.inv_apply_self
- \+ *lemma* equiv.perm.inv_def
- \+ *lemma* equiv.perm.inv_eq_iff_eq
- \+ *theorem* equiv.perm.mul_apply
- \+ *lemma* equiv.perm.mul_def
- \+ *theorem* equiv.perm.one_apply
- \+ *lemma* equiv.perm.one_def
- \+ *lemma* equiv.swap_inv
- \+ *lemma* equiv.swap_mul_eq_iff
- \+ *lemma* equiv.swap_mul_eq_mul_swap
- \+ *lemma* equiv.swap_mul_involutive
- \+ *lemma* equiv.swap_mul_self
- \+ *lemma* equiv.swap_mul_self_mul
- \+ *lemma* equiv.swap_mul_swap_mul_swap

Modified src/group_theory/perm/sign.lean
- \- *lemma* equiv.perm.eq_inv_iff_eq
- \- *lemma* equiv.perm.inv_eq_iff_eq
- \- *lemma* equiv.perm.mul_swap_eq_swap_mul
- \- *lemma* equiv.perm.swap_mul_eq_iff
- \- *lemma* equiv.perm.swap_mul_eq_mul_swap
- \- *lemma* equiv.perm.swap_mul_involutive
- \- *lemma* equiv.perm.swap_mul_self_mul
- \- *lemma* equiv.perm.swap_mul_swap_mul_swap

Modified src/logic/embedding.lean




## [2020-12-01 13:25:37](https://github.com/leanprover-community/mathlib/commit/7188eae)
feat(linear_algebra): Add alternating multilinear maps ([#5102](https://github.com/leanprover-community/mathlib/pull/5102))
#### Estimated changes
Added src/linear_algebra/alternating.lean
- \+ *lemma* alternating_map.add_apply
- \+ *theorem* alternating_map.coe_inj
- \+ *lemma* alternating_map.coe_mk
- \+ *lemma* alternating_map.coe_multilinear_map
- \+ *lemma* alternating_map.coe_multilinear_map_mk
- \+ *theorem* alternating_map.congr_arg
- \+ *theorem* alternating_map.congr_fun
- \+ *theorem* alternating_map.ext
- \+ *theorem* alternating_map.ext_iff
- \+ *lemma* alternating_map.map_add
- \+ *lemma* alternating_map.map_add_swap
- \+ *lemma* alternating_map.map_congr_perm
- \+ *lemma* alternating_map.map_eq_zero_of_eq
- \+ *lemma* alternating_map.map_perm
- \+ *lemma* alternating_map.map_smul
- \+ *lemma* alternating_map.map_sub
- \+ *lemma* alternating_map.map_swap
- \+ *lemma* alternating_map.map_swap_add
- \+ *lemma* alternating_map.map_update_self
- \+ *lemma* alternating_map.map_update_update
- \+ *lemma* alternating_map.neg_apply
- \+ *lemma* alternating_map.smul_apply
- \+ *lemma* alternating_map.to_fun_eq_coe
- \+ *lemma* alternating_map.to_multilinear_map_eq_coe
- \+ *lemma* alternating_map.zero_apply



## [2020-12-01 10:59:06](https://github.com/leanprover-community/mathlib/commit/ca3351f)
feat(rat/{basic,floor}) add floor lemmas ([#5148](https://github.com/leanprover-community/mathlib/pull/5148))
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *lemma* rat.exists_eq_mul_div_num_and_eq_mul_div_denom

Modified src/data/rat/floor.lean
- \+ *lemma* int.mod_nat_eq_sub_mul_floor_rat_div
- \+ *lemma* nat.coprime_sub_mul_floor_rat_div_of_coprime
- \+ *lemma* rat.floor_int_div_nat_eq_div
- \+ *lemma* rat.fract_inv_num_lt_num_of_pos
- \+ *lemma* rat.num_lt_succ_floor_mul_denom



## [2020-12-01 08:49:42](https://github.com/leanprover-community/mathlib/commit/2b074be)
feat(algebra/lie/basic): Define lattice structure for `lie_submodule`s ([#5146](https://github.com/leanprover-community/mathlib/pull/5146))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* lie_submodule.Inf_coe
- \+ *lemma* lie_submodule.Inf_coe_to_submodule
- \+ *lemma* lie_submodule.Inf_glb
- \+ *lemma* lie_submodule.add_eq_sup
- \+ *lemma* lie_submodule.bot_coe
- \+ *lemma* lie_submodule.coe_injective
- \+ *lemma* lie_submodule.coe_to_submodule
- \+ *lemma* lie_submodule.ext
- \+ *lemma* lie_submodule.le_def
- \+ *lemma* lie_submodule.mem_bot
- \+ *lemma* lie_submodule.mem_carrier
- \+ *lemma* lie_submodule.mem_top
- \+ *lemma* lie_submodule.top_coe

Modified src/algebra/module/submodule.lean
- \+ *lemma* submodule.mem_carrier



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


