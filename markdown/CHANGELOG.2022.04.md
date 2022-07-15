## [2022-04-30 20:50:46](https://github.com/leanprover-community/mathlib/commit/49342e3)
feat(set_theory/cardinal/basic): Add `simp` lemmas on `cardinal.sum` ([#13838](https://github.com/leanprover-community/mathlib/pull/13838))
#### Estimated changes
Modified src/set_theory/cardinal/basic.lean
- \+ *theorem* cardinal.lift_sum
- \+ *theorem* cardinal.sum_add_distrib'



## [2022-04-30 16:49:17](https://github.com/leanprover-community/mathlib/commit/0420dd8)
chore(measure_theory/measurable_space_def): make measurable_space arguments implicit ([#13832](https://github.com/leanprover-community/mathlib/pull/13832))
#### Estimated changes
Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable_fst
- \+/\- *lemma* measurable_snd

Modified src/measure_theory/measurable_space_def.lean
- \+/\- *lemma* measurable.comp
- \+/\- *lemma* measurable.le
- \+/\- *lemma* measurable_const
- \+/\- *lemma* measurable_id'
- \+/\- *lemma* measurable_id

Modified src/probability/stopping.lean




## [2022-04-30 11:26:15](https://github.com/leanprover-community/mathlib/commit/26310e7)
feat(algebra/*): a sample of easy useful lemmas ([#13696](https://github.com/leanprover-community/mathlib/pull/13696))
Lemmas needed for [#13690](https://github.com/leanprover-community/mathlib/pull/13690)
#### Estimated changes
Modified src/algebra/big_operators/intervals.lean
- \+ *lemma* finset.prod_Ioc_consecutive
- \+ *lemma* finset.prod_Ioc_succ_top

Modified src/algebra/geom_sum.lean
- \+ *lemma* geom_sum_Ico_le_of_lt_one

Modified src/algebra/group_power/basic.lean
- \+ *lemma* add_sq'
- \+ *lemma* sub_sq'

Modified src/algebra/order/floor.lean
- \+ *lemma* nat.one_le_floor_iff

Modified src/algebra/order/group.lean
- \+ *lemma* neg_abs_le_neg

Modified src/data/finset/locally_finite.lean
- \+ *lemma* finset.Ioc_union_Ioc_eq_Ioc

Modified src/data/nat/interval.lean
- \+ *lemma* nat.Ioc_succ_singleton



## [2022-04-30 10:51:30](https://github.com/leanprover-community/mathlib/commit/1c3ab8c)
feat(probability/notations): fix some notations, add a new one ([#13828](https://github.com/leanprover-community/mathlib/pull/13828))
#### Estimated changes
Modified src/probability/notation.lean




## [2022-04-30 05:24:54](https://github.com/leanprover-community/mathlib/commit/9141960)
feat(model_theory/syntax): Free variables ([#13529](https://github.com/leanprover-community/mathlib/pull/13529))
Defines `term.var_finset` and `bounded_formula.free_var_finset` to consist of all (free) variables used in a term or formula.
Defines `term.restrict_var` and `bounded_formula.restrict_free_var` to restrict formulas to sets of their variables.
#### Estimated changes
Modified src/model_theory/syntax.lean
- \+ *def* first_order.language.bounded_formula.free_var_finset
- \+ *def* first_order.language.bounded_formula.restrict_free_var
- \+ *def* first_order.language.term.restrict_var
- \+ *def* first_order.language.term.restrict_var_left
- \+ *def* first_order.language.term.var_finset
- \+ *def* first_order.language.term.var_finset_left



## [2022-04-30 02:26:48](https://github.com/leanprover-community/mathlib/commit/bb45687)
feat(model_theory/syntax, semantics): Substitution of variables in terms and formulas ([#13632](https://github.com/leanprover-community/mathlib/pull/13632))
Defines `first_order.language.term.subst` and `first_order.language.bounded_formula.subst`, which substitute free variables in terms and formulas with terms.
#### Estimated changes
Modified src/model_theory/semantics.lean
- \+/\- *lemma* first_order.language.bounded_formula.realize_all_lift_at_one_self
- \+ *lemma* first_order.language.bounded_formula.realize_subst
- \+ *lemma* first_order.language.bounded_formula.realize_subst_aux
- \+ *lemma* first_order.language.term.realize_subst

Modified src/model_theory/syntax.lean
- \+ *def* first_order.language.bounded_formula.subst
- \+ *def* first_order.language.term.subst



## [2022-04-29 22:22:48](https://github.com/leanprover-community/mathlib/commit/a34ee7b)
chore(set_theory/game/basic): golf proof ([#13810](https://github.com/leanprover-community/mathlib/pull/13810))
#### Estimated changes
Modified src/set_theory/game/basic.lean




## [2022-04-29 22:22:48](https://github.com/leanprover-community/mathlib/commit/24bc2e1)
feat(set_theory/surreal/basic): add `pgame.numeric.left_lt_right` ([#13809](https://github.com/leanprover-community/mathlib/pull/13809))
Also compress some trivial proofs into a single line
#### Estimated changes
Modified src/set_theory/surreal/basic.lean
- \+ *lemma* pgame.numeric.left_lt_right



## [2022-04-29 22:22:47](https://github.com/leanprover-community/mathlib/commit/a70166a)
feat(ring_theory): factorize a non-unit into irreducible factors without multiplying a unit ([#13682](https://github.com/leanprover-community/mathlib/pull/13682))
Used in https://proofassistants.stackexchange.com/a/1312/93. Also adds simp lemma `multiset.prod_erase` used in the main proof and the auto-generated additive version, which is immediately analogous to [list.prod_erase](https://leanprover-community.github.io/mathlib_docs/data/list/big_operators.html#list.prod_erase). Also removes some extraneous namespace prefix.
#### Estimated changes
Modified src/algebra/big_operators/multiset.lean
- \+/\- *lemma* multiset.prod_eq_foldr
- \+ *lemma* multiset.prod_erase

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* wf_dvd_monoid.not_unit_iff_exists_factors_eq



## [2022-04-29 20:31:27](https://github.com/leanprover-community/mathlib/commit/059c8eb)
chore(set_theory/game/basic): fix a single space ([#13806](https://github.com/leanprover-community/mathlib/pull/13806))
#### Estimated changes
Modified src/set_theory/game/basic.lean




## [2022-04-29 20:31:26](https://github.com/leanprover-community/mathlib/commit/8910228)
chore(data/polynomial): use dot notation for sub lemmas ([#13799](https://github.com/leanprover-community/mathlib/pull/13799))
To match the additive versions
#### Estimated changes
Modified src/data/polynomial/monic.lean
- \+ *lemma* polynomial.monic.sub_of_left
- \+ *lemma* polynomial.monic.sub_of_right
- \- *lemma* polynomial.monic_sub_of_left
- \- *lemma* polynomial.monic_sub_of_right

Modified src/ring_theory/power_basis.lean




## [2022-04-29 20:31:25](https://github.com/leanprover-community/mathlib/commit/e56b8fe)
feat(model_theory/graph): First-order language and theory of graphs ([#13720](https://github.com/leanprover-community/mathlib/pull/13720))
Defines `first_order.language.graph`, the language of graphs
Defines `first_order.Theory.simple_graph`, the theory of simple graphs
Produces models of the theory of simple graphs from simple graphs and vice versa.
#### Estimated changes
Added src/model_theory/graph.lean
- \+ *lemma* first_order.language.Structure_simple_graph_of_structure
- \+ *theorem* first_order.language.Theory.simple_graph_is_satisfiable
- \+ *lemma* first_order.language.Theory.simple_graph_model_iff
- \+ *def* first_order.language.adj
- \+ *def* first_order.language.simple_graph_of_structure
- \+ *def* simple_graph.Structure
- \+ *lemma* simple_graph.simple_graph_of_structure

Modified src/model_theory/order.lean




## [2022-04-29 20:31:23](https://github.com/leanprover-community/mathlib/commit/1d4ed4a)
chore(topology/algebra/valuation): use forgetful inheritance pattern for valued fields ([#13691](https://github.com/leanprover-community/mathlib/pull/13691))
This allows us to solve a `uniform_space` diamond problem that arises when extending valuations to the completion of a valued field.
More precisely, the main goal of this PR is to make the following work:
```lean
import topology.algebra.valued_field
example  {K Γ₀ : Type*} [field K] [linear_ordered_comm_group_with_zero Γ₀] [valued K Γ₀] :
  uniform_space.completion.uniform_space K = valued.to_uniform_space :=
rfl
```
#### Estimated changes
Modified src/number_theory/function_field.lean
- \+/\- *def* function_field.Fqt_infty
- \- *lemma* function_field.infty_valued_Fqt.completable_top_field
- \- *lemma* function_field.infty_valued_Fqt.separated_space
- \- *lemma* function_field.infty_valued_Fqt.topological_division_ring
- \- *def* function_field.infty_valued_Fqt.topological_space
- \- *lemma* function_field.infty_valued_Fqt.uniform_add_group
- \- *def* function_field.infty_valued_Fqt.uniform_space

Modified src/topology/algebra/uniform_group.lean
- \- *lemma* topological_group.separated_iff_one_closed
- \- *lemma* topological_group.separated_of_one_sep
- \+ *lemma* topological_group.t2_space_iff_one_closed
- \+ *lemma* topological_group.t2_space_of_one_sep

Modified src/topology/algebra/valuation.lean
- \+ *lemma* valuation.subgroups_basis
- \+ *lemma* valued.has_basis_nhds_zero
- \+ *lemma* valued.has_basis_uniformity
- \+ *def* valued.mk'
- \- *lemma* valued.subgroups_basis
- \+ *lemma* valued.to_uniform_space_eq

Modified src/topology/algebra/valued_field.lean
- \+ *lemma* valued.closure_coe_completion_v_lt
- \+/\- *lemma* valued.continuous_extension
- \+/\- *lemma* valued.extension_extends

Modified src/topology/algebra/with_zero_topology.lean
- \+ *lemma* linear_ordered_comm_group_with_zero.singleton_mem_nhds_of_ne_zero

Modified src/topology/dense_embedding.lean
- \+ *lemma* filter.has_basis.has_basis_of_dense_inducing



## [2022-04-29 20:31:22](https://github.com/leanprover-community/mathlib/commit/90bd6f5)
feat(model_theory/encoding): A bound on the number of bounded formulas ([#13616](https://github.com/leanprover-community/mathlib/pull/13616))
Gives an encoding `first_order.language.bounded_formula.encoding` of bounded formulas as lists.
Uses the encoding to bound the number of bounded formulas with `first_order.language.bounded_formula.card_le`.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.drop_sizeof_le

Modified src/model_theory/encoding.lean
- \+ *theorem* first_order.language.bounded_formula.card_le
- \+ *def* first_order.language.bounded_formula.list_decode
- \+ *theorem* first_order.language.bounded_formula.list_decode_encode_list
- \+ *def* first_order.language.bounded_formula.list_encode
- \+ *lemma* first_order.language.bounded_formula.list_encode_sigma_injective
- \+ *def* first_order.language.bounded_formula.sigma_all
- \+ *def* first_order.language.bounded_formula.sigma_imp
- \+ *theorem* first_order.language.term.card_sigma



## [2022-04-29 20:31:21](https://github.com/leanprover-community/mathlib/commit/9ce5e95)
feat(model_theory/syntax, semantics): A theory of infinite structures ([#13580](https://github.com/leanprover-community/mathlib/pull/13580))
Defines `first_order.language.infinite_theory`, a theory of infinite structures
Adjusts the API of the theory of nonempty structures to match
#### Estimated changes
Modified src/model_theory/elementary_maps.lean


Modified src/model_theory/semantics.lean
- \- *lemma* first_order.language.Theory.model_nonempty_iff
- \+ *lemma* first_order.language.bounded_formula.realize_foldr_inf
- \+ *lemma* first_order.language.bounded_formula.realize_foldr_sup
- \+ *lemma* first_order.language.model_infinite_theory_iff
- \+ *lemma* first_order.language.model_nonempty_theory_iff
- \+ *lemma* first_order.language.sentence.realize_card_ge
- \- *lemma* first_order.language.sentence.realize_nonempty

Modified src/model_theory/syntax.lean
- \+ *def* first_order.language.infinite_theory
- \+ *def* first_order.language.nonempty_theory



## [2022-04-29 20:31:20](https://github.com/leanprover-community/mathlib/commit/812518d)
feat(model_theory/semantics, satisfiability): Complete Theories ([#13558](https://github.com/leanprover-community/mathlib/pull/13558))
Defines `first_order.language.Theory.is_complete`, indicating that a theory is complete.
Defines `first_order.language.complete_theory`, the complete theory of a structure.
Shows that the complete theory of a structure is complete.
#### Estimated changes
Modified src/model_theory/satisfiability.lean
- \+ *def* first_order.language.Theory.is_complete
- \+ *lemma* first_order.language.Theory.models_sentence_of_mem
- \+ *lemma* first_order.language.complete_theory.is_complete
- \+ *lemma* first_order.language.complete_theory.is_satisfiable
- \+ *lemma* first_order.language.complete_theory.mem_or_not_mem

Modified src/model_theory/semantics.lean
- \+ *theorem* first_order.language.Theory.model_iff_subset_complete_theory
- \+ *def* first_order.language.complete_theory
- \+ *theorem* first_order.language.realize_iff_of_model_complete_theory
- \+ *lemma* first_order.language.sentence.realize_not



## [2022-04-29 20:31:19](https://github.com/leanprover-community/mathlib/commit/812e17f)
feat(analysis/normed_space/pointwise): Addition of balls ([#13381](https://github.com/leanprover-community/mathlib/pull/13381))
Adding two balls yields another ball.
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *lemma* dist_neg
- \+/\- *lemma* dist_neg_neg
- \+ *lemma* edist_neg
- \+/\- *lemma* edist_neg_neg

Modified src/analysis/normed/group/pointwise.lean
- \+ *lemma* add_ball
- \+ *lemma* add_ball_zero
- \+ *lemma* ball_add
- \+/\- *lemma* ball_add_singleton
- \+ *lemma* ball_add_zero
- \+ *lemma* ball_sub
- \+ *lemma* ball_sub_singleton
- \+ *lemma* ball_sub_zero
- \+/\- *lemma* ball_zero_add_singleton
- \+ *lemma* ball_zero_sub_singleton
- \+/\- *lemma* bounded_iff_exists_norm_le
- \+/\- *lemma* closed_ball_add_singleton
- \+ *lemma* closed_ball_sub_singleton
- \+/\- *lemma* closed_ball_zero_add_singleton
- \+ *lemma* closed_ball_zero_sub_singleton
- \+ *lemma* inf_edist_neg
- \+ *lemma* inf_edist_neg_neg
- \+ *lemma* is_compact.add_closed_ball
- \+ *lemma* is_compact.add_closed_ball_zero
- \+ *lemma* is_compact.closed_ball_add
- \+ *lemma* is_compact.closed_ball_sub
- \+ *lemma* is_compact.closed_ball_zero_add
- \+ *lemma* is_compact.closed_ball_zero_sub
- \- *lemma* is_compact.cthickening_eq_add_closed_ball
- \+ *lemma* is_compact.sub_closed_ball
- \+ *lemma* is_compact.sub_closed_ball_zero
- \+/\- *lemma* metric.bounded.add
- \+/\- *lemma* metric.bounded.exists_pos_norm_le
- \+ *lemma* metric.bounded.neg
- \+ *lemma* metric.bounded.sub
- \+ *lemma* neg_ball
- \+ *lemma* neg_closed_ball
- \+ *lemma* neg_cthickening
- \+ *lemma* neg_thickening
- \+/\- *lemma* singleton_add_ball
- \+/\- *lemma* singleton_add_ball_zero
- \+/\- *lemma* singleton_add_closed_ball
- \+/\- *lemma* singleton_add_closed_ball_zero
- \+ *lemma* singleton_sub_ball
- \+ *lemma* singleton_sub_ball_zero
- \+ *lemma* singleton_sub_closed_ball
- \+ *lemma* singleton_sub_closed_ball_zero
- \+ *lemma* sub_ball
- \+ *lemma* sub_ball_zero
- \+ *lemma* vadd_ball_zero
- \+ *lemma* vadd_closed_ball_zero

Modified src/analysis/normed_space/pointwise.lean
- \+ *lemma* ball_add_ball
- \+ *lemma* ball_add_closed_ball
- \+ *lemma* ball_sub_ball
- \+ *lemma* ball_sub_closed_ball
- \+ *lemma* closed_ball_add_ball
- \+ *lemma* closed_ball_add_closed_ball
- \+ *lemma* closed_ball_sub_ball
- \+ *lemma* closed_ball_sub_closed_ball
- \+ *lemma* cthickening_ball
- \+ *lemma* cthickening_closed_ball
- \+ *lemma* thickening_ball
- \+ *lemma* thickening_closed_ball
- \- *lemma* vadd_ball_zero
- \- *lemma* vadd_closed_ball_zero

Modified src/data/set/pointwise.lean
- \+/\- *lemma* set.inv_singleton

Modified src/measure_theory/function/jacobian.lean




## [2022-04-29 18:38:48](https://github.com/leanprover-community/mathlib/commit/a54db9a)
feat(data/finset/basic): A finset that's a subset of a `directed` union is contained in one element ([#13727](https://github.com/leanprover-community/mathlib/pull/13727))
Proves `directed.exists_mem_subset_of_finset_subset_bUnion`
Renames `finset.exists_mem_subset_of_subset_bUnion_of_directed_on` to `directed_on.exists_mem_subset_of_finset_subset_bUnion`
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* directed.exists_mem_subset_of_finset_subset_bUnion
- \+ *lemma* directed_on.exists_mem_subset_of_finset_subset_bUnion
- \- *lemma* finset.exists_mem_subset_of_subset_bUnion_of_directed_on

Modified src/linear_algebra/linear_independent.lean




## [2022-04-29 17:28:05](https://github.com/leanprover-community/mathlib/commit/8624f6d)
chore(analysis/normed/group/basic): add `nnnorm_sum_le_of_le` ([#13795](https://github.com/leanprover-community/mathlib/pull/13795))
This is to match `norm_sum_le_of_le`.
Also tidies up the coercion syntax a little in `pi.semi_normed_group`.
The definition is syntactically identical, just with fewer unecessary type annotations.
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *lemma* nnnorm_sum_le_of_le



## [2022-04-29 17:28:03](https://github.com/leanprover-community/mathlib/commit/8360f2c)
feat(model_theory/language_map, bundled): Reducts of structures ([#13745](https://github.com/leanprover-community/mathlib/pull/13745))
Defines `first_order.language.Lhom.reduct` which pulls a structure back along a language map.
Defines `first_order.language.Theory.Model.reduct` which sends a model of `(φ.on_Theory T)` to its reduct as a model of `T`.
#### Estimated changes
Modified src/model_theory/bundled.lean
- \+ *def* first_order.language.Theory.Model.reduct

Modified src/model_theory/language_map.lean
- \+ *def* first_order.language.Lhom.reduct



## [2022-04-29 15:59:00](https://github.com/leanprover-community/mathlib/commit/50c3028)
chore(analysis/normed_space/operator_norm): move `continuous_linear_map.op_norm_lsmul` into the correct section ([#13790](https://github.com/leanprover-community/mathlib/pull/13790))
This was in the "seminorm" section but was about regular norms.
Also relaxes some other typeclasses in the file. This file is still a mess with regards to assuming `nondiscrete_normed_field` when `normed_field` is enough, but that would require substantially more movement within the file.
This cleans up after [#13165](https://github.com/leanprover-community/mathlib/pull/13165) and [#13538](https://github.com/leanprover-community/mathlib/pull/13538)
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* continuous_linear_map.op_norm_lsmul
- \+ *lemma* continuous_linear_map.op_norm_lsmul_apply_le
- \+/\- *lemma* continuous_linear_map.to_span_singleton_smul'



## [2022-04-29 15:58:59](https://github.com/leanprover-community/mathlib/commit/64b3576)
feat(ring_theory/valuation/extend_to_localization): Extending valuations to localizations. ([#13610](https://github.com/leanprover-community/mathlib/pull/13610))
#### Estimated changes
Modified src/ring_theory/valuation/basic.lean
- \+ *lemma* valuation.comap_apply

Added src/ring_theory/valuation/extend_to_localization.lean
- \+ *def* valuation.extend_to_localization
- \+ *lemma* valuation.extend_to_localization_apply_map_apply



## [2022-04-29 14:39:20](https://github.com/leanprover-community/mathlib/commit/fe2917a)
feat(number_theory/primes_congruent_one): attempt to golf ([#13787](https://github.com/leanprover-community/mathlib/pull/13787))
As suggested in the reviews of [#12595](https://github.com/leanprover-community/mathlib/pull/12595) we try to golf the proof using the bound proved there.
This doesn't end up being as much of a golf as hoped due to annoying edge cases, but seems conceptually simpler.
#### Estimated changes
Modified archive/imo/imo2008_q3.lean


Modified src/number_theory/primes_congruent_one.lean
- \+/\- *lemma* nat.exists_prime_ge_modeq_one
- \+/\- *lemma* nat.frequently_at_top_modeq_one
- \+/\- *lemma* nat.infinite_set_of_prime_modeq_one



## [2022-04-29 14:39:18](https://github.com/leanprover-community/mathlib/commit/a3beb62)
feat(analysis/*): a sample of easy useful lemmas ([#13697](https://github.com/leanprover-community/mathlib/pull/13697))
Lemmas needed for [#13690](https://github.com/leanprover-community/mathlib/pull/13690)
#### Estimated changes
Modified src/analysis/inner_product_space/pi_L2.lean


Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* complex.cpow_int_cast
- \+/\- *lemma* complex.cpow_nat_cast
- \+ *lemma* complex.cpow_two
- \+ *lemma* ennreal.rpow_two
- \+ *lemma* nnreal.rpow_two
- \+ *lemma* real.rpow_two

Modified src/analysis/specific_limits/basic.lean
- \+ *lemma* tendsto_nat_ceil_div_at_top
- \+ *lemma* tendsto_nat_floor_at_top
- \+ *lemma* tendsto_nat_floor_div_at_top

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.one_le_two

Modified src/topology/algebra/group.lean
- \+ *lemma* tendsto_div_nhds_one_iff



## [2022-04-29 14:39:17](https://github.com/leanprover-community/mathlib/commit/7373832)
chore(analysis/convex): move `convex_on_norm`, change API ([#13631](https://github.com/leanprover-community/mathlib/pull/13631))
* Move `convex_on_norm` from `specific_functions` to `topology`, use it to golf the proof of `convex_on_dist`.
* The old `convex_on_norm` is now called `convex_on_univ_norm`. The new `convex_on_norm` is about convexity on any convex set.
* Add `convex_on_univ_dist` and make `s : set E` an implicit argument in `convex_on_dist`.
This way APIs about convexity of norm and distance agree.
#### Estimated changes
Modified src/analysis/convex/specific_functions.lean
- \- *lemma* convex_on_norm

Modified src/analysis/convex/topology.lean
- \+/\- *lemma* convex_on_dist
- \+ *lemma* convex_on_norm
- \+ *lemma* convex_on_univ_dist
- \+ *lemma* convex_on_univ_norm



## [2022-04-29 14:39:15](https://github.com/leanprover-community/mathlib/commit/ce79a27)
feat(analysis/normed_space/pi_Lp): add lemmas about `pi_Lp.equiv` ([#13569](https://github.com/leanprover-community/mathlib/pull/13569))
Most of these are trivial `dsimp` lemmas, but they also let us talk about the norm of constant vectors.
#### Estimated changes
Modified src/analysis/normed_space/pi_Lp.lean
- \+ *lemma* pi_Lp.equiv_add
- \+ *lemma* pi_Lp.equiv_apply
- \+ *lemma* pi_Lp.equiv_neg
- \+ *lemma* pi_Lp.equiv_smul
- \+ *lemma* pi_Lp.equiv_sub
- \+ *lemma* pi_Lp.equiv_symm_add
- \+ *lemma* pi_Lp.equiv_symm_apply
- \+ *lemma* pi_Lp.equiv_symm_neg
- \+ *lemma* pi_Lp.equiv_symm_smul
- \+ *lemma* pi_Lp.equiv_symm_sub
- \+ *lemma* pi_Lp.equiv_symm_zero
- \+ *lemma* pi_Lp.equiv_zero
- \+ *lemma* pi_Lp.nnnorm_equiv_symm_const
- \+ *lemma* pi_Lp.nnnorm_equiv_symm_one
- \+ *lemma* pi_Lp.norm_equiv_symm_const
- \+ *lemma* pi_Lp.norm_equiv_symm_one
- \+ *lemma* pi_Lp.zero_apply



## [2022-04-29 14:39:14](https://github.com/leanprover-community/mathlib/commit/e561264)
feat(algebra/order/monoid_lemmas_zero_lt): add instances ([#13376](https://github.com/leanprover-community/mathlib/pull/13376))
#### Estimated changes
Modified src/algebra/order/monoid_lemmas_zero_lt.lean




## [2022-04-29 12:25:32](https://github.com/leanprover-community/mathlib/commit/58552fe)
feat(set_theory/cardinal/basic): cardinality of a powerset ([#13786](https://github.com/leanprover-community/mathlib/pull/13786))
#### Estimated changes
Modified src/set_theory/cardinal/basic.lean
- \+ *theorem* cardinal.mk_powerset



## [2022-04-29 12:25:31](https://github.com/leanprover-community/mathlib/commit/b2e0a2d)
feat(group_theory/subgroup/basic): `inclusion` lemmas ([#13754](https://github.com/leanprover-community/mathlib/pull/13754))
A few lemmas for `set.inclusion`, `subgroup.inclusion`, `subalgebra.inclusion`.
#### Estimated changes
Modified src/algebra/algebra/subalgebra/basic.lean
- \+ *lemma* subalgebra.inclusion_mk
- \+/\- *lemma* subalgebra.inclusion_right

Modified src/data/set/basic.lean
- \+/\- *lemma* set.coe_inclusion
- \+/\- *def* set.inclusion
- \+/\- *lemma* set.inclusion_inclusion
- \+/\- *lemma* set.inclusion_injective
- \+ *lemma* set.inclusion_mk
- \+/\- *lemma* set.inclusion_right
- \+/\- *lemma* set.inclusion_self
- \+/\- *lemma* set.range_inclusion

Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup_class.inclusion_inclusion
- \+ *lemma* subgroup_class.inclusion_mk
- \+ *lemma* subgroup_class.inclusion_right
- \+ *lemma* subgroup_class.inclusion_self



## [2022-04-29 12:25:30](https://github.com/leanprover-community/mathlib/commit/8eb2564)
feat(topology/instances/matrix): add `matrix` lemmas about `tsum` ([#13677](https://github.com/leanprover-community/mathlib/pull/13677))
This adds lemmas about how `tsum` interacts with `diagonal` and `transpose`, along with the helper `summable` and `has_sum` lemmas.
This also moves `topology/algebra/matrix` to `topology/instances/matrix`, since that seems to align better with how other types are handled.
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean


Modified src/topology/algebra/infinite_sum.lean


Renamed src/topology/algebra/matrix.lean to src/topology/instances/matrix.lean
- \+ *lemma* continuous_matrix_diag
- \+ *lemma* has_sum.matrix_block_diagonal'
- \+ *lemma* has_sum.matrix_block_diagonal
- \+ *lemma* has_sum.matrix_diag
- \+ *lemma* has_sum.matrix_diagonal
- \+ *lemma* has_sum.matrix_transpose
- \+ *lemma* matrix.diagonal_tsum
- \+ *lemma* matrix.transpose_tsum
- \+ *lemma* summable.matrix_block_diagonal'
- \+ *lemma* summable.matrix_block_diagonal
- \+ *lemma* summable.matrix_diag
- \+ *lemma* summable.matrix_diagonal
- \+ *lemma* summable.matrix_transpose
- \+ *lemma* summable_matrix_diagonal
- \+ *lemma* summable_matrix_transpose



## [2022-04-29 11:14:10](https://github.com/leanprover-community/mathlib/commit/889e956)
chore(analysis/asymptotics/asymptotics): relax `normed_group` to `semi_normed_group` in lemmas ([#13642](https://github.com/leanprover-community/mathlib/pull/13642))
This file already uses `E` vs `E'` for `has_norm` vs `normed_group`. This adds an `E''` to this naming scheme for `normed_group`, and repurposes `E'` to `semi_normed_group`. The majority of the lemmas in this file generalize without any additional work.
I've not attempted to relax the assumptions on lemmas where any proofs would have to change. Most of them would need their assumptions changing from `c ≠ 0` to `∥c∥ ≠ 0`, which is likely to be annoying.
In one place this results in dot notation breaking as the typeclass can no longer be found by unification.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+/\- *theorem* asymptotics.bound_of_is_O_cofinite
- \+/\- *theorem* asymptotics.bound_of_is_O_nat_at_top
- \+/\- *lemma* asymptotics.is_O.eq_zero_imp
- \+/\- *theorem* asymptotics.is_O.trans_tendsto
- \+/\- *theorem* asymptotics.is_O.trans_tendsto_nhds
- \+/\- *theorem* asymptotics.is_O_cofinite_iff
- \+/\- *theorem* asymptotics.is_O_const_const
- \+/\- *theorem* asymptotics.is_O_const_const_iff
- \+/\- *theorem* asymptotics.is_O_const_of_tendsto
- \+/\- *theorem* asymptotics.is_O_nat_at_top_iff
- \+/\- *theorem* asymptotics.is_O_one_nat_at_top_iff
- \+/\- *theorem* asymptotics.is_O_one_of_tendsto
- \+/\- *lemma* asymptotics.is_O_pure
- \+/\- *lemma* asymptotics.is_O_with.eq_zero_imp
- \+/\- *theorem* asymptotics.is_O_with_const_const
- \+/\- *theorem* asymptotics.is_O_zero_right_iff
- \+/\- *theorem* asymptotics.is_o.trans_tendsto
- \+/\- *theorem* asymptotics.is_o_const_const_iff
- \+/\- *lemma* asymptotics.is_o_const_id_at_bot
- \+/\- *lemma* asymptotics.is_o_const_id_at_top
- \+/\- *lemma* asymptotics.is_o_const_id_comap_norm_at_top
- \+/\- *theorem* asymptotics.is_o_const_iff
- \+/\- *theorem* asymptotics.is_o_const_iff_is_o_one
- \+/\- *lemma* asymptotics.is_o_const_left
- \+/\- *lemma* asymptotics.is_o_const_left_of_ne
- \+/\- *lemma* asymptotics.is_o_id_const
- \+/\- *theorem* asymptotics.is_o_one_iff
- \+/\- *lemma* asymptotics.is_o_pure
- \+/\- *lemma* asymptotics.is_o_top

Modified src/analysis/normed_space/units.lean




## [2022-04-29 09:31:57](https://github.com/leanprover-community/mathlib/commit/aab0b2d)
feat(algebra/algebra/basic): add some lemmas about `subsemiring` and `algebra_map` ([#13767](https://github.com/leanprover-community/mathlib/pull/13767))
These are analogs of `algebra_map_of_subring`, `coe_algebra_map_of_subring` and `algebra_map_of_subring_apply`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* algebra.algebra_map_of_subsemiring
- \+ *lemma* algebra.algebra_map_of_subsemiring_apply
- \+ *lemma* algebra.coe_algebra_map_of_subsemiring



## [2022-04-29 08:26:15](https://github.com/leanprover-community/mathlib/commit/8abfb3b)
feat(representation_theory/Rep): Rep k G is abelian ([#13689](https://github.com/leanprover-community/mathlib/pull/13689))
#### Estimated changes
Modified src/category_theory/abelian/functor_category.lean


Modified src/category_theory/abelian/transfer.lean
- \+ *def* category_theory.abelian_of_equivalence

Modified src/category_theory/limits/shapes/functor_category.lean


Modified src/representation_theory/Action.lean
- \+ *def* Action.abelian_aux

Modified src/representation_theory/Rep.lean




## [2022-04-29 06:35:27](https://github.com/leanprover-community/mathlib/commit/bc65b7c)
feat(data/list/basic): add `list.range_map` ([#13777](https://github.com/leanprover-community/mathlib/pull/13777))
* add `list.range_map` and `list.range_map_coe`;
* add `submonoid.closure_eq_image_prod` and `add_submonoid.closure_eq_image_prod`.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.range_map
- \+ *lemma* list.range_map_coe

Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* submonoid.closure_eq_image_prod



## [2022-04-29 06:35:26](https://github.com/leanprover-community/mathlib/commit/992e26f)
feat(topology/algebra/affine): a sufficiently small dilation of a point in the interior of a set lands in the interior ([#13766](https://github.com/leanprover-community/mathlib/pull/13766))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* vadd_vsub_eq_sub_vsub
- \+ *lemma* vsub_ne_zero

Modified src/analysis/normed/group/basic.lean
- \+ *lemma* ball_eq
- \+ *lemma* normed_group.nhds_basis_norm_lt
- \+ *lemma* normed_group.nhds_zero_basis_norm_lt

Modified src/analysis/normed_space/add_torsor.lean
- \+/\- *lemma* affine_subspace.is_closed_direction_iff
- \+/\- *lemma* antilipschitz_with_line_map
- \+ *lemma* eventually_homothety_image_subset_of_finite_subset_interior
- \+ *lemma* eventually_homothety_mem_of_mem_interior



## [2022-04-29 06:35:25](https://github.com/leanprover-community/mathlib/commit/b4cad37)
chore(ring_theory/mv_polynomial/basic): golf ([#13765](https://github.com/leanprover-community/mathlib/pull/13765))
#### Estimated changes
Modified src/ring_theory/mv_polynomial/basic.lean




## [2022-04-29 06:35:24](https://github.com/leanprover-community/mathlib/commit/5c1ee35)
feat(set_theory/game/pgame): `x - 0 = x + 0` ([#13731](https://github.com/leanprover-community/mathlib/pull/13731))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.sub_zero



## [2022-04-29 04:24:26](https://github.com/leanprover-community/mathlib/commit/7170b66)
chore(scripts): update nolints.txt ([#13775](https://github.com/leanprover-community/mathlib/pull/13775))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-04-29 04:24:25](https://github.com/leanprover-community/mathlib/commit/ead85e6)
chore(*/equiv): add simp to refl_apply and trans_apply where missing ([#13760](https://github.com/leanprover-community/mathlib/pull/13760))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+/\- *lemma* alg_equiv.trans_apply

Modified src/algebra/hom/equiv.lean


Modified src/linear_algebra/affine_space/affine_equiv.lean
- \+/\- *lemma* affine_equiv.refl_apply

Modified src/order/hom/basic.lean
- \+/\- *lemma* order_iso.refl_apply
- \+/\- *lemma* order_iso.trans_apply



## [2022-04-29 04:24:24](https://github.com/leanprover-community/mathlib/commit/e294500)
feat(category_theory/monoidal): transport rigid structure over an equivalence ([#13736](https://github.com/leanprover-community/mathlib/pull/13736))
#### Estimated changes
Modified src/category_theory/monoidal/category.lean
- \+ *lemma* category_theory.monoidal_category.hom_inv_id_tensor'
- \+ *lemma* category_theory.monoidal_category.inv_hom_id_tensor'
- \+ *lemma* category_theory.monoidal_category.tensor_hom_inv_id'
- \+ *lemma* category_theory.monoidal_category.tensor_inv_hom_id'

Modified src/category_theory/monoidal/rigid.lean
- \+ *def* category_theory.exact_pairing_congr
- \+ *def* category_theory.exact_pairing_congr_left
- \+ *def* category_theory.exact_pairing_congr_right

Added src/category_theory/monoidal/rigid/of_equivalence.lean
- \+ *def* category_theory.exact_pairing_of_faithful
- \+ *def* category_theory.exact_pairing_of_fully_faithful
- \+ *def* category_theory.has_left_dual_of_equivalence
- \+ *def* category_theory.has_right_dual_of_equivalence
- \+ *def* category_theory.left_rigid_category_of_equivalence
- \+ *def* category_theory.right_rigid_category_of_equivalence
- \+ *def* category_theory.rigid_category_of_equivalence



## [2022-04-29 04:24:23](https://github.com/leanprover-community/mathlib/commit/ccb9d64)
feat(category_theory/braiding): pull back a braiding along a faithful functor ([#13684](https://github.com/leanprover-community/mathlib/pull/13684))
I intend to use this to define the braiding/symmetry on `Rep k G` using the existing braiding/symmetry on `Module k`.
#### Estimated changes
Modified src/algebraic_geometry/open_immersion.lean


Modified src/algebraic_geometry/sheafed_space.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/functor/fully_faithful.lean
- \+/\- *lemma* category_theory.functor.map_injective
- \+/\- *lemma* category_theory.functor.map_iso_injective
- \+/\- *def* category_theory.functor.preimage
- \+ *def* category_theory.functor.preimage_iso
- \+ *lemma* category_theory.functor.preimage_iso_map_iso
- \- *def* category_theory.preimage_iso
- \- *lemma* category_theory.preimage_iso_hom
- \- *lemma* category_theory.preimage_iso_inv
- \- *lemma* category_theory.preimage_iso_map_iso

Modified src/category_theory/monoidal/braided.lean
- \+ *def* category_theory.braided_category_of_faithful
- \+ *def* category_theory.braided_category_of_fully_faithful
- \+ *def* category_theory.symmetric_category_of_faithful

Modified src/category_theory/subobject/mono_over.lean


Modified src/category_theory/yoneda.lean




## [2022-04-29 03:48:10](https://github.com/leanprover-community/mathlib/commit/8edb3d1)
feat(representation_theory/Rep): the category of representations ([#13683](https://github.com/leanprover-community/mathlib/pull/13683))
We define `Rep k G`, the category of `k`-linear representations of a monoid `G`.
Happily, by abstract nonsense we get that this has (co)limits and a monoidal structure for free.
This should play well with the new design for representations in [#13573](https://github.com/leanprover-community/mathlib/pull/13573).
#### Estimated changes
Added src/representation_theory/Action.lean
- \+ *def* Action.Action_punit_equivalence
- \+ *lemma* Action.comp_hom
- \+ *def* Action.forget
- \+ *def* Action.forget_monoidal
- \+ *def* Action.functor_category_equivalence.counit_iso
- \+ *def* Action.functor_category_equivalence.functor
- \+ *def* Action.functor_category_equivalence.inverse
- \+ *def* Action.functor_category_equivalence.unit_iso
- \+ *def* Action.functor_category_equivalence
- \+ *def* Action.functor_category_equivalence_comp_evaluation
- \+ *def* Action.hom.comp
- \+ *def* Action.hom.id
- \+ *lemma* Action.id_hom
- \+ *def* Action.mk_iso
- \+ *def* Action.res
- \+ *def* Action.res_comp
- \+ *def* Action.res_id
- \+ *def* Action.trivial
- \+ *def* Action.ρ_Aut
- \+ *lemma* Action.ρ_one
- \+ *def* category_theory.functor.map_Action

Added src/representation_theory/Rep.lean
- \+ *def* Rep.of



## [2022-04-29 00:29:56](https://github.com/leanprover-community/mathlib/commit/11a4a74)
feat(ring_theory/localization/basic): generalize to semiring ([#13459](https://github.com/leanprover-community/mathlib/pull/13459))
The main ingredient of this PR is the definition of `is_localization.lift` that works for semirings. The previous definition uses `ring_hom.mk'` that essentially states that `f 0 = 0` follows from other conditions. This does not holds for semirings. Instead, this PR defines the localization of monoid with zero, and uses this to define `is_localization.lift`.
- I think definitions around `localization_with_zero_map` might be ad hoc, and any suggestions for improvement are welcome!
- I plan to further generalize the localization API for semirings. This needs generalization of other ring theory stuff such as `local_ring` and `is_domain` (generalizing `local_ring` is partially done in [#13341](https://github.com/leanprover-community/mathlib/pull/13341)).
#### Estimated changes
Modified src/group_theory/monoid_localization.lean
- \+ *lemma* localization.lift_on_zero
- \+ *lemma* localization.mk_zero
- \+/\- *lemma* submonoid.localization_map.lift_left_inverse
- \+ *lemma* submonoid.localization_map.sec_zero_fst
- \+ *def* submonoid.localization_with_zero_map.to_monoid_with_zero_hom

Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/localization/basic.lean
- \+ *lemma* is_localization.lift_spec_mul_add
- \+/\- *lemma* is_localization.map_comp_map
- \+/\- *lemma* is_localization.map_map
- \+ *theorem* is_localization.mk'_add_eq_iff_add_mul_eq_mul
- \+ *lemma* is_localization.mul_add_inv_left
- \- *def* is_localization.to_localization_map
- \+ *def* is_localization.to_localization_with_zero_map
- \- *lemma* localization.lift_on_zero
- \+/\- *lemma* localization.mk_nat_cast
- \- *lemma* localization.mk_zero



## [2022-04-28 22:42:55](https://github.com/leanprover-community/mathlib/commit/214e2f1)
chore(set_theory/surreal/basic): Allow dot notation on `pgame.numeric` ([#13768](https://github.com/leanprover-community/mathlib/pull/13768))
Rename `numeric_neg`/`numeric_add` to `numeric.add`/`numeric.neg`. Prove `numeric.sub` in passing.
#### Estimated changes
Modified src/set_theory/surreal/basic.lean
- \+ *theorem* pgame.numeric.add
- \+ *theorem* pgame.numeric.neg
- \+ *lemma* pgame.numeric.sub
- \- *theorem* pgame.numeric_add
- \- *theorem* pgame.numeric_neg



## [2022-04-28 21:23:33](https://github.com/leanprover-community/mathlib/commit/ccd3774)
chore(ring_theory/*): dot notation for `submodule.fg` and `subalgebra.fg` ([#13737](https://github.com/leanprover-community/mathlib/pull/13737))
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean


Modified src/ring_theory/adjoin/fg.lean
- \+ *lemma* subalgebra.fg.map
- \+ *lemma* subalgebra.fg.prod
- \- *lemma* subalgebra.fg_map
- \- *lemma* subalgebra.fg_prod

Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/noetherian.lean
- \+ *theorem* submodule.fg.mul
- \+ *lemma* submodule.fg.pow
- \+ *theorem* submodule.fg.prod
- \+ *theorem* submodule.fg.sup
- \- *theorem* submodule.fg_mul
- \- *lemma* submodule.fg_pow
- \- *theorem* submodule.fg_prod
- \- *theorem* submodule.fg_sup



## [2022-04-28 21:23:32](https://github.com/leanprover-community/mathlib/commit/220d4b8)
doc(order/filter/small_sets): fix in doc ([#13648](https://github.com/leanprover-community/mathlib/pull/13648))
#### Estimated changes
Modified src/order/filter/small_sets.lean




## [2022-04-28 20:49:01](https://github.com/leanprover-community/mathlib/commit/c096a33)
feat(set_theory/game/birthday): Game birthday is zero iff empty ([#13715](https://github.com/leanprover-community/mathlib/pull/13715))
#### Estimated changes
Modified src/set_theory/game/birthday.lean
- \+ *theorem* pgame.birthday_eq_zero



## [2022-04-28 19:47:12](https://github.com/leanprover-community/mathlib/commit/8a32fdf)
feat(cyclotomic/eval): (q - 1) ^ totient n < |ϕₙ(q)| ([#12595](https://github.com/leanprover-community/mathlib/pull/12595))
Originally from the Wedderburn PR, but generalized to include an exponent.
#### Estimated changes
Modified src/ring_theory/polynomial/cyclotomic/eval.lean
- \+ *lemma* polynomial.cyclotomic_eval_lt_sub_one_pow_totient
- \+ *lemma* polynomial.cyclotomic_nonneg
- \+ *lemma* polynomial.cyclotomic_pos'
- \+ *lemma* polynomial.cyclotomic_pos_and_nonneg
- \+ *lemma* polynomial.sub_one_lt_nat_abs_cyclotomic_eval
- \+ *lemma* polynomial.sub_one_pow_totient_lt_cyclotomic_eval



## [2022-04-28 17:35:20](https://github.com/leanprover-community/mathlib/commit/0d3f8a7)
feat(ring_theory/submonoid/membership): generalize a few lemmas to `mul_mem_class` ([#13748](https://github.com/leanprover-community/mathlib/pull/13748))
This generalizes lemmas relating to the additive closure of a multiplicative monoid so that they also apply to multiplicative semigroups using `mul_mem_class`
#### Estimated changes
Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* mul_mem_class.mul_left_mem_add_closure
- \+ *lemma* mul_mem_class.mul_mem_add_closure
- \+ *lemma* mul_mem_class.mul_right_mem_add_closure
- \- *lemma* submonoid.mul_left_mem_add_closure
- \- *lemma* submonoid.mul_mem_add_closure
- \- *lemma* submonoid.mul_right_mem_add_closure

Modified src/ring_theory/subsemiring/basic.lean




## [2022-04-28 15:47:51](https://github.com/leanprover-community/mathlib/commit/c5bf480)
fix(group_theory/subsemigroup/basic): change `mul_one_class` to `has_mul` ([#13747](https://github.com/leanprover-community/mathlib/pull/13747))
#### Estimated changes
Modified src/group_theory/subsemigroup/basic.lean




## [2022-04-28 13:52:30](https://github.com/leanprover-community/mathlib/commit/1c92dfd)
chore(*/equiv): missing refl_symm lemmas ([#13761](https://github.com/leanprover-community/mathlib/pull/13761))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *theorem* alg_equiv.refl_symm

Modified src/algebra/hom/equiv.lean
- \+ *theorem* mul_equiv.refl_symm

Modified src/algebra/lie/basic.lean
- \+ *theorem* lie_equiv.refl_symm



## [2022-04-28 08:07:58](https://github.com/leanprover-community/mathlib/commit/0cb20fc)
feat(set_theory/ordinal/basic): `max a 0 = a` ([#13734](https://github.com/leanprover-community/mathlib/pull/13734))
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean
- \+ *lemma* ordinal.max_eq_zero
- \+ *lemma* ordinal.max_zero_left
- \+ *lemma* ordinal.max_zero_right



## [2022-04-28 08:07:57](https://github.com/leanprover-community/mathlib/commit/98e7848)
feat(set_theory/game/pgame): Right moves of nat game are empty ([#13730](https://github.com/leanprover-community/mathlib/pull/13730))
#### Estimated changes
Modified src/set_theory/game/pgame.lean




## [2022-04-28 07:28:19](https://github.com/leanprover-community/mathlib/commit/a0af147)
feat(set_theory/game/pgame): An empty game is a relabelling of `0` ([#13753](https://github.com/leanprover-community/mathlib/pull/13753))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *def* pgame.relabelling.is_empty



## [2022-04-27 23:52:26](https://github.com/leanprover-community/mathlib/commit/e89510c)
fix(ring_theory/subsemiring/basic): make `inclusion` a `ring_hom`, not a `monoid_hom` ([#13746](https://github.com/leanprover-community/mathlib/pull/13746))
#### Estimated changes
Modified src/ring_theory/subsemiring/basic.lean
- \+/\- *def* subsemiring.inclusion



## [2022-04-27 20:32:15](https://github.com/leanprover-community/mathlib/commit/60bb071)
feat(logic/unit): Make `punit.star` simp normal form of `default : punit` ([#13741](https://github.com/leanprover-community/mathlib/pull/13741))
#### Estimated changes
Modified src/logic/unique.lean
- \+ *lemma* punit.default_eq_star



## [2022-04-27 15:34:59](https://github.com/leanprover-community/mathlib/commit/dc589c8)
fix(topology/bornology): turn `bounded_space` into a `mixin` ([#13615](https://github.com/leanprover-community/mathlib/pull/13615))
Otherwise, we would need `bounded_pseudo_metric_space`,
`bounded_metric_space` etc.
Also add `set.finite.is_bounded`, `bornology.is_bounded.all`, and
`bornology.is_bounded_univ`.
#### Estimated changes
Modified src/topology/bornology/basic.lean
- \+ *lemma* bornology.cobounded_eq_bot
- \+ *lemma* bornology.cobounded_eq_bot_iff
- \+ *lemma* bornology.is_bounded.all
- \+/\- *lemma* bornology.is_bounded_compl_iff
- \+ *lemma* bornology.is_bounded_univ
- \+ *lemma* bornology.is_cobounded.all
- \+/\- *lemma* bornology.is_cobounded_compl_iff
- \+ *lemma* set.finite.is_bounded



## [2022-04-27 14:57:36](https://github.com/leanprover-community/mathlib/commit/d399744)
feat(measure_theory/measure/finite_measure_weak_convergence): define the topology of weak convergence of measures and prove some lemmas about it. ([#9943](https://github.com/leanprover-community/mathlib/pull/9943))
This PR has the definition of the topology of weak convergence ("convergence in law" / "convergence in distribution") on `finite_measure _` and on `probability_measure _`.
#### Estimated changes
Modified src/measure_theory/measure/finite_measure_weak_convergence.lean
- \+ *lemma* measure_theory.finite_measure.coe_to_weak_dual_bcnn
- \+ *lemma* measure_theory.finite_measure.continuous_test_against_nn_eval
- \+ *theorem* measure_theory.finite_measure.tendsto_iff_forall_lintegral_tendsto
- \+ *theorem* measure_theory.finite_measure.tendsto_iff_forall_test_against_nn_tendsto
- \+ *lemma* measure_theory.finite_measure.tendsto_iff_weak_star_tendsto
- \+ *def* measure_theory.finite_measure.to_weak_dual_bcnn
- \+ *lemma* measure_theory.finite_measure.to_weak_dual_bcnn_apply
- \+ *lemma* measure_theory.finite_measure.to_weak_dual_bcnn_continuous
- \- *def* measure_theory.finite_measure.to_weak_dual_bounded_continuous_nnreal
- \+ *lemma* measure_theory.probability_measure.coe_to_weak_dual_bcnn
- \+ *lemma* measure_theory.probability_measure.continuous_test_against_nn_eval
- \+ *theorem* measure_theory.probability_measure.tendsto_iff_forall_lintegral_tendsto
- \+ *lemma* measure_theory.probability_measure.tendsto_nhds_iff_to_finite_measures_tendsto_nhds
- \- *def* measure_theory.probability_measure.test_against_nn
- \- *lemma* measure_theory.probability_measure.test_against_nn_coe_eq
- \- *lemma* measure_theory.probability_measure.test_against_nn_const
- \- *lemma* measure_theory.probability_measure.test_against_nn_mono
- \+ *lemma* measure_theory.probability_measure.to_finite_measure_continuous
- \+ *lemma* measure_theory.probability_measure.to_finite_measure_embedding
- \- *lemma* measure_theory.probability_measure.to_finite_measure_test_against_nn_eq_test_against_nn
- \+ *def* measure_theory.probability_measure.to_weak_dual_bcnn
- \+ *lemma* measure_theory.probability_measure.to_weak_dual_bcnn_apply
- \+ *lemma* measure_theory.probability_measure.to_weak_dual_bcnn_continuous
- \- *def* measure_theory.probability_measure.to_weak_dual_bounded_continuous_nnreal

Modified src/topology/algebra/module/weak_dual.lean
- \+ *theorem* tendsto_iff_forall_eval_tendsto_top_dual_pairing



## [2022-04-27 10:54:41](https://github.com/leanprover-community/mathlib/commit/ccefda0)
perf(representation_theory/basic): speed up `representation.lin_hom` by a factor of 20 ([#13739](https://github.com/leanprover-community/mathlib/pull/13739))
`ext` was over-expanding, and the `simp`s were not all squeezed.
This is causing timeouts in other PRs.
#### Estimated changes
Modified src/representation_theory/basic.lean




## [2022-04-27 07:01:45](https://github.com/leanprover-community/mathlib/commit/5ac5c92)
feat(combinatorics/simple_graph/regularity/uniform): Witnesses of non-uniformity ([#13155](https://github.com/leanprover-community/mathlib/pull/13155))
Provide ways to pick witnesses of non-uniformity.
#### Estimated changes
Modified src/combinatorics/simple_graph/regularity/uniform.lean
- \+/\- *lemma* finpartition.bot_is_uniform
- \+ *lemma* finpartition.is_uniform.mono
- \+/\- *lemma* finpartition.non_uniforms_bot
- \+ *lemma* finpartition.non_uniforms_mono
- \+ *lemma* finpartition.nonuniform_witness_mem_nonuniform_witnesses
- \+ *lemma* simple_graph.left_nonuniform_witnesses_card
- \+ *lemma* simple_graph.left_nonuniform_witnesses_subset
- \+ *lemma* simple_graph.nonuniform_witness_card_le
- \+ *lemma* simple_graph.nonuniform_witness_spec
- \+ *lemma* simple_graph.nonuniform_witness_subset
- \+ *lemma* simple_graph.nonuniform_witnesses_spec
- \+ *lemma* simple_graph.not_is_uniform_iff
- \+ *lemma* simple_graph.right_nonuniform_witnesses_card
- \+ *lemma* simple_graph.right_nonuniform_witnesses_subset



## [2022-04-27 02:01:16](https://github.com/leanprover-community/mathlib/commit/cb2b02f)
feat(representation_theory/basic): representation theory without scalar actions ([#13573](https://github.com/leanprover-community/mathlib/pull/13573))
This PR rewrites the files `representation_theory/basic` and `representation_theory/invariants` so that they avoid making use of scalar actions. It also includes the new definitions and lemmas of PR [#13502](https://github.com/leanprover-community/mathlib/pull/13502) written with this new approach.
#### Estimated changes
Modified src/representation_theory/basic.lean
- \+ *lemma* representation.as_algebra_hom_of
- \+ *lemma* representation.as_group_hom_apply
- \- *lemma* representation.as_module_apply
- \+/\- *theorem* representation.char_conj
- \+ *theorem* representation.char_mul_comm
- \+/\- *theorem* representation.char_one
- \+ *def* representation.dual
- \+ *lemma* representation.dual_apply
- \+ *def* representation.lin_hom
- \+ *lemma* representation.lin_hom_apply
- \- *lemma* representation.of_smul
- \+ *def* representation.tprod
- \+ *lemma* representation.tprod_apply
- \+ *def* representation.trivial
- \+ *lemma* representation.trivial_def

Modified src/representation_theory/invariants.lean
- \+ *lemma* group_algebra.average_def
- \+ *theorem* group_algebra.mul_average_left
- \+ *theorem* group_algebra.mul_average_right
- \- *lemma* representation.average_def
- \+ *theorem* representation.average_map_id
- \+ *theorem* representation.average_map_invariant
- \- *lemma* representation.invariants'_carrier
- \+/\- *lemma* representation.mem_invariants
- \- *theorem* representation.mul_average_left
- \- *theorem* representation.mul_average_right
- \- *theorem* representation.smul_average_id
- \- *theorem* representation.smul_average_invariant



## [2022-04-27 00:04:48](https://github.com/leanprover-community/mathlib/commit/79e309b)
feat(set_theory/game/pgame): Define `is_option` relation ([#13700](https://github.com/leanprover-community/mathlib/pull/13700))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.is_option.mk_left
- \+ *theorem* pgame.is_option.mk_right
- \+ *theorem* pgame.wf_is_option



## [2022-04-26 22:05:34](https://github.com/leanprover-community/mathlib/commit/48997d7)
fix(data/set/basic): fix name of `has_mem.mem.out` ([#13721](https://github.com/leanprover-community/mathlib/pull/13721))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* has_mem.mem.out
- \- *lemma* set.has_mem.mem.out



## [2022-04-26 20:19:00](https://github.com/leanprover-community/mathlib/commit/b00a7f8)
refactor(number_theory/padics/padic_norm): split file ([#13576](https://github.com/leanprover-community/mathlib/pull/13576))
This PR splits the initial part of the `padic_norm.lean` file that defines p-adic valuations into a new file called `padic_val.lean`. This split makes sense to me since it seems most files importing this don't actually use the norm, so those files can build more in parallel. It also seems like a good organizational change: This way people can look at the files in this directory and see immediately where the valuation is defined, and people looking for the definition of `padic_norm` in `padic_norm.lean` don't have to scroll.
#### Estimated changes
Modified src/algebra/gcd_monoid/nat.lean


Modified src/group_theory/exponent.lean


Modified src/number_theory/padics/padic_norm.lean
- \- *lemma* dvd_of_one_le_padic_val_nat
- \- *lemma* one_le_padic_val_nat_of_dvd
- \- *lemma* padic_val_int.eq_zero_of_not_dvd
- \- *lemma* padic_val_int.mul
- \- *lemma* padic_val_int.of_nat
- \- *lemma* padic_val_int.of_ne_one_ne_zero
- \- *lemma* padic_val_int.self
- \- *def* padic_val_int
- \- *lemma* padic_val_int_dvd
- \- *lemma* padic_val_int_dvd_iff
- \- *lemma* padic_val_int_mul_eq_succ
- \- *lemma* padic_val_int_self
- \- *lemma* padic_val_nat.eq_zero_of_not_dvd
- \- *lemma* padic_val_nat.self
- \- *def* padic_val_nat
- \- *lemma* padic_val_nat_def
- \- *lemma* padic_val_nat_dvd_iff
- \- *lemma* padic_val_nat_eq_factorization
- \- *lemma* padic_val_nat_primes
- \- *lemma* padic_val_nat_self
- \- *lemma* padic_val_rat.finite_int_prime_iff
- \- *theorem* padic_val_rat.le_padic_val_rat_add_of_le
- \- *theorem* padic_val_rat.min_le_padic_val_rat_add
- \- *lemma* padic_val_rat.multiplicity_sub_multiplicity
- \- *lemma* padic_val_rat.of_int
- \- *lemma* padic_val_rat.of_int_multiplicity
- \- *lemma* padic_val_rat.of_nat
- \- *lemma* padic_val_rat.padic_val_rat_le_padic_val_rat_iff
- \- *lemma* padic_val_rat.self
- \- *theorem* padic_val_rat.sum_pos_of_pos
- \- *def* padic_val_rat
- \- *lemma* padic_val_rat_of_nat
- \- *lemma* pow_padic_val_nat_dvd
- \- *lemma* pow_succ_padic_val_nat_not_dvd
- \- *lemma* prod_pow_prime_padic_val_nat
- \- *lemma* range_pow_padic_val_nat_subset_divisors'
- \- *lemma* range_pow_padic_val_nat_subset_divisors
- \- *lemma* zero_le_padic_val_rat_of_nat

Added src/number_theory/padics/padic_val.lean
- \+ *lemma* dvd_of_one_le_padic_val_nat
- \+ *lemma* one_le_padic_val_nat_of_dvd
- \+ *lemma* padic_val_int.eq_zero_of_not_dvd
- \+ *lemma* padic_val_int.mul
- \+ *lemma* padic_val_int.of_nat
- \+ *lemma* padic_val_int.of_ne_one_ne_zero
- \+ *lemma* padic_val_int.self
- \+ *def* padic_val_int
- \+ *lemma* padic_val_int_dvd
- \+ *lemma* padic_val_int_dvd_iff
- \+ *lemma* padic_val_int_mul_eq_succ
- \+ *lemma* padic_val_int_self
- \+ *lemma* padic_val_nat.eq_zero_of_not_dvd
- \+ *lemma* padic_val_nat.self
- \+ *def* padic_val_nat
- \+ *lemma* padic_val_nat_def
- \+ *lemma* padic_val_nat_dvd_iff
- \+ *lemma* padic_val_nat_eq_factorization
- \+ *lemma* padic_val_nat_primes
- \+ *lemma* padic_val_nat_self
- \+ *lemma* padic_val_rat.finite_int_prime_iff
- \+ *theorem* padic_val_rat.le_padic_val_rat_add_of_le
- \+ *theorem* padic_val_rat.min_le_padic_val_rat_add
- \+ *lemma* padic_val_rat.multiplicity_sub_multiplicity
- \+ *lemma* padic_val_rat.of_int
- \+ *lemma* padic_val_rat.of_int_multiplicity
- \+ *lemma* padic_val_rat.of_nat
- \+ *lemma* padic_val_rat.padic_val_rat_le_padic_val_rat_iff
- \+ *lemma* padic_val_rat.self
- \+ *theorem* padic_val_rat.sum_pos_of_pos
- \+ *def* padic_val_rat
- \+ *lemma* padic_val_rat_of_nat
- \+ *lemma* pow_padic_val_nat_dvd
- \+ *lemma* pow_succ_padic_val_nat_not_dvd
- \+ *lemma* prod_pow_prime_padic_val_nat
- \+ *lemma* range_pow_padic_val_nat_subset_divisors'
- \+ *lemma* range_pow_padic_val_nat_subset_divisors
- \+ *lemma* zero_le_padic_val_rat_of_nat

Modified src/ring_theory/polynomial/cyclotomic/eval.lean




## [2022-04-26 18:41:44](https://github.com/leanprover-community/mathlib/commit/de79a76)
chore(topology/continuous_function/zero_at_infty): add `is_central_scalar` instance ([#13710](https://github.com/leanprover-community/mathlib/pull/13710))
#### Estimated changes
Modified src/topology/continuous_function/zero_at_infty.lean




## [2022-04-26 18:41:43](https://github.com/leanprover-community/mathlib/commit/76de6f7)
feat(group_theory/subsemigroup/operations): port from submonoid  ([#12112](https://github.com/leanprover-community/mathlib/pull/12112))
Taken from `group_theory.submonoid.operations`, trying to keep as much API as possible
#### Estimated changes
Modified src/field_theory/intermediate_field.lean


Modified src/group_theory/submonoid/operations.lean
- \- *lemma* submonoid_class.coe_mul
- \- *lemma* submonoid_class.mk_mul_mk
- \- *lemma* submonoid_class.mul_def

Added src/group_theory/subsemigroup/operations.lean
- \+ *lemma* add_subsemigroup.to_subsemigroup'_closure
- \+ *def* add_subsemigroup.to_subsemigroup
- \+ *lemma* add_subsemigroup.to_subsemigroup_closure
- \+ *def* mul_equiv.of_left_inverse
- \+ *def* mul_equiv.subsemigroup_congr
- \+ *def* mul_equiv.subsemigroup_map
- \+ *def* mul_hom.cod_srestrict
- \+ *lemma* mul_hom.coe_srange
- \+ *lemma* mul_hom.coe_srange_restrict
- \+ *lemma* mul_hom.map_mclosure
- \+ *lemma* mul_hom.map_srange
- \+ *lemma* mul_hom.mclosure_preimage_le
- \+ *lemma* mul_hom.mem_srange
- \+ *lemma* mul_hom.prod_map_comap_prod'
- \+ *def* mul_hom.srange
- \+ *lemma* mul_hom.srange_eq_map
- \+ *def* mul_hom.srange_restrict
- \+ *lemma* mul_hom.srange_restrict_surjective
- \+ *lemma* mul_hom.srange_top_iff_surjective
- \+ *lemma* mul_hom.srange_top_of_surjective
- \+ *def* mul_hom.srestrict
- \+ *lemma* mul_hom.srestrict_apply
- \+ *def* mul_hom.subsemigroup_comap
- \+ *def* mul_hom.subsemigroup_map
- \+ *lemma* mul_hom.subsemigroup_map_surjective
- \+ *lemma* mul_mem_class.coe_mul
- \+ *theorem* mul_mem_class.coe_subtype
- \+ *lemma* mul_mem_class.mk_mul_mk
- \+ *lemma* mul_mem_class.mul_def
- \+ *def* mul_mem_class.subtype
- \+ *lemma* subsemigroup.apply_coe_mem_map
- \+ *lemma* subsemigroup.bot_prod_bot
- \+ *lemma* subsemigroup.closure_closure_coe_preimage
- \+ *lemma* subsemigroup.coe_comap
- \+ *lemma* subsemigroup.coe_equiv_map_of_injective_apply
- \+ *lemma* subsemigroup.coe_map
- \+ *lemma* subsemigroup.coe_prod
- \+ *def* subsemigroup.comap
- \+ *lemma* subsemigroup.comap_comap
- \+ *lemma* subsemigroup.comap_equiv_eq_map_symm
- \+ *lemma* subsemigroup.comap_id
- \+ *lemma* subsemigroup.comap_inf
- \+ *lemma* subsemigroup.comap_inf_map_of_injective
- \+ *lemma* subsemigroup.comap_infi
- \+ *lemma* subsemigroup.comap_infi_map_of_injective
- \+ *lemma* subsemigroup.comap_injective_of_surjective
- \+ *lemma* subsemigroup.comap_le_comap_iff_of_surjective
- \+ *lemma* subsemigroup.comap_map_comap
- \+ *lemma* subsemigroup.comap_map_eq_of_injective
- \+ *lemma* subsemigroup.comap_strict_mono_of_surjective
- \+ *lemma* subsemigroup.comap_sup_map_of_injective
- \+ *lemma* subsemigroup.comap_supr_map_of_injective
- \+ *lemma* subsemigroup.comap_surjective_of_injective
- \+ *lemma* subsemigroup.comap_top
- \+ *lemma* subsemigroup.eq_top_iff'
- \+ *lemma* subsemigroup.gc_map_comap
- \+ *def* subsemigroup.gci_map_comap
- \+ *def* subsemigroup.gi_map_comap
- \+ *def* subsemigroup.inclusion
- \+ *lemma* subsemigroup.le_comap_map
- \+ *lemma* subsemigroup.le_comap_of_map_le
- \+ *lemma* subsemigroup.le_prod_iff
- \+ *def* subsemigroup.map
- \+ *lemma* subsemigroup.map_bot
- \+ *lemma* subsemigroup.map_comap_eq_of_surjective
- \+ *lemma* subsemigroup.map_comap_le
- \+ *lemma* subsemigroup.map_comap_map
- \+ *lemma* subsemigroup.map_equiv_eq_comap_symm
- \+ *lemma* subsemigroup.map_equiv_top
- \+ *lemma* subsemigroup.map_id
- \+ *lemma* subsemigroup.map_inf_comap_of_surjective
- \+ *lemma* subsemigroup.map_infi_comap_of_surjective
- \+ *lemma* subsemigroup.map_injective_of_injective
- \+ *lemma* subsemigroup.map_le_iff_le_comap
- \+ *lemma* subsemigroup.map_le_map_iff_of_injective
- \+ *lemma* subsemigroup.map_le_of_le_comap
- \+ *lemma* subsemigroup.map_map
- \+ *lemma* subsemigroup.map_strict_mono_of_injective
- \+ *lemma* subsemigroup.map_sup
- \+ *lemma* subsemigroup.map_sup_comap_of_surjective
- \+ *lemma* subsemigroup.map_supr
- \+ *lemma* subsemigroup.map_supr_comap_of_surjective
- \+ *lemma* subsemigroup.map_surjective_of_surjective
- \+ *lemma* subsemigroup.mem_comap
- \+ *lemma* subsemigroup.mem_map
- \+ *lemma* subsemigroup.mem_map_equiv
- \+ *lemma* subsemigroup.mem_map_iff_mem
- \+ *lemma* subsemigroup.mem_map_of_mem
- \+ *lemma* subsemigroup.mem_prod
- \+ *lemma* subsemigroup.monotone_comap
- \+ *lemma* subsemigroup.monotone_map
- \+ *def* subsemigroup.prod
- \+ *lemma* subsemigroup.prod_eq_top_iff
- \+ *def* subsemigroup.prod_equiv
- \+ *lemma* subsemigroup.prod_mono
- \+ *lemma* subsemigroup.prod_top
- \+ *lemma* subsemigroup.range_subtype
- \+ *lemma* subsemigroup.srange_fst
- \+ *lemma* subsemigroup.srange_snd
- \+ *lemma* subsemigroup.to_add_subsemigroup'_closure
- \+ *def* subsemigroup.to_add_subsemigroup
- \+ *lemma* subsemigroup.to_add_subsemigroup_closure
- \+ *def* subsemigroup.top_equiv
- \+ *lemma* subsemigroup.top_equiv_to_mul_hom
- \+ *lemma* subsemigroup.top_prod
- \+ *lemma* subsemigroup.top_prod_top



## [2022-04-26 17:50:15](https://github.com/leanprover-community/mathlib/commit/560d1a7)
chore(topology/continuous_function/continuous_map): add missing instances for `continuous_map` ([#13717](https://github.com/leanprover-community/mathlib/pull/13717))
This adds instances related to the ring variants, i.e., non-unital, non-associative (semi)rings.
To avoid introducing accidental diamonds, this also changes how the existing instances are constructed, such that they now go through the `function.injective.*` definitions.
#### Estimated changes
Modified src/topology/continuous_function/algebra.lean




## [2022-04-26 17:50:14](https://github.com/leanprover-community/mathlib/commit/325dbc8)
refactor(number_theory/legendre_symbol/quadratic_reciprocity.lean): change definition of legendre_sym, simplify proofs, add lemmas ([#13667](https://github.com/leanprover-community/mathlib/pull/13667))
This changes the definition of `legendre_sym` to use `quadratic_char`.
The proof of some of the statements can then be simplified by using the corresponding statements for quadratic characters.
Some new API lemmas are added, including the fact that the Legendre symbol is multiplicative,
Also, a few `simps` are squeezed in `.../quadratic_char.lean`.
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.ring_char_zmod_n

Modified src/number_theory/legendre_symbol/quadratic_char.lean
- \+/\- *lemma* char.quadratic_char_sq_one
- \- *lemma* finite_field.unit_is_sqare_iff
- \+ *lemma* finite_field.unit_is_square_iff

Modified src/number_theory/legendre_symbol/quadratic_reciprocity.lean
- \+/\- *def* zmod.legendre_sym
- \+/\- *lemma* zmod.legendre_sym_eq_one_or_neg_one
- \+/\- *lemma* zmod.legendre_sym_eq_zero_iff
- \+ *def* zmod.legendre_sym_hom
- \+ *theorem* zmod.legendre_sym_mod
- \+ *lemma* zmod.legendre_sym_mul
- \+ *lemma* zmod.legendre_sym_one
- \+ *theorem* zmod.legendre_sym_sq_one'
- \+ *theorem* zmod.legendre_sym_sq_one
- \+ *lemma* zmod.legendre_sym_zero



## [2022-04-26 15:51:40](https://github.com/leanprover-community/mathlib/commit/8b14d48)
feat(logic/relation): Transitive closure of well-founded relation is well-founded ([#13698](https://github.com/leanprover-community/mathlib/pull/13698))
#### Estimated changes
Modified src/logic/relation.lean
- \+ *lemma* relation.well_founded.trans_gen



## [2022-04-26 13:36:55](https://github.com/leanprover-community/mathlib/commit/e77dbe0)
doc(data/list/*): Fix file links ([#13711](https://github.com/leanprover-community/mathlib/pull/13711))
They were linking to `data.list.data.list.defs`.
#### Estimated changes
Modified src/data/list/count.lean


Modified src/data/list/join.lean


Modified src/data/list/prod_sigma.lean


Modified src/order/category/BoundedDistribLattice.lean




## [2022-04-26 13:36:53](https://github.com/leanprover-community/mathlib/commit/bfa0ba5)
feat(analysis/normed_space/pointwise): The closure of a thickening ([#13708](https://github.com/leanprover-community/mathlib/pull/13708))
Prove `closure (thickening δ s) = cthickening δ s` and golf "thickening a thickening" lemmas.
#### Estimated changes
Modified src/analysis/normed_space/pointwise.lean
- \+ *lemma* closure_thickening



## [2022-04-26 13:36:52](https://github.com/leanprover-community/mathlib/commit/e6c6764)
feat(logic/relation): Add missing instances ([#13704](https://github.com/leanprover-community/mathlib/pull/13704))
#### Estimated changes
Modified src/logic/relation.lean




## [2022-04-26 13:36:51](https://github.com/leanprover-community/mathlib/commit/3d5e5ee)
feat(data/list/*): Miscellaneous lemmas ([#13577](https://github.com/leanprover-community/mathlib/pull/13577))
A few lemmas about `list.chain`, `list.pairwise`. Also rename `list.chain_of_pairwise` to `list.pairwise.chain` for dot notation.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.set_of_mem_cons

Modified src/data/list/chain.lean
- \- *theorem* list.chain_of_pairwise

Modified src/data/list/cycle.lean


Modified src/data/list/pairwise.lean
- \+ *lemma* list.pairwise.forall_of_forall_of_flip

Modified src/logic/basic.lean
- \+ *lemma* congr_fun₂
- \+ *lemma* congr_fun₃
- \+ *lemma* funext₂
- \+ *lemma* funext₃

Modified src/logic/relation.lean
- \+ *lemma* flip_eq_iff
- \+ *lemma* swap_eq_iff
- \+ *lemma* symmetric.flip_eq
- \+ *lemma* symmetric.swap_eq



## [2022-04-26 11:29:38](https://github.com/leanprover-community/mathlib/commit/c83488b)
feat(topology/order/priestley): Priestley spaces ([#12044](https://github.com/leanprover-community/mathlib/pull/12044))
Define `priestley_space`, a Prop-valued mixin for an ordered topological space to respect Priestley's separation axiom.
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* ne.not_le_or_not_le

Added src/topology/order/priestley.lean
- \+ *lemma* exists_clopen_lower_of_not_le
- \+ *lemma* exists_clopen_upper_of_not_le
- \+ *lemma* exists_clopen_upper_or_lower_of_ne



## [2022-04-26 09:51:42](https://github.com/leanprover-community/mathlib/commit/b0efdbb)
feat(algebra/module/linear_map) : cancel_right and cancel_left for linear_maps ([#13703](https://github.com/leanprover-community/mathlib/pull/13703))
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *theorem* linear_map.cancel_left
- \+ *theorem* linear_map.cancel_right



## [2022-04-26 09:51:41](https://github.com/leanprover-community/mathlib/commit/5172448)
feat(set_theory/game/pgame): Conway induction on games ([#13699](https://github.com/leanprover-community/mathlib/pull/13699))
This is a more convenient restatement of the induction principle of the type.
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *def* pgame.move_rec_on



## [2022-04-26 09:51:40](https://github.com/leanprover-community/mathlib/commit/4c6b373)
feat(group_theory/subgroup/basic): `zpowers_le` ([#13693](https://github.com/leanprover-community/mathlib/pull/13693))
This PR adds a lemma `zpowers_le : zpowers g ≤ H ↔ g ∈ H`. I also fixed the `to_additive` name of a lemma from a previous PR.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.zpowers_le



## [2022-04-26 09:51:39](https://github.com/leanprover-community/mathlib/commit/b94ea15)
refactor(linear_algebra/matrix/trace): unbundle `matrix.diag` ([#13687](https://github.com/leanprover-community/mathlib/pull/13687))
The bundling makes it awkward to work with, as the base ring has to be specified even though it doesn't affect the computation.
This brings it in line with `matrix.diagonal`.
The bundled version is now available as `matrix.diag_linear_map`.
This adds a handful of missing lemmas about `diag` inspired by those about `diagonal`; almost all of which are just `rfl`.
#### Estimated changes
Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified src/analysis/matrix.lean


Modified src/data/matrix/basic.lean
- \+ *def* matrix.diag
- \+ *theorem* matrix.diag_add
- \+ *def* matrix.diag_add_monoid_hom
- \+ *lemma* matrix.diag_col_mul_row
- \+ *lemma* matrix.diag_conj_transpose
- \+ *lemma* matrix.diag_diagonal
- \+ *def* matrix.diag_linear_map
- \+ *lemma* matrix.diag_map
- \+ *lemma* matrix.diag_minor
- \+ *theorem* matrix.diag_neg
- \+ *theorem* matrix.diag_one
- \+ *theorem* matrix.diag_smul
- \+ *theorem* matrix.diag_sub
- \+ *lemma* matrix.diag_transpose
- \+ *theorem* matrix.diag_zero
- \+/\- *theorem* matrix.diagonal_apply_eq
- \+/\- *theorem* matrix.diagonal_apply_ne'
- \+/\- *theorem* matrix.diagonal_apply_ne
- \+/\- *theorem* matrix.one_apply_eq

Modified src/data/matrix/basis.lean
- \+/\- *lemma* matrix.std_basis_matrix.diag_same
- \+/\- *lemma* matrix.std_basis_matrix.diag_zero

Modified src/linear_algebra/matrix/is_diag.lean
- \+ *lemma* matrix.is_diag.diagonal_diag
- \- *lemma* matrix.is_diag.exists_diagonal
- \+ *lemma* matrix.is_diag_iff_diagonal_diag
- \- *lemma* matrix.is_diag_iff_exists_diagonal

Modified src/linear_algebra/matrix/trace.lean
- \- *def* matrix.diag
- \- *lemma* matrix.diag_apply
- \- *lemma* matrix.diag_col_mul_row
- \- *lemma* matrix.diag_one
- \- *lemma* matrix.diag_transpose
- \+/\- *lemma* matrix.trace_diag

Modified src/topology/algebra/matrix.lean
- \+/\- *lemma* continuous.matrix_diag



## [2022-04-26 07:55:34](https://github.com/leanprover-community/mathlib/commit/6ae00ad)
chore(tactic/field_simp): fix docstring ([#13695](https://github.com/leanprover-community/mathlib/pull/13695))
#### Estimated changes
Modified src/tactic/field_simp.lean




## [2022-04-26 07:55:33](https://github.com/leanprover-community/mathlib/commit/a02f11f)
feat(algebra/ring/equiv): generalize `ring_equiv` material to allow for non-unital rings ([#13626](https://github.com/leanprover-community/mathlib/pull/13626))
#### Estimated changes
Modified src/algebra/hom/equiv.lean
- \+/\- *lemma* mul_equiv.Pi_congr_right_refl
- \+/\- *def* mul_equiv.arrow_congr

Modified src/algebra/ring/equiv.lean
- \+ *def* add_equiv.to_ring_equiv
- \+/\- *def* mul_equiv.to_ring_equiv
- \+/\- *lemma* ring_equiv.Pi_congr_right_refl
- \+ *lemma* ring_equiv.coe_non_unital_ring_hom_inj_iff
- \+/\- *lemma* ring_equiv.coe_of_bijective
- \+ *lemma* ring_equiv.coe_to_non_unital_ring_hom
- \+/\- *lemma* ring_equiv.of_bijective_apply
- \+ *def* ring_equiv.of_hom_inv'
- \+/\- *def* ring_equiv.of_hom_inv
- \- *lemma* ring_equiv.of_hom_inv_apply
- \- *lemma* ring_equiv.of_hom_inv_symm_apply
- \+ *lemma* ring_equiv.symm_to_non_unital_ring_hom_apply_to_non_unital_ring_hom_apply
- \+ *lemma* ring_equiv.symm_to_non_unital_ring_hom_comp_to_non_unital_ring_hom
- \+ *def* ring_equiv.to_non_unital_ring_hom
- \+ *lemma* ring_equiv.to_non_unital_ring_hom_apply_symm_to_non_unital_ring_hom_apply
- \+ *lemma* ring_equiv.to_non_unital_ring_hom_commutes
- \+ *lemma* ring_equiv.to_non_unital_ring_hom_comp_symm_to_non_unital_ring_hom
- \+ *lemma* ring_equiv.to_non_unital_ring_hom_eq_coe
- \+ *lemma* ring_equiv.to_non_unital_ring_hom_injective
- \+ *lemma* ring_equiv.to_non_unital_ring_hom_refl
- \+ *lemma* ring_equiv.to_non_unital_ring_hom_trans

Modified src/data/polynomial/eval.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/valuation/valuation_ring.lean




## [2022-04-26 07:55:32](https://github.com/leanprover-community/mathlib/commit/1b1ae61)
feat(analysis/normed_space/pointwise): Thickening a thickening ([#13380](https://github.com/leanprover-community/mathlib/pull/13380))
In a real normed space, thickening twice is the same as thickening once.
#### Estimated changes
Modified src/analysis/normed_space/pointwise.lean
- \+ *lemma* cthickening_cthickening
- \+ *lemma* cthickening_thickening
- \+ *lemma* inf_edist_cthickening
- \+ *lemma* inf_edist_thickening
- \+ *lemma* thickening_cthickening
- \+ *lemma* thickening_thickening

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.le_sub_of_add_le_left
- \+ *lemma* ennreal.le_sub_of_add_le_right
- \+ *lemma* ennreal.of_real_sub

Modified src/topology/metric_space/basic.lean
- \+ *lemma* edist_le_of_real
- \+ *lemma* edist_lt_of_real

Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* metric.cthickening_cthickening_subset
- \+ *lemma* metric.cthickening_thickening_subset
- \+ *lemma* metric.thickening_cthickening_subset
- \+ *lemma* metric.thickening_thickening_subset



## [2022-04-26 07:21:28](https://github.com/leanprover-community/mathlib/commit/093b583)
feat(set_theory/game/pgame): `ordinal.to_pgame` ([#13628](https://github.com/leanprover-community/mathlib/pull/13628))
We define the canonical map from ordinals to pre-games and prove it's an order embedding.
#### Estimated changes
Added src/set_theory/game/ordinal.lean
- \+ *def* ordinal.to_left_moves_to_pgame
- \+ *theorem* ordinal.to_pgame_def
- \+ *theorem* ordinal.to_pgame_injective
- \+ *theorem* ordinal.to_pgame_le
- \+ *theorem* ordinal.to_pgame_le_iff
- \+ *theorem* ordinal.to_pgame_left_moves
- \+ *theorem* ordinal.to_pgame_lt
- \+ *theorem* ordinal.to_pgame_lt_iff
- \+ *theorem* ordinal.to_pgame_move_left
- \+ *theorem* ordinal.to_pgame_move_left_heq
- \+ *theorem* ordinal.to_pgame_right_moves



## [2022-04-26 04:54:38](https://github.com/leanprover-community/mathlib/commit/bf67d47)
chore(scripts): update nolints.txt ([#13706](https://github.com/leanprover-community/mathlib/pull/13706))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2022-04-26 04:54:37](https://github.com/leanprover-community/mathlib/commit/748ea79)
feat(order/filter/basic): more lemmas about `filter.comap` ([#13619](https://github.com/leanprover-community/mathlib/pull/13619))
* add `set.compl_def`, `set.finite_image_fst_and_snd_iff`, and `set.forall_finite_image_eval_iff`;
* add `filter.coext`, an extensionality lemma that is more useful for "cofilters";
* rename `filter.eventually_comap'` to `filter.eventually.comap`;
* add `filter.mem_comap'`, `filter.mem_comap_iff_compl`, and `filter.compl_mem_comap`;
* add `filter.compl_mem_coprod`, replace `filter.compl_mem_Coprod_iff` with a simpler `filter.compl_mem_Coprod`;
* add `filter.map_top`;
* use new lemmas to golf some proofs.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.compl_def

Modified src/data/set/finite.lean
- \+ *lemma* set.finite_image_fst_and_snd_iff
- \+ *lemma* set.forall_finite_image_eval_iff

Modified src/order/filter/basic.lean
- \+ *lemma* filter.compl_mem_comap
- \+ *lemma* filter.compl_mem_coprod
- \+ *lemma* filter.eventually.comap
- \- *lemma* filter.eventually_comap'
- \+/\- *lemma* filter.eventually_comap
- \+/\- *lemma* filter.frequently_comap
- \+ *lemma* filter.map_top
- \+ *lemma* filter.mem_comap'
- \+ *lemma* filter.mem_comap_iff_compl

Modified src/order/filter/cofinite.lean


Modified src/order/filter/pi.lean
- \+ *lemma* filter.compl_mem_Coprod
- \- *lemma* filter.compl_mem_Coprod_iff

Modified src/topology/algebra/order/intermediate_value.lean


Modified src/topology/subset_properties.lean




## [2022-04-26 02:57:32](https://github.com/leanprover-community/mathlib/commit/4de6527)
feat(algebra/ring/basic): define non-unital commutative (semi)rings ([#13476](https://github.com/leanprover-community/mathlib/pull/13476))
This adds the classes of non-unital commutative (semi)rings. These are necessary to talk about, for example, non-unital commutative C∗-algebras such as `C₀(X, ℂ)` which are vital for the continuous functional calculus.
In addition, we weaken many type class assumptions in `algebra/ring/basic` to `non_unital_non_assoc_ring`.
#### Estimated changes
Modified src/algebra/monoid_algebra/basic.lean


Modified src/algebra/order/ring.lean


Modified src/algebra/ring/basic.lean
- \+/\- *lemma* is_regular_iff_ne_zero'

Modified src/algebra/ring/boolean_ring.lean
- \+ *def* generalized_boolean_algebra.to_non_unital_comm_ring
- \- *def* generalized_boolean_algebra.to_non_unital_ring

Modified src/algebra/ring/equiv.lean


Modified src/algebra/ring/opposite.lean


Modified src/algebra/ring/pi.lean


Modified src/algebra/ring/prod.lean


Modified src/algebra/ring/ulift.lean


Modified src/data/finsupp/pointwise.lean


Modified src/data/set/pointwise.lean


Modified src/logic/equiv/transfer_instance.lean


Modified src/ring_theory/hahn_series.lean


Modified src/topology/continuous_function/zero_at_infty.lean


Modified src/topology/locally_constant/algebra.lean




## [2022-04-26 01:09:50](https://github.com/leanprover-community/mathlib/commit/24a8bb9)
feat(order/well-founded): Remove redundant arguments ([#13702](https://github.com/leanprover-community/mathlib/pull/13702))
All of these are inferred as `{α : Type*}` (as opposed to `{α : Sort*}`), and there is already a `variables {α : Type*}` at the top of the file.
#### Estimated changes
Modified src/order/well_founded.lean
- \+/\- *theorem* well_founded.min_mem
- \+/\- *theorem* well_founded.not_lt_min
- \+/\- *theorem* well_founded.well_founded_iff_has_min



## [2022-04-25 23:11:10](https://github.com/leanprover-community/mathlib/commit/438b39a)
feat(set_theory/cardinal/basic): Distributivity of `cardinal.sum` and + ([#13643](https://github.com/leanprover-community/mathlib/pull/13643))
`cardinal.sum_add_distrib` shows that `cardinal.sum` distributes over +.
#### Estimated changes
Modified src/logic/equiv/basic.lean
- \+ *def* equiv.sigma_sum_distrib

Modified src/set_theory/cardinal/basic.lean
- \+ *theorem* cardinal.sum_add_distrib



## [2022-04-25 19:25:37](https://github.com/leanprover-community/mathlib/commit/8f604aa)
feat(data/nat/totient): totient equals one iff ([#13688](https://github.com/leanprover-community/mathlib/pull/13688))
#### Estimated changes
Modified src/data/nat/totient.lean
- \+ *lemma* nat.totient_eq_one_iff



## [2022-04-25 17:22:45](https://github.com/leanprover-community/mathlib/commit/4e50b68)
feat(category_theory/abelian): if D is abelian so is C ⥤ D ([#13686](https://github.com/leanprover-community/mathlib/pull/13686))
Needed for LTE, and also useful to show `Rep k G` is abelian.
#### Estimated changes
Added src/category_theory/abelian/functor_category.lean
- \+ *lemma* category_theory.abelian.functor_category.coimage_image_comparison_app'
- \+ *lemma* category_theory.abelian.functor_category.coimage_image_comparison_app
- \+ *def* category_theory.abelian.functor_category.coimage_obj_iso
- \+ *def* category_theory.abelian.functor_category.image_obj_iso

Modified src/category_theory/limits/preserves/shapes/kernels.lean
- \- *lemma* category_theory.limits.preserves_cokernel.iso_hom
- \+ *lemma* category_theory.limits.preserves_cokernel.iso_inv

Added src/category_theory/limits/shapes/functor_category.lean


Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.cokernel.map_iso
- \+ *def* category_theory.limits.kernel.map_iso



## [2022-04-25 17:22:44](https://github.com/leanprover-community/mathlib/commit/43e84cd)
feat(data/fin/succ_pred): `fin` is an archimedean succ/pred order ([#12792](https://github.com/leanprover-community/mathlib/pull/12792))
#### Estimated changes
Modified src/algebra/big_operators/fin.lean


Modified src/data/fin/basic.lean
- \+ *lemma* fin.coe_fin_one
- \+ *lemma* fin.coe_neg_one
- \+ *lemma* fin.coe_sub_one
- \+ *def* order_iso.fin_equiv
- \+ *lemma* order_iso.fin_equiv_apply
- \+ *lemma* order_iso.fin_equiv_symm_apply

Added src/data/fin/succ_pred.lean
- \+ *lemma* fin.pred_apply
- \+ *lemma* fin.pred_eq
- \+ *lemma* fin.succ_apply
- \+ *lemma* fin.succ_eq

Modified src/data/fintype/basic.lean
- \- *lemma* fintype.linear_order.is_well_order
- \+ *lemma* fintype.linear_order.is_well_order_gt
- \+ *lemma* fintype.linear_order.is_well_order_lt
- \- *lemma* fintype.preorder.well_founded
- \+ *lemma* fintype.preorder.well_founded_gt
- \+ *lemma* fintype.preorder.well_founded_lt

Modified src/order/rel_classes.lean


Modified src/order/succ_pred/basic.lean
- \+ *def* pred_order.of_core
- \+ *def* succ_order.of_core

Modified src/set_theory/ordinal/basic.lean




## [2022-04-25 15:23:31](https://github.com/leanprover-community/mathlib/commit/4481a56)
feat(algebra/group_power/order): Add sq_zero_iff ([#13670](https://github.com/leanprover-community/mathlib/pull/13670))
Tiny lemma that seems to be missing.
Should this be a simp lemma?
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *theorem* sq_eq_zero_iff



## [2022-04-25 15:23:30](https://github.com/leanprover-community/mathlib/commit/e2f5696)
feat(analysis/normed_space/exponential): add `pi.exp_apply` ([#13488](https://github.com/leanprover-community/mathlib/pull/13488))
The statement is a bit weird, but this structure is useful because it allows us to push `exp` through `matrix.diagonal` and into its elements.
#### Estimated changes
Modified src/analysis/normed_space/exponential.lean
- \+ *lemma* function.update_exp
- \+ *lemma* pi.exp_apply
- \+ *lemma* pi.exp_def



## [2022-04-25 15:23:29](https://github.com/leanprover-community/mathlib/commit/85075bc)
refactor(category_theory/monoidal): rearrange simp lemmas to work better with coherence ([#13409](https://github.com/leanprover-community/mathlib/pull/13409))
Change the direction of some simp lemma for monoidal categories, and remove some unused lemmas.
This PR is effectively a "no-op": no substantial changes to proofs. However, it should enable making `coherence` more powerful soon (following suggestions of @yuma-mizuno)!
#### Estimated changes
Modified src/category_theory/monoidal/End.lean


Modified src/category_theory/monoidal/Mon_.lean


Modified src/category_theory/monoidal/braided.lean


Modified src/category_theory/monoidal/category.lean
- \- *lemma* category_theory.monoidal_category.left_unitor_inv_comp_tensor
- \- *lemma* category_theory.monoidal_category.right_unitor_inv_comp_tensor
- \+/\- *lemma* category_theory.monoidal_category.tensor_left_iff
- \+/\- *lemma* category_theory.monoidal_category.tensor_right_iff
- \- *lemma* category_theory.monoidal_category.triangle_assoc_comp_left

Modified src/category_theory/monoidal/center.lean


Modified src/category_theory/monoidal/free/coherence.lean


Modified src/category_theory/monoidal/opposite.lean


Modified src/category_theory/monoidal/transport.lean




## [2022-04-25 15:23:28](https://github.com/leanprover-community/mathlib/commit/9f75d75)
feat(analysis/convex/measure): a convex set is null-measurable ([#13138](https://github.com/leanprover-community/mathlib/pull/13138))
#### Estimated changes
Added src/analysis/convex/measure.lean
- \+ *lemma* convex.add_haar_frontier

Modified src/analysis/convex/topology.lean
- \+ *lemma* convex.closure_subset_image_homothety_interior_of_one_lt

Modified src/data/set/basic.lean
- \+ *theorem* subtype.preimage_coe_inter_self

Modified src/topology/continuous_on.lean
- \+ *lemma* frontier_inter_open_inter



## [2022-04-25 15:23:27](https://github.com/leanprover-community/mathlib/commit/2c15ce1)
feat(data/nat/choose): add facts about the multiplicity of primes in the factorisation of central binomial coefficients ([#9925](https://github.com/leanprover-community/mathlib/pull/9925))
A number of bounds on the multiplicity of primes in the factorisation of central binomial coefficients. These are of interest because they form part of the proof of Bertrand's postulate.
#### Estimated changes
Modified src/data/nat/choose/central.lean
- \+ *lemma* nat.padic_val_nat_central_binom_le
- \+ *lemma* nat.padic_val_nat_central_binom_of_large_eq_zero
- \+ *lemma* nat.padic_val_nat_central_binom_of_large_le_one



## [2022-04-25 13:21:34](https://github.com/leanprover-community/mathlib/commit/2825f35)
feat(data/set/prod): add `set.eval_image_pi_subset` ([#13613](https://github.com/leanprover-community/mathlib/pull/13613))
Also reorder lemmas like `fst_image_prod_subset` so that simpler
lemmas go first.
#### Estimated changes
Modified src/data/set/prod.lean
- \+ *lemma* set.eval_image_pi_subset
- \+ *lemma* set.eval_image_univ_pi_subset



## [2022-04-25 13:21:32](https://github.com/leanprover-community/mathlib/commit/14b0e32)
chore(data/finsupp/fin): golf some proofs ([#13607](https://github.com/leanprover-community/mathlib/pull/13607))
#### Estimated changes
Modified src/data/finsupp/fin.lean




## [2022-04-25 13:21:31](https://github.com/leanprover-community/mathlib/commit/b7538a3)
feat(algebra/periodic): add lemmas `periodic.prod`, `periodic.smul`, `antiperiodic.smul` ([#13496](https://github.com/leanprover-community/mathlib/pull/13496))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/algebra/periodic.lean
- \+ *lemma* finset.periodic_prod
- \+ *lemma* function.antiperiodic.smul
- \+ *lemma* function.periodic.smul
- \+ *lemma* list.periodic_prod
- \+ *lemma* multiset.periodic_prod



## [2022-04-25 11:19:25](https://github.com/leanprover-community/mathlib/commit/4bfae3d)
feat(set_theory/game/pgame): remove nolint ([#13680](https://github.com/leanprover-community/mathlib/pull/13680))
We remove `@[nolint has_inhabited_instance]` from `left_moves` and `right_moves` by providing the appropriate instances for `star`.
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+/\- *def* pgame.left_moves
- \+/\- *def* pgame.right_moves



## [2022-04-25 11:19:24](https://github.com/leanprover-community/mathlib/commit/9e8d107)
feat(dynamics/periodic_pts): `pow_smul_eq_iff_minimal_period_dvd` ([#13676](https://github.com/leanprover-community/mathlib/pull/13676))
This PR adds a lemma `pow_smul_eq_iff_minimal_period_dvd`, along with additive and integer versions.
#### Estimated changes
Modified src/dynamics/periodic_pts.lean
- \+ *lemma* mul_action.pow_smul_eq_iff_minimal_period_dvd
- \+ *lemma* mul_action.zpow_smul_eq_iff_minimal_period_dvd



## [2022-04-25 11:19:22](https://github.com/leanprover-community/mathlib/commit/7231172)
feat(topology/algebra): actions on the opposite type are continuous ([#13671](https://github.com/leanprover-community/mathlib/pull/13671))
This also adds the missing `t2_space` instance.
#### Estimated changes
Modified src/topology/algebra/const_mul_action.lean


Modified src/topology/algebra/constructions.lean


Modified src/topology/algebra/mul_action.lean


Modified src/topology/algebra/uniform_mul_action.lean
- \+/\- *lemma* uniform_continuous.const_smul



## [2022-04-25 11:19:21](https://github.com/leanprover-community/mathlib/commit/ed10ba2)
feat(ring_theory/witt_vector/frobenius): add `witt_vector.frobenius_equiv` ([#13666](https://github.com/leanprover-community/mathlib/pull/13666))
This promotes the bijection to an equivalence with an explicit inverse
#### Estimated changes
Modified src/ring_theory/witt_vector/frobenius.lean
- \+ *def* witt_vector.frobenius_equiv

Modified src/ring_theory/witt_vector/frobenius_fraction_field.lean


Modified src/ring_theory/witt_vector/isocrystal.lean
- \+/\- *def* witt_vector.fraction_ring.frobenius



## [2022-04-25 11:19:20](https://github.com/leanprover-community/mathlib/commit/6d3ca07)
feat(data/zmod/basic): `-1 : zmod n` lifts to `n - 1` ([#13665](https://github.com/leanprover-community/mathlib/pull/13665))
This PR adds a lemma stating that `-1 : zmod n` lifts to `n - 1 : R` for any ring `R`. The proof is surprisingly painful, but maybe someone can find a nicer way?
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.cast_neg_one
- \+ *lemma* zmod.val_neg_one



## [2022-04-25 11:19:19](https://github.com/leanprover-community/mathlib/commit/ad0a3e6)
feat(dynamics/periodic_pts): Iteration is injective below the period ([#13660](https://github.com/leanprover-community/mathlib/pull/13660))
This PR adds `iterate_injective_of_lt_minimal_period`, generalizing `pow_injective_of_lt_order_of`.
#### Estimated changes
Modified src/dynamics/periodic_pts.lean
- \+ *lemma* function.iterate_injective_of_lt_minimal_period
- \+ *lemma* function.iterate_minimal_period

Modified src/group_theory/order_of_element.lean
- \- *lemma* pow_injective_aux



## [2022-04-25 10:43:44](https://github.com/leanprover-community/mathlib/commit/6710d65)
feat(analysis/complex/roots_of_unity): arg of a primitive root ([#13583](https://github.com/leanprover-community/mathlib/pull/13583))
#### Estimated changes
Modified src/analysis/complex/roots_of_unity.lean
- \+ *lemma* is_primitive_root.arg



## [2022-04-25 08:04:59](https://github.com/leanprover-community/mathlib/commit/b35ed40)
feat(algebra/order/hom/ring): There's at most one hom between linear ordered fields ([#13601](https://github.com/leanprover-community/mathlib/pull/13601))
There is at most one ring homomorphism from a linear ordered field to an archimedean linear ordered field. Also generalize `map_rat_cast` to take in `ring_hom_class`.
#### Estimated changes
Modified src/algebra/order/hom/ring.lean
- \+ *lemma* order_ring_hom.subsingleton
- \+ *lemma* order_ring_iso.subsingleton_left
- \+ *lemma* order_ring_iso.subsingleton_right
- \+ *lemma* order_ring_iso.symm_bijective
- \+ *lemma* order_ring_iso.to_order_ring_hom_injective

Modified src/algebra/star/basic.lean


Modified src/data/complex/basic.lean
- \+/\- *theorem* complex.of_real_rat_cast

Modified src/data/complex/is_R_or_C.lean


Modified src/data/rat/cast.lean
- \+ *lemma* map_rat_cast
- \- *lemma* ring_hom.map_rat_cast

Modified src/ring_theory/algebraic.lean




## [2022-04-25 08:04:57](https://github.com/leanprover-community/mathlib/commit/d795ea4)
feat(number_theory/legendre_symbol/quadratic_reciprocity): Alternate forms of `exists_sq_eq_neg_one` ([#13594](https://github.com/leanprover-community/mathlib/pull/13594))
Also, renamed `exists_sq_eq_neg_one_iff_mod_four_ne_three` to `exists_sq_eq_neg_one` for consistency with `exists_sq_eq_two` and for convenience.
#### Estimated changes
Modified archive/imo/imo2008_q3.lean


Modified src/number_theory/legendre_symbol/quadratic_reciprocity.lean
- \+ *lemma* zmod.exists_sq_eq_neg_one_iff
- \- *lemma* zmod.exists_sq_eq_neg_one_iff_mod_four_ne_three
- \+ *lemma* zmod.mod_four_ne_three_of_sq_eq_neg_one
- \+ *lemma* zmod.mod_four_ne_three_of_sq_eq_neg_sq'
- \+ *lemma* zmod.mod_four_ne_three_of_sq_eq_neg_sq

Modified src/number_theory/zsqrtd/gaussian_int.lean




## [2022-04-25 08:04:56](https://github.com/leanprover-community/mathlib/commit/e251ef7)
feat(logic/basic): `congr_fun` for heterogeneous equality ([#13591](https://github.com/leanprover-community/mathlib/pull/13591))
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* congr_fun_heq



## [2022-04-25 08:04:55](https://github.com/leanprover-community/mathlib/commit/e059fdf)
feat(algebra/big_operators/basic): mk0_prod ([#13582](https://github.com/leanprover-community/mathlib/pull/13582))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* units.mk0_prod



## [2022-04-25 08:04:54](https://github.com/leanprover-community/mathlib/commit/f02c784)
feat(special_functions/gamma): recurrence relation for Gamma function ([#13156](https://github.com/leanprover-community/mathlib/pull/13156))
#### Estimated changes
Modified src/analysis/special_functions/gamma.lean
- \+ *def* complex.Gamma
- \+ *theorem* complex.Gamma_add_one
- \+ *lemma* complex.Gamma_aux_recurrence1
- \+ *lemma* complex.Gamma_aux_recurrence2
- \+ *lemma* complex.Gamma_eq_Gamma_aux
- \+ *theorem* complex.Gamma_eq_integral
- \+/\- *def* complex.Gamma_integral
- \+ *theorem* complex.Gamma_integral_add_one
- \+ *theorem* complex.Gamma_nat_eq_factorial
- \+ *def* complex.partial_Gamma
- \+ *lemma* complex.partial_Gamma_add_one
- \+ *lemma* complex.tendsto_partial_Gamma



## [2022-04-25 06:24:12](https://github.com/leanprover-community/mathlib/commit/ef3769d)
feat(group_theory/subgroup/basic): Cyclic subgroups are commutative ([#13663](https://github.com/leanprover-community/mathlib/pull/13663))
This PR adds an instance stating that the cyclic subgroups `zpowers g` are commutative.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean




## [2022-04-25 06:24:11](https://github.com/leanprover-community/mathlib/commit/b0fe3cd)
feat(order/filter): add `filter.coprod_bot` etc ([#13662](https://github.com/leanprover-community/mathlib/pull/13662))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.bot_coprod
- \+ *lemma* filter.bot_coprod_bot
- \+ *lemma* filter.coprod_bot

Modified src/order/filter/pi.lean
- \+ *lemma* filter.Coprod_bot'
- \+ *lemma* filter.Coprod_bot
- \+ *lemma* filter.Coprod_eq_bot_iff'
- \+ *lemma* filter.Coprod_eq_bot_iff



## [2022-04-25 06:24:10](https://github.com/leanprover-community/mathlib/commit/feb9aed)
feat(group_theory/group_action/basic): More API for `quotient_action` ([#13661](https://github.com/leanprover-community/mathlib/pull/13661))
This PR adds a couple more API lemmas for `quotient_action`.
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \+ *lemma* mul_action.quotient.coe_smul_out'
- \+ *lemma* mul_action.quotient.mk_smul_out'
- \+/\- *lemma* mul_action.quotient.smul_coe
- \+/\- *lemma* mul_action.quotient.smul_mk



## [2022-04-25 06:24:09](https://github.com/leanprover-community/mathlib/commit/46563c5)
refactor(analysis/convex/basic): rewrite a few proofs ([#13658](https://github.com/leanprover-community/mathlib/pull/13658))
* prove that a closed segment is the union of the corresponding open segment and the endpoints;
* use this lemma to golf some proofs;
* make the "field" argument of `mem_open_segment_of_ne_left_right` implicit.
* use section variables.
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* insert_endpoints_open_segment
- \+/\- *lemma* mem_open_segment_iff_div
- \+/\- *lemma* mem_open_segment_of_ne_left_right
- \+/\- *lemma* mem_segment_iff_div
- \+/\- *lemma* mem_segment_iff_same_ray
- \+/\- *lemma* open_segment_subset_iff_segment_subset

Modified src/analysis/convex/extreme.lean




## [2022-04-25 06:24:07](https://github.com/leanprover-community/mathlib/commit/7d64215)
chore(analysis/convex/topology): generalize a few lemmas ([#13656](https://github.com/leanprover-community/mathlib/pull/13656))
This way they work for `𝕜 = ℚ` too.
#### Estimated changes
Modified src/analysis/convex/topology.lean
- \+/\- *lemma* convex.add_smul_mem_interior'
- \+/\- *lemma* convex.add_smul_mem_interior
- \+/\- *lemma* convex.add_smul_sub_mem_interior'
- \+/\- *lemma* convex.add_smul_sub_mem_interior
- \+/\- *lemma* convex.combo_closure_interior_mem_interior
- \+/\- *lemma* convex.combo_closure_interior_subset_interior
- \+/\- *lemma* convex.combo_interior_closure_mem_interior
- \+/\- *lemma* convex.combo_interior_closure_subset_interior
- \+/\- *lemma* convex.combo_interior_self_mem_interior
- \+/\- *lemma* convex.combo_interior_self_subset_interior
- \+/\- *lemma* convex.combo_self_interior_mem_interior
- \+/\- *lemma* convex.combo_self_interior_subset_interior
- \+/\- *lemma* convex.open_segment_closure_interior_subset_interior
- \+/\- *lemma* convex.open_segment_interior_closure_subset_interior
- \+/\- *lemma* convex.open_segment_interior_self_subset_interior
- \+/\- *lemma* convex.open_segment_self_interior_subset_interior



## [2022-04-25 06:24:04](https://github.com/leanprover-community/mathlib/commit/c24f1f2)
chore(number_theory/padics/*): tidy some proofs ([#13652](https://github.com/leanprover-community/mathlib/pull/13652))
#### Estimated changes
Modified src/number_theory/padics/padic_norm.lean


Modified src/number_theory/padics/padic_numbers.lean




## [2022-04-25 06:24:00](https://github.com/leanprover-community/mathlib/commit/962bfcd)
chore(field_theory/finite/polynomial): tidy + remove nolints ([#13645](https://github.com/leanprover-community/mathlib/pull/13645))
Some of these definitions only make full sense over a field (for example the indicator function can be nonsensical in non-field rings) but there's also no reason not to define them more generally. This removes all `nolint`s related to this file, and all of the generalisation linter suggestions too.
#### Estimated changes
Modified src/field_theory/finite/polynomial.lean
- \+/\- *def* mv_polynomial.R
- \+/\- *lemma* mv_polynomial.dim_R
- \+/\- *lemma* mv_polynomial.eq_zero_of_eval_eq_zero
- \+/\- *def* mv_polynomial.evalᵢ
- \+/\- *def* mv_polynomial.evalₗ
- \- *lemma* mv_polynomial.evalₗ_apply
- \+/\- *lemma* mv_polynomial.expand_zmod
- \+/\- *lemma* mv_polynomial.finrank_R
- \+/\- *lemma* mv_polynomial.frobenius_zmod
- \+/\- *def* mv_polynomial.indicator
- \+/\- *lemma* mv_polynomial.ker_evalₗ
- \+/\- *lemma* mv_polynomial.range_evalᵢ



## [2022-04-25 06:24:00](https://github.com/leanprover-community/mathlib/commit/b6a4be4)
chore(ring_theory/witt_vector/isocrystal): speed up the proof ([#13644](https://github.com/leanprover-community/mathlib/pull/13644))
to remove a timeout in [#13459](https://github.com/leanprover-community/mathlib/pull/13459)
#### Estimated changes
Modified src/ring_theory/witt_vector/isocrystal.lean




## [2022-04-25 06:23:59](https://github.com/leanprover-community/mathlib/commit/9c861e3)
feat(topology/algebra/matrix): `matrix.block_diagonal` is continuous ([#13641](https://github.com/leanprover-community/mathlib/pull/13641))
`continuous.if_const` isn't suitable for the primed `matrix.block_diagonal'` case, as the `if` is dependent.
#### Estimated changes
Modified src/topology/algebra/matrix.lean
- \+ *lemma* continuous.matrix_block_diagonal'
- \+ *lemma* continuous.matrix_block_diagonal
- \+ *lemma* continuous.matrix_from_blocks



## [2022-04-25 06:23:58](https://github.com/leanprover-community/mathlib/commit/b1b2cab)
feat(group_theory/complement): The range of a section `G ⧸ H → G` is a transversal ([#13623](https://github.com/leanprover-community/mathlib/pull/13623))
This PR adds left and right versions of the statement that the range of a section `G ⧸ H → G` is a transversal.
#### Estimated changes
Modified src/group_theory/complement.lean
- \+ *lemma* subgroup.range_mem_left_transversals
- \+ *lemma* subgroup.range_mem_right_transversals



## [2022-04-25 06:23:57](https://github.com/leanprover-community/mathlib/commit/6cbf986)
refactor(group_theory/schur_zassenhaus): Golf proof of abelian case ([#13622](https://github.com/leanprover-community/mathlib/pull/13622))
This PR golfs the proof of the abelian case of Schur-Zassenhaus by switching from a nonstandard definition of the difference of two left transversals to the definition used in `transfer.lean`.
#### Estimated changes
Modified src/group_theory/schur_zassenhaus.lean
- \- *lemma* subgroup.diff_inv
- \- *lemma* subgroup.diff_mul_diff
- \- *lemma* subgroup.diff_self
- \+ *lemma* subgroup.eq_one_of_smul_eq_one
- \+/\- *lemma* subgroup.exists_smul_eq
- \+/\- *lemma* subgroup.is_complement'_stabilizer_of_coprime
- \+/\- *def* subgroup.quotient_diff
- \+ *lemma* subgroup.smul_diff'
- \- *lemma* subgroup.smul_diff
- \+ *lemma* subgroup.smul_diff_smul'
- \- *lemma* subgroup.smul_diff_smul
- \- *lemma* subgroup.smul_left_injective



## [2022-04-25 06:23:56](https://github.com/leanprover-community/mathlib/commit/b6c8c0d)
refactor(linear_algebra/quotient): Use the same quotient relation as add_subgroup ([#13620](https://github.com/leanprover-community/mathlib/pull/13620))
This means that the quotient by `p` and `p.to_add_subgroup` are defeq as types, and the instances defined on them are defeq too.
This removes a TODO comment by Mario; I can only assume it resolves it in the right direction
#### Estimated changes
Modified src/algebra/char_p/quotient.lean


Modified src/algebra/lie/quotient.lean


Modified src/algebra/module/torsion.lean


Modified src/algebra/ring_quot.lean


Modified src/linear_algebra/invariant_basis_number.lean


Modified src/linear_algebra/quotient.lean
- \+ *lemma* submodule.quotient_rel_r_def

Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/ideal/quotient.lean


Modified src/ring_theory/valuation/basic.lean


Modified src/topology/algebra/uniform_ring.lean




## [2022-04-25 06:23:55](https://github.com/leanprover-community/mathlib/commit/91b8084)
chore(analysis/normed_space/finite_dimension): extract some lemmas from existentials ([#13600](https://github.com/leanprover-community/mathlib/pull/13600))
A few proofs in this file prove an existential where a stronger statement in terms of the witness exists.
This:
* Removes `basis.sup_norm_le_norm` and replaces it with the more general statement `pi.sum_norm_apply_le_norm`
* Renames `basis.op_norm_le` to `basis.exists_op_norm_le`
* Creates a new `basis.op_norm_le` stated without the existential
* Adds the `nnnorm` version of some `norm` lemmas. In some cases it's easier to prove these first, and derive the `norm` versions from them.
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *lemma* pi.sum_nnnorm_apply_le_nnnorm
- \+ *lemma* pi.sum_norm_apply_le_norm

Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* basis.exists_op_nnnorm_le
- \+ *lemma* basis.exists_op_norm_le
- \+ *lemma* basis.op_nnnorm_le
- \+/\- *lemma* basis.op_norm_le
- \- *lemma* basis.sup_norm_le_norm

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.op_nnnorm_eq_of_bounds
- \+ *lemma* continuous_linear_map.op_nnnorm_le_bound
- \+ *theorem* continuous_linear_map.op_nnnorm_le_of_lipschitz
- \+ *lemma* continuous_linear_map.op_nnnorm_prod



## [2022-04-25 05:10:33](https://github.com/leanprover-community/mathlib/commit/070c21b)
chore(data/matrix): generalisation linter ([#13655](https://github.com/leanprover-community/mathlib/pull/13655))
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *lemma* matrix.col_mul_vec
- \+/\- *lemma* matrix.col_vec_mul
- \+/\- *lemma* matrix.conj_transpose_mul
- \+/\- *lemma* matrix.conj_transpose_neg
- \+/\- *lemma* matrix.conj_transpose_smul
- \+/\- *lemma* matrix.conj_transpose_zero
- \+/\- *lemma* matrix.diagonal_conj_transpose
- \+/\- *lemma* matrix.dot_product_comm
- \+/\- *lemma* matrix.minor_mul
- \+/\- *lemma* matrix.minor_mul_equiv
- \+/\- *lemma* matrix.minor_mul_transpose_minor
- \+/\- *lemma* matrix.minor_smul
- \+/\- *lemma* matrix.minor_zero
- \+/\- *lemma* matrix.mul_minor_one
- \+/\- *lemma* matrix.mul_vec_smul
- \+/\- *lemma* matrix.one_minor_mul
- \+/\- *lemma* matrix.row_mul_vec
- \+/\- *lemma* matrix.row_vec_mul
- \+/\- *lemma* matrix.star_mul
- \+/\- *lemma* matrix.transpose_mul
- \+/\- *def* matrix.transpose_ring_equiv
- \+/\- *lemma* matrix.vec_mul_smul
- \+/\- *lemma* matrix.vec_mul_vec_eq
- \+/\- *lemma* ring_hom.map_dot_product
- \+/\- *lemma* ring_hom.map_mul_vec
- \+/\- *lemma* ring_hom.map_vec_mul



## [2022-04-25 04:29:05](https://github.com/leanprover-community/mathlib/commit/df4066c)
refactor(order/ideal): Make `order.ideal` extend `lower_set` ([#13070](https://github.com/leanprover-community/mathlib/pull/13070))
* Redefine `order.ideal` to extend `lower_set`.
* `set_like` instance
* Get rid of `order.ideal.ideal_Inter_nonempty` in favor of `order_bot`
* Make arguments to `order.ideal.sup_mem` semi-implicit
* Reorder sections according to typeclass assumptions (some were outdated since Yakov's `order_bot`/`order_top` refactor)
#### Estimated changes
Modified src/order/ideal.lean
- \- *lemma* order.ideal.Inf_le
- \- *lemma* order.ideal.Inter_nonempty
- \+/\- *lemma* order.ideal.bot_mem
- \+ *lemma* order.ideal.carrier_eq_coe
- \+/\- *lemma* order.ideal.coe_Inf
- \+ *lemma* order.ideal.coe_inf
- \- *lemma* order.ideal.coe_inj
- \- *lemma* order.ideal.coe_injective
- \+ *lemma* order.ideal.coe_ssubset_coe
- \+ *lemma* order.ideal.coe_subset_coe
- \+ *lemma* order.ideal.coe_sup
- \+ *lemma* order.ideal.coe_to_lower_set
- \+/\- *lemma* order.ideal.coe_top
- \+/\- *lemma* order.ideal.ext
- \- *lemma* order.ideal.ext_iff
- \- *lemma* order.ideal.ideal_Inter_nonempty.all_Inter_nonempty
- \- *lemma* order.ideal.ideal_Inter_nonempty.all_bInter_nonempty
- \- *lemma* order.ideal.ideal_Inter_nonempty.exists_all_mem
- \- *lemma* order.ideal.ideal_Inter_nonempty_iff
- \- *lemma* order.ideal.ideal_Inter_nonempty_of_exists_all_mem
- \- *lemma* order.ideal.is_glb_Inf
- \+/\- *lemma* order.ideal.is_proper.ne_top
- \- *lemma* order.ideal.le_Inf
- \+/\- *lemma* order.ideal.mem_Inf
- \- *lemma* order.ideal.mem_coe
- \+/\- *lemma* order.ideal.mem_compl_of_ge
- \+/\- *def* order.ideal.principal
- \+ *lemma* order.ideal.principal_bot
- \+ *lemma* order.ideal.principal_top
- \+/\- *lemma* order.ideal.sup_mem
- \+ *lemma* order.ideal.to_lower_set_injective
- \+/\- *lemma* order.ideal.top_of_top_mem
- \+ *lemma* order.ideal.top_to_lower_set

Modified src/order/pfilter.lean
- \+/\- *lemma* order.pfilter.ext
- \+/\- *lemma* order.pfilter.inf_mem
- \+/\- *lemma* order.pfilter.mem_of_le
- \+/\- *lemma* order.pfilter.top_mem

Modified src/order/prime_ideal.lean




## [2022-04-25 03:54:20](https://github.com/leanprover-community/mathlib/commit/d4d5b6d)
chore(scripts): update nolints.txt ([#13679](https://github.com/leanprover-community/mathlib/pull/13679))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2022-04-25 03:54:18](https://github.com/leanprover-community/mathlib/commit/65edf25)
feat(set_theory/game/pgame): `x.move_left i < x` and variants  ([#13654](https://github.com/leanprover-community/mathlib/pull/13654))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.lt_mk
- \+ *theorem* pgame.lt_move_right
- \+ *theorem* pgame.mk_lt
- \+ *theorem* pgame.move_left_lt

Modified src/set_theory/surreal/basic.lean
- \- *theorem* pgame.numeric.lt_move_right
- \- *theorem* pgame.numeric.move_left_lt

Modified src/set_theory/surreal/dyadic.lean




## [2022-04-25 01:54:43](https://github.com/leanprover-community/mathlib/commit/454b884)
chore(topology/metric_space/basic): golf an instance ([#13664](https://github.com/leanprover-community/mathlib/pull/13664))
Golf the proof of `prod.pseudo_metric_space_max` using
`pseudo_emetric_space.to_pseudo_metric_space_of_dist`.
#### Estimated changes
Modified src/topology/metric_space/basic.lean




## [2022-04-25 01:54:42](https://github.com/leanprover-community/mathlib/commit/9101c48)
docs(number_theory/sum_two_squares): Update docs ([#13593](https://github.com/leanprover-community/mathlib/pull/13593))
We add a remark for an alternate name for the theorem, and a todo note for a generalization of it.
#### Estimated changes
Modified src/number_theory/sum_two_squares.lean
- \+/\- *lemma* nat.prime.sq_add_sq



## [2022-04-25 01:54:41](https://github.com/leanprover-community/mathlib/commit/045fc44)
docs(tactic/algebra): Module docstring ([#13571](https://github.com/leanprover-community/mathlib/pull/13571))
Write the module docstring.
#### Estimated changes
Modified src/tactic/algebra.lean




## [2022-04-25 00:39:20](https://github.com/leanprover-community/mathlib/commit/54d1ddd)
feat(algebra/polynomial/big_operators): add a lemma, reduce assumptions, golf ([#13264](https://github.com/leanprover-community/mathlib/pull/13264))
#### Estimated changes
Modified src/algebra/polynomial/big_operators.lean
- \+ *lemma* polynomial.degree_list_prod
- \+/\- *lemma* polynomial.nat_degree_multiset_prod

Modified src/data/polynomial/degree/definitions.lean




## [2022-04-24 20:37:26](https://github.com/leanprover-community/mathlib/commit/0d16bb4)
refactor(*): migrate from `filter.lift' _ powerset` to `filter.small_sets` ([#13673](https://github.com/leanprover-community/mathlib/pull/13673))
#### Estimated changes
Modified src/analysis/special_functions/non_integrable.lean


Modified src/measure_theory/integral/integrable_on.lean


Modified src/measure_theory/integral/set_integral.lean


Modified src/measure_theory/measurable_space.lean
- \- *lemma* filter.eventually.exists_measurable_mem_of_lift'
- \+ *lemma* filter.eventually.exists_measurable_mem_of_small_sets

Modified src/measure_theory/measure/measure_space.lean


Modified src/order/filter/interval.lean


Modified src/order/filter/lift.lean
- \- *lemma* filter.eventually_lift'_powerset'
- \- *lemma* filter.eventually_lift'_powerset
- \- *lemma* filter.eventually_lift'_powerset_eventually
- \- *lemma* filter.eventually_lift'_powerset_forall
- \- *lemma* filter.lift'_inf_powerset
- \- *lemma* filter.lift'_infi_powerset
- \- *lemma* filter.tendsto_lift'_powerset_mono

Modified src/order/filter/small_sets.lean
- \+ *lemma* filter.comap_small_sets
- \+ *lemma* filter.eventually_small_sets'
- \+ *lemma* filter.eventually_small_sets
- \+ *lemma* filter.eventually_small_sets_eventually
- \+ *lemma* filter.eventually_small_sets_forall
- \+/\- *lemma* filter.has_basis.small_sets
- \+/\- *lemma* filter.has_basis_small_sets
- \+ *lemma* filter.monotone_small_sets
- \+/\- *def* filter.small_sets
- \+ *lemma* filter.small_sets_bot
- \+ *lemma* filter.small_sets_comap
- \+ *lemma* filter.small_sets_inf
- \+ *lemma* filter.small_sets_infi
- \+ *lemma* filter.small_sets_principal
- \+ *lemma* filter.small_sets_top
- \+ *lemma* filter.tendsto.small_sets_mono
- \+/\- *lemma* filter.tendsto_small_sets_iff

Modified src/topology/algebra/order/basic.lean


Modified src/topology/metric_space/hausdorff_dimension.lean
- \+/\- *lemma* bsupr_limsup_dimH
- \+/\- *lemma* supr_limsup_dimH



## [2022-04-24 17:23:52](https://github.com/leanprover-community/mathlib/commit/53a484e)
chore(order/filter/small_sets): redefine, golf ([#13672](https://github.com/leanprover-community/mathlib/pull/13672))
The new definition is defeq to the old one.
#### Estimated changes
Modified src/order/filter/small_sets.lean
- \+/\- *def* filter.small_sets



## [2022-04-24 13:05:30](https://github.com/leanprover-community/mathlib/commit/42b9cdf)
feat(data/quot): Decidability of `quotient.lift` and friends ([#13589](https://github.com/leanprover-community/mathlib/pull/13589))
and make `antisymmetrization.linear_order` computable.
#### Estimated changes
Modified src/data/quot.lean


Modified src/order/antisymmetrization.lean




## [2022-04-24 11:06:15](https://github.com/leanprover-community/mathlib/commit/63da426)
refactor(linear_algebra/dimension): further generalisations to division_ring ([#13657](https://github.com/leanprover-community/mathlib/pull/13657))
#### Estimated changes
Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* rank_zero



## [2022-04-24 08:21:40](https://github.com/leanprover-community/mathlib/commit/8126255)
feat(set_theory/surreal/basic): Definitional characterization of `numeric` ([#13653](https://github.com/leanprover-community/mathlib/pull/13653))
#### Estimated changes
Modified src/set_theory/surreal/basic.lean
- \+ *lemma* pgame.numeric_def



## [2022-04-24 06:52:55](https://github.com/leanprover-community/mathlib/commit/e006f38)
feat(algebra/hom/iterate): Iterating an action ([#13659](https://github.com/leanprover-community/mathlib/pull/13659))
This PR adds `smul_iterate`, generalizing  `mul_left_iterate` and `mul_right_iterate`.
#### Estimated changes
Modified src/algebra/hom/iterate.lean
- \+ *lemma* smul_iterate



## [2022-04-24 04:20:58](https://github.com/leanprover-community/mathlib/commit/b8b8bf3)
refactor(category_theory/monoidal): prove coherence lemmas by coherence ([#13406](https://github.com/leanprover-community/mathlib/pull/13406))
Now that we have a basic monoidal coherence tactic, we can replace some boring proofs of particular coherence lemmas with `by coherence`.
I've also simply deleted a few lemmas which are not actually used elsewhere in mathlib, and can be proved `by coherence`.
#### Estimated changes
Modified src/category_theory/monoidal/Mon_.lean


Modified src/category_theory/monoidal/braided.lean


Modified src/category_theory/monoidal/category.lean
- \- *lemma* category_theory.monoidal_category.id_tensor_right_unitor_inv
- \- *lemma* category_theory.monoidal_category.left_unitor_inv_tensor_id
- \- *lemma* category_theory.monoidal_category.left_unitor_tensor'
- \- *lemma* category_theory.monoidal_category.left_unitor_tensor
- \- *lemma* category_theory.monoidal_category.left_unitor_tensor_inv'
- \- *lemma* category_theory.monoidal_category.left_unitor_tensor_inv
- \- *lemma* category_theory.monoidal_category.pentagon_comp_id_tensor
- \- *lemma* category_theory.monoidal_category.pentagon_hom_inv
- \- *lemma* category_theory.monoidal_category.pentagon_inv_hom
- \- *lemma* category_theory.monoidal_category.pentagon_inv_inv_hom
- \- *lemma* category_theory.monoidal_category.triangle_assoc_comp_right_inv
- \- *lemma* category_theory.monoidal_category.unitors_equal
- \- *lemma* category_theory.monoidal_category.unitors_inv_equal

Added src/category_theory/monoidal/coherence_lemmas.lean
- \+ *lemma* category_theory.monoidal_category.id_tensor_right_unitor_inv
- \+ *lemma* category_theory.monoidal_category.left_unitor_inv_tensor_id
- \+ *lemma* category_theory.monoidal_category.left_unitor_tensor'
- \+ *lemma* category_theory.monoidal_category.left_unitor_tensor
- \+ *lemma* category_theory.monoidal_category.left_unitor_tensor_inv
- \+ *lemma* category_theory.monoidal_category.pentagon_hom_inv
- \+ *lemma* category_theory.monoidal_category.pentagon_inv_hom
- \+ *lemma* category_theory.monoidal_category.pentagon_inv_inv_hom
- \+ *lemma* category_theory.monoidal_category.triangle_assoc_comp_right_inv
- \+ *lemma* category_theory.monoidal_category.unitors_equal
- \+ *lemma* category_theory.monoidal_category.unitors_inv_equal

Modified src/category_theory/monoidal/rigid.lean




## [2022-04-24 02:22:31](https://github.com/leanprover-community/mathlib/commit/92ca136)
feat(set_theory/game/pgame): Birthdays of pre-games ([#13636](https://github.com/leanprover-community/mathlib/pull/13636))
#### Estimated changes
Added src/set_theory/game/birthday.lean
- \+ *theorem* pgame.birthday_def
- \+ *theorem* pgame.birthday_move_left_lt
- \+ *theorem* pgame.birthday_move_right_lt
- \+ *theorem* pgame.birthday_zero
- \+ *theorem* pgame.lt_birthday_iff
- \+ *theorem* pgame.relabelling.birthday_congr



## [2022-04-24 02:22:30](https://github.com/leanprover-community/mathlib/commit/5998b49)
chore(order/filter/basic): golf 2 proofs ([#13614](https://github.com/leanprover-community/mathlib/pull/13614))
#### Estimated changes
Modified src/order/filter/basic.lean




## [2022-04-24 02:22:28](https://github.com/leanprover-community/mathlib/commit/946f253)
chore(set_theory/game/pgame): Cleanup ([#13612](https://github.com/leanprover-community/mathlib/pull/13612))
We remove redundant parentheses, and make arguments explicit when they can't be inferred.
#### Estimated changes
Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/pgame.lean
- \+/\- *theorem* pgame.add_left_neg_equiv
- \+/\- *theorem* pgame.add_left_neg_le_zero
- \+/\- *theorem* pgame.add_right_neg_equiv
- \+/\- *theorem* pgame.add_right_neg_le_zero
- \+/\- *theorem* pgame.zero_le_add_left_neg
- \+/\- *theorem* pgame.zero_le_add_right_neg

Modified src/set_theory/surreal/basic.lean




## [2022-04-24 02:22:27](https://github.com/leanprover-community/mathlib/commit/b0552c1)
docs(tactic/lint/default): Module docstring ([#13570](https://github.com/leanprover-community/mathlib/pull/13570))
Write the module docstring.
#### Estimated changes
Modified src/tactic/lint/default.lean




## [2022-04-24 00:36:50](https://github.com/leanprover-community/mathlib/commit/2d0ff32)
chore(algebra/*): move function instances ([#13650](https://github.com/leanprover-community/mathlib/pull/13650))
These should have been much earlier, but I put them in their current places to avoid large build times in what was an already large refactor.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/geometry/manifold/algebra/smooth_functions.lean


Modified src/group_theory/group_action/pi.lean


Modified src/linear_algebra/pi.lean




## [2022-04-23 22:43:27](https://github.com/leanprover-community/mathlib/commit/cc406db)
feat(algebra/ring/basic): generalisation linter suggestions ([#13649](https://github.com/leanprover-community/mathlib/pull/13649))
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+/\- *lemma* is_regular_of_ne_zero'
- \+/\- *lemma* pred_ne_self
- \+/\- *lemma* succ_ne_self



## [2022-04-23 22:43:26](https://github.com/leanprover-community/mathlib/commit/1abfde6)
chore(group_theory/exponent): generalise ([#13647](https://github.com/leanprover-community/mathlib/pull/13647))
Generalises a few lemmas to not require cancellativity.
#### Estimated changes
Modified src/group_theory/exponent.lean




## [2022-04-23 22:43:25](https://github.com/leanprover-community/mathlib/commit/34b1cfd)
feat(set_theory/game/pgame): Strengthen `move_{left/right}_mk` ([#13646](https://github.com/leanprover-community/mathlib/pull/13646))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+/\- *lemma* pgame.move_left_mk
- \+/\- *lemma* pgame.move_right_mk



## [2022-04-23 22:43:24](https://github.com/leanprover-community/mathlib/commit/44a05db)
fix(topology/algebra/matrix): correct a lemma name ([#13640](https://github.com/leanprover-community/mathlib/pull/13640))
#### Estimated changes
Modified src/topology/algebra/matrix.lean
- \+ *lemma* continuous.matrix_diagonal
- \- *lemma* continuous_matrix.diagonal



## [2022-04-23 21:10:27](https://github.com/leanprover-community/mathlib/commit/09eb35f)
feat(data/part): add get_or_else_of_dom ([#13588](https://github.com/leanprover-community/mathlib/pull/13588))
Adds a lemma
#### Estimated changes
Modified src/data/part.lean
- \+ *lemma* part.get_or_else_of_dom
- \+ *lemma* part.get_or_else_of_not_dom
- \+ *lemma* part.not_none_dom
- \+ *lemma* part.some_dom



## [2022-04-23 09:50:22](https://github.com/leanprover-community/mathlib/commit/afd8a52)
feat(order/hom/basic): add simp lemmas for `strict_mono.order_iso` and friends ([#13606](https://github.com/leanprover-community/mathlib/pull/13606))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/order/hom/basic.lean
- \+ *lemma* strict_mono.coe_order_iso_of_surjective
- \+/\- *def* strict_mono.order_iso_of_right_inverse
- \+ *lemma* strict_mono.order_iso_of_surjective_self_symm_apply
- \+ *lemma* strict_mono.order_iso_of_surjective_symm_apply_self



## [2022-04-23 05:39:49](https://github.com/leanprover-community/mathlib/commit/8c262da)
chore(analysis/normed_space/ray): golf ([#13629](https://github.com/leanprover-community/mathlib/pull/13629))
Golf 2 proofs
#### Estimated changes
Modified src/analysis/normed_space/ray.lean




## [2022-04-23 05:39:48](https://github.com/leanprover-community/mathlib/commit/4ad7dc9)
chore(algebra/ring/equiv): protect ring equiv lemmas for big operators ([#13624](https://github.com/leanprover-community/mathlib/pull/13624))
#### Estimated changes
Modified src/algebra/ring/equiv.lean
- \- *lemma* ring_equiv.map_list_prod
- \- *lemma* ring_equiv.map_list_sum
- \- *lemma* ring_equiv.map_multiset_prod
- \- *lemma* ring_equiv.map_multiset_sum
- \- *lemma* ring_equiv.map_prod
- \- *lemma* ring_equiv.map_sum
- \- *lemma* ring_equiv.unop_map_list_prod



## [2022-04-23 05:39:47](https://github.com/leanprover-community/mathlib/commit/fe435de)
feat(algebra/algebra/basic,analysis/normed_space/basic): The zero ring is a (normed) algebra ([#13618](https://github.com/leanprover-community/mathlib/pull/13618))
This instance probably isn't very useful, but it's nice to have in the docs as an example of what `normed_algebra` permits.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* algebra.algebra_map_punit

Modified src/analysis/normed_space/basic.lean




## [2022-04-23 05:39:45](https://github.com/leanprover-community/mathlib/commit/0bea7a0)
feat(set_theory/pgame): Lemmas about order and left/right moves ([#13590](https://github.com/leanprover-community/mathlib/pull/13590))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.lt_move_right_of_le
- \+ *theorem* pgame.lt_of_le_move_left
- \+ *theorem* pgame.lt_of_move_right_le
- \+ *theorem* pgame.move_left_lt_of_le



## [2022-04-23 04:08:28](https://github.com/leanprover-community/mathlib/commit/26b2d72)
feat(set_theory/game/pgame): Empty instances ([#13635](https://github.com/leanprover-community/mathlib/pull/13635))
#### Estimated changes
Modified src/set_theory/game/pgame.lean




## [2022-04-23 04:08:27](https://github.com/leanprover-community/mathlib/commit/94f970a)
feat(linear_algebra/basic): add a simp lemma for comp_right ([#13625](https://github.com/leanprover-community/mathlib/pull/13625))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.comp_right_apply



## [2022-04-23 04:08:26](https://github.com/leanprover-community/mathlib/commit/b62b531)
doc(analysis/normed_space/basic): Explain how to use non-unital normed algebras ([#13605](https://github.com/leanprover-community/mathlib/pull/13605))
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.E2.9C.94.20Is.20the.20zero.20algebra.20normed.3F/near/279555566)
#### Estimated changes
Modified src/analysis/normed_space/basic.lean




## [2022-04-23 03:26:36](https://github.com/leanprover-community/mathlib/commit/79ea30c)
chore(scripts): update nolints.txt ([#13637](https://github.com/leanprover-community/mathlib/pull/13637))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-04-22 23:37:56](https://github.com/leanprover-community/mathlib/commit/9923362)
doc(measure_theory): add some missing `to_additive` docstrings ([#13456](https://github.com/leanprover-community/mathlib/pull/13456))
#### Estimated changes
Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/group/integration.lean


Modified src/measure_theory/group/measure.lean




## [2022-04-22 22:31:59](https://github.com/leanprover-community/mathlib/commit/976c544)
feat(algebra/order/archimedean): Comparing with rationals determines the order ([#13602](https://github.com/leanprover-community/mathlib/pull/13602))
In a linear ordered field, if `q < x → q ≤ y` for all `q : ℚ`, then `x ≤ y`, and similar results.
#### Estimated changes
Modified src/algebra/order/archimedean.lean
- \+ *lemma* eq_of_forall_lt_rat_iff_lt
- \+ *lemma* eq_of_forall_rat_lt_iff_lt
- \+ *lemma* le_of_forall_lt_rat_imp_le
- \+ *lemma* le_of_forall_rat_lt_imp_le



## [2022-04-22 22:31:58](https://github.com/leanprover-community/mathlib/commit/b98bd41)
feat(topology/uniform_space/matrix): Add the uniform_space structure on matrices ([#13534](https://github.com/leanprover-community/mathlib/pull/13534))
#### Estimated changes
Added src/topology/uniform_space/matrix.lean
- \+ *lemma* matrix.uniform_continuous
- \+ *lemma* matrix.uniformity



## [2022-04-22 20:06:20](https://github.com/leanprover-community/mathlib/commit/4547076)
chore(*): use zero_lt_two/two_ne_zero lemmas more ([#13609](https://github.com/leanprover-community/mathlib/pull/13609))
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* mul_self_ne_zero
- \+ *lemma* zero_ne_mul_self

Modified src/analysis/normed_space/star/spectrum.lean


Modified src/data/nat/modeq.lean


Modified src/data/nat/sqrt.lean


Modified src/number_theory/fermat4.lean


Modified src/number_theory/lucas_lehmer.lean


Modified src/number_theory/pythagorean_triples.lean




## [2022-04-22 20:06:19](https://github.com/leanprover-community/mathlib/commit/9eb3858)
feat(combinatorics/pigeonhole): Pigeons in linear commutative rings ([#13308](https://github.com/leanprover-community/mathlib/pull/13308))
Duplicate almost all the pigeonhole principle API to work in `linear_ordered_comm_ring`s.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *lemma* finset.cast_card

Modified src/combinatorics/pigeonhole.lean
- \+ *lemma* finset.exists_card_fiber_le_of_card_le_nsmul
- \+ *lemma* finset.exists_card_fiber_lt_of_card_lt_nsmul
- \+ *lemma* finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
- \+ *lemma* finset.exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to
- \+ *lemma* fintype.exists_card_fiber_le_of_card_le_nsmul
- \+ *lemma* fintype.exists_card_fiber_lt_of_card_lt_nsmul
- \+ *lemma* fintype.exists_le_card_fiber_of_nsmul_le_card
- \+ *lemma* fintype.exists_lt_card_fiber_of_nsmul_lt_card



## [2022-04-22 20:06:18](https://github.com/leanprover-community/mathlib/commit/7be21e0)
feat(topology/algebra/group): quotient by a closed subgroup is regular ([#13278](https://github.com/leanprover-community/mathlib/pull/13278))
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+/\- *lemma* topological_group.t2_space



## [2022-04-22 20:06:16](https://github.com/leanprover-community/mathlib/commit/ad3e667)
feat(order/chain): Flags ([#13089](https://github.com/leanprover-community/mathlib/pull/13089))
Define the type of maximal chains, aka flags, of an order.
#### Estimated changes
Modified src/data/set/pairwise.lean
- \+ *lemma* reflexive.set_pairwise_iff
- \+ *lemma* set.pairwise_iff_of_refl

Modified src/order/chain.lean
- \+ *lemma* flag.bot_mem
- \+ *lemma* flag.chain_le
- \+ *lemma* flag.chain_lt
- \+ *lemma* flag.coe_mk
- \+ *lemma* flag.ext
- \+ *lemma* flag.mem_coe_iff
- \+ *lemma* flag.mk_coe
- \+ *lemma* flag.top_mem
- \+ *lemma* is_max_chain.bot_mem
- \+ *lemma* is_max_chain.top_mem



## [2022-04-22 18:15:50](https://github.com/leanprover-community/mathlib/commit/9c3cb72)
feat(data/int/basic): Add unit lemmas ([#13565](https://github.com/leanprover-community/mathlib/pull/13565))
This PR adds a few more unit lemmas, and cleans up some of the proofs.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \- *lemma* int.units_sq

Modified src/data/int/basic.lean
- \+ *lemma* int.is_unit_mul_self
- \+ *lemma* int.is_unit_sq
- \+/\- *lemma* int.units_inv_eq_self
- \+ *lemma* int.units_sq



## [2022-04-22 18:15:49](https://github.com/leanprover-community/mathlib/commit/695e0b7)
feat(analysis/convex/strict_convex_space): Verify strict convexity from fixed scalars ([#13548](https://github.com/leanprover-community/mathlib/pull/13548))
Prove that `∀ x y : E, ∥x∥ ≤ 1 → ∥y∥ ≤ 1 → x ≠ y → ∥a • x + b • y∥ < 1` for **fixed** `a` and `b` is enough for `E` to be a strictly convex space.
#### Estimated changes
Modified src/analysis/convex/strict_convex_space.lean
- \+ *lemma* strict_convex_space.of_norm_add_lt
- \+ *lemma* strict_convex_space.of_norm_add_lt_aux



## [2022-04-22 18:15:48](https://github.com/leanprover-community/mathlib/commit/2e83d61)
feat(topology/metric_space/hausdorff_distance): Thickening the closure ([#13515](https://github.com/leanprover-community/mathlib/pull/13515))
`thickening δ (closure s) = thickening δ s` and other simple lemmas. Also rename `inf_edist_le_inf_edist_of_subset` to `inf_edist_anti` and make arguments to `mem_thickening_iff` implicit.
#### Estimated changes
Modified src/data/real/ennreal.lean


Modified src/data/set/lattice.lean
- \+ *lemma* infi_Union
- \+ *lemma* supr_Union

Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* emetric.inf_edist_Union
- \+ *lemma* emetric.inf_edist_anti
- \+ *lemma* emetric.inf_edist_le_edist_add_inf_edist
- \- *lemma* emetric.inf_edist_le_inf_edist_of_subset
- \+ *lemma* metric.cthickening_closure
- \+ *lemma* metric.cthickening_union
- \+ *lemma* metric.inf_edist_le_inf_edist_cthickening_add
- \+ *lemma* metric.inf_edist_le_inf_edist_thickening_add
- \+ *lemma* metric.mem_cthickening_iff
- \+/\- *lemma* metric.mem_thickening_iff
- \+ *lemma* metric.mem_thickening_iff_inf_edist_lt
- \+ *lemma* metric.thickening_Union
- \+ *lemma* metric.thickening_closure
- \+ *lemma* metric.thickening_of_nonpos
- \+ *lemma* metric.thickening_union



## [2022-04-22 15:16:45](https://github.com/leanprover-community/mathlib/commit/355d68a)
chore(ring_theory/roots_of_unity): primitive roots are not zero ([#13587](https://github.com/leanprover-community/mathlib/pull/13587))
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean




## [2022-04-22 15:16:44](https://github.com/leanprover-community/mathlib/commit/79ac4c8)
chore(data/polynomial/degree/definitions): simplify sum_fin, degree_C_le ([#13564](https://github.com/leanprover-community/mathlib/pull/13564))
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* polynomial.nat_degree_lt_iff_degree_lt

Modified src/order/bounded_order.lean
- \+ *lemma* with_bot.get_or_else_bot_lt_iff



## [2022-04-22 15:16:42](https://github.com/leanprover-community/mathlib/commit/a74df9b)
feat(number_theory/legendre_symbol): add file quadratic_char.lean ([#13503](https://github.com/leanprover-community/mathlib/pull/13503))
This adds the file `quadratic_char.lean` in `number_theory/legendre_symbol/`.
This file contains (apart from some more general stuff on finite fields that is useful for what is done in the file) the definition of the quadratic character on a finite field `F` (with values in the integers) and a number of statements of properties.
It also defines quadratic characters on `zmod 4` and `zmod 8` that will be useful for the supplements to the law of quadratic reciprocity.
#### Estimated changes
Modified src/algebra/parity.lean
- \+ *lemma* is_square_zero

Added src/number_theory/legendre_symbol/quadratic_char.lean
- \+ *def* char.quadratic_char
- \+ *lemma* char.quadratic_char_dichotomy
- \+ *lemma* char.quadratic_char_eq_one_of_char_two
- \+ *lemma* char.quadratic_char_eq_pow_of_char_ne_two
- \+ *lemma* char.quadratic_char_eq_zero_iff
- \+ *lemma* char.quadratic_char_exists_neg_one
- \+ *def* char.quadratic_char_hom
- \+ *lemma* char.quadratic_char_mul
- \+ *lemma* char.quadratic_char_one
- \+ *lemma* char.quadratic_char_one_iff_is_square
- \+ *lemma* char.quadratic_char_sq_one'
- \+ *lemma* char.quadratic_char_sq_one
- \+ *lemma* char.quadratic_char_sum_zero
- \+ *lemma* char.quadratic_char_zero
- \+ *lemma* finite_field.exists_nonsquare
- \+ *lemma* finite_field.is_square_iff
- \+ *lemma* finite_field.is_square_of_char_two
- \+ *lemma* finite_field.neg_one_ne_one_of_char_ne_two
- \+ *lemma* finite_field.odd_card_of_char_ne_two
- \+ *lemma* finite_field.pow_dichotomy
- \+ *lemma* finite_field.unit_is_sqare_iff
- \+ *lemma* is_square_of_char_two'
- \+ *def* zmod.χ₄
- \+ *def* zmod.χ₈'
- \+ *def* zmod.χ₈



## [2022-04-22 12:15:36](https://github.com/leanprover-community/mathlib/commit/631890b)
chore(data/rat/basic): tidy some proofs ([#13603](https://github.com/leanprover-community/mathlib/pull/13603))
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *theorem* rat.mk_ne_zero



## [2022-04-22 12:15:35](https://github.com/leanprover-community/mathlib/commit/f7dac5e)
feat(logic/basic): add `auto_param.out` and `opt_param.out` ([#13599](https://github.com/leanprover-community/mathlib/pull/13599))
#### Estimated changes
Modified src/logic/basic.lean
- \+ *def* auto_param.out
- \+ *def* opt_param.out



## [2022-04-22 12:15:34](https://github.com/leanprover-community/mathlib/commit/6729cca)
feat(set_theory/game/pgame): simp + private ([#13596](https://github.com/leanprover-community/mathlib/pull/13596))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+/\- *theorem* pgame.not_le
- \- *theorem* pgame.not_le_lt
- \+/\- *theorem* pgame.not_lt



## [2022-04-22 12:15:32](https://github.com/leanprover-community/mathlib/commit/62205c2)
refactor(data/nat/factorization): Infer arguments ([#13595](https://github.com/leanprover-community/mathlib/pull/13595))
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+/\- *lemma* nat.dvd_iff_div_factorization_eq_tsub
- \+/\- *lemma* nat.factorization_eq_zero_of_non_prime



## [2022-04-22 11:41:15](https://github.com/leanprover-community/mathlib/commit/9abfff3)
chore(analysis/inner_product_space/lax_milgram): tidy some proofs ([#13604](https://github.com/leanprover-community/mathlib/pull/13604))
#### Estimated changes
Modified src/analysis/inner_product_space/lax_milgram.lean




## [2022-04-22 08:34:36](https://github.com/leanprover-community/mathlib/commit/3d24b09)
feat(algebra/ring/basic): define non-unital ring homs ([#13430](https://github.com/leanprover-community/mathlib/pull/13430))
This defines a new bundled hom type and associated class for non-unital (even non-associative) (semi)rings. The associated notation introduced for these homs is `α →ₙ+* β` to parallel the `ring_hom` notation `α →+* β`, where `ₙ` stands for "non-unital".
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* non_unital_ring_hom.cancel_left
- \+ *lemma* non_unital_ring_hom.cancel_right
- \+ *lemma* non_unital_ring_hom.coe_add_monoid_hom_id
- \+ *theorem* non_unital_ring_hom.coe_add_monoid_hom_injective
- \+ *lemma* non_unital_ring_hom.coe_add_monoid_hom_mk
- \+ *lemma* non_unital_ring_hom.coe_coe
- \+ *lemma* non_unital_ring_hom.coe_comp
- \+ *lemma* non_unital_ring_hom.coe_comp_add_monoid_hom
- \+ *lemma* non_unital_ring_hom.coe_comp_mul_hom
- \+ *lemma* non_unital_ring_hom.coe_mk
- \+ *lemma* non_unital_ring_hom.coe_mul
- \+ *lemma* non_unital_ring_hom.coe_mul_hom_id
- \+ *theorem* non_unital_ring_hom.coe_mul_hom_injective
- \+ *lemma* non_unital_ring_hom.coe_mul_hom_mk
- \+ *lemma* non_unital_ring_hom.coe_one
- \+ *lemma* non_unital_ring_hom.coe_to_add_monoid_hom
- \+ *lemma* non_unital_ring_hom.coe_to_mul_hom
- \+ *lemma* non_unital_ring_hom.coe_zero
- \+ *def* non_unital_ring_hom.comp
- \+ *lemma* non_unital_ring_hom.comp_apply
- \+ *lemma* non_unital_ring_hom.comp_assoc
- \+ *lemma* non_unital_ring_hom.comp_id
- \+ *lemma* non_unital_ring_hom.comp_zero
- \+ *theorem* non_unital_ring_hom.ext
- \+ *theorem* non_unital_ring_hom.ext_iff
- \+ *lemma* non_unital_ring_hom.id_apply
- \+ *lemma* non_unital_ring_hom.id_comp
- \+ *lemma* non_unital_ring_hom.mk_coe
- \+ *lemma* non_unital_ring_hom.mul_def
- \+ *lemma* non_unital_ring_hom.one_def
- \+ *lemma* non_unital_ring_hom.to_fun_eq_coe
- \+ *lemma* non_unital_ring_hom.zero_apply
- \+ *lemma* non_unital_ring_hom.zero_comp



## [2022-04-22 06:47:42](https://github.com/leanprover-community/mathlib/commit/394dec3)
feat(order/filter/small_sets): define the filter of small sets ([#13467](https://github.com/leanprover-community/mathlib/pull/13467))
* Main author is @PatrickMassot 
* From the sphere eversion project
* Required for convolutions
Co-authored by: Patrick Massot <patrick.massot@u-psud.fr>
#### Estimated changes
Added src/order/filter/small_sets.lean
- \+ *lemma* filter.has_basis.small_sets
- \+ *lemma* filter.has_basis_small_sets
- \+ *def* filter.small_sets
- \+ *lemma* filter.small_sets_eq_generate
- \+ *lemma* filter.tendsto_small_sets_iff



## [2022-04-22 06:47:41](https://github.com/leanprover-community/mathlib/commit/9db5916)
fix(data/fintype/basic): fix `fintype_of_option_equiv` ([#13466](https://github.com/leanprover-community/mathlib/pull/13466))
A type is a `fintype` if its successor (using `option`) is a `fintype`
This fixes an error introduced in [#13086](https://github.com/leanprover-community/mathlib/pull/13086).
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+/\- *def* fintype_of_option_equiv



## [2022-04-22 06:47:40](https://github.com/leanprover-community/mathlib/commit/0d77f29)
feat(analysis/calculus/specific_functions): define normed bump functions ([#13463](https://github.com/leanprover-community/mathlib/pull/13463))
* Normed bump functions have integral 1 w.r.t. the specified measure.
* Also add a few more properties of bump functions, including its smoothness in all arguments (including midpoint and the two radii).
* From the sphere eversion project
* Required for convolutions
#### Estimated changes
Modified src/analysis/calculus/specific_functions.lean
- \+ *lemma* cont_diff.cont_diff_bump
- \+ *lemma* cont_diff_bump_of_inner.cont_diff_normed
- \+ *lemma* cont_diff_bump_of_inner.continuous_normed
- \+ *lemma* cont_diff_bump_of_inner.has_compact_support_normed
- \+ *lemma* cont_diff_bump_of_inner.integral_normed
- \+ *lemma* cont_diff_bump_of_inner.integral_normed_smul
- \+ *lemma* cont_diff_bump_of_inner.integral_pos
- \+ *lemma* cont_diff_bump_of_inner.nonneg'
- \+ *lemma* cont_diff_bump_of_inner.nonneg_normed
- \+ *lemma* cont_diff_bump_of_inner.normed_def
- \+ *lemma* cont_diff_bump_of_inner.normed_neg
- \+ *lemma* cont_diff_bump_of_inner.normed_sub
- \+ *lemma* cont_diff_bump_of_inner.support_normed_eq
- \+ *lemma* cont_diff_bump_of_inner.tsupport_eq
- \+ *lemma* cont_diff_bump_of_inner.tsupport_normed_eq

Modified src/analysis/normed/group/basic.lean
- \+ *theorem* dist_self_sub_left
- \+ *theorem* dist_self_sub_right

Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.integrable.div_const

Modified src/order/cover.lean
- \+ *lemma* covby.Iio_eq
- \+ *lemma* covby.Ioi_eq

Modified src/topology/algebra/order/basic.lean
- \+ *lemma* continuous_at.eventually_lt
- \+ *lemma* tendsto.eventually_lt



## [2022-04-22 06:47:39](https://github.com/leanprover-community/mathlib/commit/06a6044)
feat(analysis/normed_space/exponential): Weaken typeclass requirements ([#13444](https://github.com/leanprover-community/mathlib/pull/13444))
This allows the exponential to be defined independently of a choice of norm.
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/analysis/calculus/formal_multilinear_series.lean
- \+/\- *lemma* formal_multilinear_series.remove_zero_coeff_succ
- \+/\- *lemma* formal_multilinear_series.remove_zero_coeff_zero
- \+/\- *lemma* formal_multilinear_series.remove_zero_of_pos
- \+/\- *def* formal_multilinear_series

Modified src/analysis/normed_space/exponential.lean
- \+/\- *lemma* exp_eq_tsum_field
- \+/\- *lemma* exp_series_apply_eq_field'
- \+/\- *lemma* exp_series_apply_eq_field
- \+/\- *lemma* exp_series_sum_eq_field
- \+/\- *lemma* exp_zero

Modified src/analysis/normed_space/multilinear.lean




## [2022-04-22 04:34:08](https://github.com/leanprover-community/mathlib/commit/2b902eb)
chore(scripts): update nolints.txt ([#13597](https://github.com/leanprover-community/mathlib/pull/13597))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-04-22 04:34:07](https://github.com/leanprover-community/mathlib/commit/79bc6ad)
feat(data/mv_polynomial/equiv): API for `mv_polynomial.fin_succ_equiv` ([#10812](https://github.com/leanprover-community/mathlib/pull/10812))
This PR provides API for `mv_polynomial.fin_succ_equiv`: coefficients, degree, coefficientes of coefficients, degree_of of coefficients, etc.
To state and prove these lemmas I had to define `cons` and `tail` for maps `fin (n+1) →₀ M` and prove the usual properties for these. I'm not sure if this is necessary or the correct approach to do this.
#### Estimated changes
Added src/data/finsupp/fin.lean
- \+ *def* finsupp.cons
- \+ *lemma* finsupp.cons_ne_zero_iff
- \+ *lemma* finsupp.cons_ne_zero_of_left
- \+ *lemma* finsupp.cons_ne_zero_of_right
- \+ *lemma* finsupp.cons_succ
- \+ *lemma* finsupp.cons_tail
- \+ *lemma* finsupp.cons_zero
- \+ *lemma* finsupp.cons_zero_zero
- \+ *def* finsupp.tail
- \+ *lemma* finsupp.tail_apply
- \+ *lemma* finsupp.tail_cons

Modified src/data/mv_polynomial/equiv.lean
- \+ *lemma* mv_polynomial.coeff_eval_eq_eval_coeff
- \+ *lemma* mv_polynomial.degree_fin_succ_equiv
- \+ *lemma* mv_polynomial.degree_of_coeff_fin_succ_equiv
- \+ *lemma* mv_polynomial.eval_eq_eval_mv_eval'
- \+/\- *def* mv_polynomial.fin_succ_equiv
- \+ *lemma* mv_polynomial.fin_succ_equiv_X_succ
- \+ *lemma* mv_polynomial.fin_succ_equiv_X_zero
- \+/\- *lemma* mv_polynomial.fin_succ_equiv_apply
- \+ *lemma* mv_polynomial.fin_succ_equiv_coeff_coeff
- \+/\- *lemma* mv_polynomial.fin_succ_equiv_eq
- \+ *lemma* mv_polynomial.fin_succ_equiv_support'
- \+ *lemma* mv_polynomial.fin_succ_equiv_support
- \+ *lemma* mv_polynomial.nat_degree_fin_succ_equiv
- \+ *lemma* mv_polynomial.support_coeff_fin_succ_equiv
- \+ *lemma* mv_polynomial.support_fin_succ_equiv_nonempty



## [2022-04-22 01:34:22](https://github.com/leanprover-community/mathlib/commit/17d2424)
feat(polynomial/cyclotomic): `eval_apply` ([#13586](https://github.com/leanprover-community/mathlib/pull/13586))
#### Estimated changes
Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* polynomial.cyclotomic.eval_apply



## [2022-04-22 01:34:21](https://github.com/leanprover-community/mathlib/commit/40fc58c)
feat(data/quot): `quotient.out` is injective ([#13584](https://github.com/leanprover-community/mathlib/pull/13584))
#### Estimated changes
Modified src/data/quot.lean
- \+ *lemma* quotient.out_injective



## [2022-04-22 01:34:20](https://github.com/leanprover-community/mathlib/commit/821e7c8)
doc(category_theory/limits/has_limits): fix two docstrings ([#13581](https://github.com/leanprover-community/mathlib/pull/13581))
#### Estimated changes
Modified src/category_theory/limits/has_limits.lean




## [2022-04-22 01:34:19](https://github.com/leanprover-community/mathlib/commit/7b92db7)
chore(set_theory/cardinal/basic): Fix spacing ([#13562](https://github.com/leanprover-community/mathlib/pull/13562))
#### Estimated changes
Modified src/set_theory/cardinal/basic.lean




## [2022-04-22 01:34:17](https://github.com/leanprover-community/mathlib/commit/1da12b5)
fix(analysis/normed_space/basic): allow the zero ring to be a normed algebra ([#13544](https://github.com/leanprover-community/mathlib/pull/13544))
This replaces `norm_algebra_map_eq : ∀ x : 𝕜, ∥algebra_map 𝕜 𝕜' x∥ = ∥x∥` with `norm_smul_le : ∀ (r : 𝕜) (x : 𝕜'), ∥r • x∥ ≤ ∥r∥ * ∥x∥` in `normed_algebra`. With this change, `normed_algebra` means nothing more than "a normed module that is also an algebra", which seems to be the only notion actually used in mathlib anyway. In practice, this change really just removes any constraints on `∥1∥`.
The old meaning of `[normed_algebra R A]` is now achieved with `[normed_algebra R A] [norm_one_class A]`.
As a result, lemmas like `normed_algebra.norm_one_class` and `normed_algebra.nontrivial` have been removed, as they no longer make sense now that the two typeclasses are entirely orthogonal.
Notably this means that the following `normed_algebra` instances hold more generally than before:
* `continuous_linear_map.to_normed_algebra`
* `pi.normed_algebra`
* `bounded_continuous_function.normed_algebra`
* `continuous_map.normed_algebra`
* Instances not yet in mathlib:
  * Matrices under the `L1-L_inf` norm are a normed algebra even if the matrix is empty
  * Matrices under the frobenius norm are a normed algebra (note `∥(1 : matrix n n 𝕜')∥ = \sqrt (fintype.card n)` with that norm)
This last one is the original motivation for this PR; otherwise every lemma about a matrix exponential has to case on whether the matrices are empty.
It is possible that some of the `[norm_one_class A]`s added in `spectrum.lean` are unnecessary; however, the assumptions are no stronger than they were before, and I'm not interested in trying to generalize them as part of this PR.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Is.20the.20zero.20algebra.20normed.3F/near/279515954)
#### Estimated changes
Modified src/analysis/complex/basic.lean


Modified src/analysis/normed/normed_field.lean
- \+ *lemma* norm_one_class.nontrivial
- \+ *lemma* units.nnnorm_pos
- \- *lemma* units.nnorm_pos

Modified src/analysis/normed_space/basic.lean
- \+/\- *def* algebra_map_clm
- \+/\- *lemma* algebra_map_clm_coe
- \+/\- *lemma* algebra_map_clm_to_linear_map
- \+/\- *lemma* algebra_map_isometry
- \+ *lemma* nnnorm_algebra_map'
- \+ *lemma* nnnorm_algebra_map
- \- *lemma* nnorm_algebra_map_eq
- \+ *lemma* norm_algebra_map'
- \+ *lemma* norm_algebra_map
- \- *lemma* norm_algebra_map_eq
- \- *lemma* normed_algebra.nontrivial
- \- *lemma* normed_algebra.norm_one
- \- *lemma* normed_algebra.norm_one_class
- \- *lemma* normed_algebra.zero_ne_one

Modified src/analysis/normed_space/is_R_or_C.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* continuous_linear_map.coe_lmul_rightₗᵢ
- \+/\- *lemma* continuous_linear_map.coe_lmulₗᵢ
- \+/\- *def* continuous_linear_map.lmul_rightₗᵢ
- \+/\- *def* continuous_linear_map.lmulₗᵢ
- \+/\- *lemma* continuous_linear_map.op_norm_lmul
- \+/\- *lemma* continuous_linear_map.op_norm_lmul_apply
- \+ *lemma* continuous_linear_map.op_norm_lmul_apply_le
- \+/\- *lemma* continuous_linear_map.op_norm_lmul_right
- \+/\- *lemma* continuous_linear_map.op_norm_lmul_right_apply
- \+ *lemma* continuous_linear_map.op_norm_lmul_right_apply_le

Modified src/analysis/normed_space/spectrum.lean
- \+/\- *lemma* alg_hom.continuous
- \+/\- *def* alg_hom.to_continuous_linear_map
- \+/\- *lemma* spectrum.is_bounded
- \+/\- *theorem* spectrum.is_compact
- \+/\- *lemma* spectrum.mem_resolvent_of_norm_lt
- \+/\- *lemma* spectrum.norm_le_norm_of_mem
- \+/\- *theorem* spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius
- \+/\- *theorem* spectrum.pow_norm_pow_one_div_tendsto_nhds_spectral_radius
- \+/\- *theorem* spectrum.spectral_radius_le_nnnorm
- \+/\- *theorem* spectrum.spectral_radius_le_pow_nnnorm_pow_one_div
- \+/\- *lemma* spectrum.subset_closed_ball_norm

Modified src/analysis/normed_space/star/spectrum.lean
- \+/\- *lemma* spectral_radius_eq_nnnorm_of_self_adjoint
- \+/\- *lemma* spectral_radius_eq_nnnorm_of_star_normal

Modified src/analysis/quaternion.lean
- \+ *lemma* quaternion.nnnorm_coe
- \- *lemma* quaternion.nnorm_coe

Modified src/number_theory/cyclotomic/discriminant.lean


Modified src/number_theory/cyclotomic/primitive_roots.lean


Modified src/ring_theory/norm.lean
- \- *lemma* algebra.norm_algebra_map

Modified src/ring_theory/polynomial/eisenstein.lean


Modified src/topology/continuous_function/bounded.lean


Modified src/topology/continuous_function/compact.lean




## [2022-04-22 01:34:16](https://github.com/leanprover-community/mathlib/commit/77236cd)
refactor(category_theory): make has_zero_object a Prop  ([#13517](https://github.com/leanprover-community/mathlib/pull/13517))
#### Estimated changes
Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Group/zero.lean
- \+ *lemma* CommGroup.is_zero_of_subsingleton
- \+ *lemma* Group.is_zero_of_subsingleton

Modified src/algebra/category/Module/basic.lean
- \+ *lemma* Module.is_zero_of_subsingleton

Modified src/algebra/homology/augment.lean


Modified src/algebra/homology/homological_complex.lean
- \+ *lemma* homological_complex.is_zero_zero

Modified src/algebra/homology/single.lean


Modified src/analysis/normed/group/SemiNormedGroup.lean
- \+ *lemma* SemiNormedGroup.is_zero_of_subsingleton
- \+ *lemma* SemiNormedGroup₁.is_zero_of_subsingleton

Modified src/category_theory/abelian/basic.lean


Modified src/category_theory/abelian/right_derived.lean


Modified src/category_theory/differential_object.lean


Modified src/category_theory/functor/left_derived.lean


Modified src/category_theory/graded_object.lean


Modified src/category_theory/limits/shapes/biproducts.lean
- \- *def* category_theory.limits.has_zero_object_of_has_finite_biproducts

Modified src/category_theory/limits/shapes/zero_morphisms.lean
- \+ *lemma* category_theory.functor.zero_obj
- \- *lemma* category_theory.limits.has_zero_object.functor.zero_map
- \- *lemma* category_theory.limits.has_zero_object.functor.zero_obj
- \+ *lemma* category_theory.limits.has_zero_object_of_has_initial_object
- \- *def* category_theory.limits.has_zero_object_of_has_initial_object
- \+ *lemma* category_theory.limits.has_zero_object_of_has_terminal_object
- \- *def* category_theory.limits.has_zero_object_of_has_terminal_object
- \+ *lemma* category_theory.limits.is_zero.map
- \+ *lemma* category_theory.zero_map

Modified src/category_theory/limits/shapes/zero_objects.lean
- \+ *lemma* category_theory.functor.is_zero
- \+ *lemma* category_theory.functor.is_zero_iff
- \+ *lemma* category_theory.iso.is_zero_iff
- \- *def* category_theory.limits.has_zero_object.is_zero.iso_zero
- \- *lemma* category_theory.limits.has_zero_object.is_zero_zero
- \+ *lemma* category_theory.limits.is_zero.has_zero_object
- \+ *def* category_theory.limits.is_zero.iso_zero
- \+ *lemma* category_theory.limits.is_zero.obj
- \+ *lemma* category_theory.limits.is_zero_zero
- \- *lemma* category_theory.limits.iso.is_zero_iff



## [2022-04-22 01:34:15](https://github.com/leanprover-community/mathlib/commit/dced133)
feat(group_theory/group_action/basic): Right multiplication satisfies the `quotient_action` axiom ([#13475](https://github.com/leanprover-community/mathlib/pull/13475))
This PR adds a `quotient_action` instance for right multiplication.
#### Estimated changes
Modified src/group_theory/group_action/basic.lean




## [2022-04-22 01:34:14](https://github.com/leanprover-community/mathlib/commit/bb9d1c5)
chore(*): remove `subst` when not necessary ([#13453](https://github.com/leanprover-community/mathlib/pull/13453))
Where possible, this replaces `subst` with `obtain rfl` (which is equivalent to `have` and then `subst`, golfing a line).
This also tidies some non-terminal `simp`s.
#### Estimated changes
Modified archive/imo/imo1960_q1.lean


Modified src/algebra/homology/additive.lean


Modified src/algebraic_geometry/ringed_space.lean


Modified src/algebraic_topology/simplex_category.lean


Modified src/analysis/box_integral/integrability.lean


Modified src/analysis/normed/group/quotient.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/category_theory/category/basic.lean
- \+/\- *lemma* category_theory.cancel_epi

Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/limits/shapes/strict_initial.lean


Modified src/control/applicative.lean


Modified src/control/lawful_fix.lean
- \+/\- *lemma* part.fix.le_f_of_mem_approx

Modified src/data/buffer/parser/basic.lean


Modified src/data/dfinsupp/basic.lean


Modified src/data/fin/tuple/basic.lean


Modified src/data/fin_enum.lean


Modified src/data/hash_map.lean


Modified src/data/int/basic.lean


Modified src/data/list/forall2.lean


Modified src/data/list/pairwise.lean


Modified src/data/list/permutation.lean


Modified src/data/list/sort.lean


Modified src/data/multiset/pi.lean


Modified src/data/nat/gcd.lean


Modified src/data/nat/pow.lean


Modified src/data/ordmap/ordset.lean


Modified src/data/pfunctor/univariate/M.lean
- \+/\- *lemma* pfunctor.M.is_path_cons'
- \+/\- *lemma* pfunctor.M.is_path_cons

Modified src/data/rat/basic.lean


Modified src/data/rbtree/insert.lean


Modified src/data/real/irrational.lean


Modified src/data/set/basic.lean


Modified src/data/set/function.lean


Modified src/data/sigma/basic.lean


Modified src/field_theory/adjoin.lean


Modified src/linear_algebra/affine_space/affine_map.lean


Modified src/linear_algebra/affine_space/independent.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/free_module/pid.lean


Modified src/linear_algebra/linear_pmap.lean


Modified src/logic/relator.lean


Modified src/order/complete_lattice.lean


Modified src/order/order_iso_nat.lean


Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/artinian.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/set_theory/ordinal/basic.lean


Modified src/set_theory/ordinal/notation.lean


Modified src/set_theory/zfc.lean
- \+/\- *theorem* Set.pair_inj

Modified src/topology/homotopy/path.lean


Modified src/topology/sets/opens.lean


Modified src/topology/uniform_space/compact_separated.lean




## [2022-04-21 23:36:55](https://github.com/leanprover-community/mathlib/commit/afb4392)
feat(linear_algebra/prod): two lemmas about prod_map ([#13572](https://github.com/leanprover-community/mathlib/pull/13572))
#### Estimated changes
Modified src/linear_algebra/prod.lean
- \+ *lemma* linear_map.prod_map_comp
- \+ *lemma* linear_map.prod_map_id
- \+ *def* linear_map.prod_map_monoid_hom
- \+ *lemma* linear_map.prod_map_mul
- \+ *lemma* linear_map.prod_map_one



## [2022-04-21 23:36:54](https://github.com/leanprover-community/mathlib/commit/d444a27)
feat(group_theory/transfer): Define the transfer homomorphism ([#13446](https://github.com/leanprover-community/mathlib/pull/13446))
This PR adds a definition of the transfer homomorphism.
#### Estimated changes
Added src/group_theory/transfer.lean
- \+ *lemma* monoid_hom.transfer_def
- \+ *lemma* subgroup.left_transversals.diff_inv
- \+ *lemma* subgroup.left_transversals.diff_mul_diff
- \+ *lemma* subgroup.left_transversals.diff_self
- \+ *lemma* subgroup.left_transversals.smul_diff_smul



## [2022-04-21 23:36:53](https://github.com/leanprover-community/mathlib/commit/b1a1ece)
feat(ring_theory/valuation/valuation_subring): The order structure on valuation subrings of a field ([#13429](https://github.com/leanprover-community/mathlib/pull/13429))
This PR shows that for a valuation subring `R` of a field `K`, the coarsenings of `R` are in (anti)ordered bijections with the prime ideals of `R`. As a corollary, the collection of such coarsenings is totally ordered.
#### Estimated changes
Modified src/algebra/hom/units.lean


Added src/ring_theory/localization/as_subring.lean
- \+ *lemma* localization.map_is_unit_of_le
- \+ *def* localization.map_to_fraction_ring
- \+ *lemma* localization.map_to_fraction_ring_apply
- \+ *lemma* localization.mem_range_map_to_fraction_ring_iff
- \+ *lemma* localization.subalgebra.mem_range_map_to_fraction_ring_iff_of_field
- \+ *def* localization.subalgebra.of_field
- \+ *def* localization.subalgebra

Modified src/ring_theory/valuation/valuation_subring.lean
- \+ *lemma* valuation_subring.add_mem
- \+ *def* valuation_subring.ideal_of_le
- \+ *lemma* valuation_subring.ideal_of_le_le_of_le
- \+ *lemma* valuation_subring.ideal_of_le_of_prime
- \+ *def* valuation_subring.inclusion
- \+ *lemma* valuation_subring.le_of_prime
- \+ *def* valuation_subring.map_of_le
- \+ *lemma* valuation_subring.map_of_le_comp_valuation
- \+ *lemma* valuation_subring.map_of_le_valuation_apply
- \+ *lemma* valuation_subring.mem_of_subring
- \+/\- *lemma* valuation_subring.mem_of_valuation_le_one
- \+ *lemma* valuation_subring.monotone_map_of_le
- \+ *lemma* valuation_subring.mul_mem
- \+ *lemma* valuation_subring.neg_mem
- \+ *def* valuation_subring.of_le
- \+ *def* valuation_subring.of_prime
- \+ *lemma* valuation_subring.of_prime_ideal_of_le
- \+ *lemma* valuation_subring.of_prime_le_of_le
- \+ *lemma* valuation_subring.of_prime_valuation_eq_one_iff_mem_prime_compl
- \+ *def* valuation_subring.of_subring
- \+ *lemma* valuation_subring.one_mem
- \+ *def* valuation_subring.prime_spectrum_equiv
- \+ *def* valuation_subring.prime_spectrum_order_equiv
- \+ *def* valuation_subring.subtype
- \+/\- *def* valuation_subring.valuation
- \+ *lemma* valuation_subring.valuation_eq_one_iff
- \+ *lemma* valuation_subring.valuation_lt_one_iff
- \+ *lemma* valuation_subring.valuation_lt_one_or_eq_one
- \+ *lemma* valuation_subring.valuation_unit
- \+ *def* valuation_subring.value_group
- \+ *lemma* valuation_subring.zero_mem



## [2022-04-21 23:36:51](https://github.com/leanprover-community/mathlib/commit/1e76b9e)
feat(topology/constructions): more convenient lemmas ([#13423](https://github.com/leanprover-community/mathlib/pull/13423))
* Define `continuous.fst'` and friends and `continuous.comp₂` and friends for convenience (and to help with elaborator issues)
* Cleanup in `topology/constructions`
* Define `set.preimage_inl_image_inr` and `set.preimage_inr_image_inl` and prove the `range` versions in terms of these. This required reordering some lemmas (moving general lemmas about `range` above the lemmas of interactions with `range` and specific functions).
* From the sphere eversion project
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.preimage_inl_image_inr
- \+ *theorem* set.preimage_inr_image_inl
- \+/\- *lemma* set.range_const_subset

Modified src/topology/constructions.lean
- \+ *lemma* continuous.comp₂
- \+ *lemma* continuous.comp₃
- \+ *lemma* continuous.comp₄
- \+ *lemma* continuous.fst'
- \+/\- *lemma* continuous.prod.mk
- \+ *lemma* continuous.prod.mk_left
- \+ *lemma* continuous.snd'
- \+ *lemma* continuous_at.fst''
- \+ *lemma* continuous_at.fst'
- \+ *lemma* continuous_at.snd''
- \+ *lemma* continuous_at.snd'
- \+/\- *lemma* embedding_graph



## [2022-04-21 23:36:50](https://github.com/leanprover-community/mathlib/commit/63ee558)
feat(algebra/big_operators): split products and sums over fin (a+b) ([#13291](https://github.com/leanprover-community/mathlib/pull/13291))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_on_sum

Modified src/algebra/big_operators/fin.lean
- \+ *lemma* fin.prod_congr'
- \+ *lemma* fin.prod_trunc
- \+ *lemma* fin.prod_univ_add



## [2022-04-21 23:36:49](https://github.com/leanprover-community/mathlib/commit/4d7683b)
feat(group_theory/torsion): torsion-free groups and quotients by torsion subgroups ([#13173](https://github.com/leanprover-community/mathlib/pull/13173))
#### Estimated changes
Modified src/group_theory/torsion.lean
- \+ *lemma* is_torsion.not_torsion_free
- \+ *lemma* is_torsion_free.not_torsion
- \+ *lemma* is_torsion_free.prod
- \+ *lemma* is_torsion_free.quotient_torsion
- \+ *lemma* is_torsion_free.subgroup
- \+ *def* monoid.is_torsion_free
- \+ *lemma* monoid.not_is_torsion_free_iff
- \+ *lemma* monoid.not_is_torsion_iff



## [2022-04-21 23:36:48](https://github.com/leanprover-community/mathlib/commit/e728cfd)
feat(order/grade): Graded orders ([#11308](https://github.com/leanprover-community/mathlib/pull/11308))
Define graded orders. To be the most general, we use `is_min`/`is_max` rather than `order_bot`/`order_top`. A grade is a function that respects the covering relation and eventually minimality/maximality.
#### Estimated changes
Modified docs/references.bib


Modified src/data/fin/basic.lean
- \+ *lemma* fin.coe_strict_mono

Modified src/data/int/basic.lean
- \+ *lemma* int.coe_nat_strict_mono

Modified src/data/int/succ_pred.lean
- \+ *lemma* nat.cast_int_covby_iff

Modified src/data/nat/succ_pred.lean
- \+ *lemma* fin.coe_covby_iff

Added src/order/grade.lean
- \+ *lemma* covby_iff_lt_covby_grade
- \+ *def* grade
- \+ *lemma* grade_bot
- \+ *def* grade_bounded_order.lift_left
- \+ *def* grade_bounded_order.lift_right
- \+ *lemma* grade_covby_grade_iff
- \+ *lemma* grade_eq_grade_iff
- \+ *lemma* grade_injective
- \+ *lemma* grade_le_grade_iff
- \+ *lemma* grade_lt_grade_iff
- \+ *def* grade_max_order.lift_left
- \+ *def* grade_max_order.lift_right
- \+ *def* grade_min_order.fin_to_nat
- \+ *def* grade_min_order.lift_left
- \+ *def* grade_min_order.lift_right
- \+ *lemma* grade_mono
- \+ *lemma* grade_ne_grade_iff
- \+ *lemma* grade_of_dual
- \+ *def* grade_order.fin_to_nat
- \+ *def* grade_order.lift_left
- \+ *def* grade_order.lift_right
- \+ *lemma* grade_self
- \+ *lemma* grade_strict_mono
- \+ *lemma* grade_to_dual
- \+ *lemma* grade_top
- \+ *lemma* is_max_grade_iff
- \+ *lemma* is_min_grade_iff



## [2022-04-21 23:36:46](https://github.com/leanprover-community/mathlib/commit/8110ab9)
feat(number_theory/modular): fundamental domain part 2 ([#8985](https://github.com/leanprover-community/mathlib/pull/8985))
This completes the argument that the standard open domain `{z : |z|>1, |\Re(z)|<1/2}` is a fundamental domain for the action of `SL(2,\Z)` on `\H`. The first PR ([#8611](https://github.com/leanprover-community/mathlib/pull/8611)) showed that every point in the upper half plane has a representative inside its closure, and here we show that representatives in the open domain are unique.
#### Estimated changes
Modified src/algebra/group_power/order.lean
- \+ *lemma* pow_four_le_pow_two_of_pow_two_le

Modified src/algebra/order/group.lean
- \+ *lemma* abs_add'

Modified src/analysis/complex/upper_half_plane.lean
- \+ *lemma* upper_half_plane.c_mul_im_sq_le_norm_sq_denom

Modified src/data/int/basic.lean
- \+ *lemma* int.eq_one_or_neg_one_of_mul_eq_one'
- \+ *lemma* int.eq_one_or_neg_one_of_mul_eq_one
- \+ *lemma* int.one_le_abs

Modified src/data/int/cast.lean
- \+/\- *theorem* int.cast_abs
- \+ *lemma* int.cast_four
- \+ *lemma* int.cast_le_neg_one_of_neg
- \+/\- *theorem* int.cast_max
- \+/\- *theorem* int.cast_min
- \+/\- *lemma* int.cast_nat_abs
- \+ *lemma* int.cast_one_le_of_pos
- \+ *lemma* int.cast_three
- \+ *lemma* int.nneg_mul_add_sq_of_abs_le_one

Modified src/number_theory/modular.lean
- \- *def* modular_group.T'
- \+ *lemma* modular_group.abs_c_le_one
- \+ *lemma* modular_group.abs_two_mul_re_lt_one_of_mem_fdo
- \+ *lemma* modular_group.c_eq_zero
- \+ *lemma* modular_group.coe_S
- \+ *lemma* modular_group.coe_T
- \+ *lemma* modular_group.coe_T_inv
- \+ *lemma* modular_group.coe_T_zpow
- \+ *lemma* modular_group.coe_T_zpow_smul_eq
- \+/\- *lemma* modular_group.coe_smul
- \+/\- *lemma* modular_group.denom_apply
- \+ *lemma* modular_group.eq_smul_self_of_mem_fdo_mem_fdo
- \+ *lemma* modular_group.eq_zero_of_mem_fdo_of_T_zpow_mem_fdo
- \+ *lemma* modular_group.exists_eq_T_zpow_of_c_eq_zero
- \+/\- *lemma* modular_group.exists_max_im
- \+/\- *lemma* modular_group.exists_row_one_eq_and_min_re
- \+ *lemma* modular_group.exists_smul_mem_fd
- \- *lemma* modular_group.exists_smul_mem_fundamental_domain
- \+ *def* modular_group.fd
- \+ *def* modular_group.fdo
- \- *def* modular_group.fundamental_domain
- \+ *lemma* modular_group.g_eq_of_c_eq_one
- \+/\- *lemma* modular_group.im_lt_im_S_smul
- \+/\- *lemma* modular_group.im_smul
- \+/\- *lemma* modular_group.im_smul_eq_div_norm_sq
- \- *lemma* modular_group.lc_row0_apply'
- \+/\- *lemma* modular_group.neg_smul
- \+ *lemma* modular_group.norm_sq_S_smul_lt_one
- \+ *lemma* modular_group.one_lt_norm_sq_T_zpow_smul
- \+/\- *lemma* modular_group.re_smul
- \+/\- *lemma* modular_group.smul_coe
- \+/\- *lemma* modular_group.smul_eq_lc_row0_add
- \+/\- *lemma* modular_group.tendsto_abs_re_smul
- \+/\- *lemma* modular_group.tendsto_norm_sq_coprime_pair
- \+ *lemma* modular_group.three_lt_four_mul_im_sq_of_mem_fdo



## [2022-04-21 20:30:58](https://github.com/leanprover-community/mathlib/commit/ba556a7)
chore(algebra/algebra/spectrum): lemmas about the zero ring ([#13568](https://github.com/leanprover-community/mathlib/pull/13568))
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean
- \+ *lemma* spectrum.of_subsingleton
- \+ *lemma* spectrum.resolvent_set_of_subsingleton



## [2022-04-21 20:30:57](https://github.com/leanprover-community/mathlib/commit/8145333)
ci(gitpod): update leanproject version ([#13567](https://github.com/leanprover-community/mathlib/pull/13567))
#### Estimated changes
Modified .docker/gitpod/mathlib/Dockerfile




## [2022-04-21 20:30:56](https://github.com/leanprover-community/mathlib/commit/aeef727)
chore(set_theory/ordinal/basic): Small style tweaks ([#13561](https://github.com/leanprover-community/mathlib/pull/13561))
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean
- \+ *theorem* ordinal.type_lt
- \- *lemma* ordinal.type_lt



## [2022-04-21 20:30:55](https://github.com/leanprover-community/mathlib/commit/efab188)
refactor(group_theory/{submonoid, subsemigroup}/basic): move `mul_mem_class` ([#13559](https://github.com/leanprover-community/mathlib/pull/13559))
This moves `mul_mem_class` (and `add_mem_class`) from `group_theory/submonoid/basic` to `group_theory/subsemigroup/basic` so that `subsemigroup` can be an instance. We then protect `subsemigroup.mul_mem`. In addition, we add an induction principle for binary predicates to better parallel `group_theory/submonoid/basic`.
#### Estimated changes
Modified src/group_theory/submonoid/basic.lean


Modified src/group_theory/subsemigroup/basic.lean
- \+ *lemma* subsemigroup.closure_induction₂
- \- *theorem* subsemigroup.mul_mem



## [2022-04-21 20:30:54](https://github.com/leanprover-community/mathlib/commit/afe1421)
feat(data/nat/pow): add theorem `nat.pow_mod` ([#13551](https://github.com/leanprover-community/mathlib/pull/13551))
Add theorem that states `∀ (a b n : ℕ) : a ^ b % n = (a % n) ^ b % n`.
#### Estimated changes
Modified src/data/nat/pow.lean
- \+ *theorem* nat.pow_mod



## [2022-04-21 20:30:53](https://github.com/leanprover-community/mathlib/commit/090e59d)
feat(analysis/normed_space/operator_norm): norm of `lsmul` ([#13538](https://github.com/leanprover-community/mathlib/pull/13538))
* From the sphere eversion project
* Required for convolutions
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.op_norm_lsmul
- \+ *lemma* continuous_linear_map.op_norm_lsmul_le



## [2022-04-21 20:30:51](https://github.com/leanprover-community/mathlib/commit/8430aae)
feat(algebra/group_power/lemmas): More lemmas through `to_additive` ([#13537](https://github.com/leanprover-community/mathlib/pull/13537))
Use `to_additive` to generate a bunch of old `nsmul`/`zsmul` lemmas from new `pow`/`zpow` ones. Also protect `nat.nsmul_eq_mul` as it should have been.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *lemma* commute.self_zpow
- \- *theorem* commute.self_zpow
- \+/\- *lemma* commute.zpow_left
- \+/\- *lemma* commute.zpow_right
- \+ *lemma* commute.zpow_self
- \- *theorem* commute.zpow_self
- \+ *lemma* commute.zpow_zpow_self
- \- *theorem* commute.zpow_zpow_self
- \+/\- *lemma* semiconj_by.zpow_right

Modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* abs_add_eq_add_abs_iff
- \+/\- *lemma* abs_add_eq_add_abs_le
- \+/\- *lemma* abs_nsmul
- \+/\- *lemma* abs_zsmul
- \+/\- *lemma* commute.cast_int_mul_cast_int_mul
- \+/\- *lemma* commute.cast_int_mul_right
- \+/\- *theorem* commute.self_cast_int_mul
- \+/\- *theorem* commute.self_cast_int_mul_cast_int_mul
- \+/\- *theorem* commute.self_cast_nat_mul
- \+/\- *theorem* commute.self_cast_nat_mul_cast_nat_mul
- \- *theorem* nsmul_le_nsmul_iff
- \- *theorem* nsmul_lt_nsmul_iff
- \+ *lemma* one_lt_zpow'
- \+ *lemma* zpow_eq_zpow_iff'
- \+ *lemma* zpow_le_zpow'
- \+ *lemma* zpow_le_zpow
- \+ *lemma* zpow_le_zpow_iff'
- \+ *lemma* zpow_le_zpow_iff
- \+ *lemma* zpow_left_inj
- \+ *lemma* zpow_left_injective
- \+ *lemma* zpow_lt_zpow'
- \+ *lemma* zpow_lt_zpow
- \+ *lemma* zpow_lt_zpow_iff'
- \+ *lemma* zpow_lt_zpow_iff
- \+ *lemma* zpow_mono_left
- \+ *lemma* zpow_mono_right
- \+ *lemma* zpow_strict_mono_left
- \+ *lemma* zpow_strict_mono_right
- \- *lemma* zsmul_eq_zsmul_iff'
- \- *theorem* zsmul_le_zsmul'
- \- *theorem* zsmul_le_zsmul
- \- *theorem* zsmul_le_zsmul_iff'
- \- *theorem* zsmul_le_zsmul_iff
- \- *theorem* zsmul_lt_zsmul'
- \- *theorem* zsmul_lt_zsmul
- \- *theorem* zsmul_lt_zsmul_iff'
- \- *theorem* zsmul_lt_zsmul_iff
- \- *theorem* zsmul_mono_left
- \- *lemma* zsmul_mono_right
- \+ *lemma* zsmul_one
- \- *theorem* zsmul_one
- \- *lemma* zsmul_pos
- \- *lemma* zsmul_right_inj
- \- *lemma* zsmul_right_injective
- \- *theorem* zsmul_strict_mono_left
- \- *lemma* zsmul_strict_mono_right

Modified src/algebra/group_power/order.lean
- \+ *lemma* pow_le_pow_iff'
- \+ *lemma* pow_lt_pow_iff'
- \+ *lemma* pow_strict_mono_left

Modified src/data/nat/basic.lean
- \- *theorem* nat.nsmul_eq_mul

Modified src/data/nat/periodic.lean




## [2022-04-21 20:30:50](https://github.com/leanprover-community/mathlib/commit/08323cd)
feat(data/real/ennreal): `tsub` lemmas ([#13525](https://github.com/leanprover-community/mathlib/pull/13525))
Inherit lemmas about subtraction on `ℝ≥0∞` from `algebra.order.sub`. Generalize `add_le_cancellable.tsub_lt_self` in passing.
New `ennreal` lemmas
#### Estimated changes
Modified src/algebra/order/sub.lean
- \+/\- *lemma* tsub_lt_self

Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.add_div
- \- *lemma* ennreal.add_sub_self'
- \- *lemma* ennreal.add_sub_self

Modified src/measure_theory/measure/regular.lean


Modified src/topology/instances/ennreal.lean




## [2022-04-21 20:30:49](https://github.com/leanprover-community/mathlib/commit/3a06179)
refactor(category_theory): reverse simp lemmas about (co)forks ([#13519](https://github.com/leanprover-community/mathlib/pull/13519))
Makes `fork.ι` instead of `t.π.app zero` so that we avoid any unnecessary references to `walking_parallel_pair` in (co)fork  homs. This induces quite a lot of changes in other files, but I think it's worth the pain. The PR also changes `fork.is_limit.mk` to avoid stating redundant morphisms.
#### Estimated changes
Modified src/algebra/category/Module/kernels.lean


Modified src/analysis/normed/group/SemiNormedGroup/kernels.lean
- \+ *def* SemiNormedGroup.fork
- \- *def* SemiNormedGroup.parallel_pair_cone

Modified src/category_theory/abelian/basic.lean


Modified src/category_theory/abelian/non_preadditive.lean


Modified src/category_theory/idempotents/basic.lean


Modified src/category_theory/limits/preserves/shapes/equalizers.lean


Modified src/category_theory/limits/preserves/shapes/kernels.lean


Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+/\- *def* category_theory.limits.cocone_of_split_epi
- \+ *lemma* category_theory.limits.cocone_of_split_epi_π
- \+/\- *lemma* category_theory.limits.coequalizer.π_of_eq
- \+ *lemma* category_theory.limits.cofork.app_one_eq_π
- \+ *lemma* category_theory.limits.cofork.app_zero_eq_comp_π_left
- \+ *lemma* category_theory.limits.cofork.app_zero_eq_comp_π_right
- \+ *lemma* category_theory.limits.cofork.is_colimit.π_comp_desc
- \- *lemma* category_theory.limits.cofork.is_colimit.π_desc_of_π
- \- *lemma* category_theory.limits.cofork.left_app_one
- \- *lemma* category_theory.limits.cofork.right_app_one
- \+ *def* category_theory.limits.cofork.π
- \- *lemma* category_theory.limits.cofork.π_eq_app_one
- \+/\- *lemma* category_theory.limits.cofork.π_of_π
- \+/\- *def* category_theory.limits.cone_of_split_mono
- \+ *lemma* category_theory.limits.cone_of_split_mono_ι
- \+ *lemma* category_theory.limits.epi_of_is_colimit_cofork
- \- *lemma* category_theory.limits.epi_of_is_colimit_parallel_pair
- \+ *lemma* category_theory.limits.fork.app_one_eq_ι_comp_left
- \+ *lemma* category_theory.limits.fork.app_one_eq_ι_comp_right
- \+ *lemma* category_theory.limits.fork.app_zero_eq_ι
- \- *lemma* category_theory.limits.fork.app_zero_left
- \- *lemma* category_theory.limits.fork.app_zero_right
- \+/\- *lemma* category_theory.limits.fork.equalizer_ext
- \+ *lemma* category_theory.limits.fork.hom_comp_ι
- \+ *lemma* category_theory.limits.fork.is_limit.lift_comp_ι
- \- *lemma* category_theory.limits.fork.is_limit.lift_of_ι_ι
- \+ *def* category_theory.limits.fork.ι
- \- *lemma* category_theory.limits.fork.ι_eq_app_zero
- \+/\- *lemma* category_theory.limits.fork.ι_of_ι
- \+ *lemma* category_theory.limits.fork.π_comp_hom
- \+/\- *lemma* category_theory.limits.is_iso_colimit_cocone_parallel_pair_of_eq
- \+/\- *lemma* category_theory.limits.is_iso_colimit_cocone_parallel_pair_of_self
- \+/\- *lemma* category_theory.limits.is_iso_limit_cocone_parallel_pair_of_epi
- \+/\- *lemma* category_theory.limits.is_iso_limit_cone_parallel_pair_of_epi
- \+/\- *lemma* category_theory.limits.is_iso_limit_cone_parallel_pair_of_eq
- \+/\- *lemma* category_theory.limits.is_iso_limit_cone_parallel_pair_of_self
- \+ *lemma* category_theory.limits.mono_of_is_limit_fork
- \- *lemma* category_theory.limits.mono_of_is_limit_parallel_pair

Modified src/category_theory/limits/shapes/kernel_pair.lean


Modified src/category_theory/limits/shapes/kernels.lean
- \+/\- *def* category_theory.limits.cokernel.is_colimit_cocone_zero_cocone
- \- *def* category_theory.limits.cokernel.zero_cocone
- \+ *def* category_theory.limits.cokernel.zero_cokernel_cofork
- \- *lemma* category_theory.limits.cokernel_cofork.app_zero
- \+/\- *lemma* category_theory.limits.cokernel_cofork.condition
- \+ *lemma* category_theory.limits.cokernel_cofork.π_eq_zero
- \+/\- *def* category_theory.limits.kernel.is_limit_cone_zero_cone
- \- *def* category_theory.limits.kernel.zero_cone
- \+ *def* category_theory.limits.kernel.zero_kernel_fork

Modified src/category_theory/limits/shapes/multiequalizer.lean
- \+/\- *lemma* category_theory.limits.multicofork.condition
- \+/\- *lemma* category_theory.limits.multicofork.snd_app_right
- \- *lemma* category_theory.limits.multicofork.to_sigma_cofork_ι_app_one
- \- *lemma* category_theory.limits.multicofork.to_sigma_cofork_ι_app_zero
- \+ *lemma* category_theory.limits.multicofork.to_sigma_cofork_π
- \+/\- *lemma* category_theory.limits.multicofork.π_eq_app_right
- \+ *lemma* category_theory.limits.multifork.app_left_eq_ι
- \- *lemma* category_theory.limits.multifork.app_left_fst
- \- *lemma* category_theory.limits.multifork.app_left_snd
- \+ *lemma* category_theory.limits.multifork.app_right_eq_ι_comp_fst
- \+ *lemma* category_theory.limits.multifork.app_right_eq_ι_comp_snd
- \+ *lemma* category_theory.limits.multifork.hom_comp_ι
- \+/\- *lemma* category_theory.limits.multifork.pi_condition
- \+/\- *lemma* category_theory.limits.multifork.to_pi_fork_π_app_zero
- \+/\- *def* category_theory.limits.multifork.ι
- \- *lemma* category_theory.limits.multifork.ι_eq_app_left

Modified src/category_theory/limits/shapes/normal_mono/equalizers.lean


Modified src/category_theory/limits/shapes/regular_mono.lean


Modified src/category_theory/limits/shapes/split_coequalizer.lean
- \+ *lemma* category_theory.is_split_coequalizer.as_cofork_π

Modified src/category_theory/monad/coequalizer.lean
- \+ *lemma* category_theory.monad.beck_coequalizer_desc
- \+ *lemma* category_theory.monad.beck_cofork_π

Modified src/category_theory/monad/monadicity.lean
- \+ *lemma* category_theory.monad.monadicity_internal.unit_cofork_π

Modified src/category_theory/preadditive/default.lean


Modified src/category_theory/sites/limits.lean


Modified src/category_theory/sites/sheaf.lean


Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean




## [2022-04-21 17:29:16](https://github.com/leanprover-community/mathlib/commit/b7cba57)
chore(set_theory/game/*): Protect ambiguous lemmas ([#13557](https://github.com/leanprover-community/mathlib/pull/13557))
Protect `pgame.neg_zero` and inline `pgame.add_le_add_left` and friends into `covariant_class` instances.
#### Estimated changes
Modified src/set_theory/game/basic.lean
- \- *theorem* game.add_le_add_left

Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/pgame.lean
- \- *theorem* pgame.add_le_add_left
- \- *theorem* pgame.add_le_add_right
- \- *theorem* pgame.add_lt_add_left
- \- *theorem* pgame.add_lt_add_right
- \- *theorem* pgame.neg_neg
- \- *theorem* pgame.neg_zero
- \- *def* pgame.relabelling.restricted:
- \+ *def* pgame.relabelling.restricted
- \- *theorem* pgame.zero_lt_half

Modified src/set_theory/surreal/basic.lean


Modified src/set_theory/surreal/dyadic.lean




## [2022-04-21 17:29:14](https://github.com/leanprover-community/mathlib/commit/b6c96ef)
feat(combinatorics/simple_graph/clique): Clique-free graphs ([#13552](https://github.com/leanprover-community/mathlib/pull/13552))
... and the finset of cliques of a finite graph.
#### Estimated changes
Modified src/combinatorics/simple_graph/clique.lean
- \+ *def* simple_graph.clique_finset
- \+ *lemma* simple_graph.clique_finset_eq_empty_iff
- \+ *lemma* simple_graph.clique_finset_mono
- \+ *lemma* simple_graph.clique_free.anti
- \+ *lemma* simple_graph.clique_free.mono
- \+ *def* simple_graph.clique_free
- \+ *lemma* simple_graph.clique_free_bot
- \+ *lemma* simple_graph.is_3_clique_iff
- \+ *lemma* simple_graph.is_3_clique_triple_iff
- \+ *lemma* simple_graph.is_clique_bot_iff
- \+/\- *lemma* simple_graph.is_clique_iff
- \+ *lemma* simple_graph.is_n_clique_bot_iff
- \+ *lemma* simple_graph.mem_clique_finset_iff

Modified src/data/set/pairwise.lean
- \+ *lemma* set.pairwise_bot_iff



## [2022-04-21 17:29:13](https://github.com/leanprover-community/mathlib/commit/e49ac91)
feat(analysis/calculus/cont_diff): add more prod lemmas ([#13521](https://github.com/leanprover-community/mathlib/pull/13521))
* Add `cont_diff.fst`, `cont_diff.comp₂`, `cont_diff_prod_mk_left` and many variants.
* From the sphere eversion project
* Required for convolutions
* PR [#13423](https://github.com/leanprover-community/mathlib/pull/13423) is similar for continuity
#### Estimated changes
Modified src/analysis/calculus/cont_diff.lean
- \+/\- *lemma* cont_diff.comp_cont_diff_at
- \+ *lemma* cont_diff.comp₂
- \+ *lemma* cont_diff.comp₃
- \+/\- *lemma* cont_diff.cont_diff_at
- \+/\- *lemma* cont_diff.cont_diff_on
- \+/\- *lemma* cont_diff.cont_diff_within_at
- \+/\- *lemma* cont_diff.continuous
- \+/\- *lemma* cont_diff.differentiable
- \+ *lemma* cont_diff.fst'
- \+ *lemma* cont_diff.fst
- \+/\- *lemma* cont_diff.of_le
- \+ *lemma* cont_diff.of_succ
- \+ *lemma* cont_diff.one_of_succ
- \+ *lemma* cont_diff.snd'
- \+ *lemma* cont_diff.snd
- \+/\- *lemma* cont_diff_all_iff_nat
- \+ *lemma* cont_diff_apply
- \+ *lemma* cont_diff_apply_apply
- \+ *lemma* cont_diff_at.fst''
- \+ *lemma* cont_diff_at.fst'
- \+ *lemma* cont_diff_at.fst
- \+ *lemma* cont_diff_at.snd''
- \+ *lemma* cont_diff_at.snd'
- \+ *lemma* cont_diff_at.snd
- \+/\- *lemma* cont_diff_at_fst
- \+/\- *lemma* cont_diff_at_snd
- \+/\- *lemma* cont_diff_at_zero
- \+/\- *lemma* cont_diff_iff_cont_diff_at
- \+ *lemma* cont_diff_on.fst
- \+ *lemma* cont_diff_on.snd
- \+/\- *lemma* cont_diff_on_fst
- \+/\- *lemma* cont_diff_on_snd
- \+/\- *theorem* cont_diff_on_univ
- \+ *lemma* cont_diff_prod_mk_left
- \+ *lemma* cont_diff_prod_mk_right
- \+/\- *lemma* cont_diff_top
- \+/\- *lemma* cont_diff_zero

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_at_prod_mk_left
- \+ *lemma* has_fderiv_at_prod_mk_right



## [2022-04-21 17:29:12](https://github.com/leanprover-community/mathlib/commit/62b3333)
chore(algebra/star/chsh): `repeat`ed golf ([#13499](https://github.com/leanprover-community/mathlib/pull/13499))
Instead of having a real Gröbner tactic, we can leverage a loop of `ring, simp` to reach a goal.
#### Estimated changes
Modified src/algebra/star/chsh.lean
- \+ *lemma* CHSH_id



## [2022-04-21 17:29:11](https://github.com/leanprover-community/mathlib/commit/777d1ec)
feat(measure_theory/measure/measure_space): add some lemmas for the counting measure ([#13485](https://github.com/leanprover-community/mathlib/pull/13485))
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.measure.count_apply_eq_top
- \+/\- *lemma* measure_theory.measure.count_apply_lt_top
- \+ *lemma* measure_theory.measure.count_empty
- \+ *lemma* measure_theory.measure.count_eq_zero_iff
- \+ *lemma* measure_theory.measure.count_ne_zero
- \+ *lemma* measure_theory.measure.count_singleton
- \+ *lemma* measure_theory.measure.empty_of_count_eq_zero



## [2022-04-21 17:29:10](https://github.com/leanprover-community/mathlib/commit/6490ee3)
feat(topology/instances/ennreal): Add lemmas about continuity of ennreal subtraction. ([#13448](https://github.com/leanprover-community/mathlib/pull/13448))
`ennreal` does not have continuous `sub`. This PR adds `ennreal.continuous_on_sub` and related lemmas, which give the continuity of the subtraction in more restricted/specialized setups.
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.continuous_nnreal_sub
- \+ *lemma* ennreal.continuous_on_sub
- \+ *lemma* ennreal.continuous_on_sub_left
- \+ *lemma* ennreal.continuous_sub_left
- \+ *lemma* ennreal.continuous_sub_right



## [2022-04-21 15:20:01](https://github.com/leanprover-community/mathlib/commit/91cbe46)
feat(algebra/monoid_algebra/basic): lifts of (add_)monoid_algebras ([#13382](https://github.com/leanprover-community/mathlib/pull/13382))
We show that homomorphisms of the grading (add) monoids of (add) monoid algebras lift to ring/algebra homs of the algebras themselves.
This PR is preparation for introducing Laurent polynomials (see [adomani_laurent_polynomials](https://github.com/leanprover-community/mathlib/tree/adomani_laurent_polynomials), file `data/polynomial/laurent` for a preliminary version).
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Laurent.20polynomials)
#### Estimated changes
Modified src/algebra/monoid_algebra/basic.lean
- \+ *def* add_monoid_algebra.map_domain_alg_hom
- \+ *lemma* add_monoid_algebra.map_domain_algebra_map
- \+ *def* add_monoid_algebra.map_domain_non_unital_alg_hom
- \+ *def* add_monoid_algebra.map_domain_ring_hom
- \+ *def* monoid_algebra.map_domain_alg_hom
- \+ *lemma* monoid_algebra.map_domain_algebra_map
- \+ *def* monoid_algebra.map_domain_non_unital_alg_hom
- \+ *def* monoid_algebra.map_domain_ring_hom
- \+/\- *lemma* monoid_algebra.ring_hom_ext'
- \+/\- *lemma* monoid_algebra.ring_hom_ext
- \+/\- *def* monoid_algebra.single_one_ring_hom



## [2022-04-21 15:19:59](https://github.com/leanprover-community/mathlib/commit/8044794)
feat(topology/algebra/module/basic): continuous linear maps are automatically uniformly continuous ([#13276](https://github.com/leanprover-community/mathlib/pull/13276))
Generalize `continuous_linear_map.uniform_continuous`, `continuous_linear_equiv.uniform_embedding` and `linear_equiv.uniform_embedding` form `normed_space`s to `uniform_add_group`s and move them to `topology/algebra/module/basic`.
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* continuous_linear_equiv.uniform_embedding
- \+/\- *lemma* continuous_linear_map.homothety_norm
- \+/\- *theorem* continuous_linear_map.op_norm_zero_iff
- \- *lemma* linear_equiv.uniform_embedding
- \+/\- *lemma* linear_isometry.norm_to_continuous_linear_map
- \+/\- *lemma* linear_isometry.norm_to_continuous_linear_map_comp
- \+/\- *lemma* linear_map.bound_of_shell

Modified src/topology/algebra/module/basic.lean


Modified src/topology/uniform_space/uniform_embedding.lean
- \+ *lemma* equiv.uniform_embedding



## [2022-04-21 15:19:58](https://github.com/leanprover-community/mathlib/commit/79abf67)
fix(tactic/apply_rules): separate single rules and attribute names in syntax ([#13227](https://github.com/leanprover-community/mathlib/pull/13227))
@hrmacbeth reported an issue with `apply_rules` [on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/monotonicity.2Eattr.20with.20apply_rules). It boiled down to `apply_rules` not properly distinguishing between attribute names, the names of `user_attribute` declarations, and the names of normal declarations. There's an example of using `apply_rules` with attributes in the docs:
```lean
@[user_attribute]
meta def mono_rules : user_attribute :=
{ name := `mono_rules,
  descr := "lemmas usable to prove monotonicity" }
local attribute [mono_rules] add_le_add
example (a b c d : α) : a + b ≤ c + d :=
begin
  apply_rules mono_rules, -- takes action
end
```
but this only worked by coincidence because the attribute name and the name of the `user_attribute` declaration were the same.
With this change, expressions and names of attributes are now separated: the latter are specified after `with`. The call above becomes `apply_rules with mono_rules`. This mirrors the syntax of `simp`. Note that this feature was only used in meta code in mathlib.
The example from Zulip (modified for proper syntax) still doesn't work with my change:
```lean
import tactic.monotonicity
variables {α : Type*} [linear_ordered_add_comm_group α]
example (a b c d : α) : a + b ≤ c + d :=
begin
  apply_rules with mono,
end
```
but it seems to fail because the `mono` rules cause `apply_rules` to loop -- that is, the rule set is getting applied correctly.
#### Estimated changes
Modified src/measure_theory/tactic.lean


Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Modified src/topology/tactic.lean


Modified test/apply_rules.lean




## [2022-04-21 15:19:56](https://github.com/leanprover-community/mathlib/commit/e8b581a)
feat(order/countable_dense_linear_order): Relax conditions of `embedding_from_countable_to_dense` ([#12928](https://github.com/leanprover-community/mathlib/pull/12928))
We prove that any countable order embeds in any nontrivial dense order. We also slightly golf the rest of the file.
#### Estimated changes
Modified src/order/countable_dense_linear_order.lean
- \+ *theorem* order.embedding_from_countable_to_dense
- \- *def* order.embedding_from_countable_to_dense
- \+ *theorem* order.iso_of_countable_dense
- \- *def* order.iso_of_countable_dense



## [2022-04-21 12:10:04](https://github.com/leanprover-community/mathlib/commit/0f9edf9)
feat(data/set/[basic|prod]): make `×ˢ` bind more strongly, and define `mem.out` ([#13422](https://github.com/leanprover-community/mathlib/pull/13422))
* This means that  `×ˢ` does not behave the same as `∪` or `∩` around `⁻¹'` or `''`, but I think that is fine.
* From the sphere eversion project
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.has_mem.mem.out
- \+ *lemma* set.mem_set_of
- \+/\- *theorem* set.mem_set_of_eq
- \+/\- *theorem* set.nmem_set_of_eq

Modified src/data/set/pointwise.lean
- \+/\- *lemma* set.image_div_prod
- \+/\- *lemma* set.image_mul_prod
- \+/\- *lemma* set.image_smul_prod
- \+/\- *lemma* set.image_vsub_prod

Modified src/data/set/prod.lean
- \+/\- *lemma* set.fst_image_prod
- \+/\- *lemma* set.fst_image_prod_subset
- \+/\- *lemma* set.image_prod
- \+/\- *lemma* set.image_swap_prod
- \+/\- *lemma* set.mk_preimage_prod_left
- \+/\- *lemma* set.mk_preimage_prod_left_eq_empty
- \+/\- *lemma* set.mk_preimage_prod_right
- \+/\- *lemma* set.mk_preimage_prod_right_eq_empty
- \+/\- *lemma* set.preimage_swap_prod
- \+/\- *lemma* set.prod_eq_empty_iff
- \+/\- *lemma* set.prod_subset_iff
- \+/\- *lemma* set.snd_image_prod
- \+/\- *lemma* set.snd_image_prod_subset

Modified src/logic/equiv/fin.lean


Modified src/logic/equiv/set.lean
- \+/\- *lemma* equiv.prod_comm_image

Modified src/measure_theory/constructions/prod.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/measurable_space.lean


Modified src/order/filter/basic.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2022-04-21 12:10:02](https://github.com/leanprover-community/mathlib/commit/c956647)
feat(order/basic): Simple shortcut lemmas ([#13421](https://github.com/leanprover-community/mathlib/pull/13421))
Add convenience lemmas to make the API a bit more symmetric and easier to translate between `transitive` and `is_trans`. Also rename `_ge'` to `_le` in lemmas and fix the `is_max_` aliases.
#### Estimated changes
Modified src/algebra/order/floor.lean
- \+/\- *lemma* nat.lt_of_floor_lt

Modified src/algebra/parity.lean


Modified src/analysis/special_functions/pow.lean


Modified src/data/real/hyperreal.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/order/basic.lean
- \+/\- *lemma* eq.not_gt
- \+/\- *lemma* eq.not_lt
- \- *lemma* eq.trans_le
- \+/\- *lemma* ge_antisymm
- \+/\- *lemma* ge_iff_le
- \+/\- *lemma* gt_iff_lt
- \- *lemma* has_le.le.trans_eq
- \+ *lemma* le_of_eq_of_le'
- \+ *lemma* le_of_eq_of_le
- \+ *lemma* le_of_le_of_eq'
- \+ *lemma* le_of_le_of_eq
- \+/\- *lemma* le_rfl
- \+ *lemma* le_trans'
- \- *lemma* lt_iff_not_ge'
- \+ *lemma* lt_iff_not_le
- \+ *lemma* lt_of_eq_of_lt'
- \+ *lemma* lt_of_eq_of_lt
- \+ *lemma* lt_of_le_of_lt'
- \+ *lemma* lt_of_le_of_ne'
- \+ *lemma* lt_of_lt_of_eq'
- \+ *lemma* lt_of_lt_of_eq
- \+ *lemma* lt_of_lt_of_le'
- \- *lemma* lt_of_not_ge'
- \+ *lemma* lt_of_not_le
- \+/\- *lemma* lt_self_iff_false
- \+ *lemma* lt_trans'
- \+ *lemma* ne.lt_of_le'
- \+ *lemma* ne.lt_of_le

Modified src/order/bounded.lean


Modified src/order/bounded_order.lean


Modified src/order/rel_classes.lean
- \+ *lemma* of_eq
- \+ *lemma* transitive_ge
- \+ *lemma* transitive_gt
- \+ *lemma* transitive_le
- \+ *lemma* transitive_lt
- \+ *lemma* transitive_of_trans

Modified src/ring_theory/perfection.lean


Modified src/ring_theory/polynomial/basic.lean


Modified test/finish4.lean




## [2022-04-21 12:10:00](https://github.com/leanprover-community/mathlib/commit/22c4291)
chore(number_theory/dioph): Cleanup ([#13403](https://github.com/leanprover-community/mathlib/pull/13403))
Clean up, including:
* Move prerequisites to the correct files
* Make equalities in `poly` operations defeq
* Remove defeq abuse around `set`
* Slightly golf proofs by tweaking explicitness of lemma arguments
Renames
#### Estimated changes
Modified src/control/traversable/instances.lean


Modified src/data/int/basic.lean
- \+ *lemma* int.eq_nat_abs_iff_mul_eq_zero

Modified src/data/list/basic.lean
- \+ *lemma* list.all₂.imp
- \+ *lemma* list.all₂_cons
- \+ *lemma* list.all₂_iff_forall
- \+ *lemma* list.all₂_map_iff

Modified src/data/list/defs.lean
- \+ *def* list.all₂

Modified src/data/option/basic.lean
- \+ *def* option.cons
- \+ *lemma* option.cons_none_some

Modified src/number_theory/dioph.lean
- \+ *lemma* dioph.abs_poly_dioph
- \- *theorem* dioph.abs_poly_dioph
- \+ *lemma* dioph.add_dioph
- \- *theorem* dioph.add_dioph
- \- *theorem* dioph.and_dioph
- \+ *lemma* dioph.dioph_comp2
- \- *theorem* dioph.dioph_comp2
- \+ *lemma* dioph.dioph_comp
- \- *theorem* dioph.dioph_comp
- \+/\- *def* dioph.dioph_fn
- \+ *lemma* dioph.dioph_fn_comp2
- \- *theorem* dioph.dioph_fn_comp2
- \+ *lemma* dioph.dioph_fn_comp
- \- *theorem* dioph.dioph_fn_comp
- \+ *lemma* dioph.dioph_fn_compn
- \- *theorem* dioph.dioph_fn_compn
- \+ *lemma* dioph.dioph_fn_vec
- \- *theorem* dioph.dioph_fn_vec
- \+ *lemma* dioph.dioph_fn_vec_comp1
- \- *theorem* dioph.dioph_fn_vec_comp1
- \+ *lemma* dioph.dioph_list.all₂
- \- *theorem* dioph.dioph_list_all
- \+/\- *def* dioph.dioph_pfun
- \+ *lemma* dioph.dioph_pfun_vec
- \- *theorem* dioph.dioph_pfun_vec
- \+ *lemma* dioph.div_dioph
- \- *theorem* dioph.div_dioph
- \+ *lemma* dioph.dvd_dioph
- \- *theorem* dioph.dvd_dioph
- \+ *lemma* dioph.eq_dioph
- \- *theorem* dioph.eq_dioph
- \+ *lemma* dioph.ex1_dioph
- \- *theorem* dioph.ex1_dioph
- \+ *lemma* dioph.ex_dioph
- \- *theorem* dioph.ex_dioph
- \+ *lemma* dioph.ext
- \- *theorem* dioph.ext
- \+ *lemma* dioph.inject_dummies
- \- *theorem* dioph.inject_dummies
- \+ *lemma* dioph.inter
- \+ *lemma* dioph.le_dioph
- \- *theorem* dioph.le_dioph
- \+ *lemma* dioph.lt_dioph
- \- *theorem* dioph.lt_dioph
- \+ *lemma* dioph.mod_dioph
- \- *theorem* dioph.mod_dioph
- \+ *lemma* dioph.modeq_dioph
- \- *theorem* dioph.modeq_dioph
- \+ *lemma* dioph.mul_dioph
- \- *theorem* dioph.mul_dioph
- \+ *lemma* dioph.ne_dioph
- \- *theorem* dioph.ne_dioph
- \+ *lemma* dioph.of_no_dummies
- \- *theorem* dioph.of_no_dummies
- \- *theorem* dioph.or_dioph
- \+ *lemma* dioph.pell_dioph
- \- *theorem* dioph.pell_dioph
- \+/\- *theorem* dioph.pow_dioph
- \+/\- *theorem* dioph.proj_dioph
- \+/\- *theorem* dioph.proj_dioph_of_nat
- \+ *lemma* dioph.reindex_dioph
- \- *theorem* dioph.reindex_dioph
- \+ *lemma* dioph.reindex_dioph_fn
- \- *theorem* dioph.reindex_dioph_fn
- \+ *lemma* dioph.sub_dioph
- \- *theorem* dioph.sub_dioph
- \+ *lemma* dioph.union
- \+ *lemma* dioph.xn_dioph
- \- *theorem* dioph.xn_dioph
- \- *lemma* int.eq_nat_abs_iff_mul
- \+ *lemma* is_poly.add
- \+ *lemma* is_poly.neg
- \- *theorem* list_all.imp
- \- *def* list_all
- \- *theorem* list_all_congr
- \- *theorem* list_all_cons
- \- *theorem* list_all_iff_forall
- \- *theorem* list_all_map
- \- *def* option.cons
- \- *theorem* option.cons_head_tail
- \- *def* poly.add
- \+ *lemma* poly.add_apply
- \- *theorem* poly.add_eval
- \+ *lemma* poly.coe_add
- \+ *lemma* poly.coe_mul
- \+ *lemma* poly.coe_neg
- \+ *lemma* poly.coe_one
- \+ *lemma* poly.coe_sub
- \+ *lemma* poly.coe_zero
- \+ *lemma* poly.const_apply
- \- *theorem* poly.const_eval
- \+/\- *lemma* poly.ext
- \- *lemma* poly.isp
- \+ *def* poly.map
- \+ *lemma* poly.map_apply
- \- *def* poly.mul
- \+ *lemma* poly.mul_apply
- \- *theorem* poly.mul_eval
- \- *def* poly.neg
- \+ *lemma* poly.neg_apply
- \- *theorem* poly.neg_eval
- \- *def* poly.one
- \+ *lemma* poly.one_apply
- \- *theorem* poly.one_eval
- \+ *lemma* poly.proj_apply
- \- *theorem* poly.proj_eval
- \- *def* poly.remap
- \- *theorem* poly.remap_eval
- \- *def* poly.sub
- \+ *lemma* poly.sub_apply
- \- *theorem* poly.sub_eval
- \- *def* poly.subst
- \- *theorem* poly.subst_eval
- \+ *lemma* poly.sumsq_eq_zero
- \- *theorem* poly.sumsq_eq_zero
- \+ *lemma* poly.sumsq_nonneg
- \- *theorem* poly.sumsq_nonneg
- \- *def* poly.zero
- \+ *lemma* poly.zero_apply
- \- *theorem* poly.zero_eval
- \- *def* sum.join



## [2022-04-21 12:09:59](https://github.com/leanprover-community/mathlib/commit/e5f8236)
feat(analysis/normed_space/exponential): ring homomorphisms are preserved by the exponential ([#13402](https://github.com/leanprover-community/mathlib/pull/13402))
The new results here are:
* `prod.fst_exp`
* `prod.snd_exp`
* `exp_units_conj`
* `exp_conj`
* `map_exp`
* `map_exp_of_mem_ball`
This last lemma does all the heavy lifting, and also lets us golf `algebra_map_exp_comm`.
This doesn't bother to duplicate the rest of these lemmas for the `*_of_mem_ball` version, since the proofs are trivial and those lemmas probably wouldn't be used.
This also generalizes some of the lemmas about infinite sums to work with `add_monoid_hom_class`.
#### Estimated changes
Modified src/analysis/normed_space/exponential.lean
- \+ *lemma* exp_conj'
- \+ *lemma* exp_conj
- \+ *lemma* exp_smul
- \+ *lemma* exp_units_conj'
- \+ *lemma* exp_units_conj
- \+ *lemma* map_exp
- \+ *lemma* map_exp_of_mem_ball
- \+ *lemma* prod.fst_exp
- \+ *lemma* prod.snd_exp

Modified src/topology/algebra/group.lean


Modified src/topology/algebra/infinite_sum.lean




## [2022-04-21 12:09:58](https://github.com/leanprover-community/mathlib/commit/0821eef)
feat(algebraic_geometry/projective_spectrum): degree zero part of a localized ring ([#13398](https://github.com/leanprover-community/mathlib/pull/13398))
If we have a graded ring A and some element f of A, the the localised ring A away from f has a degree zero part. This construction is useful because proj locally is spec of degree zero part of some localised ring.
Perhaps this ring belongs to some other file or different name, suggestions are very welcome
#### Estimated changes
Added src/algebraic_geometry/projective_spectrum/scheme.lean
- \+ *def* algebraic_geometry.degree_zero_part.deg
- \+ *lemma* algebraic_geometry.degree_zero_part.eq
- \+ *lemma* algebraic_geometry.degree_zero_part.mul_val
- \+ *def* algebraic_geometry.degree_zero_part.num
- \+ *lemma* algebraic_geometry.degree_zero_part.num_mem
- \+ *def* algebraic_geometry.degree_zero_part



## [2022-04-21 12:09:57](https://github.com/leanprover-community/mathlib/commit/f1091b3)
feat(set_theory/cardinal): A set of cardinals is small iff it's bounded ([#13373](https://github.com/leanprover-community/mathlib/pull/13373))
We move `mk_subtype_le` and `mk_set_le` earlier within the file in order to better accomodate for the new result, `bdd_above_iff_small`.  We need this result right above the `Sup` stuff, as we'll make heavy use of it in a following refactor for `cardinal.sup`.
#### Estimated changes
Modified src/set_theory/cardinal/basic.lean
- \+ *theorem* cardinal.bdd_above_iff_small
- \+ *theorem* cardinal.mk_set_le
- \- *lemma* cardinal.mk_set_le

Modified src/set_theory/ordinal/basic.lean




## [2022-04-21 12:09:56](https://github.com/leanprover-community/mathlib/commit/c30131f)
feat(data/polynomial/{derivative, iterated_deriv}): reduce assumptions ([#13368](https://github.com/leanprover-community/mathlib/pull/13368))
#### Estimated changes
Modified src/data/polynomial/derivative.lean
- \- *lemma* polynomial.derivative_C_mul
- \+/\- *lemma* polynomial.derivative_smul
- \+/\- *lemma* polynomial.iterate_derivative_smul

Modified src/data/polynomial/iterated_deriv.lean
- \+/\- *lemma* polynomial.iterated_deriv_smul



## [2022-04-21 12:09:55](https://github.com/leanprover-community/mathlib/commit/761801f)
feat(algebra/monoid_algebra/grading): Use the new graded_algebra API ([#13360](https://github.com/leanprover-community/mathlib/pull/13360))
This removes `to_grades_by` and `of_grades_by`, and prefers `graded_algebra.decompose` as the canonical spelling.
This might undo some of the performance improvements in [#13169](https://github.com/leanprover-community/mathlib/pull/13169), but it's not clear where to apply the analogous changes here, or whether they're really needed any more anyway,
#### Estimated changes
Modified src/algebra/monoid_algebra/grading.lean
- \+ *def* add_monoid_algebra.decompose_aux
- \+ *lemma* add_monoid_algebra.decompose_aux_coe
- \+ *lemma* add_monoid_algebra.decompose_aux_eq_decompose
- \+ *lemma* add_monoid_algebra.decompose_aux_single
- \- *def* add_monoid_algebra.equiv_grades
- \- *def* add_monoid_algebra.equiv_grades_by
- \+ *lemma* add_monoid_algebra.grade.decompose_single
- \+ *lemma* add_monoid_algebra.grades_by.decompose_single
- \- *def* add_monoid_algebra.of_grades
- \- *def* add_monoid_algebra.of_grades_by
- \- *lemma* add_monoid_algebra.of_grades_by_comp_to_grades_by
- \- *lemma* add_monoid_algebra.of_grades_by_of
- \- *lemma* add_monoid_algebra.of_grades_by_to_grades_by
- \- *lemma* add_monoid_algebra.of_grades_comp_to_grades
- \- *lemma* add_monoid_algebra.of_grades_of
- \- *lemma* add_monoid_algebra.of_grades_to_grades
- \+/\- *lemma* add_monoid_algebra.single_mem_grade_by
- \- *def* add_monoid_algebra.to_grades
- \- *def* add_monoid_algebra.to_grades_by
- \- *lemma* add_monoid_algebra.to_grades_by_coe
- \- *lemma* add_monoid_algebra.to_grades_by_comp_of_grades_by
- \- *lemma* add_monoid_algebra.to_grades_by_of_grades_by
- \- *lemma* add_monoid_algebra.to_grades_by_single'
- \- *lemma* add_monoid_algebra.to_grades_by_single
- \- *lemma* add_monoid_algebra.to_grades_coe
- \- *lemma* add_monoid_algebra.to_grades_comp_of_grades
- \- *lemma* add_monoid_algebra.to_grades_of_grades
- \- *lemma* add_monoid_algebra.to_grades_single



## [2022-04-21 12:09:54](https://github.com/leanprover-community/mathlib/commit/5c2088e)
feat(algebra/group/to_additive): let @[to_additive] mimic alias’s docstrings ([#13330](https://github.com/leanprover-community/mathlib/pull/13330))
many of our `nolint.txt` entires are due to code of this shape:
    @[to_additive add_foo]
    lemma foo := .. /- no docstring -/
    alias foo <- bar
    attribute [to_additive add_bar] bar
where now `bar` has a docstring (from `alias`), but `bar_add` does not.
This PR makes `to_additive` detect that `bar` is an alias, and unless an 
explicit docstring is passed to `to_additive`, creates an “alias of add_foo”
docstring.
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/data/buffer/parser/basic.lean


Modified src/tactic/alias.lean


Modified test/lint_to_additive_doc.lean




## [2022-04-21 12:09:53](https://github.com/leanprover-community/mathlib/commit/7d61199)
feat(set_theory/cofinality): Basic fundamental sequences ([#13326](https://github.com/leanprover-community/mathlib/pull/13326))
#### Estimated changes
Modified src/set_theory/cardinal/cofinality.lean
- \+ *theorem* ordinal.is_fundamental_sequence_id_of_le_cof
- \+ *theorem* ordinal.is_fundamental_sequence_succ
- \+ *theorem* ordinal.is_fundamental_sequence_zero



## [2022-04-21 12:09:51](https://github.com/leanprover-community/mathlib/commit/ba455ea)
feat(special_functions/pow): continuity of real to complex power ([#13244](https://github.com/leanprover-community/mathlib/pull/13244))
Some lemmas excised from my Gamma-function project. The main result is that for a complex `s` with `re s > 0`, the function `(λ x, x ^ s : ℝ → ℂ)` is continuous on all of `ℝ`.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* complex.continuous_at_cpow_const_of_re_pos
- \+ *lemma* complex.continuous_at_cpow_of_re_pos
- \+ *lemma* complex.continuous_of_real_cpow_const
- \+ *lemma* complex.of_real_cpow_of_nonpos

Modified src/data/complex/basic.lean
- \+ *lemma* complex.not_lt_iff
- \+ *lemma* complex.not_lt_zero_iff



## [2022-04-21 12:09:50](https://github.com/leanprover-community/mathlib/commit/cf3b996)
feat(group_theory/torsion): extension closedness, and torsion scalars in modules ([#13172](https://github.com/leanprover-community/mathlib/pull/13172))
Co-authored by: Alex J. Best <alex.j.best@gmail.com>
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* is_of_fin_order.apply
- \- *lemma* is_of_fin_order.quotient
- \+/\- *lemma* is_of_fin_order_iff_coe
- \+ *lemma* monoid_hom.is_of_fin_order

Modified src/group_theory/torsion.lean
- \+ *lemma* add_monoid.is_torsion.module_of_fintype
- \+ *lemma* add_monoid.is_torsion.module_of_torsion
- \+/\- *lemma* exponent_exists.is_torsion
- \+ *lemma* is_torsion.extension_closed
- \+ *lemma* is_torsion.of_surjective
- \- *lemma* is_torsion.quotient_group
- \+ *lemma* is_torsion.quotient_iff



## [2022-04-21 12:09:49](https://github.com/leanprover-community/mathlib/commit/82ef19a)
feat(category_theory/path_category): canonical quotient of a path category ([#13159](https://github.com/leanprover-community/mathlib/pull/13159))
#### Estimated changes
Modified src/category_theory/path_category.lean
- \+ *lemma* category_theory.compose_path_comp'
- \+ *lemma* category_theory.compose_path_id
- \+ *lemma* category_theory.compose_path_to_path
- \+ *def* category_theory.path_composition
- \+ *def* category_theory.paths_hom_rel
- \+ *def* category_theory.quotient_paths_equiv
- \+ *def* category_theory.quotient_paths_to
- \+ *def* category_theory.to_quotient_paths

Modified src/category_theory/quotient.lean
- \+ *lemma* category_theory.quotient.comp_closure.of



## [2022-04-21 12:09:48](https://github.com/leanprover-community/mathlib/commit/8261501)
refactor(number_theory/padics/padic_norm): Switch nat and rat definitions ([#12454](https://github.com/leanprover-community/mathlib/pull/12454))
Switches the order in which `padic_val_nat` and `padic_val_rat` are defined.
This PR has also expanded to add `padic_val_int` and some API lemmas for that.
#### Estimated changes
Modified src/number_theory/padics/padic_norm.lean
- \+/\- *lemma* dvd_of_one_le_padic_val_nat
- \+ *lemma* padic_val_int.eq_zero_of_not_dvd
- \+ *lemma* padic_val_int.mul
- \+ *lemma* padic_val_int.of_nat
- \+ *lemma* padic_val_int.of_ne_one_ne_zero
- \+ *lemma* padic_val_int.self
- \+ *def* padic_val_int
- \+ *lemma* padic_val_int_dvd
- \+ *lemma* padic_val_int_dvd_iff
- \+ *lemma* padic_val_int_mul_eq_succ
- \+ *lemma* padic_val_int_self
- \+ *lemma* padic_val_nat.eq_zero_of_not_dvd
- \+ *lemma* padic_val_nat.self
- \+/\- *lemma* padic_val_nat_def
- \+ *lemma* padic_val_nat_dvd_iff
- \- *lemma* padic_val_nat_of_not_dvd
- \- *lemma* padic_val_nat_one
- \- *lemma* padic_val_nat_zero
- \+ *lemma* padic_val_rat.multiplicity_sub_multiplicity
- \+ *lemma* padic_val_rat.of_int
- \+ *lemma* padic_val_rat.of_int_multiplicity
- \+ *lemma* padic_val_rat.of_nat
- \- *lemma* padic_val_rat.padic_val_rat_of_int
- \- *lemma* padic_val_rat.padic_val_rat_self
- \+ *lemma* padic_val_rat.self
- \- *lemma* padic_val_rat_def
- \+/\- *lemma* padic_val_rat_of_nat
- \+/\- *lemma* zero_le_padic_val_rat_of_nat

Modified src/number_theory/padics/padic_numbers.lean




## [2022-04-21 11:02:58](https://github.com/leanprover-community/mathlib/commit/21bbe90)
feat(analysis/normed): more lemmas about the sup norm on pi types and matrices ([#13536](https://github.com/leanprover-community/mathlib/pull/13536))
For now we name the matrix lemmas as `matrix.norm_*` and `matrix.nnnorm_*` to match `matrix.norm_le_iff` and `matrix.nnnorm_le_iff`.
We should consider renaming these in future to indicate which norm they refer to, but should probably deal with agreeing on a name in a separate PR.
#### Estimated changes
Modified src/analysis/matrix.lean
- \+ *lemma* matrix.nnnorm_col
- \+ *lemma* matrix.nnnorm_diagonal
- \+ *lemma* matrix.nnnorm_map_eq
- \+ *lemma* matrix.nnnorm_row
- \+ *lemma* matrix.nnnorm_transpose
- \+ *lemma* matrix.norm_col
- \+ *lemma* matrix.norm_diagonal
- \+ *lemma* matrix.norm_map_eq
- \+ *lemma* matrix.norm_row
- \+ *lemma* matrix.norm_transpose

Modified src/analysis/normed/group/basic.lean
- \+ *lemma* pi.nnnorm_def
- \+ *lemma* pi.norm_def

Modified src/analysis/normed/normed_field.lean


Modified src/analysis/normed_space/star/matrix.lean
- \- *lemma* matrix.entrywise_sup_norm_star_eq_norm
- \+ *lemma* matrix.nnnorm_conj_transpose
- \+ *lemma* matrix.norm_conj_transpose



## [2022-04-21 11:02:57](https://github.com/leanprover-community/mathlib/commit/b87e193)
fix(category_theory/monoidal): improve hygiene in coherence tactic ([#13507](https://github.com/leanprover-community/mathlib/pull/13507))
#### Estimated changes
Modified src/category_theory/monoidal/coherence.lean




## [2022-04-21 11:02:56](https://github.com/leanprover-community/mathlib/commit/9f22a36)
feat(src/number_theory/cyclotomic/discriminant): add discr_prime_pow_ne_two ([#13465](https://github.com/leanprover-community/mathlib/pull/13465))
We add `discr_prime_pow_ne_two`, the discriminant of the `p^n`-th cyclotomic field.
From flt-regular
#### Estimated changes
Modified src/number_theory/cyclotomic/discriminant.lean
- \+ *lemma* is_cyclotomic_extension.discr_prime_pow_ne_two

Modified src/number_theory/cyclotomic/primitive_roots.lean
- \+ *lemma* is_primitive_root.pow_sub_one_norm_prime_pow_of_one_le



## [2022-04-21 08:48:23](https://github.com/leanprover-community/mathlib/commit/16ecb3d)
chore(algebra/group/type_tags): missing simp lemmas ([#13553](https://github.com/leanprover-community/mathlib/pull/13553))
To have `simps` generate these in an appropriate form, this inserts explicits coercions between the type synonyms.
#### Estimated changes
Modified src/algebra/group/type_tags.lean
- \+/\- *def* add_monoid_hom.to_multiplicative''
- \+/\- *def* add_monoid_hom.to_multiplicative'
- \+/\- *def* add_monoid_hom.to_multiplicative
- \+/\- *def* monoid_hom.to_additive''
- \+/\- *def* monoid_hom.to_additive'
- \+/\- *def* monoid_hom.to_additive



## [2022-04-21 08:48:22](https://github.com/leanprover-community/mathlib/commit/839f508)
feat(measure_theory): allow measurability to prove ae_strongly_measurable ([#13427](https://github.com/leanprover-community/mathlib/pull/13427))
Adds `measurable.ae_strongly_measurable` to the `measurability` list
#### Estimated changes
Modified src/measure_theory/tactic.lean




## [2022-04-21 06:55:01](https://github.com/leanprover-community/mathlib/commit/6012c21)
refactor(algebra/hom/group): generalize a few lemmas to `monoid_hom_class` ([#13447](https://github.com/leanprover-community/mathlib/pull/13447))
This generalizes a few lemmas to `monoid_hom_class` from `monoid_hom`. In particular, `monoid_hom.injective_iff` has been generalized and renamed to `injective_iff_map_eq_one`.
This also deletes `add_monoid_hom.injective_iff`, `ring_hom.injective_iff` and `alg_hom.injective_iff`. All of these are superseded by the generically applicable `injective_iff_map_eq_zero`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *theorem* alg_hom.injective_iff

Modified src/algebra/field/basic.lean


Modified src/algebra/group/ext.lean


Modified src/algebra/hom/group.lean
- \+ *lemma* injective_iff_map_eq_one'
- \+ *lemma* injective_iff_map_eq_one
- \+ *theorem* map_div'
- \+/\- *lemma* monoid_hom.eq_on_inv
- \- *lemma* monoid_hom.injective_iff'
- \- *lemma* monoid_hom.injective_iff
- \- *theorem* monoid_hom.map_div'
- \+/\- *lemma* monoid_hom.map_exists_left_inv
- \+/\- *lemma* monoid_hom.map_exists_right_inv
- \- *lemma* monoid_hom.map_mul_eq_one

Modified src/algebra/module/basic.lean


Modified src/algebra/ring/basic.lean
- \- *theorem* ring_hom.injective_iff'
- \- *theorem* ring_hom.injective_iff

Modified src/algebraic_geometry/function_field.lean


Modified src/algebraic_geometry/properties.lean


Modified src/data/polynomial/eval.lean


Modified src/data/zmod/basic.lean


Modified src/field_theory/abel_ruffini.lean


Modified src/field_theory/intermediate_field.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/field_theory/polynomial_galois_group.lean


Modified src/field_theory/ratfunc.lean


Modified src/field_theory/splitting_field.lean


Modified src/group_theory/free_product.lean


Modified src/group_theory/perm/basic.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/linear_algebra/matrix/charpoly/coeff.lean


Modified src/number_theory/class_number/finite.lean


Modified src/number_theory/function_field.lean


Modified src/number_theory/zsqrtd/basic.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/algebraic_independent.lean


Modified src/ring_theory/dedekind_domain/ideal.lean


Modified src/ring_theory/dedekind_domain/integral_closure.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/ideal/over.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/localization/basic.lean


Modified src/ring_theory/localization/integral.lean


Modified src/ring_theory/nullstellensatz.lean


Modified src/ring_theory/polynomial/eisenstein.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/roots_of_unity.lean


Modified test/import_order_timeout.lean




## [2022-04-21 03:36:38](https://github.com/leanprover-community/mathlib/commit/e0f78ab)
chore(data/list/cycle): Add basic `simp` lemmas + minor golfing ([#13533](https://github.com/leanprover-community/mathlib/pull/13533))
#### Estimated changes
Modified src/data/list/cycle.lean
- \+ *lemma* cycle.card_to_multiset
- \+/\- *def* cycle.nil
- \+/\- *lemma* cycle.nil_to_multiset
- \+ *lemma* cycle.to_finset_eq_nil
- \+ *theorem* cycle.to_finset_to_multiset
- \+ *lemma* cycle.to_multiset_eq_nil

Modified src/data/multiset/basic.lean
- \+/\- *theorem* multiset.coe_eq_zero



## [2022-04-21 03:36:36](https://github.com/leanprover-community/mathlib/commit/2f1a4af)
feat(algebra/hom/non_unital_alg): introduce notation for non-unital algebra homomorphisms ([#13470](https://github.com/leanprover-community/mathlib/pull/13470))
This introduces the notation `A →ₙₐ[R] B` for `non_unital_alg_hom R A B` to mirror that of `non_unital_ring_hom R S` as `R →ₙ+* S` from [#13430](https://github.com/leanprover-community/mathlib/pull/13430). Here, the `ₙ` stands for "non-unital".
#### Estimated changes
Modified src/algebra/algebra/unitization.lean
- \+/\- *def* unitization.lift

Modified src/algebra/free_non_unital_non_assoc_algebra.lean
- \+/\- *lemma* free_non_unital_non_assoc_algebra.hom_ext
- \+/\- *def* free_non_unital_non_assoc_algebra.lift
- \+/\- *lemma* free_non_unital_non_assoc_algebra.lift_comp_of
- \+/\- *lemma* free_non_unital_non_assoc_algebra.lift_symm_apply

Modified src/algebra/hom/non_unital_alg.lean
- \+/\- *def* alg_hom.to_non_unital_alg_hom
- \+/\- *lemma* non_unital_alg_hom.coe_comp
- \+/\- *lemma* non_unital_alg_hom.coe_distrib_mul_action_hom_mk
- \+/\- *lemma* non_unital_alg_hom.coe_inverse
- \+/\- *lemma* non_unital_alg_hom.coe_mul_hom_mk
- \+/\- *lemma* non_unital_alg_hom.coe_one
- \+/\- *lemma* non_unital_alg_hom.coe_to_distrib_mul_action_hom
- \+/\- *lemma* non_unital_alg_hom.coe_to_mul_hom
- \+/\- *lemma* non_unital_alg_hom.coe_zero
- \+/\- *def* non_unital_alg_hom.comp
- \+/\- *lemma* non_unital_alg_hom.comp_apply
- \+/\- *lemma* non_unital_alg_hom.congr_fun
- \+/\- *lemma* non_unital_alg_hom.ext
- \+/\- *lemma* non_unital_alg_hom.ext_iff
- \+/\- *def* non_unital_alg_hom.inverse
- \+/\- *lemma* non_unital_alg_hom.map_add
- \+/\- *lemma* non_unital_alg_hom.map_mul
- \+/\- *lemma* non_unital_alg_hom.map_smul
- \+/\- *lemma* non_unital_alg_hom.map_zero
- \+/\- *lemma* non_unital_alg_hom.mk_coe
- \+/\- *lemma* non_unital_alg_hom.one_apply
- \+/\- *lemma* non_unital_alg_hom.to_distrib_mul_action_hom_eq_coe
- \+/\- *lemma* non_unital_alg_hom.to_distrib_mul_action_hom_injective
- \+/\- *lemma* non_unital_alg_hom.to_fun_eq_coe
- \+/\- *lemma* non_unital_alg_hom.to_mul_hom_eq_coe
- \+/\- *lemma* non_unital_alg_hom.to_mul_hom_injective
- \+/\- *lemma* non_unital_alg_hom.zero_apply

Modified src/algebra/lie/free.lean
- \+/\- *def* free_lie_algebra.mk

Modified src/algebra/lie/non_unital_non_assoc_algebra.lean
- \+/\- *def* lie_hom.to_non_unital_alg_hom

Modified src/algebra/monoid_algebra/basic.lean


Modified src/topology/algebra/module/character_space.lean
- \+/\- *def* weak_dual.character_space.to_non_unital_alg_hom

Modified src/topology/continuous_function/zero_at_infty.lean




## [2022-04-21 01:41:41](https://github.com/leanprover-community/mathlib/commit/c93b99f)
chore(algebra/group/defs): Declare `field_simps` attribute earlier ([#13543](https://github.com/leanprover-community/mathlib/pull/13543))
Declaring `field_simps` earlier make the relevant lemmas taggable as they are declared.
#### Estimated changes
Modified src/algebra/field/basic.lean


Modified src/algebra/group/basic.lean


Modified src/algebra/group/defs.lean


Modified src/algebra/group_with_zero/basic.lean




## [2022-04-20 22:44:21](https://github.com/leanprover-community/mathlib/commit/b2518be)
feat(analysis/normed/normed_field): add `one_le_(nn)norm_one` for nontrivial normed rings ([#13556](https://github.com/leanprover-community/mathlib/pull/13556))
#### Estimated changes
Modified src/analysis/normed/normed_field.lean
- \+ *lemma* one_le_nnnorm_one
- \+ *lemma* one_le_norm_one



## [2022-04-20 22:44:20](https://github.com/leanprover-community/mathlib/commit/81c8f31)
refactor(analysis/calculus/cont_diff): reorder the file ([#13468](https://github.com/leanprover-community/mathlib/pull/13468))
* There are no functional changes in this PR (except the order of implicit arguments in some lemmas)
* This PR tries to move `cont_diff.comp` above some other lemmas. In a follow-up PR I will use this to add lemmas like `cont_diff.fst` which requires `cont_diff.comp`, but after this PR we can add it near `cont_diff_fst`.
* We also add `{m n : with_top ℕ}` as variables, so that we don't have to repeat this in every lemma
#### Estimated changes
Modified src/analysis/calculus/cont_diff.lean
- \+/\- *lemma* cont_diff.add
- \+/\- *lemma* cont_diff.comp
- \+/\- *lemma* cont_diff.comp_cont_diff_on
- \+/\- *lemma* cont_diff.comp_continuous_linear_map
- \+/\- *lemma* cont_diff.cont_diff_at
- \+/\- *lemma* cont_diff.cont_diff_fderiv_apply
- \+/\- *lemma* cont_diff.cont_diff_on
- \+/\- *lemma* cont_diff.cont_diff_within_at
- \+/\- *lemma* cont_diff.continuous
- \+/\- *lemma* cont_diff.continuous_deriv
- \+/\- *lemma* cont_diff.continuous_fderiv
- \+/\- *lemma* cont_diff.continuous_fderiv_apply
- \+/\- *lemma* cont_diff.continuous_linear_map_comp
- \+/\- *lemma* cont_diff.differentiable
- \+/\- *lemma* cont_diff.mul
- \+/\- *lemma* cont_diff.neg
- \+/\- *lemma* cont_diff.of_le
- \+/\- *lemma* cont_diff.pow
- \+/\- *lemma* cont_diff.prod
- \+/\- *lemma* cont_diff.prod_map
- \+/\- *lemma* cont_diff.smul
- \+/\- *lemma* cont_diff.sub
- \+/\- *lemma* cont_diff_add
- \+/\- *lemma* cont_diff_at.add
- \+/\- *lemma* cont_diff_at.comp
- \+/\- *lemma* cont_diff_at.congr_of_eventually_eq
- \+/\- *lemma* cont_diff_at.cont_diff_within_at
- \+/\- *lemma* cont_diff_at.continuous_at
- \+/\- *lemma* cont_diff_at.continuous_linear_map_comp
- \+/\- *lemma* cont_diff_at.differentiable_at
- \+/\- *lemma* cont_diff_at.has_strict_deriv_at
- \+/\- *lemma* cont_diff_at.has_strict_fderiv_at
- \+/\- *lemma* cont_diff_at.mul
- \+/\- *lemma* cont_diff_at.neg
- \+/\- *lemma* cont_diff_at.of_le
- \+/\- *lemma* cont_diff_at.pow
- \+/\- *lemma* cont_diff_at.prod
- \+/\- *lemma* cont_diff_at.smul
- \+/\- *lemma* cont_diff_at.sub
- \+/\- *lemma* cont_diff_at_const
- \+/\- *lemma* cont_diff_at_fst
- \+/\- *lemma* cont_diff_at_id
- \+/\- *lemma* cont_diff_at_map_inverse
- \+/\- *lemma* cont_diff_at_of_subsingleton
- \+/\- *lemma* cont_diff_at_ring_inverse
- \+/\- *lemma* cont_diff_at_snd
- \+/\- *lemma* cont_diff_const
- \+/\- *lemma* cont_diff_fst
- \+/\- *lemma* cont_diff_id
- \+/\- *lemma* cont_diff_iff_cont_diff_at
- \+/\- *lemma* cont_diff_iff_continuous_differentiable
- \+/\- *lemma* cont_diff_mul
- \+/\- *lemma* cont_diff_neg
- \+/\- *lemma* cont_diff_of_differentiable_iterated_fderiv
- \+/\- *lemma* cont_diff_of_subsingleton
- \+/\- *lemma* cont_diff_on.add
- \+/\- *lemma* cont_diff_on.comp_continuous_linear_map
- \+/\- *lemma* cont_diff_on.congr
- \+/\- *lemma* cont_diff_on.congr_mono
- \+/\- *lemma* cont_diff_on.cont_diff_within_at
- \+/\- *lemma* cont_diff_on.continuous_linear_map_comp
- \+/\- *lemma* cont_diff_on.continuous_on
- \+/\- *lemma* cont_diff_on.continuous_on_deriv_of_open
- \+/\- *lemma* cont_diff_on.continuous_on_deriv_within
- \+/\- *lemma* cont_diff_on.continuous_on_fderiv_of_open
- \+/\- *lemma* cont_diff_on.continuous_on_fderiv_within
- \+/\- *lemma* cont_diff_on.continuous_on_iterated_fderiv_within
- \+/\- *lemma* cont_diff_on.deriv_of_open
- \+/\- *lemma* cont_diff_on.deriv_within
- \+/\- *lemma* cont_diff_on.differentiable_on
- \+/\- *lemma* cont_diff_on.differentiable_on_iterated_fderiv_within
- \+/\- *lemma* cont_diff_on.fderiv_of_open
- \+/\- *lemma* cont_diff_on.fderiv_within
- \+/\- *theorem* cont_diff_on.ftaylor_series_within
- \+/\- *lemma* cont_diff_on.mono
- \+/\- *lemma* cont_diff_on.mul
- \+/\- *lemma* cont_diff_on.neg
- \+/\- *lemma* cont_diff_on.of_le
- \+/\- *lemma* cont_diff_on.pow
- \+/\- *lemma* cont_diff_on.prod
- \+/\- *lemma* cont_diff_on.smul
- \+/\- *lemma* cont_diff_on.sub
- \+/\- *lemma* cont_diff_on_congr
- \+/\- *lemma* cont_diff_on_const
- \+/\- *lemma* cont_diff_on_fst
- \+/\- *lemma* cont_diff_on_id
- \+/\- *lemma* cont_diff_on_iff_continuous_on_differentiable_on
- \+/\- *lemma* cont_diff_on_iff_forall_nat_le
- \+/\- *theorem* cont_diff_on_iff_ftaylor_series
- \+/\- *lemma* cont_diff_on_of_continuous_on_differentiable_on
- \+/\- *lemma* cont_diff_on_of_differentiable_on
- \+/\- *lemma* cont_diff_on_of_locally_cont_diff_on
- \+/\- *lemma* cont_diff_on_of_subsingleton
- \+/\- *lemma* cont_diff_on_snd
- \+/\- *theorem* cont_diff_on_univ
- \+/\- *lemma* cont_diff_smul
- \+/\- *lemma* cont_diff_snd
- \+/\- *lemma* cont_diff_within_at.add
- \+/\- *lemma* cont_diff_within_at.comp'
- \+/\- *lemma* cont_diff_within_at.comp_continuous_linear_map
- \+/\- *lemma* cont_diff_within_at.congr'
- \+/\- *lemma* cont_diff_within_at.congr
- \+/\- *lemma* cont_diff_within_at.congr_nhds
- \+/\- *lemma* cont_diff_within_at.congr_of_eventually_eq'
- \+/\- *lemma* cont_diff_within_at.congr_of_eventually_eq
- \+/\- *lemma* cont_diff_within_at.cont_diff_at
- \+/\- *lemma* cont_diff_within_at.cont_diff_on
- \+/\- *lemma* cont_diff_within_at.continuous_linear_map_comp
- \+/\- *lemma* cont_diff_within_at.continuous_within_at
- \+/\- *lemma* cont_diff_within_at.differentiable_within_at'
- \+/\- *lemma* cont_diff_within_at.differentiable_within_at
- \+/\- *lemma* cont_diff_within_at.mono
- \+/\- *lemma* cont_diff_within_at.mono_of_mem
- \+/\- *lemma* cont_diff_within_at.mul
- \+/\- *lemma* cont_diff_within_at.neg
- \+/\- *lemma* cont_diff_within_at.of_le
- \+/\- *lemma* cont_diff_within_at.pow
- \+/\- *lemma* cont_diff_within_at.prod
- \+/\- *lemma* cont_diff_within_at.smul
- \+/\- *lemma* cont_diff_within_at.sub
- \+/\- *lemma* cont_diff_within_at_congr_nhds
- \+/\- *lemma* cont_diff_within_at_const
- \+/\- *lemma* cont_diff_within_at_fst
- \+/\- *lemma* cont_diff_within_at_id
- \+/\- *lemma* cont_diff_within_at_iff_forall_nat_le
- \+/\- *lemma* cont_diff_within_at_inter'
- \+/\- *lemma* cont_diff_within_at_inter
- \+/\- *lemma* cont_diff_within_at_of_subsingleton
- \+/\- *lemma* cont_diff_within_at_snd
- \+/\- *theorem* cont_diff_within_at_univ
- \+/\- *lemma* cont_diff_zero_fun
- \+/\- *lemma* continuous_linear_equiv.cont_diff
- \+/\- *lemma* continuous_linear_equiv.cont_diff_on_comp_iff
- \+/\- *lemma* continuous_linear_equiv.cont_diff_within_at_comp_iff
- \+/\- *lemma* continuous_linear_map.cont_diff
- \+/\- *lemma* filter.eventually_eq.cont_diff_within_at_iff
- \+/\- *lemma* has_ftaylor_series_up_to.continuous
- \+/\- *lemma* has_ftaylor_series_up_to.differentiable
- \+/\- *lemma* has_ftaylor_series_up_to.has_fderiv_at
- \+/\- *lemma* has_ftaylor_series_up_to.has_ftaylor_series_up_to_on
- \+/\- *lemma* has_ftaylor_series_up_to.of_le
- \+/\- *lemma* has_ftaylor_series_up_to.zero_eq'
- \+/\- *lemma* has_ftaylor_series_up_to_on.comp_continuous_linear_map
- \+/\- *lemma* has_ftaylor_series_up_to_on.congr
- \+/\- *lemma* has_ftaylor_series_up_to_on.continuous_linear_map_comp
- \+/\- *lemma* has_ftaylor_series_up_to_on.continuous_on
- \+/\- *lemma* has_ftaylor_series_up_to_on.differentiable_at
- \+/\- *lemma* has_ftaylor_series_up_to_on.differentiable_on
- \+/\- *theorem* has_ftaylor_series_up_to_on.eq_ftaylor_series_of_unique_diff_on
- \+/\- *lemma* has_ftaylor_series_up_to_on.eventually_has_fderiv_at
- \+/\- *lemma* has_ftaylor_series_up_to_on.has_fderiv_at
- \+/\- *lemma* has_ftaylor_series_up_to_on.has_fderiv_within_at
- \+/\- *lemma* has_ftaylor_series_up_to_on.mono
- \+/\- *lemma* has_ftaylor_series_up_to_on.of_le
- \+/\- *lemma* has_ftaylor_series_up_to_on.prod
- \+/\- *lemma* has_ftaylor_series_up_to_on.zero_eq'
- \+/\- *lemma* has_ftaylor_series_up_to_on_univ_iff
- \+/\- *lemma* is_bounded_bilinear_map.cont_diff
- \+/\- *lemma* is_bounded_linear_map.cont_diff
- \+/\- *lemma* linear_isometry.cont_diff
- \+/\- *lemma* linear_isometry_equiv.cont_diff
- \+/\- *theorem* local_homeomorph.cont_diff_at_symm
- \+/\- *theorem* local_homeomorph.cont_diff_at_symm_deriv



## [2022-04-20 21:15:06](https://github.com/leanprover-community/mathlib/commit/b86b927)
move(set_theory/*): Organize in folders ([#13530](https://github.com/leanprover-community/mathlib/pull/13530))
Create folders `cardinal`, `ordinal` and `game`. Most files under `set_theory` belong to a least one of them.
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified src/algebra/quaternion.lean


Modified src/category_theory/limits/small_complete.lean


Modified src/combinatorics/configuration.lean


Modified src/computability/encoding.lean


Modified src/data/W/cardinal.lean


Modified src/data/nat/count.lean


Modified src/data/rat/denumerable.lean


Modified src/data/real/cardinality.lean


Modified src/field_theory/cardinality.lean


Modified src/group_theory/free_product.lean


Modified src/group_theory/index.lean


Modified src/group_theory/solvable.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/measure_theory/card_measurable_space.lean


Modified src/measure_theory/covering/besicovitch.lean


Modified src/model_theory/basic.lean


Modified src/model_theory/encoding.lean


Modified src/ring_theory/localization/cardinality.lean


Renamed src/set_theory/cardinal.lean to src/set_theory/cardinal/basic.lean


Renamed src/set_theory/cofinality.lean to src/set_theory/cardinal/cofinality.lean


Renamed src/set_theory/continuum.lean to src/set_theory/cardinal/continuum.lean


Renamed src/set_theory/cardinal_divisibility.lean to src/set_theory/cardinal/divisibility.lean


Renamed src/set_theory/fincard.lean to src/set_theory/cardinal/finite.lean


Renamed src/set_theory/cardinal_ordinal.lean to src/set_theory/cardinal/ordinal.lean


Renamed src/set_theory/game.lean to src/set_theory/game/basic.lean


Modified src/set_theory/game/nim.lean


Renamed src/set_theory/pgame.lean to src/set_theory/game/pgame.lean


Modified src/set_theory/game/short.lean


Modified src/set_theory/game/winner.lean


Renamed src/set_theory/ordinal_arithmetic.lean to src/set_theory/ordinal/arithmetic.lean


Renamed src/set_theory/ordinal.lean to src/set_theory/ordinal/basic.lean


Renamed src/set_theory/fixed_points.lean to src/set_theory/ordinal/fixed_point.lean


Renamed src/set_theory/ordinal_notation.lean to src/set_theory/ordinal/notation.lean


Renamed src/set_theory/principal.lean to src/set_theory/ordinal/principal.lean


Renamed src/set_theory/ordinal_topology.lean to src/set_theory/ordinal/topology.lean


Modified src/set_theory/surreal/basic.lean


Modified src/topology/metric_space/emetric_paracompact.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/partition_of_unity.lean




## [2022-04-20 20:40:18](https://github.com/leanprover-community/mathlib/commit/741d285)
chore(number_theory/zsqrtd/basic): simplify le_total proof ([#13555](https://github.com/leanprover-community/mathlib/pull/13555))
#### Estimated changes
Modified src/number_theory/zsqrtd/basic.lean




## [2022-04-20 18:42:11](https://github.com/leanprover-community/mathlib/commit/9d6d8c2)
feat(group_theory/perm/basic): Iterating a permutation is the same as taking a power ([#13554](https://github.com/leanprover-community/mathlib/pull/13554))
#### Estimated changes
Modified src/group_theory/perm/basic.lean
- \+ *lemma* equiv.perm.iterate_eq_pow
- \+/\- *lemma* equiv.perm.zpow_apply_comm



## [2022-04-20 18:42:10](https://github.com/leanprover-community/mathlib/commit/27a8328)
feat(data/real/sqrt): `sqrt x < y ↔ x < y^2` ([#13546](https://github.com/leanprover-community/mathlib/pull/13546))
Prove `real.sqrt_lt_iff` and generalize `real.lt_sqrt`.
#### Estimated changes
Modified src/data/complex/basic.lean


Modified src/data/real/sqrt.lean
- \+ *lemma* real.le_sqrt'
- \- *theorem* real.le_sqrt'
- \+ *lemma* real.lt_sqrt
- \- *theorem* real.lt_sqrt
- \+ *lemma* real.sq_lt
- \- *theorem* real.sq_lt
- \+ *lemma* real.sqrt_lt'
- \+ *lemma* real.sqrt_lt



## [2022-04-20 18:42:09](https://github.com/leanprover-community/mathlib/commit/242d687)
feat(algebra/hom/group and *): introduce `mul_hom M N` notation `M →ₙ* N` ([#13526](https://github.com/leanprover-community/mathlib/pull/13526))
The discussion and poll related to this new notation can be found in this [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/ring_hom.20notation.20and.20friends/near/279313301)
#### Estimated changes
Modified src/algebra/category/Semigroup/basic.lean
- \+/\- *def* Magma.of_hom
- \+/\- *lemma* Magma.of_hom_apply
- \+/\- *def* Semigroup.of_hom
- \+/\- *lemma* Semigroup.of_hom_apply

Modified src/algebra/divisibility.lean
- \+/\- *lemma* mul_hom.map_dvd

Modified src/algebra/free.lean
- \+/\- *def* free_magma.lift
- \+/\- *theorem* free_magma.lift_aux_unique

Modified src/algebra/group/pi.lean
- \+/\- *def* mul_hom.single

Modified src/algebra/group/prod.lean
- \+/\- *lemma* mul_hom.coe_prod
- \+/\- *def* mul_hom.coprod
- \+/\- *def* mul_hom.fst
- \+/\- *lemma* mul_hom.fst_comp_prod
- \+/\- *lemma* mul_hom.prod_apply
- \+/\- *lemma* mul_hom.prod_comp_prod_map
- \+/\- *def* mul_hom.prod_map
- \+/\- *lemma* mul_hom.prod_unique
- \+/\- *def* mul_hom.snd
- \+/\- *lemma* mul_hom.snd_comp_prod
- \+/\- *def* mul_mul_hom

Modified src/algebra/group/with_one.lean
- \+/\- *def* with_one.coe_mul_hom
- \+/\- *def* with_one.lift
- \+/\- *def* with_one.map
- \+/\- *lemma* with_one.map_coe
- \+/\- *lemma* with_one.map_comp
- \+/\- *lemma* with_one.map_map

Modified src/algebra/hom/equiv.lean
- \+/\- *def* mul_hom.inverse

Modified src/algebra/hom/group.lean
- \+/\- *lemma* mul_hom.coe_inj
- \+/\- *lemma* mul_hom.ext
- \+/\- *lemma* mul_hom.ext_iff
- \+/\- *def* mul_hom.id
- \+/\- *lemma* mul_hom.to_fun_eq_coe

Modified src/algebra/hom/non_unital_alg.lean


Modified src/algebra/monoid_algebra/basic.lean
- \+/\- *def* add_monoid_algebra.of_magma
- \+/\- *def* monoid_algebra.of_magma

Modified src/algebra/order/absolute_value.lean


Modified src/data/fintype/basic.lean


Modified src/data/set/pointwise.lean
- \+/\- *def* set.singleton_mul_hom

Modified src/group_theory/group_action/prod.lean


Modified src/group_theory/subsemigroup/basic.lean
- \+/\- *def* mul_hom.eq_mlocus
- \+/\- *lemma* mul_hom.eq_of_eq_on_mdense
- \+/\- *lemma* mul_hom.eq_of_eq_on_mtop
- \+/\- *lemma* mul_hom.eq_on_mclosure

Modified src/tactic/simps.lean


Modified src/topology/algebra/group.lean
- \+/\- *def* nhds_mul_hom

Modified src/topology/continuous_function/zero_at_infty.lean




## [2022-04-20 17:09:57](https://github.com/leanprover-community/mathlib/commit/7bfaa5c)
feat(group_theory/schreier): Schreier's lemma in terms of `group.fg` and `group.rank` ([#13361](https://github.com/leanprover-community/mathlib/pull/13361))
This PR adds statements of Schreier's lemma in terms of `group.fg` and `group.rank`.
#### Estimated changes
Modified src/group_theory/schreier.lean
- \+ *lemma* subgroup.exists_finset_card_le_mul
- \+ *lemma* subgroup.fg_of_index_ne_zero
- \+ *lemma* subgroup.rank_le_index_mul_rank



## [2022-04-20 17:09:56](https://github.com/leanprover-community/mathlib/commit/b0805a5)
feat(linear_algebra/trace): dual_tensor_hom is an equivalence + basis-free characterization of the trace ([#10372](https://github.com/leanprover-community/mathlib/pull/10372))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.single_smul
- \+ *lemma* finsupp.sum_univ_single'
- \+ *lemma* finsupp.sum_univ_single

Modified src/data/matrix/basis.lean
- \+ *lemma* matrix.std_basis_matrix.diag_same

Modified src/linear_algebra/contraction.lean
- \+ *lemma* dual_tensor_hom_equiv_of_basis_to_linear_map
- \+ *theorem* to_matrix_dual_tensor_hom

Modified src/linear_algebra/dual.lean
- \+ *lemma* basis.sum_dual_apply_smul_coord

Modified src/linear_algebra/tensor_product_basis.lean
- \+ *lemma* basis.tensor_product_apply'
- \+ *lemma* basis.tensor_product_apply

Modified src/linear_algebra/trace.lean
- \+ *theorem* linear_map.trace_eq_contract'
- \+ *theorem* linear_map.trace_eq_contract
- \+ *lemma* linear_map.trace_eq_contract_of_basis'
- \+ *lemma* linear_map.trace_eq_contract_of_basis

Modified src/representation_theory/basic.lean
- \+/\- *theorem* representation.char_one



## [2022-04-20 16:01:13](https://github.com/leanprover-community/mathlib/commit/311ca72)
feat(order/filter/basic): allow functions between different types in lemmas about [co]map by a constant function ([#13542](https://github.com/leanprover-community/mathlib/pull/13542))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.comap_const_of_mem
- \+/\- *lemma* filter.comap_const_of_not_mem
- \+/\- *lemma* filter.map_const



## [2022-04-20 14:05:05](https://github.com/leanprover-community/mathlib/commit/d79f6f3)
feat(data/finset/basic): simp `to_finset_eq_empty` ([#13531](https://github.com/leanprover-community/mathlib/pull/13531))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+/\- *theorem* multiset.to_finset_eq_empty



## [2022-04-20 12:56:15](https://github.com/leanprover-community/mathlib/commit/8ba7df8)
feat(topology/algebra/algebra): ℚ-scalar multiplication is continuous ([#13458](https://github.com/leanprover-community/mathlib/pull/13458))
#### Estimated changes
Modified src/topology/algebra/algebra.lean




## [2022-04-20 10:38:26](https://github.com/leanprover-community/mathlib/commit/a3a166b)
chore(model_theory/encoding): Improve the encoding of terms  ([#13532](https://github.com/leanprover-community/mathlib/pull/13532))
Makes it so that the encoding of terms no longer requires the assumption `inhabited (L.term A)`.
Adjusts following lemmas to use the `encoding` API more directly.
#### Estimated changes
Modified src/model_theory/encoding.lean
- \+/\- *theorem* first_order.language.term.card_le
- \+/\- *def* first_order.language.term.list_decode
- \+/\- *theorem* first_order.language.term.list_decode_encode_list

Modified src/model_theory/substructures.lean




## [2022-04-20 10:38:25](https://github.com/leanprover-community/mathlib/commit/d9a8d6e)
feat(topology/separation): Finite sets in T2 spaces ([#12845](https://github.com/leanprover-community/mathlib/pull/12845))
We prove the following theorem: given a finite set in a T2 space, one can choose an open set around each point so that these are pairwise disjoint.
#### Estimated changes
Modified src/topology/separation.lean
- \+ *lemma* t2_separation_finset



## [2022-04-20 10:04:20](https://github.com/leanprover-community/mathlib/commit/8d351dc)
feat(analysis/inner_product_space/gram_schmidt_ortho): Gram-Schmidt Orthogonalization and Orthonormalization ([#12857](https://github.com/leanprover-community/mathlib/pull/12857))
Formalize Gram-Schmidt Orthogonalization and Orthonormalization
#### Estimated changes
Modified docs/undergrad.yaml


Added src/analysis/inner_product_space/gram_schmidt_ortho.lean
- \+ *lemma* gram_schmidt_def'
- \+ *lemma* gram_schmidt_def
- \+ *lemma* gram_schmidt_ne_zero'
- \+ *lemma* gram_schmidt_ne_zero
- \+ *lemma* gram_schmidt_normed_unit_length'
- \+ *lemma* gram_schmidt_normed_unit_length
- \+ *theorem* gram_schmidt_orthogonal
- \+ *theorem* gram_schmidt_orthonormal
- \+ *theorem* gram_schmidt_pairwise_orthogonal
- \+ *lemma* gram_schmidt_zero
- \+ *lemma* span_gram_schmidt



## [2022-04-20 08:56:47](https://github.com/leanprover-community/mathlib/commit/92f6eb6)
chore(algebra/big_operators/fin): golf finset.prod_range ([#13535](https://github.com/leanprover-community/mathlib/pull/13535))
#### Estimated changes
Modified src/algebra/big_operators/fin.lean




## [2022-04-19 23:26:34](https://github.com/leanprover-community/mathlib/commit/71b470f)
chore(analysis/normed_space/star): make an argument explicit ([#13523](https://github.com/leanprover-community/mathlib/pull/13523))
#### Estimated changes
Modified src/analysis/normed_space/star/basic.lean
- \+/\- *lemma* nnnorm_star

Modified src/analysis/normed_space/star/matrix.lean


Modified src/topology/continuous_function/bounded.lean


Modified src/topology/continuous_function/zero_at_infty.lean




## [2022-04-19 20:26:49](https://github.com/leanprover-community/mathlib/commit/5038a4a)
feat(*): `op_op_op_comm` lemmas ([#13528](https://github.com/leanprover-community/mathlib/pull/13528))
A handful of lemmas of the form `op (op a b) (op c d) = op (op a c) (op b d)`.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* div_div_div_comm

Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* div_div_div_comm₀

Modified src/group_theory/group_action/defs.lean
- \+ *lemma* smul_smul_smul_comm

Modified src/order/symm_diff.lean
- \+ *lemma* symm_diff_left_comm
- \+ *lemma* symm_diff_right_comm
- \+ *lemma* symm_diff_symm_diff_symm_diff_comm



## [2022-04-19 20:26:48](https://github.com/leanprover-community/mathlib/commit/cf5aea0)
chore(data/real/nnreal): add commuted version of `nnreal.mul_finset_sup` ([#13512](https://github.com/leanprover-community/mathlib/pull/13512))
Also make the argument explicit
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.finset_sup_mul
- \+/\- *lemma* nnreal.mul_finset_sup
- \+ *lemma* nnreal.sup_mul



## [2022-04-19 20:26:47](https://github.com/leanprover-community/mathlib/commit/094b1f5)
chore(*/matrix): order `m` and `n` alphabetically ([#13510](https://github.com/leanprover-community/mathlib/pull/13510))
In a few places this also reorders `(n) [fintype n] (m) [fintype m]` to `(m n) [fintype m] [fintype n]` which seems to be where we prefer to put typeclasses.
#### Estimated changes
Modified src/analysis/matrix.lean
- \+/\- *lemma* matrix.nnnorm_entry_le_entrywise_sup_nnorm
- \+/\- *lemma* matrix.nnnorm_le_iff
- \+/\- *lemma* matrix.nnnorm_lt_iff
- \+/\- *lemma* matrix.norm_entry_le_entrywise_sup_norm
- \+/\- *lemma* matrix.norm_le_iff
- \+/\- *lemma* matrix.norm_lt_iff

Modified src/data/matrix/basic.lean
- \+/\- *lemma* matrix.map_update_column
- \+/\- *lemma* matrix.map_update_row
- \+/\- *lemma* matrix.minor_mul_transpose_minor
- \+/\- *def* matrix.update_column
- \+/\- *lemma* matrix.update_column_apply
- \+/\- *lemma* matrix.update_column_conj_transpose
- \+/\- *lemma* matrix.update_column_ne
- \+/\- *lemma* matrix.update_column_self
- \+/\- *lemma* matrix.update_column_subsingleton
- \+/\- *lemma* matrix.update_column_transpose
- \+/\- *def* matrix.update_row
- \+/\- *lemma* matrix.update_row_apply
- \+/\- *lemma* matrix.update_row_conj_transpose
- \+/\- *lemma* matrix.update_row_ne
- \+/\- *lemma* matrix.update_row_self
- \+/\- *lemma* matrix.update_row_subsingleton
- \+/\- *lemma* matrix.update_row_transpose
- \+/\- *lemma* matrix.vec_mul_smul

Modified src/data/matrix/basis.lean
- \+/\- *lemma* matrix.matrix_eq_sum_std_basis

Modified src/linear_algebra/free_module/basic.lean


Modified src/linear_algebra/free_module/finite/rank.lean
- \+/\- *lemma* module.free.finrank_matrix

Modified src/linear_algebra/free_module/rank.lean
- \+/\- *lemma* module.free.rank_matrix''
- \+/\- *lemma* module.free.rank_matrix'
- \+/\- *lemma* module.free.rank_matrix

Modified src/linear_algebra/matrix/to_lin.lean


Modified src/linear_algebra/std_basis.lean


Modified src/topology/algebra/matrix.lean
- \+/\- *lemma* continuous.matrix_map
- \+/\- *lemma* continuous.matrix_transpose



## [2022-04-19 19:41:21](https://github.com/leanprover-community/mathlib/commit/3ac979a)
feat(analysis/calculus/specific_functions): trivial extra lemmas ([#13516](https://github.com/leanprover-community/mathlib/pull/13516))
#### Estimated changes
Modified src/analysis/calculus/specific_functions.lean




## [2022-04-19 17:41:07](https://github.com/leanprover-community/mathlib/commit/70759ef)
feat(analysis): lemmas about nnnorm and nndist ([#13498](https://github.com/leanprover-community/mathlib/pull/13498))
Most of these lemmas follow trivially from the `norm` versions. This is far from exhaustive.
Additionally:
* `nnreal.coe_supr` and `nnreal.coe_infi` are added
* The old `is_primitive_root.nnnorm_eq_one` is renamed to `is_primitive_root.norm'_eq_one` as it was not about `nnnorm` at all. The unprimed name is already taken in reference to `algebra.norm`.
* `parallelogram_law_with_norm_real` is removed since it's syntactically identical to `parallelogram_law_with_norm ℝ` and also not used anywhere.
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* complex.conj_cle_nnorm
- \+ *lemma* complex.im_clm_nnnorm
- \+ *lemma* complex.nndist_conj_comm
- \+ *lemma* complex.nndist_conj_conj
- \+ *lemma* complex.of_real_clm_nnnorm
- \+ *lemma* complex.re_clm_nnnorm

Modified src/analysis/complex/roots_of_unity.lean
- \+ *lemma* is_primitive_root.norm'_eq_one

Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* nnnorm_inner_le_nnnorm
- \+ *lemma* parallelogram_law_with_nnnorm
- \+/\- *lemma* parallelogram_law_with_norm
- \- *lemma* parallelogram_law_with_norm_real

Modified src/analysis/inner_product_space/projection.lean


Modified src/analysis/matrix.lean
- \+ *lemma* matrix.nnnorm_entry_le_entrywise_sup_nnorm
- \+ *lemma* matrix.nnnorm_le_iff
- \+ *lemma* matrix.nnnorm_lt_iff

Modified src/analysis/normed/group/basic.lean
- \+ *lemma* coe_comp_nnnorm
- \+ *lemma* lipschitz_with_one_nnnorm
- \+ *lemma* nnnorm_le_add_nnnorm_add
- \+ *lemma* nnnorm_le_insert'
- \+ *lemma* nnnorm_le_insert
- \+ *lemma* nnnorm_le_pi_nnnorm
- \+ *lemma* pi_nnnorm_le_iff
- \+ *lemma* pi_nnnorm_lt_iff

Modified src/analysis/normed/normed_field.lean
- \+ *lemma* finset.nnnorm_prod_le'
- \+ *lemma* finset.nnnorm_prod_le
- \+ *lemma* list.nnnorm_prod_le'
- \+ *lemma* list.nnnorm_prod_le
- \+ *lemma* units.nnorm_pos

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.nnnorm_def
- \+ *lemma* continuous_linear_map.op_nnnorm_comp_le

Modified src/analysis/normed_space/pi_Lp.lean
- \+ *lemma* pi_Lp.nnnorm_eq

Modified src/analysis/normed_space/star/basic.lean
- \+ *lemma* nnnorm_star

Modified src/analysis/quaternion.lean
- \+ *lemma* quaternion.nnorm_coe

Modified src/data/real/nnreal.lean
- \+/\- *lemma* nnreal.coe_Inf
- \+/\- *lemma* nnreal.coe_Sup
- \+ *lemma* nnreal.coe_image
- \+ *lemma* nnreal.coe_infi
- \+ *lemma* nnreal.coe_supr

Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.nndist_coe_le_nndist
- \+ *lemma* bounded_continuous_function.nndist_eq
- \+ *lemma* bounded_continuous_function.nndist_eq_supr
- \+ *lemma* bounded_continuous_function.nndist_le_two_nnnorm
- \+ *lemma* bounded_continuous_function.nndist_set_exists
- \+ *lemma* bounded_continuous_function.nnnorm_coe_le_nnnorm
- \+ *lemma* bounded_continuous_function.nnnorm_const_eq
- \+ *lemma* bounded_continuous_function.nnnorm_const_le
- \+ *lemma* bounded_continuous_function.nnnorm_def
- \+ *lemma* bounded_continuous_function.nnnorm_eq_supr_nnnorm
- \+ *lemma* bounded_continuous_function.nnnorm_le

Modified src/topology/metric_space/isometry.lean
- \+ *theorem* isometry.nndist_eq



## [2022-04-19 15:52:32](https://github.com/leanprover-community/mathlib/commit/f06dca7)
feat(data/int/basic): add lemma `int.abs_le_one_iff` ([#13513](https://github.com/leanprover-community/mathlib/pull/13513))
Also renaming `int.eq_zero_iff_abs_lt_one`.
The proof is due to @Ruben-VandeVelde 
Discussed on Zulip [here](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Integers.20of.20norm.20at.20most.20one)
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.abs_le_one_iff
- \+ *lemma* int.abs_lt_one_iff
- \- *lemma* int.eq_zero_iff_abs_lt_one



## [2022-04-19 15:52:31](https://github.com/leanprover-community/mathlib/commit/634eab1)
feat(category_theory/limits): add characteristic predicate for zero objects ([#13511](https://github.com/leanprover-community/mathlib/pull/13511))
#### Estimated changes
Modified src/algebra/category/Group/zero.lean


Modified src/analysis/normed/group/SemiNormedGroup.lean


Modified src/category_theory/closed/zero.lean


Modified src/category_theory/limits/preserves/shapes/zero.lean


Modified src/category_theory/limits/shapes/default.lean


Renamed src/category_theory/limits/shapes/zero.lean to src/category_theory/limits/shapes/zero_morphisms.lean
- \- *lemma* category_theory.limits.has_zero_object.from_zero_ext
- \- *lemma* category_theory.limits.has_zero_object.to_zero_ext
- \- *def* category_theory.limits.has_zero_object.zero_is_initial
- \- *def* category_theory.limits.has_zero_object.zero_is_terminal
- \- *def* category_theory.limits.has_zero_object.zero_iso_initial
- \- *def* category_theory.limits.has_zero_object.zero_iso_is_initial
- \- *def* category_theory.limits.has_zero_object.zero_iso_is_terminal
- \- *def* category_theory.limits.has_zero_object.zero_iso_terminal
- \+ *def* category_theory.limits.is_zero.has_zero_morphisms

Added src/category_theory/limits/shapes/zero_objects.lean
- \+ *lemma* category_theory.limits.has_zero_object.from_zero_ext
- \+ *def* category_theory.limits.has_zero_object.is_zero.iso_zero
- \+ *lemma* category_theory.limits.has_zero_object.is_zero_zero
- \+ *lemma* category_theory.limits.has_zero_object.to_zero_ext
- \+ *def* category_theory.limits.has_zero_object.zero_is_initial
- \+ *def* category_theory.limits.has_zero_object.zero_is_terminal
- \+ *def* category_theory.limits.has_zero_object.zero_iso_initial
- \+ *def* category_theory.limits.has_zero_object.zero_iso_is_initial
- \+ *def* category_theory.limits.has_zero_object.zero_iso_is_terminal
- \+ *def* category_theory.limits.has_zero_object.zero_iso_terminal
- \+ *lemma* category_theory.limits.is_zero.eq_from
- \+ *lemma* category_theory.limits.is_zero.eq_of_src
- \+ *lemma* category_theory.limits.is_zero.eq_of_tgt
- \+ *lemma* category_theory.limits.is_zero.eq_to
- \+ *lemma* category_theory.limits.is_zero.from_eq
- \+ *def* category_theory.limits.is_zero.iso
- \+ *def* category_theory.limits.is_zero.iso_is_initial
- \+ *def* category_theory.limits.is_zero.iso_is_terminal
- \+ *lemma* category_theory.limits.is_zero.of_iso
- \+ *lemma* category_theory.limits.is_zero.to_eq
- \+ *lemma* category_theory.limits.iso.is_zero_iff

Modified src/category_theory/simple.lean




## [2022-04-19 14:04:47](https://github.com/leanprover-community/mathlib/commit/5dc8c1c)
feat(order/filter/n_ary): Add lemma equating map₂ to map on the product ([#13490](https://github.com/leanprover-community/mathlib/pull/13490))
Proof that map₂ is the image of the corresponding function `α × β → γ`.
Discussion: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/filter.20map.E2.82.82.20as.20map
#### Estimated changes
Modified src/order/filter/n_ary.lean
- \+ *lemma* filter.map_prod_eq_map₂'
- \+ *lemma* filter.map_prod_eq_map₂



## [2022-04-19 14:04:46](https://github.com/leanprover-community/mathlib/commit/8fa3263)
fix(analysis/locally_convex/balanced_hull_core): minimize import ([#13450](https://github.com/leanprover-community/mathlib/pull/13450))
I'm doing this because I need to have `balanced_hull_core` before `normed_space.finite_dimensional` and this little change seems to be enough for that, but I think at some point we'll need to move lemmas so that normed_spaces come as late as possible
#### Estimated changes
Modified src/analysis/locally_convex/balanced_core_hull.lean




## [2022-04-19 14:04:45](https://github.com/leanprover-community/mathlib/commit/ba6a985)
feat(order/cover): define `wcovby` ([#13424](https://github.com/leanprover-community/mathlib/pull/13424))
* This defines the reflexive closure of `covby`, which I call `wcovby` ("weakly covered by")
* This is useful, since some results about `covby` still hold for `wcovby`. 
* Use `wcovby` in the proofs of the properties for `covby`.
* Also define `wcovby_insert` (the motivating example, since I really want `(wcovby_insert _ _).eq_or_eq`)
#### Estimated changes
Modified src/data/set/intervals/ord_connected.lean
- \+ *lemma* set.ord_connected_image
- \+ *lemma* set.ord_connected_range

Modified src/order/cover.lean
- \+/\- *lemma* apply_covby_apply_iff
- \+ *lemma* apply_wcovby_apply_iff
- \+/\- *lemma* covby.image
- \+/\- *lemma* covby.of_image
- \+ *lemma* covby_iff_wcovby_and_lt
- \+ *lemma* covby_iff_wcovby_and_ne
- \+ *lemma* covby_iff_wcovby_and_not_le
- \+ *lemma* not_wcovby_iff
- \+ *lemma* of_dual_wcovby_of_dual_iff
- \+ *lemma* set.covby_insert
- \+ *lemma* set.ord_connected.apply_covby_apply_iff
- \+ *lemma* set.ord_connected.apply_wcovby_apply_iff
- \+ *lemma* set.wcovby_insert
- \+ *lemma* to_dual_wcovby_to_dual_iff
- \+ *lemma* wcovby.Icc_eq
- \+ *lemma* wcovby.Ico_subset
- \+ *lemma* wcovby.Ioc_subset
- \+ *lemma* wcovby.Ioo_eq
- \+ *lemma* wcovby.covby_of_lt
- \+ *lemma* wcovby.covby_of_ne
- \+ *lemma* wcovby.covby_of_not_le
- \+ *lemma* wcovby.eq_or_eq
- \+ *lemma* wcovby.image
- \+ *lemma* wcovby.le
- \+ *lemma* wcovby.le_and_le_iff
- \+ *lemma* wcovby.of_image
- \+ *lemma* wcovby.refl
- \+ *lemma* wcovby.rfl
- \+ *lemma* wcovby.wcovby_iff_le
- \+ *def* wcovby
- \+ *lemma* wcovby_iff_covby_or_eq
- \+ *lemma* wcovby_iff_covby_or_le_and_le
- \+ *lemma* wcovby_of_eq_or_eq
- \+ *lemma* wcovby_of_le_of_le

Modified src/order/succ_pred/basic.lean
- \+ *lemma* order.pred_wcovby
- \+ *lemma* order.wcovby_succ



## [2022-04-19 14:04:44](https://github.com/leanprover-community/mathlib/commit/8f7e10b)
refactor(group_theory/group_action/big_operators): extract to a new file ([#13340](https://github.com/leanprover-community/mathlib/pull/13340))
`basic` is a misleading name, as `group_action.basic` imports a lot of things.
For now I'm not renaming it, but I've adding a skeletal docstring.
Splitting out the big operator lemmas allows access to big operators before modules and quotients.
This also performs a drive-by generalization of the typeclasses on `smul_cancel_of_non_zero_divisor`.
Authorship is from [#1910](https://github.com/leanprover-community/mathlib/pull/1910)
#### Estimated changes
Modified src/algebra/hom/group_action.lean
- \- *def* mul_action_hom.to_quotient
- \- *lemma* mul_action_hom.to_quotient_apply

Modified src/algebra/module/basic.lean


Modified src/data/dfinsupp/interval.lean


Modified src/data/finset/finsupp.lean


Modified src/group_theory/group_action/basic.lean
- \- *lemma* finset.smul_prod
- \- *lemma* finset.smul_sum
- \- *lemma* list.smul_prod
- \- *lemma* list.smul_sum
- \+ *def* mul_action_hom.to_quotient
- \+ *lemma* mul_action_hom.to_quotient_apply
- \- *lemma* multiset.smul_prod
- \- *lemma* multiset.smul_sum
- \+/\- *lemma* smul_cancel_of_non_zero_divisor

Added src/group_theory/group_action/big_operators.lean
- \+ *lemma* finset.smul_prod
- \+ *lemma* finset.smul_sum
- \+ *lemma* list.smul_prod
- \+ *lemma* list.smul_sum
- \+ *lemma* multiset.smul_prod
- \+ *lemma* multiset.smul_sum



## [2022-04-19 12:11:00](https://github.com/leanprover-community/mathlib/commit/3e78c23)
fix(algebra/hom/units): better defeq in `is_unit.lift_right` ([#13508](https://github.com/leanprover-community/mathlib/pull/13508))
… and fix a timeout introduced by this change and remove some extraneous parentheses there.
#### Estimated changes
Modified src/algebra/hom/units.lean


Modified src/algebraic_geometry/structure_sheaf.lean




## [2022-04-19 10:05:03](https://github.com/leanprover-community/mathlib/commit/5a4bae1)
feat(algebra/*/basic): add trivial lemmas ([#13416](https://github.com/leanprover-community/mathlib/pull/13416))
These save you from having to fiddle with `mul_one` when you want to rewrite them the other way, or allow easier commutativity rewrites.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* mul_rotate'
- \+ *lemma* mul_rotate

Modified src/algebra/ring/basic.lean
- \+ *lemma* add_one_mul
- \+ *lemma* mul_add_one
- \+ *lemma* mul_one_add
- \+ *lemma* mul_one_sub
- \+ *lemma* mul_sub_one
- \+ *lemma* one_add_mul
- \+ *lemma* one_sub_mul
- \+ *lemma* sub_one_mul



## [2022-04-19 08:07:49](https://github.com/leanprover-community/mathlib/commit/9202b6d)
feat(order/succ_pred/basic): Intervals and `succ`/`pred` ([#13486](https://github.com/leanprover-community/mathlib/pull/13486))
Relate `order.succ`, `order.pred` and `set.Ixx`.
#### Estimated changes
Modified src/analysis/calculus/cont_diff.lean


Modified src/data/set/basic.lean
- \- *lemma* set.insert_inter
- \+ *lemma* set.insert_inter_distrib
- \+/\- *lemma* set.insert_inter_of_mem
- \+/\- *lemma* set.insert_inter_of_not_mem
- \+ *lemma* set.insert_union_distrib
- \+ *lemma* set.inter_insert_of_mem
- \+ *lemma* set.inter_insert_of_not_mem

Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Ico_insert_right
- \+ *lemma* set.Iic_inter_Ici
- \+ *lemma* set.Iic_inter_Ioi
- \+ *lemma* set.Iio_insert
- \+ *lemma* set.Iio_inter_Ici
- \+ *lemma* set.Iio_inter_Ioi
- \+ *lemma* set.Ioc_insert_left
- \+ *lemma* set.Ioi_insert
- \+ *lemma* set.Ioo_insert_left
- \+ *lemma* set.Ioo_insert_right

Modified src/data/set/intervals/ord_connected.lean


Modified src/logic/basic.lean
- \+ *lemma* and_and_distrib_left
- \+ *lemma* and_and_distrib_right
- \+ *lemma* or_or_distrib_left
- \+ *lemma* or_or_distrib_right

Modified src/order/succ_pred/basic.lean
- \+ *lemma* order.Icc_pred_left
- \+ *lemma* order.Icc_pred_right
- \+ *lemma* order.Icc_pred_right_of_not_is_min
- \+ *lemma* order.Icc_succ_left
- \+ *lemma* order.Icc_succ_left_of_not_is_max
- \+ *lemma* order.Icc_succ_right
- \+ *lemma* order.Ici_pred
- \+/\- *lemma* order.Ici_succ
- \+ *lemma* order.Ico_pred_left
- \+ *lemma* order.Ico_pred_right_eq_insert
- \+ *lemma* order.Ico_succ_left
- \+ *lemma* order.Ico_succ_left_of_not_is_max
- \+ *lemma* order.Ico_succ_right
- \+ *lemma* order.Ico_succ_right_eq_insert
- \+ *lemma* order.Ico_succ_right_of_not_is_max
- \+/\- *lemma* order.Iic_pred
- \+ *lemma* order.Iic_succ
- \+/\- *lemma* order.Iio_succ
- \+ *lemma* order.Iio_succ_eq_insert
- \+ *lemma* order.Ioc_pred_left
- \+ *lemma* order.Ioc_pred_left_of_not_is_min
- \+ *lemma* order.Ioc_pred_right
- \+ *lemma* order.Ioc_pred_right_of_not_is_min
- \+ *lemma* order.Ioc_succ_right
- \+/\- *lemma* order.Ioi_pred
- \+ *lemma* order.Ioi_pred_eq_insert
- \+ *lemma* order.Ioo_pred_left
- \+ *lemma* order.Ioo_pred_left_of_not_is_min
- \+ *lemma* order.Ioo_pred_right_eq_insert
- \+ *lemma* order.Ioo_succ_right
- \+ *lemma* order.Ioo_succ_right_eq_insert
- \+ *lemma* order.Ioo_succ_right_of_not_is_max
- \- *lemma* order.le_pred_iff_lt_or_eq
- \+ *lemma* order.le_succ_iff_eq_or_le
- \- *lemma* order.le_succ_iff_lt_or_eq
- \+ *lemma* order.lt_succ_iff_eq_or_lt
- \+ *lemma* order.lt_succ_iff_eq_or_lt_of_not_is_max
- \- *lemma* order.lt_succ_iff_lt_or_eq
- \+ *lemma* order.pred_le_iff_eq_or_le
- \+ *lemma* order.pred_lt_iff_eq_or_lt
- \+ *lemma* order.pred_lt_iff_eq_or_lt_of_not_is_min
- \- *lemma* order.pred_lt_iff_lt_or_eq



## [2022-04-19 06:50:55](https://github.com/leanprover-community/mathlib/commit/d19e8cb)
chore(docs): don't use deprecated is_subring ([#13505](https://github.com/leanprover-community/mathlib/pull/13505))
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml




## [2022-04-19 05:04:57](https://github.com/leanprover-community/mathlib/commit/828ef48)
fix(category_theory/monoidal): increase class search depth in coherence tactic ([#13413](https://github.com/leanprover-community/mathlib/pull/13413))
There were two places, not just one, where the class search depth needs to be increased.
#### Estimated changes
Modified src/category_theory/monoidal/braided.lean


Modified src/category_theory/monoidal/coherence.lean




## [2022-04-19 03:39:47](https://github.com/leanprover-community/mathlib/commit/fb44330)
feat(data/matrix/block): `matrix.block_diagonal` is a ring homomorphism ([#13489](https://github.com/leanprover-community/mathlib/pull/13489))
This is one of the steps on the path to showing that the matrix exponential of a block diagonal matrix is a block diagonal matrix of the exponents of the blocks.
As well as adding the new bundled homomorphisms, this generalizes the typeclasses in this file and tidies up the order of arguments.
Finally, this protects some `map_*` lemmas to prevent clashes with the global lemmas of the same name.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \- *lemma* matrix.map_add
- \- *lemma* matrix.map_sub
- \- *lemma* matrix.map_zero

Modified src/data/matrix/block.lean
- \+/\- *def* matrix.block_diagonal'
- \+/\- *lemma* matrix.block_diagonal'_add
- \+ *def* matrix.block_diagonal'_add_monoid_hom
- \+/\- *lemma* matrix.block_diagonal'_apply
- \+/\- *lemma* matrix.block_diagonal'_apply_eq
- \+/\- *lemma* matrix.block_diagonal'_apply_ne
- \+/\- *lemma* matrix.block_diagonal'_conj_transpose
- \+/\- *lemma* matrix.block_diagonal'_diagonal
- \+/\- *lemma* matrix.block_diagonal'_map
- \+/\- *lemma* matrix.block_diagonal'_mul
- \+/\- *lemma* matrix.block_diagonal'_neg
- \+ *def* matrix.block_diagonal'_ring_hom
- \+/\- *lemma* matrix.block_diagonal'_sub
- \+/\- *lemma* matrix.block_diagonal'_transpose
- \+/\- *def* matrix.block_diagonal
- \+/\- *lemma* matrix.block_diagonal_add
- \+ *def* matrix.block_diagonal_add_monoid_hom
- \+/\- *lemma* matrix.block_diagonal_apply
- \+/\- *lemma* matrix.block_diagonal_apply_eq
- \+/\- *lemma* matrix.block_diagonal_apply_ne
- \+/\- *lemma* matrix.block_diagonal_map
- \+/\- *lemma* matrix.block_diagonal_mul
- \+/\- *lemma* matrix.block_diagonal_neg
- \+ *def* matrix.block_diagonal_ring_hom
- \+/\- *lemma* matrix.block_diagonal_smul
- \+/\- *lemma* matrix.block_diagonal_sub
- \+/\- *lemma* matrix.block_diagonal_transpose
- \+/\- *lemma* matrix.from_blocks_add
- \+/\- *lemma* matrix.from_blocks_diagonal
- \+/\- *lemma* matrix.from_blocks_multiply
- \+/\- *lemma* matrix.from_blocks_one
- \+/\- *lemma* matrix.from_blocks_smul



## [2022-04-19 01:03:57](https://github.com/leanprover-community/mathlib/commit/eb22ba4)
chore(algebra/monoid_algebra/basic): use the homomorphism typeclasses ([#13389](https://github.com/leanprover-community/mathlib/pull/13389))
This replaces `mul_hom` with `mul_hom_class` and `add_hom` with `add_hom_class`.
Also adds two trivial lemmas, `monoid_algebra.map_domain_one` and `add_monoid_algebra.map_domain_one`.
#### Estimated changes
Modified src/algebra/monoid_algebra/basic.lean
- \+/\- *lemma* add_monoid_algebra.map_domain_mul
- \+ *lemma* add_monoid_algebra.map_domain_one
- \+ *lemma* monoid_algebra.map_domain_one



## [2022-04-18 20:47:04](https://github.com/leanprover-community/mathlib/commit/37d02d3)
chore(ring_theory/hahn_series, topology/locally_constant/algebra): add missing `non_unital_non_assoc_ring` instances ([#13504](https://github.com/leanprover-community/mathlib/pull/13504))
#### Estimated changes
Modified src/ring_theory/hahn_series.lean


Modified src/topology/locally_constant/algebra.lean




## [2022-04-18 19:11:39](https://github.com/leanprover-community/mathlib/commit/3c20253)
chore(algebra/ring/{pi, prod}): fix errors in `ring_hom` for `pi` and `prod`. ([#13501](https://github.com/leanprover-community/mathlib/pull/13501))
Looks like some things were incorrectly changed when copied from the corresponding `monoid_hom` files.
#### Estimated changes
Modified src/algebra/ring/pi.lean


Modified src/algebra/ring/prod.lean
- \+/\- *lemma* ring_hom.prod_comp_prod_map
- \+/\- *def* ring_hom.prod_map



## [2022-04-18 19:11:38](https://github.com/leanprover-community/mathlib/commit/b54591f)
chore(analysis/normed_space/finite_dimension): golf a proof ([#13491](https://github.com/leanprover-community/mathlib/pull/13491))
These `letI`s just made this proof convoluted, the instances were not needed.
Without them, we don't even need the import.
Similarly, the `classical` was the cause of the need for the `congr`.
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean




## [2022-04-18 19:11:37](https://github.com/leanprover-community/mathlib/commit/fd08afe)
chore(data/nat/factorization): golf `dvd_iff_prime_pow_dvd_dvd` ([#13473](https://github.com/leanprover-community/mathlib/pull/13473))
Golfing the edge-case proof added in https://github.com/leanprover-community/mathlib/pull/13316
#### Estimated changes
Modified src/data/nat/factorization.lean




## [2022-04-18 17:14:07](https://github.com/leanprover-community/mathlib/commit/d89160b)
feat(order/bounded_order): Strictly monotone functions preserve maximality ([#13434](https://github.com/leanprover-community/mathlib/pull/13434))
Prove `f a = f ⊤ ↔ a = ⊤` and `f a = f ⊥ ↔ a = ⊥` for strictly monotone/antitone functions. Also fix `is_max.eq_top` and friends and delete `eq_top_of_maximal` (which accidentally survived the last refactor).
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* iff.not_left
- \+ *lemma* iff.not_right

Modified src/order/bounded_order.lean
- \- *lemma* eq_top_of_maximal
- \+ *lemma* not_bot_lt_iff
- \+ *lemma* not_lt_top_iff
- \+ *lemma* strict_anti.apply_eq_bot_iff
- \+ *lemma* strict_anti.apply_eq_top_iff
- \+ *lemma* strict_mono.apply_eq_bot_iff
- \+ *lemma* strict_mono.apply_eq_top_iff

Modified src/order/monotone.lean
- \+ *lemma* strict_anti.is_max_of_apply
- \+ *lemma* strict_anti.is_min_of_apply
- \+ *lemma* strict_mono.is_max_of_apply
- \+ *lemma* strict_mono.is_min_of_apply



## [2022-04-18 17:14:06](https://github.com/leanprover-community/mathlib/commit/5c75390)
feat(data/real/ennreal): Order properties of addition ([#13371](https://github.com/leanprover-community/mathlib/pull/13371))
Inherit algebraic order lemmas from `with_top`. Also protect `ennreal.add_lt_add_iff_left` and `ennreal.add_lt_add_iff_right`, as they should have been.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \- *lemma* ennreal.add_lt_add_iff_left
- \- *lemma* ennreal.add_lt_add_iff_right
- \- *lemma* ennreal.add_lt_add_left
- \- *lemma* ennreal.add_lt_add_right
- \- *lemma* ennreal.le_of_add_le_add_left
- \- *lemma* ennreal.le_of_add_le_add_right

Modified src/measure_theory/integral/lebesgue.lean


Modified src/order/filter/ennreal.lean




## [2022-04-18 17:14:05](https://github.com/leanprover-community/mathlib/commit/546618e)
feat(order/upper_lower): Principal upper/lower sets ([#13069](https://github.com/leanprover-community/mathlib/pull/13069))
Define `upper_set.Ici` and `lower_set.Iic`. Also add membership lemmas for the lattice operations.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.Ici_Sup
- \+ *lemma* set.Ici_supr
- \+ *lemma* set.Ici_supr₂
- \+ *lemma* set.Iic_Inf
- \+ *lemma* set.Iic_infi
- \+ *lemma* set.Iic_infi₂

Modified src/order/upper_lower.lean
- \+ *lemma* is_lower_set_Iic
- \+ *lemma* is_lower_set_Iio
- \+ *lemma* is_upper_set_Ici
- \+ *lemma* is_upper_set_Ioi
- \+ *def* lower_set.Iic
- \+ *lemma* lower_set.Iic_Inf
- \+ *def* lower_set.Iic_Inf_hom
- \+ *lemma* lower_set.Iic_Inf_hom_apply
- \+ *lemma* lower_set.Iic_inf
- \+ *def* lower_set.Iic_inf_hom
- \+ *lemma* lower_set.Iic_inf_hom_apply
- \+ *lemma* lower_set.Iic_infi
- \+ *lemma* lower_set.Iic_infi₂
- \+ *lemma* lower_set.Iic_top
- \+ *def* lower_set.Iio
- \+ *lemma* lower_set.Iio_bot
- \+ *lemma* lower_set.Ioi_le_Ici
- \+ *lemma* lower_set.coe_Iic
- \+ *lemma* lower_set.coe_Iic_Inf_hom
- \+ *lemma* lower_set.coe_Iic_inf_hom
- \+ *lemma* lower_set.coe_Iio
- \+ *lemma* lower_set.mem_Iic_iff
- \+ *lemma* lower_set.mem_Iio_iff
- \+ *lemma* lower_set.mem_Inf_iff
- \+ *lemma* lower_set.mem_Sup_iff
- \+ *lemma* lower_set.mem_inf_iff
- \+ *lemma* lower_set.mem_infi_iff
- \+ *lemma* lower_set.mem_infi₂_iff
- \+ *lemma* lower_set.mem_sup_iff
- \+ *lemma* lower_set.mem_supr_iff
- \+ *lemma* lower_set.mem_supr₂_iff
- \+ *lemma* lower_set.mem_top
- \+ *lemma* lower_set.not_mem_bot
- \+ *def* upper_set.Ici
- \+ *lemma* upper_set.Ici_Sup
- \+ *def* upper_set.Ici_Sup_hom
- \+ *lemma* upper_set.Ici_Sup_hom_apply
- \+ *lemma* upper_set.Ici_sup
- \+ *def* upper_set.Ici_sup_hom
- \+ *lemma* upper_set.Ici_sup_hom_apply
- \+ *lemma* upper_set.Ici_supr
- \+ *lemma* upper_set.Ici_supr₂
- \+ *lemma* upper_set.Ici_top
- \+ *def* upper_set.Ioi
- \+ *lemma* upper_set.Ioi_bot
- \+ *lemma* upper_set.Ioi_le_Ici
- \+ *lemma* upper_set.coe_Ici
- \+ *lemma* upper_set.coe_Ioi
- \+ *lemma* upper_set.mem_Ici_iff
- \+ *lemma* upper_set.mem_Inf_iff
- \+ *lemma* upper_set.mem_Ioi_iff
- \+ *lemma* upper_set.mem_Sup_iff
- \+ *lemma* upper_set.mem_inf_iff
- \+ *lemma* upper_set.mem_infi_iff
- \+ *lemma* upper_set.mem_infi₂_iff
- \+ *lemma* upper_set.mem_sup_iff
- \+ *lemma* upper_set.mem_supr_iff
- \+ *lemma* upper_set.mem_supr₂_iff
- \+ *lemma* upper_set.mem_top
- \+ *lemma* upper_set.not_mem_bot



## [2022-04-18 15:45:35](https://github.com/leanprover-community/mathlib/commit/d790b4b)
feat(set_theory/cardinal): `lt_omega_of_fintype` ([#13365](https://github.com/leanprover-community/mathlib/pull/13365))
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified src/data/W/cardinal.lean


Modified src/data/mv_polynomial/cardinal.lean


Modified src/data/polynomial/cardinal.lean


Modified src/field_theory/is_alg_closed/classification.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.lt_omega_of_fintype



## [2022-04-18 10:31:05](https://github.com/leanprover-community/mathlib/commit/e18ea79)
feat(number_theory/legendre_symbol/quadratic_reciprocity): replace `[fact (p % 2 = 1)]` arguments by `(p ≠ 2)` ([#13474](https://github.com/leanprover-community/mathlib/pull/13474))
This removes implicit arguments of the form `[fact (p % 2 = 1)]` and replaces them by explicit arguments `(hp : p ≠ 2)`.
(See the short discussion on April 9 in [this topic](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Quadratic.20Hilbert.20symbol.20over.20.E2.84.9A).)
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.prime.mod_two_eq_one_iff_ne_two

Modified src/number_theory/legendre_symbol/quadratic_reciprocity.lean
- \+/\- *lemma* zmod.eisenstein_lemma
- \+/\- *lemma* zmod.exists_sq_eq_prime_iff_of_mod_four_eq_one
- \+/\- *lemma* zmod.exists_sq_eq_two_iff
- \+/\- *lemma* zmod.gauss_lemma
- \+/\- *lemma* zmod.legendre_sym_two
- \+/\- *theorem* zmod.quadratic_reciprocity



## [2022-04-18 05:37:15](https://github.com/leanprover-community/mathlib/commit/82348a6)
feat(computability/partrec_code): add eval prec helpers ([#11945](https://github.com/leanprover-community/mathlib/pull/11945))
A few helpers to clarify the definition of `eval`.
#### Estimated changes
Modified src/computability/partrec_code.lean
- \+ *lemma* nat.partrec.code.eval_prec_succ
- \+ *lemma* nat.partrec.code.eval_prec_zero



## [2022-04-18 03:41:36](https://github.com/leanprover-community/mathlib/commit/279b7f3)
chore(scripts): update nolints.txt ([#13493](https://github.com/leanprover-community/mathlib/pull/13493))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-04-17 15:18:45](https://github.com/leanprover-community/mathlib/commit/e6322c6)
feat(analysis/convex): golf some proofs ([#13451](https://github.com/leanprover-community/mathlib/pull/13451))
#### Estimated changes
Modified src/algebra/order/smul.lean


Modified src/analysis/convex/extrema.lean


Modified src/analysis/convex/topology.lean


Modified src/data/real/cardinality.lean


Modified src/data/set/intervals/image_preimage.lean
- \- *lemma* set.image_inv_Ioo_0_left
- \+ *lemma* set.inv_Ioi
- \+ *lemma* set.inv_Ioo_0_left

Modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* affine_map.homothety_mul_apply



## [2022-04-17 15:18:44](https://github.com/leanprover-community/mathlib/commit/b90e770)
feat(data/fin/tuple/nat_antidiagonal): add `list.nat.antidiagonal_tuple_pairwise_pi_lex` ([#13339](https://github.com/leanprover-community/mathlib/pull/13339))
This proof feels a little clumsy, but maybe that's unavoidable.
#### Estimated changes
Modified src/data/fin/tuple/nat_antidiagonal.lean
- \+ *lemma* finset.nat.antidiagonal_tuple_zero_right
- \+ *lemma* list.nat.antidiagonal_tuple_pairwise_pi_lex
- \+ *lemma* list.nat.antidiagonal_tuple_zero_right
- \+ *lemma* multiset.nat.antidiagonal_tuple_zero_right



## [2022-04-17 13:47:06](https://github.com/leanprover-community/mathlib/commit/9380977)
chore(algebra/big_operators/fin): moving lemmas ([#13331](https://github.com/leanprover-community/mathlib/pull/13331))
This PR moves lemmas about products and sums over `fin n` from `data/fintype/card.lean` to `algebra/big_operators/fin.lean`.
#### Estimated changes
Modified src/algebra/big_operators/fin.lean
- \+ *lemma* fin.prod_const
- \+ *theorem* fin.prod_of_fn
- \+ *theorem* fin.prod_univ_cast_succ
- \+ *theorem* fin.prod_univ_def
- \+ *theorem* fin.prod_univ_one
- \+ *theorem* fin.prod_univ_succ
- \+ *theorem* fin.prod_univ_succ_above
- \+ *theorem* fin.prod_univ_two
- \+ *theorem* fin.prod_univ_zero
- \+ *lemma* fin.sum_const
- \+ *lemma* fin.sum_pow_mul_eq_add_pow
- \+ *theorem* finset.prod_range
- \+ *lemma* list.alternating_prod_eq_finset_prod
- \+ *lemma* list.alternating_sum_eq_finset_sum
- \+ *lemma* list.prod_of_fn
- \+ *lemma* list.prod_take_of_fn

Modified src/algebraic_topology/alternating_face_map_complex.lean


Modified src/combinatorics/composition.lean


Modified src/data/fintype/card.lean
- \- *lemma* fin.prod_const
- \- *theorem* fin.prod_of_fn
- \- *theorem* fin.prod_univ_cast_succ
- \- *theorem* fin.prod_univ_def
- \- *theorem* fin.prod_univ_one
- \- *theorem* fin.prod_univ_succ
- \- *theorem* fin.prod_univ_succ_above
- \- *theorem* fin.prod_univ_two
- \- *theorem* fin.prod_univ_zero
- \- *lemma* fin.sum_const
- \- *lemma* fin.sum_pow_mul_eq_add_pow
- \- *theorem* finset.prod_range
- \- *lemma* list.alternating_prod_eq_finset_prod
- \- *lemma* list.alternating_sum_eq_finset_sum
- \- *lemma* list.prod_of_fn
- \- *lemma* list.prod_take_of_fn

Modified src/data/matrix/notation.lean




## [2022-04-17 12:41:22](https://github.com/leanprover-community/mathlib/commit/7c7f351)
feat(topology/[separation, homeomorph]): separation properties are topological invariants ([#13401](https://github.com/leanprover-community/mathlib/pull/13401))
#### Estimated changes
Modified src/topology/homeomorph.lean


Modified src/topology/separation.lean
- \+ *lemma* t1_space_of_injective_of_continuous



## [2022-04-17 10:27:47](https://github.com/leanprover-community/mathlib/commit/49e41eb)
feat(topology/algebra/order): extreme value thm for a function continuous on a closed set ([#13348](https://github.com/leanprover-community/mathlib/pull/13348))
#### Estimated changes
Modified src/topology/algebra/order/compact.lean
- \+ *lemma* continuous_on.exists_forall_ge'
- \+ *lemma* continuous_on.exists_forall_le'



## [2022-04-17 03:57:45](https://github.com/leanprover-community/mathlib/commit/f4f46cd)
chore(scripts): update nolints.txt ([#13482](https://github.com/leanprover-community/mathlib/pull/13482))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-04-16 19:28:42](https://github.com/leanprover-community/mathlib/commit/d4fda04)
feat(data/finsupp/basic): add a few lemmas, mostly about `finsupp.filter` ([#13457](https://github.com/leanprover-community/mathlib/pull/13457))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.filter_eq_self_iff
- \+ *lemma* finsupp.filter_eq_zero_iff
- \+/\- *lemma* finsupp.filter_single_of_neg
- \+/\- *lemma* finsupp.filter_single_of_pos
- \+ *lemma* finsupp.prod_div_prod_filter
- \+ *lemma* finsupp.prod_filter_index
- \+ *lemma* finsupp.prod_filter_mul_prod_filter_not
- \+ *lemma* finsupp.single_apply_ne_zero



## [2022-04-16 17:33:14](https://github.com/leanprover-community/mathlib/commit/96667b5)
chore(number_theory/*): Weaken assumptions ([#13443](https://github.com/leanprover-community/mathlib/pull/13443))
Follow @alexjbest's generalization linter to weaken typeclass assumptions in number theory.
#### Estimated changes
Modified src/number_theory/arithmetic_function.lean
- \+/\- *lemma* nat.arithmetic_function.coe_moebius_mul_coe_zeta
- \+/\- *theorem* nat.arithmetic_function.sum_eq_iff_sum_mul_moebius_eq

Modified src/number_theory/class_number/admissible_card_pow_degree.lean
- \+/\- *lemma* polynomial.exists_approx_polynomial_aux
- \+/\- *lemma* polynomial.exists_eq_polynomial

Modified src/number_theory/class_number/finite.lean
- \+/\- *lemma* class_group.norm_lt

Modified src/number_theory/liouville/basic.lean
- \+/\- *lemma* liouville.exists_one_le_pow_mul_dist

Modified src/number_theory/padics/ring_homs.lean
- \+/\- *lemma* padic_int.to_zmod_pow_eq_iff_ext

Modified src/number_theory/zsqrtd/basic.lean
- \+/\- *lemma* zsqrtd.hom_ext



## [2022-04-16 17:33:13](https://github.com/leanprover-community/mathlib/commit/018e9b5)
chore(order/bounded_order): Match the `with_bot` and `with_top` API ([#13419](https://github.com/leanprover-community/mathlib/pull/13419))
The API for `with_top` and the API for `with_bot` somehow evolved independently from each other, which created frustating disparity in lemmas and argument implicitness. This synchronizes everything (including the layout), generalize a few lemmas from `preorder`/`partial_order` to `has_le`/`has_lt`, and removes the duplicated `is_total (with_bot α) (≤)`/`is_total (with_top α) (≤)` instances.
#### Estimated changes
Modified src/algebra/cubic_discriminant.lean


Modified src/analysis/box_integral/partition/basic.lean


Modified src/analysis/box_integral/partition/split.lean


Modified src/linear_algebra/lagrange.lean


Modified src/order/bounded_order.lean
- \+/\- *lemma* with_bot.bot_lt_coe
- \+ *lemma* with_bot.bot_ne_coe
- \- *theorem* with_bot.bot_ne_coe
- \+ *lemma* with_bot.coe_eq_coe
- \- *theorem* with_bot.coe_eq_coe
- \+ *lemma* with_bot.coe_le
- \- *theorem* with_bot.coe_le
- \+ *lemma* with_bot.coe_le_coe
- \- *theorem* with_bot.coe_le_coe
- \+ *lemma* with_bot.coe_le_iff
- \+/\- *lemma* with_bot.coe_lt_coe
- \+ *lemma* with_bot.coe_ne_bot
- \- *theorem* with_bot.coe_ne_bot
- \+/\- *lemma* with_bot.coe_unbot
- \+ *lemma* with_bot.le_coe_iff
- \+ *lemma* with_bot.lt_coe_iff
- \+ *lemma* with_bot.lt_iff_exists_coe
- \+ *lemma* with_bot.lt_iff_exists_coe_btwn
- \+/\- *lemma* with_bot.ne_bot_iff_exists
- \+ *lemma* with_bot.none_le
- \+/\- *lemma* with_bot.none_lt_some
- \+/\- *lemma* with_bot.not_coe_le_bot
- \+/\- *lemma* with_bot.not_lt_none
- \+ *lemma* with_bot.some_le_some
- \- *theorem* with_bot.some_le_some
- \+ *lemma* with_bot.some_lt_some
- \- *theorem* with_bot.some_lt_some
- \+/\- *lemma* with_bot.unbot_coe
- \+ *lemma* with_bot.well_founded_gt
- \+/\- *lemma* with_bot.well_founded_lt
- \+ *lemma* with_top.coe_eq_coe
- \- *theorem* with_top.coe_eq_coe
- \+ *lemma* with_top.coe_le_coe
- \- *theorem* with_top.coe_le_coe
- \+ *lemma* with_top.coe_le_iff
- \- *theorem* with_top.coe_le_iff
- \+/\- *lemma* with_top.coe_lt_coe
- \+ *lemma* with_top.coe_lt_iff
- \- *theorem* with_top.coe_lt_iff
- \+/\- *lemma* with_top.coe_lt_top
- \+/\- *lemma* with_top.coe_max
- \+/\- *lemma* with_top.coe_min
- \+ *lemma* with_top.coe_ne_top
- \- *theorem* with_top.coe_ne_top
- \+/\- *lemma* with_top.coe_untop
- \+ *lemma* with_top.le_coe
- \- *theorem* with_top.le_coe
- \+ *lemma* with_top.le_coe_iff
- \- *theorem* with_top.le_coe_iff
- \+ *lemma* with_top.le_none
- \- *theorem* with_top.le_none
- \+ *lemma* with_top.lt_iff_exists_coe
- \- *theorem* with_top.lt_iff_exists_coe
- \+/\- *lemma* with_top.lt_iff_exists_coe_btwn
- \+/\- *lemma* with_top.ne_top_iff_exists
- \+ *lemma* with_top.not_none_lt
- \- *theorem* with_top.not_none_lt
- \+/\- *lemma* with_top.not_top_le_coe
- \+ *lemma* with_top.some_le_some
- \- *theorem* with_top.some_le_some
- \+ *lemma* with_top.some_lt_none
- \- *theorem* with_top.some_lt_none
- \+ *lemma* with_top.some_lt_some
- \- *theorem* with_top.some_lt_some
- \+ *lemma* with_top.top_ne_coe
- \- *theorem* with_top.top_ne_coe
- \+ *lemma* with_top.well_founded_gt
- \+/\- *lemma* with_top.well_founded_lt



## [2022-04-16 17:33:12](https://github.com/leanprover-community/mathlib/commit/8decd4b)
chore(logic/encodable/basic): Rename `encodable` instances ([#13396](https://github.com/leanprover-community/mathlib/pull/13396))
The instances were called `encodable.foo` instead of `foo.encodable` as the naming convention preconizes.
#### Estimated changes
Modified src/algebra/algebraic_card.lean


Modified src/analysis/box_integral/partition/measure.lean


Modified src/computability/encoding.lean


Modified src/data/W/basic.lean


Modified src/data/rat/denumerable.lean


Modified src/data/set/countable.lean


Modified src/data/tprod.lean


Modified src/logic/encodable/basic.lean


Modified src/logic/equiv/list.lean
- \- *def* encodable.trunc_encodable_of_fintype
- \+ *def* fintype.trunc_encodable

Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/function/strongly_measurable.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measurable_space_def.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/model_theory/basic.lean


Modified src/model_theory/encoding.lean


Modified src/set_theory/cardinal_ordinal.lean


Modified src/topology/bases.lean


Modified src/topology/metric_space/basic.lean




## [2022-04-16 17:33:11](https://github.com/leanprover-community/mathlib/commit/91a43e7)
feat(algebra/order/monoid): Co/contravariant classes for `with_bot`/`with_top` ([#13369](https://github.com/leanprover-community/mathlib/pull/13369))
Add the `covariant_class (with_bot α) (with_bot α) (+) (≤)` and `contravariant_class (with_bot α) (with_bot α) (+) (<)` instances, as well as the lemmas that `covariant_class (with_bot α) (with_bot α) (+) (<)` and `contravariant_class (with_bot α) (with_bot α) (+) (≤)` almost hold.
On the way, match the APIs for `with_bot`/`with_top` by adding missing lemmas.
#### Estimated changes
Modified src/algebra/order/monoid.lean
- \+/\- *lemma* with_bot.add_bot
- \+ *lemma* with_bot.add_coe_eq_bot_iff
- \+/\- *lemma* with_bot.add_eq_bot
- \+ *lemma* with_bot.add_eq_coe
- \- *lemma* with_bot.add_lt_add_iff_left
- \- *lemma* with_bot.add_lt_add_iff_right
- \+ *lemma* with_bot.add_ne_bot
- \+/\- *lemma* with_bot.bot_add
- \+ *lemma* with_bot.bot_lt_add
- \+/\- *lemma* with_bot.coe_add
- \+ *lemma* with_bot.coe_add_eq_bot_iff
- \+/\- *lemma* with_bot.coe_bit0
- \+/\- *lemma* with_bot.coe_bit1
- \+/\- *lemma* with_top.add_coe_eq_top_iff
- \+/\- *lemma* with_top.add_eq_coe
- \+/\- *lemma* with_top.add_eq_top
- \- *lemma* with_top.add_lt_add_iff_left
- \- *lemma* with_top.add_lt_add_iff_right
- \+/\- *lemma* with_top.add_lt_top
- \+ *lemma* with_top.add_ne_top
- \+/\- *lemma* with_top.add_top
- \+/\- *lemma* with_top.coe_add
- \+/\- *lemma* with_top.coe_add_eq_top_iff
- \+/\- *lemma* with_top.coe_bit0
- \+/\- *lemma* with_top.coe_bit1
- \+/\- *lemma* with_top.top_add
- \+/\- *lemma* with_zero.to_mul_bot_le
- \+/\- *lemma* with_zero.to_mul_bot_lt
- \+/\- *lemma* with_zero.to_mul_bot_strict_mono

Modified src/topology/instances/ereal.lean




## [2022-04-16 16:18:59](https://github.com/leanprover-community/mathlib/commit/874dde5)
feat(data/polynomial/eval): generalize smul lemmas ([#13479](https://github.com/leanprover-community/mathlib/pull/13479))
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+/\- *lemma* polynomial.eval_smul
- \+ *lemma* polynomial.smul_comp

Modified src/topology/continuous_function/polynomial.lean




## [2022-04-16 14:27:42](https://github.com/leanprover-community/mathlib/commit/010f09e)
feat(data/polynomial/taylor): add `taylor_alg_hom` ([#13477](https://github.com/leanprover-community/mathlib/pull/13477))
#### Estimated changes
Modified src/data/polynomial/taylor.lean
- \+ *def* polynomial.taylor_alg_hom



## [2022-04-16 12:38:45](https://github.com/leanprover-community/mathlib/commit/f7430cd)
feat(data/polynomial/eval): add `protected` on some lemmas about `polynomial.map` ([#13478](https://github.com/leanprover-community/mathlib/pull/13478))
These clash with global lemmas.
#### Estimated changes
Modified src/algebra/polynomial/group_ring_action.lean


Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/div.lean


Modified src/data/polynomial/eval.lean
- \- *lemma* polynomial.map_add
- \- *lemma* polynomial.map_mul
- \- *lemma* polynomial.map_neg
- \- *lemma* polynomial.map_one
- \- *lemma* polynomial.map_sub
- \- *lemma* polynomial.map_zero

Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/lifts.lean


Modified src/data/polynomial/ring_division.lean


Modified src/field_theory/polynomial_galois_group.lean


Modified src/field_theory/separable.lean


Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/polynomial/cyclotomic/basic.lean


Modified src/ring_theory/polynomial/dickson.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean




## [2022-04-16 05:39:36](https://github.com/leanprover-community/mathlib/commit/862a585)
feat(topology/stone_cech): add stone_cech_hom_ext ([#13472](https://github.com/leanprover-community/mathlib/pull/13472))
The universal property that characterises the Stone–Čech compactification of a topological space X is that any function from X to a compact Hausdorff space extends uniquely to a continuous function on βX. Existence is already provided by `unique_stone_cech_extend`, but it seems that the uniqueness lemma was intentionally omitted previously. Easy, but probably worth being explicit about.
#### Estimated changes
Modified src/topology/stone_cech.lean
- \+ *lemma* stone_cech_hom_ext



## [2022-04-15 20:29:48](https://github.com/leanprover-community/mathlib/commit/449e06a)
feat(algebraic_topology/fundamental_groupoid/fundamental_group): add type checker helpers for convertings paths to/from elements of fundamental group ([#13182](https://github.com/leanprover-community/mathlib/pull/13182))
This pr adds the following helper functions for converting paths to and from elements of the fundamental group:
- `to_arrow`: converts element of the fundamental group to an arrow in the fundamental groupoid
- `to_path`: converts element of the fundamental group to a (quotient of homotopic) path in the space
- `from_arrow`: constructs an element of the fundamental group from a self-arrow in the fundamental groupoid
- `from_path`: constructs an element of the fundamental group from a (quotient of homotopic) path in the space
These parallel  the similarly named functions for the fundamental group [here](https://github.com/leanprover-community/mathlib/blob/743ed5d1dd54fffd65e3a7f3522e4a4e85472964/src/algebraic_topology/fundamental_groupoid/basic.lean#L339-L355). They will prove helpful in doing computations with the fundamental group later e.g. for the disk, circle, etc.
#### Estimated changes
Modified src/algebraic_topology/fundamental_groupoid/fundamental_group.lean




## [2022-04-15 17:50:17](https://github.com/leanprover-community/mathlib/commit/c988c62)
chore(number_theory/function_field): fix typo ([#13464](https://github.com/leanprover-community/mathlib/pull/13464))
#### Estimated changes
Modified src/number_theory/function_field.lean




## [2022-04-15 17:50:16](https://github.com/leanprover-community/mathlib/commit/fbff76b)
refactor(number_theory/legendre_symbol/): move Gauss/Eisenstein lemma code to separate file ([#13449](https://github.com/leanprover-community/mathlib/pull/13449))
In preparation of further changes to number_theory/legendre_symbol/quadratic_reciprocity, this takes most of the code dealing with the lemmas of Gauss and Eisenstein out of quadratic_reciprocity.lean into a new file gauss_eisenstein_lemmas.lean.
Since I am not planning to do much (if anything) to this part of the code and it is rather involved and slows down Lean when I'm editing quadratic_reciprocity.lean, it makes sense to separate this code from the remainder of the file.
#### Estimated changes
Added src/number_theory/legendre_symbol/gauss_eisenstein_lemmas.lean
- \+ *lemma* legendre_symbol.Ico_map_val_min_abs_nat_abs_eq_Ico_map_id
- \+ *lemma* legendre_symbol.div_eq_filter_card
- \+ *lemma* legendre_symbol.eisenstein_lemma_aux
- \+ *lemma* legendre_symbol.gauss_lemma_aux
- \+ *lemma* legendre_symbol.sum_mul_div_add_sum_mul_div_eq_mul
- \+ *lemma* zmod.prod_Ico_one_prime
- \+ *lemma* zmod.wilsons_lemma

Modified src/number_theory/legendre_symbol/quadratic_reciprocity.lean
- \- *lemma* Ico_map_val_min_abs_nat_abs_eq_Ico_map_id
- \- *lemma* div_eq_filter_card
- \- *lemma* zmod.prod_Ico_one_prime
- \- *lemma* zmod.wilsons_lemma



## [2022-04-15 17:09:01](https://github.com/leanprover-community/mathlib/commit/0c2d68a)
feat(data/sym/sym2): mem_map/mem_congr/map_id' ([#13437](https://github.com/leanprover-community/mathlib/pull/13437))
Additional simplification lemmas, one to address non-simp-normal-form. (Also did a few proof simplifications.)
#### Estimated changes
Modified src/data/sym/sym2.lean
- \+/\- *lemma* sym2.map_comp
- \+ *lemma* sym2.map_congr
- \+ *lemma* sym2.map_id'
- \+/\- *lemma* sym2.map_id
- \+ *lemma* sym2.mem_map



## [2022-04-15 15:03:07](https://github.com/leanprover-community/mathlib/commit/d6c1cf1)
feat(analysis/normed_space/pointwise): Balls disjointness ([#13379](https://github.com/leanprover-community/mathlib/pull/13379))
Two balls in a real normed space are disjoint iff the sum of their radii is less than the distance between their centers.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *lemma* convex.combo_self

Modified src/algebra/order/ring.lean
- \+ *lemma* mul_lt_of_lt_one_left
- \+ *lemma* mul_lt_of_lt_one_right

Modified src/analysis/convex/basic.lean
- \- *lemma* convex.combo_self

Modified src/analysis/normed_space/pointwise.lean
- \+ *lemma* disjoint_ball_ball_iff
- \+ *lemma* disjoint_ball_closed_ball_iff
- \+ *lemma* disjoint_closed_ball_ball_iff
- \+ *lemma* disjoint_closed_ball_closed_ball_iff
- \+ *lemma* exists_dist_eq
- \+ *lemma* exists_dist_le_le
- \+ *lemma* exists_dist_le_lt
- \+ *lemma* exists_dist_lt_le
- \+ *lemma* exists_dist_lt_lt

Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* metric.ball_disjoint_ball
- \+ *lemma* metric.ball_disjoint_closed_ball
- \+/\- *lemma* metric.closed_ball_disjoint_ball
- \+/\- *lemma* metric.closed_ball_disjoint_closed_ball



## [2022-04-15 15:03:06](https://github.com/leanprover-community/mathlib/commit/2194eef)
chore(ring_theory/ideal/local_ring): generalize to semirings ([#13341](https://github.com/leanprover-community/mathlib/pull/13341))
#### Estimated changes
Modified src/logic/equiv/transfer_instance.lean


Modified src/number_theory/padics/padic_integers.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/graded_algebra/homogeneous_localization.lean


Modified src/ring_theory/ideal/local_ring.lean
- \+/\- *lemma* is_local_ring_hom_of_comp
- \+/\- *lemma* is_unit_map_iff
- \+/\- *lemma* is_unit_of_map_unit
- \- *lemma* local_of_nonunits_ideal
- \- *lemma* local_of_surjective
- \- *lemma* local_of_unique_max_ideal
- \- *lemma* local_of_unique_nonzero_prime
- \+/\- *lemma* local_ring.is_unit_of_mem_nonunits_one_sub_self
- \+/\- *lemma* local_ring.is_unit_or_is_unit_one_sub_self
- \+/\- *lemma* local_ring.ker_eq_maximal_ideal
- \+/\- *lemma* local_ring.maximal_ideal_unique
- \+/\- *lemma* local_ring.mem_maximal_ideal
- \- *lemma* local_ring.nonunits_add
- \+ *lemma* local_ring.of_is_unit_or_is_unit_one_sub_self
- \+ *lemma* local_ring.of_surjective
- \+ *lemma* local_ring.of_unique_max_ideal
- \+ *lemma* local_ring.of_unique_nonzero_prime
- \+ *lemma* map_mem_nonunits_iff
- \+/\- *lemma* map_nonunit
- \+/\- *theorem* of_irreducible_map
- \+/\- *lemma* ring_hom.domain_local_ring

Modified src/ring_theory/localization/at_prime.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/valuation/valuation_ring.lean




## [2022-04-15 15:03:05](https://github.com/leanprover-community/mathlib/commit/c65bebb)
feat(number_theory/padics/padic_numbers): add padic.add_valuation ([#12939](https://github.com/leanprover-community/mathlib/pull/12939))
We define the p-adic additive valuation on `Q_[p]`, as an `add_valuation` with values in `with_top Z`.
#### Estimated changes
Modified src/number_theory/padics/padic_numbers.lean
- \+ *lemma* padic.add_valuation.apply
- \+ *lemma* padic.add_valuation.map_add
- \+ *lemma* padic.add_valuation.map_mul
- \+ *lemma* padic.add_valuation.map_one
- \+ *lemma* padic.add_valuation.map_zero
- \+ *def* padic.add_valuation
- \+ *def* padic.add_valuation_def
- \+ *lemma* padic.valuation_map_add
- \+ *lemma* padic.valuation_map_mul



## [2022-04-15 13:10:57](https://github.com/leanprover-community/mathlib/commit/bbbea1c)
chore(*): clean up unnecessary uses of nat.cases_on ([#13454](https://github.com/leanprover-community/mathlib/pull/13454))
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/group_with_zero/power.lean


Modified src/algebra/homology/augment.lean


Modified src/data/int/basic.lean


Modified src/data/list/rotate.lean
- \+/\- *lemma* list.rotate_nil

Modified src/data/nat/basic.lean


Modified src/data/nat/log.lean


Modified src/data/polynomial/inductions.lean


Modified src/group_theory/specific_groups/dihedral.lean


Modified src/group_theory/specific_groups/quaternion.lean


Modified src/logic/equiv/fin.lean


Modified src/ring_theory/polynomial/pochhammer.lean


Modified src/set_theory/surreal/dyadic.lean




## [2022-04-15 11:12:38](https://github.com/leanprover-community/mathlib/commit/ebc8b44)
feat(analysis/normed_space/basic): `pi` and `prod` are `normed_algebra`s ([#13442](https://github.com/leanprover-community/mathlib/pull/13442))
Note that over an empty index type, `pi` is not a normed_algebra since it is trivial as a ring.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* nnorm_algebra_map_eq

Modified src/measure_theory/measure/haar_lebesgue.lean




## [2022-04-15 10:39:09](https://github.com/leanprover-community/mathlib/commit/d13f291)
feat(group_theory/group_action/conj_act): conjugation by the units of a monoid ([#13439](https://github.com/leanprover-community/mathlib/pull/13439))
I suspect we can make this even more general in future by introducing a compatibility typeclass, but this is good enough for me for now.
This also adds a stronger typeclass for the existing action of `conj_act K` where `K` is a `division_ring`.
#### Estimated changes
Modified src/group_theory/group_action/conj_act.lean
- \+/\- *lemma* conj_act.of_conj_act_zero
- \+/\- *lemma* conj_act.to_conj_act_zero
- \+ *lemma* conj_act.units_smul_def



## [2022-04-15 09:02:46](https://github.com/leanprover-community/mathlib/commit/dd51529)
feat(combinatorics/simple_graph/subgraph): delete_edges ([#13306](https://github.com/leanprover-community/mathlib/pull/13306))
Construct a subgraph from another by deleting edges.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean


Modified src/combinatorics/simple_graph/subgraph.lean
- \- *def* simple_graph.subgraph.coe
- \+ *lemma* simple_graph.subgraph.coe_delete_edges_eq
- \+ *lemma* simple_graph.subgraph.coe_delete_edges_le
- \+ *def* simple_graph.subgraph.delete_edges
- \+ *lemma* simple_graph.subgraph.delete_edges_adj
- \+ *lemma* simple_graph.subgraph.delete_edges_coe_eq
- \+ *lemma* simple_graph.subgraph.delete_edges_delete_edges
- \+ *lemma* simple_graph.subgraph.delete_edges_empty_eq
- \+ *lemma* simple_graph.subgraph.delete_edges_inter_edge_set_left_eq
- \+ *lemma* simple_graph.subgraph.delete_edges_inter_edge_set_right_eq
- \+ *lemma* simple_graph.subgraph.delete_edges_le
- \+ *lemma* simple_graph.subgraph.delete_edges_le_of_le
- \+ *lemma* simple_graph.subgraph.delete_edges_spanning_coe_eq
- \+ *lemma* simple_graph.subgraph.delete_edges_verts
- \- *def* simple_graph.subgraph.spanning_coe
- \+ *lemma* simple_graph.subgraph.spanning_coe_delete_edges_le



## [2022-04-15 04:32:08](https://github.com/leanprover-community/mathlib/commit/d6a46b7)
chore(scripts): update nolints.txt ([#13455](https://github.com/leanprover-community/mathlib/pull/13455))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-04-15 03:41:29](https://github.com/leanprover-community/mathlib/commit/6a5764b)
chore(analysis/normed_space/multilinear): use notation ([#13452](https://github.com/leanprover-community/mathlib/pull/13452))
* use notation `A [×n]→L[𝕜] B`;
* use `A → B` instead of `Π x : A, B`.
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean
- \+/\- *def* continuous_multilinear_map.restr



## [2022-04-15 02:47:13](https://github.com/leanprover-community/mathlib/commit/d81cedb)
feat(topology/algebra/module/multilinear): relax requirements for `continuous_multilinear_map.mk_pi_algebra` ([#13426](https://github.com/leanprover-community/mathlib/pull/13426))
`continuous_multilinear_map.mk_pi_algebra` and `continuous_multilinear_map.mk_pi_algebra_fin` do not need a norm on either the algebra or base ring; all they need is a topology on the algebra compatible with multiplication.
The much weaker typeclasses cause some elaboration issues in a few places, as the normed space can no longer be found by unification. Adding a non-dependent version of `continuous_multilinear_map.has_op_norm` largely resolves this, although a few  API proofs about `mk_pi_algebra` and `mk_pi_algebra_fin` end up quite underscore heavy.
This is the first step in being able to define `exp` without first choosing a `norm`.
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean
- \- *lemma* continuous_multilinear_map.mk_pi_algebra_apply
- \- *lemma* continuous_multilinear_map.mk_pi_algebra_fin_apply

Modified src/topology/algebra/module/multilinear.lean
- \+ *lemma* continuous_multilinear_map.mk_pi_algebra_apply
- \+ *lemma* continuous_multilinear_map.mk_pi_algebra_fin_apply



## [2022-04-14 20:31:11](https://github.com/leanprover-community/mathlib/commit/1506335)
chore(number_theory/zsqrtd/*): Missing docstrings and cleanups ([#13445](https://github.com/leanprover-community/mathlib/pull/13445))
Add docstrings to `gaussian_int` and `zsqrtd.norm` and inline definitions which did not have a docstring nor deserved one.
#### Estimated changes
Modified src/number_theory/pell.lean


Modified src/number_theory/zsqrtd/basic.lean
- \- *def* zsqrtd.add
- \+ *lemma* zsqrtd.add_def
- \- *theorem* zsqrtd.add_def
- \+ *lemma* zsqrtd.add_im
- \- *theorem* zsqrtd.add_im
- \+ *lemma* zsqrtd.add_re
- \- *theorem* zsqrtd.add_re
- \+ *lemma* zsqrtd.bit0_im
- \- *theorem* zsqrtd.bit0_im
- \+ *lemma* zsqrtd.bit0_re
- \- *theorem* zsqrtd.bit0_re
- \+/\- *theorem* zsqrtd.bit1_re
- \+/\- *def* zsqrtd.conj
- \+ *lemma* zsqrtd.conj_im
- \- *theorem* zsqrtd.conj_im
- \+/\- *lemma* zsqrtd.conj_neg
- \+ *lemma* zsqrtd.conj_re
- \- *theorem* zsqrtd.conj_re
- \- *theorem* zsqrtd.le_refl
- \- *def* zsqrtd.mul
- \+ *lemma* zsqrtd.mul_im
- \- *theorem* zsqrtd.mul_im
- \+ *lemma* zsqrtd.mul_re
- \- *theorem* zsqrtd.mul_re
- \- *def* zsqrtd.neg
- \+ *lemma* zsqrtd.neg_im
- \- *theorem* zsqrtd.neg_im
- \+ *lemma* zsqrtd.neg_re
- \- *theorem* zsqrtd.neg_re
- \+ *lemma* zsqrtd.nonneg.add
- \- *theorem* zsqrtd.nonneg_add
- \- *def* zsqrtd.one
- \- *def* zsqrtd.zero

Modified src/number_theory/zsqrtd/gaussian_int.lean




## [2022-04-14 17:32:49](https://github.com/leanprover-community/mathlib/commit/cbf3062)
feat(combinatorics/simple_graph/connectivity): define connected components ([#12766](https://github.com/leanprover-community/mathlib/pull/12766))
#### Estimated changes
Modified src/combinatorics/simple_graph/connectivity.lean
- \+ *def* simple_graph.connected_component
- \+ *def* simple_graph.connected_component_mk
- \+ *lemma* simple_graph.preconnected.subsingleton_connected_component



## [2022-04-14 15:31:41](https://github.com/leanprover-community/mathlib/commit/251bd84)
feat(group_theory/subgroup/basic): One more `mem_normalizer_iff` lemma ([#13395](https://github.com/leanprover-community/mathlib/pull/13395))
This PR golfs `mem_normalizer_iff'` and adds `mem_normalizer_iff''`. There are not so easy to deduce from each other, so it's nice to have these variations available.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.mem_normalizer_iff''
- \+/\- *lemma* subgroup.mem_normalizer_iff'



## [2022-04-14 15:31:40](https://github.com/leanprover-community/mathlib/commit/8bbc5ac)
feat(combinatorics/additive/salem_spencer): Salem-Spencer sets under images ([#13279](https://github.com/leanprover-community/mathlib/pull/13279))
A set `s` is Salem-Spencer iff its image under an injective Freiman hom is.
#### Estimated changes
Modified src/algebra/big_operators/multiset.lean
- \+ *lemma* multiset.prod_pair

Modified src/algebra/hom/freiman.lean
- \+ *lemma* map_mul_map_eq_map_mul_map

Modified src/combinatorics/additive/salem_spencer.lean
- \+ *lemma* mul_salem_spencer.image
- \+ *lemma* mul_salem_spencer.of_image

Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.card_pair



## [2022-04-14 14:09:05](https://github.com/leanprover-community/mathlib/commit/fecdd4b)
feat(measure_theory/card_measurable_space): `generate_measurable_rec s` gives precisely the generated sigma-algebra ([#12462](https://github.com/leanprover-community/mathlib/pull/12462))
#### Estimated changes
Modified src/measure_theory/card_measurable_space.lean
- \+ *theorem* measurable_space.Union_mem_generate_measurable_rec
- \- *lemma* measurable_space.cardinal_Union_generate_measurable_rec_le
- \+/\- *theorem* measurable_space.cardinal_measurable_set_le_continuum
- \+ *theorem* measurable_space.compl_mem_generate_measurable_rec
- \+ *theorem* measurable_space.empty_mem_generate_measurable_rec
- \+ *theorem* measurable_space.generate_measurable_eq_rec
- \+ *theorem* measurable_space.generate_measurable_rec_subset
- \- *theorem* measurable_space.generate_measurable_subset_rec
- \+ *theorem* measurable_space.self_subset_generate_measurable_rec

Modified src/set_theory/cardinal_ordinal.lean




## [2022-04-14 13:04:58](https://github.com/leanprover-community/mathlib/commit/adfe9c7)
feat(topology/algebra/order/compact): Sup is continuous ([#13347](https://github.com/leanprover-community/mathlib/pull/13347))
* Prove that the `Sup` of a binary function over a compact set is continuous in the second variable
* Some other lemmas about `Sup`
* Move and generalize `is_compact.bdd_[above|below]_image`
* from the sphere eversion project
#### Estimated changes
Modified src/topology/algebra/order/basic.lean
- \+ *lemma* is_compact.bdd_above_image
- \+ *lemma* is_compact.bdd_below_image

Modified src/topology/algebra/order/compact.lean
- \+ *lemma* is_compact.Sup_lt_iff_of_continuous
- \- *lemma* is_compact.bdd_above_image
- \- *lemma* is_compact.bdd_below_image
- \+ *lemma* is_compact.continuous_Inf
- \+ *lemma* is_compact.continuous_Sup
- \+ *lemma* is_compact.exists_Inf_image_eq_and_le
- \+ *lemma* is_compact.exists_Sup_image_eq_and_ge
- \+ *lemma* is_compact.lt_Inf_iff_of_continuous



## [2022-04-14 11:12:39](https://github.com/leanprover-community/mathlib/commit/936eb7e)
feat(analysis/normed_space/finite_dimension): a finite dimensional affine subspace is closed ([#13440](https://github.com/leanprover-community/mathlib/pull/13440))
#### Estimated changes
Modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* affine_subspace.is_closed_direction_iff

Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* affine_equiv.coe_to_homeomorph_of_finite_dimensional
- \+ *lemma* affine_equiv.coe_to_homeomorph_of_finite_dimensional_symm
- \+ *theorem* affine_equiv.continuous_of_finite_dimensional
- \+ *def* affine_equiv.to_homeomorph_of_finite_dimensional
- \+/\- *theorem* affine_map.continuous_of_finite_dimensional
- \+ *lemma* affine_subspace.closed_of_finite_dimensional



## [2022-04-14 11:12:38](https://github.com/leanprover-community/mathlib/commit/9631a91)
feat(ring_theory/multiplicity): int.nat_abs ([#13420](https://github.com/leanprover-community/mathlib/pull/13420))
Spinning off of [#12454](https://github.com/leanprover-community/mathlib/pull/12454)
#### Estimated changes
Modified src/ring_theory/multiplicity.lean
- \+ *theorem* multiplicity.int.nat_abs



## [2022-04-14 11:12:37](https://github.com/leanprover-community/mathlib/commit/88ba31c)
feat(measure_theory/constructions/pi): more `measure_preserving` lemmas ([#13404](https://github.com/leanprover-community/mathlib/pull/13404))
* Reformulate `map_pi_equiv_pi_subtype_prod` in terms of
  `measure_preserving`.
* Add more equivalences (bare equivalences, order isomorphisms, and
  measurable equivalences) on pi types.
#### Estimated changes
Modified src/logic/equiv/fin.lean
- \+ *def* equiv.pi_fin_succ_above_equiv
- \+ *def* order_iso.pi_fin_succ_above_iso

Modified src/logic/equiv/set.lean
- \+ *lemma* equiv.preimage_pi_equiv_pi_subtype_prod_symm_pi

Modified src/measure_theory/constructions/pi.lean
- \- *lemma* measure_theory.measure.map_pi_equiv_pi_subtype_prod
- \- *lemma* measure_theory.measure.map_pi_equiv_pi_subtype_prod_symm
- \+ *lemma* measure_theory.measure_preserving_pi_equiv_pi_subtype_prod
- \+ *lemma* measure_theory.measure_preserving_pi_fin_succ_above_equiv
- \+ *lemma* measure_theory.volume_preserving_pi_equiv_pi_subtype_prod
- \+ *lemma* measure_theory.volume_preserving_pi_fin_succ_above_equiv

Modified src/measure_theory/measurable_space.lean
- \+ *def* measurable_equiv.pi_equiv_pi_subtype_prod
- \+ *def* measurable_equiv.pi_fin_succ_above_equiv

Modified src/measure_theory/measure/lebesgue.lean
- \- *lemma* real.map_transvection_volume_pi
- \+ *lemma* real.volume_preserving_transvection_struct



## [2022-04-14 11:12:36](https://github.com/leanprover-community/mathlib/commit/dd34ffa)
refactor(group_theory/schur_zassenhaus): Golf using `is_complement'_stabilizer` ([#13392](https://github.com/leanprover-community/mathlib/pull/13392))
This PR golfs the proof of the abelian case of Schur-Zassenhaus using the new lemma `is_complement'_stabilizer`.
#### Estimated changes
Modified src/group_theory/schur_zassenhaus.lean
- \+/\- *lemma* subgroup.is_complement'_stabilizer_of_coprime



## [2022-04-14 11:12:35](https://github.com/leanprover-community/mathlib/commit/15b764d)
feat(group_theory/complement): Add more API for the action on left transversals ([#13363](https://github.com/leanprover-community/mathlib/pull/13363))
This PR adds more API for the action on left transversals.
#### Estimated changes
Modified src/group_theory/complement.lean
- \+ *lemma* subgroup.smul_apply_eq_smul_apply_inv_smul
- \+ *lemma* subgroup.smul_to_equiv

Modified src/group_theory/schur_zassenhaus.lean
- \- *lemma* subgroup.smul_symm_apply_eq_mul_symm_apply_inv_smul



## [2022-04-14 11:12:34](https://github.com/leanprover-community/mathlib/commit/769ec8c)
feat(group_theory/group_action/basic): Right multiplication satisfies the `quotient_action` axiom ([#13362](https://github.com/leanprover-community/mathlib/pull/13362))
This PR adds an instance stating that the right multiplication action of `H.normalizer.opposite` on `G` satisfies the `quotient_action` axiom. In particular, we automatically get the induced action of `H.normalizer.opposite` on `G ⧸ H`, so we can delete the existing instance. (Technically, the existing instance was stated in terms of `H.normalizerᵐᵒᵖ`, but I think `H.normalizer.opposite` is a more natural way to write it).
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \- *lemma* mul_action.quotient'.smul_coe
- \- *lemma* mul_action.quotient'.smul_mk



## [2022-04-14 11:12:33](https://github.com/leanprover-community/mathlib/commit/3676f11)
chore(order/complete_lattice): General cleanup ([#13323](https://github.com/leanprover-community/mathlib/pull/13323))
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+/\- *lemma* Inf_eq_bot
- \+/\- *theorem* Inf_eq_of_forall_ge_of_forall_gt_exists_lt
- \+/\- *theorem* Inf_eq_top
- \+/\- *lemma* Inf_le_iff
- \+/\- *theorem* Sup_eq_bot
- \+/\- *lemma* Sup_eq_top
- \+/\- *theorem* Sup_le
- \+/\- *theorem* Sup_le_iff
- \+/\- *lemma* inf_infi
- \+/\- *theorem* infi_const
- \+/\- *lemma* infi_eq_bot
- \+/\- *lemma* infi_inf
- \+/\- *theorem* infi_infi_eq_left
- \+/\- *theorem* infi_infi_eq_right
- \+/\- *lemma* infi_le_iff
- \+/\- *theorem* infi_sigma
- \+/\- *theorem* infi_subtype
- \+/\- *theorem* le_Inf
- \+/\- *theorem* le_Inf_iff
- \+/\- *lemma* le_infi_comp
- \+/\- *theorem* monotone_Inf_of_monotone
- \+/\- *theorem* monotone_Sup_of_monotone
- \+/\- *lemma* supr_comp_le
- \+/\- *theorem* supr_const
- \+/\- *lemma* supr_eq_top
- \+/\- *theorem* supr_sigma
- \+/\- *theorem* supr_supr_eq_left
- \+/\- *theorem* supr_supr_eq_right
- \+/\- *theorem* supr_union



## [2022-04-14 11:12:32](https://github.com/leanprover-community/mathlib/commit/7bb1081)
feat(category_theory): turn a split mono with cokernel into a biproduct ([#13184](https://github.com/leanprover-community/mathlib/pull/13184))
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.binary_bicone_of_split_epi_of_kernel
- \+ *def* category_theory.limits.binary_bicone_of_split_mono_of_cokernel
- \+ *def* category_theory.limits.is_bilimit_binary_bicone_of_split_epi_of_kernel
- \+ *def* category_theory.limits.is_bilimit_binary_bicone_of_split_mono_of_cokernel

Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/kernels.lean
- \+/\- *def* category_theory.limits.cokernel_epi_comp
- \+/\- *def* category_theory.limits.is_cokernel_epi_comp
- \+ *lemma* category_theory.limits.is_cokernel_epi_comp_desc
- \+/\- *def* category_theory.limits.is_kernel_comp_mono
- \+ *lemma* category_theory.limits.is_kernel_comp_mono_lift

Modified src/category_theory/preadditive/default.lean
- \+ *lemma* category_theory.preadditive.cokernel_cofork_of_cofork_of_π
- \+ *lemma* category_theory.preadditive.cokernel_cofork_of_cofork_π
- \+ *lemma* category_theory.preadditive.is_colimit_cofork_of_cokernel_cofork_desc
- \+ *lemma* category_theory.preadditive.is_limit_fork_of_kernel_fork_lift
- \+ *lemma* category_theory.preadditive.kernel_fork_of_fork_of_ι
- \+ *lemma* category_theory.preadditive.kernel_fork_of_fork_ι



## [2022-04-14 10:16:39](https://github.com/leanprover-community/mathlib/commit/2693ab5)
feat(number_theory/legendre_symbol): add directory legendre_symbol and move quadratic_reciprocity.lean into it ([#13441](https://github.com/leanprover-community/mathlib/pull/13441))
In preparation of adding more code in a structured way, this sets up a new directory `legendre_symbol` below `number_theory` and moves the file `quadratic_reciprocity.lean` there.
The imports in `src/number_theory/zsqrtd/gaussian_int.lean` and `archive/imo/imp2008_q3.lean` are changed accordingly.
#### Estimated changes
Modified archive/imo/imo2008_q3.lean


Renamed src/number_theory/quadratic_reciprocity.lean to src/number_theory/legendre_symbol/quadratic_reciprocity.lean


Modified src/number_theory/zsqrtd/gaussian_int.lean




## [2022-04-14 10:16:38](https://github.com/leanprover-community/mathlib/commit/eb2780b)
feat(topology/unit_interval): add lemmas ([#13344](https://github.com/leanprover-community/mathlib/pull/13344))
* also change the statement of `unit_interval.mul_mem`
* from the sphere eversion project
#### Estimated changes
Modified src/topology/unit_interval.lean
- \+ *lemma* unit_interval.div_mem
- \+ *lemma* unit_interval.fract_mem
- \+/\- *lemma* unit_interval.mul_mem
- \+ *lemma* unit_interval.one_mem
- \+/\- *def* unit_interval.symm
- \+ *lemma* unit_interval.zero_mem



## [2022-04-14 08:29:02](https://github.com/leanprover-community/mathlib/commit/87f8076)
chore(data/nat/factorial): tidy ([#13436](https://github.com/leanprover-community/mathlib/pull/13436))
I noticed this file had non-terminal simps, so I tidied it a little whilst removing them.
#### Estimated changes
Modified src/data/nat/factorial/basic.lean




## [2022-04-14 08:29:00](https://github.com/leanprover-community/mathlib/commit/dac4f18)
feat(data/mv_polynomial): add support_X_pow ([#13435](https://github.com/leanprover-community/mathlib/pull/13435))
A simple lemma to match the `polynomial` API
from flt-regular
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.support_X_pow



## [2022-04-14 08:28:58](https://github.com/leanprover-community/mathlib/commit/1378eab)
feat(complex/roots_of_unity):  extensionality ([#13431](https://github.com/leanprover-community/mathlib/pull/13431))
Primitive roots are equal iff their arguments are equal. Adds some useful specialisations, too.
#### Estimated changes
Modified src/analysis/complex/roots_of_unity.lean
- \+ *lemma* is_primitive_root.arg_eq_pi_iff
- \+ *lemma* is_primitive_root.arg_eq_zero_iff
- \+ *lemma* is_primitive_root.arg_ext



## [2022-04-14 06:30:11](https://github.com/leanprover-community/mathlib/commit/2249a24)
chore(*): suggestions from the generalisation linter ([#13092](https://github.com/leanprover-community/mathlib/pull/13092))
Prompted by zulip discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/An.20example.20of.20why.20formalization.20is.20useful
These are the "reasonable" suggestions from @alexjbest's generalisation linter up to `algebra.group.basic`.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+/\- *theorem* left_inverse_inv

Modified src/order/basic.lean
- \+/\- *lemma* eq.not_gt
- \+/\- *lemma* eq.not_lt



## [2022-04-14 03:43:29](https://github.com/leanprover-community/mathlib/commit/a565471)
chore(scripts): update nolints.txt ([#13438](https://github.com/leanprover-community/mathlib/pull/13438))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-04-14 02:07:07](https://github.com/leanprover-community/mathlib/commit/b62626e)
feat(complex/arg): arg_eq_zero_iff ([#13432](https://github.com/leanprover-community/mathlib/pull/13432))
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* complex.arg_eq_zero_iff



## [2022-04-13 23:29:58](https://github.com/leanprover-community/mathlib/commit/0765994)
chore(order/category/Preorder): reduce imports ([#13301](https://github.com/leanprover-community/mathlib/pull/13301))
Because `punit_instances` comes at the very end of the algebraic import hierarchy, we were requiring the entire algebraic hierarchy before we could begin compiling the theory of categorical limits.
This tweak substantially reduces the import dependencies.
#### Estimated changes
Modified src/analysis/normed/group/SemiNormedGroup.lean


Modified src/category_theory/Fintype.lean


Modified src/category_theory/category/preorder.lean
- \- *def* category_theory.Preorder_to_Cat

Modified src/category_theory/differential_object.lean


Modified src/category_theory/graded_object.lean


Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean


Modified src/category_theory/limits/shapes/pullbacks.lean


Modified src/category_theory/shift.lean


Modified src/category_theory/subobject/basic.lean


Modified src/category_theory/triangulated/basic.lean


Modified src/order/category/Preorder.lean
- \+ *def* Preorder_to_Cat



## [2022-04-13 22:15:36](https://github.com/leanprover-community/mathlib/commit/6f401ac)
feat(data/polynomial/*): suggestions from the generalization linter ([#13342](https://github.com/leanprover-community/mathlib/pull/13342))
#### Estimated changes
Modified src/data/complex/exponential.lean
- \+/\- *lemma* is_cau_geo_series

Modified src/data/polynomial/algebra_map.lean
- \+/\- *lemma* polynomial.eval₂_algebra_map_X

Modified src/data/polynomial/cancel_leads.lean


Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* polynomial.sum_fin

Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/div.lean
- \- *lemma* polynomial.sum_fin

Modified src/data/polynomial/eval.lean
- \+/\- *lemma* polynomial.support_map_subset

Modified src/data/polynomial/field_division.lean
- \+/\- *lemma* polynomial.degree_map
- \+/\- *lemma* polynomial.leading_coeff_map
- \+/\- *theorem* polynomial.monic_map_iff
- \+/\- *lemma* polynomial.nat_degree_map

Modified src/data/polynomial/integral_normalization.lean


Modified src/data/polynomial/monic.lean


Modified src/data/polynomial/reverse.lean
- \+/\- *lemma* polynomial.reverse_mul_of_domain
- \+/\- *lemma* polynomial.trailing_coeff_mul

Modified src/data/polynomial/ring_division.lean




## [2022-04-13 18:43:15](https://github.com/leanprover-community/mathlib/commit/76c969b)
chore(algebra/polynomial/big_operators): drop some nontrivial assumptions ([#13428](https://github.com/leanprover-community/mathlib/pull/13428))
#### Estimated changes
Modified src/algebra/polynomial/big_operators.lean
- \+/\- *lemma* polynomial.nat_degree_multiset_prod
- \+/\- *lemma* polynomial.nat_degree_multiset_prod_of_monic
- \+/\- *lemma* polynomial.nat_degree_prod
- \+/\- *lemma* polynomial.nat_degree_prod_of_monic



## [2022-04-13 17:31:46](https://github.com/leanprover-community/mathlib/commit/da13598)
feat(model_theory/encoding): Bundled encoding of terms ([#13226](https://github.com/leanprover-community/mathlib/pull/13226))
Bundles `term.list_encode` and `term.list_decode` into a `computability.encoding`
#### Estimated changes
Modified src/model_theory/encoding.lean
- \+/\- *theorem* first_order.language.term.card_le
- \+/\- *def* first_order.language.term.list_encode

Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* cardinal.mk_list_eq_max_mk_omega



## [2022-04-13 16:27:43](https://github.com/leanprover-community/mathlib/commit/9913860)
feat(ring_theory/tensor_product): add assoc for tensor product as an algebra homomorphism ([#13309](https://github.com/leanprover-community/mathlib/pull/13309))
By speeding up a commented out def, this goes from from ~100s to ~7s on my machine .
#### Estimated changes
Modified src/ring_theory/tensor_product.lean
- \+ *theorem* algebra.tensor_product.assoc_tmul



## [2022-04-13 10:56:42](https://github.com/leanprover-community/mathlib/commit/0c3f75b)
feat(analysis/normed_space/basic): normed division algebras over ℝ are also normed algebras over ℚ ([#13384](https://github.com/leanprover-community/mathlib/pull/13384))
This results shows that `algebra_rat` respects the norm in ` ℝ`-algebras that respect the norm.
The new instance carries no new data, as the norm and algebra structure are already defined elsewhere.
Probably there is a weaker requirement for compatibility, but I have no idea what it is, and the weakening can come later.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean




## [2022-04-13 10:56:41](https://github.com/leanprover-community/mathlib/commit/50ff59a)
feat(model_theory/skolem, satisfiability): A weak Downward Loewenheim Skolem ([#13141](https://github.com/leanprover-community/mathlib/pull/13141))
Defines a language and structure with built-in Skolem functions for a particular language
Proves a weak form of Downward Loewenheim Skolem: every structure has a small (in the universe sense) elementary substructure
Shows that `T` having a model in any universe implies `T.is_satisfiable`.
#### Estimated changes
Modified src/model_theory/bundled.lean


Modified src/model_theory/language_map.lean


Modified src/model_theory/satisfiability.lean
- \+/\- *lemma* first_order.language.Theory.model.is_satisfiable

Modified src/model_theory/semantics.lean


Added src/model_theory/skolem.lean
- \+ *theorem* first_order.language.exists_small_elementary_substructure
- \+ *def* first_order.language.skolem₁
- \+ *lemma* first_order.language.substructure.coe_sort_elementary_skolem₁_reduct
- \+ *lemma* first_order.language.substructure.skolem₁_reduct_is_elementary



## [2022-04-13 10:56:40](https://github.com/leanprover-community/mathlib/commit/647aa5b)
feat(model_theory/fraisse): Defines ultrahomogeneous structures, fixes Fraïssé limit definition ([#12994](https://github.com/leanprover-community/mathlib/pull/12994))
Defines ultrahomogeneous structures
Fixes the definition of a Fraïssé limit to require ultrahomogeneity
Completes the characterization of when a class is the age of a countable structure.
#### Estimated changes
Modified src/model_theory/fraisse.lean
- \+ *lemma* first_order.language.age.nonempty
- \- *theorem* first_order.language.age_fraisse_limit
- \+ *theorem* first_order.language.exists_countable_is_age_of_iff
- \+ *theorem* first_order.language.is_fraisse_limit.is_fraisse
- \+ *lemma* first_order.language.is_ultrahomogeneous.age_is_fraisse
- \+ *lemma* first_order.language.is_ultrahomogeneous.amalgamation_age
- \+ *def* first_order.language.is_ultrahomogeneous



## [2022-04-13 08:59:52](https://github.com/leanprover-community/mathlib/commit/6f59d77)
feat(order/bounded_order): Basic API for `subtype.order_bot` and  `subtype.order_top` ([#12904](https://github.com/leanprover-community/mathlib/pull/12904))
A few `simp` lemmas that were needed for `subtype.order_bot` and  `subtype.order_top`.
#### Estimated changes
Modified src/order/bounded_order.lean
- \+ *lemma* subtype.coe_eq_bot_iff
- \+ *lemma* subtype.coe_eq_top_iff
- \+ *lemma* subtype.mk_eq_bot_iff
- \+ *lemma* subtype.mk_eq_top_iff



## [2022-04-13 07:30:42](https://github.com/leanprover-community/mathlib/commit/5b8bb9b)
feat(category_theory/monoidal): define monoidal structure on the category of monoids in a braided monoidal category ([#13122](https://github.com/leanprover-community/mathlib/pull/13122))
Building on the preliminary work from the previous PRs, we finally show that monoids in a braided monoidal category form a monoidal category.
#### Estimated changes
Modified src/category_theory/monoidal/Mon_.lean
- \+ *lemma* Mon_.Mon_tensor_mul_assoc
- \+ *lemma* Mon_.Mon_tensor_mul_one
- \+ *lemma* Mon_.Mon_tensor_one_mul
- \+ *def* Mon_.iso_of_iso
- \+ *lemma* Mon_.mul_associator
- \+ *lemma* Mon_.mul_left_unitor
- \+ *lemma* Mon_.mul_right_unitor
- \+ *lemma* Mon_.one_associator
- \+ *lemma* Mon_.one_left_unitor
- \+ *lemma* Mon_.one_right_unitor

Modified src/category_theory/monoidal/braided.lean




## [2022-04-13 04:14:04](https://github.com/leanprover-community/mathlib/commit/1de6ce9)
chore(scripts): update nolints.txt ([#13408](https://github.com/leanprover-community/mathlib/pull/13408))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-04-13 04:14:03](https://github.com/leanprover-community/mathlib/commit/b0bd771)
fix(combinatorics/simple_graph/connectivity): correctly generalized variables ([#13405](https://github.com/leanprover-community/mathlib/pull/13405))
#### Estimated changes
Modified src/combinatorics/simple_graph/connectivity.lean




## [2022-04-13 04:14:02](https://github.com/leanprover-community/mathlib/commit/917fc96)
refactor(set_theory/cofinality): Normalize names ([#13400](https://github.com/leanprover-community/mathlib/pull/13400))
We rename lemmas of the form `is_regular (foo x)` to `is_regular_foo` instead of `foo_is_regular`.
#### Estimated changes
Modified src/set_theory/cofinality.lean
- \- *theorem* cardinal.aleph'_succ_is_regular
- \- *theorem* cardinal.aleph_succ_is_regular
- \- *theorem* cardinal.cof_is_regular
- \+ *theorem* cardinal.is_regular_aleph'_succ
- \+ *theorem* cardinal.is_regular_aleph_succ
- \+ *theorem* cardinal.is_regular_cof
- \+ *theorem* cardinal.is_regular_omega
- \+ *theorem* cardinal.is_regular_succ
- \- *theorem* cardinal.omega_is_regular
- \- *theorem* cardinal.succ_is_regular



## [2022-04-13 02:38:14](https://github.com/leanprover-community/mathlib/commit/ac7a356)
chore(set_theory/*): Fix lint ([#13399](https://github.com/leanprover-community/mathlib/pull/13399))
Add missing docstrings and `inhabited` instances or a `nolint` when an `inhabited` instance isn't reasonable.
#### Estimated changes
Modified src/set_theory/cofinality.lean


Modified src/set_theory/game.lean


Modified src/set_theory/pgame.lean
- \+/\- *def* pgame.left_moves
- \+/\- *def* pgame.right_moves

Modified src/set_theory/zfc.lean
- \+/\- *def* pSet.type



## [2022-04-13 02:38:13](https://github.com/leanprover-community/mathlib/commit/8c9ee31)
feat(order/conditionally_complete_lattice): Add `le_cSup_iff` ([#13321](https://github.com/leanprover-community/mathlib/pull/13321))
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+ *theorem* cInf_le_iff
- \+ *theorem* le_cSup_iff'
- \+ *theorem* le_cSup_iff



## [2022-04-13 00:37:31](https://github.com/leanprover-community/mathlib/commit/fb94880)
refactor(category_theory/shift): tighten scope of local attribute [reducible] ([#13335](https://github.com/leanprover-community/mathlib/pull/13335))
In all the files dealing with shifts on categories, we have a sprinkling of `local attribute [reducible]`, without which we get somewhat mysterious errors.
However with them, we produce some very fragile proof states (recently I was upset to see that shifting by `(0 : A)` and shifting by the tensor unit in `discrete A` were not definitionally commuting...).
I've been attempting to refactor this part of the library so we just never need to use `local attribute [reducible]`, in the hope of making these problems go away.
Having failed so far, this PR simply tightens the scopes of these local attributes as narrowly as possible (or in cases removes them entirely), so it is clearer exactly what is relying on them to work.
#### Estimated changes
Modified src/category_theory/differential_object.lean


Modified src/category_theory/graded_object.lean


Modified src/category_theory/shift.lean


Modified src/category_theory/triangulated/rotate.lean




## [2022-04-12 23:52:20](https://github.com/leanprover-community/mathlib/commit/f496ef4)
feat(computability/{language/regular_expressions): Map along a function ([#13197](https://github.com/leanprover-community/mathlib/pull/13197))
Define `language.map` and `regular_expression.map`.
#### Estimated changes
Modified src/computability/language.lean
- \+ *def* language.map
- \+ *lemma* language.map_id
- \+ *lemma* language.map_map
- \+ *lemma* language.map_star

Modified src/computability/regular_expressions.lean
- \+ *def* regular_expression.map
- \+ *lemma* regular_expression.map_id
- \+ *lemma* regular_expression.map_map
- \+/\- *def* regular_expression.matches
- \+ *lemma* regular_expression.matches_map



## [2022-04-12 23:00:49](https://github.com/leanprover-community/mathlib/commit/7ece83e)
feat(topology/homotopy): Add definition of contractible spaces ([#12731](https://github.com/leanprover-community/mathlib/pull/12731))
#### Estimated changes
Added src/topology/homotopy/contractible.lean
- \+ *lemma* continuous_map.nullhomotopic.comp_left
- \+ *lemma* continuous_map.nullhomotopic.comp_right
- \+ *def* continuous_map.nullhomotopic
- \+ *lemma* continuous_map.nullhomotopic_of_constant
- \+ *lemma* contractible_iff_id_nullhomotopic
- \+ *lemma* id_nullhomotopic



## [2022-04-12 22:12:37](https://github.com/leanprover-community/mathlib/commit/94a52c4)
feat(category_theory/monoidal): prove that in a braided monoidal category unitors and associators are monoidal natural transformations ([#13121](https://github.com/leanprover-community/mathlib/pull/13121))
This PR contains proofs of lemmas that are used in the stacked PR to define a monoidal structure on the category of monoids in a braided monoidal category.  The lemmas can be summarised by saying that in a braided monoidal category unitors and associators are monoidal natural transformations.
Note that for these statements to make sense we would need to define monoidal functors that are sources and targets of these monoidal natural transformations.  For example, the morphisms `(α_ X Y Z).hom` are the components of a monoidal natural transformation
```
(tensor.prod (𝟭 C)) ⊗⋙ tensor  ⟶ Α_ ⊗⋙ ((𝟭 C).prod tensor) ⊗⋙ tensor
```
where `Α_ : monoidal_functor ((C × C) × C) (C × (C × C))` is the associator functor given by `λ X, (X.1.1, (X.1.2, X.2))` on objects.  I didn't define the functor `Α_`.  (The easiest way would be to build it up using `prod'` we have already defined from `fst` and `snd`, which we would need to define as monoidal functors.)  Instead, I stated and proved the commutative diagram that expresses the monoidality of the above transformation.  Ditto for unitors.  Please let me know if you'd like me to define all the required functors and monoidal natural transformations.  The monoidal natural transformations themselves are not used in the proof that the category of monoids in a braided monoidal category is monoidal and only provide meaningful names to the lemmas that are used in the proof.
#### Estimated changes
Modified src/category_theory/monoidal/braided.lean
- \+ *lemma* category_theory.associator_monoidal
- \+ *lemma* category_theory.associator_monoidal_aux
- \+ *lemma* category_theory.left_unitor_monoidal
- \+ *lemma* category_theory.right_unitor_monoidal



## [2022-04-12 20:53:45](https://github.com/leanprover-community/mathlib/commit/78ea75a)
feat(order/filter/cofinite): add lemmas, golf ([#13394](https://github.com/leanprover-community/mathlib/pull/13394))
* add `filter.comap_le_cofinite`,
  `function.injective.comap_cofinite_eq`, and
  `filter.has_basis.coprod`;
* rename `at_top_le_cofinite` to `filter.at_top_le_cofinite`;
* golf `filter.coprod_cofinite` and `filter.Coprod_cofinite`, move
  them below `filter.comap_cofinite_le`;
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.coprod

Modified src/order/filter/cofinite.lean
- \- *lemma* at_top_le_cofinite
- \+/\- *lemma* filter.Coprod_cofinite
- \+ *lemma* filter.at_top_le_cofinite
- \+ *lemma* filter.comap_cofinite_le
- \+/\- *lemma* filter.coprod_cofinite
- \+/\- *lemma* filter.eventually_cofinite_ne
- \+/\- *lemma* filter.le_cofinite_iff_compl_singleton_mem
- \+ *lemma* filter.le_cofinite_iff_eventually_ne
- \+/\- *lemma* filter.tendsto.exists_forall_ge
- \+/\- *lemma* filter.tendsto.exists_forall_le
- \+/\- *lemma* filter.tendsto.exists_within_forall_ge
- \+/\- *lemma* finset.eventually_cofinite_nmem
- \+ *lemma* function.injective.comap_cofinite_eq
- \+/\- *lemma* function.injective.tendsto_cofinite
- \+/\- *lemma* set.finite.compl_mem_cofinite
- \+/\- *lemma* set.finite.eventually_cofinite_nmem
- \+/\- *lemma* set.infinite_iff_frequently_cofinite



## [2022-04-12 20:08:54](https://github.com/leanprover-community/mathlib/commit/da4ec7e)
feat(ring_theory/valuation/valuation_subring): Valuation subrings of a field ([#12741](https://github.com/leanprover-community/mathlib/pull/12741))
#### Estimated changes
Added src/ring_theory/valuation/valuation_subring.lean
- \+ *lemma* valuation_subring.algebra_map_apply
- \+ *lemma* valuation_subring.ext
- \+ *lemma* valuation_subring.le_top
- \+ *lemma* valuation_subring.mem_carrier
- \+ *lemma* valuation_subring.mem_of_valuation_le_one
- \+ *lemma* valuation_subring.mem_or_inv_mem
- \+ *lemma* valuation_subring.mem_to_subring
- \+ *lemma* valuation_subring.mem_top
- \+ *def* valuation_subring.valuation
- \+ *lemma* valuation_subring.valuation_eq_iff
- \+ *lemma* valuation_subring.valuation_le_iff
- \+ *lemma* valuation_subring.valuation_le_one
- \+ *lemma* valuation_subring.valuation_le_one_iff
- \+ *lemma* valuation_subring.valuation_surjective



## [2022-04-12 18:28:33](https://github.com/leanprover-community/mathlib/commit/e72f275)
feat(number_theory/qudratic_reciprocity): change type of `a` in API lemmas to `int` ([#13393](https://github.com/leanprover-community/mathlib/pull/13393))
This is step 2 in the overhaul of number_theory/qudratic_reciprocity.
The only changes are that the argument `a` is now of type `int` rather than `nat` in a bunch of statements.
This is more natural, since the corresponding (now second) argument of `legendre_symnbol` is of type `int`; it therefore makes the API lemmas more easily useable.
#### Estimated changes
Modified src/number_theory/quadratic_reciprocity.lean
- \+/\- *lemma* zmod.gauss_lemma
- \+/\- *lemma* zmod.legendre_sym_eq_one_iff
- \+/\- *lemma* zmod.legendre_sym_eq_one_or_neg_one
- \+/\- *lemma* zmod.legendre_sym_eq_pow
- \+/\- *lemma* zmod.legendre_sym_eq_zero_iff



## [2022-04-12 18:28:32](https://github.com/leanprover-community/mathlib/commit/3bbb847)
chore(*): remove instance arguments that are inferrable from earlier ([#13386](https://github.com/leanprover-community/mathlib/pull/13386))
Some lemmas have typeclass arguments that are in fact inferrable from the earlier ones, at least when everything is Prop valued this is unecessary so we clean up a few cases as they likely stem from typos or library changes. 
- `src/field_theory/finiteness.lean` it wasn't known at the time ([#7644](https://github.com/leanprover-community/mathlib/pull/7644)) that a division ring was noetherian, but now it is ([#7661](https://github.com/leanprover-community/mathlib/pull/7661))
- `src/category_theory/simple.lean` any abelian category has all cokernels so no need to assume it seperately
- `src/analysis/convex/extreme.lean` assumed `linear_ordered_field` and `no_smul_zero_divisors` which is unnecessary, we take this as a sign that this and a couple of other convexity results should be generalized to densely ordered linear ordered rings (of which there are examples that are not fields) cc @YaelDillies
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+/\- *lemma* left_mem_open_segment_iff
- \+/\- *lemma* right_mem_open_segment_iff

Modified src/analysis/convex/extreme.lean
- \+/\- *lemma* mem_extreme_points_iff_forall_segment

Modified src/analysis/inner_product_space/projection.lean


Modified src/category_theory/simple.lean


Modified src/field_theory/finiteness.lean


Modified src/linear_algebra/finite_dimensional.lean




## [2022-04-12 18:28:30](https://github.com/leanprover-community/mathlib/commit/116ac71)
feat(analysis/normed_space/exponential): exponentials of negations, scalar actions, and sums ([#13036](https://github.com/leanprover-community/mathlib/pull/13036))
The new lemmas are:
* `exp_invertible_of_mem_ball`
* `exp_invertible`
* `is_unit_exp_of_mem_ball`
* `is_unit_exp`
* `ring.inverse_exp`
* `exp_neg_of_mem_ball`
* `exp_neg`
* `exp_sum_of_commute`
* `exp_sum`
* `exp_nsmul`
* `exp_zsmul`
I don't know enough about the radius of convergence of `exp` to know if `exp_nsmul` holds more generally under extra conditions.
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *lemma* edist_add_left
- \+ *lemma* edist_add_right
- \+ *lemma* edist_neg_neg
- \+ *lemma* edist_sub_left
- \+ *lemma* edist_sub_right

Modified src/analysis/normed_space/exponential.lean
- \+ *lemma* commute.exp
- \+/\- *lemma* exp_add_of_commute
- \+ *lemma* exp_neg
- \+ *lemma* exp_neg_of_mem_ball
- \+ *lemma* exp_nsmul
- \+ *lemma* exp_sum
- \+ *lemma* exp_sum_of_commute
- \+/\- *lemma* exp_zero
- \+ *lemma* exp_zsmul
- \+ *lemma* inv_of_exp
- \+ *lemma* inv_of_exp_of_mem_ball
- \+ *lemma* is_unit_exp
- \+ *lemma* is_unit_exp_of_mem_ball
- \+ *lemma* ring.inverse_exp



## [2022-04-12 17:21:31](https://github.com/leanprover-community/mathlib/commit/949021d)
feat(ring_theory/algebraic): Rational numbers are algebraic ([#13367](https://github.com/leanprover-community/mathlib/pull/13367))
#### Estimated changes
Modified src/ring_theory/algebraic.lean
- \+ *lemma* is_algebraic_int
- \+ *lemma* is_algebraic_rat



## [2022-04-12 17:21:10](https://github.com/leanprover-community/mathlib/commit/c994ab3)
feat(category_theory/monoidal): define a monoidal structure on the tensor product functor of a braided monoidal category ([#13150](https://github.com/leanprover-community/mathlib/pull/13150))
Given a braided monoidal category `C`, equip its tensor product functor, viewed as a functor from `C × C` to `C` with a strength that turns it into a monoidal functor.
See [#13033](https://github.com/leanprover-community/mathlib/pull/13033) for a discussion of the motivation of this definition.
(This PR replaces [#13034](https://github.com/leanprover-community/mathlib/pull/13034) which was accidentally closed.)
#### Estimated changes
Modified docs/references.bib


Modified src/category_theory/monoidal/braided.lean
- \+ *lemma* category_theory.left_unitor_inv_braiding
- \+ *lemma* category_theory.right_unitor_inv_braiding
- \+ *lemma* category_theory.tensor_associativity
- \+ *lemma* category_theory.tensor_associativity_aux
- \+ *lemma* category_theory.tensor_left_unitality
- \+ *def* category_theory.tensor_monoidal
- \+ *lemma* category_theory.tensor_right_unitality
- \+ *def* category_theory.tensor_μ
- \+ *lemma* category_theory.tensor_μ_def₁
- \+ *lemma* category_theory.tensor_μ_def₂
- \+ *lemma* category_theory.tensor_μ_natural

Modified src/category_theory/monoidal/category.lean
- \+/\- *def* category_theory.monoidal_category.tensor



## [2022-04-12 15:33:18](https://github.com/leanprover-community/mathlib/commit/4c0a274)
doc(model_theory/order): typo in docstrings ([#13390](https://github.com/leanprover-community/mathlib/pull/13390))
#### Estimated changes
Modified src/model_theory/order.lean




## [2022-04-12 15:33:16](https://github.com/leanprover-community/mathlib/commit/0c8b808)
fix(measure_theory/function/lp_space): fix an instance diamond in `measure_theory.Lp.has_edist` ([#13388](https://github.com/leanprover-community/mathlib/pull/13388))
This also changes the definition of `edist` to something definitionally nicer
#### Estimated changes
Modified src/measure_theory/function/lp_space.lean




## [2022-04-12 15:33:15](https://github.com/leanprover-community/mathlib/commit/c21561a)
feat(algebra/direct_sum): Reindexing direct sums ([#13076](https://github.com/leanprover-community/mathlib/pull/13076))
Lemmas to reindex direct sums, as well as to rewrite direct sums over an option or sigma type.
#### Estimated changes
Modified src/algebra/direct_sum/basic.lean
- \+ *def* direct_sum.equiv_congr_left
- \+ *lemma* direct_sum.equiv_congr_left_apply
- \+ *lemma* direct_sum.sigma_curry_apply
- \+ *lemma* direct_sum.sigma_uncurry_apply

Modified src/algebra/direct_sum/module.lean
- \+ *def* direct_sum.lequiv_congr_left
- \+ *lemma* direct_sum.lequiv_congr_left_apply
- \+ *lemma* direct_sum.sigma_lcurry_apply
- \+ *lemma* direct_sum.sigma_luncurry_apply

Modified src/data/dfinsupp/basic.lean
- \+ *def* dfinsupp.comap_domain'[Π
- \+ *lemma* dfinsupp.comap_domain'_add
- \+ *lemma* dfinsupp.comap_domain'_apply
- \+ *lemma* dfinsupp.comap_domain'_smul
- \+ *lemma* dfinsupp.comap_domain'_zero
- \+ *lemma* dfinsupp.comap_domain_add
- \+ *lemma* dfinsupp.comap_domain_apply
- \+ *lemma* dfinsupp.comap_domain_smul
- \+ *lemma* dfinsupp.comap_domain_zero
- \+ *def* dfinsupp.equiv_congr_left
- \+ *lemma* dfinsupp.equiv_prod_dfinsupp_add
- \+ *lemma* dfinsupp.equiv_prod_dfinsupp_smul
- \+ *def* dfinsupp.extend_with
- \+ *lemma* dfinsupp.extend_with_none
- \+ *lemma* dfinsupp.extend_with_some
- \+ *lemma* dfinsupp.sigma_curry_add
- \+ *lemma* dfinsupp.sigma_curry_apply
- \+ *lemma* dfinsupp.sigma_curry_smul
- \+ *lemma* dfinsupp.sigma_curry_zero
- \+ *lemma* dfinsupp.sigma_uncurry_add
- \+ *lemma* dfinsupp.sigma_uncurry_apply
- \+ *lemma* dfinsupp.sigma_uncurry_smul
- \+ *lemma* dfinsupp.sigma_uncurry_zero



## [2022-04-12 13:28:12](https://github.com/leanprover-community/mathlib/commit/745099b)
chore(*/parity): Generalize lemmas and clarify names  ([#13268](https://github.com/leanprover-community/mathlib/pull/13268))
Generalizations
#### Estimated changes
Modified src/algebra/geom_sum.lean


Modified src/algebra/group_power/basic.lean
- \+ *lemma* neg_one_sq
- \+/\- *lemma* neg_sq

Modified src/algebra/order/sub.lean
- \+ *lemma* tsub_add_tsub_comm

Modified src/algebra/parity.lean
- \+ *lemma* even.neg_one_pow
- \+ *lemma* even.neg_one_zpow
- \+ *lemma* even.neg_pow
- \+ *lemma* even.neg_zpow
- \+ *lemma* even.sub_odd
- \- *theorem* even.sub_odd
- \+ *lemma* even.tsub_even
- \- *lemma* even.zpow_neg
- \- *lemma* even.zpow_nonneg
- \+ *lemma* even_iff_exists_bit0
- \+/\- *lemma* is_square.map
- \+/\- *lemma* is_square_sq
- \+/\- *lemma* odd.neg
- \+ *lemma* odd.neg_one_pow
- \+ *lemma* odd.neg_one_zpow
- \+ *lemma* odd.neg_pow
- \+ *lemma* odd.neg_zpow
- \+ *lemma* odd.sub_even
- \- *theorem* odd.sub_even
- \+/\- *lemma* odd.sub_odd
- \- *theorem* odd.zpow_nonneg
- \+/\- *lemma* odd_bit1
- \+ *lemma* odd_iff_exists_bit1

Modified src/analysis/convex/specific_functions.lean


Modified src/data/int/parity.lean


Modified src/data/nat/digits.lean


Modified src/data/nat/parity.lean
- \- *theorem* nat.even.sub_even
- \- *theorem* nat.neg_one_pow_eq_one_iff_even
- \- *theorem* nat.neg_one_pow_of_even
- \- *theorem* nat.neg_one_pow_of_odd
- \- *theorem* nat.neg_one_sq
- \+ *lemma* neg_one_pow_eq_one_iff_even

Modified src/group_theory/specific_groups/alternating.lean


Modified src/linear_algebra/general_linear_group.lean


Modified src/linear_algebra/special_linear_group.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/cyclotomic/discriminant.lean


Modified src/number_theory/cyclotomic/primitive_roots.lean




## [2022-04-12 12:36:48](https://github.com/leanprover-community/mathlib/commit/4b45a71)
feat(counterexamples/pseudoelement): add counterexample to uniqueness in category_theory.abelian.pseudoelement.pseudo_pullback ([#13387](https://github.com/leanprover-community/mathlib/pull/13387))
Borceux claims that the pseudoelement constructed in `category_theory.abelian.pseudoelement.pseudo_pullback` is unique. We show here that this claim is false.
#### Estimated changes
Added counterexamples/pseudoelement.lean
- \+ *lemma* category_theory.abelian.pseudoelement.exist_ne_and_fst_eq_fst_and_snd_eq_snd
- \+ *lemma* category_theory.abelian.pseudoelement.fst_mk_x_eq_fst_mk_y
- \+ *lemma* category_theory.abelian.pseudoelement.fst_x_pseudo_eq_fst_y
- \+ *lemma* category_theory.abelian.pseudoelement.mk_x_ne_mk_y
- \+ *lemma* category_theory.abelian.pseudoelement.snd_mk_x_eq_snd_mk_y
- \+ *lemma* category_theory.abelian.pseudoelement.snd_x_pseudo_eq_snd_y
- \+ *def* category_theory.abelian.pseudoelement.x
- \+ *lemma* category_theory.abelian.pseudoelement.x_not_pseudo_eq
- \+ *def* category_theory.abelian.pseudoelement.y

Modified src/category_theory/abelian/pseudoelements.lean
- \+ *lemma* category_theory.abelian.pseudoelement.Module.eq_range_of_pseudoequal



## [2022-04-12 12:36:47](https://github.com/leanprover-community/mathlib/commit/73ec5b2)
chore(category_theory/closed/monoidal): correct error in doc string ([#13385](https://github.com/leanprover-community/mathlib/pull/13385))
Sorry, should have done this immediately when @b-mehta pointed out my mistake.
#### Estimated changes
Modified src/category_theory/closed/monoidal.lean




## [2022-04-12 12:36:46](https://github.com/leanprover-community/mathlib/commit/ef8e256)
feat(number_theory/cyclotomic): alg-closed fields are cyclotomic extensions over themselves ([#13366](https://github.com/leanprover-community/mathlib/pull/13366))
#### Estimated changes
Modified archive/100-theorems-list/37_solution_of_cubic.lean


Modified src/number_theory/cyclotomic/basic.lean
- \+ *lemma* is_alg_closed.is_cyclotomic_extension

Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* is_primitive_root.is_root_cyclotomic
- \- *lemma* polynomial.is_root_cyclotomic



## [2022-04-12 11:56:25](https://github.com/leanprover-community/mathlib/commit/5534e24)
chore(category_theory/preadditive/biproducts): Speed up `biprod.column_nonzero_of_iso` ([#13383](https://github.com/leanprover-community/mathlib/pull/13383))
From 76s down to 2s. The decidability synthesis in `by_contradiction` is stupidly expensive.
#### Estimated changes
Modified src/category_theory/preadditive/biproducts.lean




## [2022-04-12 11:56:24](https://github.com/leanprover-community/mathlib/commit/4bcc532)
refactor(control/fold): don't use is_monoid_hom ([#13350](https://github.com/leanprover-community/mathlib/pull/13350))
#### Estimated changes
Modified src/control/fold.lean
- \+/\- *def* monoid.foldl.of_free_monoid
- \+/\- *def* monoid.foldr.of_free_monoid
- \+/\- *def* monoid.mfoldl.of_free_monoid
- \+/\- *def* monoid.mfoldr.of_free_monoid
- \- *lemma* traversable.fold_foldl
- \- *lemma* traversable.fold_foldr
- \- *lemma* traversable.fold_mfoldl
- \- *lemma* traversable.fold_mfoldr
- \- *lemma* traversable.free.map.is_monoid_hom
- \+/\- *def* traversable.free.map
- \+/\- *def* traversable.map_fold
- \- *lemma* traversable.mfoldl.unop_of_free_monoid



## [2022-04-12 10:40:32](https://github.com/leanprover-community/mathlib/commit/8b27c45)
feat(order/filter/pointwise): Missing pointwise operations ([#13170](https://github.com/leanprover-community/mathlib/pull/13170))
Define inversion/negation, division/subtraction, scalar multiplication/addition, scaling/translation, scalar subtraction of filters using the new `filter.map₂`. Golf the existing API.
#### Estimated changes
Modified src/order/filter/pointwise.lean
- \+ *lemma* filter.bot_div
- \+ *lemma* filter.bot_mul
- \+ *lemma* filter.bot_smul
- \+ *lemma* filter.bot_vsub
- \+ *lemma* filter.div_bot
- \+ *lemma* filter.div_eq_bot_iff
- \+ *lemma* filter.div_mem_div
- \+ *lemma* filter.div_ne_bot_iff
- \+ *lemma* filter.eventually_one
- \+ *lemma* filter.inv_mem_inv
- \+ *lemma* filter.le_mul_iff
- \+ *lemma* filter.le_one_iff
- \+ *lemma* filter.le_smul_iff
- \+ *lemma* filter.le_vsub_iff
- \+ *lemma* filter.map_inv'
- \+ *lemma* filter.map_smul
- \+ *lemma* filter.map₂_div
- \+ *lemma* filter.map₂_mul
- \+ *lemma* filter.map₂_smul
- \+ *lemma* filter.map₂_vsub
- \+ *lemma* filter.mem_div
- \+ *lemma* filter.mem_inv
- \- *lemma* filter.mem_mul
- \+ *lemma* filter.mem_mul_iff
- \+/\- *lemma* filter.mem_one
- \+ *lemma* filter.mem_smul
- \+ *lemma* filter.mem_smul_filter
- \+ *lemma* filter.mem_vsub
- \+ *lemma* filter.mul_bot
- \+ *lemma* filter.mul_eq_bot_iff
- \+/\- *lemma* filter.mul_mem_mul
- \+ *lemma* filter.mul_ne_bot_iff
- \+ *lemma* filter.ne_bot.div
- \+ *lemma* filter.ne_bot.inv
- \+/\- *lemma* filter.ne_bot.mul
- \+ *lemma* filter.ne_bot.smul
- \+ *lemma* filter.ne_bot.smul_filter
- \+ *lemma* filter.ne_bot.vsub
- \+ *lemma* filter.ne_bot_inv_iff
- \+/\- *lemma* filter.one_mem_one
- \+ *lemma* filter.principal_one
- \+ *lemma* filter.pure_one
- \+ *lemma* filter.smul_bot
- \+ *lemma* filter.smul_eq_bot_iff
- \+ *lemma* filter.smul_filter_bot
- \+ *lemma* filter.smul_filter_eq_bot_iff
- \+ *lemma* filter.smul_filter_le_smul_filter
- \+ *lemma* filter.smul_filter_ne_bot_iff
- \+ *lemma* filter.smul_le_smul
- \+ *lemma* filter.smul_le_smul_left
- \+ *lemma* filter.smul_le_smul_right
- \+ *lemma* filter.smul_mem_smul
- \+ *lemma* filter.smul_ne_bot_iff
- \+ *lemma* filter.smul_set_mem_smul_filter
- \+ *lemma* filter.tendsto.div_div
- \+ *lemma* filter.tendsto.inv_inv
- \+ *lemma* filter.tendsto_one
- \+ *lemma* filter.vsub_bot
- \+ *lemma* filter.vsub_eq_bot_iff
- \+ *lemma* filter.vsub_le_vsub
- \+ *lemma* filter.vsub_le_vsub_left
- \+ *lemma* filter.vsub_le_vsub_right
- \+ *lemma* filter.vsub_mem_vsub
- \+ *lemma* filter.vsub_ne_bot_iff

Modified src/topology/algebra/filter_basis.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/order/basic.lean
- \- *lemma* filter.map_neg
- \+ *lemma* filter.map_neg_eq_comap_neg



## [2022-04-12 08:46:24](https://github.com/leanprover-community/mathlib/commit/9984960)
fix(counterexamples): typo in module docstring ([#13378](https://github.com/leanprover-community/mathlib/pull/13378))
#### Estimated changes
Modified counterexamples/homogeneous_prime_not_prime.lean




## [2022-04-12 08:46:23](https://github.com/leanprover-community/mathlib/commit/36bafae)
feat(topology/bornology/basic): review ([#13374](https://github.com/leanprover-community/mathlib/pull/13374))
* add lemmas;
* upgrade some implications to `iff`s.
#### Estimated changes
Modified src/topology/bornology/basic.lean
- \+/\- *lemma* bornology.is_bounded.subset
- \+/\- *lemma* bornology.is_bounded.union
- \+/\- *def* bornology.is_bounded
- \+/\- *lemma* bornology.is_bounded_Union
- \+/\- *lemma* bornology.is_bounded_bUnion
- \+ *lemma* bornology.is_bounded_bUnion_finset
- \+/\- *lemma* bornology.is_bounded_sUnion
- \+/\- *lemma* bornology.is_bounded_singleton
- \+ *lemma* bornology.is_bounded_union
- \+ *lemma* bornology.is_cobounded.inter
- \+ *lemma* bornology.is_cobounded.superset
- \+ *lemma* bornology.is_cobounded_Inter
- \+ *lemma* bornology.is_cobounded_bInter
- \+ *lemma* bornology.is_cobounded_bInter_finset
- \+ *lemma* bornology.is_cobounded_inter
- \+ *lemma* bornology.is_cobounded_sInter
- \+ *lemma* bornology.is_cobounded_univ
- \+/\- *lemma* bornology.sUnion_bounded_univ



## [2022-04-12 08:46:23](https://github.com/leanprover-community/mathlib/commit/d065fd4)
feat(ring_theory/ideal): generalize `x mod I ∈ J mod I ↔ x ∈ J` ([#13358](https://github.com/leanprover-community/mathlib/pull/13358))
We already had a lemma like this assuming `I ≤ J`, and we can drop the assumption if we instead change the RHS to `x ∈ J \sup I`.
This also golfs the proof of the original `mem_quotient_iff_mem`.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* ideal.mem_quotient_iff_mem
- \+ *lemma* ideal.mem_quotient_iff_mem_sup



## [2022-04-12 08:46:22](https://github.com/leanprover-community/mathlib/commit/c883519)
feat(ring_theory/unique_factorization_domain): `factors x = normalized_factors x` ([#13356](https://github.com/leanprover-community/mathlib/pull/13356))
If the group of units is trivial, an arbitrary choice of factors is exactly the unique set of normalized factors.
I made this a `simp` lemma in this direction because `normalized_factors` has a stronger specification than `factors`. I believe currently we actually know less about `normalized_factors` than `factors`, so if it proves too inconvenient I can also remove the `@[simp]`.
#### Estimated changes
Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* unique_factorization_monoid.factors_eq_normalized_factors



## [2022-04-12 08:46:20](https://github.com/leanprover-community/mathlib/commit/85588f8)
feat(data/multiset): lemmas on intersecting a multiset with `repeat x n` ([#13355](https://github.com/leanprover-community/mathlib/pull/13355))
Intersecting a multiset `s` with `repeat x n` gives `repeat x (min n (s.count x))`.
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.inter_repeat
- \+ *lemma* multiset.repeat_inter



## [2022-04-12 08:46:19](https://github.com/leanprover-community/mathlib/commit/f7fe7dd)
refactor(ring_theory/free_comm_ring): don't use is_ring_hom ([#13352](https://github.com/leanprover-community/mathlib/pull/13352))
#### Estimated changes
Modified src/ring_theory/free_comm_ring.lean
- \- *def* free_ring.of'



## [2022-04-12 08:46:19](https://github.com/leanprover-community/mathlib/commit/fd53ce0)
feat(order/filter/at_top_bot): add more `disjoint` lemmas ([#13351](https://github.com/leanprover-community/mathlib/pull/13351))
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.Iic_mem_at_bot
- \+ *lemma* filter.disjoint_at_bot_at_top
- \+ *lemma* filter.disjoint_at_bot_principal_Ici
- \+ *lemma* filter.disjoint_at_bot_principal_Ioi
- \+ *lemma* filter.disjoint_at_top_at_bot
- \+ *lemma* filter.disjoint_at_top_principal_Iic
- \+ *lemma* filter.disjoint_at_top_principal_Iio



## [2022-04-12 08:46:18](https://github.com/leanprover-community/mathlib/commit/708e2de)
chore(group_theory/free_abelian_group): remove is_add_monoid_hom ([#13349](https://github.com/leanprover-community/mathlib/pull/13349))
#### Estimated changes
Modified src/group_theory/free_abelian_group.lean
- \- *lemma* free_abelian_group.is_add_group_hom_lift'
- \- *lemma* free_abelian_group.is_add_group_hom_seq
- \+ *def* free_abelian_group.seq_add_group_hom



## [2022-04-12 08:46:17](https://github.com/leanprover-community/mathlib/commit/333e4be)
feat(algebra/group/basic|topology/connected): add two lemmas ([#13345](https://github.com/leanprover-community/mathlib/pull/13345))
* from the sphere eversion project
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* mul_div_left_comm

Modified src/topology/connected.lean
- \+ *lemma* is_connected_univ



## [2022-04-12 08:46:16](https://github.com/leanprover-community/mathlib/commit/56d6399)
chore(set_theory/cardinal): Golf `mk_le_mk_mul_of_mk_preimage_le` ([#13329](https://github.com/leanprover-community/mathlib/pull/13329))
#### Estimated changes
Modified src/set_theory/cardinal.lean




## [2022-04-12 08:46:15](https://github.com/leanprover-community/mathlib/commit/670735f)
feat(model_theory/order): The theory of dense linear orders without endpoints ([#13253](https://github.com/leanprover-community/mathlib/pull/13253))
Defines the theory of dense linear orders without endpoints
#### Estimated changes
Modified src/model_theory/order.lean
- \- *def* first_order.language.is_ordered_structure
- \+ *lemma* first_order.language.is_ordered_structure_iff
- \+ *lemma* first_order.language.order_Lhom_le_symb
- \+ *lemma* first_order.language.realize_densely_ordered
- \+ *theorem* first_order.language.realize_densely_ordered_iff
- \+ *lemma* first_order.language.realize_no_bot_order
- \+ *theorem* first_order.language.realize_no_bot_order_iff
- \+ *lemma* first_order.language.realize_no_top_order
- \+ *theorem* first_order.language.realize_no_top_order_iff
- \+ *lemma* first_order.language.rel_map_le_symb
- \+ *def* first_order.language.term.lt
- \+ *lemma* first_order.language.term.realize_le
- \+ *lemma* first_order.language.term.realize_lt



## [2022-04-12 08:46:14](https://github.com/leanprover-community/mathlib/commit/34853a9)
feat(topology/algebra/algebra): define the topological subalgebra generated by an element ([#13093](https://github.com/leanprover-community/mathlib/pull/13093))
This defines the topological subalgebra generated by a single element `x : A` of an algebra `A` as the topological closure of `algebra.adjoin R {x}`, and show it is commutative.
I called it `algebra.elemental_algebra`; if someone knows if this actually has a name in the literature, or just has a better idea for the name, let me know!
#### Estimated changes
Modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* algebra.self_mem_adjoin_singleton

Modified src/topology/algebra/algebra.lean
- \+ *def* algebra.elemental_algebra
- \+ *lemma* algebra.self_mem_elemental_algebra
- \+/\- *def* subalgebra.comm_ring_topological_closure



## [2022-04-12 08:46:12](https://github.com/leanprover-community/mathlib/commit/ed919b6)
feat(algebra/algebraic_card): Cardinality of algebraic numbers ([#12869](https://github.com/leanprover-community/mathlib/pull/12869))
We prove the following result: the cardinality of algebraic numbers under an R-algebra is at most `# polynomial R * ω`.
#### Estimated changes
Added src/algebra/algebraic_card.lean
- \+ *theorem* algebraic.cardinal_mk_le_max
- \+ *theorem* algebraic.cardinal_mk_le_mul
- \+ *theorem* algebraic.cardinal_mk_le_of_infinite
- \+ *theorem* algebraic.cardinal_mk_lift_le_max
- \+ *theorem* algebraic.cardinal_mk_lift_le_mul
- \+ *theorem* algebraic.cardinal_mk_lift_le_of_infinite
- \+ *theorem* algebraic.cardinal_mk_of_encodable_of_char_zero
- \+ *theorem* algebraic.countable_of_encodable
- \+ *theorem* algebraic.omega_le_cardinal_mk_of_char_zero



## [2022-04-12 08:46:11](https://github.com/leanprover-community/mathlib/commit/6bc2bd6)
feat(algebraic_geometry/projective_spectrum): Proj as a locally ringed space ([#12773](https://github.com/leanprover-community/mathlib/pull/12773))
This pr is about proving that Proj with its structure sheaf is a locally ringed space
#### Estimated changes
Modified src/algebraic_geometry/projective_spectrum/structure_sheaf.lean
- \+ *def* algebraic_geometry.Proj.stalk_iso'
- \+ *def* algebraic_geometry.Proj.to_LocallyRingedSpace
- \+ *def* algebraic_geometry.Proj.to_SheafedSpace
- \+ *lemma* algebraic_geometry.germ_comp_stalk_to_fiber_ring_hom
- \+ *lemma* algebraic_geometry.homogeneous_localization.mem_basic_open
- \+ *def* algebraic_geometry.homogeneous_localization_to_stalk
- \+ *def* algebraic_geometry.open_to_localization
- \+ *lemma* algebraic_geometry.res_apply
- \+ *def* algebraic_geometry.section_in_basic_open
- \+ *def* algebraic_geometry.stalk_to_fiber_ring_hom
- \+ *lemma* algebraic_geometry.stalk_to_fiber_ring_hom_germ'
- \+ *lemma* algebraic_geometry.stalk_to_fiber_ring_hom_germ



## [2022-04-12 08:46:10](https://github.com/leanprover-community/mathlib/commit/72e1a9e)
feat(ring_theory/valuation/valuation_ring): Valuation rings and their associated valuation. ([#12719](https://github.com/leanprover-community/mathlib/pull/12719))
This PR defines a class `valuation_ring`, stating that an integral domain is a valuation ring.
We also show that valuation rings induce valuations on their fraction fields, that valuation rings are local, and that their lattice of ideals is totally ordered.
#### Estimated changes
Added src/ring_theory/valuation/valuation_ring.lean
- \+ *lemma* valuation_ring.coe_equiv_integer_apply
- \+ *lemma* valuation_ring.mem_integer_iff
- \+ *lemma* valuation_ring.of_integers
- \+ *lemma* valuation_ring.range_algebra_map_eq
- \+ *def* valuation_ring.valuation
- \+ *def* valuation_ring.value_group

Modified src/ring_theory/witt_vector/discrete_valuation_ring.lean
- \+ *lemma* witt_vector.discrete_valuation_ring



## [2022-04-12 07:55:03](https://github.com/leanprover-community/mathlib/commit/b889567)
feat(data/complex/basic): add a few lemmas ([#13354](https://github.com/leanprover-community/mathlib/pull/13354))
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *lemma* complex.I_mul_im
- \+ *lemma* complex.I_mul_re
- \+ *lemma* complex.abs_im_lt_abs
- \+ *lemma* complex.abs_re_lt_abs
- \+ *lemma* complex.mul_I_im
- \+ *lemma* complex.mul_I_re



## [2022-04-12 05:57:50](https://github.com/leanprover-community/mathlib/commit/0783742)
chore(*): more assumptions to lemmas that are removable ([#13364](https://github.com/leanprover-community/mathlib/pull/13364))
This time I look at assumptions that are actually provable by simp from the earlier assumptions (fortunately there are only a couple of these), and one more from the review of [#13316](https://github.com/leanprover-community/mathlib/pull/13316) that was slightly too nontrivial to be found automatically.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* nnreal.rpow_lt_one

Modified src/data/nat/log.lean
- \+/\- *lemma* nat.lt_pow_succ_log_self

Modified src/ring_theory/adjoin/basic.lean




## [2022-04-12 05:57:49](https://github.com/leanprover-community/mathlib/commit/56f6c8e)
chore(algebra/big_operators/intervals): Move and golf sum_range_sub_sum_range ([#13359](https://github.com/leanprover-community/mathlib/pull/13359))
Move sum_range_sub_sum_range to a better file. Also implemented the golf demonstrated in this paper https://arxiv.org/pdf/2202.01344.pdf from @spolu.
#### Estimated changes
Modified src/algebra/big_operators/intervals.lean
- \+ *lemma* finset.prod_Ico_eq_div
- \+ *lemma* finset.prod_range_sub_prod_range
- \- *lemma* finset.sum_Ico_eq_sub

Modified src/data/complex/exponential.lean
- \- *lemma* sum_range_sub_sum_range



## [2022-04-12 05:57:48](https://github.com/leanprover-community/mathlib/commit/603db27)
feat(topology/metric_space/basic): some lemmas about dist ([#13343](https://github.com/leanprover-community/mathlib/pull/13343))
from the sphere eversion project
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *theorem* dist_self_add_left
- \+ *theorem* dist_self_add_right

Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* ball_prod_same
- \+/\- *theorem* closed_ball_prod_same
- \+ *lemma* dist_prod_same_left
- \+ *lemma* dist_prod_same_right
- \+/\- *lemma* prod.dist_eq



## [2022-04-12 05:24:39](https://github.com/leanprover-community/mathlib/commit/cbea7e1)
feat(algebra/order/monoid_lemmas_zero_lt): add some lemmas assuming `mul_one_class` `preorder` ([#13299](https://github.com/leanprover-community/mathlib/pull/13299))
#### Estimated changes
Modified src/algebra/order/monoid_lemmas_zero_lt.lean
- \+ *lemma* zero_lt.le_of_le_mul_of_le_one_left
- \+ *lemma* zero_lt.le_of_le_mul_of_le_one_right
- \+ *lemma* zero_lt.le_of_mul_le_of_one_le_left
- \+ *lemma* zero_lt.le_of_mul_le_of_one_le_right
- \+ *lemma* zero_lt.lt_of_lt_mul_of_le_one_left
- \+ *lemma* zero_lt.lt_of_lt_mul_of_le_one_right
- \+ *lemma* zero_lt.lt_of_mul_lt_of_one_le_left
- \+ *lemma* zero_lt.lt_of_mul_lt_of_one_le_right



## [2022-04-12 05:24:38](https://github.com/leanprover-community/mathlib/commit/e3db2e7)
feat(group_theory/complement): Criterion for complementary subgroups ([#13292](https://github.com/leanprover-community/mathlib/pull/13292))
This lemma gives a criterion for a stabilizer subgroup to be a complementary subgroup.
#### Estimated changes
Modified src/group_theory/complement.lean
- \+ *lemma* subgroup.is_complement'_stabilizer



## [2022-04-12 03:21:18](https://github.com/leanprover-community/mathlib/commit/fdd68d9)
fix(category_theory/elements): speed up `groupoid_of_elements` ([#13372](https://github.com/leanprover-community/mathlib/pull/13372))
from 14.5s to 6s
It's [reported](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Quadratic.20Hilbert.20symbol.20over.20.E2.84.9A/near/278592167) that this is causing timeouts in recent bors batches.
#### Estimated changes
Modified src/category_theory/elements.lean




## [2022-04-12 03:21:17](https://github.com/leanprover-community/mathlib/commit/bf1b813)
chore(algebra/module/basic): generalize to add_monoid_hom_class ([#13346](https://github.com/leanprover-community/mathlib/pull/13346))
I need some of these lemmas for `ring_hom`.
Additionally, this:
* removes `map_nat_module_smul` (duplicate of `map_nsmul`) and `map_int_module_smul` (duplicate of `map_zsmul`)
* renames `map_rat_module_smul` to `map_rat_smul` for brevity.
* adds the lemmas `inv_nat_cast_smul_comm` and `inv_int_cast_smul_comm`.
* Swaps the order of the arguments to `map_zsmul` and `map_nsmul` to align with the usual rules (`to_additive` emitted them in the wrong order)
#### Estimated changes
Modified src/algebra/category/Group/Z_Module_equivalence.lean


Modified src/algebra/hom/group.lean
- \+ *theorem* map_nsmul
- \+/\- *theorem* map_pow
- \+ *theorem* map_zsmul

Modified src/algebra/module/basic.lean
- \- *lemma* add_monoid_hom.map_int_cast_smul
- \- *lemma* add_monoid_hom.map_int_module_smul
- \- *lemma* add_monoid_hom.map_inv_int_cast_smul
- \- *lemma* add_monoid_hom.map_inv_nat_cast_smul
- \- *lemma* add_monoid_hom.map_nat_cast_smul
- \- *lemma* add_monoid_hom.map_nat_module_smul
- \- *lemma* add_monoid_hom.map_rat_cast_smul
- \- *lemma* add_monoid_hom.map_rat_module_smul
- \+ *lemma* inv_int_cast_smul_comm
- \+ *lemma* inv_nat_cast_smul_comm
- \+ *lemma* map_int_cast_smul
- \+ *lemma* map_inv_int_cast_smul
- \+ *lemma* map_inv_nat_cast_smul
- \+ *lemma* map_nat_cast_smul
- \+ *lemma* map_rat_cast_smul
- \+ *lemma* map_rat_smul

Modified src/algebra/module/linear_map.lean


Modified src/category_theory/preadditive/default.lean


Modified src/group_theory/free_abelian_group.lean


Modified src/topology/instances/real_vector_space.lean




## [2022-04-12 03:21:16](https://github.com/leanprover-community/mathlib/commit/955cb8e)
feat(data/list/basic): add a theorem about last and append ([#13336](https://github.com/leanprover-community/mathlib/pull/13336))
When `ys` is not empty, we can conclude that `last (xs ++ ys)` is `last ys`.
#### Estimated changes
Modified src/data/list/basic.lean
- \+/\- *theorem* list.last_append
- \+ *theorem* list.last_append_singleton

Modified src/data/list/cycle.lean




## [2022-04-12 03:21:15](https://github.com/leanprover-community/mathlib/commit/10a3faa)
feat(algebra/order/monoid_lemmas_zero_lt): add lemmas assuming `mul_zero_class` `preorder` ([#13297](https://github.com/leanprover-community/mathlib/pull/13297))
#### Estimated changes
Modified src/algebra/order/monoid_lemmas_zero_lt.lean
- \+ *lemma* zero_lt.left.mul_pos
- \+ *lemma* zero_lt.mul_neg_of_neg_of_pos
- \+ *lemma* zero_lt.mul_neg_of_pos_of_neg
- \+ *lemma* zero_lt.right.mul_pos



## [2022-04-12 03:21:14](https://github.com/leanprover-community/mathlib/commit/fe1c78a)
feat(data/polynomial/algebra_map): remove some lemmas about `aeval`, add `protected` on `polynomial.map_list_prod` ([#13294](https://github.com/leanprover-community/mathlib/pull/13294))
Remove `aeval_sum` which is a duplicate of `map_sum`.
Remove `aeval_prod` which is a duplicate of `map_prod`.
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \- *lemma* polynomial.aeval_prod
- \- *lemma* polynomial.aeval_sum

Modified src/data/polynomial/eval.lean
- \- *lemma* polynomial.map_list_prod



## [2022-04-12 03:21:13](https://github.com/leanprover-community/mathlib/commit/483b7df)
feat(analysis/convex/strict_convex_space): Ray characterization of `∥x - y∥` ([#13293](https://github.com/leanprover-community/mathlib/pull/13293))
`∥x - y∥ = |∥x∥ - ∥y∥|` if and only if `x` and `y` are on the same ray.
#### Estimated changes
Modified src/analysis/complex/arg.lean
- \+/\- *lemma* complex.abs_add_eq
- \+/\- *lemma* complex.abs_add_eq_iff
- \+/\- *lemma* complex.abs_sub_eq
- \+ *lemma* complex.abs_sub_eq_iff
- \+/\- *lemma* complex.same_ray_iff
- \+/\- *lemma* complex.same_ray_of_arg_eq

Modified src/analysis/convex/strict_convex_space.lean
- \+ *lemma* abs_lt_norm_sub_of_not_same_ray
- \+ *lemma* lt_norm_sub_of_not_same_ray
- \+ *lemma* not_same_ray_iff_abs_lt_norm_sub
- \+ *lemma* same_ray_iff_norm_sub



## [2022-04-12 03:21:12](https://github.com/leanprover-community/mathlib/commit/f1c98ba)
feat(topology/uniform_space/uniform_convergence_topology): define the uniform structure of uniform convergence ([#13073](https://github.com/leanprover-community/mathlib/pull/13073))
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+ *lemma* inf_uniformity'
- \+ *lemma* infi_uniformity'
- \+ *lemma* le_iff_uniform_continuous_id

Added src/topology/uniform_space/uniform_convergence_topology.lean
- \+ *lemma* uniform_convergence.t2_space
- \+ *lemma* uniform_convergence.uniform_continuous_eval
- \+ *lemma* uniform_convergence_on.t2_space_of_covering
- \+ *lemma* uniform_convergence_on.uniform_continuous_eval_of_mem



## [2022-04-12 01:13:15](https://github.com/leanprover-community/mathlib/commit/7ba9c3f)
feat(order/basic): More order instances for `subtype` ([#13134](https://github.com/leanprover-community/mathlib/pull/13134))
Add the `has_le`, `has_lt`, `decidable_le`, `decidable_lt`, `bounded_order` instances.
Incorporating the `decidable_le` and `decidable_lt` instances into the `linear_order` one breaks some defeqs with `ite`/`dite`.
#### Estimated changes
Modified src/algebraic_topology/simplex_category.lean


Modified src/data/pnat/basic.lean


Modified src/order/basic.lean
- \+/\- *lemma* subtype.coe_le_coe
- \+/\- *lemma* subtype.coe_lt_coe
- \+/\- *lemma* subtype.mk_le_mk
- \+/\- *lemma* subtype.mk_lt_mk

Modified src/order/bounded_order.lean
- \+ *lemma* subtype.coe_bot
- \+ *lemma* subtype.coe_top
- \+ *lemma* subtype.mk_bot
- \+ *lemma* subtype.mk_top



## [2022-04-11 23:09:24](https://github.com/leanprover-community/mathlib/commit/0453d60)
feat(algebraic_geometry/projective_spectrum): structure sheaf of Proj of graded ring ([#13072](https://github.com/leanprover-community/mathlib/pull/13072))
Construct the structure sheaf of Proj of a graded algebra.
#### Estimated changes
Added src/algebraic_geometry/projective_spectrum/structure_sheaf.lean
- \+ *def* algebraic_geometry.projective_spectrum.Proj.structure_sheaf
- \+ *def* algebraic_geometry.projective_spectrum.structure_sheaf.is_fraction
- \+ *def* algebraic_geometry.projective_spectrum.structure_sheaf.is_fraction_prelocal
- \+ *def* algebraic_geometry.projective_spectrum.structure_sheaf.is_locally_fraction
- \+ *lemma* algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.add_mem'
- \+ *lemma* algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.mul_mem'
- \+ *lemma* algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.neg_mem'
- \+ *lemma* algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.one_mem'
- \+ *lemma* algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.zero_mem'
- \+ *def* algebraic_geometry.projective_spectrum.structure_sheaf.sections_subring
- \+ *def* algebraic_geometry.projective_spectrum.structure_sheaf.structure_presheaf_comp_forget
- \+ *def* algebraic_geometry.projective_spectrum.structure_sheaf.structure_presheaf_in_CommRing
- \+ *def* algebraic_geometry.projective_spectrum.structure_sheaf.structure_sheaf_in_Type

Modified src/algebraic_geometry/projective_spectrum/topology.lean
- \+ *def* projective_spectrum.Top



## [2022-04-11 23:09:23](https://github.com/leanprover-community/mathlib/commit/f94cd0f)
feat(analysis/normed/normed_field): Pi types form a normed ring ([#12912](https://github.com/leanprover-community/mathlib/pull/12912))
#### Estimated changes
Modified src/analysis/normed/normed_field.lean


Modified src/data/finset/lattice.lean
- \+ *lemma* finset.inf'_mul_le_mul_inf'_of_nonneg
- \+ *lemma* finset.mul_inf_le_inf_mul_of_nonneg
- \+ *lemma* finset.sup'_mul_le_mul_sup'_of_nonneg
- \+ *lemma* finset.sup_mul_le_mul_sup_of_nonneg



## [2022-04-11 20:58:27](https://github.com/leanprover-community/mathlib/commit/887f933)
feat(data/fin/tuple/nat_antidiagonal): add an equiv and some TODO comments. ([#13338](https://github.com/leanprover-community/mathlib/pull/13338))
This follows on from [#13031](https://github.com/leanprover-community/mathlib/pull/13031), and:
* Adds the tuple version of an antidiagonal equiv
* Makes some arguments implicit
* Adds some comments to tie together `finset.nat.antidiagonal_tuple` with the `cut` definition used in one of the 100 Freek problems.
#### Estimated changes
Modified archive/100-theorems-list/45_partition.lean
- \+ *lemma* cut_univ_fin_eq_antidiagonal_tuple

Modified src/data/fin/tuple/nat_antidiagonal.lean
- \+/\- *lemma* finset.nat.mem_antidiagonal_tuple
- \+ *def* finset.nat.sigma_antidiagonal_tuple_equiv_tuple
- \+/\- *lemma* list.nat.mem_antidiagonal_tuple
- \+/\- *lemma* multiset.nat.mem_antidiagonal_tuple



## [2022-04-11 20:58:26](https://github.com/leanprover-community/mathlib/commit/455bc65)
chore(representation_theory/invariants): clean up some simps ([#13337](https://github.com/leanprover-community/mathlib/pull/13337))
#### Estimated changes
Modified src/representation_theory/invariants.lean
- \+/\- *theorem* representation.smul_average_id



## [2022-04-11 20:58:25](https://github.com/leanprover-community/mathlib/commit/e8339bd)
feat(category_theory/fully_faithful): nat_trans_of_comp_fully_faithful ([#13327](https://github.com/leanprover-community/mathlib/pull/13327))
I added `nat_iso_of_comp_fully_faithful` in an earlier PR, but left out the more basic construction.
#### Estimated changes
Modified src/category_theory/functor/fully_faithful.lean
- \+/\- *def* category_theory.nat_iso_of_comp_fully_faithful
- \+ *lemma* category_theory.nat_iso_of_comp_fully_faithful_hom
- \+ *lemma* category_theory.nat_iso_of_comp_fully_faithful_inv
- \+ *def* category_theory.nat_trans_of_comp_fully_faithful



## [2022-04-11 20:58:24](https://github.com/leanprover-community/mathlib/commit/4a07054)
chore(*): remove numerous edge cases from lemmas ([#13316](https://github.com/leanprover-community/mathlib/pull/13316))
This PR uses the same methodology as [#10774](https://github.com/leanprover-community/mathlib/pull/10774) to use a linter to remove edge case assumptions from lemmas when the result is easy to prove without the assumption.
These are assumptions things like: n \ne 0, 0 < n, p \ne \top, nontrivial R, nonempty R.
Removing these unneeded assumptions makes such lemmas easier to apply, and lets us golf a few other proofs along the way.
The file with the most changes is `src/ring_theory/unique_factorization_domain.lean` where the linter inspired me to allow trivial monoids in many places.
The code I used to find these is in the branch [https://github.com/leanprover-community/mathlib/tree/alexjbest/simple_edge_cases_linter](https://github.com/leanprover-community/mathlib/tree/alexjbest/simple_edge_cases_linter?rgh-link-date=2021-12-13T23%3A53%3A31Z)
#### Estimated changes
Modified src/algebra/big_operators/intervals.lean
- \+/\- *lemma* finset.sum_range_by_parts

Modified src/algebra/order/ring.lean


Modified src/algebra/order/with_zero.lean
- \+/\- *lemma* mul_inv_le_of_le_mul

Modified src/algebra/polynomial/big_operators.lean
- \+/\- *lemma* polynomial.multiset_prod_X_sub_C_coeff_card_pred
- \+/\- *lemma* polynomial.prod_X_sub_C_coeff_card_pred

Modified src/analysis/specific_limits/normed.lean


Modified src/data/nat/factorization.lean
- \+/\- *lemma* nat.dvd_iff_prime_pow_dvd_dvd

Modified src/data/polynomial/degree/definitions.lean


Modified src/data/polynomial/mirror.lean


Modified src/data/rat/basic.lean
- \+/\- *lemma* rat.exists_eq_mul_div_num_and_eq_mul_div_denom
- \+/\- *lemma* rat.num_denom_mk

Modified src/data/rat/floor.lean


Modified src/data/zmod/basic.lean
- \+/\- *lemma* zmod.neg_eq_self_mod_two

Modified src/field_theory/minpoly.lean
- \+/\- *lemma* minpoly.eq_X_sub_C_of_algebra_map_inj

Modified src/field_theory/ratfunc.lean
- \+/\- *lemma* ratfunc.int_degree_add_le
- \+/\- *lemma* ratfunc.num_div
- \+ *lemma* ratfunc.num_div_dvd'
- \+/\- *lemma* ratfunc.num_div_dvd

Modified src/linear_algebra/matrix/charpoly/coeff.lean
- \+/\- *lemma* finite_field.trace_pow_card
- \+/\- *lemma* zmod.trace_pow_card

Modified src/measure_theory/constructions/pi.lean
- \+/\- *lemma* measure_theory.pi_premeasure_pi'
- \+/\- *lemma* measure_theory.pi_premeasure_pi_eval

Modified src/measure_theory/function/uniform_integrable.lean


Modified src/measure_theory/integral/circle_integral.lean


Modified src/number_theory/cyclotomic/basic.lean


Modified src/number_theory/function_field.lean


Modified src/number_theory/padics/padic_norm.lean


Modified src/ring_theory/chain_of_divisors.lean


Modified src/ring_theory/dedekind_domain/ideal.lean
- \+/\- *lemma* irreducible_pow_sup_of_le

Modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *theorem* associates.coprime_iff_inf_one
- \+/\- *lemma* associates.count_le_count_of_factors_le
- \+/\- *lemma* associates.count_le_count_of_le
- \+/\- *theorem* associates.count_mul
- \+/\- *theorem* associates.count_mul_of_coprime'
- \+/\- *theorem* associates.count_mul_of_coprime
- \+/\- *theorem* associates.count_of_coprime
- \+/\- *theorem* associates.dvd_count_of_dvd_count_mul
- \+/\- *theorem* associates.factors_le
- \+/\- *theorem* associates.factors_mono
- \+/\- *theorem* associates.factors_mul
- \+/\- *theorem* associates.le_of_count_ne_zero
- \+/\- *lemma* associates.sup_mul_inf



## [2022-04-11 20:58:23](https://github.com/leanprover-community/mathlib/commit/a839f4d)
feat(number_theory/quadratic_reciprocity): change order of arguments … ([#13311](https://github.com/leanprover-community/mathlib/pull/13311))
…in legendre_sym
This is the first step in a major overhaul of the contents of number_theory/quadratic_reciprocity.
As a first step, the order of the arguments `a` and `p` to `legendre_sym` is swapped, based on a [poll](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Quadratic.20Hilbert.20symbol.20over.20.E2.84.9A) on Zulip.
#### Estimated changes
Modified src/number_theory/quadratic_reciprocity.lean
- \+/\- *def* zmod.legendre_sym
- \+/\- *lemma* zmod.legendre_sym_eq_one_or_neg_one
- \+/\- *lemma* zmod.legendre_sym_eq_pow
- \+/\- *lemma* zmod.legendre_sym_eq_zero_iff
- \+/\- *lemma* zmod.legendre_sym_two



## [2022-04-11 20:58:22](https://github.com/leanprover-community/mathlib/commit/4e1102a)
feat(probability/integration): characterize indep_fun by expected product of comp ([#13270](https://github.com/leanprover-community/mathlib/pull/13270))
This is the third PR into probability/integration, to characterize independence by the expected product of compositions.
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+ *lemma* set.inter_indicator_one

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_theory.integral_indicator_one

Modified src/probability/integration.lean
- \+ *theorem* probability_theory.indep_fun_iff_integral_comp_mul



## [2022-04-11 18:49:41](https://github.com/leanprover-community/mathlib/commit/a521a32)
feat(data/set/basic): Missing `set.image_perm` ([#13242](https://github.com/leanprover-community/mathlib/pull/13242))
#### Estimated changes
Modified src/data/finset/basic.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.image_perm



## [2022-04-11 18:49:39](https://github.com/leanprover-community/mathlib/commit/dee4958)
feat(computability/*): Automata lemmas ([#13194](https://github.com/leanprover-community/mathlib/pull/13194))
A bunch of missing API for `language`, `regular_expression`, `DFA`, `NFA`, `ε_NFA`.
#### Estimated changes
Modified src/computability/DFA.lean
- \+/\- *def* DFA.eval
- \+ *lemma* DFA.eval_append_singleton
- \+ *lemma* DFA.eval_from_append_singleton
- \+ *lemma* DFA.eval_from_nil
- \+ *lemma* DFA.eval_from_singleton
- \+ *lemma* DFA.eval_nil
- \+ *lemma* DFA.eval_singleton

Modified src/computability/NFA.lean
- \+/\- *def* NFA.eval
- \+ *lemma* NFA.eval_append_singleton
- \+ *lemma* NFA.eval_from_append_singleton
- \+ *lemma* NFA.eval_from_nil
- \+ *lemma* NFA.eval_from_singleton
- \+ *lemma* NFA.eval_nil
- \+ *lemma* NFA.eval_singleton
- \+/\- *lemma* NFA.mem_step_set
- \+/\- *def* NFA.step_set
- \+ *lemma* NFA.step_set_empty

Modified src/computability/epsilon_NFA.lean
- \+ *lemma* ε_NFA.accept_one
- \+ *lemma* ε_NFA.accept_zero
- \+/\- *def* ε_NFA.accepts
- \+ *lemma* ε_NFA.eval_append_singleton
- \+ *lemma* ε_NFA.eval_from_append_singleton
- \+ *lemma* ε_NFA.eval_from_empty
- \+ *lemma* ε_NFA.eval_from_nil
- \+ *lemma* ε_NFA.eval_from_singleton
- \+ *lemma* ε_NFA.eval_nil
- \+ *lemma* ε_NFA.eval_singleton
- \+ *lemma* ε_NFA.mem_step_set_iff
- \+ *lemma* ε_NFA.start_one
- \+ *lemma* ε_NFA.start_zero
- \+ *lemma* ε_NFA.step_one
- \+/\- *def* ε_NFA.step_set
- \+ *lemma* ε_NFA.step_set_empty
- \+ *lemma* ε_NFA.step_zero
- \+ *lemma* ε_NFA.subset_ε_closure
- \+ *lemma* ε_NFA.ε_closure_empty
- \+ *lemma* ε_NFA.ε_closure_univ

Modified src/computability/language.lean
- \+ *lemma* language.append_mem_mul
- \+ *lemma* language.join_mem_star
- \+/\- *lemma* language.mem_add
- \+/\- *lemma* language.mem_mul
- \+/\- *lemma* language.mem_one
- \+/\- *lemma* language.mem_star
- \+/\- *lemma* language.nil_mem_one
- \+ *lemma* language.nil_mem_star

Modified src/computability/regular_expressions.lean
- \+ *lemma* regular_expression.deriv_add
- \+ *lemma* regular_expression.deriv_char_of_ne
- \+ *lemma* regular_expression.deriv_char_self
- \+ *lemma* regular_expression.deriv_one
- \+ *lemma* regular_expression.deriv_star
- \+ *lemma* regular_expression.deriv_zero
- \+ *lemma* regular_expression.matches_add
- \- *lemma* regular_expression.matches_add_def
- \+ *lemma* regular_expression.matches_char
- \+ *lemma* regular_expression.matches_epsilon
- \- *lemma* regular_expression.matches_epsilon_def
- \+ *lemma* regular_expression.matches_mul
- \- *lemma* regular_expression.matches_mul_def
- \+ *lemma* regular_expression.matches_star
- \- *lemma* regular_expression.matches_star_def
- \+ *lemma* regular_expression.matches_zero
- \- *lemma* regular_expression.matches_zero_def

Modified src/data/set/basic.lean
- \+ *lemma* set.eq_empty_of_forall_not_mem



## [2022-04-11 18:49:38](https://github.com/leanprover-community/mathlib/commit/77ae091)
feat(number_theory/cyclotomic/primitive_roots): add `pow_sub_one_norm_prime_pow_ne_two` ([#13152](https://github.com/leanprover-community/mathlib/pull/13152))
We add `pow_sub_one_norm_prime_pow_ne_two`, that computes the norm of `ζ ^ (p ^ s) - 1`, where `ζ` is a primitive `p ^ (k + 1)`-th root of unity. This will be used to compute the discriminant of the `p ^ n`-th cyclotomic field.
From flt-regular
#### Estimated changes
Modified src/number_theory/cyclotomic/primitive_roots.lean
- \+/\- *lemma* is_cyclotomic_extension.prime_ne_two_norm_zeta_sub_one
- \+ *lemma* is_cyclotomic_extension.prime_ne_two_pow_norm_zeta_pow_sub_one
- \+/\- *lemma* is_cyclotomic_extension.prime_ne_two_pow_norm_zeta_sub_one
- \+ *lemma* is_primitive_root.pow_sub_one_norm_prime_ne_two
- \+ *lemma* is_primitive_root.pow_sub_one_norm_prime_pow_ne_two
- \+ *lemma* is_primitive_root.pow_sub_one_norm_two
- \- *lemma* is_primitive_root.sub_one_norm_pow_two
- \+/\- *lemma* is_primitive_root.sub_one_norm_prime
- \+/\- *lemma* is_primitive_root.sub_one_norm_prime_ne_two
- \+ *lemma* is_primitive_root.sub_one_norm_two

Modified src/ring_theory/roots_of_unity.lean
- \- *lemma* is_primitive_root.coe_subgroup_iff
- \+ *lemma* is_primitive_root.coe_submonoid_class_iff



## [2022-04-11 18:49:37](https://github.com/leanprover-community/mathlib/commit/04250c8)
feat(measure_theory/measure/haar): Add the Steinhaus Theorem ([#12932](https://github.com/leanprover-community/mathlib/pull/12932))
This PR proves the [Steinhaus Theorem](https://en.wikipedia.org/wiki/Steinhaus_theorem) in any locally compact group with a Haar measure.
#### Estimated changes
Modified src/measure_theory/measure/haar.lean
- \+ *theorem* measure_theory.measure.div_mem_nhds_one_of_haar_pos



## [2022-04-11 18:49:35](https://github.com/leanprover-community/mathlib/commit/cea5e4b)
feat(data/sign): the sign function ([#12835](https://github.com/leanprover-community/mathlib/pull/12835))
#### Estimated changes
Added src/data/sign.lean
- \+ *def* sign
- \+ *lemma* sign_apply
- \+ *lemma* sign_eq_zero_iff
- \+ *def* sign_hom
- \+ *lemma* sign_ne_zero
- \+ *lemma* sign_neg
- \+ *lemma* sign_pos
- \+ *def* sign_type.cast
- \+ *lemma* sign_type.cast_eq_coe
- \+ *def* sign_type.cast_hom
- \+ *lemma* sign_type.coe_neg_one
- \+ *lemma* sign_type.coe_one
- \+ *lemma* sign_type.coe_zero
- \+ *def* sign_type.fin3_equiv
- \+ *def* sign_type.mul
- \+ *lemma* sign_type.neg_eq_neg_one
- \+ *lemma* sign_type.pos_eq_one
- \+ *lemma* sign_type.zero_eq_zero
- \+ *lemma* sign_zero



## [2022-04-11 16:38:59](https://github.com/leanprover-community/mathlib/commit/695a2b6)
feat(combinatorics/simple_graph/connectivity): induced maps on walks and paths ([#13310](https://github.com/leanprover-community/mathlib/pull/13310))
Every graph homomorphism gives an induced map on walks.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *def* simple_graph.hom.map_dart
- \+ *lemma* simple_graph.hom.map_dart_apply

Modified src/combinatorics/simple_graph/connectivity.lean
- \+ *lemma* simple_graph.path.map_embedding_injective
- \+ *lemma* simple_graph.path.map_injective
- \+ *lemma* simple_graph.walk.darts_map
- \+ *lemma* simple_graph.walk.edges_map
- \+ *lemma* simple_graph.walk.length_map
- \+ *lemma* simple_graph.walk.map_append
- \+ *lemma* simple_graph.walk.map_cons
- \+ *lemma* simple_graph.walk.map_injective_of_injective
- \+ *lemma* simple_graph.walk.map_is_path_of_injective
- \+ *lemma* simple_graph.walk.map_nil
- \+ *lemma* simple_graph.walk.reverse_map
- \+ *lemma* simple_graph.walk.support_map



## [2022-04-11 16:38:58](https://github.com/leanprover-community/mathlib/commit/a447dae)
chore(category_theory/*): reduce imports ([#13305](https://github.com/leanprover-community/mathlib/pull/13305))
An unnecessary import of `tactic.monotonicity` earlier in the hierarchy was pulling in quite a lot. A few compensatory imports are needed later.
#### Estimated changes
Modified src/algebra/category/Semigroup/basic.lean


Modified src/category_theory/essential_image.lean


Modified src/category_theory/functor/basic.lean




## [2022-04-11 16:38:57](https://github.com/leanprover-community/mathlib/commit/5e8d6bb)
feat(combinatorics/simple_graph/{connectivity,adj_matrix}): powers of adjacency matrix ([#13304](https://github.com/leanprover-community/mathlib/pull/13304))
The number of walks of length-n between two vertices is given by the corresponding entry of the n-th power of the adjacency matrix.
#### Estimated changes
Modified src/combinatorics/simple_graph/adj_matrix.lean
- \+ *theorem* simple_graph.adj_matrix_pow_apply_eq_card_walk

Modified src/combinatorics/simple_graph/connectivity.lean
- \+ *lemma* simple_graph.card_set_walk_length_eq
- \+ *lemma* simple_graph.coe_finset_walk_length_eq
- \+ *def* simple_graph.finset_walk_length
- \+ *lemma* simple_graph.set_walk_length_succ_eq
- \+ *lemma* simple_graph.set_walk_length_to_finset_eq
- \+ *lemma* simple_graph.set_walk_length_zero_eq_of_ne
- \+ *lemma* simple_graph.set_walk_self_length_zero_eq
- \+ *lemma* simple_graph.walk.length_eq_of_mem_finset_walk_length
- \+ *lemma* simple_graph.walk.length_eq_zero_iff



## [2022-04-11 16:38:56](https://github.com/leanprover-community/mathlib/commit/bfd5384)
chore(category_theory): switch ulift and filtered in import hierarchy ([#13302](https://github.com/leanprover-community/mathlib/pull/13302))
Many files require `ulift` but not `filtered`, so `ulift` should be lower in the import hierarchy. This avoids needing all of `data/` up to `data/fintype/basic` before we can start defining categorical limits.
#### Estimated changes
Modified src/category_theory/category/ulift.lean


Modified src/category_theory/filtered.lean




## [2022-04-11 16:38:55](https://github.com/leanprover-community/mathlib/commit/dcb6c86)
feat(measure_theory/function/uniform_integrable): Equivalent condition for uniformly integrable in the probability sense ([#12955](https://github.com/leanprover-community/mathlib/pull/12955))
A sequence of functions is uniformly integrable in the probability sense if and only if `∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ i, snorm ({x | C ≤ ∥f i x∥₊}.indicator (f i)) p μ ≤ ennreal.of_real ε`.
#### Estimated changes
Modified src/algebra/order/ring.lean
- \+ *lemma* lt_two_mul_self

Modified src/measure_theory/function/lp_space.lean
- \+ *lemma* measure_theory.snorm_indicator_ge_of_bdd_below

Modified src/measure_theory/function/uniform_integrable.lean
- \+ *lemma* measure_theory.uniform_integrable.spec
- \+ *lemma* measure_theory.uniform_integrable_iff

Modified src/order/filter/indicator_function.lean
- \+ *lemma* filter.eventually_eq.indicator
- \+ *lemma* filter.eventually_eq.indicator_zero



## [2022-04-11 16:38:54](https://github.com/leanprover-community/mathlib/commit/797c713)
feat(ring_theory/coprime/lemmas): alternative characterisations of pairwise coprimeness ([#12911](https://github.com/leanprover-community/mathlib/pull/12911))
This provides two condtions equivalent to pairwise coprimeness : 
* each term is coprime to the product of all others
* 1 can be obtained as a linear combination of all products with one term missing.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.pairwise_cons'
- \+ *lemma* finset.pairwise_cons
- \+ *lemma* finset.pairwise_subtype_iff_pairwise_finset'
- \+ *lemma* finset.pairwise_subtype_iff_pairwise_finset

Modified src/ring_theory/coprime/lemmas.lean
- \+ *lemma* exists_sum_eq_one_iff_pairwise_coprime'
- \+ *lemma* exists_sum_eq_one_iff_pairwise_coprime
- \+ *lemma* pairwise_coprime_iff_coprime_prod



## [2022-04-11 14:08:55](https://github.com/leanprover-community/mathlib/commit/67d6097)
feat(data/option/basic): add `option.coe_get` ([#13081](https://github.com/leanprover-community/mathlib/pull/13081))
Adds lemma `coe_get {o : option α} (h : o.is_some) : ((option.get h : α) : option α) = o`
Extracted from @huynhtrankhanh's https://github.com/leanprover-community/mathlib/pull/11162, moved here to a separate PR
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* option.coe_get



## [2022-04-11 11:52:38](https://github.com/leanprover-community/mathlib/commit/4139824)
refactor(category_theory/differential_object): simp only -> simp_rw ([#13333](https://github.com/leanprover-community/mathlib/pull/13333))
This is extremely minor; I replace a `simp only` with a `simp_rw`.
This proof is apparently rather fragile with respect to some other changes I'm trying to make, and I worked out the correct `simp_rw` sequence while debugging. May as well preserve it for posterity, or at least until next time I make it break.
#### Estimated changes
Modified src/category_theory/differential_object.lean




## [2022-04-11 11:52:37](https://github.com/leanprover-community/mathlib/commit/c7e76bc)
chore(category_theory/monoidal/discrete): typo in to_additive name ([#13332](https://github.com/leanprover-community/mathlib/pull/13332))
#### Estimated changes
Modified src/category_theory/monoidal/discrete.lean




## [2022-04-11 11:52:36](https://github.com/leanprover-community/mathlib/commit/d405955)
feat(analysis/complex/re_im_topology): add `metric.bounded.re_prod_im` ([#13324](https://github.com/leanprover-community/mathlib/pull/13324))
Also add `complex.mem_re_prod_im`.
#### Estimated changes
Modified src/analysis/complex/re_im_topology.lean
- \+/\- *lemma* is_closed.re_prod_im
- \+/\- *lemma* is_open.re_prod_im
- \+ *lemma* metric.bounded.re_prod_im

Modified src/data/complex/basic.lean
- \+ *lemma* complex.mem_re_prod_im



## [2022-04-11 11:52:34](https://github.com/leanprover-community/mathlib/commit/ebbe763)
feat(measure_theory/constructions/borel_space): a set with `μ (∂ s) = 0` is null measurable ([#13322](https://github.com/leanprover-community/mathlib/pull/13322))
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* closure_ae_eq_of_null_frontier
- \+ *lemma* interior_ae_eq_of_null_frontier
- \- *lemma* measure_closure_of_null_bdry
- \+ *lemma* measure_closure_of_null_frontier
- \- *lemma* measure_interior_of_null_bdry
- \+ *lemma* measure_interior_of_null_frontier
- \+ *lemma* null_measurable_set_of_null_frontier



## [2022-04-11 11:52:33](https://github.com/leanprover-community/mathlib/commit/7e69148)
feat(order/conditionally_complete_lattice): Make `cSup_empty` a `simp` lemma ([#13318](https://github.com/leanprover-community/mathlib/pull/13318))
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* cSup_empty
- \+/\- *lemma* csupr_of_empty



## [2022-04-11 11:52:32](https://github.com/leanprover-community/mathlib/commit/159855d)
feat(set_theory/ordinal_arithmetic): `is_normal.monotone` ([#13314](https://github.com/leanprover-community/mathlib/pull/13314))
We introduce a convenient abbreviation for `is_normal.strict_mono.monotone`.
#### Estimated changes
Modified src/set_theory/fixed_points.lean


Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.is_normal.monotone



## [2022-04-11 11:52:31](https://github.com/leanprover-community/mathlib/commit/c5b83f0)
doc(combinatorics/simple_graph/basic): mention half-edge synonym for darts ([#13312](https://github.com/leanprover-community/mathlib/pull/13312))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean




## [2022-04-11 11:52:30](https://github.com/leanprover-community/mathlib/commit/722c0df)
feat(category_theory/nat_iso): add simp lemmas ([#13303](https://github.com/leanprover-community/mathlib/pull/13303))
#### Estimated changes
Modified src/category_theory/natural_isomorphism.lean
- \+ *lemma* category_theory.nat_iso.naturality_1'
- \+ *lemma* category_theory.nat_iso.naturality_2'



## [2022-04-11 11:52:29](https://github.com/leanprover-community/mathlib/commit/f7e862f)
feat(analysis/special_functions/pow): `z ^ w` is continuous in `(z, w)` at `(0, w)` if `0 < re w` ([#13288](https://github.com/leanprover-community/mathlib/pull/13288))
Also add a few supporting lemmas.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* complex.abs_cpow_le
- \+ *lemma* complex.abs_cpow_of_ne_zero
- \+ *lemma* complex.continuous_at_cpow_zero_of_re_pos



## [2022-04-11 11:52:28](https://github.com/leanprover-community/mathlib/commit/57682ff)
feat(data/complex/is_R_or_C): add `polynomial.of_real_eval` ([#13287](https://github.com/leanprover-community/mathlib/pull/13287))
#### Estimated changes
Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* polynomial.of_real_eval



## [2022-04-11 11:52:27](https://github.com/leanprover-community/mathlib/commit/577df07)
feat(analysis/asymptotics): add a few versions of `c=o(x)` as `x→∞` ([#13286](https://github.com/leanprover-community/mathlib/pull/13286))
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+ *lemma* asymptotics.is_o_const_id_at_bot
- \+ *lemma* asymptotics.is_o_const_id_at_top
- \+ *lemma* asymptotics.is_o_const_id_comap_norm_at_top



## [2022-04-11 11:52:26](https://github.com/leanprover-community/mathlib/commit/171e2aa)
feat(group_theory/group_action/basic): A `quotient_action` induces an action on left cosets ([#13283](https://github.com/leanprover-community/mathlib/pull/13283))
A `quotient_action` induces an action on left cosets.
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \+/\- *lemma* mul_action.quotient.smul_coe
- \+/\- *lemma* mul_action.quotient.smul_mk

Modified src/linear_algebra/alternating.lean




## [2022-04-11 11:52:25](https://github.com/leanprover-community/mathlib/commit/65b5dd8)
feat(group_theory/transversal): A `quotient_action` induces an action on left transversals ([#13282](https://github.com/leanprover-community/mathlib/pull/13282))
A `quotient_action` induces an action on left transversals.
Once [#13283](https://github.com/leanprover-community/mathlib/pull/13283) is merged, I'll PR some more API generalizing the existing lemma `smul_symm_apply_eq_mul_symm_apply_inv_smul`.
#### Estimated changes
Modified src/group_theory/complement.lean
- \+ *lemma* subgroup.smul_to_fun

Modified src/group_theory/schur_zassenhaus.lean




## [2022-04-11 11:52:24](https://github.com/leanprover-community/mathlib/commit/2eba524)
chore(topology/algebra/uniform_group): use morphism classes ([#13273](https://github.com/leanprover-community/mathlib/pull/13273))
#### Estimated changes
Modified src/topology/algebra/uniform_group.lean
- \+/\- *lemma* uniform_continuous_monoid_hom_of_continuous
- \+ *lemma* uniform_continuous_of_continuous_at_one
- \+/\- *lemma* uniform_continuous_of_tendsto_one
- \+/\- *lemma* uniform_group.uniform_continuous_iff_open_ker



## [2022-04-11 11:52:23](https://github.com/leanprover-community/mathlib/commit/2b80d4a)
feat(topology/order): if `e` is an equiv, `induced e.symm = coinduced e` ([#13272](https://github.com/leanprover-community/mathlib/pull/13272))
#### Estimated changes
Modified src/topology/order.lean
- \+ *lemma* equiv.coinduced_symm
- \+ *lemma* equiv.induced_symm



## [2022-04-11 11:52:21](https://github.com/leanprover-community/mathlib/commit/c160083)
feat(algebra/big_operators): `norm_num` plugin for list/multiset/finset prod/sum ([#13005](https://github.com/leanprover-community/mathlib/pull/13005))
This PR provides a plugin for the `norm_num` tactic that can evaluate finite sums and products, over lists, multisets and finsets.
`simp` could already handle some of these operations, but `norm_num` is overall much more suited to dealing with larger numerical operations such as arising from large sums.
I implemented the tactic as a `norm_num` plugin since it's intended to deal with numbers. I'm happy to make it its own tactic (`norm_bigop`?) if you feel this is outside of the `norm_num` scope. Similarly, I could also make a separate tactic for the parts that rewrite a list/multiset/finset into a sequence of `list.cons`es.
#### Estimated changes
Added src/algebra/big_operators/norm_num.lean
- \+ *lemma* tactic.norm_num.finset.eval_prod_of_list
- \+ *lemma* tactic.norm_num.finset.insert_eq_coe_list_cons
- \+ *lemma* tactic.norm_num.finset.insert_eq_coe_list_of_mem
- \+ *lemma* tactic.norm_num.list.cons_congr
- \+ *lemma* tactic.norm_num.list.map_congr
- \+ *lemma* tactic.norm_num.list.map_cons_congr
- \+ *lemma* tactic.norm_num.list.not_mem_cons
- \+ *lemma* tactic.norm_num.list.prod_congr
- \+ *lemma* tactic.norm_num.list.prod_cons_congr
- \+ *lemma* tactic.norm_num.multiset.cons_congr
- \+ *lemma* tactic.norm_num.multiset.map_congr
- \+ *lemma* tactic.norm_num.multiset.prod_congr

Modified src/tactic/core.lean


Modified test/norm_num_ext.lean




## [2022-04-11 09:27:57](https://github.com/leanprover-community/mathlib/commit/e5bd941)
feat(scripts): make style lint script more robust to lines starting with spaces ([#13317](https://github.com/leanprover-community/mathlib/pull/13317))
Currently some banned commands aren't caught if the line is indented.
Because of this I previously snuck in a `set_option pp.all true` by accident
#### Estimated changes
Modified scripts/lint-style.py


Modified src/group_theory/order_of_element.lean




## [2022-04-11 09:27:56](https://github.com/leanprover-community/mathlib/commit/cd616e0)
feat(analysis/special_functions/pow): more versions of `x ^ k = o(exp(b * x))` ([#13285](https://github.com/leanprover-community/mathlib/pull/13285))
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* is_o_pow_exp_pos_mul_at_top
- \+ *lemma* is_o_rpow_exp_at_top
- \+ *lemma* is_o_rpow_exp_pos_mul_at_top
- \+ *lemma* is_o_zpow_exp_pos_mul_at_top



## [2022-04-11 09:27:54](https://github.com/leanprover-community/mathlib/commit/706905c)
fix(algebra/indicator_function): fix name of `mul_indicator_eq_one_iff` ([#13284](https://github.com/leanprover-community/mathlib/pull/13284))
It is about `≠`, so call it `mul_indicator_ne_one_iff`/`indicator_ne_zero_iff`.
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+ *lemma* set.mul_indicator_apply_ne_one
- \- *lemma* set.mul_indicator_eq_one_iff

Modified src/measure_theory/measure/measure_space_def.lean


Modified src/measure_theory/probability_mass_function/constructions.lean
- \+/\- *lemma* pmf.mem_support_filter_iff



## [2022-04-11 09:27:53](https://github.com/leanprover-community/mathlib/commit/ff507a3)
feat(model_theory/basic): Structures over the empty language ([#13281](https://github.com/leanprover-community/mathlib/pull/13281))
Any type is a first-order structure over the empty language.
Any function, embedding, or equiv is a first-order hom, embedding or equiv over the empty language.
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *def* embedding.empty
- \+ *def* equiv.empty
- \+/\- *def* first_order.language.embedding.to_hom
- \+ *lemma* first_order.language.empty.nonempty_embedding_iff
- \+ *lemma* first_order.language.empty.nonempty_equiv_iff
- \+/\- *def* first_order.language.equiv.to_embedding
- \+/\- *def* first_order.language.equiv.to_hom
- \+ *def* first_order.language.hom_class.to_hom
- \+ *def* first_order.language.strong_hom_class.to_embedding
- \+ *def* first_order.language.strong_hom_class.to_equiv
- \+ *def* function.empty_hom

Modified src/model_theory/language_map.lean
- \+/\- *def* first_order.language.constants_on



## [2022-04-11 09:27:52](https://github.com/leanprover-community/mathlib/commit/fe17fee)
feat(topology/algebra/uniform_group): a subgroup of a uniform group is a uniform group ([#13277](https://github.com/leanprover-community/mathlib/pull/13277))
#### Estimated changes
Modified src/topology/algebra/uniform_group.lean




## [2022-04-11 09:27:50](https://github.com/leanprover-community/mathlib/commit/6f428ed)
feat(group_theory/schreier): Finset version of Schreier's lemma ([#13274](https://github.com/leanprover-community/mathlib/pull/13274))
This PR adds a finset version of Schreier's lemma, getting closer to a statement in terms of `group.fg` and `group.rank`.
#### Estimated changes
Modified src/group_theory/schreier.lean
- \+ *lemma* subgroup.closure_mul_image_eq_top'



## [2022-04-11 09:27:48](https://github.com/leanprover-community/mathlib/commit/102311e)
fix(algebra/module/basic,group_theory/group_action/defs): generalize nat and int smul_comm_class instances ([#13174](https://github.com/leanprover-community/mathlib/pull/13174))
The `add_group.int_smul_with_zero` instance appears to be new, everything else is moved and has `[semiring R] [add_comm_monoid M] [module R M]` relaxed to `[monoid R] [add_monoid M] [distrib_mul_action R M]`, with the variables renamed to match the destination file.
#### Estimated changes
Modified src/algebra/group_power/basic.lean


Modified src/algebra/module/basic.lean


Modified src/algebra/smul_with_zero.lean


Modified src/group_theory/group_action/defs.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/tactic/abel.lean




## [2022-04-11 04:32:07](https://github.com/leanprover-community/mathlib/commit/4d27ecf)
refactor(order/conditionally_complete_lattice): `csupr_le_csupr` → `csupr_mono` ([#13320](https://github.com/leanprover-community/mathlib/pull/13320))
For consistency with `supr_mono` and `infi_mono`
#### Estimated changes
Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/order/conditionally_complete_lattice.lean
- \- *lemma* cinfi_le_cinfi
- \+ *lemma* cinfi_mono
- \- *lemma* csupr_le_csupr
- \+ *lemma* csupr_mono

Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean




## [2022-04-11 02:03:03](https://github.com/leanprover-community/mathlib/commit/6f9cb03)
chore(*): make more transitive relations available to calc ([#12860](https://github.com/leanprover-community/mathlib/pull/12860))
Fixed as many possible declarations to have the correct argument order, as per [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/calc.20with.20.60.E2.89.83*.60). Golfed some random ones while I was at it.
#### Estimated changes
Modified src/algebra/divisibility.lean
- \+/\- *theorem* dvd_trans

Modified src/analysis/asymptotics/asymptotic_equivalent.lean
- \+/\- *lemma* asymptotics.is_equivalent.trans
- \+/\- *def* asymptotics.is_equivalent

Modified src/analysis/convex/extreme.lean


Modified src/analysis/special_functions/polynomials.lean


Modified src/combinatorics/colex.lean
- \+/\- *lemma* colex.le_trans
- \+/\- *lemma* colex.lt_trans

Modified src/computability/tm_computable.lean
- \+/\- *def* turing.evals_to_in_time.trans

Modified src/computability/turing_machine.lean


Modified src/data/list/rotate.lean
- \+/\- *lemma* list.is_rotated.trans

Modified src/data/set/basic.lean
- \+/\- *theorem* set.mem_of_mem_of_subset
- \+/\- *theorem* set.subset.trans

Modified src/data/sym/sym2.lean
- \+/\- *lemma* sym2.rel.trans

Modified src/logic/equiv/basic.lean


Modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* interval_integrable.trans

Modified src/measure_theory/measure/vector_measure.lean
- \+/\- *lemma* measure_theory.vector_measure.absolutely_continuous.trans

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.eventually_eq.trans

Modified src/order/ideal.lean
- \+/\- *lemma* order.ideal.mem_of_mem_of_le

Modified src/order/rel_classes.lean
- \+/\- *lemma* ssubset_trans
- \+/\- *lemma* subset_trans

Added test/calc.lean




## [2022-04-11 00:55:09](https://github.com/leanprover-community/mathlib/commit/a85958c)
chore(measure_theory/mconstructions/prod): Speed up `finite_spanning_sets_in.prod` ([#13325](https://github.com/leanprover-community/mathlib/pull/13325))
Disable the computability check on `measure_theory.measure.finite_spanning_sets_in.prod` because it was taking 20s of compilation.
#### Estimated changes
Modified src/measure_theory/constructions/prod.lean
- \- *def* measure_theory.measure.finite_spanning_sets_in.prod



## [2022-04-11 00:55:08](https://github.com/leanprover-community/mathlib/commit/a2d09b2)
feat(topology/algebra/order): add `le_on_closure` ([#13290](https://github.com/leanprover-community/mathlib/pull/13290))
#### Estimated changes
Modified src/topology/algebra/order/basic.lean
- \+ *lemma* le_on_closure



## [2022-04-10 23:04:54](https://github.com/leanprover-community/mathlib/commit/e5ae099)
chore(topology/uniform_space/basic): golf a proof ([#13289](https://github.com/leanprover-community/mathlib/pull/13289))
Rewrite a proof using tactic mode and golf it.
#### Estimated changes
Modified src/topology/uniform_space/basic.lean




## [2022-04-10 23:04:53](https://github.com/leanprover-community/mathlib/commit/8491021)
chore(algebra/invertible): generalise typeclasses ([#13275](https://github.com/leanprover-community/mathlib/pull/13275))
#### Estimated changes
Modified src/algebra/invertible.lean
- \+/\- *lemma* inv_of_neg
- \+/\- *lemma* inv_of_two_add_inv_of_two
- \+/\- *def* invertible_neg

Modified src/algebra/ne_zero.lean




## [2022-04-10 23:04:52](https://github.com/leanprover-community/mathlib/commit/4ded5ca)
fix(field_theory/galois): update docstring ([#13188](https://github.com/leanprover-community/mathlib/pull/13188))
#### Estimated changes
Modified src/field_theory/galois.lean




## [2022-04-10 23:04:51](https://github.com/leanprover-community/mathlib/commit/be22d07)
feat(data/sym/basic): some basic lemmas in preparation for stars and bars ([#12479](https://github.com/leanprover-community/mathlib/pull/12479))
Some lemmas extracted from @huynhtrankhanh's [#11162](https://github.com/leanprover-community/mathlib/pull/11162), moved here to a separate PR
#### Estimated changes
Modified src/data/sym/basic.lean
- \+ *def* sym.attach
- \+ *lemma* sym.attach_cons
- \+ *lemma* sym.attach_map_coe
- \+ *lemma* sym.attach_mk
- \+ *lemma* sym.attach_nil
- \+ *lemma* sym.coe_attach
- \+ *lemma* sym.coe_cons
- \+ *lemma* sym.coe_erase
- \+ *lemma* sym.coe_inj
- \+ *lemma* sym.coe_injective
- \+ *lemma* sym.coe_map
- \+/\- *def* sym.cons'
- \+/\- *def* sym.cons
- \+/\- *lemma* sym.cons_equiv_eq_equiv_cons
- \+/\- *lemma* sym.cons_erase
- \+/\- *def* sym.equiv_congr
- \+ *lemma* sym.erase_cons_head
- \+ *lemma* sym.erase_mk
- \+/\- *def* sym.map
- \+ *lemma* sym.map_congr
- \+/\- *lemma* sym.map_cons
- \+ *lemma* sym.map_id'
- \+/\- *lemma* sym.map_id
- \+ *lemma* sym.map_injective
- \+ *lemma* sym.map_mk
- \+/\- *lemma* sym.map_zero
- \+ *lemma* sym.mem_attach
- \+/\- *lemma* sym.mem_map
- \+ *lemma* sym.mem_mk
- \+/\- *def* sym.sym'
- \+/\- *def* sym.sym_equiv_sym'
- \+/\- *def* sym
- \+/\- *def* vector.perm.is_setoid



## [2022-04-10 23:04:50](https://github.com/leanprover-community/mathlib/commit/609eb59)
feat(set_theory/cofinality): Every ordinal has a fundamental sequence ([#12317](https://github.com/leanprover-community/mathlib/pull/12317))
#### Estimated changes
Modified src/set_theory/cofinality.lean
- \+/\- *theorem* ordinal.cof_cof
- \+ *theorem* ordinal.exists_fundamental_sequence
- \+ *theorem* ordinal.is_fundamental_sequence.blsub_eq
- \+ *theorem* ordinal.is_fundamental_sequence.cof_eq
- \+ *theorem* ordinal.is_fundamental_sequence.monotone
- \+ *theorem* ordinal.is_fundamental_sequence.strict_mono
- \+ *theorem* ordinal.is_fundamental_sequence.trans
- \+ *def* ordinal.is_fundamental_sequence



## [2022-04-10 21:57:11](https://github.com/leanprover-community/mathlib/commit/5bf5740)
chore(category_theory/fin_category): Speed up `as_type_equiv_obj_as_type` ([#13298](https://github.com/leanprover-community/mathlib/pull/13298))
Rename `obj_as_type_equiv_as_type` to `as_type_equiv_obj_as_type` (likely a typo). Use `equivalence.mk` instead of `equivalence.mk'` to build it and split the functors to separate definitions to tag them with `@[simps]` and make `dsimp` go further.
On my machine, this cuts down the compile time from 41s to 3s.
#### Estimated changes
Modified src/category_theory/fin_category.lean
- \- *def* category_theory.fin_category.obj_as_type_equiv_as_type



## [2022-04-10 20:28:46](https://github.com/leanprover-community/mathlib/commit/60ccf8f)
feat(linear_algebra): add `adjoint_pair` from `bilinear_form` ([#13203](https://github.com/leanprover-community/mathlib/pull/13203))
Copying the definition and theorem about adjoint pairs from `bilinear_form` to `sesquilinear_form`.
Defines the composition of two linear maps with a bilinear map to form a new bilinear map, which was missing from the `bilinear_map` API.
We also use the new definition of adjoint pairs in `analysis/inner_product_space/adjoint`.
#### Estimated changes
Modified src/analysis/inner_product_space/adjoint.lean
- \- *lemma* continuous_linear_map.is_adjoint_pair
- \+ *lemma* continuous_linear_map.is_adjoint_pair_inner
- \- *lemma* linear_map.is_adjoint_pair
- \+ *lemma* linear_map.is_adjoint_pair_inner

Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* bilin_form.comp_inj
- \- *lemma* bilin_form.comp_injective

Modified src/linear_algebra/bilinear_map.lean
- \+ *def* linear_map.compl₁₂
- \+ *theorem* linear_map.compl₁₂_apply
- \+ *lemma* linear_map.compl₁₂_inj

Modified src/linear_algebra/sesquilinear_form.lean
- \+ *lemma* linear_map.is_adjoint_pair.add
- \+ *lemma* linear_map.is_adjoint_pair.comp
- \+ *lemma* linear_map.is_adjoint_pair.mul
- \+ *lemma* linear_map.is_adjoint_pair.smul
- \+ *lemma* linear_map.is_adjoint_pair.sub
- \+ *def* linear_map.is_adjoint_pair
- \+ *lemma* linear_map.is_adjoint_pair_id
- \+ *lemma* linear_map.is_adjoint_pair_iff_comp_eq_compl₂
- \+ *lemma* linear_map.is_adjoint_pair_zero
- \+ *def* linear_map.is_pair_self_adjoint
- \+ *lemma* linear_map.is_pair_self_adjoint_equiv
- \+ *def* linear_map.is_pair_self_adjoint_submodule
- \+ *def* linear_map.is_skew_adjoint
- \+ *lemma* linear_map.is_skew_adjoint_iff_neg_self_adjoint
- \+ *lemma* linear_map.mem_is_pair_self_adjoint_submodule
- \+ *lemma* linear_map.mem_self_adjoint_submodule
- \+ *lemma* linear_map.mem_skew_adjoint_submodule
- \+ *def* linear_map.self_adjoint_submodule
- \+ *def* linear_map.skew_adjoint_submodule



## [2022-04-10 20:28:45](https://github.com/leanprover-community/mathlib/commit/a30cba4)
feat(set_theory/cardinal_ordinal): Simp lemmas for `mk` ([#13119](https://github.com/leanprover-community/mathlib/pull/13119))
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* cardinal.add_eq_max'
- \+ *theorem* cardinal.add_mk_eq_max'
- \+ *theorem* cardinal.add_mk_eq_max
- \+ *lemma* cardinal.mk_add_one_eq
- \+ *theorem* cardinal.mk_mul_omega_eq
- \+ *theorem* cardinal.mul_mk_eq_max
- \+ *theorem* cardinal.omega_mul_mk_eq



## [2022-04-10 19:34:23](https://github.com/leanprover-community/mathlib/commit/965f46d)
feat(category_theory/monoidal): coherence tactic ([#13125](https://github.com/leanprover-community/mathlib/pull/13125))
This is an alternative to [#12697](https://github.com/leanprover-community/mathlib/pull/12697) (although this one does not handle bicategories!)
From the docstring:
```
Use the coherence theorem for monoidal categories to solve equations in a monoidal equation,
where the two sides only differ by replacing strings of "structural" morphisms with
different strings with the same source and target.
That is, `coherence` can handle goals of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `coherence1`.
```
This PR additionally provides a "composition up to unitors+associators" operation, so you can write
```
example {U V W X Y : C} (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) : U ⟶ Y := f ⊗≫ g
```
#### Estimated changes
Modified src/category_theory/monoidal/center.lean


Added src/category_theory/monoidal/coherence.lean
- \+ *def* category_theory.monoidal_category.monoidal_comp
- \+ *lemma* category_theory.monoidal_category.monoidal_comp_refl
- \+ *def* category_theory.monoidal_category.monoidal_iso
- \+ *def* category_theory.monoidal_category.monoidal_iso_comp
- \+ *lemma* tactic.coherence.assoc_lift_hom

Modified src/category_theory/monoidal/rigid.lean


Added test/coherence.lean




## [2022-04-10 19:34:22](https://github.com/leanprover-community/mathlib/commit/0bc2aa9)
feat(data/fin/tuple/nat_antidiagonal): add `antidiagonal_tuple` ([#13031](https://github.com/leanprover-community/mathlib/pull/13031))
#### Estimated changes
Added src/data/fin/tuple/nat_antidiagonal.lean
- \+ *def* finset.nat.antidiagonal_tuple
- \+ *lemma* finset.nat.antidiagonal_tuple_one
- \+ *lemma* finset.nat.antidiagonal_tuple_two
- \+ *lemma* finset.nat.antidiagonal_tuple_zero_succ
- \+ *lemma* finset.nat.antidiagonal_tuple_zero_zero
- \+ *lemma* finset.nat.mem_antidiagonal_tuple
- \+ *def* list.nat.antidiagonal_tuple
- \+ *lemma* list.nat.antidiagonal_tuple_one
- \+ *lemma* list.nat.antidiagonal_tuple_two
- \+ *lemma* list.nat.antidiagonal_tuple_zero_succ
- \+ *lemma* list.nat.antidiagonal_tuple_zero_zero
- \+ *lemma* list.nat.mem_antidiagonal_tuple
- \+ *lemma* list.nat.nodup_antidiagonal_tuple
- \+ *def* multiset.nat.antidiagonal_tuple
- \+ *lemma* multiset.nat.antidiagonal_tuple_one
- \+ *lemma* multiset.nat.antidiagonal_tuple_two
- \+ *lemma* multiset.nat.antidiagonal_tuple_zero_succ
- \+ *lemma* multiset.nat.antidiagonal_tuple_zero_zero
- \+ *lemma* multiset.nat.mem_antidiagonal_tuple
- \+ *lemma* multiset.nat.nodup_antidiagonal_tuple



## [2022-04-10 15:57:49](https://github.com/leanprover-community/mathlib/commit/6d0984d)
doc(README): improve documentation on how to contribute ([#13116](https://github.com/leanprover-community/mathlib/pull/13116))
Create a new contributing section which highlights the basic steps on how to start contributing to mathlib
#### Estimated changes
Modified README.md




## [2022-04-10 13:49:42](https://github.com/leanprover-community/mathlib/commit/6368956)
counterexample(counterexamples/char_p_zero_ne_char_zero.lean): `char_p R 0` and `char_zero R` need not coincide ([#13080](https://github.com/leanprover-community/mathlib/pull/13080))
Following the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F), this counterexample formalizes a `semiring R` for which `char_p R 0` holds, but `char_zero R` does not.
See [#13075](https://github.com/leanprover-community/mathlib/pull/13075) for the PR that lead to this example.
#### Estimated changes
Added counterexamples/char_p_zero_ne_char_zero.lean
- \+ *lemma* add_one_eq_one
- \+ *lemma* with_zero_unit_char_p_zero
- \+ *lemma* with_zero_unit_not_char_zero

Modified src/algebra/char_p/basic.lean


Modified src/algebra/char_zero.lean




## [2022-04-10 12:36:58](https://github.com/leanprover-community/mathlib/commit/83225b3)
feat(order/monovary): Add missing `monovary` lemmas ([#13243](https://github.com/leanprover-community/mathlib/pull/13243))
Add lemmas for postcomposing monovarying functions with monotone/antitone functions. Protect lemmas that needed it. Fix typos.
#### Estimated changes
Modified src/order/monovary.lean
- \+ *lemma* antivary.comp_antitone_left
- \+ *lemma* antivary.comp_monotone_left
- \+/\- *lemma* antivary.dual
- \+/\- *lemma* antivary.dual_left
- \+/\- *lemma* antivary.dual_right
- \+ *lemma* antivary_on.comp_antitone_on_left
- \+ *lemma* antivary_on.comp_antitone_on_right
- \+ *lemma* antivary_on.comp_monotone_on_left
- \+ *lemma* antivary_on.comp_monotone_on_right
- \+ *lemma* antivary_on.comp_right
- \+/\- *lemma* antivary_on.dual
- \+/\- *lemma* antivary_on.dual_left
- \+/\- *lemma* antivary_on.dual_right
- \+ *lemma* antivary_on.empty
- \+ *lemma* monovary.comp_antitone_left
- \+ *lemma* monovary.comp_monotone_left
- \+/\- *lemma* monovary.dual
- \+/\- *lemma* monovary.dual_left
- \+/\- *lemma* monovary.dual_right
- \+ *lemma* monovary_on.comp_antitone_on_left
- \+ *lemma* monovary_on.comp_antitone_on_right
- \+ *lemma* monovary_on.comp_monotone_on_left
- \+ *lemma* monovary_on.comp_monotone_on_right
- \+ *lemma* monovary_on.comp_right
- \+/\- *lemma* monovary_on.dual
- \+/\- *lemma* monovary_on.dual_left
- \+/\- *lemma* monovary_on.dual_right
- \+ *lemma* monovary_on.empty
- \+/\- *lemma* monovary_on_self
- \- *lemma* subsingleton.antivary
- \- *lemma* subsingleton.antivary_on
- \- *lemma* subsingleton.monovary
- \- *lemma* subsingleton.monovary_on



## [2022-04-10 12:36:57](https://github.com/leanprover-community/mathlib/commit/32cc868)
feat(measure_theory/measure/measure_space): let measure.map work with ae_measurable functions ([#13241](https://github.com/leanprover-community/mathlib/pull/13241))
Currently, `measure.map f μ` is zero if `f` is not measurable. This means that one can not say that two integrable random variables `X` and `Y` have the same distribution by requiring `measure.map X μ = measure.map Y μ`, as `X` or `Y` might not be measurable. We adjust the definition of `measure.map` to also work with almost everywhere measurable functions. This means that many results in the library that were only true for measurable functions become true for ae measurable functions. We generalize some of the existing code to this more general setting.
#### Estimated changes
Modified src/dynamics/ergodic/measure_preserving.lean


Modified src/measure_theory/constructions/borel_space.lean
- \+/\- *lemma* continuous.ae_measurable

Modified src/measure_theory/constructions/prod.lean


Modified src/measure_theory/function/ess_sup.lean
- \+/\- *lemma* ess_sup_comp_le_ess_sup_map_measure
- \+/\- *lemma* ess_sup_map_measure
- \+/\- *lemma* ess_sup_map_measure_of_measurable

Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.integrable.comp_ae_measurable

Modified src/measure_theory/function/lp_space.lean
- \+/\- *lemma* measure_theory.mem_ℒp_map_measure_iff
- \+/\- *lemma* measure_theory.snorm_map_measure

Modified src/measure_theory/function/strongly_measurable.lean
- \+ *lemma* measure_theory.ae_strongly_measurable.comp_ae_measurable

Modified src/measure_theory/group/integration.lean


Modified src/measure_theory/group/prod.lean


Modified src/measure_theory/integral/bochner.lean
- \+/\- *lemma* measure_theory.integral_map

Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/integral/set_integral.lean


Modified src/measure_theory/measure/ae_measurable.lean
- \+ *lemma* ae_measurable.comp_ae_measurable
- \+/\- *lemma* ae_measurable.comp_measurable
- \+ *lemma* measure_theory.measure.map_mono_of_ae_measurable
- \+ *lemma* measure_theory.measure.restrict_map_of_ae_measurable

Modified src/measure_theory/measure/lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.ae_eq_comp'
- \+/\- *lemma* measure_theory.ae_eq_comp
- \+/\- *lemma* measure_theory.ae_map_iff
- \+/\- *lemma* measure_theory.ae_of_ae_map
- \- *lemma* measure_theory.ae_smul_measure_iff
- \+ *lemma* measure_theory.measure.ae_smul_measure_iff
- \+/\- *theorem* measure_theory.measure.le_map_apply
- \+/\- *def* measure_theory.measure.map
- \+/\- *lemma* measure_theory.measure.map_add
- \+/\- *theorem* measure_theory.measure.map_apply
- \+ *theorem* measure_theory.measure.map_apply_of_ae_measurable
- \+ *lemma* measure_theory.measure.map_congr
- \+/\- *lemma* measure_theory.measure.map_mono
- \+ *theorem* measure_theory.measure.map_of_not_ae_measurable
- \- *theorem* measure_theory.measure.map_of_not_measurable
- \+/\- *lemma* measure_theory.measure.map_smul
- \+/\- *lemma* measure_theory.measure.map_to_outer_measure
- \+/\- *lemma* measure_theory.measure.map_zero
- \- *lemma* measure_theory.measure.mapₗ_apply
- \+ *lemma* measure_theory.measure.mapₗ_apply_of_measurable
- \+ *lemma* measure_theory.measure.mapₗ_congr
- \+ *lemma* measure_theory.measure.mapₗ_mk_apply_of_ae_measurable
- \+/\- *lemma* measure_theory.measure.preimage_null_of_map_null
- \+/\- *lemma* measure_theory.measure.tendsto_ae_map
- \+/\- *lemma* measure_theory.mem_ae_map_iff
- \+/\- *lemma* measure_theory.mem_ae_of_mem_ae_map
- \+/\- *lemma* measure_theory.sigma_finite.of_map

Modified src/measure_theory/measure/regular.lean


Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_eq.preimage

Modified src/probability/density.lean




## [2022-04-10 09:05:10](https://github.com/leanprover-community/mathlib/commit/ef51d23)
feat(category_theory/shift): restricting shift functors to a subcategory ([#13265](https://github.com/leanprover-community/mathlib/pull/13265))
Given a family of endomorphisms of `C` which are interwined by a fully faithful `F : C ⥤ D`
with shift functors on `D`, we can promote that family to shift functors on `C`.
For LTE.
#### Estimated changes
Modified src/category_theory/functor/fully_faithful.lean
- \+ *def* category_theory.nat_iso_of_comp_fully_faithful

Modified src/category_theory/shift.lean
- \+ *def* category_theory.has_shift_of_fully_faithful
- \+ *def* category_theory.has_shift_of_fully_faithful_comm



## [2022-04-10 09:05:09](https://github.com/leanprover-community/mathlib/commit/c916b64)
feat(ring_theory/polynomial/opposites + data/{polynomial/basic + finsupp/basic}): move `op_ring_equiv` to a new file + lemmas ([#13162](https://github.com/leanprover-community/mathlib/pull/13162))
This PR moves the isomorphism `R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X]` to a new file `ring_theory.polynomial.opposites`.
I also proved some basic lemmas about the equivalence.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members)
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.support_map_range_of_injective

Modified src/data/polynomial/basic.lean
- \- *def* polynomial.op_ring_equiv

Added src/ring_theory/polynomial/opposites.lean
- \+ *lemma* polynomial.coeff_op_ring_equiv
- \+ *lemma* polynomial.leading_coeff_op_ring_equiv
- \+ *lemma* polynomial.nat_degree_op_ring_equiv
- \+ *def* polynomial.op_ring_equiv
- \+ *lemma* polynomial.op_ring_equiv_op_C
- \+ *lemma* polynomial.op_ring_equiv_op_C_mul_X_pow
- \+ *lemma* polynomial.op_ring_equiv_op_X
- \+ *lemma* polynomial.op_ring_equiv_op_monomial
- \+ *lemma* polynomial.op_ring_equiv_symm_C
- \+ *lemma* polynomial.op_ring_equiv_symm_C_mul_X_pow
- \+ *lemma* polynomial.op_ring_equiv_symm_X
- \+ *lemma* polynomial.op_ring_equiv_symm_monomial
- \+ *lemma* polynomial.support_op_ring_equiv



## [2022-04-10 09:05:08](https://github.com/leanprover-community/mathlib/commit/d70e26b)
feat(analysis/convex/topology): improve some lemmas ([#13136](https://github.com/leanprover-community/mathlib/pull/13136))
Replace some `s` with `closure s` in the LHS of `⊆` in some lemmas.
#### Estimated changes
Modified src/analysis/calculus/fderiv_symmetric.lean


Modified src/analysis/convex/integral.lean


Modified src/analysis/convex/strict_convex_space.lean


Modified src/analysis/convex/topology.lean
- \+ *lemma* convex.add_smul_mem_interior'
- \+ *lemma* convex.add_smul_sub_mem_interior'
- \- *lemma* convex.closure
- \+ *lemma* convex.closure_subset_interior_image_homothety_of_one_lt
- \+ *lemma* convex.combo_closure_interior_mem_interior
- \+ *lemma* convex.combo_closure_interior_subset_interior
- \+ *lemma* convex.combo_interior_closure_mem_interior
- \+ *lemma* convex.combo_interior_closure_subset_interior
- \+ *lemma* convex.combo_interior_self_mem_interior
- \- *lemma* convex.combo_mem_interior_left
- \- *lemma* convex.combo_mem_interior_right
- \+ *lemma* convex.combo_self_interior_mem_interior
- \- *lemma* convex.interior
- \- *lemma* convex.is_path_connected
- \+ *lemma* convex.open_segment_closure_interior_subset_interior
- \+ *lemma* convex.open_segment_interior_closure_subset_interior
- \+ *lemma* convex.open_segment_interior_self_subset_interior
- \+ *lemma* convex.open_segment_self_interior_subset_interior
- \- *lemma* convex.open_segment_subset_interior_left
- \- *lemma* convex.open_segment_subset_interior_right
- \+/\- *lemma* convex.subset_interior_image_homothety_of_one_lt
- \- *lemma* topological_add_group.path_connected



## [2022-04-10 06:43:20](https://github.com/leanprover-community/mathlib/commit/208ebd4)
feat(algebra/order/monoid_lemmas_zero_lt): port some lemmas from `algebra.order.monoid_lemmas` ([#12961](https://github.com/leanprover-community/mathlib/pull/12961))
Although the names of these lemmas are from `algebra.order.monoid_lemmas`, many of the lemmas in `algebra.order.monoid_lemmas` have incorrect names, and some others may not be appropriate. Also, many lemmas are missing in `algebra.order.monoid_lemmas`. It may be necessary to make some renames and additions.
#### Estimated changes
Modified src/algebra/order/monoid_lemmas_zero_lt.lean
- \+ *lemma* zero_lt.exists_square_le'
- \+ *lemma* zero_lt.exists_square_le
- \+ *lemma* zero_lt.le_mul_iff_one_le_left
- \+ *lemma* zero_lt.le_mul_iff_one_le_right
- \+ *lemma* zero_lt.le_mul_of_le_of_one_le'
- \+ *lemma* zero_lt.le_mul_of_le_of_one_le
- \+ *lemma* zero_lt.le_mul_of_one_le_left'
- \+ *lemma* zero_lt.le_mul_of_one_le_left
- \+ *lemma* zero_lt.le_mul_of_one_le_of_le'
- \+ *lemma* zero_lt.le_mul_of_one_le_of_le
- \+ *lemma* zero_lt.le_mul_of_one_le_right'
- \+ *lemma* zero_lt.le_mul_of_one_le_right
- \+ *lemma* zero_lt.left.mul_le_one_of_le_of_le'
- \+ *lemma* zero_lt.left.mul_le_one_of_le_of_le
- \+ *lemma* zero_lt.left.mul_lt_one_of_le_of_lt
- \+ *lemma* zero_lt.left.mul_lt_one_of_lt_of_le
- \+ *lemma* zero_lt.left.mul_lt_one_of_lt_of_lt
- \+ *lemma* zero_lt.left.one_le_mul_of_le_of_le'
- \+ *lemma* zero_lt.left.one_le_mul_of_le_of_le
- \+ *lemma* zero_lt.left.one_lt_mul_of_le_of_lt
- \+ *lemma* zero_lt.left.one_lt_mul_of_lt_of_le
- \+ *lemma* zero_lt.left.one_lt_mul_of_lt_of_lt
- \+ *lemma* zero_lt.lt_mul_iff_one_lt_left
- \+ *lemma* zero_lt.lt_mul_iff_one_lt_right
- \+ *lemma* zero_lt.lt_mul_of_le_of_one_lt
- \+ *lemma* zero_lt.lt_mul_of_lt_of_one_le
- \+ *lemma* zero_lt.lt_mul_of_lt_of_one_lt
- \+ *lemma* zero_lt.lt_mul_of_one_le_of_lt
- \+ *lemma* zero_lt.lt_mul_of_one_lt_of_le
- \+ *lemma* zero_lt.lt_mul_of_one_lt_of_lt
- \+ *lemma* zero_lt.mul_le_iff_le_one_left
- \+ *lemma* zero_lt.mul_le_iff_le_one_right
- \+/\- *lemma* zero_lt.mul_le_mul_left'
- \+ *lemma* zero_lt.mul_le_of_le_of_le_one'
- \+ *lemma* zero_lt.mul_le_of_le_of_le_one
- \+ *lemma* zero_lt.mul_le_of_le_one_left'
- \+ *lemma* zero_lt.mul_le_of_le_one_left
- \+ *lemma* zero_lt.mul_le_of_le_one_of_le'
- \+ *lemma* zero_lt.mul_le_of_le_one_of_le
- \+ *lemma* zero_lt.mul_le_of_le_one_right'
- \+ *lemma* zero_lt.mul_le_of_le_one_right
- \+ *lemma* zero_lt.mul_lt_iff_lt_one_left
- \+ *lemma* zero_lt.mul_lt_iff_lt_one_right
- \+/\- *lemma* zero_lt.mul_lt_mul_left'
- \+ *lemma* zero_lt.mul_lt_of_le_of_lt_one
- \+ *lemma* zero_lt.mul_lt_of_le_one_of_lt
- \+ *lemma* zero_lt.mul_lt_of_lt_of_le_one
- \+ *lemma* zero_lt.mul_lt_of_lt_of_lt_one
- \+ *lemma* zero_lt.mul_lt_of_lt_one_of_le
- \+ *lemma* zero_lt.mul_lt_of_lt_one_of_lt
- \+ *lemma* zero_lt.right.mul_le_one_of_le_of_le'
- \+ *lemma* zero_lt.right.mul_le_one_of_le_of_le
- \+ *lemma* zero_lt.right.mul_lt_one_of_le_of_lt
- \+ *lemma* zero_lt.right.mul_lt_one_of_lt_of_le
- \+ *lemma* zero_lt.right.mul_lt_one_of_lt_of_lt
- \+ *lemma* zero_lt.right.one_le_mul_of_le_of_le'
- \+ *lemma* zero_lt.right.one_le_mul_of_le_of_le
- \+ *lemma* zero_lt.right.one_lt_mul_of_le_of_lt
- \+ *lemma* zero_lt.right.one_lt_mul_of_lt_of_le
- \+ *lemma* zero_lt.right.one_lt_mul_of_lt_of_lt



## [2022-04-10 06:43:19](https://github.com/leanprover-community/mathlib/commit/00980d9)
feat(group_theory/free_product): The ping pong lemma for free groups ([#12916](https://github.com/leanprover-community/mathlib/pull/12916))
We already have the ping-pong-lemma for free products; phrasing it for free groups is
a (potentially) useful corollary, and brings us on-par with the Wikipedia page.
Again, we state it as a lemma that gives a criteria for when `lift` is injective.
#### Estimated changes
Modified src/data/int/basic.lean


Modified src/group_theory/free_product.lean
- \+ *theorem* free_group.injective_lift_of_ping_pong
- \+ *def* free_group_equiv_free_product



## [2022-04-10 06:43:18](https://github.com/leanprover-community/mathlib/commit/dfc1b4c)
feat(topology/algebra/module/character_space): Introduce the character space of an algebra ([#12838](https://github.com/leanprover-community/mathlib/pull/12838))
The character space of a topological algebra is the subset of elements of the weak dual that are also algebra homomorphisms. This space is used in the Gelfand transform, which gives an isomorphism between a commutative C⋆-algebra and continuous functions on the character space of the algebra. This, in turn, is used to construct the continuous functional calculus on C⋆-algebras.
#### Estimated changes
Added src/topology/algebra/module/character_space.lean
- \+ *lemma* weak_dual.character_space.apply_mem_spectrum
- \+ *lemma* weak_dual.character_space.coe_apply
- \+ *lemma* weak_dual.character_space.continuous
- \+ *lemma* weak_dual.character_space.map_add
- \+ *lemma* weak_dual.character_space.map_mul
- \+ *lemma* weak_dual.character_space.map_one
- \+ *lemma* weak_dual.character_space.map_smul
- \+ *lemma* weak_dual.character_space.map_zero
- \+ *def* weak_dual.character_space.to_alg_hom
- \+ *def* weak_dual.character_space.to_clm
- \+ *lemma* weak_dual.character_space.to_clm_apply
- \+ *def* weak_dual.character_space.to_non_unital_alg_hom
- \+ *def* weak_dual.character_space

Modified src/topology/algebra/module/weak_dual.lean




## [2022-04-10 06:43:17](https://github.com/leanprover-community/mathlib/commit/55baab3)
feat(field_theory/krull_topology): added fintype_alg_hom ([#12777](https://github.com/leanprover-community/mathlib/pull/12777))
#### Estimated changes
Modified src/field_theory/minpoly.lean
- \+ *lemma* minpoly.ne_zero_of_finite_field_extension

Modified src/field_theory/primitive_element.lean
- \+ *lemma* field.aux_inj_roots_of_min_poly
- \+ *def* field.roots_of_min_poly_pi_type



## [2022-04-10 06:10:08](https://github.com/leanprover-community/mathlib/commit/36fceb9)
feat(data/list/cycle): Define `cycle.chain` analog to `list.chain` ([#12970](https://github.com/leanprover-community/mathlib/pull/12970))
We define `cycle.chain`, which means that a relation holds in all adjacent elements in a cyclic list. We then show that for `r` a transitive relation, `cycle.chain r l` is equivalent to `r` holding for all pairs of elements in `l`.
#### Estimated changes
Modified src/data/list/cycle.lean
- \+ *lemma* cycle.chain.nil
- \+ *def* cycle.chain
- \+ *lemma* cycle.chain_coe_cons
- \+ *theorem* cycle.chain_iff_pairwise
- \+ *lemma* cycle.chain_map
- \+ *lemma* cycle.chain_ne_nil
- \+ *theorem* cycle.chain_of_pairwise
- \+ *lemma* cycle.chain_singleton
- \+ *lemma* cycle.coe_cons_eq_coe_append
- \+ *lemma* cycle.coe_to_finset
- \+ *theorem* cycle.forall_eq_of_chain



## [2022-04-10 04:05:20](https://github.com/leanprover-community/mathlib/commit/de0aea4)
feat(topology/uniform_space/uniform_convergence): add lemma `tendsto_locally_uniformly_iff_forall_tendsto` ([#13201](https://github.com/leanprover-community/mathlib/pull/13201))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.forall_in_swap

Modified src/order/filter/basic.lean
- \+ *lemma* filter.forall_in_swap

Modified src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* tendsto_locally_uniformly_iff_forall_tendsto
- \+ *lemma* tendsto_uniformly.tendsto_at



## [2022-04-10 04:05:19](https://github.com/leanprover-community/mathlib/commit/26729d6)
chore(ring_theory/polynomial/basic): Generalize `polynomial.degree_lt_equiv` to commutative rings ([#13190](https://github.com/leanprover-community/mathlib/pull/13190))
This is a minor PR to generalise degree_lt_equiv to comm_ring.
Its restriction to field appears to be an oversight.
#### Estimated changes
Modified src/ring_theory/polynomial/basic.lean
- \+/\- *def* polynomial.degree_lt_equiv



## [2022-04-10 04:05:18](https://github.com/leanprover-community/mathlib/commit/2ff12ea)
feat(linear_algebra/bilinear_form): generalize from is_symm to is_refl ([#13181](https://github.com/leanprover-community/mathlib/pull/13181))
Generalize some lemmas that assumed symmetric bilinear forms to reflexive bilinear forms (which is more general) and update docstring (before the condition 'symmetric' was not mentioned)
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/sesquilinear_form.lean
- \+ *lemma* linear_map.is_refl.dom_restrict_refl
- \+ *lemma* linear_map.is_refl.flip_is_refl_iff
- \+ *lemma* linear_map.is_refl.ker_eq_bot_iff_ker_flip_eq_bot
- \+ *lemma* linear_map.is_refl.ker_flip_eq_bot
- \+ *lemma* linear_map.is_refl.nondegenerate_of_separating_left
- \+ *lemma* linear_map.is_refl.nondegenerate_of_separating_right
- \- *lemma* linear_map.is_symm.nondegenerate_of_separating_left
- \- *lemma* linear_map.is_symm.nondegenerate_of_separating_right



## [2022-04-10 01:48:20](https://github.com/leanprover-community/mathlib/commit/8b8f46e)
feat(analysis/complex/arg): link same_ray and complex.arg ([#12764](https://github.com/leanprover-community/mathlib/pull/12764))
#### Estimated changes
Added src/analysis/complex/arg.lean
- \+ *lemma* complex.abs_add_eq
- \+ *lemma* complex.abs_add_eq_iff
- \+ *lemma* complex.abs_sub_eq
- \+ *lemma* complex.same_ray_iff
- \+ *lemma* complex.same_ray_of_arg_eq

Modified src/linear_algebra/ray.lean
- \+/\- *lemma* same_ray.zero_left
- \+/\- *lemma* same_ray.zero_right



## [2022-04-10 01:48:19](https://github.com/leanprover-community/mathlib/commit/7eff233)
feat(set_theory/cofinality): Golf and extend existing results relating `cof` to `sup` and `bsup` ([#12321](https://github.com/leanprover-community/mathlib/pull/12321))
#### Estimated changes
Modified src/set_theory/cofinality.lean
- \+ *theorem* cardinal.blsub_lt_ord_lift_of_is_regular
- \+ *theorem* cardinal.blsub_lt_ord_of_is_regular
- \+ *theorem* cardinal.bsup_lt_ord_lift_of_is_regular
- \+ *theorem* cardinal.bsup_lt_ord_of_is_regular
- \+ *theorem* cardinal.lsub_lt_ord_lift_of_is_regular
- \+ *theorem* cardinal.lsub_lt_ord_of_is_regular
- \+ *theorem* cardinal.sum_lt_lift_of_is_regular
- \+/\- *theorem* cardinal.sum_lt_of_is_regular
- \+ *theorem* cardinal.sup_lt_lift_of_is_regular
- \+/\- *theorem* cardinal.sup_lt_of_is_regular
- \+ *theorem* cardinal.sup_lt_ord_lift_of_is_regular
- \+/\- *theorem* cardinal.sup_lt_ord_of_is_regular
- \+ *theorem* ordinal.blsub_lt_ord
- \+ *theorem* ordinal.blsub_lt_ord_lift
- \+ *theorem* ordinal.bsup_lt_ord
- \+ *theorem* ordinal.bsup_lt_ord_lift
- \+ *theorem* ordinal.cof_blsub_le_lift
- \+/\- *theorem* ordinal.cof_bsup_le
- \+/\- *theorem* ordinal.cof_bsup_le_lift
- \+ *theorem* ordinal.cof_lsub_le_lift
- \+/\- *theorem* ordinal.cof_sup_le
- \+/\- *theorem* ordinal.cof_sup_le_lift
- \+ *theorem* ordinal.lsub_lt_ord
- \+ *theorem* ordinal.lsub_lt_ord_lift
- \+/\- *theorem* ordinal.sup_lt
- \+ *theorem* ordinal.sup_lt_lift
- \+/\- *theorem* ordinal.sup_lt_ord
- \+ *theorem* ordinal.sup_lt_ord_lift



## [2022-04-10 01:48:17](https://github.com/leanprover-community/mathlib/commit/c2d870e)
feat(set_theory/{ordinal_arithmetic, fixed_points}): Next fixed point of families ([#12200](https://github.com/leanprover-community/mathlib/pull/12200))
We define the next common fixed point of a family of normal ordinal functions. We prove these fixed points to be unbounded, and that their enumerator functions are normal.
#### Estimated changes
Added src/set_theory/fixed_points.lean
- \+ *theorem* ordinal.apply_le_nfp_family
- \+ *theorem* ordinal.apply_lt_nfp_bfamily
- \+ *theorem* ordinal.apply_lt_nfp_family
- \+ *theorem* ordinal.apply_lt_nfp_family_iff
- \+ *def* ordinal.deriv_bfamily
- \+ *theorem* ordinal.deriv_bfamily_eq_deriv_family
- \+ *theorem* ordinal.deriv_bfamily_eq_enum_ord
- \+ *theorem* ordinal.deriv_bfamily_fp
- \+ *theorem* ordinal.deriv_bfamily_is_normal
- \+ *def* ordinal.deriv_family
- \+ *theorem* ordinal.deriv_family_eq_enum_ord
- \+ *theorem* ordinal.deriv_family_fp
- \+ *theorem* ordinal.deriv_family_is_normal
- \+ *theorem* ordinal.deriv_family_limit
- \+ *theorem* ordinal.deriv_family_succ
- \+ *theorem* ordinal.deriv_family_zero
- \+ *theorem* ordinal.foldr_le_nfp_bfamily
- \+ *theorem* ordinal.foldr_le_nfp_family
- \+ *theorem* ordinal.fp_bfamily_unbounded
- \+ *theorem* ordinal.fp_family_unbounded
- \+ *theorem* ordinal.fp_iff_deriv_bfamily
- \+ *theorem* ordinal.fp_iff_deriv_family
- \+ *theorem* ordinal.le_iff_deriv_bfamily
- \+ *theorem* ordinal.le_iff_deriv_family
- \+ *theorem* ordinal.le_nfp_bfamily
- \+ *theorem* ordinal.lt_nfp_bfamily
- \+ *theorem* ordinal.lt_nfp_family
- \+ *def* ordinal.nfp_bfamily
- \+ *theorem* ordinal.nfp_bfamily_eq_nfp_family
- \+ *theorem* ordinal.nfp_bfamily_eq_self
- \+ *theorem* ordinal.nfp_bfamily_fp
- \+ *theorem* ordinal.nfp_bfamily_le
- \+ *theorem* ordinal.nfp_bfamily_le_apply
- \+ *theorem* ordinal.nfp_bfamily_le_fp
- \+ *theorem* ordinal.nfp_bfamily_le_iff
- \+ *theorem* ordinal.nfp_bfamily_monotone
- \+ *def* ordinal.nfp_family
- \+ *theorem* ordinal.nfp_family_eq_self
- \+ *theorem* ordinal.nfp_family_eq_sup
- \+ *theorem* ordinal.nfp_family_fp
- \+ *theorem* ordinal.nfp_family_le
- \+ *theorem* ordinal.nfp_family_le_apply
- \+ *theorem* ordinal.nfp_family_le_fp
- \+ *theorem* ordinal.nfp_family_le_iff
- \+ *theorem* ordinal.nfp_family_monotone
- \+ *theorem* ordinal.self_le_nfp_bfamily
- \+ *theorem* ordinal.self_le_nfp_family



## [2022-04-10 01:48:16](https://github.com/leanprover-community/mathlib/commit/b2c707c)
feat(group_theory): use generic `subobject_class` lemmas ([#11758](https://github.com/leanprover-community/mathlib/pull/11758))
This subobject class refactor PR follows up from [#11750](https://github.com/leanprover-community/mathlib/pull/11750) by moving the `{zero,one,add,mul,...}_mem_class` lemmas to the root namespace and marking the previous `sub{monoid,group,module,algebra,...}.{zero,one,add,mul,...}_mem` lemmas as `protected`. This is the second part of [#11545](https://github.com/leanprover-community/mathlib/pull/11545) to be split off.
I made the subobject parameter to the `_mem` lemmas implicit if it appears in the hypotheses, e.g.
```lean
lemma mul_mem {S M : Type*} [monoid M] [set_like S M] [submonoid_class S M]
  {s : S} {x y : M} (hx : x ∈ s) (hy : y ∈ s) : x * y ∈ s
```
instead of having `(s : S)` explicit. The generic `_mem` lemmas are not namespaced, so there is no dot notation that requires `s` to be explicit. Also there were already a couple of instances for the same operator where `s` was implicit and others where `s` was explicit, so some change was needed.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/algebra/operations.lean


Modified src/algebra/algebra/subalgebra/basic.lean
- \- *theorem* subalgebra.add_mem
- \- *lemma* subalgebra.coe_add
- \- *lemma* subalgebra.coe_eq_one
- \- *lemma* subalgebra.coe_eq_zero
- \- *theorem* subalgebra.coe_int_mem
- \- *lemma* subalgebra.coe_mul
- \- *theorem* subalgebra.coe_nat_mem
- \- *lemma* subalgebra.coe_neg
- \- *lemma* subalgebra.coe_one
- \- *lemma* subalgebra.coe_pow
- \- *lemma* subalgebra.coe_sub
- \- *lemma* subalgebra.coe_zero
- \- *theorem* subalgebra.list_prod_mem
- \- *theorem* subalgebra.list_sum_mem
- \- *theorem* subalgebra.mul_mem
- \- *theorem* subalgebra.multiset_prod_mem
- \- *theorem* subalgebra.multiset_sum_mem
- \- *theorem* subalgebra.neg_mem
- \- *theorem* subalgebra.nsmul_mem
- \- *theorem* subalgebra.one_mem
- \- *theorem* subalgebra.pow_mem
- \- *theorem* subalgebra.prod_mem
- \- *theorem* subalgebra.sub_mem
- \- *theorem* subalgebra.sum_mem
- \- *theorem* subalgebra.zero_mem
- \- *theorem* subalgebra.zsmul_mem

Modified src/algebra/algebra/subalgebra/pointwise.lean


Modified src/algebra/algebra/tower.lean


Modified src/algebra/direct_sum/internal.lean


Modified src/algebra/lie/cartan_subalgebra.lean


Modified src/algebra/lie/subalgebra.lean
- \- *lemma* lie_subalgebra.add_mem
- \- *lemma* lie_subalgebra.neg_mem_iff
- \- *lemma* lie_subalgebra.sub_mem
- \- *lemma* lie_subalgebra.zero_mem

Modified src/algebra/lie/submodule.lean
- \- *lemma* lie_submodule.zero_mem

Modified src/algebra/module/submodule.lean
- \- *lemma* submodule.add_mem
- \- *lemma* submodule.add_mem_iff_left
- \- *lemma* submodule.add_mem_iff_right
- \- *lemma* submodule.coe_neg
- \- *lemma* submodule.coe_sub
- \- *lemma* submodule.neg_mem
- \- *lemma* submodule.neg_mem_iff
- \- *lemma* submodule.sub_mem
- \- *lemma* submodule.sum_mem
- \- *lemma* submodule.zero_mem

Modified src/algebra/module/submodule_lattice.lean


Modified src/algebra/star/unitary.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/inner_product_space/l2_space.lean


Modified src/data/dfinsupp/basic.lean
- \- *lemma* add_submonoid.dfinsupp_sum_add_hom_mem
- \+ *lemma* dfinsupp_prod_mem
- \+ *lemma* dfinsupp_sum_add_hom_mem
- \- *lemma* submonoid.dfinsupp_prod_mem

Modified src/data/finsupp/basic.lean
- \- *lemma* submonoid.finsupp_prod_mem
- \+ *lemma* submonoid_class.finsupp_prod_mem

Modified src/data/set/pointwise.lean


Modified src/deprecated/subgroup.lean


Modified src/field_theory/abel_ruffini.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/field_theory/intermediate_field.lean
- \- *theorem* intermediate_field.add_mem
- \- *lemma* intermediate_field.coe_add
- \- *lemma* intermediate_field.coe_int_mem
- \- *lemma* intermediate_field.coe_inv
- \- *lemma* intermediate_field.coe_mul
- \- *lemma* intermediate_field.coe_neg
- \- *lemma* intermediate_field.coe_one
- \- *lemma* intermediate_field.coe_pow
- \- *lemma* intermediate_field.coe_zero
- \- *theorem* intermediate_field.div_mem
- \- *theorem* intermediate_field.inv_mem
- \- *lemma* intermediate_field.list_prod_mem
- \- *lemma* intermediate_field.list_sum_mem
- \- *theorem* intermediate_field.mul_mem
- \- *lemma* intermediate_field.multiset_prod_mem
- \- *lemma* intermediate_field.multiset_sum_mem
- \- *theorem* intermediate_field.neg_mem
- \- *theorem* intermediate_field.one_mem
- \- *lemma* intermediate_field.pow_mem
- \- *lemma* intermediate_field.prod_mem
- \- *theorem* intermediate_field.sub_mem
- \- *lemma* intermediate_field.sum_mem
- \- *theorem* intermediate_field.zero_mem
- \- *lemma* intermediate_field.zsmul_mem

Modified src/field_theory/primitive_element.lean


Modified src/field_theory/subfield.lean
- \- *theorem* subfield.add_mem
- \- *lemma* subfield.coe_int_mem
- \- *theorem* subfield.div_mem
- \- *theorem* subfield.inv_mem
- \- *lemma* subfield.list_prod_mem
- \- *lemma* subfield.list_sum_mem
- \- *theorem* subfield.mul_mem
- \- *lemma* subfield.multiset_prod_mem
- \- *lemma* subfield.multiset_sum_mem
- \- *theorem* subfield.neg_mem
- \- *theorem* subfield.one_mem
- \- *lemma* subfield.pow_mem
- \- *lemma* subfield.prod_mem
- \- *theorem* subfield.sub_mem
- \- *lemma* subfield.sum_mem
- \- *theorem* subfield.zero_mem
- \- *lemma* subfield.zsmul_mem

Modified src/group_theory/coset.lean


Modified src/group_theory/nilpotent.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/cycle_type.lean


Modified src/group_theory/specific_groups/alternating.lean


Modified src/group_theory/subgroup/basic.lean
- \+ *theorem* div_mem
- \+ *lemma* div_mem_comm_iff
- \+ *lemma* exists_inv_mem_iff_exists_mem
- \+ *theorem* inv_coe_set
- \+ *theorem* inv_mem_iff
- \+ *lemma* mul_mem_cancel_left
- \+ *lemma* mul_mem_cancel_right
- \- *theorem* subgroup.div_mem
- \- *lemma* subgroup.div_mem_comm_iff
- \- *lemma* subgroup.exists_inv_mem_iff_exists_mem
- \- *theorem* subgroup.inv_coe_set
- \- *theorem* subgroup.inv_mem
- \- *theorem* subgroup.inv_mem_iff
- \- *lemma* subgroup.list_prod_mem
- \- *theorem* subgroup.mul_mem
- \- *lemma* subgroup.mul_mem_cancel_left
- \- *lemma* subgroup.mul_mem_cancel_right
- \- *lemma* subgroup.multiset_prod_mem
- \- *theorem* subgroup.one_mem
- \- *lemma* subgroup.pow_mem
- \- *lemma* subgroup.prod_mem
- \- *lemma* subgroup.zpow_mem
- \- *theorem* subgroup_class.div_mem
- \- *lemma* subgroup_class.div_mem_comm_iff
- \- *lemma* subgroup_class.exists_inv_mem_iff_exists_mem
- \- *theorem* subgroup_class.inv_coe_set
- \- *theorem* subgroup_class.inv_mem_iff
- \- *lemma* subgroup_class.mul_mem_cancel_left
- \- *lemma* subgroup_class.mul_mem_cancel_right
- \- *lemma* subgroup_class.zpow_mem
- \+ *lemma* zpow_mem

Modified src/group_theory/submonoid/basic.lean
- \- *theorem* submonoid.mul_mem
- \- *theorem* submonoid.one_mem

Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* list_prod_mem
- \+ *lemma* multiset_prod_mem
- \+ *lemma* prod_mem
- \- *lemma* submonoid_class.list_prod_mem
- \- *lemma* submonoid_class.multiset_prod_mem
- \- *lemma* submonoid_class.prod_mem

Modified src/group_theory/submonoid/operations.lean
- \- *lemma* submonoid.pow_mem

Modified src/group_theory/submonoid/pointwise.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/dfinsupp.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/finsupp.lean
- \- *lemma* submodule.finsupp_sum_mem

Modified src/linear_algebra/linear_independent.lean
- \+/\- *def* linear_independent.total_equiv

Modified src/linear_algebra/linear_pmap.lean


Modified src/linear_algebra/prod.lean


Modified src/linear_algebra/quotient.lean


Modified src/linear_algebra/span.lean


Modified src/linear_algebra/std_basis.lean


Modified src/ring_theory/adjoin/fg.lean


Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/graded_algebra/homogeneous_localization.lean


Modified src/ring_theory/ideal/basic.lean
- \- *lemma* ideal.add_mem_iff_left
- \- *lemma* ideal.add_mem_iff_right
- \- *lemma* ideal.neg_mem_iff

Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/jacobson_ideal.lean


Modified src/ring_theory/local_properties.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial/scale_roots.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/subring/basic.lean
- \+ *lemma* coe_int_mem
- \- *theorem* subring.add_mem
- \- *lemma* subring.coe_int_mem
- \+/\- *lemma* subring.coe_pow
- \- *lemma* subring.list_prod_mem
- \- *lemma* subring.list_sum_mem
- \- *theorem* subring.mul_mem
- \- *lemma* subring.multiset_prod_mem
- \- *lemma* subring.multiset_sum_mem
- \- *theorem* subring.neg_mem
- \- *theorem* subring.one_mem
- \- *lemma* subring.pow_mem
- \- *lemma* subring.prod_mem
- \- *theorem* subring.sub_mem
- \- *lemma* subring.sum_mem
- \- *theorem* subring.zero_mem
- \- *lemma* subring.zsmul_mem
- \- *lemma* subring_class.coe_int_mem

Modified src/ring_theory/subsemiring/basic.lean
- \+ *lemma* coe_nat_mem
- \- *theorem* subsemiring.add_mem
- \- *lemma* subsemiring.coe_nat_mem
- \- *lemma* subsemiring.list_sum_mem
- \- *theorem* subsemiring.mul_mem
- \- *lemma* subsemiring.multiset_prod_mem
- \- *lemma* subsemiring.multiset_sum_mem
- \- *lemma* subsemiring.nsmul_mem
- \- *theorem* subsemiring.one_mem
- \- *lemma* subsemiring.pow_mem
- \- *lemma* subsemiring.prod_mem
- \- *lemma* subsemiring.sum_mem
- \- *theorem* subsemiring.zero_mem
- \- *lemma* subsemiring_class.coe_nat_mem



## [2022-04-10 01:48:15](https://github.com/leanprover-community/mathlib/commit/d133874)
feat(representation_theory/basic): basics of group representation theory ([#11207](https://github.com/leanprover-community/mathlib/pull/11207))
Some basic lemmas about group representations and some theory regarding the subspace of fixed points of a representation.
#### Estimated changes
Modified src/algebra/monoid_algebra/basic.lean
- \+ *lemma* monoid_algebra.smul_of
- \+ *def* monoid_algebra.submodule_of_smul_mem

Added src/representation_theory/basic.lean
- \+ *lemma* representation.as_algebra_hom_def
- \+ *lemma* representation.as_algebra_hom_single
- \+ *def* representation.as_group_hom
- \+ *lemma* representation.as_module_apply
- \+ *theorem* representation.char_conj
- \+ *theorem* representation.char_one
- \+ *lemma* representation.of_smul

Added src/representation_theory/invariants.lean
- \+ *lemma* representation.average_def
- \+ *lemma* representation.invariants'_carrier
- \+ *def* representation.invariants
- \+ *lemma* representation.invariants_eq_inter
- \+ *lemma* representation.mem_invariants
- \+ *theorem* representation.mul_average_left
- \+ *theorem* representation.mul_average_right
- \+ *theorem* representation.smul_average_id
- \+ *theorem* representation.smul_average_invariant



## [2022-04-10 01:48:14](https://github.com/leanprover-community/mathlib/commit/3fe5c93)
feat(algebra/ring/boolean_ring): Turning a Boolean algebra into a Boolean ring ([#6476](https://github.com/leanprover-community/mathlib/pull/6476))
Define `as_boolring`, a type synonym to turn a Boolean algebra into a Boolean ring and show that `as_boolring` and `as_boolalg` are "inverse" to each other.
#### Estimated changes
Modified src/algebra/category/BoolRing.lean


Modified src/algebra/ring/boolean_ring.lean
- \+ *def* as_boolring
- \+ *def* boolean_algebra.to_boolean_ring
- \+ *lemma* bounded_lattice_hom.as_boolring_comp
- \+ *lemma* bounded_lattice_hom.as_boolring_id
- \+ *def* generalized_boolean_algebra.to_non_unital_ring
- \+ *lemma* of_boolalg_compl
- \+ *lemma* of_boolalg_mul_of_boolalg_eq_left_iff
- \+ *lemma* of_boolalg_sdiff
- \+ *lemma* of_boolalg_symm_diff
- \+ *def* of_boolring
- \+ *lemma* of_boolring_add
- \+ *lemma* of_boolring_inj
- \+ *lemma* of_boolring_le_of_boolring_iff
- \+ *lemma* of_boolring_mul
- \+ *lemma* of_boolring_neg
- \+ *lemma* of_boolring_one
- \+ *lemma* of_boolring_sub
- \+ *lemma* of_boolring_symm_eq
- \+ *lemma* of_boolring_to_boolring
- \+ *lemma* of_boolring_zero
- \+ *def* order_iso.as_boolalg_as_boolring
- \+ *def* ring_equiv.as_boolring_as_boolalg
- \+ *lemma* to_boolalg_add
- \+/\- *lemma* to_boolalg_add_add_mul
- \+ *def* to_boolring
- \+ *lemma* to_boolring_bot
- \+ *lemma* to_boolring_inf
- \+ *lemma* to_boolring_inj
- \+ *lemma* to_boolring_of_boolring
- \+ *lemma* to_boolring_symm_diff
- \+ *lemma* to_boolring_symm_eq
- \+ *lemma* to_boolring_top

Modified src/order/hom/lattice.lean
- \+ *lemma* disjoint.map
- \+ *lemma* is_compl.map
- \+ *lemma* map_compl
- \+ *lemma* map_sdiff
- \+ *lemma* map_symm_diff



## [2022-04-10 01:48:13](https://github.com/leanprover-community/mathlib/commit/9495b8c)
feat(data/set/intervals/with_bot_top): lemmas about `I??` and `with_top/bot` ([#4273](https://github.com/leanprover-community/mathlib/pull/4273))
Prove theorems about (pre)images of intervals under `coe : α → with_top α` and `coe : α → with_bot α`.
#### Estimated changes
Added src/data/set/intervals/with_bot_top.lean
- \+ *lemma* with_bot.image_coe_Icc
- \+ *lemma* with_bot.image_coe_Ici
- \+ *lemma* with_bot.image_coe_Ico
- \+ *lemma* with_bot.image_coe_Iic
- \+ *lemma* with_bot.image_coe_Iio
- \+ *lemma* with_bot.image_coe_Ioc
- \+ *lemma* with_bot.image_coe_Ioi
- \+ *lemma* with_bot.image_coe_Ioo
- \+ *lemma* with_bot.preimage_coe_Icc
- \+ *lemma* with_bot.preimage_coe_Ici
- \+ *lemma* with_bot.preimage_coe_Ico
- \+ *lemma* with_bot.preimage_coe_Iic
- \+ *lemma* with_bot.preimage_coe_Iio
- \+ *lemma* with_bot.preimage_coe_Ioc
- \+ *lemma* with_bot.preimage_coe_Ioc_bot
- \+ *lemma* with_bot.preimage_coe_Ioi
- \+ *lemma* with_bot.preimage_coe_Ioi_bot
- \+ *lemma* with_bot.preimage_coe_Ioo
- \+ *lemma* with_bot.preimage_coe_Ioo_bot
- \+ *lemma* with_bot.preimage_coe_bot
- \+ *lemma* with_bot.range_coe
- \+ *lemma* with_top.image_coe_Icc
- \+ *lemma* with_top.image_coe_Ici
- \+ *lemma* with_top.image_coe_Ico
- \+ *lemma* with_top.image_coe_Iic
- \+ *lemma* with_top.image_coe_Iio
- \+ *lemma* with_top.image_coe_Ioc
- \+ *lemma* with_top.image_coe_Ioi
- \+ *lemma* with_top.image_coe_Ioo
- \+ *lemma* with_top.preimage_coe_Icc
- \+ *lemma* with_top.preimage_coe_Ici
- \+ *lemma* with_top.preimage_coe_Ico
- \+ *lemma* with_top.preimage_coe_Ico_top
- \+ *lemma* with_top.preimage_coe_Iic
- \+ *lemma* with_top.preimage_coe_Iio
- \+ *lemma* with_top.preimage_coe_Iio_top
- \+ *lemma* with_top.preimage_coe_Ioc
- \+ *lemma* with_top.preimage_coe_Ioi
- \+ *lemma* with_top.preimage_coe_Ioo
- \+ *lemma* with_top.preimage_coe_Ioo_top
- \+ *lemma* with_top.preimage_coe_top
- \+ *lemma* with_top.range_coe



## [2022-04-09 23:54:02](https://github.com/leanprover-community/mathlib/commit/e4f93e6)
feat(group_theory/solvable): Golf some proofs ([#13271](https://github.com/leanprover-community/mathlib/pull/13271))
This PR uses `solvable_of_ker_le_range` to golf some proofs.
#### Estimated changes
Modified src/group_theory/solvable.lean




## [2022-04-09 23:54:01](https://github.com/leanprover-community/mathlib/commit/b7f7c4a)
feat(combinatorics/simple_graph/clique): Cliques ([#12982](https://github.com/leanprover-community/mathlib/pull/12982))
Define cliques.
#### Estimated changes
Added src/combinatorics/simple_graph/clique.lean
- \+ *lemma* simple_graph.is_clique.mono
- \+ *lemma* simple_graph.is_clique.subset
- \+ *lemma* simple_graph.is_clique_iff
- \+ *lemma* simple_graph.is_n_clique.mono
- \+ *lemma* simple_graph.is_n_clique_iff

Modified src/data/finset/pairwise.lean




## [2022-04-09 22:07:41](https://github.com/leanprover-community/mathlib/commit/e690875)
chore(ring_theory/roots_of_unity): generalise ([#13261](https://github.com/leanprover-community/mathlib/pull/13261))
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+/\- *lemma* is_primitive_root.eq_neg_one_of_two_right
- \+/\- *lemma* is_primitive_root.mem_roots_of_unity
- \+/\- *lemma* is_primitive_root.pow
- \+/\- *lemma* roots_of_unity.coe_pow



## [2022-04-09 22:07:40](https://github.com/leanprover-community/mathlib/commit/3879621)
feat(combinatorics/additive/salem_spencer): The sphere does not contain arithmetic progressions ([#13259](https://github.com/leanprover-community/mathlib/pull/13259))
Prove that the frontier of a strictly convex closed set is Salem-Spencer. For this we need
* simple lemmas about `same_ray`. This involves renaming `same_ray.exists_right_eq_smul`/`same_ray.exists_left_eq_smul` to `same_ray.exists_nonneg_left`/`same_ray.exists_nonneg_right`.
* that the norm in a real normed space is injective on rays.
* that the midpoint of two points of equal norm has smaller norm, in a strictly convex space
#### Estimated changes
Modified src/analysis/convex/strict.lean


Modified src/analysis/convex/strict_convex_space.lean
- \+ *lemma* norm_midpoint_lt_iff
- \+ *lemma* not_same_ray_iff_norm_add_lt

Modified src/analysis/normed_space/ray.lean
- \+ *lemma* norm_inj_on_ray_left
- \+ *lemma* norm_inj_on_ray_right
- \+ *lemma* not_same_ray_iff_of_norm_eq
- \+/\- *lemma* same_ray_iff_inv_norm_smul_eq
- \+/\- *lemma* same_ray_iff_inv_norm_smul_eq_of_ne
- \+/\- *lemma* same_ray_iff_norm_smul_eq
- \+ *lemma* same_ray_iff_of_norm_eq

Modified src/combinatorics/additive/salem_spencer.lean
- \+ *lemma* add_salem_spencer_frontier
- \+ *lemma* add_salem_spencer_sphere

Modified src/linear_algebra/ray.lean
- \- *lemma* same_ray.exists_left_eq_smul
- \+ *lemma* same_ray.exists_nonneg_left
- \+ *lemma* same_ray.exists_nonneg_right
- \+ *lemma* same_ray.exists_pos_left
- \+ *lemma* same_ray.exists_pos_right
- \- *lemma* same_ray.exists_right_eq_smul

Modified src/topology/basic.lean
- \+ *lemma* is_closed.frontier_subset



## [2022-04-09 22:07:39](https://github.com/leanprover-community/mathlib/commit/b3a0f85)
feat(group_theory/coset): Fintype instance for quotient by the right relation ([#13257](https://github.com/leanprover-community/mathlib/pull/13257))
This PR adds a fintype instance for the quotient by the right relation.
#### Estimated changes
Modified src/group_theory/coset.lean
- \+ *lemma* quotient_group.card_quotient_right_rel



## [2022-04-09 22:07:38](https://github.com/leanprover-community/mathlib/commit/e3a8ef1)
feat(algebra/algebra/*): generalise ([#13252](https://github.com/leanprover-community/mathlib/pull/13252))
Some generalisations straight from Alex's generalisation linter, with some care about how to place them. Some `algebra` lemmas are weakened to semirings, allowing us to talk about ℕ-algebras much more easily.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+/\- *lemma* algebra.mem_algebra_map_submonoid_of_mem
- \+/\- *lemma* ring_hom.map_rat_algebra_map

Modified src/algebra/algebra/operations.lean
- \+/\- *lemma* submodule.mem_span_mul_finite_of_mem_span_mul

Modified src/algebra/algebra/spectrum.lean
- \- *lemma* is_unit.smul_sub_iff_sub_inv_smul
- \+/\- *lemma* spectrum.exists_mem_of_not_is_unit_aeval_prod

Modified src/algebra/algebra/subalgebra/basic.lean


Modified src/algebra/algebra/tower.lean


Modified src/algebra/algebra/unitization.lean
- \+/\- *lemma* unitization.coe_add
- \+/\- *lemma* unitization.coe_mul
- \+/\- *lemma* unitization.coe_mul_inl
- \+/\- *lemma* unitization.inl_mul_coe

Modified src/group_theory/group_action/group.lean
- \+ *lemma* is_unit.smul_sub_iff_sub_inv_smul
- \+/\- *lemma* is_unit_smul_iff



## [2022-04-09 22:07:37](https://github.com/leanprover-community/mathlib/commit/1480161)
feat(group_theory/group_action/basic): Left multiplication satisfies the `quotient_action` axiom ([#13249](https://github.com/leanprover-community/mathlib/pull/13249))
This PR adds an instance `quotient_action α H`, meaning that left multiplication satisfies the `quotient_action` axiom.
#### Estimated changes
Modified src/group_theory/group_action/basic.lean




## [2022-04-09 22:07:36](https://github.com/leanprover-community/mathlib/commit/22b7d21)
feat(analysis/normed*): if `f → 0` and `g` is bounded, then `f * g → 0` ([#13248](https://github.com/leanprover-community/mathlib/pull/13248))
Also drop `is_bounded_under_of_tendsto`: it's just `h.norm.is_bounded_under_le`.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/normed/group/basic.lean
- \+ *lemma* filter.tendsto.op_zero_is_bounded_under_le'
- \+ *lemma* filter.tendsto.op_zero_is_bounded_under_le
- \- *lemma* is_bounded_under_of_tendsto

Modified src/analysis/normed/normed_field.lean
- \+ *lemma* filter.is_bounded_under_le.mul_tendsto_zero
- \+ *lemma* filter.tendsto.zero_mul_is_bounded_under_le

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* filter.is_bounded_under.smul_tendsto_zero
- \+ *lemma* filter.tendsto.zero_smul_is_bounded_under_le



## [2022-04-09 22:07:35](https://github.com/leanprover-community/mathlib/commit/4c4e5e8)
feat(analysis/locally_convex): every totally bounded set is von Neumann bounded ([#13204](https://github.com/leanprover-community/mathlib/pull/13204))
Add one lemma and some cleanups of previous PR.
#### Estimated changes
Modified src/analysis/locally_convex/balanced_core_hull.lean


Modified src/analysis/locally_convex/basic.lean
- \+/\- *lemma* absorbs.add
- \+/\- *lemma* absorbs_empty

Modified src/analysis/locally_convex/bounded.lean
- \+ *lemma* totally_bounded.is_vonN_bounded



## [2022-04-09 19:44:54](https://github.com/leanprover-community/mathlib/commit/cc65716)
refactor(analysis/complex): replace `diff_on_int_cont` with `diff_cont_on_cl` ([#13148](https://github.com/leanprover-community/mathlib/pull/13148))
Use "differentiable on a set and continuous on its closure" instead of "continuous on a set and differentiable on its interior".
There are a few reasons to prefer the latter:
* it has better "composition" lemma;
* it allows us to talk about functions that are, e.g., differentiable on `{z : ℂ | abs z < 1 ∧ (re z < 0 ∨ im z ≠ 0)}` and continuous on the closed unit disk.
Also generalize `eq_on_of_eq_on_frontier` from a compact set to a bounded set (so that it works, e.g., for the unit ball in a Banach space).
This PR does not move the file `diff_on_int_cont` to make the diff more readable; the file will be moved in another PR.
#### Estimated changes
Modified src/analysis/calculus/diff_on_int_cont.lean
- \+ *lemma* diff_cont_on_cl.add
- \+ *lemma* diff_cont_on_cl.add_const
- \+ *lemma* diff_cont_on_cl.comp
- \+ *lemma* diff_cont_on_cl.const_add
- \+ *lemma* diff_cont_on_cl.const_smul
- \+ *lemma* diff_cont_on_cl.const_sub
- \+ *lemma* diff_cont_on_cl.continuous_on_ball
- \+ *lemma* diff_cont_on_cl.differentiable_at'
- \+ *lemma* diff_cont_on_cl.inv
- \+ *lemma* diff_cont_on_cl.mk_ball
- \+ *lemma* diff_cont_on_cl.neg
- \+ *lemma* diff_cont_on_cl.smul
- \+ *lemma* diff_cont_on_cl.smul_const
- \+ *lemma* diff_cont_on_cl.sub
- \+ *lemma* diff_cont_on_cl.sub_const
- \+ *lemma* diff_cont_on_cl_const
- \+ *lemma* diff_cont_on_cl_univ
- \- *lemma* diff_on_int_cont.add
- \- *lemma* diff_on_int_cont.add_const
- \- *lemma* diff_on_int_cont.comp
- \- *lemma* diff_on_int_cont.const_add
- \- *lemma* diff_on_int_cont.const_smul
- \- *lemma* diff_on_int_cont.const_sub
- \- *lemma* diff_on_int_cont.differentiable_at'
- \- *lemma* diff_on_int_cont.differentiable_on_ball
- \- *lemma* diff_on_int_cont.inv
- \- *lemma* diff_on_int_cont.mk_ball
- \- *lemma* diff_on_int_cont.neg
- \- *lemma* diff_on_int_cont.smul
- \- *lemma* diff_on_int_cont.smul_const
- \- *lemma* diff_on_int_cont.sub
- \- *lemma* diff_on_int_cont.sub_const
- \- *lemma* diff_on_int_cont_const
- \- *lemma* diff_on_int_cont_open
- \- *lemma* diff_on_int_cont_univ
- \+ *lemma* differentiable.comp_diff_cont_on_cl
- \- *lemma* differentiable.comp_diff_on_int_cont
- \+ *lemma* differentiable.diff_cont_on_cl
- \- *lemma* differentiable.diff_on_int_cont
- \- *lemma* differentiable_on.comp_diff_on_int_cont
- \+ *lemma* differentiable_on.diff_cont_on_cl
- \- *lemma* differentiable_on.diff_on_int_cont
- \+ *lemma* is_closed.diff_cont_on_cl_iff

Modified src/analysis/complex/abs_max.lean
- \+ *lemma* complex.eq_on_closure_of_eq_on_frontier
- \+/\- *lemma* complex.eq_on_of_eq_on_frontier
- \+/\- *lemma* complex.exists_mem_frontier_is_max_on_norm
- \+/\- *lemma* complex.norm_le_of_forall_mem_frontier_norm_le
- \+/\- *lemma* complex.norm_max_aux₂

Modified src/analysis/complex/cauchy_integral.lean
- \+ *lemma* diff_cont_on_cl.circle_integral_sub_inv_smul
- \+ *lemma* diff_cont_on_cl.has_fpower_series_on_ball
- \- *lemma* diff_on_int_cont.circle_integral_sub_inv_smul
- \- *lemma* diff_on_int_cont.has_fpower_series_on_ball

Modified src/analysis/complex/liouville.lean
- \+/\- *lemma* complex.deriv_eq_smul_circle_integral

Modified src/analysis/complex/schwarz.lean


Modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* antilipschitz_with_line_map

Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* metric.ball_inf_dist_compl_subset
- \+ *lemma* metric.ball_inf_dist_subset_compl



## [2022-04-09 19:44:52](https://github.com/leanprover-community/mathlib/commit/57f382a)
feat(order/bounds): Boundedness of monotone/antitone functions ([#13079](https://github.com/leanprover-community/mathlib/pull/13079))
#### Estimated changes
Modified src/order/bounds.lean
- \+ *lemma* antitone_on.image_lower_bounds_subset_upper_bounds_image
- \+ *lemma* antitone_on.image_upper_bounds_subset_lower_bounds_image
- \+ *lemma* antitone_on.is_lub_image_le
- \+ *lemma* antitone_on.le_is_glb_image
- \+ *lemma* antitone_on.map_bdd_above
- \+ *lemma* antitone_on.map_bdd_below
- \+ *lemma* antitone_on.map_is_greatest
- \+ *lemma* antitone_on.map_is_least
- \+ *lemma* antitone_on.mem_lower_bounds_image
- \+ *lemma* antitone_on.mem_upper_bounds_image
- \+ *lemma* monotone_on.image_lower_bounds_subset_lower_bounds_image
- \+ *lemma* monotone_on.image_upper_bounds_subset_upper_bounds_image
- \+ *lemma* monotone_on.is_lub_image_le
- \+ *lemma* monotone_on.le_is_glb_image
- \+ *lemma* monotone_on.map_bdd_above
- \+ *lemma* monotone_on.map_bdd_below
- \+ *lemma* monotone_on.map_is_greatest
- \+ *lemma* monotone_on.map_is_least
- \+ *lemma* monotone_on.mem_lower_bounds_image
- \+ *lemma* monotone_on.mem_upper_bounds_image



## [2022-04-09 19:44:50](https://github.com/leanprover-community/mathlib/commit/0dde2cb)
feat(data/list/chain): Lemma for `chain r a (list.range n.succ)` ([#12990](https://github.com/leanprover-community/mathlib/pull/12990))
#### Estimated changes
Modified src/data/list/chain.lean
- \+ *theorem* list.chain'_append_cons_cons

Modified src/data/list/range.lean
- \+ *theorem* list.chain'_range_succ
- \+ *theorem* list.chain_range_succ

Modified src/data/nat/basic.lean
- \+ *theorem* nat.exists_lt_succ
- \+ *theorem* nat.forall_lt_succ



## [2022-04-09 17:28:10](https://github.com/leanprover-community/mathlib/commit/bc140d2)
feat(data/polynomial/degree/lemmas): add some lemmas and rename some lemmas ([#13235](https://github.com/leanprover-community/mathlib/pull/13235))
rename `nat_degree_mul_C_eq_of_no_zero_divisors` to `nat_degree_mul_C`
rename `nat_degree_C_mul_eq_of_no_zero_divisors` to `nat_degree_C_mul`
#### Estimated changes
Modified src/data/polynomial/degree/lemmas.lean
- \+ *lemma* polynomial.degree_C_mul
- \+ *lemma* polynomial.degree_mul_C
- \+ *lemma* polynomial.nat_degree_C_mul
- \- *lemma* polynomial.nat_degree_C_mul_eq_of_no_zero_divisors
- \+ *lemma* polynomial.nat_degree_mul_C
- \- *lemma* polynomial.nat_degree_mul_C_eq_of_no_zero_divisors



## [2022-04-09 17:28:09](https://github.com/leanprover-community/mathlib/commit/f8467aa)
feat(data/polynomial/eval): add some lemmas for `eval₂` ([#13234](https://github.com/leanprover-community/mathlib/pull/13234))
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+/\- *lemma* polynomial.eval₂_comp
- \+ *lemma* polynomial.eval₂_finset_prod
- \+/\- *lemma* polynomial.eval₂_hom
- \+ *lemma* polynomial.eval₂_list_prod
- \+ *lemma* polynomial.eval₂_list_sum
- \+ *lemma* polynomial.eval₂_multiset_prod
- \+ *lemma* polynomial.eval₂_multiset_sum



## [2022-04-09 17:28:08](https://github.com/leanprover-community/mathlib/commit/25d28c8)
feat(group_theory/schreier): Add version of Schreier's lemma ([#13231](https://github.com/leanprover-community/mathlib/pull/13231))
This PR adds a version of Schreier's lemma of the form `closure (_ : set H) = ⊤`, as opposed to `closure (_ : set G) = H`. This is closer to saying that `H` is finitely generated.
I also fiddled with the names a bit.
#### Estimated changes
Modified docs/overview.yaml


Modified src/group_theory/schreier.lean
- \- *lemma* subgroup.closure_mul_eq
- \- *lemma* subgroup.closure_mul_eq_top
- \+ *lemma* subgroup.closure_mul_image_eq
- \+ *lemma* subgroup.closure_mul_image_eq_top
- \+ *lemma* subgroup.closure_mul_image_mul_eq_top



## [2022-04-09 17:28:06](https://github.com/leanprover-community/mathlib/commit/d831478)
feat(computability/encoding): Bounds on cardinality from an encoding ([#13224](https://github.com/leanprover-community/mathlib/pull/13224))
Generalizes universe variables for `computability.encoding`
Uses a `computability.encoding` to bound the cardinality of a type
#### Estimated changes
Modified src/computability/encoding.lean
- \+ *lemma* computability.encoding.card_le_card_list
- \+ *lemma* computability.encoding.card_le_omega
- \+ *lemma* computability.encoding.encode_injective
- \+ *lemma* computability.fin_encoding.card_le_omega



## [2022-04-09 17:28:05](https://github.com/leanprover-community/mathlib/commit/6abb6de)
feat(category_theory/bicategory): monoidal categories are single object bicategories ([#13157](https://github.com/leanprover-community/mathlib/pull/13157))
#### Estimated changes
Added src/category_theory/bicategory/End.lean
- \+ *def* category_theory.End_monoidal

Modified src/category_theory/bicategory/basic.lean


Added src/category_theory/bicategory/single_obj.lean
- \+ *def* category_theory.monoidal_single_obj.End_monoidal_star_functor
- \+ *def* category_theory.monoidal_single_obj.End_monoidal_star_functor_is_equivalence
- \+ *def* category_theory.monoidal_single_obj



## [2022-04-09 17:28:04](https://github.com/leanprover-community/mathlib/commit/823699f)
feat(linear_algebra/general_linear_group): Add some lemmas about SL to GL_pos coercions. ([#12393](https://github.com/leanprover-community/mathlib/pull/12393))
#### Estimated changes
Modified src/linear_algebra/general_linear_group.lean
- \+ *lemma* matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix
- \+ *lemma* matrix.special_linear_group.coe_GL_pos_neg
- \+ *lemma* matrix.special_linear_group.coe_to_GL_det
- \+ *lemma* matrix.special_linear_group.coe_to_GL_pos_to_GL_det



## [2022-04-09 15:37:04](https://github.com/leanprover-community/mathlib/commit/d42f6a8)
chore(algebra/associated): golf irreducible_iff_prime_iff ([#13267](https://github.com/leanprover-community/mathlib/pull/13267))
#### Estimated changes
Modified src/algebra/associated.lean




## [2022-04-09 15:37:03](https://github.com/leanprover-community/mathlib/commit/348b41d)
chore(archive/imo/imo1994_q1): tidy a bit ([#13266](https://github.com/leanprover-community/mathlib/pull/13266))
#### Estimated changes
Modified archive/imo/imo1994_q1.lean




## [2022-04-09 15:37:02](https://github.com/leanprover-community/mathlib/commit/1d9d153)
chore(algebraic_geometry/pullbacks): replaced some simps by simp onlys ([#13258](https://github.com/leanprover-community/mathlib/pull/13258))
This PR optimizes the file `algebraic_geometry/pullbacks` by replacing some calls to `simp` by `simp only [⋯]`.
This file has a high [`sec/LOC` ratio](https://mathlib-bench.limperg.de/commit/5e98dc1cc915d3226ea293c118d2ff657b48b0dc) and is not very short, which makes it a good candidate for such optimizations attempts.
On my machine, these changes reduced the compile time from 2m30s to 1m20s.
#### Estimated changes
Modified src/algebraic_geometry/pullbacks.lean




## [2022-04-09 15:37:01](https://github.com/leanprover-community/mathlib/commit/8c7e8a4)
feat(group_theory/commutator): The commutator subgroup is characteristic ([#13255](https://github.com/leanprover-community/mathlib/pull/13255))
This PR adds instances stating that the commutator subgroup is characteristic.
#### Estimated changes
Modified src/group_theory/abelianization.lean


Modified src/group_theory/commutator.lean




## [2022-04-09 15:37:00](https://github.com/leanprover-community/mathlib/commit/d23fd6f)
refactor(group_theory/solvable): Golf and move `solvable_of_ker_le_range` ([#13254](https://github.com/leanprover-community/mathlib/pull/13254))
This PR moves `solvable_of_ker_le_range` to earlier in the file so that it can be used to golf the proofs of `solvable_of_solvable_injective` and `solvable_of_surjective`.
#### Estimated changes
Modified src/group_theory/solvable.lean




## [2022-04-09 15:02:56](https://github.com/leanprover-community/mathlib/commit/f24918e)
refactor(group_theory/solvable): Golf some proofs ([#13256](https://github.com/leanprover-community/mathlib/pull/13256))
This PR golfs some proofs in `group_theory/solvable.lean`.
#### Estimated changes
Modified src/group_theory/solvable.lean




## [2022-04-09 12:31:00](https://github.com/leanprover-community/mathlib/commit/d6ff44e)
feat(category_theory/faithful): map_iso_injective ([#13263](https://github.com/leanprover-community/mathlib/pull/13263))
#### Estimated changes
Modified src/category_theory/functor/fully_faithful.lean
- \- *lemma* category_theory.equiv_of_fully_faithful_apply
- \- *lemma* category_theory.equiv_of_fully_faithful_symm_apply
- \+ *lemma* category_theory.functor.map_iso_injective
- \+ *def* category_theory.iso_equiv_of_fully_faithful



## [2022-04-09 10:39:57](https://github.com/leanprover-community/mathlib/commit/7a0513d)
feat(data/nat/*): generalize typeclass assumptions ([#13260](https://github.com/leanprover-community/mathlib/pull/13260))
#### Estimated changes
Modified src/data/nat/cast.lean
- \+/\- *lemma* map_nat_cast'

Modified src/data/nat/parity.lean




## [2022-04-09 07:19:58](https://github.com/leanprover-community/mathlib/commit/f5ee47b)
feat(category_theory/triangulated): upgrade map_triangle to a functor ([#13262](https://github.com/leanprover-community/mathlib/pull/13262))
Useful for LTE.
#### Estimated changes
Modified src/category_theory/triangulated/pretriangulated.lean
- \+/\- *def* category_theory.triangulated.pretriangulated.triangulated_functor.map_triangle
- \+ *def* category_theory.triangulated.pretriangulated.triangulated_functor_struct.id
- \+/\- *def* category_theory.triangulated.pretriangulated.triangulated_functor_struct.map_triangle

Modified src/category_theory/triangulated/rotate.lean
- \+/\- *def* category_theory.triangulated.from_inv_rotate_rotate
- \+/\- *def* category_theory.triangulated.from_rotate_inv_rotate
- \+/\- *def* category_theory.triangulated.inv_rot_comp_rot
- \+/\- *def* category_theory.triangulated.inv_rot_comp_rot_hom
- \+/\- *def* category_theory.triangulated.inv_rot_comp_rot_inv
- \+/\- *def* category_theory.triangulated.inv_rotate
- \+/\- *def* category_theory.triangulated.rot_comp_inv_rot
- \+/\- *def* category_theory.triangulated.rot_comp_inv_rot_hom
- \+/\- *def* category_theory.triangulated.rot_comp_inv_rot_inv
- \+/\- *def* category_theory.triangulated.rotate
- \+/\- *def* category_theory.triangulated.to_inv_rotate_rotate
- \+/\- *def* category_theory.triangulated.to_rotate_inv_rotate



## [2022-04-09 06:37:15](https://github.com/leanprover-community/mathlib/commit/a98a26b)
chore(measure_theory): move lemmas about `ae_measurable` to a new file ([#13246](https://github.com/leanprover-community/mathlib/pull/13246))
#### Estimated changes
Modified src/dynamics/ergodic/measure_preserving.lean


Modified src/measure_theory/group/arithmetic.lean


Modified src/measure_theory/lattice.lean


Added src/measure_theory/measure/ae_measurable.lean
- \+ *lemma* ae_measurable.add_measure
- \+ *lemma* ae_measurable.ae_inf_principal_eq_mk
- \+ *lemma* ae_measurable.ae_mem_imp_eq_mk
- \+ *lemma* ae_measurable.comp_measurable'
- \+ *lemma* ae_measurable.comp_measurable
- \+ *lemma* ae_measurable.exists_ae_eq_range_subset
- \+ *lemma* ae_measurable.indicator
- \+ *lemma* ae_measurable.mono_measure
- \+ *lemma* ae_measurable.mono_set
- \+ *lemma* ae_measurable.prod_mk
- \+ *lemma* ae_measurable.restrict
- \+ *lemma* ae_measurable.smul_measure
- \+ *lemma* ae_measurable.subtype_mk
- \+ *lemma* ae_measurable.sum_measure
- \+ *lemma* ae_measurable_Union_iff
- \+ *lemma* ae_measurable_add_measure_iff
- \+ *lemma* ae_measurable_iff_measurable
- \+ *lemma* ae_measurable_indicator_iff
- \+ *lemma* ae_measurable_interval_oc_iff
- \+ *lemma* ae_measurable_map_equiv_iff
- \+ *lemma* ae_measurable_of_ae_measurable_trim
- \+ *lemma* ae_measurable_of_subsingleton_codomain
- \+ *lemma* ae_measurable_one
- \+ *lemma* ae_measurable_restrict_iff_comap_subtype
- \+ *lemma* ae_measurable_restrict_of_measurable_subtype
- \+ *lemma* ae_measurable_smul_measure_iff
- \+ *lemma* ae_measurable_sum_measure_iff
- \+ *lemma* ae_measurable_union_iff
- \+ *lemma* ae_measurable_zero_measure
- \+ *lemma* measurable_embedding.ae_measurable_comp_iff
- \+ *lemma* measurable_embedding.ae_measurable_map_iff
- \+ *lemma* subsingleton.ae_measurable

Modified src/measure_theory/measure/measure_space.lean
- \- *lemma* ae_measurable.add_measure
- \- *lemma* ae_measurable.ae_inf_principal_eq_mk
- \- *lemma* ae_measurable.ae_mem_imp_eq_mk
- \- *lemma* ae_measurable.comp_measurable'
- \- *lemma* ae_measurable.comp_measurable
- \- *lemma* ae_measurable.exists_ae_eq_range_subset
- \- *lemma* ae_measurable.indicator
- \- *lemma* ae_measurable.mono_measure
- \- *lemma* ae_measurable.mono_set
- \- *lemma* ae_measurable.prod_mk
- \- *lemma* ae_measurable.restrict
- \- *lemma* ae_measurable.smul_measure
- \- *lemma* ae_measurable.subtype_mk
- \- *lemma* ae_measurable.sum_measure
- \- *lemma* ae_measurable_Union_iff
- \- *lemma* ae_measurable_add_measure_iff
- \- *lemma* ae_measurable_iff_measurable
- \- *lemma* ae_measurable_indicator_iff
- \- *lemma* ae_measurable_interval_oc_iff
- \- *lemma* ae_measurable_map_equiv_iff
- \- *lemma* ae_measurable_of_ae_measurable_trim
- \- *lemma* ae_measurable_of_subsingleton_codomain
- \- *lemma* ae_measurable_one
- \- *lemma* ae_measurable_restrict_iff_comap_subtype
- \- *lemma* ae_measurable_restrict_of_measurable_subtype
- \- *lemma* ae_measurable_smul_measure_iff
- \- *lemma* ae_measurable_sum_measure_iff
- \- *lemma* ae_measurable_union_iff
- \- *lemma* ae_measurable_zero_measure
- \- *lemma* measurable_embedding.ae_measurable_comp_iff
- \- *lemma* measurable_embedding.ae_measurable_map_iff
- \- *lemma* subsingleton.ae_measurable



## [2022-04-09 05:46:44](https://github.com/leanprover-community/mathlib/commit/59cf367)
chore(analysis/special_functions/pow): golf a proof ([#13247](https://github.com/leanprover-community/mathlib/pull/13247))
`complex.continuous_at_cpow_const` follows from `complex.continuous_at_cpow`.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean




## [2022-04-09 00:02:05](https://github.com/leanprover-community/mathlib/commit/2a04ec0)
feat(data/list/big_operators): More lemmas about alternating product ([#13195](https://github.com/leanprover-community/mathlib/pull/13195))
A few more lemmas about `list.alternating_prod` and `list.alternating_sum` and a proof that 11 divides even length base 10 palindromes.
Also rename `palindrome` to `list.palindrome` (as it should have been).
#### Estimated changes
Modified src/data/list/big_operators.lean
- \+ *lemma* list.alternating_prod_append
- \+ *lemma* list.alternating_prod_cons'
- \+ *lemma* list.alternating_prod_cons
- \+ *lemma* list.alternating_prod_cons_cons'
- \+/\- *lemma* list.alternating_prod_cons_cons
- \+/\- *lemma* list.alternating_prod_nil
- \+ *lemma* list.alternating_prod_reverse
- \+/\- *lemma* list.alternating_prod_singleton
- \- *lemma* list.alternating_sum_cons_cons

Modified src/data/list/palindrome.lean
- \+ *lemma* list.palindrome.append_reverse
- \+ *lemma* list.palindrome.iff_reverse_eq
- \+ *lemma* list.palindrome.of_reverse_eq
- \+ *lemma* list.palindrome.reverse_eq
- \- *lemma* palindrome.append_reverse
- \- *lemma* palindrome.iff_reverse_eq
- \- *lemma* palindrome.of_reverse_eq
- \- *lemma* palindrome.reverse_eq

Modified src/data/nat/digits.lean
- \+/\- *lemma* nat.eleven_dvd_iff
- \+ *lemma* nat.eleven_dvd_of_palindrome



## [2022-04-08 21:51:39](https://github.com/leanprover-community/mathlib/commit/485d648)
feat(algebra/big_operators): some big operator lemmas ([#13066](https://github.com/leanprover-community/mathlib/pull/13066))
Note that `prod_coe_sort` is essentially `prod_finset_coe` restated with the relatively new `finset.has_coe_to_sort`. I can also place `prod_finset_coe` with `prod_coe_sort` if we prefer.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_coe_sort
- \+ *lemma* finset.prod_coe_sort_eq_attach
- \- *lemma* fintype.prod_finset_coe

Modified src/data/finset/basic.lean
- \+ *lemma* finset.erase_insert_eq_erase

Modified src/measure_theory/measure/measure_space.lean




## [2022-04-08 17:20:39](https://github.com/leanprover-community/mathlib/commit/9498bea)
feat(group_theory/group_action/fixing_subgroup): add lemmas about fixing_subgroup ([#13202](https://github.com/leanprover-community/mathlib/pull/13202))
- pull back here the definition of fixing_subgroup and fixing_submonoid from field_theory.galois
- add lemmas about fixing_subgroup or fixing_submonoid in the context of mul_action
- add Galois connection relating it with fixed_points.
#### Estimated changes
Modified src/field_theory/galois.lean
- \- *def* fixing_subgroup
- \- *def* fixing_submonoid

Modified src/field_theory/krull_topology.lean
- \+ *lemma* intermediate_field.mem_fixing_subgroup_iff
- \- *lemma* mem_fixing_subgroup_iff

Added src/group_theory/group_action/fixing_subgroup.lean
- \+ *lemma* fixed_points_antitone
- \+ *lemma* fixed_points_subgroup_antitone
- \+ *lemma* fixed_points_subgroup_sup
- \+ *lemma* fixed_points_subgroup_supr
- \+ *lemma* fixed_points_submonoid_sup
- \+ *lemma* fixed_points_submonoid_supr
- \+ *def* fixing_subgroup
- \+ *lemma* fixing_subgroup_Union
- \+ *lemma* fixing_subgroup_antitone
- \+ *lemma* fixing_subgroup_fixed_points_gc
- \+ *lemma* fixing_subgroup_union
- \+ *def* fixing_submonoid
- \+ *lemma* fixing_submonoid_Union
- \+ *lemma* fixing_submonoid_antitone
- \+ *theorem* fixing_submonoid_fixed_points_gc
- \+ *lemma* fixing_submonoid_union
- \+ *lemma* mem_fixing_subgroup_iff
- \+ *lemma* mem_fixing_submonoid_iff



## [2022-04-08 15:41:02](https://github.com/leanprover-community/mathlib/commit/ed266e5)
feat(category_theory/limits/terminal): limit of the constant terminal functor ([#13238](https://github.com/leanprover-community/mathlib/pull/13238))
Needed in LTE.
#### Estimated changes
Modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* category_theory.limits.colimit_const_initial
- \+ *def* category_theory.limits.limit_const_terminal
- \+ *lemma* category_theory.limits.limit_const_terminal_inv_π
- \+ *lemma* category_theory.limits.ι_colimit_const_initial_hom



## [2022-04-08 15:41:01](https://github.com/leanprover-community/mathlib/commit/afa9be2)
feat(category_theory/limits/pullbacks): missing simp lemmas ([#13237](https://github.com/leanprover-community/mathlib/pull/13237))
Absence noted in LTE.
#### Estimated changes
Modified src/category_theory/limits/shapes/pullbacks.lean
- \+/\- *lemma* category_theory.limits.cospan_comp_iso_app_left
- \+/\- *lemma* category_theory.limits.cospan_comp_iso_app_one
- \+/\- *lemma* category_theory.limits.cospan_comp_iso_app_right
- \+ *lemma* category_theory.limits.cospan_comp_iso_hom_app_left
- \+ *lemma* category_theory.limits.cospan_comp_iso_hom_app_one
- \+ *lemma* category_theory.limits.cospan_comp_iso_hom_app_right
- \+ *lemma* category_theory.limits.cospan_comp_iso_inv_app_left
- \+ *lemma* category_theory.limits.cospan_comp_iso_inv_app_one
- \+ *lemma* category_theory.limits.cospan_comp_iso_inv_app_right
- \+/\- *lemma* category_theory.limits.cospan_ext_app_left
- \+/\- *lemma* category_theory.limits.cospan_ext_app_one
- \+/\- *lemma* category_theory.limits.cospan_ext_app_right
- \+ *lemma* category_theory.limits.cospan_ext_hom_app_left
- \+ *lemma* category_theory.limits.cospan_ext_hom_app_one
- \+ *lemma* category_theory.limits.cospan_ext_hom_app_right
- \+ *lemma* category_theory.limits.cospan_ext_inv_app_left
- \+ *lemma* category_theory.limits.cospan_ext_inv_app_one
- \+ *lemma* category_theory.limits.cospan_ext_inv_app_right
- \+/\- *lemma* category_theory.limits.span_comp_iso_app_left
- \+/\- *lemma* category_theory.limits.span_comp_iso_app_right
- \+/\- *lemma* category_theory.limits.span_comp_iso_app_zero
- \+ *lemma* category_theory.limits.span_comp_iso_hom_app_left
- \+ *lemma* category_theory.limits.span_comp_iso_hom_app_right
- \+ *lemma* category_theory.limits.span_comp_iso_hom_app_zero
- \+ *lemma* category_theory.limits.span_comp_iso_inv_app_left
- \+ *lemma* category_theory.limits.span_comp_iso_inv_app_right
- \+ *lemma* category_theory.limits.span_comp_iso_inv_app_zero
- \+/\- *lemma* category_theory.limits.span_ext_app_left
- \+/\- *lemma* category_theory.limits.span_ext_app_one
- \+/\- *lemma* category_theory.limits.span_ext_app_right
- \+ *lemma* category_theory.limits.span_ext_hom_app_left
- \+ *lemma* category_theory.limits.span_ext_hom_app_right
- \+ *lemma* category_theory.limits.span_ext_hom_app_zero
- \+ *lemma* category_theory.limits.span_ext_inv_app_left
- \+ *lemma* category_theory.limits.span_ext_inv_app_right
- \+ *lemma* category_theory.limits.span_ext_inv_app_zero



## [2022-04-08 15:40:59](https://github.com/leanprover-community/mathlib/commit/0521344)
feat(analysis/locally_convex/basic): add lemmas about finite unions for absorbs ([#13236](https://github.com/leanprover-community/mathlib/pull/13236))
- Lemma for absorbing sets and addition
- Two Lemmas for absorbing sets as finite unions (set.finite and finset variant)
- Lemma for absorbent sets absorb finite sets.
#### Estimated changes
Modified src/analysis/locally_convex/basic.lean
- \+ *lemma* absorbent.absorbs_finite
- \+ *lemma* absorbs.add
- \+ *lemma* absorbs_Union_finset
- \+ *lemma* set.finite.absorbs_Union



## [2022-04-08 15:40:58](https://github.com/leanprover-community/mathlib/commit/0831e4f)
feat(data/polynomial/degree/definitions): add `degree_monoid_hom` ([#13233](https://github.com/leanprover-community/mathlib/pull/13233))
It will be used to simplify the proof of some lemmas.
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+ *def* polynomial.degree_monoid_hom



## [2022-04-08 13:45:44](https://github.com/leanprover-community/mathlib/commit/f5d4fa1)
feat(data/fintype/basic): add `fintype_of_{equiv,option}` ([#13086](https://github.com/leanprover-community/mathlib/pull/13086))
`fintype_of_option_equiv` was extracted from @huynhtrankhanh's https://github.com/leanprover-community/mathlib/pull/11162, moved here to a separate PR.  The split into `fintype_of_option` and `fintype_of_equiv` is based on a comment on that PR by @jcommelin.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *def* fintype_of_option
- \+ *def* fintype_of_option_equiv



## [2022-04-08 13:45:43](https://github.com/leanprover-community/mathlib/commit/d96e17d)
feat(data/multiset/basic): add `map_le_map_iff` and `map_embedding` ([#13082](https://github.com/leanprover-community/mathlib/pull/13082))
Adds lemmas `map_le_map_iff : s.map f ≤ t.map f ↔ s ≤ t` and `map_embedding : multiset α ↪o multiset β` for embedding `f`.
Extracted from @huynhtrankhanh's [#11162](https://github.com/leanprover-community/mathlib/pull/11162), moved here to a separate PR
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *def* multiset.map_embedding
- \+ *lemma* multiset.map_le_map_iff



## [2022-04-08 13:45:41](https://github.com/leanprover-community/mathlib/commit/5acaeaf)
chore(computability/language): Golf ([#13039](https://github.com/leanprover-community/mathlib/pull/13039))
Golf the `semiring` instance using the `set.image2` API, add half missing docstring.
#### Estimated changes
Modified src/computability/language.lean
- \+/\- *lemma* language.mem_one
- \+/\- *lemma* language.mul_def
- \+ *lemma* language.nil_mem_one
- \+ *lemma* language.not_mem_zero



## [2022-04-08 13:45:40](https://github.com/leanprover-community/mathlib/commit/2569ad5)
feat(data/set/intervals/basic): An open interval of a dense order has no maximum/minimum ([#12924](https://github.com/leanprover-community/mathlib/pull/12924))
#### Estimated changes
Modified src/data/set/intervals/basic.lean




## [2022-04-08 12:12:47](https://github.com/leanprover-community/mathlib/commit/91ce04d)
chore(model_theory/encoding): Move the encoding for terms to its own file ([#13223](https://github.com/leanprover-community/mathlib/pull/13223))
Moves the declarations about encodings and cardinality of terms to their own file, `model_theory/encoding`
#### Estimated changes
Added src/model_theory/encoding.lean
- \+ *theorem* first_order.language.term.card_le
- \+ *lemma* first_order.language.term.card_le_omega
- \+ *def* first_order.language.term.list_decode
- \+ *theorem* first_order.language.term.list_decode_encode_list
- \+ *def* first_order.language.term.list_encode
- \+ *lemma* first_order.language.term.list_encode_injective

Modified src/model_theory/substructures.lean


Modified src/model_theory/syntax.lean
- \- *theorem* first_order.language.term.card_le
- \- *lemma* first_order.language.term.card_le_omega
- \- *def* first_order.language.term.list_decode
- \- *theorem* first_order.language.term.list_decode_encode_list
- \- *def* first_order.language.term.list_encode
- \- *lemma* first_order.language.term.list_encode_injective



## [2022-04-08 12:12:46](https://github.com/leanprover-community/mathlib/commit/ed68854)
feat(model_theory/*): Theory of nonempty structures and bundling elementary substructures ([#13118](https://github.com/leanprover-community/mathlib/pull/13118))
Defines a sentence and theory to indicate a structure is nonempty
Defines a map to turn elementary substructures of a bundled model into bundled models
#### Estimated changes
Modified src/model_theory/bundled.lean
- \+ *def* first_order.language.elementary_substructure.to_Model

Modified src/model_theory/elementary_maps.lean
- \+ *lemma* first_order.language.elementary_substructure.Theory_model_iff
- \+ *lemma* first_order.language.elementary_substructure.realize_sentence

Modified src/model_theory/semantics.lean
- \+ *lemma* first_order.language.Theory.model_nonempty_iff
- \+ *lemma* first_order.language.sentence.realize_nonempty

Modified src/model_theory/syntax.lean




## [2022-04-08 12:12:45](https://github.com/leanprover-community/mathlib/commit/710fe04)
feat(model_theory/order): Defines ordered languages and structures ([#13088](https://github.com/leanprover-community/mathlib/pull/13088))
Defines ordered languages and ordered structures
Defines the theories of pre-, partial, and linear orders, shows they are modeled by the respective structures.
#### Estimated changes
Added src/model_theory/order.lean
- \+ *def* first_order.language.is_ordered_structure
- \+ *def* first_order.language.order_Lhom
- \+ *lemma* first_order.language.order_Lhom_order
- \+ *def* first_order.language.term.le



## [2022-04-08 12:12:44](https://github.com/leanprover-community/mathlib/commit/7340720)
feat(group_theory/group_action/basic): Add typeclass for actions that descend to the quotient ([#12999](https://github.com/leanprover-community/mathlib/pull/12999))
Part of [#12848](https://github.com/leanprover-community/mathlib/pull/12848).
#### Estimated changes
Modified src/group_theory/group_action/basic.lean




## [2022-04-08 11:40:03](https://github.com/leanprover-community/mathlib/commit/851b320)
feat(ring_theory/localization): b is linear independent over R iff l.i. over `Frac(R)` ([#13041](https://github.com/leanprover-community/mathlib/pull/13041))
#### Estimated changes
Added src/ring_theory/localization/module.lean
- \+ *lemma* linear_independent.iff_fraction_ring
- \+ *lemma* linear_independent.localization



## [2022-04-08 07:42:13](https://github.com/leanprover-community/mathlib/commit/7d41715)
feat(archive/imo/imo2008_q3): golf ([#13232](https://github.com/leanprover-community/mathlib/pull/13232))
#### Estimated changes
Modified archive/imo/imo2008_q3.lean




## [2022-04-08 07:42:12](https://github.com/leanprover-community/mathlib/commit/e85dc17)
feat(group_theory/subgroup/basic): The centralizer of a characteristic subgroup is characteristic ([#13230](https://github.com/leanprover-community/mathlib/pull/13230))
This PR proves that the centralizer of a characteristic subgroup is characteristic.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean




## [2022-04-08 07:42:10](https://github.com/leanprover-community/mathlib/commit/95ebbad)
refactor(group_theory/commutator): Move `commutator_le_map_commutator` ([#13229](https://github.com/leanprover-community/mathlib/pull/13229))
`commutator_le_map_commutator` is a general lemma about commutators, so it should be moved from `solvable.lean` to `commutator.lean`.
#### Estimated changes
Modified src/group_theory/commutator.lean
- \+ *lemma* subgroup.commutator_le_map_commutator

Modified src/group_theory/solvable.lean
- \- *lemma* commutator_le_map_commutator



## [2022-04-08 07:42:09](https://github.com/leanprover-community/mathlib/commit/1a4203a)
feat(group_theory/coset): Right cosets are in bijection with left cosets ([#13228](https://github.com/leanprover-community/mathlib/pull/13228))
Right cosets are in bijection with left cosets. This came up in some work involving right transversals.
#### Estimated changes
Modified src/group_theory/coset.lean
- \+ *def* quotient_group.quotient_right_rel_equiv_quotient_left_rel



## [2022-04-08 07:42:08](https://github.com/leanprover-community/mathlib/commit/499a4a8)
feat(group_theory/index): `fintype_of_index_ne_zero` ([#13225](https://github.com/leanprover-community/mathlib/pull/13225))
This PR adds `fintype_of_index_ne_zero`.
#### Estimated changes
Modified src/group_theory/index.lean




## [2022-04-08 06:14:18](https://github.com/leanprover-community/mathlib/commit/ccf3e37)
feat(ring_theory/unique_factorization_domain): alternative specification for `count (normalized_factors x)` ([#13161](https://github.com/leanprover-community/mathlib/pull/13161))
`count_normalized_factors_eq` specifies the number of times an irreducible factor `p` appears in `normalized_factors x`, namely the number of times it divides `x`. This is often easier to work with than going through `multiplicity` since this way we avoid coercing to `enat`.
#### Estimated changes
Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* unique_factorization_monoid.count_normalized_factors_eq



## [2022-04-08 06:14:17](https://github.com/leanprover-community/mathlib/commit/0c424e9)
refactor(analysis/normed_space/conformal_linear_map): redefine ([#13143](https://github.com/leanprover-community/mathlib/pull/13143))
Use equality of bundled maps instead of coercions to functions in the definition of `is_conformal_map`. Also golf some proofs.
#### Estimated changes
Modified src/analysis/calculus/conformal/normed_space.lean
- \+ *lemma* subsingleton.conformal_at

Modified src/analysis/complex/conformal.lean
- \+/\- *lemma* is_conformal_map_complex_linear

Modified src/analysis/complex/real_deriv.lean
- \+/\- *lemma* differentiable_at.conformal_at

Modified src/analysis/inner_product_space/conformal_linear_map.lean
- \+/\- *lemma* is_conformal_map_iff

Modified src/analysis/normed_space/conformal_linear_map.lean
- \+/\- *lemma* is_conformal_map.comp
- \- *lemma* is_conformal_map.injective
- \+ *lemma* is_conformal_map.smul
- \+/\- *lemma* is_conformal_map_const_smul
- \+/\- *lemma* is_conformal_map_of_subsingleton
- \- *lemma* linear_isometry.is_conformal_map

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry.coe_mk
- \+ *lemma* linear_isometry.id_to_continuous_linear_map



## [2022-04-08 06:14:16](https://github.com/leanprover-community/mathlib/commit/036fc99)
feat(topology/uniform_space/uniform_convergence): add `tendsto_uniformly_iff_seq_tendsto_uniformly` ([#13128](https://github.com/leanprover-community/mathlib/pull/13128))
For countably generated filters, uniform convergence is equivalent to uniform convergence of sub-sequences.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.eventually_iff_seq_eventually

Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_antitone_basis.prod

Modified src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* tendsto_uniformly_iff_seq_tendsto_uniformly
- \+ *lemma* tendsto_uniformly_on.seq_tendsto_uniformly_on
- \+ *lemma* tendsto_uniformly_on_iff_seq_tendsto_uniformly_on
- \+ *lemma* tendsto_uniformly_on_of_seq_tendsto_uniformly_on



## [2022-04-08 06:14:15](https://github.com/leanprover-community/mathlib/commit/ab60244)
feat(model_theory/basic,bundled): Structures induced by equivalences ([#13124](https://github.com/leanprover-community/mathlib/pull/13124))
Defines `equiv.induced_Structure`, a structure on the codomain of a bijection that makes the bijection an isomorphism.
Defines maps on bundled models to shift them along bijections and up and down universes.
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *def* equiv.induced_Structure
- \+ *def* equiv.induced_Structure_equiv

Modified src/model_theory/bundled.lean
- \+ *def* first_order.language.Theory.Model.equiv_induced
- \+ *def* first_order.language.Theory.Model.ulift

Modified src/model_theory/semantics.lean
- \+ *lemma* first_order.language.equiv.Theory_model
- \+/\- *lemma* first_order.language.equiv.realize_bounded_formula
- \+/\- *lemma* first_order.language.equiv.realize_formula
- \+ *lemma* first_order.language.equiv.realize_sentence



## [2022-04-08 05:13:45](https://github.com/leanprover-community/mathlib/commit/9f3e7fb)
feat(category_theory/limits): further API for commuting limits ([#13215](https://github.com/leanprover-community/mathlib/pull/13215))
Needed for LTE.
#### Estimated changes
Modified src/category_theory/functor/currying.lean
- \+ *def* category_theory.uncurry_obj_flip

Modified src/category_theory/limits/fubini.lean
- \+ *def* category_theory.limits.limit_flip_comp_lim_iso_limit_comp_lim
- \+ *lemma* category_theory.limits.limit_flip_comp_lim_iso_limit_comp_lim_hom_π_π
- \+ *lemma* category_theory.limits.limit_flip_comp_lim_iso_limit_comp_lim_inv_π_π

Modified src/category_theory/limits/has_limits.lean
- \+ *lemma* category_theory.limits.has_colimit.iso_of_nat_iso_inv_desc
- \+ *lemma* category_theory.limits.has_colimit.iso_of_nat_iso_ι_inv
- \+ *lemma* category_theory.limits.has_limit.iso_of_nat_iso_inv_π
- \+ *lemma* category_theory.limits.has_limit.lift_iso_of_nat_iso_inv

Modified src/category_theory/limits/is_limit.lean
- \+ *lemma* category_theory.limits.is_colimit.cocone_points_iso_of_nat_iso_inv_desc
- \+ *lemma* category_theory.limits.is_limit.lift_comp_cone_points_iso_of_nat_iso_inv



## [2022-04-08 02:06:33](https://github.com/leanprover-community/mathlib/commit/5e98dc1)
feat(topology/continuous_function/zero_at_infty): add more instances for zero_at_infty_continuous_map and establish C₀ functorial properties ([#13196](https://github.com/leanprover-community/mathlib/pull/13196))
This adds more instances for the type `C₀(α, β)` of continuous functions vanishing at infinity. Notably, these new instances include its non-unital ring, normed space and star structures, culminating with `cstar_ring` when `β` is a `cstar_ring` which is also a `topological_ring`.
In addition, this establishes functorial properties of `C₀(-, β)` for various choices of algebraic categories involving `β`. The domain of these (contravariant) functors is the category of topological spaces with cocompact continuous maps, and the functor applied to a cocompact map is given by pre-composition.
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean


Modified src/topology/continuous_function/cocompact_map.lean


Modified src/topology/continuous_function/zero_at_infty.lean
- \+ *lemma* zero_at_infty_continuous_map.coe_comp_to_continuous_fun
- \+ *lemma* zero_at_infty_continuous_map.coe_star
- \+ *lemma* zero_at_infty_continuous_map.coe_to_bcf_add_monoid_hom
- \+ *def* zero_at_infty_continuous_map.comp
- \+ *def* zero_at_infty_continuous_map.comp_add_monoid_hom
- \+ *lemma* zero_at_infty_continuous_map.comp_assoc
- \+ *lemma* zero_at_infty_continuous_map.comp_id
- \+ *def* zero_at_infty_continuous_map.comp_linear_map
- \+ *def* zero_at_infty_continuous_map.comp_mul_hom
- \+ *def* zero_at_infty_continuous_map.comp_non_unital_alg_hom
- \+ *lemma* zero_at_infty_continuous_map.norm_to_bcf_eq_norm
- \+ *lemma* zero_at_infty_continuous_map.star_apply
- \+ *def* zero_at_infty_continuous_map.to_bcf_add_monoid_hom
- \+ *lemma* zero_at_infty_continuous_map.to_bcf_injective
- \- *lemma* zero_at_infty_continuous_map.to_bounded_continuous_function_injective
- \+ *lemma* zero_at_infty_continuous_map.zero_comp



## [2022-04-08 00:26:57](https://github.com/leanprover-community/mathlib/commit/0719b36)
feat(category_theory/limits/shapes): isomorphisms of (co)spans ([#13216](https://github.com/leanprover-community/mathlib/pull/13216))
#### Estimated changes
Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* category_theory.limits.cospan_comp_iso
- \+ *lemma* category_theory.limits.cospan_comp_iso_app_left
- \+ *lemma* category_theory.limits.cospan_comp_iso_app_one
- \+ *lemma* category_theory.limits.cospan_comp_iso_app_right
- \+ *def* category_theory.limits.cospan_ext
- \+ *lemma* category_theory.limits.cospan_ext_app_left
- \+ *lemma* category_theory.limits.cospan_ext_app_one
- \+ *lemma* category_theory.limits.cospan_ext_app_right
- \+ *def* category_theory.limits.span_comp_iso
- \+ *lemma* category_theory.limits.span_comp_iso_app_left
- \+ *lemma* category_theory.limits.span_comp_iso_app_right
- \+ *lemma* category_theory.limits.span_comp_iso_app_zero
- \+ *def* category_theory.limits.span_ext
- \+ *lemma* category_theory.limits.span_ext_app_left
- \+ *lemma* category_theory.limits.span_ext_app_one
- \+ *lemma* category_theory.limits.span_ext_app_right



## [2022-04-08 00:26:56](https://github.com/leanprover-community/mathlib/commit/b897115)
chore(algebra/associated): generalisation linter ([#13108](https://github.com/leanprover-community/mathlib/pull/13108))
#### Estimated changes
Modified src/algebra/associated.lean
- \+/\- *lemma* associates.bot_eq_one
- \+/\- *lemma* associates.mk_injective
- \+/\- *lemma* associates.mk_one
- \+/\- *lemma* dvd_not_unit.is_unit_of_irreducible_right
- \+/\- *lemma* dvd_not_unit.not_unit
- \+/\- *lemma* dvd_not_unit_of_dvd_not_unit_associated
- \+/\- *lemma* not_irreducible_of_not_unit_dvd_not_unit



## [2022-04-07 22:31:46](https://github.com/leanprover-community/mathlib/commit/cae5164)
chore(algebra/order/{monoid,ring}): missing typeclasses about `*` and `+` on `order_dual` ([#13004](https://github.com/leanprover-community/mathlib/pull/13004))
#### Estimated changes
Modified src/algebra/order/group.lean


Modified src/algebra/order/monoid.lean


Modified src/algebra/order/ring.lean




## [2022-04-07 20:32:53](https://github.com/leanprover-community/mathlib/commit/02a2560)
feat(analysis/normed_space/add_torsor_bases): add `convex.interior_nonempty_iff_affine_span_eq_top` ([#13220](https://github.com/leanprover-community/mathlib/pull/13220))
Generalize `interior_convex_hull_nonempty_iff_aff_span_eq_top` to any
convex set, not necessarily written as the convex hull of a set.
#### Estimated changes
Modified src/analysis/normed_space/add_torsor_bases.lean
- \+ *lemma* convex.interior_nonempty_iff_affine_span_eq_top



## [2022-04-07 20:32:52](https://github.com/leanprover-community/mathlib/commit/0f4d0ae)
feat(data/polynomial/identities): golf using `linear_combination` ([#13212](https://github.com/leanprover-community/mathlib/pull/13212))
#### Estimated changes
Modified src/data/polynomial/identities.lean




## [2022-04-07 20:32:51](https://github.com/leanprover-community/mathlib/commit/3b04f48)
feat(number_theory/fermat4): golf using `linear_combination` ([#13211](https://github.com/leanprover-community/mathlib/pull/13211))
#### Estimated changes
Modified src/number_theory/fermat4.lean




## [2022-04-07 20:32:50](https://github.com/leanprover-community/mathlib/commit/82d1e9f)
feat(algebra/quadratic_discriminant): golf using `linear_combination` ([#13210](https://github.com/leanprover-community/mathlib/pull/13210))
#### Estimated changes
Modified src/algebra/quadratic_discriminant.lean




## [2022-04-07 18:41:47](https://github.com/leanprover-community/mathlib/commit/4ff75f5)
refactor(category_theory/bicategory): set simp-normal form for 2-morphisms ([#13185](https://github.com/leanprover-community/mathlib/pull/13185))
## Problem
The definition of bicategories contains the following axioms:
```lean
associator_naturality_left : ∀ {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d),
  (η ▷ g) ▷ h ≫ (α_ f' g h).hom = (α_ f g h).hom ≫ η ▷ (g ≫ h)
associator_naturality_middle : ∀ (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d),
  (f ◁ η) ▷ h ≫ (α_ f g' h).hom = (α_ f g h).hom ≫ f ◁ (η ▷ h)
associator_naturality_right : ∀ (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h'),
  (f ≫ g) ◁ η ≫ (α_ f g h').hom = (α_ f g h).hom ≫ f ◁ (g ◁ η) 
left_unitor_naturality : ∀ {f g : a ⟶ b} (η : f ⟶ g),
  𝟙 a ◁ η ≫ (λ_ g).hom = (λ_ f).hom ≫ η
right_unitor_naturality : ∀ {f g : a ⟶ b} (η : f ⟶ g) :
  η ▷ 𝟙 b ≫ (ρ_ g).hom = (ρ_ f).hom ≫ η
```
By using these axioms, we can see that, for example, 2-morphisms `(f₁ ≫ f₂) ◁ (f₃ ◁ (η ▷ (f₄ ≫ f₅)))` and `f₁ ◁ ((𝟙_ ≫ f₂ ≫ f₃) ◁ ((η ▷ f₄) ▷ f₅))` are equal up to some associators and unitors. The problem is that the proof of this fact requires tedious rewriting. We should insert appropriate associators and unitors, and then rewrite using the above axioms manually.
This tedious rewriting is also a problem when we use the (forthcoming) `coherence` tactic (bicategorical version of [#13125](https://github.com/leanprover-community/mathlib/pull/13125)), which only works if the non-structural 2-morphisms in the LHS and the RHS are the same.
## Main change
The main proposal of this PR is to introduce a normal form of such 2-morphisms, and put simp attributes to suitable lemmas in order to rewrite any 2-morphism into the normal form. For example, the normal form of the previouse example is `f₁ ◁ (f₂ ◁ (f₃ ◁ ((η ▷ f₄) ▷ f₅)))`. The precise definition of the normal form can be found in the docs in `basic.lean` file. The new simp lemmas introduced in this PR are the following:
```lean
whisker_right_comp : ∀ {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d),
  η ▷ (g ≫ h) = (α_ f g h).inv ≫ η ▷ g ▷ h ≫ (α_ f' g h).hom 
whisker_assoc : ∀ (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d),
  (f ◁ η) ▷ h = (α_ f g h).hom ≫ f ◁ (η ▷ h) ≫ (α_ f g' h).inv
comp_whisker_left : ∀ (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h'),
  (f ≫ g) ◁ η = (α_ f g h).hom ≫ f ◁ g ◁ η ≫ (α_ f g h').inv
id_whisker_left : ∀ {f g : a ⟶ b} (η : f ⟶ g),
  𝟙 a ◁ η = (λ_ f).hom ≫ η ≫ (λ_ g).inv
whisker_right_id : ∀ {f g : a ⟶ b} (η : f ⟶ g),
  η ▷ 𝟙 b = (ρ_ f).hom ≫ η ≫ (ρ_ g).inv
```
Logically, these are equivalent to the five axioms presented above. The point is that these equalities have the definite simplification direction.
## Improvement 
Some proofs that had been based on tedious rewriting are now automated. For example, the conditions in `oplax_nat_trans.id`, `oplax_nat_trans.comp`, and several functions in `functor_bicategory.lean` are now proved by `tidy`.
## Specific changes
- The new simp lemmas `whisker_right_comp` etc. actually have been included in the definition of bicategories instead of `associate_naturality_left` etc. so that the latter lemmas are proved in later of the file just by `simp`.
- The precedence of the whiskering notations "infixr ` ◁ `:70" and "infixr ` ◁ `:70" have been changed into "infixr ` ◁ `:81" and "infixr ` ◁ `:81", which is now higher than that of the composition `≫`. This setting is consistent with the normal form introduced in this PR in the sence that an expression is in normal form only if it has the minimal number of parentheses in this setting. For example, the normal form `f₁ ◁ (f₂ ◁ (f₃ ◁ ((η ▷ f₄) ▷ f₅)))` can be written as `f₁ ◁ f₂ ◁ f₃ ◁ η ▷ f₄ ▷ f₅`.
- The unneeded parentheses caused by the precedence change have been removed.
- The lemmas `whisker_right_id` and `whisker_right_comp` have been renamed to `id_whisker_right` and `comp_whisker_right` since these are more consistent with the notation. Note that the name `whisker_right_id` and `whisker_right_comp` are now used for the two of the five simp lemmas presented above.
- The lemmas in `basic.lean` have been rearranged to be more logically consistent.
## Future work
I would like to apply a similar strategy for monoidal categories.
#### Estimated changes
Modified src/category_theory/bicategory/basic.lean
- \- *lemma* category_theory.bicategory.associator_conjugation_left
- \- *lemma* category_theory.bicategory.associator_conjugation_middle
- \- *lemma* category_theory.bicategory.associator_conjugation_right
- \- *lemma* category_theory.bicategory.associator_inv_conjugation_left
- \- *lemma* category_theory.bicategory.associator_inv_conjugation_middle
- \- *lemma* category_theory.bicategory.associator_inv_conjugation_right
- \+ *lemma* category_theory.bicategory.associator_naturality_left
- \+ *lemma* category_theory.bicategory.associator_naturality_middle
- \+ *lemma* category_theory.bicategory.associator_naturality_right
- \+ *lemma* category_theory.bicategory.comp_whisker_left_symm
- \+ *lemma* category_theory.bicategory.id_whisker_left_symm
- \- *lemma* category_theory.bicategory.left_unitor_comp'
- \- *lemma* category_theory.bicategory.left_unitor_comp_inv'
- \- *lemma* category_theory.bicategory.left_unitor_conjugation
- \+/\- *lemma* category_theory.bicategory.left_unitor_inv_naturality
- \+ *lemma* category_theory.bicategory.left_unitor_naturality
- \- *lemma* category_theory.bicategory.right_unitor_conjugation
- \+/\- *lemma* category_theory.bicategory.right_unitor_inv_naturality
- \+ *lemma* category_theory.bicategory.right_unitor_naturality
- \+ *lemma* category_theory.bicategory.whisker_assoc_symm
- \+ *lemma* category_theory.bicategory.whisker_right_comp_symm
- \+ *lemma* category_theory.bicategory.whisker_right_id_symm

Modified src/category_theory/bicategory/coherence.lean
- \+ *lemma* category_theory.free_bicategory.preinclusion_obj

Modified src/category_theory/bicategory/free.lean


Modified src/category_theory/bicategory/functor.lean


Modified src/category_theory/bicategory/functor_bicategory.lean


Modified src/category_theory/bicategory/natural_transformation.lean


Modified src/category_theory/bicategory/strict.lean




## [2022-04-07 18:41:46](https://github.com/leanprover-community/mathlib/commit/44c31d8)
feat(data/finset/basic): add `map_injective` and `sigma_equiv_option_of_inhabited` ([#13083](https://github.com/leanprover-community/mathlib/pull/13083))
Adds `map_injective (f : α ↪ β) : injective (map f) := (map_embedding f).injective` and `sigma_equiv_option_of_inhabited [inhabited α] : Σ (β : Type u), α ≃ option β`.
Extracted from @huynhtrankhanh's https://github.com/leanprover-community/mathlib/pull/11162, moved here to a separate PR
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *def* equiv.sigma_equiv_option_of_inhabited
- \+ *lemma* finset.map_injective



## [2022-04-07 18:41:45](https://github.com/leanprover-community/mathlib/commit/9d786ce)
feat(topology/metric/basic): construct a bornology from metric axioms and add it to the pseudo metric structure ([#12078](https://github.com/leanprover-community/mathlib/pull/12078))
Every metric structure naturally gives rise to a bornology where the bounded sets are precisely the metric bounded sets. The eventual goal will be to replace the existing `metric.bounded` with one defined in terms of the bornology, so we need to construct the bornology first, as we do here.
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean


Modified src/number_theory/modular.lean


Modified src/topology/metric_space/basic.lean
- \+ *def* bornology.of_dist



## [2022-04-07 16:53:29](https://github.com/leanprover-community/mathlib/commit/2d2d09c)
feat(data/nat/gcd): added gcd_mul_of_dvd_coprime ([#12989](https://github.com/leanprover-community/mathlib/pull/12989))
Added gcd_mul_of_dvd_coprime lemma to gcd.lean.
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+ *lemma* nat.gcd_mul_of_coprime_of_dvd



## [2022-04-07 16:20:47](https://github.com/leanprover-community/mathlib/commit/733aed5)
chore(group_theory/index): Add `to_additive` ([#13191](https://github.com/leanprover-community/mathlib/pull/13191))
This PR adds `to_additive` to the rest of `group_theory/index.lean`.
#### Estimated changes



## [2022-04-07 16:20:46](https://github.com/leanprover-community/mathlib/commit/c522e3b)
feat(data/polynomial/basic): add simp lemmas X_mul_C and X_pow_mul_C ([#13163](https://github.com/leanprover-community/mathlib/pull/13163))
These lemmas are direct applications of `X_mul` and `X_pow_mul`.  However, their more general version cannot be `simp` lemmas since they form loops.  These versions do not, since they involve an explicit `C`.
I golfed slightly a proof in `linear_algebra.eigenspace` since it was timing out.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/polynomial.20op_C/near/277703846)
#### Estimated changes



## [2022-04-07 16:20:44](https://github.com/leanprover-community/mathlib/commit/6a0524f)
feat(category_theory/monoidal): upgrades for monoidal equivalences ([#13158](https://github.com/leanprover-community/mathlib/pull/13158))
(Recall that a "monoidal equivalence" is a functor which is separately monoidal, and an equivalence.
This PR completes the work required to see this is the same as having a monoidal inverse, up to monoidal units and counits.)
* Shows that the unit and counit of a monoidal equivalence have a natural monoidal structure. 
* Previously, when transporting a monoidal structure across a (non-monoidal) equivalence,
we constructed directly the monoidal strength on the inverse functor. In the meantime, @b-mehta has provided a general construction for the monoidal strength on the inverse of any monoidal equivalence, so now we use that.
The proofs of `monoidal_unit` and `monoidal_counit` in `category_theory/monoidal/natural_transformation.lean` are quite ugly. If anyone would like to golf these that would be lovely! :-)
#### Estimated changes



## [2022-04-07 16:20:43](https://github.com/leanprover-community/mathlib/commit/d7ad7d3)
feat(set_theory/cardinal): Upper bound on domain from upper bound on fibers ([#13147](https://github.com/leanprover-community/mathlib/pull/13147))
A uniform upper bound on fibers gives an upper bound on the domain.
#### Estimated changes



## [2022-04-07 16:20:41](https://github.com/leanprover-community/mathlib/commit/47a3cd2)
feat(probability/integration): Bochner integral of the product of independent functions ([#13140](https://github.com/leanprover-community/mathlib/pull/13140))
This is limited to real-valued functions, which is not very satisfactory but it is not clear (to me) what the most general version of each of those lemmas would be.
#### Estimated changes



## [2022-04-07 16:20:40](https://github.com/leanprover-community/mathlib/commit/ab1bf0f)
feat(algebra/order/monoid): add eq_one_or_one_lt ([#13131](https://github.com/leanprover-community/mathlib/pull/13131))
Needed in LTE.
#### Estimated changes



## [2022-04-07 16:20:39](https://github.com/leanprover-community/mathlib/commit/7c04f36)
feat(group_theory/schreier): prove Schreier's lemma ([#13019](https://github.com/leanprover-community/mathlib/pull/13019))
This PR adds a proof of Schreier's lemma.
#### Estimated changes



## [2022-04-07 16:20:37](https://github.com/leanprover-community/mathlib/commit/315bff3)
feat(archive/100-theorems-list/37_solution_of_cubic): golf ([#13012](https://github.com/leanprover-community/mathlib/pull/13012))
Express one of the lemmas for the solution of the cubic as a giant `linear_combination` calculation.
#### Estimated changes



## [2022-04-07 14:25:29](https://github.com/leanprover-community/mathlib/commit/c4f3869)
chore(order/symm_diff): Change the symmetric difference notation ([#13217](https://github.com/leanprover-community/mathlib/pull/13217))
The notation for `symm_diff` was `Δ` (`\D`, `\GD`, `\Delta`). It now is `∆` (`\increment`).
#### Estimated changes
Modified src/combinatorics/colex.lean


Modified src/data/mv_polynomial/basic.lean


Modified src/measure_theory/decomposition/jordan.lean


Modified src/measure_theory/decomposition/signed_hahn.lean


Modified src/measure_theory/measurable_space_def.lean


Modified src/order/imp.lean
- \+/\- *lemma* lattice.compl_biimp
- \+/\- *lemma* lattice.compl_symm_diff

Modified src/order/symm_diff.lean
- \+/\- *lemma* bot_symm_diff
- \+/\- *lemma* compl_symm_diff
- \+/\- *lemma* compl_symm_diff_self
- \+/\- *lemma* disjoint.symm_diff_eq_sup
- \+/\- *lemma* disjoint_symm_diff_inf
- \+/\- *lemma* inf_symm_diff_distrib_left
- \+/\- *lemma* inf_symm_diff_distrib_right
- \+/\- *lemma* inf_symm_diff_symm_diff
- \+/\- *lemma* is_compl.symm_diff_eq_top
- \+/\- *lemma* sdiff_symm_diff'
- \+/\- *lemma* sdiff_symm_diff
- \+/\- *lemma* sdiff_symm_diff_self
- \+/\- *lemma* sup_sdiff_symm_diff
- \+/\- *lemma* symm_diff_assoc
- \+/\- *lemma* symm_diff_bot
- \+/\- *lemma* symm_diff_comm
- \+/\- *lemma* symm_diff_compl_self
- \+/\- *lemma* symm_diff_eq
- \+/\- *lemma* symm_diff_eq_bot
- \+/\- *lemma* symm_diff_eq_left
- \+/\- *lemma* symm_diff_eq_right
- \+/\- *lemma* symm_diff_eq_sup
- \+/\- *lemma* symm_diff_eq_sup_sdiff_inf
- \+/\- *lemma* symm_diff_eq_top_iff
- \+/\- *lemma* symm_diff_eq_xor
- \+/\- *lemma* symm_diff_le_sup
- \+/\- *lemma* symm_diff_left_inj
- \+/\- *lemma* symm_diff_right_inj
- \+/\- *lemma* symm_diff_sdiff
- \+/\- *lemma* symm_diff_sdiff_left
- \+/\- *lemma* symm_diff_sdiff_right
- \+/\- *lemma* symm_diff_self
- \+/\- *lemma* symm_diff_symm_diff_inf
- \+/\- *lemma* symm_diff_symm_diff_self'
- \+/\- *lemma* symm_diff_symm_diff_self
- \+/\- *lemma* symm_diff_top
- \+/\- *lemma* top_symm_diff



## [2022-04-07 14:25:16](https://github.com/leanprover-community/mathlib/commit/ac5188d)
chore(algebra/char_p/{basic + algebra}): weaken assumptions for char_p_to_char_zero ([#13214](https://github.com/leanprover-community/mathlib/pull/13214))
The assumptions for lemma `char_p_to_char_zero` can be weakened, without changing the proof.
Since the weakening breaks up one typeclass assumption into two, when the lemma was applied with `@`, I inserted an extra `_`.  This happens twice: once in the file where the lemma is, and once in a separate file.
#### Estimated changes
Modified src/algebra/char_p/algebra.lean


Modified src/algebra/char_p/basic.lean
- \+/\- *lemma* char_p.char_p_to_char_zero



## [2022-04-07 14:25:13](https://github.com/leanprover-community/mathlib/commit/321d159)
feat(algebra/order/monoid): generalize, convert to `to_additive` and iff of `lt_or_lt_of_mul_lt_mul` ([#13192](https://github.com/leanprover-community/mathlib/pull/13192))
I converted a lemma showing
`m + n < a + b →  m < a ∨ n < b`
to the `to_additive` version of a lemma showing
`m * n < a * b →  m < a ∨ n < b`.
I also added a lemma showing `m * n < a * b ↔  m < a ∨ n < b` and its `to_additive` version.
#### Estimated changes
Modified src/algebra/order/monoid.lean
- \- *lemma* lt_or_lt_of_add_lt_add
- \+ *lemma* lt_or_lt_of_mul_lt_mul
- \+ *lemma* mul_lt_mul_iff_of_le_of_le



## [2022-04-07 12:26:52](https://github.com/leanprover-community/mathlib/commit/506ad31)
feat(order/monotone): simp lemmas for monotonicity in dual orders ([#13207](https://github.com/leanprover-community/mathlib/pull/13207))
Add 4 lemmas of the kind `antitone_to_dual_comp_iff`
Add their variants for `antitone_on`
Add their strict variants
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* forall₂_swap
- \+ *def* function.swap₂

Modified src/order/monotone.lean
- \+ *lemma* antitone_comp_of_dual_iff
- \+ *lemma* antitone_on_comp_of_dual_iff
- \+ *lemma* antitone_on_to_dual_comp_iff
- \+ *lemma* antitone_to_dual_comp_iff
- \+ *lemma* monotone_comp_of_dual_iff
- \+ *lemma* monotone_on_comp_of_dual_iff
- \+ *lemma* monotone_on_to_dual_comp_iff
- \+ *lemma* monotone_to_dual_comp_iff
- \+ *lemma* strict_anti_comp_of_dual_iff
- \+ *lemma* strict_anti_on_comp_of_dual_iff
- \+ *lemma* strict_anti_on_to_dual_comp_iff
- \+ *lemma* strict_anti_to_dual_comp_iff
- \+ *lemma* strict_mono_comp_of_dual_iff
- \+ *lemma* strict_mono_on_comp_of_dual_iff
- \+ *lemma* strict_mono_on_to_dual_comp_iff
- \+ *lemma* strict_mono_to_dual_comp_iff



## [2022-04-07 11:44:37](https://github.com/leanprover-community/mathlib/commit/be147af)
feat(ring_theory/graded_algebra/homogeneous_localization): homogeneous localization ring is local ([#13071](https://github.com/leanprover-community/mathlib/pull/13071))
showed that `local_ring (homogeneous_localization 𝒜 x)` from prime ideal `x`
#### Estimated changes
Modified src/ring_theory/graded_algebra/homogeneous_localization.lean
- \+ *lemma* homogeneous_localization.is_unit_iff_is_unit_val
- \+ *lemma* homogeneous_localization.val_mk'



## [2022-04-07 10:39:20](https://github.com/leanprover-community/mathlib/commit/3e4bf5d)
feat(order/symm_diff): More symmetric difference lemmas ([#13133](https://github.com/leanprover-community/mathlib/pull/13133))
A few more `symm_diff` lemmas.
#### Estimated changes



## [2022-04-07 07:05:52](https://github.com/leanprover-community/mathlib/commit/faa7e52)
chore(group_theory/index): Add `to_additive` ([#13191](https://github.com/leanprover-community/mathlib/pull/13191))
This PR adds `to_additive` to the rest of `group_theory/index.lean`.
#### Estimated changes
Modified src/group_theory/coset.lean


Modified src/group_theory/index.lean
- \+/\- *lemma* subgroup.index_eq_one
- \+/\- *lemma* subgroup.index_inf_le
- \+/\- *lemma* subgroup.index_inf_ne_zero
- \+/\- *lemma* subgroup.index_ne_zero_of_fintype
- \+/\- *lemma* subgroup.inf_relindex_left
- \+/\- *lemma* subgroup.inf_relindex_right
- \+/\- *lemma* subgroup.relindex_dvd_of_le_left
- \+/\- *lemma* subgroup.relindex_eq_relindex_sup
- \+/\- *lemma* subgroup.relindex_inf_le
- \+/\- *lemma* subgroup.relindex_inf_ne_zero
- \+/\- *lemma* subgroup.relindex_le_of_le_left
- \+/\- *lemma* subgroup.relindex_le_of_le_right
- \+/\- *lemma* subgroup.relindex_mul_index
- \+/\- *lemma* subgroup.relindex_mul_relindex
- \+/\- *lemma* subgroup.relindex_ne_zero_trans



## [2022-04-07 07:05:50](https://github.com/leanprover-community/mathlib/commit/45a8f6c)
feat(data/polynomial/basic): add simp lemmas X_mul_C and X_pow_mul_C ([#13163](https://github.com/leanprover-community/mathlib/pull/13163))
These lemmas are direct applications of `X_mul` and `X_pow_mul`.  However, their more general version cannot be `simp` lemmas since they form loops.  These versions do not, since they involve an explicit `C`.
I golfed slightly a proof in `linear_algebra.eigenspace` since it was timing out.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/polynomial.20op_C/near/277703846)
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.X_mul_C
- \+ *lemma* polynomial.X_pow_mul_C
- \+ *lemma* polynomial.X_pow_mul_assoc_C

Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/matrix/polynomial.lean




## [2022-04-07 07:05:49](https://github.com/leanprover-community/mathlib/commit/d047eb4)
feat(category_theory/monoidal): upgrades for monoidal equivalences ([#13158](https://github.com/leanprover-community/mathlib/pull/13158))
(Recall that a "monoidal equivalence" is a functor which is separately monoidal, and an equivalence.
This PR completes the work required to see this is the same as having a monoidal inverse, up to monoidal units and counits.)
* Shows that the unit and counit of a monoidal equivalence have a natural monoidal structure. 
* Previously, when transporting a monoidal structure across a (non-monoidal) equivalence,
we constructed directly the monoidal strength on the inverse functor. In the meantime, @b-mehta has provided a general construction for the monoidal strength on the inverse of any monoidal equivalence, so now we use that.
The proofs of `monoidal_unit` and `monoidal_counit` in `category_theory/monoidal/natural_transformation.lean` are quite ugly. If anyone would like to golf these that would be lovely! :-)
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean
- \+ *lemma* category_theory.equivalence.as_equivalence_to_adjunction_counit
- \+ *lemma* category_theory.equivalence.as_equivalence_to_adjunction_unit

Modified src/category_theory/monoidal/functor.lean
- \- *lemma* category_theory.monoidal_inverse_to_functor

Modified src/category_theory/monoidal/natural_transformation.lean
- \+ *def* category_theory.monoidal_counit
- \+ *def* category_theory.monoidal_unit

Modified src/category_theory/monoidal/transport.lean
- \- *def* category_theory.monoidal.lax_from_transported



## [2022-04-07 07:05:48](https://github.com/leanprover-community/mathlib/commit/91db821)
feat(set_theory/cardinal): Upper bound on domain from upper bound on fibers ([#13147](https://github.com/leanprover-community/mathlib/pull/13147))
A uniform upper bound on fibers gives an upper bound on the domain.
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.mk_le_mk_mul_of_mk_preimage_le



## [2022-04-07 07:05:46](https://github.com/leanprover-community/mathlib/commit/409f5f2)
feat(probability/integration): Bochner integral of the product of independent functions ([#13140](https://github.com/leanprover-community/mathlib/pull/13140))
This is limited to real-valued functions, which is not very satisfactory but it is not clear (to me) what the most general version of each of those lemmas would be.
#### Estimated changes
Modified src/probability/integration.lean
- \+ *lemma* probability_theory.indep_fun.integrable_mul
- \+ *theorem* probability_theory.indep_fun.integral_mul_of_integrable
- \+ *lemma* probability_theory.indep_fun.integral_mul_of_nonneg
- \+ *lemma* probability_theory.lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun'
- \+/\- *lemma* probability_theory.lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun
- \+/\- *lemma* probability_theory.lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator



## [2022-04-07 07:05:45](https://github.com/leanprover-community/mathlib/commit/fabad7e)
feat(order/symm_diff): More symmetric difference lemmas ([#13133](https://github.com/leanprover-community/mathlib/pull/13133))
A few more `symm_diff` lemmas.
#### Estimated changes
Modified src/order/boolean_algebra.lean
- \+ *lemma* eq_of_sdiff_eq_sdiff
- \+ *lemma* inf_sdiff_distrib_left
- \+ *lemma* inf_sdiff_distrib_right
- \+ *lemma* inf_sdiff_right_comm
- \+ *lemma* sdiff_eq_comm
- \+ *lemma* sdiff_eq_symm
- \+ *lemma* sdiff_sdiff_eq_sdiff_sup
- \+ *lemma* sdiff_sdiff_le
- \+ *lemma* sdiff_sup_sdiff_cancel
- \- *theorem* sdiff_symm

Modified src/order/lattice.lean
- \+ *lemma* inf_inf_distrib_left
- \+ *lemma* inf_inf_distrib_right
- \+ *lemma* sup_sup_distrib_left
- \+ *lemma* sup_sup_distrib_right

Modified src/order/symm_diff.lean
- \- *lemma* disjoint.disjoint_symm_diff_of_disjoint
- \+ *lemma* inf_symm_diff_distrib_left
- \+ *lemma* inf_symm_diff_distrib_right
- \+ *lemma* inf_symm_diff_symm_diff
- \+ *lemma* sup_sdiff_symm_diff
- \+ *lemma* symm_diff_symm_diff_inf



## [2022-04-07 07:05:44](https://github.com/leanprover-community/mathlib/commit/2a74d4e)
feat(algebra/order/monoid): add eq_one_or_one_lt ([#13131](https://github.com/leanprover-community/mathlib/pull/13131))
Needed in LTE.
#### Estimated changes
Modified src/algebra/order/monoid.lean
- \+ *lemma* eq_one_or_one_lt



## [2022-04-07 07:05:40](https://github.com/leanprover-community/mathlib/commit/9eff8cb)
feat(group_theory/schreier): prove Schreier's lemma ([#13019](https://github.com/leanprover-community/mathlib/pull/13019))
This PR adds a proof of Schreier's lemma.
#### Estimated changes
Modified docs/overview.yaml


Added src/group_theory/schreier.lean
- \+ *lemma* subgroup.closure_mul_eq
- \+ *lemma* subgroup.closure_mul_eq_top



## [2022-04-07 07:05:37](https://github.com/leanprover-community/mathlib/commit/45e4e62)
feat(archive/100-theorems-list/37_solution_of_cubic): golf ([#13012](https://github.com/leanprover-community/mathlib/pull/13012))
Express one of the lemmas for the solution of the cubic as a giant `linear_combination` calculation.
#### Estimated changes
Modified archive/100-theorems-list/37_solution_of_cubic.lean




## [2022-04-07 06:05:46](https://github.com/leanprover-community/mathlib/commit/f0ee4c8)
feat(topology/metric_space): the product of bounded sets is bounded ([#13176](https://github.com/leanprover-community/mathlib/pull/13176))
Also add an `iff` version.
#### Estimated changes
Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* metric.bounded.left_of_prod
- \+ *lemma* metric.bounded.right_of_prod
- \+ *lemma* metric.bounded_prod
- \+ *lemma* metric.bounded_prod_of_nonempty



## [2022-04-07 00:57:22](https://github.com/leanprover-community/mathlib/commit/05820c5)
feat(archive/imo/imo2008_q4): golf using `linear_combination` ([#13209](https://github.com/leanprover-community/mathlib/pull/13209))
#### Estimated changes
Modified archive/imo/imo2008_q4.lean




## [2022-04-07 00:24:49](https://github.com/leanprover-community/mathlib/commit/c4ced3a)
feat(archive/imo/imo2005_q6): golf using `field_simp` ([#13206](https://github.com/leanprover-community/mathlib/pull/13206))
#### Estimated changes
Modified archive/imo/imo2005_q3.lean




## [2022-04-06 23:45:15](https://github.com/leanprover-community/mathlib/commit/cc28054)
feat(archive/imo/imo2001_q6): golf using `linear_combination` ([#13205](https://github.com/leanprover-community/mathlib/pull/13205))
#### Estimated changes
Modified archive/imo/imo2001_q6.lean




## [2022-04-06 15:26:14](https://github.com/leanprover-community/mathlib/commit/06bdd8b)
feat(geometry/manifold/tangent_bundle): adapt the definition to the new vector bundle definition ([#13199](https://github.com/leanprover-community/mathlib/pull/13199))
Also a few tweaks to simplify the defeq behavior of tangent spaces.
#### Estimated changes
Modified src/geometry/manifold/cont_mdiff.lean
- \+ *def* tangent_bundle.zero_section

Modified src/geometry/manifold/tangent_bundle.lean
- \+ *lemma* basic_smooth_vector_bundle_core.coord_change_continuous
- \+ *lemma* basic_smooth_vector_bundle_core.coord_change_smooth
- \+/\- *def* tangent_bundle.proj
- \+/\- *def* tangent_bundle
- \+/\- *def* tangent_space



## [2022-04-06 12:59:06](https://github.com/leanprover-community/mathlib/commit/138448a)
feat(algebra/parity): introduce `is_square` and, via `to_additive`, also `even` ([#13037](https://github.com/leanprover-community/mathlib/pull/13037))
This PR continues the refactor began in [#12882](https://github.com/leanprover-community/mathlib/pull/12882).  Now that most of the the even/odd lemmas are in the same file, I changed the definition of `even` to become the `to_additive` version of `is_square`.
The reason for the large number of files touched is that the definition of `even` actually changed, from being of the form `2 * n` to being of the form `n + n`.  Thus, I inserted appropriate `two_mul`s and `even_iff_two_dvd`s in a few places where the defeq to the divisibility by 2 was exploited.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/even.2Fodd)
#### Estimated changes
Modified archive/100-theorems-list/45_partition.lean


Modified archive/100-theorems-list/70_perfect_numbers.lean


Modified archive/imo/imo2013_q1.lean


Modified src/algebra/parity.lean
- \- *lemma* add_monoid_hom.even
- \- *lemma* even.add_even
- \- *lemma* even.sub_even
- \- *def* even
- \+/\- *lemma* even_abs
- \+ *lemma* even_iff_exists_two_mul
- \+/\- *lemma* even_iff_two_dvd
- \- *theorem* even_neg
- \+/\- *lemma* even_neg_two
- \+/\- *lemma* even_two
- \+/\- *lemma* even_two_mul
- \- *lemma* even_zero
- \+ *lemma* is_square.div_is_square
- \+ *lemma* is_square.map
- \+ *lemma* is_square.mul_is_square
- \+ *def* is_square
- \+ *lemma* is_square_iff_exists_sq
- \+ *lemma* is_square_inv
- \+ *lemma* is_square_mul_self
- \+ *lemma* is_square_one
- \+ *lemma* is_square_op_iff
- \+ *lemma* is_square_sq
- \+/\- *lemma* odd_abs

Modified src/algebra/periodic.lean


Modified src/analysis/convex/specific_functions.lean


Modified src/combinatorics/simple_graph/degree_sum.lean


Modified src/combinatorics/simple_graph/matching.lean


Modified src/data/int/parity.lean
- \+/\- *lemma* int.div_two_mul_two_of_even
- \+/\- *lemma* int.two_mul_div_two_of_even

Modified src/data/nat/parity.lean
- \+/\- *lemma* nat.div_two_mul_two_of_even
- \+/\- *lemma* nat.two_mul_div_two_of_even

Modified src/group_theory/specific_groups/alternating.lean


Modified src/number_theory/number_field.lean
- \+/\- *lemma* int.not_is_field

Modified src/number_theory/primorial.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/ring_theory/polynomial/cyclotomic/eval.lean




## [2022-04-06 06:48:08](https://github.com/leanprover-community/mathlib/commit/6930ad5)
feat(topology/continuous_function/zero_at_infty): add the type of continuous functions vanishing at infinity ([#12907](https://github.com/leanprover-community/mathlib/pull/12907))
This adds the type of of continuous functions vanishing at infinity (`zero_at_infty`) with the localized notation `C₀(α, β)` (we also allow `α →C₀ β` but the former has higher priority). This type is defined when `α` and `β` are topological spaces and `β` has a zero element. Elements of this type are continuous functions `f` with the additional property that `tendsto f (cocompact α) (𝓝 0)`. Here we attempt to follow closely the recent hom refactor and so we also create the type class `zero_at_infty_continuous_map_class`.
Various algebraic structures are instantiated on `C₀(α, β)` when corresponding structures exist on `β`. When `β` is a metric space, there is a natural inclusion `zero_at_infty_continuous_map.to_bcf : C₀(α, β) → α →ᵇ β`, which induces a metric space structure on `C₀(α, β)`, and the range of this map is closed. Therefore, when `β` is complete, `α →ᵇ β` is complete, and hence so is `C₀(α, β)`.
- [x] depends on: [#12894](https://github.com/leanprover-community/mathlib/pull/12894)
#### Estimated changes
Added src/topology/continuous_function/zero_at_infty.lean
- \+ *lemma* zero_at_infty_continuous_map.add_apply
- \+ *lemma* zero_at_infty_continuous_map.bounded_image
- \+ *lemma* zero_at_infty_continuous_map.bounded_range
- \+ *lemma* zero_at_infty_continuous_map.closed_range_to_bcf
- \+ *lemma* zero_at_infty_continuous_map.coe_add
- \+ *lemma* zero_at_infty_continuous_map.coe_mul
- \+ *lemma* zero_at_infty_continuous_map.coe_neg
- \+ *lemma* zero_at_infty_continuous_map.coe_nsmul_rec
- \+ *lemma* zero_at_infty_continuous_map.coe_smul
- \+ *lemma* zero_at_infty_continuous_map.coe_sub
- \+ *lemma* zero_at_infty_continuous_map.coe_to_continuous_fun
- \+ *lemma* zero_at_infty_continuous_map.coe_zero
- \+ *lemma* zero_at_infty_continuous_map.coe_zsmul_rec
- \+ *def* zero_at_infty_continuous_map.continuous_map.lift_zero_at_infty
- \+ *lemma* zero_at_infty_continuous_map.dist_to_bcf_eq_dist
- \+ *lemma* zero_at_infty_continuous_map.eq_of_empty
- \+ *lemma* zero_at_infty_continuous_map.ext
- \+ *lemma* zero_at_infty_continuous_map.isometry_to_bcf
- \+ *lemma* zero_at_infty_continuous_map.mul_apply
- \+ *lemma* zero_at_infty_continuous_map.neg_apply
- \+ *lemma* zero_at_infty_continuous_map.smul_apply
- \+ *lemma* zero_at_infty_continuous_map.sub_apply
- \+ *lemma* zero_at_infty_continuous_map.tendsto_iff_tendsto_uniformly
- \+ *def* zero_at_infty_continuous_map.to_bcf
- \+ *lemma* zero_at_infty_continuous_map.to_bounded_continuous_function_injective
- \+ *lemma* zero_at_infty_continuous_map.zero_apply
- \+ *def* zero_at_infty_continuous_map.zero_at_infty_continuous_map_class.of_compact

Modified src/topology/subset_properties.lean
- \+ *lemma* filter.cocompact_eq_bot



## [2022-04-06 03:42:41](https://github.com/leanprover-community/mathlib/commit/2841aad)
chore(scripts): update nolints.txt ([#13193](https://github.com/leanprover-community/mathlib/pull/13193))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-04-06 01:48:21](https://github.com/leanprover-community/mathlib/commit/2e8d269)
feat(data/nat/factorization): Generalize natural factorization recursors. ([#12973](https://github.com/leanprover-community/mathlib/pull/12973))
Switches `rec_on_prime_pow` precondition to allow use of `0 < n`, and strengthens correspondingly `rec_on_pos_prime_pos_coprime` and `rec_on_prime_coprime`.
#### Estimated changes
Modified src/data/nat/factorization.lean


Modified src/data/nat/gcd.lean
- \+/\- *lemma* nat.coprime_pow_left_iff
- \+/\- *lemma* nat.coprime_pow_right_iff

Modified src/number_theory/von_mangoldt.lean




## [2022-04-05 23:46:08](https://github.com/leanprover-community/mathlib/commit/2504a2b)
chore(data/list/basic): remove axiom of choice assumption in some lemmas ([#13189](https://github.com/leanprover-community/mathlib/pull/13189))
#### Estimated changes
Modified src/data/list/basic.lean




## [2022-04-05 21:26:16](https://github.com/leanprover-community/mathlib/commit/a841361)
refactor(topology/vector_bundle): redefine ([#13175](https://github.com/leanprover-community/mathlib/pull/13175))
The definition of topological vector bundle in [#4658](https://github.com/leanprover-community/mathlib/pull/4658) was (inadvertently) a nonstandard definition, which agreed in finite dimension with the usual definition but not in infinite dimension.
Specifically, it omitted the compatibility condition that for a vector bundle over `B` with model fibre `F`, the transition function `B → F ≃L[R] F` associated to any pair of trivializations be continuous, with respect to to the norm topology on `F →L[R] F`.  (The transition function is automatically continuous with respect to the topology of pointwise convergence, which is why this works in finite dimension.  The discrepancy between these conditions in infinite dimension turns out to be a [classic](https://mathoverflow.net/questions/4943/vector-bundle-with-non-smoothly-varying-transition-functions/4997[#4997](https://github.com/leanprover-community/mathlib/pull/4997))
[gotcha](https://mathoverflow.net/questions/54550/the-third-axiom-in-the-definition-of-infinite-dimensional-vector-bundles-why/54706[#54706](https://github.com/leanprover-community/mathlib/pull/54706)).)
We refactor to add this compatibility condition to the definition of topological vector bundle, and to verify this condition in the existing examples of topological vector bundles (construction via a cocycle, direct sum of vector bundles, tangent bundle).
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable_within_at.antimono
- \+ *lemma* fderiv_within_subset'
- \+ *lemma* has_fderiv_within_at.antimono

Modified src/data/set/prod.lean
- \+ *lemma* set.prod_eq_iff_eq

Modified src/geometry/manifold/tangent_bundle.lean


Modified src/topology/vector_bundle.lean
- \+ *def* continuous_transitions
- \+ *lemma* topological_vector_bundle.continuous_on_coord_change
- \+ *def* topological_vector_bundle.coord_change
- \+ *lemma* topological_vector_bundle.trans_eq_coord_change
- \+ *lemma* topological_vector_bundle.trivial_topological_vector_bundle.trivialization_source
- \+ *lemma* topological_vector_bundle.trivial_topological_vector_bundle.trivialization_target
- \+ *lemma* topological_vector_bundle.trivialization.comp_continuous_linear_equiv_at_eq_coord_change
- \+/\- *lemma* topological_vector_bundle.trivialization.prod_apply



## [2022-04-05 19:36:21](https://github.com/leanprover-community/mathlib/commit/7ec52a1)
chore(algebraic_topology/simplex_category): removed ulift ([#13183](https://github.com/leanprover-community/mathlib/pull/13183))
#### Estimated changes
Modified src/algebraic_topology/alternating_face_map_complex.lean
- \+/\- *lemma* algebraic_topology.map_alternating_face_map_complex

Modified src/algebraic_topology/simplex_category.lean
- \+/\- *def* simplex_category.const
- \+/\- *lemma* simplex_category.const_comp
- \+/\- *lemma* simplex_category.epi_iff_surjective
- \+/\- *lemma* simplex_category.eq_id_of_epi
- \+/\- *lemma* simplex_category.eq_id_of_is_iso
- \+/\- *lemma* simplex_category.eq_id_of_mono
- \+/\- *lemma* simplex_category.ext
- \+/\- *def* simplex_category.hom.comp
- \+/\- *lemma* simplex_category.hom.ext
- \+/\- *def* simplex_category.hom.id
- \+/\- *def* simplex_category.hom.mk
- \+/\- *lemma* simplex_category.hom.mk_to_order_hom
- \+/\- *lemma* simplex_category.hom.mk_to_order_hom_apply
- \+/\- *def* simplex_category.hom.to_order_hom
- \+/\- *lemma* simplex_category.hom.to_order_hom_mk
- \+/\- *lemma* simplex_category.is_iso_of_bijective
- \+/\- *def* simplex_category.is_skeleton_of
- \+/\- *lemma* simplex_category.iso_eq_iso_refl
- \+/\- *def* simplex_category.len
- \+/\- *lemma* simplex_category.len_le_of_epi
- \+/\- *lemma* simplex_category.len_le_of_mono
- \+/\- *def* simplex_category.mk
- \+/\- *lemma* simplex_category.mk_len
- \+/\- *theorem* simplex_category.mono_iff_injective
- \+/\- *def* simplex_category.order_iso_of_iso
- \+/\- *lemma* simplex_category.skeletal
- \+/\- *def* simplex_category.skeletal_functor
- \+/\- *def* simplex_category.truncated.inclusion
- \+/\- *def* simplex_category.truncated
- \+/\- *def* simplex_category

Modified src/algebraic_topology/simplicial_object.lean
- \+/\- *def* category_theory.cosimplicial_object.augmented.whiskering
- \+/\- *def* category_theory.cosimplicial_object.augmented.whiskering_obj
- \+/\- *def* category_theory.cosimplicial_object.truncated.whiskering
- \+/\- *def* category_theory.cosimplicial_object.truncated
- \+/\- *def* category_theory.cosimplicial_object.whiskering
- \+/\- *def* category_theory.cosimplicial_object
- \+/\- *def* category_theory.simplicial_object.augmented.whiskering
- \+/\- *def* category_theory.simplicial_object.augmented.whiskering_obj
- \+/\- *def* category_theory.simplicial_object.truncated.whiskering
- \+/\- *def* category_theory.simplicial_object.truncated
- \+/\- *def* category_theory.simplicial_object.whiskering
- \+/\- *def* category_theory.simplicial_object



## [2022-04-05 19:36:20](https://github.com/leanprover-community/mathlib/commit/960abb5)
chore(algebra/monoid_algebra/grading): fix slow elaboration ([#13169](https://github.com/leanprover-community/mathlib/pull/13169))
There were a couple of lemmas in this file taking multiple seconds to elaborate.  Apart from `squeeze_dsimps`, the main change in this PR is to help the elaborator unfold certain definitions (that it originally did unfold, but only after multiple seconds of trying to unfold other things), by replacing proofs with `by simpa only [some_unfolding_lemma] using the_original_proof`.
The main alternative I discovered for the `simpa` changes was to strategically mark certain definitions irreducible. Those definitions needed to be unfolded in other places in this file, and it's less obviously connected to the source of the slowness: we might keep around the `local attribute [irreducible]` lines even if it's not needed after a refactor.
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Slow.20defeqs.20in.20.60algebra.2Fmonoid_algebra.2Fgrading.2Elean.60
#### Estimated changes
Modified src/algebra/monoid_algebra/grading.lean




## [2022-04-05 19:36:19](https://github.com/leanprover-community/mathlib/commit/d34cbcf)
refactor(algebra/homology, category_theory/*): declassify exactness ([#13153](https://github.com/leanprover-community/mathlib/pull/13153))
Having  `exact` be a class was very often somewhat inconvenient, so many lemmas took it as a normal argument while many others had it as a typeclass argument. This PR removes this inconsistency by downgrading `exact` to a structure. We lose very little by doing this, and using typeclass inference as a Prolog-like "automatic theorem prover" is rarely a good idea anyway.
#### Estimated changes
Modified src/algebra/homology/exact.lean
- \+/\- *lemma* category_theory.comp_eq_zero_of_exact
- \+ *lemma* category_theory.exact_comp_hom_inv_comp
- \+ *lemma* category_theory.exact_comp_inv_hom_comp
- \+/\- *lemma* category_theory.exact_comp_mono
- \+/\- *lemma* category_theory.exact_epi_comp
- \+ *lemma* category_theory.exact_epi_zero
- \+ *lemma* category_theory.exact_of_zero
- \+ *lemma* category_theory.exact_zero_mono
- \+/\- *lemma* category_theory.fork_ι_comp_cofork_π
- \- *lemma* category_theory.functor.exact_of_exact_map'
- \+/\- *lemma* category_theory.kernel_comp_cokernel
- \+/\- *lemma* category_theory.kernel_subobject_arrow_eq_zero_of_exact_zero_left
- \+/\- *lemma* category_theory.kernel_ι_eq_zero_of_exact_zero_left

Modified src/category_theory/abelian/diagram_lemmas/four.lean


Modified src/category_theory/abelian/exact.lean
- \+ *lemma* category_theory.abelian.exact.op
- \+ *lemma* category_theory.abelian.exact.unop
- \+/\- *def* category_theory.abelian.is_colimit_coimage
- \+/\- *def* category_theory.abelian.is_colimit_image
- \+/\- *def* category_theory.abelian.is_limit_image'
- \+/\- *def* category_theory.abelian.is_limit_image

Modified src/category_theory/abelian/homology.lean


Modified src/category_theory/abelian/injective_resolution.lean


Modified src/category_theory/abelian/pseudoelements.lean
- \+/\- *theorem* category_theory.abelian.pseudoelement.pseudo_exact_of_exact

Modified src/category_theory/abelian/right_derived.lean


Modified src/category_theory/preadditive/injective.lean
- \+/\- *def* category_theory.injective.exact.desc

Modified src/category_theory/preadditive/injective_resolution.lean
- \+ *lemma* category_theory.InjectiveResolution.complex_d_comp
- \+ *lemma* category_theory.InjectiveResolution.ι_f_zero_comp_complex_d

Modified src/category_theory/preadditive/projective.lean


Modified src/category_theory/preadditive/projective_resolution.lean
- \+ *lemma* category_theory.ProjectiveResolution.complex_d_comp_π_f_zero
- \+ *lemma* category_theory.ProjectiveResolution.complex_d_succ_comp



## [2022-04-05 19:36:18](https://github.com/leanprover-community/mathlib/commit/427aae3)
chore(algebra/*): generalisation linter (replacing ring with non_assoc_ring) ([#13106](https://github.com/leanprover-community/mathlib/pull/13106))
#### Estimated changes
Modified src/algebra/big_operators/multiset.lean


Modified src/algebra/big_operators/pi.lean
- \+/\- *lemma* ring_hom.functions_ext

Modified src/algebra/big_operators/ring.lean


Modified src/algebra/char_zero.lean


Modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* bit0_mul
- \+/\- *lemma* bit1_mul
- \+/\- *lemma* mul_bit0
- \+/\- *lemma* mul_bit1
- \+/\- *theorem* nsmul_eq_mul'
- \+/\- *theorem* nsmul_eq_mul
- \+/\- *theorem* zsmul_eq_mul

Modified src/algebra/ring/equiv.lean


Modified src/ring_theory/subring/basic.lean




## [2022-04-05 19:00:50](https://github.com/leanprover-community/mathlib/commit/e510b20)
feat(group_theory/index): Index of intersection ([#13186](https://github.com/leanprover-community/mathlib/pull/13186))
This PR adds `relindex_inf_le` and `index_inf_le`, which are companion lemmas to `relindex_inf_ne_zero` and `index_inf_ne_zero`.
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* subgroup.index_inf_le
- \+ *lemma* subgroup.relindex_inf_le



## [2022-04-05 16:22:19](https://github.com/leanprover-community/mathlib/commit/cf131e1)
feat(data/complex/exponential): add `real.cos_abs` ([#13177](https://github.com/leanprover-community/mathlib/pull/13177))
#### Estimated changes
Modified src/data/complex/exponential.lean
- \+ *lemma* real.cos_abs



## [2022-04-05 16:22:18](https://github.com/leanprover-community/mathlib/commit/b011b0e)
feat(ring_theory/unique_factorization_domain): The only divisors of prime powers are prime powers. ([#12799](https://github.com/leanprover-community/mathlib/pull/12799))
The only divisors of prime powers are prime powers in the associates monoid of an UFD.
#### Estimated changes
Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* associates.count_eq_zero_of_ne
- \+ *lemma* associates.count_factors_eq_find_of_dvd_pow
- \+ *lemma* associates.count_le_count_of_factors_le
- \+ *lemma* associates.count_le_count_of_le
- \+ *theorem* associates.eq_pow_count_factors_of_dvd_pow
- \+ *theorem* associates.eq_pow_find_of_dvd_irreducible_pow



## [2022-04-05 14:51:10](https://github.com/leanprover-community/mathlib/commit/fd1861c)
fix(tactic/ring): `ring_nf` should descend into subexpressions ([#12430](https://github.com/leanprover-community/mathlib/pull/12430))
Since the lambda passed to `ext_simp_core` was returning `ff`, this means the simplifier didn't descend into subexpressions, so `ring_nf` only tried to use the Horner normal form if the head symbol of the goal/hypothesis was `+`, `*`, `-` or `^`. In particular, since there are no such operations on `Sort`, `ring_nf` was exactly equivalent to `simp only [horner.equations._eqn_1, add_zero, one_mul, pow_one, neg_mul, add_neg_eq_sub]`. Toggling the return value means `ring_nf` will try to simplify all subexpressions, including the left hand side and right hand side of an equality.
@alexjbest discovered the MWE included in `test/ring.lean` while trying to use `ring_nf` to simplify a complicated expression.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean


Modified src/data/zmod/basic.lean


Modified src/tactic/ring.lean


Modified test/ring.lean




## [2022-04-05 12:54:02](https://github.com/leanprover-community/mathlib/commit/91dd3b1)
chore(ring_theory/integral_domain): dedup, tidy ([#13180](https://github.com/leanprover-community/mathlib/pull/13180))
#### Estimated changes
Modified src/field_theory/finite/basic.lean


Modified src/ring_theory/integral_domain.lean
- \- *def* field_of_is_domain



## [2022-04-05 12:54:00](https://github.com/leanprover-community/mathlib/commit/da132ec)
feat(*): define subobject classes from submonoid up to subfield ([#11750](https://github.com/leanprover-community/mathlib/pull/11750))
The next part of my big refactoring plans: subobject classes in the same style as morphism classes.
This PR introduces the following subclasses of `set_like`:
 * `one_mem_class`, `zero_mem_class`, `mul_mem_class`, `add_mem_class`, `inv_mem_class`, `neg_mem_class`
 * `submonoid_class`, `add_submonoid_class`
 * `subgroup_class`, `add_subgroup_class`
 * `subsemiring_class`, `subring_class`, `subfield_class`
The main purpose of this refactor is that we can replace the wide variety of lemmas like `{add_submonoid,add_subgroup,subring,subfield,submodule,subwhatever}.{prod,sum}_mem` with a single `prod_mem` lemma that is generic over all types `B` that extend `submonoid`:
```lean
@[to_additive]
lemma prod_mem {M : Type*} [comm_monoid M] [set_like B M] [submonoid_class B M]
  {ι : Type*} {t : finset ι} {f : ι → M} (h : ∀c ∈ t, f c ∈ S) : ∏ c in t, f c ∈ S
```
## API changes
 * When you extend a `struct subobject`, make sure to create a corresponding `subobject_class` instance.
## Upcoming PRs
This PR splits out the first part of [#11545](https://github.com/leanprover-community/mathlib/pull/11545), namely defining the subobject classes. I am planning these follow-up PRs for further parts of [#11545](https://github.com/leanprover-community/mathlib/pull/11545):
 - [ ] make the subobject consistently implicit in `{add,mul}_mem` [#11758](https://github.com/leanprover-community/mathlib/pull/11758)
 - [ ] remove duplicate instances like `subgroup.to_group` (replaced by the `subgroup_class.to_subgroup` instances that are added by this PR) [#11759](https://github.com/leanprover-community/mathlib/pull/11759)
 - [ ] further deduplication such as `finsupp_sum_mem`
## Subclassing `set_like`
Contrary to mathlib's typical subclass pattern, we don't extend `set_like`, but take a `set_like` instance parameter:
```lean
class one_mem_class (S : Type*) (M : out_param $ Type*) [has_one M] [set_like S M] :=
(one_mem : ∀ (s : S), (1 : M) ∈ s)
```
instead of:
```lean
class one_mem_class (S : Type*) (M : out_param $ Type*) [has_one M]
  extends set_like S M :=
(one_mem : ∀ (s : S), (1 : M) ∈ s)
```
The main reason is that this avoids some big defeq checks when typechecking e.g. `x * y : s`, where `s : S` and `[comm_group G] [subgroup_class S G]`. Namely, the type `coe_sort s` could be given by `subgroup_class → @@submonoid_class _ _ (comm_group.to_group.to_monoid) → set_like → has_coe_to_sort` or by `subgroup_class → @@submonoid_class _ _ (comm_group.to_comm_monoid.to_monoid) → set_like → has_coe_to_sort`. When checking that `has_mul` on the first type is the same as `has_mul` on the second type, those two inheritance paths are unified many times over ([sometimes exponentially many](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Why.20is.20.60int.2Ecast_abs.60.20so.20slow.3F/near/266945077)). So it's important to keep the size of types small, and therefore we avoid `extends`-based inheritance.
## Defeq fixes
Adding instances like `subgroup_class.to_group` means that there are now two (defeq) group instances for `subgroup`. This makes some code more fragile, until we can replace `subgroup.to_group` with its more generic form in a follow-up PR. Especially when taking subgroups of subgroups I needed to help the elaborator in a few places. These should be minimally invasive for other uses of the code.
## Timeout fixes
Some of the leaf files started timing out, so I made a couple of fixes. Generally these can be classed as:
 * `squeeze_simps`
 * Give inheritance `subX_class S M` → `X s` (where `s : S`) a lower prority than `Y s` → `X s` so that `subY_class S M` → `Y s` → `X s` is preferred over `subY_class S M` → `subX_class S M` → `X s`. This addresses slow unifications when `x : s`, `s` is a submonoid of `t`, which is itself a subgroup of `G`: existing code expects to go `subgroup → group → monoid`, which got changed to `subgroup_class → submonoid_class → monoid`; when this kind of unification issue appears in your type this results in slow unification. By tweaking the priorities, we help the elaborator find our preferred instance, avoiding the big defeq checks. (The real fix should of course be to fix the unifier so it doesn't become exponential in these kinds of cases.)
 * Split a long proof with duplication into smaller parts. This was basically my last resort.
I decided to bump the limit for the `fails_quickly` linter for `measure_theory.Lp_meas.complete_space`, which apparently just barely goes over this limit now. The time difference was about 10%-20% for that specific instance.
#### Estimated changes
Modified src/algebra/algebra/subalgebra/basic.lean


Modified src/algebra/lie/subalgebra.lean


Modified src/algebra/lie/submodule.lean


Modified src/algebra/module/submodule.lean
- \+/\- *lemma* submodule.neg_mem

Modified src/analysis/inner_product_space/l2_space.lean


Modified src/field_theory/galois.lean


Modified src/field_theory/intermediate_field.lean


Modified src/field_theory/subfield.lean


Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup_class.coe_div
- \+ *lemma* subgroup_class.coe_inclusion
- \+ *lemma* subgroup_class.coe_inv
- \+ *lemma* subgroup_class.coe_pow
- \+ *theorem* subgroup_class.coe_subtype
- \+ *lemma* subgroup_class.coe_zpow
- \+ *theorem* subgroup_class.div_mem
- \+ *lemma* subgroup_class.div_mem_comm_iff
- \+ *lemma* subgroup_class.exists_inv_mem_iff_exists_mem
- \+ *def* subgroup_class.inclusion
- \+ *theorem* subgroup_class.inv_coe_set
- \+ *theorem* subgroup_class.inv_mem_iff
- \+ *lemma* subgroup_class.mul_mem_cancel_left
- \+ *lemma* subgroup_class.mul_mem_cancel_right
- \+ *def* subgroup_class.subtype
- \+ *lemma* subgroup_class.subtype_comp_inclusion
- \+ *lemma* subgroup_class.zpow_mem

Modified src/group_theory/submonoid/basic.lean
- \+ *lemma* pow_mem

Modified src/group_theory/submonoid/membership.lean
- \+/\- *theorem* submonoid.coe_list_prod
- \+/\- *lemma* submonoid.list_prod_mem
- \+ *theorem* submonoid_class.coe_finset_prod
- \+ *theorem* submonoid_class.coe_list_prod
- \+ *theorem* submonoid_class.coe_multiset_prod
- \+ *lemma* submonoid_class.list_prod_mem
- \+ *lemma* submonoid_class.multiset_prod_mem
- \+ *lemma* submonoid_class.prod_mem

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* submonoid_class.coe_eq_one
- \+ *lemma* submonoid_class.coe_mul
- \+ *lemma* submonoid_class.coe_one
- \+ *lemma* submonoid_class.coe_pow
- \+ *theorem* submonoid_class.coe_subtype
- \+ *lemma* submonoid_class.mk_mul_mk
- \+ *lemma* submonoid_class.mk_pow
- \+ *lemma* submonoid_class.mul_def
- \+ *lemma* submonoid_class.one_def
- \+ *def* submonoid_class.subtype

Modified src/group_theory/sylow.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/integral/bochner.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/norm.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/subring/basic.lean
- \+ *lemma* subring_class.coe_int_cast
- \+ *lemma* subring_class.coe_int_mem
- \+ *lemma* subring_class.coe_nat_cast
- \+ *theorem* subring_class.coe_subtype
- \+ *def* subring_class.subtype

Modified src/ring_theory/subsemiring/basic.lean
- \+ *lemma* subsemiring_class.coe_nat_mem
- \+ *lemma* subsemiring_class.coe_pow
- \+ *theorem* subsemiring_class.coe_subtype
- \+ *def* subsemiring_class.subtype

Modified src/ring_theory/trace.lean


Modified src/tactic/lint/type_classes.lean




## [2022-04-05 11:06:01](https://github.com/leanprover-community/mathlib/commit/220f71b)
refactor(data/polynomial/basic): overhaul all the misnamed `to_finsupp` lemmas ([#13139](https://github.com/leanprover-community/mathlib/pull/13139))
`zero_to_finsupp` was the statement `of_finsupp 0 = 0`, which doesn't match the name at all.
This change:
* Renames all those lemmas to `of_finsupp_<foo>`
* Changes the direction of `add_to_finsupp` to be `of_finsupp_add`, so the statement is now `of_finsupp (a + b) = _`
* Adds the missing `to_finsupp_<foo>` lemmas
* Uses the new lemmas to golf the semiring and ring instances
The renames include:
* `zero_to_finsupp` → `of_finsupp_zero`
* `one_to_finsupp` → `of_finsupp_one`
* `add_to_finsupp` → `of_finsupp_add` (direction reversed)
* `neg_to_finsupp` → `of_finsupp_neg` (direction reversed)
* `mul_to_finsupp` → `of_finsupp_mul` (direction reversed)
* `smul_to_finsupp` → `of_finsupp_smul` (direction reversed)
* `sum_to_finsupp` → `of_finsupp_sum` (direction reversed)
* `to_finsupp_iso_monomial` → `to_finsupp_monomial`
* `to_finsupp_iso_symm_single` → `of_finsupp_single`
* `eval₂_to_finsupp_eq_lift_nc` → `eval₂_of_finsupp`
The new lemmas include:
* `of_finsupp_sub`
* `of_finsupp_pow`
* `of_finsupp_erase`
* `of_finsupp_algebra_map`
* `of_finsupp_eq_zero`
* `of_finsupp_eq_one`
* `to_finsupp_zero`
* `to_finsupp_one`
* `to_finsupp_add`
* `to_finsupp_neg`
* `to_finsupp_sub`
* `to_finsupp_mul`
* `to_finsupp_pow`
* `to_finsupp_erase`
* `to_finsupp_algebra_map`
* `to_finsupp_eq_zero`
* `to_finsupp_eq_one`
* `to_finsupp_C`
Note that by marking things like `support` and `coeff` as `@[simp]`, they behave as if they were `support_of_finsupp` or `coeff_of_finsupp` lemma. By making `coeff` pattern match fewer arguments, we encourage it to apply more keenly.
Neither lemma will fire unless our expression contains `polynomial.of_finsupp`.
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* polynomial.of_finsupp_algebra_map
- \+ *lemma* polynomial.to_finsupp_algebra_map

Modified src/data/polynomial/basic.lean
- \- *lemma* polynomial.add_to_finsupp
- \+/\- *def* polynomial.coeff
- \- *lemma* polynomial.mul_to_finsupp
- \- *lemma* polynomial.neg_to_finsupp
- \+ *lemma* polynomial.of_finsupp_add
- \+ *lemma* polynomial.of_finsupp_eq_one
- \+ *lemma* polynomial.of_finsupp_eq_zero
- \+ *lemma* polynomial.of_finsupp_erase
- \+ *lemma* polynomial.of_finsupp_inj
- \+ *lemma* polynomial.of_finsupp_mul
- \+ *lemma* polynomial.of_finsupp_neg
- \+ *lemma* polynomial.of_finsupp_one
- \+ *lemma* polynomial.of_finsupp_pow
- \+ *lemma* polynomial.of_finsupp_single
- \+ *lemma* polynomial.of_finsupp_smul
- \+ *lemma* polynomial.of_finsupp_sub
- \+ *lemma* polynomial.of_finsupp_sum
- \+ *lemma* polynomial.of_finsupp_zero
- \- *lemma* polynomial.one_to_finsupp
- \- *lemma* polynomial.smul_to_finsupp
- \- *lemma* polynomial.sum_to_finsupp
- \+ *lemma* polynomial.support_of_finsupp
- \+ *lemma* polynomial.to_finsupp_C
- \+ *lemma* polynomial.to_finsupp_add
- \+ *lemma* polynomial.to_finsupp_eq_one
- \+ *lemma* polynomial.to_finsupp_eq_zero
- \+ *lemma* polynomial.to_finsupp_erase
- \+ *lemma* polynomial.to_finsupp_inj
- \+ *lemma* polynomial.to_finsupp_injective
- \- *lemma* polynomial.to_finsupp_iso_monomial
- \- *lemma* polynomial.to_finsupp_iso_symm_single
- \+ *lemma* polynomial.to_finsupp_monomial
- \+ *lemma* polynomial.to_finsupp_mul
- \+ *lemma* polynomial.to_finsupp_neg
- \+ *lemma* polynomial.to_finsupp_one
- \+ *lemma* polynomial.to_finsupp_pow
- \+ *lemma* polynomial.to_finsupp_smul
- \+ *lemma* polynomial.to_finsupp_sub
- \+ *lemma* polynomial.to_finsupp_sum
- \+ *lemma* polynomial.to_finsupp_zero
- \- *lemma* polynomial.zero_to_finsupp

Modified src/data/polynomial/coeff.lean


Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.eval₂_of_finsupp
- \- *lemma* polynomial.eval₂_to_finsupp_eq_lift_nc

Modified src/data/polynomial/monomial.lean


Modified src/data/polynomial/reverse.lean


Modified src/ring_theory/mv_polynomial/basic.lean


Modified src/ring_theory/polynomial/basic.lean




## [2022-04-05 11:06:00](https://github.com/leanprover-community/mathlib/commit/c108ed4)
feat(topology/algebra): add several lemmas ([#13135](https://github.com/leanprover-community/mathlib/pull/13135))
* add `closure_smul`, `interior_smul`, and `closure_smul₀`;
* add `is_open.mul_closure` and `is_open.closure_mul`.
#### Estimated changes
Modified src/topology/algebra/const_mul_action.lean
- \+ *lemma* closure_smul
- \+ *lemma* closure_smul₀
- \+/\- *def* homeomorph.smul
- \+ *lemma* interior_smul

Modified src/topology/algebra/group.lean
- \+ *lemma* is_open.closure_mul
- \+ *lemma* is_open.mul_closure



## [2022-04-05 11:05:59](https://github.com/leanprover-community/mathlib/commit/bb4099b)
feat(analysis/normed/normed_field): add abs_le_floor_nnreal_iff ([#13130](https://github.com/leanprover-community/mathlib/pull/13130))
From LTE.
#### Estimated changes
Modified src/analysis/normed/normed_field.lean
- \+ *lemma* int.abs_le_floor_nnreal_iff



## [2022-04-05 11:05:57](https://github.com/leanprover-community/mathlib/commit/c7626b7)
feat(analysis/calculus/fderiv_analytic): an analytic function is smooth ([#13127](https://github.com/leanprover-community/mathlib/pull/13127))
This basic fact was missing from the library, but all the nontrivial maths were already there, we are just adding the necessary glue.
Also, replace `ac_refl` by `ring` in several proofs (to go down from 30s to 4s in one proof, for instance). I wonder if we should ban `ac_refl` from mathlib currently.
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+ *def* analytic_on
- \+ *lemma* continuous_linear_map.comp_analytic_on
- \+ *lemma* continuous_linear_map.comp_has_fpower_series_on_ball
- \+ *lemma* formal_multilinear_series.radius_le_radius_continuous_linear_map_comp
- \+ *lemma* has_fpower_series_on_ball.analytic_on
- \+ *lemma* has_fpower_series_on_ball.comp_sub
- \+ *lemma* has_fpower_series_on_ball.congr

Modified src/analysis/analytic/composition.lean


Modified src/analysis/calculus/cont_diff.lean
- \+ *lemma* iterated_fderiv_within_of_is_open

Modified src/analysis/calculus/fderiv_analytic.lean
- \+ *lemma* analytic_on.cont_diff_on
- \+ *lemma* analytic_on.deriv
- \+ *lemma* analytic_on.differentiable_on
- \+ *lemma* analytic_on.fderiv
- \+ *lemma* analytic_on.iterated_deriv
- \+ *lemma* analytic_on.iterated_fderiv
- \- *lemma* has_fpower_series_at.fderiv
- \+ *lemma* has_fpower_series_at.fderiv_eq
- \+ *lemma* has_fpower_series_on_ball.fderiv
- \+ *lemma* has_fpower_series_on_ball.fderiv_eq
- \+ *lemma* has_fpower_series_on_ball.has_fderiv_at

Modified src/analysis/calculus/formal_multilinear_series.lean
- \+ *def* continuous_linear_map.comp_formal_multilinear_series
- \+ *lemma* continuous_linear_map.comp_formal_multilinear_series_apply'
- \+ *lemma* continuous_linear_map.comp_formal_multilinear_series_apply



## [2022-04-05 11:05:56](https://github.com/leanprover-community/mathlib/commit/cbbaef5)
chore(algebra/field_power): generalisation linter ([#13107](https://github.com/leanprover-community/mathlib/pull/13107))
@alexjbest, this one is slightly more interesting, as the generalisation linter detected that two lemmas were stated incorrectly!
#### Estimated changes
Modified src/algebra/field_power.lean
- \- *lemma* zpow_eq_zero_iff
- \+/\- *theorem* zpow_two_nonneg
- \+/\- *theorem* zpow_two_pos_of_ne_zero

Modified src/algebra/group_with_zero/power.lean
- \+ *lemma* zpow_eq_zero_iff



## [2022-04-05 11:05:55](https://github.com/leanprover-community/mathlib/commit/225d1ce)
refactor(combinatorics/hall/finite): small simplifications and readability improvements ([#13091](https://github.com/leanprover-community/mathlib/pull/13091))
#### Estimated changes
Modified src/combinatorics/hall/finite.lean
- \+/\- *theorem* hall_marriage_theorem.hall_hard_inductive
- \- *theorem* hall_marriage_theorem.hall_hard_inductive_step
- \- *theorem* hall_marriage_theorem.hall_hard_inductive_zero



## [2022-04-05 09:11:51](https://github.com/leanprover-community/mathlib/commit/9ff42fd)
feat(topology/fiber_bundle): lemmas about `e.symm.trans e'` ([#13168](https://github.com/leanprover-community/mathlib/pull/13168))
#### Estimated changes
Modified src/topology/fiber_bundle.lean
- \+ *lemma* topological_fiber_bundle.pretrivialization.symm_trans_source_eq
- \+ *lemma* topological_fiber_bundle.pretrivialization.symm_trans_symm
- \+ *lemma* topological_fiber_bundle.pretrivialization.symm_trans_target_eq
- \+ *lemma* topological_fiber_bundle.trivialization.symm_trans_source_eq
- \+ *lemma* topological_fiber_bundle.trivialization.symm_trans_target_eq



## [2022-04-05 09:11:50](https://github.com/leanprover-community/mathlib/commit/01a424b)
feat(analysis): continuous_linear_map.prod_mapL ([#13165](https://github.com/leanprover-community/mathlib/pull/13165))
From the sphere eversion project,
Co-authored by Heather Macbeth <25316162+hrmacbeth@users.noreply.github.com>
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous.prod_mapL
- \+ *lemma* continuous.prod_map_equivL
- \+ *def* continuous_linear_map.prod_mapL
- \+ *lemma* continuous_linear_map.prod_mapL_apply
- \+ *lemma* continuous_on.prod_mapL
- \+ *lemma* continuous_on.prod_map_equivL



## [2022-04-05 09:11:49](https://github.com/leanprover-community/mathlib/commit/0e26022)
feat(group_theory/complement): Existence of transversals ([#13016](https://github.com/leanprover-community/mathlib/pull/13016))
This PR constructs transversals containing a specified element. This will be useful for Schreier's lemma (which requires a transversal containing the identity element).
#### Estimated changes
Modified src/group_theory/complement.lean
- \+ *lemma* subgroup.exists_left_transversal
- \+ *lemma* subgroup.exists_right_transversal



## [2022-04-05 09:11:48](https://github.com/leanprover-community/mathlib/commit/63feb1b)
feat(group_theory/index): Add `relindex_le_of_le_left` and `relindex_le_of_le_right` ([#13015](https://github.com/leanprover-community/mathlib/pull/13015))
This PR adds `relindex_le_of_le_left` and `relindex_le_of_le_right`, which are companion lemmas to `relindex_eq_zero_of_le_left` and `relindex_eq_zero_of_le_right`.
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* subgroup.relindex_le_of_le_left
- \+ *lemma* subgroup.relindex_le_of_le_right



## [2022-04-05 09:11:47](https://github.com/leanprover-community/mathlib/commit/ea1917b)
feat(algebra/group/to_additive + algebra/regular/basic): add to_additive for `is_regular` ([#12930](https://github.com/leanprover-community/mathlib/pull/12930))
This PR add the `to_additive` attribute to most lemmas in the file `algebra.regular.basic`.
I also added `to_additive` support for this: `to_additive` converts
*  `is_regular` to `is_add_regular`;
*  `is_left_regular` to `is_add_left_regular`;
*  `is_right_regular` to `is_add_right_regular`.
~~Currently, `to_additive` converts `regular` to `add_regular`.  This means that, for instance, `is_left_regular` becomes `is_left_add_regular`.~~
~~I have a slight preference for `is_add_left_regular/is_add_right_regular`, but I am not able to achieve this automatically.~~
~~EDIT: actually, the command~~
```
git ls-files | xargs grep -A1 "to\_additive" | grep -B1 regular
```
~~reveals more name changed by `to_additive` that require more thought.~~
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/algebra/regular/basic.lean
- \+/\- *lemma* mul_is_left_regular_iff
- \+/\- *lemma* mul_is_right_regular_iff

Modified src/group_theory/group_action/opposite.lean




## [2022-04-05 08:08:57](https://github.com/leanprover-community/mathlib/commit/21c48e1)
doc(topology/algebra/*): explanation of relation between `uniform_group` and `topological_group` ([#13151](https://github.com/leanprover-community/mathlib/pull/13151))
Adding some comments on how to use `uniform_group` and `topological_group`.
#### Estimated changes
Modified src/topology/algebra/group.lean


Modified src/topology/algebra/uniform_group.lean




## [2022-04-05 05:20:37](https://github.com/leanprover-community/mathlib/commit/429c6e3)
chore(topology/algebra/infinite_sum): weaken from equiv to surjective ([#13164](https://github.com/leanprover-community/mathlib/pull/13164))
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean
- \- *lemma* equiv.summable_iff_of_has_sum_iff
- \- *lemma* equiv.tsum_eq_tsum_of_has_sum_iff_has_sum
- \+ *lemma* function.surjective.summable_iff_of_has_sum_iff
- \+ *lemma* function.surjective.tsum_eq_tsum_of_has_sum_iff_has_sum



## [2022-04-05 05:20:36](https://github.com/leanprover-community/mathlib/commit/4c83474)
chore(model_theory/basic): Fix namespace on notation for first-order maps ([#13145](https://github.com/leanprover-community/mathlib/pull/13145))
Removes projection notation from the definition of notation for first-order maps
#### Estimated changes
Modified src/model_theory/basic.lean


Modified src/model_theory/elementary_maps.lean




## [2022-04-05 03:53:18](https://github.com/leanprover-community/mathlib/commit/41cd2f8)
chore(data/fin/tuple/basic): lemmas about `cons` ([#13027](https://github.com/leanprover-community/mathlib/pull/13027))
#### Estimated changes
Modified src/data/fin/tuple/basic.lean
- \+ *lemma* fin.cons_eq_cons
- \+ *def* fin.cons_induction
- \+ *lemma* fin.cons_induction_cons
- \+ *lemma* fin.cons_injective2
- \+ *lemma* fin.cons_left_injective
- \+ *lemma* fin.cons_right_injective



## [2022-04-04 23:36:07](https://github.com/leanprover-community/mathlib/commit/4eee8bc)
chore(order/complete_lattice): Generalize `⨆`/`⨅` lemmas to dependent families ([#13154](https://github.com/leanprover-community/mathlib/pull/13154))
The "bounded supremum" and "bounded infimum" are both instances of nested `⨆`/`⨅`. But they only apply when the inner one runs over a predicate `p : ι → Prop`, and the function couldn't depend on `p`. This generalizes to `κ : ι → Sort*` and allows dependence on `κ i`.
The lemmas are renamed from `bsupr`/`binfi` to `supr₂`/`infi₂` to show that they are more general.
Some lemmas were missing between `⨆` and `⨅` or between `⨆`/`⨅` and nested `⨆`/`⨅`, so I'm adding them as well.
Renames
#### Estimated changes
Modified src/analysis/box_integral/partition/filter.lean


Modified src/analysis/normed_space/spectrum.lean


Modified src/analysis/seminorm.lean


Modified src/data/dfinsupp/basic.lean


Modified src/data/real/ennreal.lean


Modified src/data/set/lattice.lean
- \+/\- *lemma* set.Inter_congr
- \+ *lemma* set.Inter_subset
- \- *theorem* set.Inter_subset
- \+/\- *lemma* set.Union_congr
- \+ *lemma* set.subset_Union
- \- *theorem* set.subset_Union

Modified src/data/set/pairwise.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/linear_algebra/clifford_algebra/grading.lean


Modified src/linear_algebra/dfinsupp.lean


Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/linear_algebra/span.lean
- \+ *lemma* submodule.span_Union₂

Modified src/linear_algebra/std_basis.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/integral/lebesgue.lean
- \- *theorem* measure_theory.le_infi2_lintegral
- \+ *lemma* measure_theory.le_infi₂_lintegral
- \- *theorem* measure_theory.supr2_lintegral_le
- \+ *lemma* measure_theory.supr₂_lintegral_le

Modified src/measure_theory/measure/content.lean
- \+/\- *lemma* measure_theory.content.inner_content_mono'

Modified src/measure_theory/measure/giry_monad.lean


Modified src/measure_theory/measure/haar.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/null_measurable.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/measure_theory/measure/regular.lean


Modified src/measure_theory/measure/stieltjes.lean
- \+/\- *lemma* stieltjes_function.length_mono

Modified src/order/closure.lean
- \- *lemma* closure_operator.closure_bsupr_closure
- \+/\- *lemma* closure_operator.closure_supr_closure
- \+ *lemma* closure_operator.closure_supr₂_closure
- \+/\- *lemma* lower_adjoint.closure_Union_closure
- \+ *lemma* lower_adjoint.closure_Union₂_closure
- \- *lemma* lower_adjoint.closure_bUnion_closure
- \- *lemma* lower_adjoint.closure_bsupr_closure
- \+/\- *lemma* lower_adjoint.closure_supr_closure
- \+ *lemma* lower_adjoint.closure_supr₂_closure

Modified src/order/compactly_generated.lean


Modified src/order/complete_boolean_algebra.lean


Modified src/order/complete_lattice.lean
- \+/\- *lemma* Inf_Prop_eq
- \+ *lemma* Inf_eq_infi'
- \- *theorem* Inf_eq_infi'
- \+ *lemma* Inf_eq_infi
- \- *theorem* Inf_eq_infi
- \+ *lemma* Inf_image'
- \- *theorem* Inf_image'
- \+/\- *theorem* Inf_image
- \+/\- *lemma* Inf_lt_iff
- \+/\- *lemma* Inf_range
- \+ *lemma* Inf_sUnion
- \+/\- *lemma* Inf_sup_le_infi_sup
- \+/\- *lemma* Sup_Prop_eq
- \+/\- *lemma* Sup_eq_supr'
- \+ *lemma* Sup_eq_supr
- \- *theorem* Sup_eq_supr
- \+ *lemma* Sup_image'
- \- *theorem* Sup_image'
- \+/\- *theorem* Sup_image
- \+/\- *lemma* Sup_range
- \+/\- *lemma* Sup_sUnion
- \+ *lemma* antitone.le_map_Inf
- \+ *lemma* antitone.le_map_infi
- \+ *lemma* antitone.le_map_infi₂
- \+ *lemma* antitone.map_Sup_le
- \+ *lemma* antitone.map_supr_le
- \+ *lemma* antitone.map_supr₂_le
- \- *theorem* binfi_le
- \- *theorem* binfi_le_binfi
- \- *theorem* binfi_le_of_le
- \+ *lemma* binfi_mono
- \- *theorem* bsupr_le
- \- *theorem* bsupr_le_bsupr'
- \- *theorem* bsupr_le_bsupr
- \- *theorem* bsupr_le_supr
- \+ *lemma* bsupr_mono
- \+/\- *lemma* function.surjective.infi_comp
- \+ *lemma* function.surjective.infi_congr
- \+/\- *lemma* function.surjective.supr_comp
- \+/\- *lemma* infi_Prop_eq
- \+ *lemma* infi_and
- \- *theorem* infi_and
- \+ *lemma* infi_comm
- \- *theorem* infi_comm
- \+/\- *lemma* infi_congr
- \+ *lemma* infi_congr_Prop
- \- *theorem* infi_congr_Prop
- \+ *lemma* infi_const_mono
- \+/\- *lemma* infi_eq_top
- \+ *lemma* infi_exists
- \- *theorem* infi_exists
- \+ *lemma* infi_le'
- \- *theorem* infi_le'
- \+ *lemma* infi_le
- \- *theorem* infi_le
- \- *theorem* infi_le_binfi
- \- *theorem* infi_le_infi2
- \- *theorem* infi_le_infi
- \- *theorem* infi_le_infi_const
- \+ *lemma* infi_le_infi₂
- \+ *lemma* infi_le_of_le
- \- *theorem* infi_le_of_le
- \+/\- *lemma* infi_lt_iff
- \+ *lemma* infi_mono'
- \+ *lemma* infi_mono
- \+/\- *lemma* infi_range'
- \+/\- *lemma* infi_range
- \+/\- *lemma* infi_top
- \+ *lemma* infi_true
- \- *theorem* infi_true
- \+ *lemma* infi₂_eq_top
- \+ *lemma* infi₂_le
- \+ *lemma* infi₂_le_of_le
- \+ *lemma* infi₂_mono'
- \+ *lemma* infi₂_mono
- \+/\- *lemma* is_glb.infi_eq
- \+/\- *lemma* is_glb_Inf
- \+/\- *lemma* is_glb_infi
- \+/\- *lemma* is_lub.supr_eq
- \+/\- *lemma* is_lub_Sup
- \+/\- *lemma* is_lub_supr
- \- *theorem* le_binfi
- \- *theorem* le_bsupr
- \- *theorem* le_bsupr_of_le
- \+ *lemma* le_infi
- \- *theorem* le_infi
- \+ *lemma* le_infi_iff
- \- *theorem* le_infi_iff
- \+ *lemma* le_infi₂
- \+ *lemma* le_infi₂_iff
- \+ *lemma* le_supr'
- \- *theorem* le_supr'
- \+ *lemma* le_supr
- \- *theorem* le_supr
- \+ *lemma* le_supr_of_le
- \- *theorem* le_supr_of_le
- \+ *lemma* le_supr₂
- \+ *lemma* le_supr₂_of_le
- \+/\- *lemma* lt_Sup_iff
- \+ *lemma* lt_infi_iff
- \+/\- *lemma* lt_supr_iff
- \- *lemma* monotone.le_map_supr2
- \+ *lemma* monotone.le_map_supr₂
- \- *lemma* monotone.map_infi2_le
- \+ *lemma* monotone.map_infi₂_le
- \+/\- *lemma* sup_Inf_le_infi_sup
- \+/\- *lemma* supr_Prop_eq
- \+ *lemma* supr_and
- \- *theorem* supr_and
- \+/\- *lemma* supr_bot
- \+ *lemma* supr_comm
- \- *theorem* supr_comm
- \+/\- *lemma* supr_congr
- \+ *lemma* supr_congr_Prop
- \- *theorem* supr_congr_Prop
- \+ *lemma* supr_const_mono
- \+/\- *lemma* supr_eq_bot
- \+ *lemma* supr_exists
- \- *theorem* supr_exists
- \+/\- *lemma* supr_inf_le_Sup_inf
- \+/\- *lemma* supr_inf_le_inf_Sup
- \+ *lemma* supr_le
- \- *theorem* supr_le
- \+ *lemma* supr_le_iff
- \- *theorem* supr_le_iff
- \- *theorem* supr_le_supr2
- \- *theorem* supr_le_supr
- \- *theorem* supr_le_supr_const
- \+ *lemma* supr_lt_iff
- \- *theorem* supr_lt_iff
- \+ *lemma* supr_mono'
- \+ *lemma* supr_mono
- \+/\- *lemma* supr_range'
- \+/\- *lemma* supr_range
- \+ *lemma* supr_true
- \- *theorem* supr_true
- \+ *lemma* supr₂_eq_bot
- \+ *lemma* supr₂_le
- \+ *lemma* supr₂_le_iff
- \+ *lemma* supr₂_le_supr
- \+ *lemma* supr₂_mono'
- \+ *lemma* supr₂_mono

Modified src/order/filter/basic.lean


Modified src/order/filter/lift.lean
- \+/\- *lemma* filter.lift_mono'

Modified src/order/filter/pi.lean
- \+/\- *lemma* filter.pi_mono

Modified src/order/hom/order.lean


Modified src/order/liminf_limsup.lean


Modified src/order/partial_sups.lean


Modified src/order/succ_pred/basic.lean


Modified src/order/sup_indep.lean


Modified src/probability/stopping.lean


Modified src/topology/algebra/order/basic.lean


Modified src/topology/algebra/order/monotone_convergence.lean


Modified src/topology/bases.lean


Modified src/topology/compact_open.lean


Modified src/topology/fiber_bundle.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/ereal.lean


Modified src/topology/instances/nnreal.lean


Modified src/topology/metric_space/hausdorff_dimension.lean


Modified src/topology/metric_space/hausdorff_distance.lean
- \+/\- *lemma* emetric.inf_edist_le_edist_of_mem

Modified src/topology/order.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/compact_separated.lean




## [2022-04-04 20:06:50](https://github.com/leanprover-community/mathlib/commit/bae79d0)
chore(number_theory/cyclotomic/discriminant): golf `repr_pow_is_integral` a little ([#13167](https://github.com/leanprover-community/mathlib/pull/13167))
Using nice mathlib tactics instead of doing boilerplate tasks by hand to reduce the verbosity.
#### Estimated changes
Modified src/ring_theory/adjoin/power_basis.lean




## [2022-04-04 20:06:48](https://github.com/leanprover-community/mathlib/commit/a925d1d)
chore(topology/algebra/module/basic): add continuous_linear_map.copy ([#13166](https://github.com/leanprover-community/mathlib/pull/13166))
As suggested by the fun_like docs
#### Estimated changes
Modified src/topology/algebra/module/basic.lean




## [2022-04-04 18:23:21](https://github.com/leanprover-community/mathlib/commit/05e2fc0)
chore(order/*): generalisation linter ([#13105](https://github.com/leanprover-community/mathlib/pull/13105))
#### Estimated changes
Modified src/order/atoms.lean
- \+/\- *theorem* set.is_simple_order_Ici_iff_is_coatom
- \+/\- *theorem* set.is_simple_order_Iic_iff_is_atom

Modified src/order/conditionally_complete_lattice.lean


Modified src/order/lattice_intervals.lean
- \+/\- *lemma* set.Ici.coe_bot
- \+/\- *lemma* set.Iic.coe_top

Modified src/order/modular_lattice.lean


Modified src/order/order_iso_nat.lean




## [2022-04-04 16:21:07](https://github.com/leanprover-community/mathlib/commit/fe21f5d)
feat(group_theory/torsion): define torsion subgroups and show they're torsion ([#12769](https://github.com/leanprover-community/mathlib/pull/12769))
Also tidy up some linter errors and docstring for the module.
#### Estimated changes
Modified scripts/nolints.txt


Modified src/group_theory/torsion.lean
- \+ *lemma* comm_monoid.torsion.is_torsion
- \+ *def* comm_monoid.torsion
- \+ *lemma* monoid.is_torsion.torsion_eq_top
- \+ *def* monoid.is_torsion.torsion_mul_equiv
- \+ *def* torsion.of_torsion
- \+ *def* torsion
- \+ *lemma* torsion_eq_torsion_submonoid



## [2022-04-04 16:21:06](https://github.com/leanprover-community/mathlib/commit/2108284)
refactor(order/succ_order/basic): Use `is_min`/`is_max` ([#12597](https://github.com/leanprover-community/mathlib/pull/12597))
Reformulate the `succ a ≤ a` and `a ≤ pred a` conditions to use `is_max` and `is_min`. This simplifies the proofs.
Change namespaces from `succ_order` and `pred_order` to `order`.
Lemma renames
#### Estimated changes
Modified src/analysis/calculus/specific_functions.lean


Modified src/data/int/succ_pred.lean
- \+ *lemma* int.pred_eq_pred
- \+/\- *lemma* int.pred_iterate
- \+ *lemma* int.succ_eq_succ
- \+/\- *lemma* int.succ_iterate

Modified src/data/nat/succ_pred.lean
- \+ *lemma* nat.pred_eq_pred
- \+/\- *lemma* nat.pred_iterate
- \+ *lemma* nat.succ_eq_succ
- \+/\- *lemma* nat.succ_iterate

Modified src/order/bounded_order.lean
- \+ *lemma* not_is_bot_iff_ne_bot
- \+ *lemma* not_is_max_bot
- \+ *lemma* not_is_max_iff_ne_top
- \+ *lemma* not_is_min_iff_ne_bot
- \+ *lemma* not_is_min_top
- \+ *lemma* not_is_top_iff_ne_top
- \+ *lemma* with_bot.not_coe_le_bot
- \+/\- *lemma* with_top.not_top_le_coe

Modified src/order/max.lean
- \+ *lemma* not_is_max_of_lt
- \+ *lemma* not_is_min_of_lt

Modified src/order/succ_pred/basic.lean
- \+/\- *lemma* covby.succ_eq
- \- *lemma* covby_iff_pred_eq
- \- *lemma* covby_iff_succ_eq
- \+ *lemma* order.Ici_succ
- \+ *lemma* order.Ici_succ_of_not_is_max
- \+ *lemma* order.Iic_pred
- \+ *lemma* order.Iic_pred_of_not_is_min
- \+ *lemma* order.Iio_succ
- \+ *lemma* order.Iio_succ_of_not_is_max
- \+ *lemma* order.Ioi_pred
- \+ *lemma* order.Ioi_pred_of_not_is_min
- \+ *lemma* order.bot_lt_succ
- \+ *lemma* order.covby_succ
- \+ *lemma* order.covby_succ_of_not_is_max
- \+ *lemma* order.le_le_succ_iff
- \+ *lemma* order.le_of_lt_succ
- \+ *lemma* order.le_of_pred_lt
- \+ *lemma* order.le_pred_iff
- \+ *lemma* order.le_pred_iff_eq_bot
- \+ *lemma* order.le_pred_iff_is_min
- \+ *lemma* order.le_pred_iff_lt_or_eq
- \+ *lemma* order.le_pred_iff_of_not_is_min
- \+ *lemma* order.le_pred_of_lt
- \+ *lemma* order.le_succ
- \+ *lemma* order.le_succ_iff_lt_or_eq
- \+ *lemma* order.lt_succ
- \+ *lemma* order.lt_succ_iff
- \+ *lemma* order.lt_succ_iff_lt_or_eq
- \+ *lemma* order.lt_succ_iff_ne_top
- \+ *lemma* order.lt_succ_iff_not_is_max
- \+ *lemma* order.lt_succ_iff_of_not_is_max
- \+ *lemma* order.max_of_succ_le
- \+ *lemma* order.min_of_le_pred
- \+ *def* order.pred
- \+ *lemma* order.pred_bot
- \+ *lemma* order.pred_covby
- \+ *lemma* order.pred_covby_of_not_is_min
- \+ *lemma* order.pred_eq_iff_covby
- \+ *lemma* order.pred_eq_iff_is_min
- \+ *lemma* order.pred_eq_pred_iff
- \+ *lemma* order.pred_eq_supr
- \+ *lemma* order.pred_injective
- \+ *lemma* order.pred_le
- \+ *lemma* order.pred_le_le_iff
- \+ *lemma* order.pred_le_pred
- \+ *lemma* order.pred_le_pred_iff
- \+ *lemma* order.pred_lt
- \+ *lemma* order.pred_lt_iff
- \+ *lemma* order.pred_lt_iff_lt_or_eq
- \+ *lemma* order.pred_lt_iff_ne_bot
- \+ *lemma* order.pred_lt_iff_not_is_min
- \+ *lemma* order.pred_lt_iff_of_not_is_min
- \+ *lemma* order.pred_lt_pred_iff
- \+ *lemma* order.pred_lt_top
- \+ *lemma* order.pred_mono
- \+ *lemma* order.pred_ne_pred_iff
- \+ *lemma* order.pred_ne_top
- \+ *lemma* order.pred_strict_mono
- \+ *lemma* order.pred_succ
- \+ *lemma* order.pred_succ_of_not_is_max
- \+ *def* order.succ
- \+ *lemma* order.succ_eq_iff_covby
- \+ *lemma* order.succ_eq_iff_is_max
- \+ *lemma* order.succ_eq_infi
- \+ *lemma* order.succ_eq_succ_iff
- \+ *lemma* order.succ_injective
- \+ *lemma* order.succ_le_iff
- \+ *lemma* order.succ_le_iff_eq_top
- \+ *lemma* order.succ_le_iff_is_max
- \+ *lemma* order.succ_le_iff_of_not_is_max
- \+ *lemma* order.succ_le_of_lt
- \+ *lemma* order.succ_le_succ
- \+ *lemma* order.succ_le_succ_iff
- \+ *lemma* order.succ_lt_succ_iff
- \+ *lemma* order.succ_mono
- \+ *lemma* order.succ_ne_bot
- \+ *lemma* order.succ_ne_succ_iff
- \+ *lemma* order.succ_pred
- \+ *lemma* order.succ_pred_of_not_is_min
- \+ *lemma* order.succ_strict_mono
- \+ *lemma* order.succ_top
- \- *lemma* pred_order.Ici_eq_Ioi_pred'
- \- *lemma* pred_order.Ici_eq_Ioi_pred
- \- *lemma* pred_order.Iio_eq_Iic_pred'
- \- *lemma* pred_order.Iio_eq_Iic_pred
- \- *lemma* pred_order.le_pred_iff
- \- *lemma* pred_order.le_pred_iff_eq_bot
- \- *lemma* pred_order.le_pred_iff_lt_or_eq
- \- *lemma* pred_order.le_pred_iff_of_not_is_min
- \+/\- *def* pred_order.of_le_pred_iff
- \+/\- *def* pred_order.of_le_pred_iff_of_pred_le_pred
- \- *lemma* pred_order.pred_bot
- \- *lemma* pred_order.pred_covby
- \- *lemma* pred_order.pred_covby_of_nonempty_Iio
- \- *lemma* pred_order.pred_eq_pred_iff
- \- *lemma* pred_order.pred_eq_supr
- \- *lemma* pred_order.pred_injective
- \- *lemma* pred_order.pred_le_le_iff
- \- *lemma* pred_order.pred_le_pred
- \- *lemma* pred_order.pred_le_pred_iff
- \- *lemma* pred_order.pred_lt
- \- *lemma* pred_order.pred_lt_iff
- \- *lemma* pred_order.pred_lt_iff_lt_or_eq
- \- *lemma* pred_order.pred_lt_iff_ne_bot
- \- *lemma* pred_order.pred_lt_iff_of_not_is_min
- \- *lemma* pred_order.pred_lt_of_not_is_min
- \- *lemma* pred_order.pred_lt_of_not_minimal
- \- *lemma* pred_order.pred_lt_pred_iff
- \- *lemma* pred_order.pred_lt_top
- \- *lemma* pred_order.pred_mono
- \- *lemma* pred_order.pred_ne_pred_iff
- \- *lemma* pred_order.pred_ne_top
- \- *lemma* pred_order.pred_strict_mono
- \- *lemma* pred_succ
- \- *lemma* pred_succ_of_nonempty_Ioi
- \- *lemma* succ_order.Iic_eq_Iio_succ'
- \- *lemma* succ_order.Iic_eq_Iio_succ
- \- *lemma* succ_order.Ioi_eq_Ici_succ'
- \- *lemma* succ_order.Ioi_eq_Ici_succ
- \- *lemma* succ_order.bot_lt_succ
- \- *lemma* succ_order.covby_succ
- \- *lemma* succ_order.covby_succ_of_nonempty_Ioi
- \- *lemma* succ_order.le_le_succ_iff
- \- *lemma* succ_order.le_succ_iff_lt_or_eq
- \- *lemma* succ_order.lt_succ
- \- *lemma* succ_order.lt_succ_iff
- \- *lemma* succ_order.lt_succ_iff_lt_or_eq
- \- *lemma* succ_order.lt_succ_iff_ne_top
- \- *lemma* succ_order.lt_succ_iff_of_not_is_max
- \- *lemma* succ_order.lt_succ_of_not_is_max
- \- *lemma* succ_order.lt_succ_of_not_maximal
- \+/\- *def* succ_order.of_succ_le_iff
- \+/\- *def* succ_order.of_succ_le_iff_of_le_lt_succ
- \- *lemma* succ_order.succ_eq_infi
- \- *lemma* succ_order.succ_eq_succ_iff
- \- *lemma* succ_order.succ_injective
- \- *lemma* succ_order.succ_le_iff
- \- *lemma* succ_order.succ_le_iff_eq_top
- \- *lemma* succ_order.succ_le_iff_of_not_is_max
- \- *lemma* succ_order.succ_le_succ
- \- *lemma* succ_order.succ_le_succ_iff
- \- *lemma* succ_order.succ_lt_succ_iff
- \- *lemma* succ_order.succ_mono
- \- *lemma* succ_order.succ_ne_bot
- \- *lemma* succ_order.succ_ne_succ_iff
- \- *lemma* succ_order.succ_strict_mono
- \- *lemma* succ_order.succ_top
- \- *lemma* succ_pred
- \- *lemma* succ_pred_of_nonempty_Iio

Modified src/order/succ_pred/relation.lean


Modified src/probability/stopping.lean


Modified src/topology/connected.lean


Modified src/topology/instances/discrete.lean




## [2022-04-04 14:28:18](https://github.com/leanprover-community/mathlib/commit/f55d352)
feat(order/filter/n_ary): Binary and ternary maps of filters ([#13062](https://github.com/leanprover-community/mathlib/pull/13062))
Define `filter.map₂` and `filter.map₃`, the binary and ternary maps of filters.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.image_subset_image2_left
- \+ *lemma* set.image_subset_image2_right

Added src/order/filter/n_ary.lean
- \+ *lemma* filter.image2_mem_map₂
- \+ *lemma* filter.le_map₂_iff
- \+ *lemma* filter.map_map₂
- \+ *lemma* filter.map_map₂_antidistrib
- \+ *lemma* filter.map_map₂_antidistrib_left
- \+ *lemma* filter.map_map₂_antidistrib_right
- \+ *lemma* filter.map_map₂_distrib
- \+ *lemma* filter.map_map₂_distrib_left
- \+ *lemma* filter.map_map₂_distrib_right
- \+ *lemma* filter.map_map₂_right_anticomm
- \+ *lemma* filter.map_map₂_right_comm
- \+ *def* filter.map₂
- \+ *lemma* filter.map₂_assoc
- \+ *lemma* filter.map₂_bot_left
- \+ *lemma* filter.map₂_bot_right
- \+ *lemma* filter.map₂_comm
- \+ *lemma* filter.map₂_eq_bot_iff
- \+ *lemma* filter.map₂_inf_subset_left
- \+ *lemma* filter.map₂_inf_subset_right
- \+ *lemma* filter.map₂_left
- \+ *lemma* filter.map₂_left_comm
- \+ *lemma* filter.map₂_map_left
- \+ *lemma* filter.map₂_map_left_anticomm
- \+ *lemma* filter.map₂_map_left_comm
- \+ *lemma* filter.map₂_map_right
- \+ *lemma* filter.map₂_map₂_left
- \+ *lemma* filter.map₂_map₂_right
- \+ *lemma* filter.map₂_mono
- \+ *lemma* filter.map₂_mono_left
- \+ *lemma* filter.map₂_mono_right
- \+ *lemma* filter.map₂_ne_bot_iff
- \+ *lemma* filter.map₂_pure
- \+ *lemma* filter.map₂_pure_left
- \+ *lemma* filter.map₂_pure_right
- \+ *lemma* filter.map₂_right
- \+ *lemma* filter.map₂_right_comm
- \+ *lemma* filter.map₂_sup_left
- \+ *lemma* filter.map₂_sup_right
- \+ *lemma* filter.map₂_swap
- \+ *def* filter.map₃
- \+ *lemma* filter.mem_map₂_iff
- \+ *lemma* filter.ne_bot.map₂



## [2022-04-04 09:32:39](https://github.com/leanprover-community/mathlib/commit/b189be7)
feat(algebra/big_operators): add `commute.*_sum_{left,right}` lemmas ([#13035](https://github.com/leanprover-community/mathlib/pull/13035))
This moves the existing `prod_commute` lemmas into the `commute` namespace for discoverabiliy, and adds the swapped variants.
This also fixes an issue where lemmas about `add_commute` were misnamed using `commute`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* commute.sum_left
- \+ *lemma* commute.sum_right

Modified src/algebra/big_operators/multiset.lean
- \+ *lemma* commute.multiset_sum_left
- \+ *lemma* commute.multiset_sum_right

Modified src/data/finset/noncomm_prod.lean


Modified src/data/list/big_operators.lean
- \+ *lemma* commute.list_prod_left
- \+ *lemma* commute.list_prod_right
- \+ *lemma* commute.list_sum_left
- \+ *lemma* commute.list_sum_right
- \- *lemma* list.prod_commute



## [2022-04-04 08:56:24](https://github.com/leanprover-community/mathlib/commit/19448a9)
refactor(group_theory/schur_zassenhaus): Some golfing ([#13017](https://github.com/leanprover-community/mathlib/pull/13017))
This PR uses `mem_left_transversals.to_equiv` to golf the start of `schur_zassenhaus.lean`.
#### Estimated changes
Modified src/group_theory/schur_zassenhaus.lean




## [2022-04-04 08:23:22](https://github.com/leanprover-community/mathlib/commit/0cb9407)
chore(measure_theory/function/locally_integrable): fix typo ([#13160](https://github.com/leanprover-community/mathlib/pull/13160))
#### Estimated changes
Modified src/measure_theory/function/locally_integrable.lean
- \- *lemma* measure_theory.locally_integrable.ae_measurable
- \+ *lemma* measure_theory.locally_integrable.ae_strongly_measurable



## [2022-04-04 06:48:14](https://github.com/leanprover-community/mathlib/commit/6dde651)
feat(algebra/quaternion): Cardinality of quaternion algebras ([#12891](https://github.com/leanprover-community/mathlib/pull/12891))
#### Estimated changes
Modified src/algebra/quaternion.lean
- \+ *lemma* cardinal.mk_quaternion
- \+ *lemma* cardinal.mk_quaternion_algebra
- \+ *lemma* cardinal.mk_quaternion_algebra_of_infinite
- \+ *lemma* cardinal.mk_quaternion_of_infinite
- \+ *lemma* cardinal.mk_univ_quaternion
- \+ *lemma* cardinal.mk_univ_quaternion_algebra
- \+ *lemma* cardinal.mk_univ_quaternion_algebra_of_infinite
- \+ *lemma* cardinal.mk_univ_quaternion_of_infinite
- \+ *def* quaternion.equiv_prod
- \+ *def* quaternion_algebra.equiv_prod



## [2022-04-04 06:15:27](https://github.com/leanprover-community/mathlib/commit/8cb151f)
feat(number_theory/cyclotomic/discriminant): add discr_zeta_eq_discr_zeta_sub_one ([#12710](https://github.com/leanprover-community/mathlib/pull/12710))
We add `discr_zeta_eq_discr_zeta_sub_one`: the discriminant of the power basis given by a primitive root of unity `ζ` is the same as the
discriminant of the power basis given by `ζ - 1`.
from flt-regular
#### Estimated changes
Modified src/number_theory/cyclotomic/basic.lean


Modified src/number_theory/cyclotomic/discriminant.lean
- \+ *lemma* is_primitive_root.discr_zeta_eq_discr_zeta_sub_one

Modified src/number_theory/cyclotomic/gal.lean


Modified src/ring_theory/adjoin/power_basis.lean
- \+ *lemma* power_basis.repr_gen_pow_is_integral
- \+ *lemma* power_basis.repr_mul_is_integral
- \+ *lemma* power_basis.repr_pow_is_integral
- \+ *lemma* power_basis.to_matrix_is_integral



## [2022-04-03 17:52:03](https://github.com/leanprover-community/mathlib/commit/61e18ae)
fix(data/polynomial/basic): op_ring_equiv docstring ([#13132](https://github.com/leanprover-community/mathlib/pull/13132))
#### Estimated changes
Modified src/data/polynomial/basic.lean




## [2022-04-03 16:42:11](https://github.com/leanprover-community/mathlib/commit/36e1cdf)
feat(topology/uniform_space/basic): constructing a `uniform_space.core` from a filter basis for the uniformity ([#13065](https://github.com/leanprover-community/mathlib/pull/13065))
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+ *def* uniform_space.core.mk_of_basis



## [2022-04-03 11:32:25](https://github.com/leanprover-community/mathlib/commit/1212818)
feat(category_theory/abelian): transferring "abelian-ness" across a functor ([#13059](https://github.com/leanprover-community/mathlib/pull/13059))
If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.
See https://stacks.math.columbia.edu/tag/03A3
#### Estimated changes
Added src/category_theory/abelian/transfer.lean
- \+ *def* category_theory.abelian_of_adjunction.coimage_iso_image
- \+ *def* category_theory.abelian_of_adjunction.coimage_iso_image_aux
- \+ *lemma* category_theory.abelian_of_adjunction.coimage_iso_image_hom
- \+ *def* category_theory.abelian_of_adjunction.cokernel_iso
- \+ *lemma* category_theory.abelian_of_adjunction.has_cokernels
- \+ *lemma* category_theory.abelian_of_adjunction.has_kernels
- \+ *def* category_theory.abelian_of_adjunction

Modified src/category_theory/limits/preserves/shapes/kernels.lean




## [2022-04-03 09:48:57](https://github.com/leanprover-community/mathlib/commit/6e26cff)
feat(analysis/special_functions): add the Gamma function ([#12917](https://github.com/leanprover-community/mathlib/pull/12917))
#### Estimated changes
Added src/analysis/special_functions/gamma.lean
- \+ *def* complex.Gamma_integral
- \+ *lemma* complex.Gamma_integral_convergent
- \+ *lemma* complex.Gamma_integral_of_real
- \+ *lemma* complex.Gamma_integral_one
- \+ *lemma* integral_exp_neg_Ioi
- \+ *def* real.Gamma_integral
- \+ *lemma* real.Gamma_integral_convergent
- \+ *lemma* real.Gamma_integral_one
- \+ *lemma* real.Gamma_integrand_is_O



## [2022-04-03 06:44:02](https://github.com/leanprover-community/mathlib/commit/6e5ca7d)
chore(*): Bump to Lean 3.42.1 ([#13146](https://github.com/leanprover-community/mathlib/pull/13146))
#### Estimated changes
Modified leanpkg.toml




## [2022-04-03 06:44:01](https://github.com/leanprover-community/mathlib/commit/d6731a4)
docs(data/polynomial/basic): Remove commutative from doc-module ([#13144](https://github.com/leanprover-community/mathlib/pull/13144))
#### Estimated changes
Modified src/data/polynomial/basic.lean




## [2022-04-03 04:50:50](https://github.com/leanprover-community/mathlib/commit/4f14d4d)
chore(topology/vector_bundle): split long proof ([#13142](https://github.com/leanprover-community/mathlib/pull/13142))
The construction of the direct sum of two vector bundles is on the verge of timing out, and an upcoming refactor will push it over the edge.  Split it pre-emptively.
#### Estimated changes
Modified src/topology/vector_bundle.lean
- \+ *lemma* topological_vector_bundle.trivialization.prod.continuous_inv_fun
- \+ *lemma* topological_vector_bundle.trivialization.prod.continuous_to_fun
- \+ *lemma* topological_vector_bundle.trivialization.prod.left_inv
- \+ *lemma* topological_vector_bundle.trivialization.prod.right_inv



## [2022-04-03 04:50:49](https://github.com/leanprover-community/mathlib/commit/410e3d0)
feat(logic/small, model_theory/*): Smallness of vectors, lists, terms, and substructures ([#13123](https://github.com/leanprover-community/mathlib/pull/13123))
Provides instances of `small` on vectors, lists, terms, and `substructure.closure`.
#### Estimated changes
Modified src/logic/small.lean


Modified src/model_theory/substructures.lean


Modified src/model_theory/syntax.lean




## [2022-04-03 04:50:48](https://github.com/leanprover-community/mathlib/commit/2d22b5d)
chore(algebra/*): generalisation linter ([#13109](https://github.com/leanprover-community/mathlib/pull/13109))
#### Estimated changes
Modified src/algebra/group/conj.lean


Modified src/algebra/group_power/order.lean


Modified src/algebra/indicator_function.lean
- \+/\- *lemma* monoid_hom.map_mul_indicator

Modified src/algebra/invertible.lean
- \+/\- *lemma* nonzero_of_invertible

Modified src/algebra/module/basic.lean
- \+/\- *lemma* add_monoid_hom.map_int_module_smul
- \+/\- *lemma* add_monoid_hom.map_nat_module_smul

Modified src/algebra/support.lean
- \+/\- *lemma* function.mul_support_mul



## [2022-04-03 04:50:47](https://github.com/leanprover-community/mathlib/commit/d33ea7b)
chore(ring_theory/polynomial/pochhammer): make semiring implicit in a lemma that I just moved ([#13077](https://github.com/leanprover-community/mathlib/pull/13077))
Moving lemma `pochhammer_succ_eval` to reduce typeclass assumptions ([#13024](https://github.com/leanprover-community/mathlib/pull/13024)), the `semiring` became accidentally explicit.  Since one of the explicit arguments of the lemma is a term in the semiring, I changed the `semiring` to being implicit.
The neighbouring lemmas do not involve terms in their respective semiring, which is why the semiring is explicit throughout the section.
#### Estimated changes
Modified src/ring_theory/polynomial/pochhammer.lean
- \+/\- *lemma* pochhammer_succ_eval



## [2022-04-03 04:50:46](https://github.com/leanprover-community/mathlib/commit/955e95a)
feat(logic/function/basic): add some more API for `injective2` ([#13074](https://github.com/leanprover-community/mathlib/pull/13074))
Note that the new `.left` and `.right` lemmas are weaker than the original ones, but the original lemmas were pretty much useless anyway, as `hf.left h` was the same as `(hf h).left`.
#### Estimated changes
Modified src/logic/function/basic.lean
- \+/\- *lemma* function.injective2.eq_iff
- \+ *lemma* function.injective2.left'
- \+ *lemma* function.injective2.right'



## [2022-04-03 03:07:24](https://github.com/leanprover-community/mathlib/commit/ef7298d)
chore(data/nat/gcd): move nat.coprime.mul_add_mul_ne_mul ([#13022](https://github.com/leanprover-community/mathlib/pull/13022))
I'm not sure if it will be useful elsewhere, but this seems like a better place for it anyway.
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+ *lemma* nat.coprime.mul_add_mul_ne_mul

Modified src/number_theory/frobenius_number.lean
- \- *lemma* nat.coprime.mul_add_mul_ne_mul



## [2022-04-03 02:04:00](https://github.com/leanprover-community/mathlib/commit/e1eb0bd)
feat(algebra/algebra/unitization): add star structure for the unitization of a non-unital algebra ([#13120](https://github.com/leanprover-community/mathlib/pull/13120))
The unitization of an algebra has a natural star structure when the underlying scalar ring and non-unital algebra have suitably interacting star structures.
#### Estimated changes
Modified src/algebra/algebra/unitization.lean
- \+ *lemma* unitization.coe_star
- \+ *lemma* unitization.fst_star
- \+ *lemma* unitization.inl_star
- \+ *lemma* unitization.snd_star



## [2022-04-03 00:36:47](https://github.com/leanprover-community/mathlib/commit/e41208d)
feat(category_theory/monoidal): define monoidal structures on cartesian products of monoidal categories, (lax) monoidal functors and monoidal natural transformations ([#13033](https://github.com/leanprover-community/mathlib/pull/13033))
This PR contains (fairly straightforward) definitions / proofs of the following facts:
- Cartesian product of monoidal categories is a monoidal category.
- Cartesian product of (lax) monoidal functors is a (lax) monoidal functor.
- Cartesian product of monoidal natural transformations is a monoidal natural transformation.
These are prerequisites to defining a monoidal category structure on the category of monoids in a braided monoidal category (with the approach that I've chosen).  In particular, the first bullet point above is a prerequisite to endowing the tensor product functor, viewed as a functor from `C × C` to `C`, where `C` is a braided monoidal category, with a strength that turns it into a monoidal functor (stacked  PR).
This fits as follows into the general strategy for defining a monoidal category structure on the category of monoids in a braided monoidal category `C`, at least conceptually:
first, define a monoidal category structure on the category of lax monoidal functors into `C`, and then transport this structure to the category `Mon_ C` of monoids along the equivalence between `Mon_ C` and the category `lax_monoid_functor (discrete punit) C`.  All, not necessarily lax monoidal functors into `C` form a monoidal category with "pointwise" tensor product.  The tensor product of two lax monoidal functors equals the composition of their cartesian product, which is lax monoidal, with the tensor product on`C`, which is monoidal if `C` is braided.  This gives a way to define a tensor product of two lax monoidal functors.  The details still need to be fleshed out.
#### Estimated changes
Modified src/category_theory/monoidal/category.lean
- \+ *lemma* category_theory.monoidal_category.prod_monoidal_left_unitor_hom_fst
- \+ *lemma* category_theory.monoidal_category.prod_monoidal_left_unitor_hom_snd
- \+ *lemma* category_theory.monoidal_category.prod_monoidal_left_unitor_inv_fst
- \+ *lemma* category_theory.monoidal_category.prod_monoidal_left_unitor_inv_snd
- \+ *lemma* category_theory.monoidal_category.prod_monoidal_right_unitor_hom_fst
- \+ *lemma* category_theory.monoidal_category.prod_monoidal_right_unitor_hom_snd
- \+ *lemma* category_theory.monoidal_category.prod_monoidal_right_unitor_inv_fst
- \+ *lemma* category_theory.monoidal_category.prod_monoidal_right_unitor_inv_snd

Modified src/category_theory/monoidal/functor.lean
- \+ *def* category_theory.lax_monoidal_functor.prod'
- \+ *lemma* category_theory.lax_monoidal_functor.prod'_to_functor
- \+ *lemma* category_theory.lax_monoidal_functor.prod'_ε
- \+ *lemma* category_theory.lax_monoidal_functor.prod'_μ
- \+ *def* category_theory.lax_monoidal_functor.prod
- \+ *def* category_theory.monoidal_functor.diag
- \+ *def* category_theory.monoidal_functor.prod'
- \+ *lemma* category_theory.monoidal_functor.prod'_to_lax_monoidal_functor
- \+ *def* category_theory.monoidal_functor.prod

Modified src/category_theory/monoidal/natural_transformation.lean
- \+ *def* category_theory.monoidal_nat_trans.prod

Modified src/category_theory/products/basic.lean
- \+ *def* category_theory.functor.diag
- \+ *lemma* category_theory.functor.diag_map
- \+ *lemma* category_theory.functor.diag_obj
- \+ *lemma* category_theory.is_iso_prod_iff
- \+ *def* category_theory.iso.prod



## [2022-04-02 23:29:08](https://github.com/leanprover-community/mathlib/commit/bb5e598)
feat(set_theory/cardinal_ordinal): Add `simp` lemmas for `aleph` ([#13056](https://github.com/leanprover-community/mathlib/pull/13056))
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* cardinal.aleph_add_aleph
- \+ *theorem* cardinal.aleph_mul_aleph
- \+ *theorem* cardinal.aleph_mul_omega
- \+ *theorem* cardinal.max_aleph_eq
- \+ *theorem* cardinal.omega_mul_aleph



## [2022-04-02 22:23:30](https://github.com/leanprover-community/mathlib/commit/d4b40c3)
feat(measure_theory/measure/haar_lebesgue): measure of an affine subspace is zero ([#13137](https://github.com/leanprover-community/mathlib/pull/13137))
* Additive Haar measure of an affine subspace of a finite dimensional
real vector space is zero.
* Additive Haar measure of the image of a set `s` under `homothety x r` is
  equal to `|r ^ d| * μ s`.
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* affine_subspace.coe_eq_bot_iff
- \+ *lemma* affine_subspace.coe_eq_univ_iff
- \+ *lemma* affine_subspace.eq_bot_or_nonempty
- \+ *lemma* affine_subspace.nonempty_iff_ne_bot

Modified src/measure_theory/measure/haar_lebesgue.lean
- \+ *lemma* measure_theory.measure.add_haar_affine_subspace
- \+ *lemma* measure_theory.measure.add_haar_image_homothety



## [2022-04-02 22:23:29](https://github.com/leanprover-community/mathlib/commit/7617942)
feat(order/filter/basic): add `filter.eventually_{eq,le}.prod_map` ([#13103](https://github.com/leanprover-community/mathlib/pull/13103))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_eq.prod_map
- \+ *lemma* filter.eventually_le.prod_map



## [2022-04-02 19:43:29](https://github.com/leanprover-community/mathlib/commit/a29bd58)
feat(algebra/regular/basic): add lemma commute.is_regular_iff ([#13104](https://github.com/leanprover-community/mathlib/pull/13104))
This lemma shows that an element that commutes with every element is regular if and only if it is left regular.
#### Estimated changes
Modified src/algebra/regular/basic.lean
- \+ *lemma* commute.is_regular_iff
- \+ *lemma* is_left_regular.right_of_commute



## [2022-04-02 16:29:33](https://github.com/leanprover-community/mathlib/commit/8e476fa)
chore(topology/vector_bundle): use continuous-linear rather than linear in core construction ([#13053](https://github.com/leanprover-community/mathlib/pull/13053))
The `vector_bundle_core` construction builds a vector bundle from a cocycle, the data of which are an open cover and a choice of transition function between any two elements of the cover.  Currently, for base `B` and model fibre `F`, the transition function has type `ι → ι → B → (F →ₗ[R] F)`.
This PR changes it to type `ι → ι → B → (F →L[R] F)`.  This is no loss of generality since there already were other conditions which forced the transition function to be continuous-linear on each fibre.  Of course, it is a potential loss of convenience since the proof obligation for continuity now occurs upfront.
The change is needed because in the vector bundle refactor to come, the further condition will be imposed that each transition function `B → (F →L[R] F)` is continuous; stating this requires a topology on `F →L[R] F`.
#### Estimated changes
Modified src/geometry/manifold/mfderiv.lean


Modified src/geometry/manifold/tangent_bundle.lean


Modified src/topology/vector_bundle.lean




## [2022-04-02 15:55:20](https://github.com/leanprover-community/mathlib/commit/cf6f27e)
refactor(topology/{fiber_bundle, vector_bundle}): make trivializations data rather than an existential ([#13052](https://github.com/leanprover-community/mathlib/pull/13052))
Previously, the construction `topological_vector_bundle` was a mixin requiring the _existence_ of a suitable trivialization at each point.
Change this to a class with data: a choice of trivialization at each point.  This has no effect on the mathematics, but it is necessary for the forthcoming refactor in which a further condition is imposed on the mutual compatibility of the trivializations.
Furthermore, attach to `topological_vector_bundle` and to two other constructions `topological_fiber_prebundle`, `topological_vector_prebundle` a further piece of data: an atlas of "good" trivializations.  This is not really mathematically necessary, since you could always take the atlas of "good" trivializations to be simply the set of canonical trivializations at each point in the manifold.  But sometimes one naturally has this larger "good" class and it's convenient to be able to access it.  The `charted_space` definition in the manifolds library does something similar.
#### Estimated changes
Modified src/topology/fiber_bundle.lean
- \+ *lemma* topological_fiber_prebundle.continuous_symm_of_mem_pretrivialization_atlas
- \- *lemma* topological_fiber_prebundle.continuous_symm_pretrivialization_at
- \+ *lemma* topological_fiber_prebundle.is_open_source
- \- *lemma* topological_fiber_prebundle.is_open_source_pretrivialization_at
- \+ *lemma* topological_fiber_prebundle.is_open_target_of_mem_pretrivialization_atlas_inter
- \- *lemma* topological_fiber_prebundle.is_open_target_pretrivialization_at_inter
- \- *def* topological_fiber_prebundle.trivialization_at
- \+ *def* topological_fiber_prebundle.trivialization_of_mem_pretrivialization_atlas

Modified src/topology/vector_bundle.lean
- \- *lemma* topological_vector_bundle.mem_base_set_trivialization_at
- \- *def* topological_vector_bundle.trivialization_at
- \+ *lemma* topological_vector_bundle_core.coe_coord_change
- \- *lemma* topological_vector_bundle_core.coe_cord_change
- \+ *def* topological_vector_prebundle.to_topological_vector_bundle
- \- *lemma* topological_vector_prebundle.to_topological_vector_bundle
- \- *def* topological_vector_prebundle.trivialization_at
- \+ *def* topological_vector_prebundle.trivialization_of_mem_pretrivialization_atlas



## [2022-04-02 13:47:28](https://github.com/leanprover-community/mathlib/commit/3164b1a)
feat(probability/independence): two lemmas on indep_fun ([#13126](https://github.com/leanprover-community/mathlib/pull/13126))
These two lemmas show that `indep_fun` is preserved under composition by measurable maps and under a.e. equality.
#### Estimated changes
Modified src/probability/independence.lean
- \+ *lemma* probability_theory.indep_fun.ae_eq
- \+ *lemma* probability_theory.indep_fun.comp



## [2022-04-02 13:47:26](https://github.com/leanprover-community/mathlib/commit/1d5b99b)
feat(group_theory/free_product): add (m)range_eq_supr ([#12956](https://github.com/leanprover-community/mathlib/pull/12956))
and lemmas leading to it as inspired by the corresponding lemmas from
`free_groups.lean`.
As suggested by @ocfnash, polish the free group lemmas a bit as well.
#### Estimated changes
Modified src/group_theory/free_group.lean
- \- *theorem* free_group.closure_subset
- \+ *theorem* free_group.lift.range_le
- \- *theorem* free_group.lift.range_subset

Modified src/group_theory/free_product.lean
- \+ *lemma* free_product.lift_mrange_le
- \+ *lemma* free_product.lift_range_le
- \+ *lemma* free_product.mrange_eq_supr
- \+ *lemma* free_product.range_eq_supr



## [2022-04-02 11:56:22](https://github.com/leanprover-community/mathlib/commit/7df5907)
chore(algebra/order/ring): generalisation linter ([#13096](https://github.com/leanprover-community/mathlib/pull/13096))
#### Estimated changes
Modified src/algebra/order/ring.lean
- \+/\- *lemma* add_one_le_two_mul
- \+/\- *lemma* with_bot.bot_lt_mul
- \+/\- *lemma* with_top.mul_lt_top



## [2022-04-02 01:59:06](https://github.com/leanprover-community/mathlib/commit/607f4f8)
feat(model_theory/semantics): A simp lemma for `Theory.model` ([#13117](https://github.com/leanprover-community/mathlib/pull/13117))
Defines `Theory.model_iff` to make it easier to show when a structure models a theory.
#### Estimated changes
Modified src/model_theory/semantics.lean
- \+ *lemma* first_order.language.Theory.model_iff
- \+ *lemma* first_order.language.Theory.model_singleton_iff



## [2022-04-01 22:20:38](https://github.com/leanprover-community/mathlib/commit/6dad5f8)
feat(topology/bornology/basic): alternate way of defining a bornology by its bounded set ([#13064](https://github.com/leanprover-community/mathlib/pull/13064))
More precisely, this defines an alternative to https://leanprover-community.github.io/mathlib_docs/topology/bornology/basic.html#bornology.of_bounded (which is renamed `bornology.of_bounded'`) which expresses the covering condition as containing the singletons, and factors the old version trough it to have a simpler proof.
Note : I chose to add a prime to the old constructor because it's now defined in terms of the new one, so defeq works better this way (i.e lemma about the new constructor can be used whenever the old one is used).
#### Estimated changes
Modified src/analysis/locally_convex/bounded.lean


Modified src/order/filter/cofinite.lean
- \+ *lemma* filter.le_cofinite_iff_compl_singleton_mem

Modified src/topology/bornology/basic.lean
- \+ *lemma* bornology.is_bounded_singleton
- \+ *def* bornology.of_bounded'



## [2022-04-01 22:20:36](https://github.com/leanprover-community/mathlib/commit/6cf5dc5)
feat(topology/support): add lemma `locally_finite.exists_finset_nhd_mul_support_subset` ([#13006](https://github.com/leanprover-community/mathlib/pull/13006))
When using a partition of unity to glue together a family of functions, this lemma allows
us to pass to a finite family in the neighbourhood of any point.
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.subset_coe_filter_of_subset_forall

Modified src/topology/partition_of_unity.lean
- \+ *lemma* partition_of_unity.exists_finset_nhd_support_subset
- \+/\- *def* partition_of_unity.is_subordinate

Modified src/topology/support.lean
- \+ *lemma* locally_finite.exists_finset_nhd_mul_support_subset



## [2022-04-01 20:35:06](https://github.com/leanprover-community/mathlib/commit/912f195)
feat(dynamics/periodic_pts): Lemma about periodic point from periodic point of iterate ([#12940](https://github.com/leanprover-community/mathlib/pull/12940))
#### Estimated changes
Modified src/dynamics/periodic_pts.lean
- \+ *lemma* function.is_periodic_pt_of_mem_periodic_pts_of_is_periodic_pt_iterate



## [2022-04-01 19:21:53](https://github.com/leanprover-community/mathlib/commit/196a48c)
feat(set_theory/ordinal_arithmetic): Coefficients of Cantor Normal Form ([#12681](https://github.com/leanprover-community/mathlib/pull/12681))
We prove all coefficients of the base-b expansion of an ordinal are less than `b`. We also tweak the parameters of various other theorems.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *def* ordinal.CNF
- \+/\- *theorem* ordinal.CNF_fst_le
- \+/\- *theorem* ordinal.CNF_fst_le_log
- \+ *theorem* ordinal.CNF_lt_snd
- \+/\- *theorem* ordinal.CNF_pairwise
- \+/\- *theorem* ordinal.CNF_snd_lt
- \+/\- *theorem* ordinal.CNF_sorted
- \+/\- *theorem* ordinal.one_CNF



## [2022-04-01 17:02:37](https://github.com/leanprover-community/mathlib/commit/a3c753c)
feat(topology/[subset_properties, separation]): bornologies for filter.co[closed_]compact ([#12927](https://github.com/leanprover-community/mathlib/pull/12927))
#### Estimated changes
Modified src/topology/separation.lean
- \+ *lemma* bornology.relatively_compact.is_bounded_iff
- \+ *def* bornology.relatively_compact
- \+ *lemma* bornology.relatively_compact_eq_in_compact
- \+ *lemma* filter.coclosed_compact_le_cofinite

Modified src/topology/subset_properties.lean
- \+ *lemma* bornology.in_compact.is_bounded_iff
- \+ *def* bornology.in_compact
- \+ *lemma* is_compact.compl_mem_coclosed_compact_of_is_closed



## [2022-04-01 16:30:59](https://github.com/leanprover-community/mathlib/commit/e8ef744)
docs(probability/martingale): missing word ([#13113](https://github.com/leanprover-community/mathlib/pull/13113))
#### Estimated changes
Modified src/probability/martingale.lean




## [2022-04-01 16:30:58](https://github.com/leanprover-community/mathlib/commit/b365371)
feat(model_theory/syntax,semantics): Sentences for binary relation properties ([#13087](https://github.com/leanprover-community/mathlib/pull/13087))
Defines sentences for basic properties of binary relations
Proves that realizing these sentences is equivalent to properties in the binary relation library
#### Estimated changes
Modified src/model_theory/semantics.lean
- \+ *lemma* first_order.language.relations.realize_antisymmetric
- \+ *lemma* first_order.language.relations.realize_irreflexive
- \+ *lemma* first_order.language.relations.realize_reflexive
- \+ *lemma* first_order.language.relations.realize_symmetric
- \+ *lemma* first_order.language.relations.realize_total
- \+ *lemma* first_order.language.relations.realize_transitive

Modified src/model_theory/syntax.lean




## [2022-04-01 12:39:38](https://github.com/leanprover-community/mathlib/commit/342a4b0)
feat(data/polynomial/coeff): add `char_zero` instance on polynomials ([#13075](https://github.com/leanprover-community/mathlib/pull/13075))
Besides adding the instance, I also added a warning on the difference between `char_zero R` and `char_p R 0` for general semirings.
An example showing the difference is in [#13080](https://github.com/leanprover-community/mathlib/pull/13080).
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F)
#### Estimated changes
Modified src/algebra/char_p/basic.lean


Modified src/algebra/char_zero.lean


Modified src/data/polynomial/coeff.lean




## [2022-04-01 12:39:37](https://github.com/leanprover-community/mathlib/commit/89275df)
feat(topology/algebra/uniform_group): add characterization of total boundedness ([#12808](https://github.com/leanprover-community/mathlib/pull/12808))
The main result is `totally_bounded_iff_subset_finite_Union_nhds_one`.
We prove it for noncommutative groups, which involves taking opposites.
Add `uniform_group` instance for the opposite group.
Adds several helper lemmas for
* (co-)map of opposites applied to neighborhood filter
* filter basis of uniformity in a uniform group in terms of neighborhood basis at identity
Simplified proofs for `totally_bounded_of_forall_symm` and `totally_bounded.closure`.
#### Estimated changes
Modified src/algebra/group/opposite.lean
- \+ *lemma* mul_opposite.op_div
- \+ *lemma* mul_opposite.unop_div

Modified src/topology/algebra/constructions.lean
- \+ *lemma* mul_opposite.comap_op_nhds
- \+ *lemma* mul_opposite.comap_unop_nhds
- \+ *lemma* mul_opposite.map_op_nhds
- \+ *lemma* mul_opposite.map_unop_nhds

Modified src/topology/algebra/uniform_group.lean
- \+ *lemma* filter.has_basis.uniformity_of_nhds_one
- \+ *lemma* filter.has_basis.uniformity_of_nhds_one_inv_mul
- \+ *lemma* filter.has_basis.uniformity_of_nhds_one_inv_mul_swapped
- \+ *lemma* filter.has_basis.uniformity_of_nhds_one_swapped
- \+ *lemma* totally_bounded_iff_subset_finite_Union_nhds_one
- \+ *lemma* uniformity_eq_comap_inv_mul_nhds_one
- \+ *lemma* uniformity_eq_comap_inv_mul_nhds_one_swapped
- \+ *lemma* uniformity_eq_comap_nhds_one_swapped

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* comap_swap_uniformity
- \+ *lemma* comap_uniformity_mul_opposite

Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* filter.has_basis.totally_bounded_iff
- \- *lemma* is_compact.totally_bounded
- \+ *theorem* totally_bounded.exists_subset



## [2022-04-01 10:46:51](https://github.com/leanprover-community/mathlib/commit/c61f7e8)
chore(model_theory/elementary_maps): Fix Tarski-Vaught Test ([#13102](https://github.com/leanprover-community/mathlib/pull/13102))
Fixes the assumption of the Tarski-Vaught test.
#### Estimated changes
Modified src/model_theory/elementary_maps.lean




## [2022-04-01 10:46:50](https://github.com/leanprover-community/mathlib/commit/e6a0a26)
chore(algebra/order/*): generalisation linter ([#13098](https://github.com/leanprover-community/mathlib/pull/13098))
#### Estimated changes
Modified src/algebra/order/monoid.lean
- \+/\- *lemma* with_bot.add_bot
- \+/\- *lemma* with_bot.add_eq_bot
- \+/\- *lemma* with_bot.bot_add
- \+/\- *lemma* with_bot.coe_add
- \+/\- *lemma* with_bot.coe_bit0
- \+/\- *lemma* with_bot.coe_bit1
- \+/\- *lemma* with_zero.coe_le_coe
- \+/\- *lemma* with_zero.coe_lt_coe

Modified src/algebra/order/monoid_lemmas.lean
- \+/\- *lemma* mul_left_cancel''
- \+/\- *lemma* mul_right_cancel''



## [2022-04-01 10:46:48](https://github.com/leanprover-community/mathlib/commit/8a51798)
chore(order/*): generalisation linter ([#13097](https://github.com/leanprover-community/mathlib/pull/13097))
#### Estimated changes
Modified src/data/set/intervals/basic.lean


Modified src/order/bounded_order.lean
- \+/\- *theorem* with_top.coe_le_iff
- \+/\- *theorem* with_top.lt_iff_exists_coe

Modified src/order/galois_connection.lean
- \+/\- *lemma* galois_coinsertion.strict_mono_l



## [2022-04-01 10:46:47](https://github.com/leanprover-community/mathlib/commit/0e95cad)
chore(algebra/group_power/basic): generalisation linter ([#13095](https://github.com/leanprover-community/mathlib/pull/13095))
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+/\- *lemma* eq_or_eq_neg_of_sq_eq_sq
- \+/\- *lemma* of_add_zsmul
- \+/\- *lemma* of_mul_zpow
- \+/\- *lemma* units.eq_or_eq_neg_of_sq_eq_sq



## [2022-04-01 10:46:46](https://github.com/leanprover-community/mathlib/commit/6652766)
chore(algebra/ring/basic): generalisation linter ([#13094](https://github.com/leanprover-community/mathlib/pull/13094))
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+/\- *lemma* boole_mul
- \+/\- *lemma* commute.bit1_left
- \+/\- *lemma* commute.bit1_right
- \+/\- *lemma* distrib_three_right
- \+/\- *lemma* is_left_regular_of_non_zero_divisor
- \+/\- *lemma* is_right_regular_of_non_zero_divisor
- \+/\- *lemma* mul_boole



## [2022-04-01 10:46:45](https://github.com/leanprover-community/mathlib/commit/e326fe6)
feat(model_theory/basic,language_map): More about `language.mk₂` ([#13090](https://github.com/leanprover-community/mathlib/pull/13090))
Provides instances on `language.mk₂`
Defines `first_order.language.Lhom.mk₂`, a constructor for maps from languages built with `language.mk₂`.
#### Estimated changes
Modified src/model_theory/basic.lean


Modified src/model_theory/language_map.lean
- \+ *lemma* first_order.language.Lhom.mk₂_funext



## [2022-04-01 08:58:07](https://github.com/leanprover-community/mathlib/commit/873f268)
chore(group_theory/group_action/*): generalisation linter ([#13100](https://github.com/leanprover-community/mathlib/pull/13100))
#### Estimated changes
Modified src/group_theory/group_action/basic.lean


Modified src/group_theory/group_action/defs.lean
- \+/\- *lemma* mul_smul_one

Modified src/group_theory/group_action/opposite.lean


Modified src/group_theory/group_action/prod.lean


Modified src/group_theory/group_action/sub_mul_action.lean




## [2022-04-01 07:06:11](https://github.com/leanprover-community/mathlib/commit/3a0c034)
chore(algebra/*): generalisation linter ([#13099](https://github.com/leanprover-community/mathlib/pull/13099))
#### Estimated changes
Modified src/algebra/group/prod.lean
- \+/\- *lemma* prod.fst_div
- \+/\- *lemma* prod.mk_div_mk
- \+/\- *lemma* prod.snd_div
- \+/\- *lemma* prod.swap_div

Modified src/algebra/hom/group.lean
- \+/\- *lemma* monoid_hom.mul_comp
- \+/\- *lemma* monoid_with_zero_hom.to_monoid_hom_injective
- \+/\- *lemma* monoid_with_zero_hom.to_zero_hom_injective
- \+/\- *lemma* mul_hom.mul_comp

Modified src/algebra/hom/group_instances.lean
- \+/\- *def* monoid_hom.compl₂
- \+/\- *lemma* monoid_hom.compl₂_apply



## [2022-04-01 03:39:04](https://github.com/leanprover-community/mathlib/commit/9728396)
chore(scripts): update nolints.txt ([#13101](https://github.com/leanprover-community/mathlib/pull/13101))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


