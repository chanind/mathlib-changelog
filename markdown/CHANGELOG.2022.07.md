## [2022-07-15 18:31:03](https://github.com/leanprover-community/mathlib/commit/15da625)
chore(analysis/locally_convex): golf a proof ([#15323](https://github.com/leanprover-community/mathlib/pull/15323))
#### Estimated changes
Modified src/analysis/locally_convex/balanced_core_hull.lean




## [2022-07-15 18:31:02](https://github.com/leanprover-community/mathlib/commit/959586c)
feat(analysis/special_functions/polar_coord): define polar coordinates, polar change of variable formula in integrals ([#15258](https://github.com/leanprover-community/mathlib/pull/15258))
#### Estimated changes
Added src/analysis/special_functions/polar_coord.lean
- \+ *lemma* has_fderiv_at_polar_coord_symm
- \+ *theorem* integral_comp_polar_coord_symm
- \+ *def* polar_coord
- \+ *lemma* polar_coord_source_ae_eq_univ



## [2022-07-15 18:31:00](https://github.com/leanprover-community/mathlib/commit/f6e9ec3)
chore(ring_theory/ideal/operations): generalise some typeclasses ([#15200](https://github.com/leanprover-community/mathlib/pull/15200))
Using the generalisation linter mostly.
Some more changes are possible surrounding map / comap, but they involve more restructuring, and I want to explore the right definitions of map and comap separately.
All changes here are of the form: dropping commutativity, changing domain to no_zero_divisors (i.e. not assuming nontriviality), or dropping subtraction (ring to semiring).
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* associates.mk_ne_zero'
- \+/\- *lemma* ideal.add_eq_sup
- \+/\- *lemma* ideal.mul_eq_bot
- \+/\- *lemma* ideal.radical_bot_of_is_domain
- \+/\- *theorem* ideal.subset_union



## [2022-07-15 18:30:59](https://github.com/leanprover-community/mathlib/commit/9c8bc91)
feat(linear_algebra/linear_pmap): construct a `linear_pmap` from its graph ([#14922](https://github.com/leanprover-community/mathlib/pull/14922))
Define a partial linear map from its graph. This is a key step in constructing the closure of an linear operator.
#### Estimated changes
Modified src/linear_algebra/linear_pmap.lean
- \+ *lemma* submodule.exists_unique_from_graph
- \+ *lemma* submodule.mem_graph_to_linear_pmap
- \+ *def* submodule.to_linear_pmap
- \+ *lemma* submodule.to_linear_pmap_graph_eq
- \+ *def* submodule.val_from_graph
- \+ *lemma* submodule.val_from_graph_mem



## [2022-07-15 15:49:47](https://github.com/leanprover-community/mathlib/commit/ecaa289)
feat(data/finset/basic): lemmas about `filter`, `cons`, and `disj_union` ([#15385](https://github.com/leanprover-community/mathlib/pull/15385))
The lemma names and statements match the existing multiset versions.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+/\- *def* finset.disj_union
- \+ *lemma* finset.disj_union_comm
- \+ *lemma* finset.disj_union_empty
- \+ *lemma* finset.disj_union_singleton
- \+ *lemma* finset.empty_disj_union
- \+ *theorem* finset.filter_cons
- \+ *theorem* finset.filter_cons_of_neg
- \+ *theorem* finset.filter_cons_of_pos
- \+ *theorem* finset.filter_disj_union
- \+ *lemma* finset.singleton_disj_union



## [2022-07-15 15:49:46](https://github.com/leanprover-community/mathlib/commit/6b2ebac)
chore(category_theory/limits): clean up splittings of (co)product morphisms ([#15382](https://github.com/leanprover-community/mathlib/pull/15382))
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/zero_morphisms.lean




## [2022-07-15 15:49:46](https://github.com/leanprover-community/mathlib/commit/c271266)
feat(ring_theory): the integral closure `C` of `A` is Noetherian over `A` ([#15381](https://github.com/leanprover-community/mathlib/pull/15381))
where `A` is an integrally closed Noetherian domain and `C` is the closure in a finite separable extension `L` of `Frac(A)`
I was going to use this in https://github.com/leanprover-community/mathlib/pull/15315 but it turns out we don't assume separability there. Since it might still be useful elsewhere, I turned it into a new PR.
The proof was already in mathlib, as part of showing that the integral closure of a Dedekind domain is Noetherian, so I could just split off the part that dealt with Noetherianness.
#### Estimated changes
Modified src/ring_theory/dedekind_domain/integral_closure.lean
- \+ *lemma* is_integral_closure.is_noetherian



## [2022-07-15 15:49:45](https://github.com/leanprover-community/mathlib/commit/30220eb)
feat(order/rel_iso): relation embedding from empty type ([#15372](https://github.com/leanprover-community/mathlib/pull/15372))
#### Estimated changes
Modified src/order/rel_iso.lean
- \+ *def* rel_embedding.of_is_empty



## [2022-07-15 15:49:43](https://github.com/leanprover-community/mathlib/commit/d6b861b)
chore(algebra/order/archimedean): Move material to correct files ([#15290](https://github.com/leanprover-community/mathlib/pull/15290))
Move `round` and some `floor` lemmas to `algebra.order.floor`. Move the `rat.cast` lemmas about `floor` and `ceil` to `data.rat.floor`. Merge a few sections together now that unrelated lemmas are gone.
#### Estimated changes
Modified src/algebra/order/archimedean.lean
- \- *lemma* abs_sub_round
- \+ *lemma* archimedean_iff_nat_le
- \- *theorem* archimedean_iff_nat_le
- \+ *lemma* archimedean_iff_nat_lt
- \- *theorem* archimedean_iff_nat_lt
- \+ *lemma* archimedean_iff_rat_le
- \- *theorem* archimedean_iff_rat_le
- \+ *lemma* archimedean_iff_rat_lt
- \- *theorem* archimedean_iff_rat_lt
- \+/\- *lemma* exists_mem_Ico_zpow
- \+/\- *lemma* exists_mem_Ioc_zpow
- \+/\- *lemma* exists_nat_pow_near_of_lt_one
- \+/\- *lemma* exists_pow_lt_of_lt_one
- \+ *lemma* exists_rat_gt
- \- *theorem* exists_rat_gt
- \+ *lemma* exists_rat_near
- \- *theorem* exists_rat_near
- \- *theorem* rat.cast_fract
- \- *theorem* rat.ceil_cast
- \- *theorem* rat.floor_cast
- \- *theorem* rat.round_cast
- \- *def* round
- \- *lemma* round_one
- \- *lemma* round_zero
- \- *lemma* sub_floor_div_mul_lt
- \- *lemma* sub_floor_div_mul_nonneg

Modified src/algebra/order/floor.lean
- \+ *lemma* abs_sub_round
- \+ *lemma* int.sub_floor_div_mul_lt
- \+ *lemma* int.sub_floor_div_mul_nonneg
- \+ *def* round
- \+ *lemma* round_one
- \+ *lemma* round_zero

Modified src/analysis/special_functions/trigonometric/basic.lean


Modified src/data/rat/floor.lean
- \+ *lemma* rat.cast_fract
- \+ *lemma* rat.ceil_cast
- \+ *lemma* rat.floor_cast
- \+ *lemma* rat.round_cast



## [2022-07-15 15:49:42](https://github.com/leanprover-community/mathlib/commit/8199f67)
feat(ring_theory/power_series/well_known): Coefficients of sin and cos ([#15287](https://github.com/leanprover-community/mathlib/pull/15287))
This PR adds lemmas for the coefficients of sin and cos.
#### Estimated changes
Modified src/ring_theory/power_series/well_known.lean
- \+ *lemma* power_series.coeff_cos_bit0
- \+ *lemma* power_series.coeff_cos_bit1
- \+ *lemma* power_series.coeff_sin_bit0
- \+ *lemma* power_series.coeff_sin_bit1



## [2022-07-15 15:49:41](https://github.com/leanprover-community/mathlib/commit/85cd3e6)
feat(category_theory/yoneda): coyoneda.obj_op_op ([#14831](https://github.com/leanprover-community/mathlib/pull/14831))
#### Estimated changes
Modified src/category_theory/yoneda.lean
- \+ *def* category_theory.coyoneda.obj_op_op



## [2022-07-15 13:58:45](https://github.com/leanprover-community/mathlib/commit/0807d66)
chore(linear_algebra/alternating): add an is_central_scalar instance ([#15359](https://github.com/leanprover-community/mathlib/pull/15359))
#### Estimated changes
Modified src/linear_algebra/alternating.lean




## [2022-07-15 13:58:34](https://github.com/leanprover-community/mathlib/commit/fc63bdd)
chore(linear_algebra/matrix/hermitian): move `matrix.conj_transpose_map` to the same file as `matrix.transpose_map` ([#15297](https://github.com/leanprover-community/mathlib/pull/15297))
Also restates the hypothesis using `function.semiconj` since that has more API and is definitionally easier to work with.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.conj_transpose_map

Modified src/linear_algebra/matrix/hermitian.lean
- \- *lemma* matrix.conj_transpose_map



## [2022-07-15 13:03:06](https://github.com/leanprover-community/mathlib/commit/1a424e1)
chore(number_theory/modular): add missing lemmas to squeeze simps ([#15351](https://github.com/leanprover-community/mathlib/pull/15351))
I was running into some timeouts in `exists_smul_mem_fd` when making some other changes; this extracts some `simp` calls to standalone lemmas. These lemmas don't have particularly fast proofs either, but the statements are much simpler so will be easier to speed up in future if we need to.
Simp-normal form in this file seems to aggressively unfold to matrices, so we can't mark these new lemmas `simp`.
At some point the simp lemmas for modular forms might want to be revisited.
#### Estimated changes
Modified src/number_theory/modular.lean
- \+ *lemma* modular_group.T_inv_mul_apply_one
- \+ *lemma* modular_group.T_mul_apply_one
- \+ *lemma* modular_group.T_pow_mul_apply_one
- \+ *lemma* modular_group.im_T_inv_smul
- \+ *lemma* modular_group.im_T_smul
- \+ *lemma* modular_group.im_T_zpow_smul
- \+ *lemma* modular_group.re_T_inv_smul
- \+ *lemma* modular_group.re_T_smul
- \+ *lemma* modular_group.re_T_zpow_smul



## [2022-07-15 12:02:33](https://github.com/leanprover-community/mathlib/commit/ca872b6)
style(set_theory/game/nim): `O` → `o` ([#15361](https://github.com/leanprover-community/mathlib/pull/15361))
This is the only file that uses uppercase variable names for ordinals - we standardize it to match all the others.
#### Estimated changes
Modified src/set_theory/game/nim.lean
- \+/\- *lemma* pgame.grundy_value_eq_iff_equiv_nim
- \+/\- *lemma* pgame.nim.add_equiv_zero_iff_eq
- \+/\- *lemma* pgame.nim.add_fuzzy_zero_iff_ne
- \+/\- *lemma* pgame.nim.equiv_iff_eq
- \+/\- *lemma* pgame.nim.exists_move_left_eq
- \+/\- *lemma* pgame.nim.exists_ordinal_move_left_eq
- \+/\- *lemma* pgame.nim.grundy_value
- \+/\- *lemma* pgame.nim.left_moves_nim
- \+/\- *lemma* pgame.nim.move_left_nim'
- \+/\- *lemma* pgame.nim.move_left_nim
- \+/\- *lemma* pgame.nim.move_left_nim_heq
- \+/\- *lemma* pgame.nim.move_right_nim'
- \+/\- *lemma* pgame.nim.move_right_nim
- \+/\- *lemma* pgame.nim.move_right_nim_heq
- \+/\- *lemma* pgame.nim.neg_nim
- \+/\- *lemma* pgame.nim.nim_birthday
- \+/\- *lemma* pgame.nim.nim_def
- \+/\- *lemma* pgame.nim.non_zero_first_wins
- \+/\- *lemma* pgame.nim.right_moves_nim
- \+/\- *theorem* pgame.nim.to_left_moves_nim_symm_lt
- \+/\- *theorem* pgame.nim.to_right_moves_nim_symm_lt



## [2022-07-15 12:02:32](https://github.com/leanprover-community/mathlib/commit/ecef686)
feat(algebra/category/Group):  The forgetful-units adjunction between `Group` and `Mon`. ([#15330](https://github.com/leanprover-community/mathlib/pull/15330))
#### Estimated changes
Modified src/algebra/category/Group/adjunctions.lean
- \+ *def* CommGroup.forget₂_CommMon_adj
- \+ *def* CommMon.units
- \+ *def* Group.forget₂_Mon_adj
- \+ *def* Mon.units



## [2022-07-15 12:02:31](https://github.com/leanprover-community/mathlib/commit/863a30a)
feat(category_theory/*/algebra): epi_of_epi and mono_of_mono ([#15121](https://github.com/leanprover-community/mathlib/pull/15121))
This PR proves that a morphism whose underlying carrier part is an epi/mono, is itself an epi/mono. Migrated and generalised from #LTE.
#### Estimated changes
Modified src/category_theory/endofunctor/algebra.lean
- \+ *lemma* category_theory.endofunctor.algebra.epi_of_epi
- \+ *lemma* category_theory.endofunctor.algebra.mono_of_mono
- \+ *lemma* category_theory.endofunctor.coalgebra.epi_of_epi
- \+ *lemma* category_theory.endofunctor.coalgebra.mono_of_mono

Modified src/category_theory/monad/algebra.lean
- \+ *lemma* category_theory.comonad.algebra_epi_of_epi
- \+ *lemma* category_theory.comonad.algebra_mono_of_mono
- \+ *lemma* category_theory.monad.algebra_epi_of_epi
- \+ *lemma* category_theory.monad.algebra_mono_of_mono



## [2022-07-15 10:49:36](https://github.com/leanprover-community/mathlib/commit/72d7b4e)
feat(measure_theory/measure/measure_space): generalize measure.comap ([#15343](https://github.com/leanprover-community/mathlib/pull/15343))
Generalize comap to functions verifying `injective f ∧ ∀ s, measurable_set s → null_measurable_set (f '' s) μ`.
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+/\- *def* measure_theory.measure.comap
- \+ *lemma* measure_theory.measure.comap_apply₀
- \+ *def* measure_theory.measure.comapₗ
- \+ *lemma* measure_theory.measure.comapₗ_apply
- \+ *lemma* measure_theory.measure.comapₗ_eq_comap



## [2022-07-15 10:49:35](https://github.com/leanprover-community/mathlib/commit/4f23c9b)
feat(number_theory/slash_actions): Slash actions class for modular forms ([#15007](https://github.com/leanprover-community/mathlib/pull/15007))
We define a new class of slash actions which are to be used in the definition of modular forms (see [#13250](https://github.com/leanprover-community/mathlib/pull/13250)).
#### Estimated changes
Added src/number_theory/modular_forms/slash_actions.lean
- \+ *def* modular_forms.slash
- \+ *lemma* modular_forms.slash_add
- \+ *lemma* modular_forms.slash_mul_one
- \+ *lemma* modular_forms.slash_right_action
- \+ *lemma* modular_forms.smul_slash
- \+ *def* monoid_hom_slash_action



## [2022-07-15 09:35:51](https://github.com/leanprover-community/mathlib/commit/e166cce)
chore(analysis/inner_product_space): split slow proof ([#15271](https://github.com/leanprover-community/mathlib/pull/15271))
This proof times out in the kernel at about 90 000 out of 100 000 heartbeats, and [#14894](https://github.com/leanprover-community/mathlib/pull/14894) pushed it over the edge of timing out (except [#15251](https://github.com/leanprover-community/mathlib/pull/15251) upped the timeout limits so everything sitll builds at the moment). I don't know enough about the kernel to debug why it doesn't like this proof, but splitting it into a `rw` part and a part that uses defeq seems to fix the timeout (moving it back down to about 60 000 out of 100 000 heartbeats).
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Timeout.20in.20the.20kernel/near/289294804
#### Estimated changes
Modified src/analysis/inner_product_space/l2_space.lean
- \+ *lemma* orthonormal.linear_isometry_equiv_symm_apply_single_one



## [2022-07-15 09:35:50](https://github.com/leanprover-community/mathlib/commit/fc78e3c)
feat(category_theory/abelian/*): functors that preserve finite limits and colimits preserve exactness ([#14581](https://github.com/leanprover-community/mathlib/pull/14581))
If $F$ is a functor between two abelian categories which preserves limits and colimits, then it preserves exactness.
#### Estimated changes
Modified src/category_theory/abelian/basic.lean


Modified src/category_theory/abelian/exact.lean
- \+ *lemma* category_theory.functor.map_exact

Added src/category_theory/limits/preserves/shapes/images.lean
- \+ *lemma* category_theory.preserves_image.factor_thru_image_comp_hom
- \+ *lemma* category_theory.preserves_image.hom_comp_map_image_ι
- \+ *lemma* category_theory.preserves_image.inv_comp_image_ι_map
- \+ *def* category_theory.preserves_image.iso

Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* category_theory.limits.image.is_image_lift



## [2022-07-15 07:02:47](https://github.com/leanprover-community/mathlib/commit/5e2e804)
feat(order/bounded_order): `subrelation r s ↔ r ≤ s` ([#15357](https://github.com/leanprover-community/mathlib/pull/15357))
We have to place the lemma here, since comparing relations requires `has_le Prop`. I haven't made any judgement on whether either of them should be a simp-normal form.
#### Estimated changes
Modified src/order/bounded_order.lean
- \+ *lemma* subrelation_iff_le



## [2022-07-15 07:02:46](https://github.com/leanprover-community/mathlib/commit/2406dc5)
feat(topology/support): tsupport of product is a subset of tsupport ([#15346](https://github.com/leanprover-community/mathlib/pull/15346))
#### Estimated changes
Modified src/topology/support.lean
- \+ *lemma* tsupport_mul_subset_left
- \+ *lemma* tsupport_mul_subset_right



## [2022-07-15 07:02:44](https://github.com/leanprover-community/mathlib/commit/daf1117)
feat(field_theory/tower): if `L / K / F` is finite, so is `K / F` ([#15303](https://github.com/leanprover-community/mathlib/pull/15303))
This result came up in the discussion of [#15191](https://github.com/leanprover-community/mathlib/pull/15191), where I couldn't find it. (In the end we didn't up needing it.) I saw we already had finiteness of `L / K` (in fact, for any vector space instead of the field `L`) as `finite_dimensional.right`, so I made the `left` version too.
Also use this to provide an instance where `K` is an intermediate field.
#### Estimated changes
Modified src/field_theory/intermediate_field.lean


Modified src/field_theory/tower.lean
- \+ *theorem* finite_dimensional.left



## [2022-07-15 05:42:11](https://github.com/leanprover-community/mathlib/commit/2123bc3)
feat(measure_theory/measurable_space_def): add `generate_from_induction` ([#15342](https://github.com/leanprover-community/mathlib/pull/15342))
This lemma does (almost?) the same thing as `induction (ht : measurable_set[generate_from C] t)`, but the hypotheses in the generated subgoals are much easier to read.
#### Estimated changes
Modified src/measure_theory/measurable_space_def.lean
- \+ *lemma* measurable_space.generate_from_induction



## [2022-07-15 05:42:10](https://github.com/leanprover-community/mathlib/commit/0e72a4e)
feat(data/polynomial/laurent): define `degree` and some API ([#15225](https://github.com/leanprover-community/mathlib/pull/15225))
This PR introduces the `degree` for Laurent polynomials.  It takes values in `with_bot ℤ`and is defined as `f.support.max`.
It may make sense to define a "degree" on any `add_monoid_algebra` whose value group is `linear_ordered`, but I am only defining `degree` for Laurent polynomials.
The PR also proves some API lemmas about support and relationship between the degree of a Laurent polynomial and the degree with polynomials, seen as Laurent polynomials.
In future PRs I intend to define also `int_degree`, analogous to `nat_degree` of polynomials.
#### Estimated changes
Modified src/data/polynomial/laurent.lean
- \+ *def* laurent_polynomial.degree
- \+ *lemma* laurent_polynomial.degree_C
- \+ *lemma* laurent_polynomial.degree_C_ite
- \+ *lemma* laurent_polynomial.degree_C_le
- \+ *lemma* laurent_polynomial.degree_C_mul_T
- \+ *lemma* laurent_polynomial.degree_C_mul_T_ite
- \+ *lemma* laurent_polynomial.degree_C_mul_T_le
- \+ *lemma* laurent_polynomial.degree_T
- \+ *lemma* laurent_polynomial.degree_T_le
- \+ *lemma* laurent_polynomial.degree_eq_bot_iff
- \+ *lemma* laurent_polynomial.degree_zero
- \+ *lemma* laurent_polynomial.support_C_mul_T
- \+ *lemma* laurent_polynomial.support_C_mul_T_of_ne_zero
- \+ *lemma* laurent_polynomial.to_laurent_support
- \+ *lemma* polynomial.to_laurent_ne_zero



## [2022-07-15 01:25:38](https://github.com/leanprover-community/mathlib/commit/09a7f7a)
refactor(algebra/algebra/subalgebra/basic): Remove `'` from `subalgebra.comap'`  ([#15349](https://github.com/leanprover-community/mathlib/pull/15349))
This PR removes `'` from `subalgebra.comap'`.
<https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/subalgebra.2Ecomap'>
#### Estimated changes
Modified src/algebra/algebra/subalgebra/basic.lean
- \+/\- *theorem* algebra.comap_top
- \- *def* subalgebra.comap'
- \+ *def* subalgebra.comap
- \+/\- *lemma* subalgebra.gc_map_comap

Modified src/topology/algebra/algebra.lean
- \- *lemma* subalgebra.topological_closure_comap'_homeomorph
- \+ *lemma* subalgebra.topological_closure_comap_homeomorph

Modified src/topology/continuous_function/polynomial.lean
- \- *lemma* polynomial_functions.comap'_comp_right_alg_hom_Icc_homeo_I
- \+ *lemma* polynomial_functions.comap_comp_right_alg_hom_Icc_homeo_I

Modified src/topology/continuous_function/stone_weierstrass.lean


Modified src/topology/continuous_function/weierstrass.lean




## [2022-07-15 01:25:37](https://github.com/leanprover-community/mathlib/commit/8d749e6)
refactor(field_theory/*): Replace weaker `alg_hom.fintype` with stronger `alg_hom.fintype` ([#15345](https://github.com/leanprover-community/mathlib/pull/15345))
Mathlib has two instances of `alg_hom.fintype`. The version in `field_theory.fixed` is weaker (it assumes finite-dimensionality of the target). The version in `field_theory.primitive_element` is stronger (it does not assume finite-dimensionality of the target). So why not replace the weaker version by the stronger version?
#### Estimated changes
Modified src/field_theory/fixed.lean
- \+ *lemma* aux_inj_roots_of_min_poly

Modified src/field_theory/primitive_element.lean
- \- *lemma* field.aux_inj_roots_of_min_poly



## [2022-07-15 01:25:36](https://github.com/leanprover-community/mathlib/commit/b8b18fa)
feat(order/complete_boolean_algebra): A frame is distributive ([#15340](https://github.com/leanprover-community/mathlib/pull/15340))
`frame α`/`coframe α` imply `distrib_lattice α`.
#### Estimated changes
Modified src/order/complete_boolean_algebra.lean


Modified src/order/lattice.lean
- \+ *def* distrib_lattice.of_inf_sup_le



## [2022-07-15 01:25:35](https://github.com/leanprover-community/mathlib/commit/11bfd9c)
chore(logic/equiv/basic): remove `nolint` ([#15329](https://github.com/leanprover-community/mathlib/pull/15329))
#### Estimated changes
Modified src/logic/equiv/basic.lean




## [2022-07-15 01:25:34](https://github.com/leanprover-community/mathlib/commit/6f48d95)
feat(ring_theory/localization/basic): add `mk_sum` ([#15261](https://github.com/leanprover-community/mathlib/pull/15261))
add a missing lemma stating that $\frac{\sum_i, a\_i}{b}=\sum_i\frac{a_i}b$
#### Estimated changes
Modified src/ring_theory/localization/basic.lean
- \+ *def* localization.mk_add_monoid_hom
- \+ *lemma* localization.mk_list_sum
- \+ *lemma* localization.mk_multiset_sum
- \+ *lemma* localization.mk_sum



## [2022-07-14 22:11:08](https://github.com/leanprover-community/mathlib/commit/635b858)
doc(logic/equiv/basic): explicitly state functions equivalences are based on ([#15354](https://github.com/leanprover-community/mathlib/pull/15354))
This should make them more searchable. Also some trivial spacing fixes.
#### Estimated changes
Modified src/logic/equiv/basic.lean




## [2022-07-14 22:11:07](https://github.com/leanprover-community/mathlib/commit/466b892)
feat(analysis/asymptotics/asymptotics): generalize, golf ([#15010](https://github.com/leanprover-community/mathlib/pull/15010))
* add `is_o_iff_nat_mul_le`, `is_o_iff_nat_mul_le'`, `is_o_irrefl`, `is_O.not_is_o`, `is_o.not_is_O`;
* generalize lemmas about `1 = o(f)`, `1 = O(f)`, `f = o(1)`, `f = O(1)` to `[has_one F] [norm_one_class F]`, add some `@[simp]` attrs;
* rename `is_O_one_of_tendsto` to `filter.tendsto.is_O_one`;
* golf some proofs
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/analysis/asymptotics/asymptotics.lean
- \+ *theorem* asymptotics.is_O.not_is_o
- \+/\- *theorem* asymptotics.is_O.trans_tendsto_nhds
- \+/\- *theorem* asymptotics.is_O_const_one
- \+ *theorem* asymptotics.is_O_iff_is_bounded_under_le_div
- \+ *theorem* asymptotics.is_O_one_iff
- \- *theorem* asymptotics.is_O_one_of_tendsto
- \+/\- *theorem* asymptotics.is_O_with_const_one
- \+ *lemma* asymptotics.is_O_with_inv
- \+ *theorem* asymptotics.is_o.not_is_O
- \+ *lemma* asymptotics.is_o_iff_nat_mul_le'
- \+ *lemma* asymptotics.is_o_iff_nat_mul_le
- \+ *lemma* asymptotics.is_o_iff_nat_mul_le_aux
- \+ *theorem* asymptotics.is_o_irrefl'
- \+ *theorem* asymptotics.is_o_irrefl
- \+/\- *theorem* asymptotics.is_o_one_iff
- \+ *theorem* asymptotics.is_o_one_left_iff
- \+ *theorem* filter.tendsto.is_O_one

Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/complex/phragmen_lindelof.lean




## [2022-07-14 17:53:30](https://github.com/leanprover-community/mathlib/commit/356f889)
golf(data/polynomial/degree/definitions): golf three proofs ([#15236](https://github.com/leanprover-community/mathlib/pull/15236))
Lemmas `degree_update_le`, `degree_nonneg_iff_ne_zero` and `degree_le_iff_coeff_zero` have shorter proofs.
All three lemmas use the same axioms as they did before: 
```lean
propext
quot.sound
classical.choice
```
The golfing in `degree_le_iff_coeff_zero` is motivated by [#15199](https://github.com/leanprover-community/mathlib/pull/15199), where the older version no longer compiles.
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean




## [2022-07-14 17:53:29](https://github.com/leanprover-community/mathlib/commit/0bea64b)
feat(ring_theory/integrally_closed): if x is in Frac R such that x^n is in R then x is in R ([#12812](https://github.com/leanprover-community/mathlib/pull/12812))
#### Estimated changes
Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_integral.pow_iff
- \+ *lemma* is_integral_of_pow

Modified src/ring_theory/integrally_closed.lean
- \+ *lemma* is_integrally_closed.exists_algebra_map_eq_of_is_integral_pow
- \+ *lemma* is_integrally_closed.exists_algebra_map_eq_of_pow_mem_subalgebra
- \+/\- *lemma* is_integrally_closed.is_integral_iff



## [2022-07-14 13:52:46](https://github.com/leanprover-community/mathlib/commit/f3fac40)
feat(data/fin/basic): add a reflected instance ([#15337](https://github.com/leanprover-community/mathlib/pull/15337))
This helps with writing tactics to expand fixed-size matrices into their components.
This instance is written using the same approach as the `int.has_reflect` instance.
#### Estimated changes
Modified src/data/fin/basic.lean




## [2022-07-14 13:52:45](https://github.com/leanprover-community/mathlib/commit/48b7ad6)
chore(*): upgrade to lean 3.45.0c ([#15325](https://github.com/leanprover-community/mathlib/pull/15325))
The `decidable_eq json` instance has moved to core, since it was needed for tests there too.
#### Estimated changes
Modified leanpkg.toml


Modified test/polyrith.lean




## [2022-07-14 13:52:44](https://github.com/leanprover-community/mathlib/commit/51f5e6c)
feat(algebra/module/linear_map): use morphisms class for lemmas about linear [pre]images of `c • S` ([#15103](https://github.com/leanprover-community/mathlib/pull/15103))
#### Estimated changes
Modified src/algebra/module/equiv.lean
- \- *lemma* linear_equiv.image_smul_set
- \- *lemma* linear_equiv.image_smul_setₛₗ
- \- *lemma* linear_equiv.preimage_smul_set
- \- *lemma* linear_equiv.preimage_smul_setₛₗ

Modified src/algebra/module/linear_map.lean
- \+ *lemma* image_smul_set
- \+ *lemma* image_smul_setₛₗ
- \- *lemma* linear_map.image_smul_set
- \- *lemma* linear_map.image_smul_setₛₗ
- \- *lemma* linear_map.preimage_smul_set
- \- *lemma* linear_map.preimage_smul_setₛₗ
- \+ *lemma* preimage_smul_set
- \+ *lemma* preimage_smul_setₛₗ

Modified src/analysis/locally_convex/bounded.lean


Modified src/measure_theory/function/jacobian.lean


Modified src/topology/algebra/module/basic.lean
- \- *lemma* continuous_linear_equiv.image_smul_set
- \- *lemma* continuous_linear_equiv.image_smul_setₛₗ
- \- *lemma* continuous_linear_equiv.preimage_smul_set
- \- *lemma* continuous_linear_equiv.preimage_smul_setₛₗ
- \- *lemma* continuous_linear_map.image_smul_set
- \- *lemma* continuous_linear_map.image_smul_setₛₗ
- \- *lemma* continuous_linear_map.preimage_smul_set
- \- *lemma* continuous_linear_map.preimage_smul_setₛₗ



## [2022-07-14 12:49:30](https://github.com/leanprover-community/mathlib/commit/2570613)
feat(measure_theory/integral/set_integral): add `set_integral_indicator` ([#15344](https://github.com/leanprover-community/mathlib/pull/15344))
#### Estimated changes
Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_theory.set_integral_indicator



## [2022-07-14 09:37:11](https://github.com/leanprover-community/mathlib/commit/f3ae2d0)
feat(measure_theory/constructions/prod): The layercake integral. ([#14424](https://github.com/leanprover-community/mathlib/pull/14424))
Prove the layercake formula, a.k.a. Cavalieri's principle, often used in measure theory and probability theory. It will in particular be a part of the proof of the portmanteau theorem.
#### Estimated changes
Modified src/measure_theory/function/l1_space.lean


Modified src/measure_theory/function/strongly_measurable.lean
- \- *lemma* measure_theory.ae_measurable_zero_measure
- \+ *lemma* measure_theory.ae_strongly_measurable_zero_measure

Added src/measure_theory/integral/layercake.lean
- \+ *theorem* measure_theory.lintegral_comp_eq_lintegral_meas_le_mul
- \+ *lemma* measure_theory.lintegral_comp_eq_lintegral_meas_le_mul_of_measurable
- \+ *theorem* measure_theory.lintegral_eq_lintegral_meas_le
- \+ *theorem* measure_theory.lintegral_rpow_eq_lintegral_meas_le_mul

Modified src/measure_theory/measure/ae_measurable.lean
- \+ *lemma* ae_measurable.exists_measurable_nonneg
- \+ *lemma* ae_measurable_Ioi_of_forall_Ioc

Modified src/measure_theory/measure/lebesgue.lean
- \+ *lemma* measurable_set_graph
- \+ *lemma* measurable_set_region_between_cc
- \+ *lemma* measurable_set_region_between_co
- \+ *lemma* measurable_set_region_between_oc



## [2022-07-14 05:43:46](https://github.com/leanprover-community/mathlib/commit/073c3ac)
feat(ring_theory): Basic framework for classes of ring homomorphisms ([#14966](https://github.com/leanprover-community/mathlib/pull/14966))
#### Estimated changes
Modified src/ring_theory/local_properties.lean
- \+ *lemma* localization_preserves_surjective
- \+ *def* ring_hom.holds_for_localization_away
- \- *lemma* ring_hom.localization_away_of_localization_preserves
- \+ *lemma* ring_hom.localization_preserves.away
- \+ *def* ring_hom.of_localization_prime
- \+ *def* ring_hom.of_localization_span_target
- \+ *lemma* ring_hom.property_is_local.of_localization_span
- \+ *lemma* ring_hom.property_is_local.respects_iso
- \+ *lemma* surjective_of_localization_span

Modified src/ring_theory/localization/away.lean
- \+ *lemma* is_localization.away_of_is_unit_of_bijective

Added src/ring_theory/ring_hom_properties.lean
- \+ *lemma* ring_hom.respects_iso.cancel_left_is_iso
- \+ *lemma* ring_hom.respects_iso.cancel_right_is_iso
- \+ *lemma* ring_hom.respects_iso.is_localization_away_iff
- \+ *def* ring_hom.respects_iso
- \+ *lemma* ring_hom.stable_under_base_change.pushout_inl
- \+ *def* ring_hom.stable_under_base_change
- \+ *lemma* ring_hom.stable_under_composition.respects_iso
- \+ *def* ring_hom.stable_under_composition



## [2022-07-14 03:55:19](https://github.com/leanprover-community/mathlib/commit/e479bfb)
chore(scripts): update nolints.txt ([#15332](https://github.com/leanprover-community/mathlib/pull/15332))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2022-07-13 21:11:31](https://github.com/leanprover-community/mathlib/commit/b89df0a)
chore(set_theory/pgame): remove redundant `dsimp` ([#15312](https://github.com/leanprover-community/mathlib/pull/15312))
Thanks to [#14660](https://github.com/leanprover-community/mathlib/pull/14660), we no longer need the `dsimp, simp` pattern to prove some results.
#### Estimated changes
Modified src/set_theory/game/pgame.lean




## [2022-07-13 21:11:29](https://github.com/leanprover-community/mathlib/commit/4302cb7)
chore(data/matrix/block): lemmas about swapping blocks of matrices ([#15298](https://github.com/leanprover-community/mathlib/pull/15298))
Also makes `equiv.sum_comm` reduce to `equiv.sum_swap` slightly more agressively.
#### Estimated changes
Modified src/data/matrix/block.lean
- \+ *lemma* matrix.from_blocks_minor_sum_swap_left
- \+ *lemma* matrix.from_blocks_minor_sum_swap_right
- \+ *lemma* matrix.from_blocks_minor_sum_swap_sum_swap

Modified src/logic/equiv/basic.lean




## [2022-07-13 21:11:28](https://github.com/leanprover-community/mathlib/commit/5590b0a)
doc(set_theory/ordinal/cantor_normal_form): document most theorems ([#15227](https://github.com/leanprover-community/mathlib/pull/15227))
The API around CNF is somewhat hard to wrap around, so we document many of the theorems.
#### Estimated changes
Modified src/set_theory/ordinal/cantor_normal_form.lean




## [2022-07-13 21:11:27](https://github.com/leanprover-community/mathlib/commit/5744b50)
chore(order/order_iso_nat): remove `decidable_pred` assumption from `subtype.order_iso_of_nat` ([#15190](https://github.com/leanprover-community/mathlib/pull/15190))
This is a `noncomputable def` anyways, so the assumption wasn't really helping anyone.
#### Estimated changes
Modified src/data/nat/nth.lean
- \+/\- *lemma* nat.nth_eq_order_iso_of_nat

Modified src/order/order_iso_nat.lean
- \+/\- *def* nat.order_embedding_of_set



## [2022-07-13 21:11:26](https://github.com/leanprover-community/mathlib/commit/0864805)
feat(data/finset/basic): Add `decidable_nonempty` for finsets. ([#15170](https://github.com/leanprover-community/mathlib/pull/15170))
Also remove some redundant decidable instances in multiset and list.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean


Modified src/data/bool/all_any.lean


Modified src/data/finset/basic.lean


Modified src/data/multiset/basic.lean
- \- *def* multiset.decidable_exists_multiset



## [2022-07-13 21:11:24](https://github.com/leanprover-community/mathlib/commit/1e82f5e)
feat(linear_algebra/projectivization/independence): defines (in)dependence of points in projective space ([#14542](https://github.com/leanprover-community/mathlib/pull/14542))
This PR only provides definitions and basic lemmas. In an upcoming pull request we use this to prove the axioms for an abstract projective space.
#### Estimated changes
Modified src/linear_algebra/projective_space/basic.lean
- \+ *lemma* projectivization.mk_eq_mk_iff'

Added src/linear_algebra/projective_space/independence.lean
- \+ *lemma* projectivization.dependent_iff
- \+ *lemma* projectivization.dependent_iff_not_independent
- \+ *lemma* projectivization.dependent_pair_iff_eq
- \+ *lemma* projectivization.independent_iff
- \+ *lemma* projectivization.independent_iff_complete_lattice_independent
- \+ *lemma* projectivization.independent_iff_not_dependent
- \+ *lemma* projectivization.independent_pair_iff_neq



## [2022-07-13 18:30:28](https://github.com/leanprover-community/mathlib/commit/f731315)
feat(topology/local_homeomorph): "injectivity" local_homeomorph.prod ([#15311](https://github.com/leanprover-community/mathlib/pull/15311))
* Also some other lemmas about `local_equiv` and `local_homeomorph`
* From the sphere eversion project
#### Estimated changes
Modified src/data/set/prod.lean
- \+ *lemma* set.prod_eq_prod_iff
- \+ *lemma* set.prod_eq_prod_iff_of_nonempty

Modified src/logic/basic.lean
- \+ *lemma* forall_forall_const

Modified src/logic/equiv/local_equiv.lean
- \+ *lemma* local_equiv.mem_symm_trans_source
- \+ *lemma* local_equiv.trans_apply

Modified src/topology/local_homeomorph.lean
- \+ *lemma* local_homeomorph.image_source_eq_target
- \+ *lemma* local_homeomorph.prod_eq_prod_of_nonempty'
- \+ *lemma* local_homeomorph.prod_eq_prod_of_nonempty
- \+ *lemma* local_homeomorph.symm_image_target_eq_source
- \+ *lemma* local_homeomorph.trans_apply



## [2022-07-13 18:30:27](https://github.com/leanprover-community/mathlib/commit/25f60b4)
feat(analysis/calculus/cont_diff): extra lemmas about cont_diff_within_at ([#15309](https://github.com/leanprover-community/mathlib/pull/15309))
* Also some lemmas about `fderiv_within` and `nhds_within`.
* From the sphere eversion project
#### Estimated changes
Modified src/analysis/calculus/cont_diff.lean
- \+ *lemma* cont_diff_within_at.congr_of_eventually_eq_insert
- \+ *lemma* cont_diff_within_at.fderiv_within'
- \+ *lemma* cont_diff_within_at.fderiv_within
- \+ *lemma* cont_diff_within_at.has_fderiv_within_at_nhds
- \+ *lemma* cont_diff_within_at_succ_iff_has_fderiv_within_at_of_mem

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* fderiv_within.comp₃
- \+ *lemma* filter.eventually_eq.fderiv_within_eq_nhds
- \+ *theorem* has_fderiv_within_at.mono_of_mem

Modified src/topology/continuous_on.lean
- \+ *lemma* nhds_within_le_iff



## [2022-07-13 18:30:26](https://github.com/leanprover-community/mathlib/commit/51f76d0)
feat(tactic/linear_combination): add parser for `h / a` ([#15284](https://github.com/leanprover-community/mathlib/pull/15284))
As reported during LFTCM 2022.
#### Estimated changes
Modified src/tactic/linear_combination.lean


Modified src/tactic/polyrith.lean


Modified test/linear_combination.lean


Modified test/polyrith.lean




## [2022-07-13 18:30:25](https://github.com/leanprover-community/mathlib/commit/be53c7c)
feat(topology/algebra/order): ⁻¹ continuous for linear ordered fields ([#15022](https://github.com/leanprover-community/mathlib/pull/15022))
Closes [#12781](https://github.com/leanprover-community/mathlib/pull/12781).
#### Estimated changes
Modified src/topology/algebra/order/basic.lean




## [2022-07-13 18:30:23](https://github.com/leanprover-community/mathlib/commit/44999a9)
feat(combinatorics/additive/behrend): Behrend's construction ([#14070](https://github.com/leanprover-community/mathlib/pull/14070))
Construct large Salem-Spencer sets in `ℕ` using Behrend's construction. The idea is to turn the Euclidean sphere into a discrete set of points in Euclidean space which we then squash onto `ℕ`.
#### Estimated changes
Modified src/algebra/group_power/order.lean
- \+ *lemma* zero_pow_le_one

Added src/combinatorics/additive/behrend.lean
- \+ *lemma* behrend.add_salem_spencer_image_sphere
- \+ *lemma* behrend.add_salem_spencer_sphere
- \+ *def* behrend.box
- \+ *lemma* behrend.box_zero
- \+ *lemma* behrend.card_box
- \+ *lemma* behrend.card_sphere_le_roth_number_nat
- \+ *def* behrend.map
- \+ *lemma* behrend.map_eq_iff
- \+ *lemma* behrend.map_inj_on
- \+ *lemma* behrend.map_le_of_mem_box
- \+ *lemma* behrend.map_mod
- \+ *lemma* behrend.map_monotone
- \+ *lemma* behrend.map_succ'
- \+ *lemma* behrend.map_succ
- \+ *lemma* behrend.map_zero
- \+ *lemma* behrend.mem_box
- \+ *lemma* behrend.norm_of_mem_sphere
- \+ *def* behrend.sphere
- \+ *lemma* behrend.sphere_subset_box
- \+ *lemma* behrend.sphere_subset_preimage_metric_sphere
- \+ *lemma* behrend.sphere_zero_right
- \+ *lemma* behrend.sphere_zero_subset
- \+ *lemma* behrend.sum_eq
- \+ *lemma* behrend.sum_lt
- \+ *lemma* behrend.sum_sq_le_of_mem_box

Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.pi_finset_empty
- \+ *lemma* fintype.pi_finset_singleton
- \+ *lemma* fintype.pi_finset_subsingleton



## [2022-07-13 16:39:58](https://github.com/leanprover-community/mathlib/commit/2084baf)
feat(set_theory/ordinal/basic): mark `type_fintype` as `simp` ([#15194](https://github.com/leanprover-community/mathlib/pull/15194))
This PR does the following:
- move `type_fintype` along with some other lemmas from `set_theory/ordinal/arithmetic.lean` to `set_theory/ordinal/basic.lean`.
- tag `type_fintype` as `simp`.
- untag various lemmas as `simp`, since they can now be proved by it.
#### Estimated changes
Modified src/set_theory/ordinal/arithmetic.lean
- \- *theorem* ordinal.card_eq_nat
- \- *theorem* ordinal.card_le_nat
- \- *theorem* ordinal.card_lt_nat
- \- *theorem* ordinal.nat_le_card
- \- *theorem* ordinal.nat_lt_card
- \- *theorem* ordinal.type_fin
- \- *theorem* ordinal.type_fintype

Modified src/set_theory/ordinal/basic.lean
- \+ *theorem* ordinal.card_eq_nat
- \+ *theorem* ordinal.card_le_nat
- \+ *theorem* ordinal.card_lt_nat
- \+ *theorem* ordinal.nat_le_card
- \+ *theorem* ordinal.nat_lt_card
- \+/\- *theorem* ordinal.type_eq_one_of_unique
- \+/\- *theorem* ordinal.type_eq_zero_of_empty
- \+ *theorem* ordinal.type_fin
- \+ *theorem* ordinal.type_fintype
- \+/\- *theorem* ordinal.type_pempty
- \+/\- *theorem* ordinal.type_punit
- \+/\- *theorem* ordinal.type_unit



## [2022-07-13 16:39:57](https://github.com/leanprover-community/mathlib/commit/93e164e)
refactor(field_theory/intermediate_field): introduce `restrict_scalars` which replaces `lift2` ([#15191](https://github.com/leanprover-community/mathlib/pull/15191))
This brings the API in line with `submodule` and `subalgebra` by removing `intermediate_field.lift2` and `intermediate_field.has_lift2`, and replacing them with `intermediate_field.restrict_scalars`. This definition is strictly more general than the previous `intermediate_field.lift2` definition was. A few downstream lemma statements have been generalized in the same way.
The handful of API lemmas for `restrict_scalars` that this adds were already missing for `lift2`.
`intermediate_field.lift2_alg_equiv` has been removed since we didn't appear to have anything similar for `subalgebra` or `submodule`, but it's possible I missed it. At any rate, it's only needed in one proof, and we can just use `show` or `refl` instead.
Note that `(↑x : intermediate_field F E)` is not actually a shorter spelling than `x.restrict_scalars F`, especially when `E` is more than a single character.
Finally this renames `lift1` to `lift` now that no ambiguity remains.
#### Estimated changes
Modified src/algebra/algebra/tower.lean


Modified src/field_theory/adjoin.lean
- \+/\- *lemma* intermediate_field.adjoin_adjoin_left
- \+/\- *lemma* intermediate_field.adjoin_simple_adjoin_simple
- \+/\- *lemma* intermediate_field.adjoin_simple_comm
- \- *lemma* intermediate_field.coe_bot_eq_self
- \- *lemma* intermediate_field.coe_top_eq_top
- \+ *lemma* intermediate_field.restrict_scalars_bot_eq_self
- \+ *lemma* intermediate_field.restrict_scalars_top

Modified src/field_theory/galois.lean
- \+/\- *lemma* is_galois.of_separable_splitting_field_aux

Modified src/field_theory/intermediate_field.lean
- \+ *lemma* intermediate_field.coe_restrict_scalars
- \- *def* intermediate_field.lift1
- \- *def* intermediate_field.lift2
- \- *def* intermediate_field.lift2_alg_equiv
- \- *lemma* intermediate_field.lift2_algebra_map
- \+ *def* intermediate_field.lift
- \- *lemma* intermediate_field.mem_lift2
- \+ *lemma* intermediate_field.mem_restrict_scalars
- \+ *def* intermediate_field.restrict_scalars
- \+ *lemma* intermediate_field.restrict_scalars_injective
- \+ *lemma* intermediate_field.restrict_scalars_to_subalgebra
- \+ *lemma* intermediate_field.restrict_scalars_to_subfield

Modified src/field_theory/primitive_element.lean




## [2022-07-13 13:55:17](https://github.com/leanprover-community/mathlib/commit/ed5453c)
chore(*/enat): rename files ([#15245](https://github.com/leanprover-community/mathlib/pull/15245))
rename `**/enat.lean` to `**/part_enat.lean`.
#### Estimated changes
Modified archive/imo/imo2019_q4.lean


Modified src/algebra/big_operators/default.lean


Renamed src/algebra/big_operators/enat.lean to src/algebra/big_operators/part_enat.lean


Modified src/data/nat/lattice.lean


Renamed src/data/nat/enat.lean to src/data/nat/part_enat.lean


Modified src/set_theory/cardinal/basic.lean




## [2022-07-13 13:55:16](https://github.com/leanprover-community/mathlib/commit/f8488be)
fix(algebra/group/units): splitting out `mul_one_class` for group of units ([#14923](https://github.com/leanprover-community/mathlib/pull/14923))
Without this proposed change, the following example gives a `(deterministic) timeout`:
```lean
import algebra.ring.basic
example (R : Type*) [comm_ring R] (a b : Rˣ) : a * (b / a) = b :=
begin
  rw mul_div_cancel'_right,
  -- or: `simp`
end
```
#### Estimated changes
Modified src/algebra/group/units.lean


Added test/units.lean




## [2022-07-13 13:55:14](https://github.com/leanprover-community/mathlib/commit/632b031)
feat(algebra/order/complete_field): `conditionally_complete_linear_ordered_field`, aka the reals ([#3292](https://github.com/leanprover-community/mathlib/pull/3292))
Introduce a class `conditionally_complete_linear_ordered_field`, which axiomatises the real numbers. Show that there exist a unique ordered ring isomorphism from any two such.
Additionally, show there is a unique order ring hom from any archimedean linear ordered field to such a field, giving that the ordered ring homomorphism from the rationals to the reals is unique for instance.
#### Estimated changes
Modified src/algebra/group_power/order.lean
- \+ *lemma* lt_of_mul_self_lt_mul_self

Added src/algebra/order/complete_field.lean
- \+ *lemma* linear_ordered_field.coe_induced_order_ring_iso
- \+ *lemma* linear_ordered_field.coe_lt_induced_map_iff
- \+ *lemma* linear_ordered_field.coe_mem_cut_map_iff
- \+ *def* linear_ordered_field.cut_map
- \+ *lemma* linear_ordered_field.cut_map_add
- \+ *lemma* linear_ordered_field.cut_map_bdd_above
- \+ *lemma* linear_ordered_field.cut_map_coe
- \+ *lemma* linear_ordered_field.cut_map_mono
- \+ *lemma* linear_ordered_field.cut_map_nonempty
- \+ *lemma* linear_ordered_field.cut_map_self
- \+ *lemma* linear_ordered_field.exists_mem_cut_map_mul_self_of_lt_induced_map_mul_self
- \+ *def* linear_ordered_field.induced_add_hom
- \+ *def* linear_ordered_field.induced_map
- \+ *lemma* linear_ordered_field.induced_map_add
- \+ *lemma* linear_ordered_field.induced_map_induced_map
- \+ *lemma* linear_ordered_field.induced_map_inv_self
- \+ *lemma* linear_ordered_field.induced_map_mono
- \+ *lemma* linear_ordered_field.induced_map_nonneg
- \+ *lemma* linear_ordered_field.induced_map_one
- \+ *lemma* linear_ordered_field.induced_map_rat
- \+ *lemma* linear_ordered_field.induced_map_self
- \+ *lemma* linear_ordered_field.induced_map_zero
- \+ *def* linear_ordered_field.induced_order_ring_hom
- \+ *def* linear_ordered_field.induced_order_ring_iso
- \+ *lemma* linear_ordered_field.induced_order_ring_iso_self
- \+ *lemma* linear_ordered_field.induced_order_ring_iso_symm
- \+ *lemma* linear_ordered_field.le_induced_map_mul_self_of_mem_cut_map
- \+ *lemma* linear_ordered_field.lt_induced_map_iff
- \+ *lemma* linear_ordered_field.mem_cut_map_iff



## [2022-07-13 12:42:43](https://github.com/leanprover-community/mathlib/commit/1d048c5)
chore(analysis/inner_product_space): move definition of self-adjointness ([#15281](https://github.com/leanprover-community/mathlib/pull/15281))
The file `analysis/inner_product_space/basic` is way to large and since `is_self_adjoint` will be rephrased in terms of the adjoint, it should be in the `adjoint` file.
#### Estimated changes
Modified src/analysis/inner_product_space/adjoint.lean
- \+ *lemma* inner_product_space.is_self_adjoint.apply_clm
- \+ *def* inner_product_space.is_self_adjoint.clm
- \+ *lemma* inner_product_space.is_self_adjoint.clm_apply
- \+ *lemma* inner_product_space.is_self_adjoint.coe_re_apply_inner_self_apply
- \+ *lemma* inner_product_space.is_self_adjoint.conj_inner_sym
- \+ *lemma* inner_product_space.is_self_adjoint.continuous
- \+ *lemma* inner_product_space.is_self_adjoint.restrict_invariant
- \+ *def* inner_product_space.is_self_adjoint
- \+ *lemma* inner_product_space.is_self_adjoint_iff_bilin_form
- \+ *lemma* inner_product_space.is_self_adjoint_iff_inner_map_self_real

Modified src/analysis/inner_product_space/basic.lean
- \- *lemma* inner_product_space.is_self_adjoint.apply_clm
- \- *def* inner_product_space.is_self_adjoint.clm
- \- *lemma* inner_product_space.is_self_adjoint.clm_apply
- \- *lemma* inner_product_space.is_self_adjoint.coe_re_apply_inner_self_apply
- \- *lemma* inner_product_space.is_self_adjoint.conj_inner_sym
- \- *lemma* inner_product_space.is_self_adjoint.continuous
- \- *lemma* inner_product_space.is_self_adjoint.restrict_invariant
- \- *def* inner_product_space.is_self_adjoint
- \- *lemma* inner_product_space.is_self_adjoint_iff_bilin_form
- \- *lemma* inner_product_space.is_self_adjoint_iff_inner_map_self_real

Modified src/analysis/inner_product_space/rayleigh.lean




## [2022-07-13 12:42:42](https://github.com/leanprover-community/mathlib/commit/2dfa69c)
feat(ring_theory/rees_algebra): Define the Rees algebra of an ideal. ([#15089](https://github.com/leanprover-community/mathlib/pull/15089))
#### Estimated changes
Added src/ring_theory/rees_algebra.lean
- \+ *lemma* adjoin_monomial_eq_rees_algebra
- \+ *lemma* mem_rees_algebra_iff
- \+ *lemma* mem_rees_algebra_iff_support
- \+ *lemma* monomial_mem_adjoin_monomial
- \+ *lemma* rees_algebra.fg
- \+ *lemma* rees_algebra.monomial_mem
- \+ *def* rees_algebra



## [2022-07-13 12:42:41](https://github.com/leanprover-community/mathlib/commit/8d7f001)
feat(measure_theory/pmf): lawful monad instance for probability mass function monad ([#15066](https://github.com/leanprover-community/mathlib/pull/15066))
Provide `is_lawful_functor` and `is_lawful_monad` instances for `pmf`. Also switch the `seq` and `map` operations to the ones coming from the `monad` instance.
#### Estimated changes
Modified src/measure_theory/probability_mass_function/basic.lean


Modified src/measure_theory/probability_mass_function/constructions.lean
- \+ *lemma* pmf.monad_map_eq_map
- \+ *lemma* pmf.monad_seq_eq_seq

Modified src/measure_theory/probability_mass_function/monad.lean
- \+/\- *lemma* pmf.pure_bind



## [2022-07-13 09:50:47](https://github.com/leanprover-community/mathlib/commit/83092fb)
feat(data/matrix/notation): add `!![1, 2; 3, 4]` notation ([#14991](https://github.com/leanprover-community/mathlib/pull/14991))
This adds `!![1, 2; 3, 4]` as a matlab-like shorthand for `matrix.of ![![1, 2], ![3, 4]]`. This has special support for empty arrays, where `!![,,,]` is a matrix with 0 rows and 3 columns, and `![;;;]` is a matrix with 3 rows and zero columns.
#### Estimated changes
Modified src/data/fin/vec_notation.lean


Modified src/data/matrix/notation.lean
- \+/\- *lemma* matrix.one_fin_three
- \+/\- *lemma* matrix.one_fin_two

Modified src/tactic/core.lean


Modified src/tactic/reserved_notation.lean


Modified test/matrix.lean




## [2022-07-13 09:50:45](https://github.com/leanprover-community/mathlib/commit/01a1824)
feat(data/polynomial/unit_trinomial): An irreducibility criterion for unit trinomials ([#14914](https://github.com/leanprover-community/mathlib/pull/14914))
This PR adds an irreducibility criterion for unit trinomials. This is building up to irreducibility of $x^n-x-1$.
#### Estimated changes
Added src/data/polynomial/unit_trinomial.lean
- \+ *lemma* polynomial.is_unit_trinomial.card_support_eq_three
- \+ *lemma* polynomial.is_unit_trinomial.coeff_is_unit
- \+ *lemma* polynomial.is_unit_trinomial.irreducible_aux1
- \+ *lemma* polynomial.is_unit_trinomial.irreducible_aux2
- \+ *lemma* polynomial.is_unit_trinomial.irreducible_aux3
- \+ *lemma* polynomial.is_unit_trinomial.irreducible_of_coprime
- \+ *lemma* polynomial.is_unit_trinomial.irreducible_of_is_coprime
- \+ *lemma* polynomial.is_unit_trinomial.leading_coeff_is_unit
- \+ *lemma* polynomial.is_unit_trinomial.ne_zero
- \+ *lemma* polynomial.is_unit_trinomial.not_is_unit
- \+ *lemma* polynomial.is_unit_trinomial.trailing_coeff_is_unit
- \+ *def* polynomial.is_unit_trinomial
- \+ *lemma* polynomial.is_unit_trinomial_iff''
- \+ *lemma* polynomial.is_unit_trinomial_iff'
- \+ *lemma* polynomial.is_unit_trinomial_iff
- \+ *lemma* polynomial.trinomial_def
- \+ *lemma* polynomial.trinomial_leading_coeff'
- \+ *lemma* polynomial.trinomial_leading_coeff
- \+ *lemma* polynomial.trinomial_middle_coeff
- \+ *lemma* polynomial.trinomial_mirror
- \+ *lemma* polynomial.trinomial_nat_degree
- \+ *lemma* polynomial.trinomial_nat_trailing_degree
- \+ *lemma* polynomial.trinomial_support
- \+ *lemma* polynomial.trinomial_trailing_coeff'
- \+ *lemma* polynomial.trinomial_trailing_coeff



## [2022-07-13 09:50:44](https://github.com/leanprover-community/mathlib/commit/581b694)
feat(data/polynomial/erase_lead): Characterization of polynomials of fixed support ([#14741](https://github.com/leanprover-community/mathlib/pull/14741))
This PR adds a lemma characterizing polynomials of fixed support.
#### Estimated changes
Modified src/data/polynomial/erase_lead.lean
- \+ *lemma* polynomial.card_support_eq'
- \+ *lemma* polynomial.card_support_eq



## [2022-07-13 09:09:29](https://github.com/leanprover-community/mathlib/commit/7340203)
feat(information_theory/hamming): add Hamming distance and norm ([#14739](https://github.com/leanprover-community/mathlib/pull/14739))
Add the Hamming distance, Hamming norm, and a `hamming` type synonym equipped with a normed group instance using the Hamming norm.
#### Estimated changes
Added src/information_theory/hamming.lean
- \+ *lemma* eq_of_hamming_dist_eq_zero
- \+ *lemma* hamming.dist_eq_hamming_dist
- \+ *lemma* hamming.nndist_eq_hamming_dist
- \+ *lemma* hamming.nnnorm_eq_hamming_norm
- \+ *lemma* hamming.norm_eq_hamming_norm
- \+ *def* hamming.of_hamming
- \+ *lemma* hamming.of_hamming_add
- \+ *lemma* hamming.of_hamming_inj
- \+ *lemma* hamming.of_hamming_neg
- \+ *lemma* hamming.of_hamming_smul
- \+ *lemma* hamming.of_hamming_sub
- \+ *lemma* hamming.of_hamming_symm_eq
- \+ *lemma* hamming.of_hamming_to_hamming
- \+ *lemma* hamming.of_hamming_zero
- \+ *def* hamming.to_hamming
- \+ *lemma* hamming.to_hamming_add
- \+ *lemma* hamming.to_hamming_inj
- \+ *lemma* hamming.to_hamming_neg
- \+ *lemma* hamming.to_hamming_of_hamming
- \+ *lemma* hamming.to_hamming_smul
- \+ *lemma* hamming.to_hamming_sub
- \+ *lemma* hamming.to_hamming_symm_eq
- \+ *lemma* hamming.to_hamming_zero
- \+ *def* hamming
- \+ *def* hamming_dist
- \+ *lemma* hamming_dist_comm
- \+ *lemma* hamming_dist_comp
- \+ *lemma* hamming_dist_comp_le_hamming_dist
- \+ *lemma* hamming_dist_eq_hamming_norm
- \+ *lemma* hamming_dist_eq_zero
- \+ *lemma* hamming_dist_le_card_fintype
- \+ *lemma* hamming_dist_lt_one
- \+ *lemma* hamming_dist_ne_zero
- \+ *lemma* hamming_dist_nonneg
- \+ *lemma* hamming_dist_pos
- \+ *lemma* hamming_dist_self
- \+ *lemma* hamming_dist_smul
- \+ *lemma* hamming_dist_smul_le_hamming_dist
- \+ *lemma* hamming_dist_triangle
- \+ *lemma* hamming_dist_triangle_left
- \+ *lemma* hamming_dist_triangle_right
- \+ *lemma* hamming_dist_zero_left
- \+ *lemma* hamming_dist_zero_right
- \+ *def* hamming_norm
- \+ *lemma* hamming_norm_comp
- \+ *lemma* hamming_norm_comp_le_hamming_norm
- \+ *lemma* hamming_norm_eq_zero
- \+ *lemma* hamming_norm_le_card_fintype
- \+ *lemma* hamming_norm_lt_one
- \+ *lemma* hamming_norm_ne_zero_iff
- \+ *lemma* hamming_norm_nonneg
- \+ *lemma* hamming_norm_pos_iff
- \+ *lemma* hamming_norm_smul
- \+ *lemma* hamming_norm_smul_le_hamming_norm
- \+ *lemma* hamming_norm_zero
- \+ *lemma* hamming_zero_eq_dist
- \+ *theorem* swap_hamming_dist



## [2022-07-13 06:13:44](https://github.com/leanprover-community/mathlib/commit/b06e32c)
chore(scripts): update nolints.txt ([#15293](https://github.com/leanprover-community/mathlib/pull/15293))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-07-13 06:13:43](https://github.com/leanprover-community/mathlib/commit/5cb17dd)
refactor(logic/is_empty): tag `is_empty.forall_iff` and `is_empty.exists_iff` as `simp` ([#14660](https://github.com/leanprover-community/mathlib/pull/14660))
We tag the lemmas `forall_iff` and `exists_iff` on empty types as `simp`. We remove `forall_pempty`, `exists_pempty`, `forall_false_left`, and `exists_false_left` due to being redundant.
#### Estimated changes
Modified src/algebra/associated.lean


Modified src/analysis/locally_convex/basic.lean


Modified src/data/list/cycle.lean


Modified src/data/nat/nth.lean


Modified src/data/polynomial/laurent.lean


Modified src/data/rbtree/basic.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/logic/basic.lean
- \+/\- *lemma* dite_eq_iff
- \+/\- *lemma* dite_eq_left_iff
- \+/\- *lemma* dite_eq_right_iff
- \- *lemma* exists_false_left
- \- *theorem* exists_pempty
- \- *lemma* forall_false_left
- \- *theorem* forall_pempty

Modified src/logic/is_empty.lean
- \+/\- *lemma* is_empty.exists_iff
- \+/\- *lemma* is_empty.forall_iff

Modified src/measure_theory/covering/besicovitch.lean


Modified src/measure_theory/function/strongly_measurable.lean


Modified src/measure_theory/integral/set_to_l1.lean


Modified src/order/filter/basic.lean


Modified src/order/partition/finpartition.lean


Modified src/order/well_founded_set.lean


Modified src/probability/hitting_time.lean




## [2022-07-13 02:40:33](https://github.com/leanprover-community/mathlib/commit/ea13c1c)
refactor(topology/subset_properties): reformulate `is_clopen_b{Union,Inter}` in terms of `set.finite` ([#15272](https://github.com/leanprover-community/mathlib/pull/15272))
This way it mirrors `is_open_bInter`/`is_closed_bUnion`. Also add `is_clopen.prod`.
#### Estimated changes
Modified src/topology/category/Profinite/cofiltered_limit.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean
- \+ *lemma* is_clopen.prod
- \+/\- *lemma* is_clopen_bInter
- \+ *lemma* is_clopen_bInter_finset
- \+/\- *lemma* is_clopen_bUnion
- \+ *lemma* is_clopen_bUnion_finset



## [2022-07-13 02:40:32](https://github.com/leanprover-community/mathlib/commit/2a32596)
feat(data/finsupp/basic): graph of a finitely supported function ([#15197](https://github.com/leanprover-community/mathlib/pull/15197))
We define the graph of a finitely supported function, i.e. the finset of input/output pairs, and prove basic results.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.apply_eq_of_mem_graph
- \+ *def* finsupp.graph
- \+ *lemma* finsupp.graph_eq_empty
- \+ *lemma* finsupp.graph_inj
- \+ *lemma* finsupp.graph_injective
- \+ *lemma* finsupp.graph_zero
- \+ *lemma* finsupp.image_fst_graph
- \+ *lemma* finsupp.mem_graph_iff
- \+ *lemma* finsupp.mk_mem_graph
- \+ *lemma* finsupp.mk_mem_graph_iff
- \+ *lemma* finsupp.not_mem_graph_snd_zero



## [2022-07-13 02:40:31](https://github.com/leanprover-community/mathlib/commit/c6014bd)
feat(algebra/parity): more general odd.pos ([#15186](https://github.com/leanprover-community/mathlib/pull/15186))
The old version of this lemma (added in [#13040](https://github.com/leanprover-community/mathlib/pull/13040)) was only for ℕ and didn't allow dot notation. We remove this and add a version for `canonically_ordered_comm_semiring`s, and if the definition of `odd` changes, this will also work for `canononically_ordered_add_monoid`s.
#### Estimated changes
Modified archive/imo/imo1998_q2.lean


Modified src/algebra/parity.lean
- \+ *lemma* odd.pos

Modified src/data/nat/parity.lean
- \- *lemma* nat.pos_of_odd



## [2022-07-13 00:00:41](https://github.com/leanprover-community/mathlib/commit/ede73b2)
refactor(topology/separation): rename `regular_space` to `t3_space` ([#15169](https://github.com/leanprover-community/mathlib/pull/15169))
I'm going to add a version of `regular_space` without `t0_space` and prove, e.g., that any uniform space is a regular space in this sense. To do this, I need to rename the existing `regular_space`.
#### Estimated changes
Modified src/analysis/complex/upper_half_plane/topology.lean


Modified src/analysis/locally_convex/balanced_core_hull.lean
- \+/\- *lemma* nhds_basis_closed_balanced

Modified src/analysis/locally_convex/bounded.lean


Modified src/topology/alexandroff.lean


Modified src/topology/algebra/group.lean
- \- *lemma* topological_group.regular_space
- \+ *lemma* topological_group.t3_space

Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* has_sum.prod_fiberwise
- \+/\- *lemma* has_sum.sigma
- \+/\- *lemma* has_sum.sigma_of_has_sum
- \+/\- *lemma* summable.sigma'
- \+/\- *lemma* tsum_comm'
- \+/\- *lemma* tsum_prod'
- \+/\- *lemma* tsum_sigma'

Modified src/topology/algebra/module/basic.lean


Modified src/topology/algebra/order/basic.lean


Modified src/topology/algebra/order/extend_from.lean


Modified src/topology/algebra/uniform_field.lean


Modified src/topology/algebra/valued_field.lean


Modified src/topology/algebra/with_zero_topology.lean


Modified src/topology/dense_embedding.lean
- \+/\- *lemma* dense_inducing.continuous_at_extend
- \+/\- *lemma* dense_inducing.continuous_extend

Modified src/topology/extend_from.lean
- \+/\- *lemma* continuous_extend_from
- \+/\- *lemma* continuous_on_extend_from

Modified src/topology/homeomorph.lean


Modified src/topology/metric_space/metrizable.lean
- \- *lemma* topological_space.metrizable_space_of_regular_second_countable
- \+ *lemma* topological_space.metrizable_space_of_t3_second_countable

Modified src/topology/separation.lean
- \+/\- *lemma* closed_nhds_basis
- \+/\- *lemma* disjoint_nested_nhds
- \+/\- *lemma* exists_compact_between
- \+/\- *lemma* exists_open_between_and_is_compact_closure
- \+/\- *lemma* nhds_is_closed
- \- *lemma* normal_space_of_regular_second_countable
- \+ *lemma* normal_space_of_t3_second_countable
- \+/\- *lemma* topological_space.is_topological_basis.exists_closure_subset
- \+/\- *lemma* topological_space.is_topological_basis.nhds_basis_closure

Modified src/topology/uniform_space/compact_separated.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/separation.lean




## [2022-07-13 00:00:40](https://github.com/leanprover-community/mathlib/commit/6c351a8)
refactor(data/matrix/basic): add matrix.of for type casting ([#14992](https://github.com/leanprover-community/mathlib/pull/14992))
Without this, it is easier to get confused between matrix and pi types, which have different multiplication operators.
With this in place, we can have a special matrix notation that actually produces terms of type `matrix`.
#### Estimated changes
Modified src/analysis/matrix.lean


Modified src/data/matrix/basic.lean
- \+/\- *def* matrix.map
- \+ *lemma* matrix.neg_of
- \+ *def* matrix.of
- \+ *lemma* matrix.of_add_of
- \+ *lemma* matrix.of_apply
- \+ *lemma* matrix.of_sub_of
- \+ *lemma* matrix.of_symm_apply
- \+ *lemma* matrix.of_zero
- \+ *lemma* matrix.smul_of

Modified src/data/matrix/block.lean


Modified src/data/matrix/notation.lean
- \+/\- *lemma* matrix.cons_mul
- \+/\- *lemma* matrix.cons_val'
- \+/\- *lemma* matrix.cons_vec_mul
- \+/\- *lemma* matrix.head_transpose
- \+/\- *lemma* matrix.head_val'
- \+/\- *lemma* matrix.smul_mat_cons
- \+/\- *lemma* matrix.tail_transpose
- \+/\- *lemma* matrix.tail_val'
- \+/\- *lemma* matrix.transpose_empty_cols
- \+/\- *lemma* matrix.transpose_empty_rows
- \+/\- *lemma* matrix.vec_mul_cons

Modified src/linear_algebra/matrix/basis.lean


Modified src/linear_algebra/matrix/bilinear_form.lean
- \+ *lemma* bilin_form.to_matrix_aux_apply

Modified src/linear_algebra/matrix/determinant.lean
- \- *lemma* matrix.det_fin_two_mk
- \+ *lemma* matrix.det_fin_two_of

Modified src/linear_algebra/matrix/to_lin.lean


Modified src/linear_algebra/matrix/transvection.lean


Modified src/linear_algebra/vandermonde.lean


Modified src/logic/equiv/basic.lean
- \+/\- *theorem* equiv.perm.coe_subsingleton

Modified src/ring_theory/matrix_algebra.lean


Modified src/ring_theory/trace.lean
- \+/\- *lemma* algebra.trace_matrix_def

Modified test/matrix.lean




## [2022-07-12 21:43:25](https://github.com/leanprover-community/mathlib/commit/834488e)
feat(topology/maps): more `iff` lemmas ([#15165](https://github.com/leanprover-community/mathlib/pull/15165))
* add `inducing_iff` and `inducing_iff_nhds`;
* add `embedding_iff`;
* add `open_embedding_iff_embedding_open` and `open_embedding_iff_continuous_injective_open`;
* add `open_embedding.is_open_map_iff`;
* reorder `open_embedding_iff_open_embedding_compose` and `open_embedding_of_open_embedding_compose`, golf.
#### Estimated changes
Modified src/topology/category/Top/basic.lean


Modified src/topology/maps.lean
- \+ *lemma* inducing_iff_nhds
- \+ *lemma* open_embedding.is_open_map_iff
- \+ *lemma* open_embedding.of_comp
- \+ *lemma* open_embedding.of_comp_iff
- \+ *lemma* open_embedding_iff_continuous_injective_open
- \+ *lemma* open_embedding_iff_embedding_open
- \- *lemma* open_embedding_iff_open_embedding_compose
- \- *lemma* open_embedding_of_open_embedding_compose



## [2022-07-12 21:43:24](https://github.com/leanprover-community/mathlib/commit/7bd4755)
feat(analysis/special_functions/pow): drop an assumption in `is_o_log_rpow_rpow_at_top` ([#15164](https://github.com/leanprover-community/mathlib/pull/15164))
Drop an unneeded assumption in `is_o_log_rpow_rpow_at_top`, add a few variants.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* is_o_abs_log_rpow_rpow_nhds_zero
- \+ *lemma* is_o_log_rpow_nhds_zero
- \+/\- *lemma* is_o_log_rpow_rpow_at_top
- \+ *lemma* tendsto_log_div_rpow_nhds_zero
- \+ *lemma* tensdto_log_mul_rpow_nhds_zero



## [2022-07-12 21:43:23](https://github.com/leanprover-community/mathlib/commit/3543262)
feat(ring_theory/bezout): Define Bézout rings. ([#15091](https://github.com/leanprover-community/mathlib/pull/15091))
#### Estimated changes
Added src/ring_theory/bezout.lean
- \+ *lemma* function.surjective.is_bezout
- \+ *lemma* is_bezout.dvd_gcd
- \+ *def* is_bezout.gcd
- \+ *lemma* is_bezout.gcd_dvd_left
- \+ *lemma* is_bezout.gcd_dvd_right
- \+ *lemma* is_bezout.gcd_eq_sum
- \+ *lemma* is_bezout.iff_span_pair_is_principal
- \+ *lemma* is_bezout.span_gcd
- \+ *lemma* is_bezout.tfae
- \+ *def* is_bezout.to_gcd_domain

Modified src/ring_theory/noetherian.lean
- \+ *lemma* is_noetherian_iff_fg_well_founded
- \+ *lemma* submodule.fg_induction



## [2022-07-12 21:43:22](https://github.com/leanprover-community/mathlib/commit/ece3044)
feat(algebra/ring/{pi, prod, opposite}): add basic defs for non_unital_ring_hom ([#13958](https://github.com/leanprover-community/mathlib/pull/13958))
The defs added mimic the corresponding ones for `ring_hom`, wherever possible.
- [x] depends on: [#13956](https://github.com/leanprover-community/mathlib/pull/13956)
#### Estimated changes
Modified src/algebra/ring/opposite.lean
- \+ *def* non_unital_ring_hom.from_opposite
- \+ *def* non_unital_ring_hom.op
- \+ *def* non_unital_ring_hom.to_opposite
- \+ *def* non_unital_ring_hom.unop

Modified src/algebra/ring/pi.lean
- \+ *def* pi.const_non_unital_ring_hom
- \+ *def* pi.eval_non_unital_ring_hom
- \+ *lemma* pi.non_unital_ring_hom_injective

Modified src/algebra/ring/prod.lean
- \+ *lemma* non_unital_ring_hom.coe_fst
- \+ *lemma* non_unital_ring_hom.coe_prod_map
- \+ *lemma* non_unital_ring_hom.coe_snd
- \+ *def* non_unital_ring_hom.fst
- \+ *lemma* non_unital_ring_hom.fst_comp_prod
- \+ *lemma* non_unital_ring_hom.prod_apply
- \+ *lemma* non_unital_ring_hom.prod_comp_prod_map
- \+ *def* non_unital_ring_hom.prod_map
- \+ *lemma* non_unital_ring_hom.prod_map_def
- \+ *lemma* non_unital_ring_hom.prod_unique
- \+ *def* non_unital_ring_hom.snd
- \+ *lemma* non_unital_ring_hom.snd_comp_prod



## [2022-07-12 19:18:58](https://github.com/leanprover-community/mathlib/commit/55db072)
chore(data/set/finite): golf some proofs ([#15273](https://github.com/leanprover-community/mathlib/pull/15273))
#### Estimated changes
Modified src/data/set/finite.lean


Modified src/data/set/lattice.lean
- \+ *theorem* set.Union_eq_range_psigma



## [2022-07-12 19:18:57](https://github.com/leanprover-community/mathlib/commit/7251bbf)
feat(analysis/special_functions/trigonometric/angle): equality of twice angles ([#14988](https://github.com/leanprover-community/mathlib/pull/14988))
Add lemmas about equality of twice `real.angle` values (i.e. equality
as angles modulo π).
#### Estimated changes
Added src/algebra/char_zero/quotient.lean
- \+ *lemma* add_subgroup.nsmul_mem_zmultiples_iff_exists_sub_div
- \+ *lemma* add_subgroup.zsmul_mem_zmultiples_iff_exists_sub_div
- \+ *lemma* quotient_add_group.zmultiples_nsmul_eq_nsmul_iff
- \+ *lemma* quotient_add_group.zmultiples_zsmul_eq_zsmul_iff

Modified src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* real.angle.nsmul_eq_iff
- \+ *lemma* real.angle.two_nsmul_eq_iff
- \+ *lemma* real.angle.two_nsmul_eq_zero_iff
- \+ *lemma* real.angle.two_zsmul_eq_iff
- \+ *lemma* real.angle.two_zsmul_eq_zero_iff
- \+ *lemma* real.angle.zsmul_eq_iff



## [2022-07-12 16:39:10](https://github.com/leanprover-community/mathlib/commit/89a80e6)
feat(data/nat/parity): `nat.bit1_div_bit0` ([#15268](https://github.com/leanprover-community/mathlib/pull/15268))
This PR adds `nat.bit1_div_bit0` and related lemmas. This came up when working with the power series of sin.
#### Estimated changes
Modified src/data/nat/parity.lean
- \+ *lemma* nat.bit0_div_bit0
- \+ *lemma* nat.bit0_div_two
- \+ *lemma* nat.bit1_div_bit0
- \+ *lemma* nat.bit1_div_two



## [2022-07-12 16:39:09](https://github.com/leanprover-community/mathlib/commit/9c40093)
chore(*): improve some definitional equalities ([#15083](https://github.com/leanprover-community/mathlib/pull/15083))
* add `set.mem_diagonal_iff`, move `simp` from `set.mem_diagonal`;
* add `@[simp]` to `set.prod_subset_compl_diagonal_iff_disjoint`;
* redefine `sum.map` in terms of `sum.elim`, add `sum.map_inl` and `sum.map_inr`;
* redefine `sum.swap` in terms of `sum.elim`, add `sum.swap_inl` and `sum.swap_inr`;
* use `lift_rel_swap_iff` to prove  `swap_le_swap` and `swap_lt_swap`;
* redefine `equiv.sum_prod_distrib` and `equiv.sigma_sum_distrib` in terms of `sum.elim` and `sum.map`;
* add `filter.compl_diagonal_mem_prod`;
* rename `continuous_sum_rec` to `continuous.sum_elim`, use `sum.elim` in the statement;
* add `continuous.sum_map`;
* golf `homeomorph.sum_congr` and `homeomorph.sum_prod_distrib`.
#### Estimated changes
Modified src/data/set/prod.lean
- \+/\- *lemma* set.mem_diagonal
- \+ *lemma* set.mem_diagonal_iff
- \+/\- *lemma* set.prod_subset_compl_diagonal_iff_disjoint

Modified src/data/sum/basic.lean
- \+/\- *def* sum.swap
- \+ *lemma* sum.swap_inl
- \+ *lemma* sum.swap_inr

Modified src/data/sum/order.lean


Modified src/logic/equiv/basic.lean
- \+ *theorem* equiv.prod_sum_distrib_symm_apply_left
- \+ *theorem* equiv.prod_sum_distrib_symm_apply_right
- \+ *theorem* equiv.sum_prod_distrib_symm_apply_left
- \+ *theorem* equiv.sum_prod_distrib_symm_apply_right

Modified src/order/filter/bases.lean
- \+ *lemma* filter.compl_diagonal_mem_prod

Modified src/topology/constructions.lean
- \+ *lemma* continuous.sum_elim
- \+ *lemma* continuous.sum_map
- \- *lemma* continuous_sum_rec

Modified src/topology/homeomorph.lean




## [2022-07-12 16:39:08](https://github.com/leanprover-community/mathlib/commit/eb091f8)
feat(data/nat/basic): add `strong_sub_recursion` and `pincer_recursion` ([#15061](https://github.com/leanprover-community/mathlib/pull/15061))
Adding two recursion principles for `P : ℕ → ℕ → Sort*`
`strong_sub_recursion`: if for all `a b : ℕ` we can extend `P` from the rectangle strictly below `(a,b)` to `P a b`, then we have `P n m` for all `n m : ℕ`.
`pincer_recursion`: if we have `P i 0` and `P 0 i` for all `i : ℕ`, and for any `x y : ℕ` we can extend `P` from `(x,y+1)` and `(x+1,y)` to `(x+1,y+1)` then we have `P n m` for all `n m : ℕ`.
`strong_sub_recursion` is adapted by @vihdzp from @CBirkbeck 's [#14828](https://github.com/leanprover-community/mathlib/pull/14828)
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *def* nat.pincer_recursion
- \+ *def* nat.strong_sub_recursion



## [2022-07-12 14:37:15](https://github.com/leanprover-community/mathlib/commit/13f04ec)
feat(set_theory/game/pgame): strengthen `lf_or_equiv_of_le` to `lt_or_equiv_of_le` ([#15255](https://github.com/leanprover-community/mathlib/pull/15255))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \- *theorem* pgame.lf_or_equiv_of_le
- \+ *theorem* pgame.lt_or_equiv_of_le



## [2022-07-12 14:37:14](https://github.com/leanprover-community/mathlib/commit/0d659de)
feat(algebra/module/torsion): `R/I`-module structure on `M/IM`. ([#15092](https://github.com/leanprover-community/mathlib/pull/15092))
#### Estimated changes
Modified src/algebra/module/torsion.lean




## [2022-07-12 14:37:13](https://github.com/leanprover-community/mathlib/commit/fef5124)
feat(order/order_iso_nat): generalize `well_founded.monotone_chain_condition` to preorders ([#15073](https://github.com/leanprover-community/mathlib/pull/15073))
We also clean up the spacing throughout the file.
#### Estimated changes
Modified src/order/order_iso_nat.lean
- \+/\- *theorem* exists_increasing_or_nonincreasing_subseq'
- \+/\- *theorem* exists_increasing_or_nonincreasing_subseq
- \+/\- *theorem* nat.exists_subseq_of_forall_mem_union
- \+/\- *lemma* nat.subtype.order_iso_of_nat_apply
- \+/\- *def* rel_embedding.nat_gt
- \+/\- *lemma* rel_embedding.nat_lt_apply
- \+ *lemma* well_founded.monotone_chain_condition'
- \+/\- *lemma* well_founded.monotone_chain_condition
- \+/\- *lemma* well_founded.supr_eq_monotonic_sequence_limit

Modified src/order/well_founded_set.lean


Modified src/ring_theory/artinian.lean




## [2022-07-12 13:45:52](https://github.com/leanprover-community/mathlib/commit/119e166)
feat(representation_theory/character): formula for the dimension of the invariants in terms of the character ([#15084](https://github.com/leanprover-community/mathlib/pull/15084))
#### Estimated changes
Modified src/representation_theory/character.lean
- \+ *theorem* fdRep.average_char_eq_finrank_invariants

Modified src/representation_theory/invariants.lean
- \- *lemma* group_algebra.average_def



## [2022-07-12 12:46:38](https://github.com/leanprover-community/mathlib/commit/aadba9b)
feat(order/well_founded_set): any relation is well-founded on `Ø` ([#15266](https://github.com/leanprover-community/mathlib/pull/15266))
#### Estimated changes
Modified src/order/well_founded_set.lean
- \+/\- *theorem* set.is_pwo_empty
- \+ *lemma* set.is_wf_empty
- \+ *theorem* set.partially_well_ordered_on_empty
- \+ *lemma* set.well_founded_on_empty



## [2022-07-12 12:46:37](https://github.com/leanprover-community/mathlib/commit/6c5e9fe)
feat(set_theory/game/pgame): `is_option (-x) (-y) ↔ is_option x y` ([#15256](https://github.com/leanprover-community/mathlib/pull/15256))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.is_option_neg
- \+ *theorem* pgame.is_option_neg_neg



## [2022-07-12 12:46:36](https://github.com/leanprover-community/mathlib/commit/087bc1f)
feat(set_theory/game/pgame): add `equiv.comm` ([#15254](https://github.com/leanprover-community/mathlib/pull/15254))
#### Estimated changes
Modified src/set_theory/game/pgame.lean




## [2022-07-12 12:46:35](https://github.com/leanprover-community/mathlib/commit/2bca4d6)
chore(set_theory/ordinal/cantor_normal_form): mark `CNF` as `pp_nodot` ([#15228](https://github.com/leanprover-community/mathlib/pull/15228))
`b.CNF o` doesn't make much sense, since `b` is the base argument rather than the main argument.
The existing lemmas all use the `CNF b o` spelling anyway.
#### Estimated changes
Modified src/set_theory/ordinal/cantor_normal_form.lean
- \+/\- *def* ordinal.CNF



## [2022-07-12 12:05:18](https://github.com/leanprover-community/mathlib/commit/8284c00)
feat(algebra/order/monoid_lemmas_zero_lt): add missing lemmas ([#14770](https://github.com/leanprover-community/mathlib/pull/14770))
#### Estimated changes
Modified src/algebra/order/monoid_lemmas_zero_lt.lean
- \+ *lemma* zero_lt.lt_mul_of_one_lt_left
- \+ *lemma* zero_lt.lt_mul_of_one_lt_right
- \+ *lemma* zero_lt.mul_lt_of_lt_one_left
- \+ *lemma* zero_lt.mul_lt_of_lt_one_right



## [2022-07-12 09:40:23](https://github.com/leanprover-community/mathlib/commit/30daa3c)
chore(logic/is_empty): add lemmas for subtype, sigma, and psigma ([#15134](https://github.com/leanprover-community/mathlib/pull/15134))
This reorders the nonempty lemmas to put `sigma` next to `psigma`. The resulting `is_empty` and `nonempty` lemmas are now in the same order.
#### Estimated changes
Modified src/logic/is_empty.lean
- \+ *lemma* is_empty_Prop
- \+ *lemma* is_empty_plift
- \+ *lemma* is_empty_psigma
- \+ *lemma* is_empty_sigma
- \+ *lemma* is_empty_subtype
- \+ *lemma* is_empty_ulift

Modified src/logic/nonempty.lean




## [2022-07-12 08:44:51](https://github.com/leanprover-community/mathlib/commit/a8fdd99)
feat(probability/moments): Chernoff bound on the upper/lower tail of a real random variable ([#15129](https://github.com/leanprover-community/mathlib/pull/15129))
For `t` nonnegative such that the cgf exists, `ℙ(ε ≤ X) ≤ exp(-t*ε + cgf X ℙ t)`. We prove a similar result for the lower tail, as well as two corresponding versions using mgf instead of cgf.
#### Estimated changes
Modified src/analysis/special_functions/log/basic.lean
- \+ *lemma* real.le_exp_log

Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_theory.mul_meas_ge_le_integral_of_nonneg

Modified src/probability/moments.lean
- \+/\- *def* probability_theory.cgf
- \+ *lemma* probability_theory.cgf_neg
- \+/\- *lemma* probability_theory.cgf_undef
- \+/\- *lemma* probability_theory.cgf_zero'
- \+/\- *lemma* probability_theory.cgf_zero_fun
- \+ *lemma* probability_theory.measure_ge_le_exp_cgf
- \+ *lemma* probability_theory.measure_ge_le_exp_mul_mgf
- \+ *lemma* probability_theory.measure_le_le_exp_cgf
- \+ *lemma* probability_theory.measure_le_le_exp_mul_mgf
- \+/\- *def* probability_theory.mgf
- \+/\- *lemma* probability_theory.mgf_const'
- \+/\- *lemma* probability_theory.mgf_const
- \+ *lemma* probability_theory.mgf_neg
- \+/\- *lemma* probability_theory.mgf_pos'
- \+/\- *lemma* probability_theory.mgf_pos
- \+/\- *lemma* probability_theory.mgf_undef



## [2022-07-12 07:50:38](https://github.com/leanprover-community/mathlib/commit/0039a19)
feat(probability/independence): two tuples indexed by disjoint subsets of an independent family of r.v. are independent ([#15131](https://github.com/leanprover-community/mathlib/pull/15131))
If `f` is a family of independent random variables and `S,T` are two disjoint finsets, then we have `indep_fun (λ a (i : S), f i a) (λ a (i : T), f i a) μ`.
Also golf `indep_fun_iff_measure_inter_preimage_eq_mul` and add its `Indep` version: `Indep_fun_iff_measure_inter_preimage_eq_mul`.
#### Estimated changes
Modified src/measure_theory/pi_system.lean
- \+ *lemma* is_pi_system.comap

Modified src/probability/independence.lean
- \+ *lemma* probability_theory.Indep_fun.indep_fun
- \+ *lemma* probability_theory.Indep_fun.indep_fun_finset
- \+ *lemma* probability_theory.Indep_fun_iff_measure_inter_preimage_eq_mul



## [2022-07-12 03:56:12](https://github.com/leanprover-community/mathlib/commit/d6d3d61)
feat(tactic/lint): add a linter for `[fintype _]` assumptions ([#15202](https://github.com/leanprover-community/mathlib/pull/15202))
Adopted from the `decidable` linter.
#### Estimated changes
Modified scripts/nolints.txt


Modified src/tactic/lint/type_classes.lean




## [2022-07-12 03:56:11](https://github.com/leanprover-community/mathlib/commit/423a8b9)
feat(tactic/polyrith): a tactic using Sage to solve polynomial equalities with hypotheses ([#14878](https://github.com/leanprover-community/mathlib/pull/14878))
Created a new tactic called polyrith that solves polynomial equalities through polynomial arithmetic on the hypotheses/proof terms. Similar to how linarith solves linear equalities through linear arithmetic on the hypotheses/proof terms.
#### Estimated changes
Modified .github/workflows/bors.yml


Modified .github/workflows/build.yml


Modified .github/workflows/build.yml.in


Modified .github/workflows/build_fork.yml


Modified docs/references.bib


Added scripts/polyrith_sage.py


Added scripts/polyrith_sage_helper.py


Modified src/data/buffer/parser/numeral.lean


Modified src/tactic/default.lean


Added src/tactic/polyrith.lean


Added test/polyrith.lean




## [2022-07-12 03:14:44](https://github.com/leanprover-community/mathlib/commit/1f3c2c0)
chore(set_theory/game/ordinal): minor golf ([#15253](https://github.com/leanprover-community/mathlib/pull/15253))
#### Estimated changes
Modified src/set_theory/game/ordinal.lean




## [2022-07-12 03:14:43](https://github.com/leanprover-community/mathlib/commit/623a658)
doc(set_theory/game/pgame): divide file into sections ([#15250](https://github.com/leanprover-community/mathlib/pull/15250))
#### Estimated changes
Modified src/set_theory/game/pgame.lean




## [2022-07-11 22:33:23](https://github.com/leanprover-community/mathlib/commit/52d4dae)
feat(representation_theory/monoid_algebra_basis): add some API for `k[G^n]` ([#14308](https://github.com/leanprover-community/mathlib/pull/14308))
#### Estimated changes
Modified src/algebra/big_operators/fin.lean
- \+ *def* fin.partial_prod
- \+ *lemma* fin.partial_prod_succ'
- \+ *lemma* fin.partial_prod_succ
- \+ *lemma* fin.partial_prod_zero
- \+/\- *lemma* list.prod_of_fn
- \+/\- *lemma* list.prod_take_of_fn

Modified src/representation_theory/basic.lean
- \+ *lemma* representation.of_mul_action_apply
- \+ *lemma* representation.of_mul_action_def

Added src/representation_theory/group_cohomology_resolution.lean
- \+ *def* group_cohomology.resolution.of_tensor
- \+ *def* group_cohomology.resolution.of_tensor_aux
- \+ *lemma* group_cohomology.resolution.of_tensor_aux_comm_of_mul_action
- \+ *lemma* group_cohomology.resolution.of_tensor_aux_single
- \+ *lemma* group_cohomology.resolution.of_tensor_single'
- \+ *lemma* group_cohomology.resolution.of_tensor_single
- \+ *def* group_cohomology.resolution.to_tensor
- \+ *def* group_cohomology.resolution.to_tensor_aux
- \+ *lemma* group_cohomology.resolution.to_tensor_aux_of_mul_action
- \+ *lemma* group_cohomology.resolution.to_tensor_aux_single
- \+ *lemma* group_cohomology.resolution.to_tensor_single



## [2022-07-11 16:51:25](https://github.com/leanprover-community/mathlib/commit/00dbc7b)
fix(.github/workflows): temporarily increase timeout ([#15251](https://github.com/leanprover-community/mathlib/pull/15251))
Quick hack to fix our olean files after https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.22saving.20olean.22.3F.
#### Estimated changes
Modified .github/workflows/bors.yml


Modified .github/workflows/build.yml


Modified .github/workflows/build.yml.in


Modified .github/workflows/build_fork.yml




## [2022-07-11 16:51:24](https://github.com/leanprover-community/mathlib/commit/201d2c6)
refactor(data/nat/enat): rename `enat` to `part_enat` ([#15235](https://github.com/leanprover-community/mathlib/pull/15235))
* find+replace `enat` with `part_enat`;
* reflow long lines
* add a sentence to the module docstring of `data.nat.enat`.
I'm going to define `enat := with_top nat` and use it as the default implementation of "nat with top".
#### Estimated changes
Modified archive/imo/imo2019_q4.lean


Modified src/algebra/big_operators/enat.lean


Modified src/algebra/order/sub.lean


Modified src/algebra/squarefree.lean


Modified src/data/nat/choose/factorization.lean


Modified src/data/nat/enat.lean
- \- *lemma* enat.add_eq_top_iff
- \- *lemma* enat.add_one_le_iff_lt
- \- *lemma* enat.add_one_le_of_lt
- \- *lemma* enat.add_top
- \- *lemma* enat.coe_add_get
- \- *lemma* enat.coe_coe_hom
- \- *lemma* enat.coe_get
- \- *def* enat.coe_hom
- \- *lemma* enat.coe_inj
- \- *lemma* enat.coe_le_coe
- \- *lemma* enat.coe_le_iff
- \- *lemma* enat.coe_lt_coe
- \- *lemma* enat.coe_lt_iff
- \- *lemma* enat.coe_lt_top
- \- *lemma* enat.coe_ne_top
- \- *lemma* enat.dom_coe
- \- *lemma* enat.dom_of_le_coe
- \- *lemma* enat.dom_of_le_of_dom
- \- *lemma* enat.dom_of_le_some
- \- *lemma* enat.dom_of_lt
- \- *lemma* enat.dom_some
- \- *lemma* enat.eq_top_iff_forall_le
- \- *lemma* enat.eq_top_iff_forall_lt
- \- *lemma* enat.eq_zero_iff
- \- *def* enat.find
- \- *lemma* enat.find_dom
- \- *lemma* enat.find_eq_top_iff
- \- *lemma* enat.find_get
- \- *lemma* enat.find_le
- \- *lemma* enat.get_add
- \- *lemma* enat.get_coe'
- \- *lemma* enat.get_coe
- \- *lemma* enat.get_eq_iff_eq_coe
- \- *lemma* enat.get_eq_iff_eq_some
- \- *lemma* enat.get_le_get
- \- *lemma* enat.get_one
- \- *lemma* enat.get_zero
- \- *lemma* enat.le_coe_iff
- \- *lemma* enat.le_def
- \- *lemma* enat.le_of_lt_add_one
- \- *lemma* enat.lt_add_one
- \- *lemma* enat.lt_add_one_iff_lt
- \- *lemma* enat.lt_coe_iff
- \- *lemma* enat.lt_def
- \- *lemma* enat.lt_find
- \- *lemma* enat.lt_find_iff
- \- *lemma* enat.lt_wf
- \- *lemma* enat.ne_top_iff
- \- *lemma* enat.ne_top_iff_dom
- \- *lemma* enat.ne_top_of_lt
- \- *lemma* enat.ne_zero_iff
- \- *lemma* enat.not_dom_iff_eq_top
- \- *lemma* enat.not_is_max_coe
- \- *lemma* enat.pos_iff_one_le
- \- *def* enat.some
- \- *lemma* enat.some_eq_coe
- \- *def* enat.to_with_top
- \- *lemma* enat.to_with_top_add
- \- *lemma* enat.to_with_top_coe'
- \- *lemma* enat.to_with_top_coe
- \- *lemma* enat.to_with_top_le
- \- *lemma* enat.to_with_top_lt
- \- *lemma* enat.to_with_top_some
- \- *lemma* enat.to_with_top_top'
- \- *lemma* enat.to_with_top_top
- \- *lemma* enat.to_with_top_zero'
- \- *lemma* enat.to_with_top_zero
- \- *lemma* enat.top_add
- \- *lemma* enat.top_eq_none
- \- *lemma* enat.with_top_equiv_coe
- \- *lemma* enat.with_top_equiv_le
- \- *lemma* enat.with_top_equiv_lt
- \- *lemma* enat.with_top_equiv_symm_coe
- \- *lemma* enat.with_top_equiv_symm_le
- \- *lemma* enat.with_top_equiv_symm_lt
- \- *lemma* enat.with_top_equiv_symm_top
- \- *lemma* enat.with_top_equiv_symm_zero
- \- *lemma* enat.with_top_equiv_top
- \- *lemma* enat.with_top_equiv_zero
- \- *def* enat
- \+ *lemma* part_enat.add_eq_top_iff
- \+ *lemma* part_enat.add_one_le_iff_lt
- \+ *lemma* part_enat.add_one_le_of_lt
- \+ *lemma* part_enat.add_top
- \+ *lemma* part_enat.coe_add_get
- \+ *lemma* part_enat.coe_coe_hom
- \+ *lemma* part_enat.coe_get
- \+ *def* part_enat.coe_hom
- \+ *lemma* part_enat.coe_inj
- \+ *lemma* part_enat.coe_le_coe
- \+ *lemma* part_enat.coe_le_iff
- \+ *lemma* part_enat.coe_lt_coe
- \+ *lemma* part_enat.coe_lt_iff
- \+ *lemma* part_enat.coe_lt_top
- \+ *lemma* part_enat.coe_ne_top
- \+ *lemma* part_enat.dom_coe
- \+ *lemma* part_enat.dom_of_le_coe
- \+ *lemma* part_enat.dom_of_le_of_dom
- \+ *lemma* part_enat.dom_of_le_some
- \+ *lemma* part_enat.dom_of_lt
- \+ *lemma* part_enat.dom_some
- \+ *lemma* part_enat.eq_top_iff_forall_le
- \+ *lemma* part_enat.eq_top_iff_forall_lt
- \+ *lemma* part_enat.eq_zero_iff
- \+ *def* part_enat.find
- \+ *lemma* part_enat.find_dom
- \+ *lemma* part_enat.find_eq_top_iff
- \+ *lemma* part_enat.find_get
- \+ *lemma* part_enat.find_le
- \+ *lemma* part_enat.get_add
- \+ *lemma* part_enat.get_coe'
- \+ *lemma* part_enat.get_coe
- \+ *lemma* part_enat.get_eq_iff_eq_coe
- \+ *lemma* part_enat.get_eq_iff_eq_some
- \+ *lemma* part_enat.get_le_get
- \+ *lemma* part_enat.get_one
- \+ *lemma* part_enat.get_zero
- \+ *lemma* part_enat.le_coe_iff
- \+ *lemma* part_enat.le_def
- \+ *lemma* part_enat.le_of_lt_add_one
- \+ *lemma* part_enat.lt_add_one
- \+ *lemma* part_enat.lt_add_one_iff_lt
- \+ *lemma* part_enat.lt_coe_iff
- \+ *lemma* part_enat.lt_def
- \+ *lemma* part_enat.lt_find
- \+ *lemma* part_enat.lt_find_iff
- \+ *lemma* part_enat.lt_wf
- \+ *lemma* part_enat.ne_top_iff
- \+ *lemma* part_enat.ne_top_iff_dom
- \+ *lemma* part_enat.ne_top_of_lt
- \+ *lemma* part_enat.ne_zero_iff
- \+ *lemma* part_enat.not_dom_iff_eq_top
- \+ *lemma* part_enat.not_is_max_coe
- \+ *lemma* part_enat.pos_iff_one_le
- \+ *def* part_enat.some
- \+ *lemma* part_enat.some_eq_coe
- \+ *def* part_enat.to_with_top
- \+ *lemma* part_enat.to_with_top_add
- \+ *lemma* part_enat.to_with_top_coe'
- \+ *lemma* part_enat.to_with_top_coe
- \+ *lemma* part_enat.to_with_top_le
- \+ *lemma* part_enat.to_with_top_lt
- \+ *lemma* part_enat.to_with_top_some
- \+ *lemma* part_enat.to_with_top_top'
- \+ *lemma* part_enat.to_with_top_top
- \+ *lemma* part_enat.to_with_top_zero'
- \+ *lemma* part_enat.to_with_top_zero
- \+ *lemma* part_enat.top_add
- \+ *lemma* part_enat.top_eq_none
- \+ *lemma* part_enat.with_top_equiv_coe
- \+ *lemma* part_enat.with_top_equiv_le
- \+ *lemma* part_enat.with_top_equiv_lt
- \+ *lemma* part_enat.with_top_equiv_symm_coe
- \+ *lemma* part_enat.with_top_equiv_symm_le
- \+ *lemma* part_enat.with_top_equiv_symm_lt
- \+ *lemma* part_enat.with_top_equiv_symm_top
- \+ *lemma* part_enat.with_top_equiv_symm_zero
- \+ *lemma* part_enat.with_top_equiv_top
- \+ *lemma* part_enat.with_top_equiv_zero
- \+ *def* part_enat

Modified src/data/nat/lattice.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/part.lean


Modified src/data/polynomial/div.lean


Modified src/field_theory/separable.lean


Modified src/number_theory/padics/padic_norm.lean


Modified src/number_theory/padics/padic_val.lean


Modified src/ring_theory/chain_of_divisors.lean


Modified src/ring_theory/dedekind_domain/ideal.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/multiplicity.lean
- \+/\- *lemma* multiplicity.dvd_iff_multiplicity_pos
- \+/\- *lemma* multiplicity.dvd_of_multiplicity_pos
- \+/\- *lemma* multiplicity.pow_dvd_of_le_multiplicity
- \+/\- *def* multiplicity

Modified src/ring_theory/power_series/basic.lean
- \+/\- *lemma* power_series.le_order
- \+/\- *def* power_series.order
- \+/\- *lemma* power_series.order_eq

Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/set_theory/cardinal/basic.lean
- \- *theorem* cardinal.aleph_0_to_enat
- \+ *theorem* cardinal.aleph_0_to_part_enat
- \- *lemma* cardinal.mk_to_enat_eq_coe_card
- \- *lemma* cardinal.mk_to_enat_of_infinite
- \+ *lemma* cardinal.mk_to_part_enat_eq_coe_card
- \+ *lemma* cardinal.mk_to_part_enat_of_infinite
- \- *def* cardinal.to_enat
- \- *lemma* cardinal.to_enat_apply_of_aleph_0_le
- \- *lemma* cardinal.to_enat_apply_of_lt_aleph_0
- \- *lemma* cardinal.to_enat_cast
- \- *lemma* cardinal.to_enat_surjective
- \+ *def* cardinal.to_part_enat
- \+ *lemma* cardinal.to_part_enat_apply_of_aleph_0_le
- \+ *lemma* cardinal.to_part_enat_apply_of_lt_aleph_0
- \+ *lemma* cardinal.to_part_enat_cast
- \+ *lemma* cardinal.to_part_enat_surjective

Modified src/set_theory/cardinal/continuum.lean
- \- *theorem* cardinal.continuum_to_enat
- \+ *theorem* cardinal.continuum_to_part_enat

Modified src/set_theory/cardinal/finite.lean
- \- *def* enat.card
- \- *lemma* enat.card_eq_coe_fintype_card
- \- *lemma* enat.card_eq_top_of_infinite
- \+ *def* part_enat.card
- \+ *lemma* part_enat.card_eq_coe_fintype_card
- \+ *lemma* part_enat.card_eq_top_of_infinite

Modified src/set_theory/cardinal/ordinal.lean
- \- *theorem* cardinal.aleph_to_enat
- \+ *theorem* cardinal.aleph_to_part_enat



## [2022-07-11 16:51:23](https://github.com/leanprover-community/mathlib/commit/44905df)
feat(order/hom/basic): `order_iso` to `rel_iso (<) (<)` ([#15182](https://github.com/leanprover-community/mathlib/pull/15182))
Couldn't find this in the library. Asked on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/rel_iso.20.28.3C.29.20.28.3C.29.20from.20order_iso/near/288891638) in case anyone knew of this already.
#### Estimated changes
Modified src/order/hom/basic.lean
- \+ *def* order_iso.to_rel_iso_lt



## [2022-07-11 16:51:22](https://github.com/leanprover-community/mathlib/commit/0f56b2d)
feat(combinatorics/simple_graph/connectivity): simp confluence ([#15153](https://github.com/leanprover-community/mathlib/pull/15153))
From branch `walks_and_trees`. Adds data/list/basic lemma to help simp prove `d ∈ p.reverse.darts ↔ d.symm ∈ p.darts`.
#### Estimated changes
Modified src/combinatorics/simple_graph/connectivity.lean
- \+/\- *lemma* simple_graph.walk.dart_snd_mem_support_of_mem_darts
- \+ *lemma* simple_graph.walk.fst_mem_support_of_mem_edges
- \+ *lemma* simple_graph.walk.is_cycle.not_of_nil
- \+ *lemma* simple_graph.walk.mem_darts_reverse
- \- *lemma* simple_graph.walk.mem_support_of_mem_edges
- \+ *lemma* simple_graph.walk.snd_mem_support_of_mem_edges

Modified src/data/list/basic.lean
- \+ *lemma* function.involutive.exists_mem_and_apply_eq_iff
- \+ *theorem* list.mem_map_of_involutive



## [2022-07-11 16:51:20](https://github.com/leanprover-community/mathlib/commit/9a2e5c8)
fix(order/basic): fix `subtype.linear_order` ([#15056](https://github.com/leanprover-community/mathlib/pull/15056))
This makes `subtype.lattice` definitionally equal to `linear_order.to_lattice`, after unfolding some (which?) semireducible definitions.
* Rewrite `linear_order.lift` to allow custom `max` and `min` fields. Move the old definition to `linear_order.lift'`.
* Use the new `linear_order.lift` to fix a non-defeq diamond on `subtype _`.
* Use the new `linear_order.lift` in various `function.injective.linear_*` definitions.
#### Estimated changes
Modified counterexamples/linear_order_with_pos_mul_pos_eq_zero.lean


Modified src/algebra/module/submodule/basic.lean


Modified src/algebra/order/field.lean


Modified src/algebra/order/group.lean


Modified src/algebra/order/monoid.lean
- \+ *def* units.order_embedding_coe

Modified src/algebra/order/nonneg.lean


Modified src/algebra/order/ring.lean


Modified src/algebra/order/with_zero.lean


Modified src/data/fin/basic.lean


Modified src/data/ulift.lean


Modified src/field_theory/subfield.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/group_theory/submonoid/operations.lean


Modified src/order/basic.lean
- \+ *def* linear_order.lift'
- \+/\- *def* linear_order.lift
- \+ *lemma* max_rec'
- \+ *lemma* max_rec
- \+ *lemma* min_rec'
- \+ *lemma* min_rec

Modified src/order/category/NonemptyFinLinOrd.lean


Modified src/order/lattice.lean


Modified src/order/min_max.lean
- \- *lemma* max_rec'
- \- *lemma* max_rec
- \- *lemma* min_rec'
- \- *lemma* min_rec

Modified src/ring_theory/subring/basic.lean


Modified src/ring_theory/subsemiring/basic.lean




## [2022-07-11 16:51:19](https://github.com/leanprover-community/mathlib/commit/bbe25d4)
feat(category_theory): left-exact functors preserve finite limits ([#14026](https://github.com/leanprover-community/mathlib/pull/14026))
Also adds the following:
* Convenient constructors for `binary_fan` and adjustments to its simp NF
* Generalize the (co)kernel constructions in inclusions and projections of binary biproducts
* Fixes the name of `kernel_fork.is_limit.of_ι`
* Derives `preserves_limits_of_shape (discrete pempty) G` from the preservation of just *the* terminal morphism
* Preserving zero morphisms implies preserving terminal morphisms
* Isomorphisms from any fork to an application of `fork.of_ι`
#### Estimated changes
Modified src/category_theory/abelian/exact.lean


Modified src/category_theory/limits/constructions/finite_products_of_binary_products.lean


Modified src/category_theory/limits/preserves/shapes/terminal.lean
- \+ *def* category_theory.limits.preserves_colimits_of_shape_pempty_of_preserves_initial
- \+ *def* category_theory.limits.preserves_limits_of_shape_pempty_of_preserves_terminal

Modified src/category_theory/limits/preserves/shapes/zero.lean
- \+ *def* category_theory.functor.preserves_initial_object_of_preserves_zero_morphisms
- \+ *def* category_theory.functor.preserves_terminal_object_of_preserves_zero_morphisms

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* category_theory.limits.binary_cofan.mk_inl
- \+ *lemma* category_theory.limits.binary_cofan.mk_inr
- \- *lemma* category_theory.limits.binary_cofan.mk_ι_app_left
- \- *lemma* category_theory.limits.binary_cofan.mk_ι_app_right
- \+ *lemma* category_theory.limits.binary_fan.mk_fst
- \+ *lemma* category_theory.limits.binary_fan.mk_snd
- \- *lemma* category_theory.limits.binary_fan.mk_π_app_left
- \- *lemma* category_theory.limits.binary_fan.mk_π_app_right
- \+ *def* category_theory.limits.iso_binary_cofan_mk
- \+ *def* category_theory.limits.iso_binary_fan_mk

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.binary_bicone.fst_kernel_fork
- \+ *lemma* category_theory.limits.binary_bicone.fst_kernel_fork_ι
- \+ *def* category_theory.limits.binary_bicone.inl_cokernel_cofork
- \+ *lemma* category_theory.limits.binary_bicone.inl_cokernel_cofork_π
- \+ *def* category_theory.limits.binary_bicone.inr_cokernel_cofork
- \+ *lemma* category_theory.limits.binary_bicone.inr_cokernel_cofork_π
- \+ *def* category_theory.limits.binary_bicone.is_colimit_inl_cokernel_cofork
- \+ *def* category_theory.limits.binary_bicone.is_colimit_inr_cokernel_cofork
- \+ *def* category_theory.limits.binary_bicone.is_limit_fst_kernel_fork
- \+ *def* category_theory.limits.binary_bicone.is_limit_snd_kernel_fork
- \+ *def* category_theory.limits.binary_bicone.snd_kernel_fork
- \+ *lemma* category_theory.limits.binary_bicone.snd_kernel_fork_ι
- \+ *def* category_theory.limits.biprod.inl_cokernel_cofork
- \+ *lemma* category_theory.limits.biprod.inl_cokernel_cofork_π
- \- *def* category_theory.limits.biprod.inl_cokernel_fork
- \- *lemma* category_theory.limits.biprod.inl_cokernel_fork_π
- \+ *def* category_theory.limits.biprod.inr_cokernel_cofork
- \+ *lemma* category_theory.limits.biprod.inr_cokernel_cofork_π
- \- *def* category_theory.limits.biprod.inr_cokernel_fork
- \- *lemma* category_theory.limits.biprod.inr_cokernel_fork_π
- \+/\- *def* category_theory.limits.biprod.is_cokernel_inl_cokernel_fork
- \+/\- *def* category_theory.limits.biprod.is_cokernel_inr_cokernel_fork

Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* category_theory.limits.cofork.iso_cofork_of_π
- \+ *lemma* category_theory.limits.cofork.π_precompose
- \+ *def* category_theory.limits.fork.iso_fork_of_ι
- \+ *lemma* category_theory.limits.fork.ι_postcompose
- \+ *def* category_theory.limits.parallel_pair.eq_of_hom_eq

Modified src/category_theory/limits/shapes/images.lean


Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.cokernel_cofork.is_colimit.of_π
- \- *def* category_theory.limits.is_colimit.of_π
- \- *def* category_theory.limits.is_limit.of_ι
- \+ *def* category_theory.limits.kernel_fork.is_limit.of_ι

Modified src/category_theory/limits/shapes/normal_mono/basic.lean


Modified src/category_theory/preadditive/additive_functor.lean


Modified src/category_theory/preadditive/default.lean
- \+ *lemma* category_theory.preadditive.cofork_of_cokernel_cofork_π
- \+ *lemma* category_theory.preadditive.fork_of_kernel_fork_ι

Added src/category_theory/preadditive/left_exact.lean
- \+ *def* category_theory.functor.is_colimit_map_cocone_binary_cofan_of_preserves_cokernels
- \+ *def* category_theory.functor.is_limit_map_cone_binary_fan_of_preserves_kernels
- \+ *def* category_theory.functor.preserves_binary_coproducts_of_preserves_cokernels
- \+ *def* category_theory.functor.preserves_binary_product_of_preserves_kernels
- \+ *def* category_theory.functor.preserves_binary_products_of_preserves_kernels
- \+ *def* category_theory.functor.preserves_coequalizer_of_preserves_cokernels
- \+ *def* category_theory.functor.preserves_coequalizers_of_preserves_cokernels
- \+ *def* category_theory.functor.preserves_coproduct_of_preserves_cokernels
- \+ *def* category_theory.functor.preserves_equalizer_of_preserves_kernels
- \+ *def* category_theory.functor.preserves_equalizers_of_preserves_kernels
- \+ *def* category_theory.functor.preserves_finite_colimits_of_preserves_cokernels
- \+ *def* category_theory.functor.preserves_finite_limits_of_preserves_kernels



## [2022-07-11 16:51:18](https://github.com/leanprover-community/mathlib/commit/d3f5adb)
feat(combinatorics/simple_graph/regularity/equitabilise): Equitabilising a partition ([#13222](https://github.com/leanprover-community/mathlib/pull/13222))
Define the equitabilisation of a partition and a way to find an arbitrary equipartition of any size.
#### Estimated changes
Added src/combinatorics/simple_graph/regularity/equitabilise.lean
- \+ *lemma* finpartition.card_eq_of_mem_parts_equitabilise
- \+ *lemma* finpartition.card_filter_equitabilise_big
- \+ *lemma* finpartition.card_filter_equitabilise_small
- \+ *lemma* finpartition.card_parts_equitabilise
- \+ *lemma* finpartition.card_parts_equitabilise_subset_le
- \+ *lemma* finpartition.equitabilise_aux
- \+ *lemma* finpartition.equitabilise_is_equipartition
- \+ *lemma* finpartition.exists_equipartition_card_eq

Modified src/order/partition/finpartition.lean
- \+ *lemma* finpartition.mem_avoid



## [2022-07-11 16:51:17](https://github.com/leanprover-community/mathlib/commit/888caf7)
feat(order/modular_lattice): Semimodular lattices ([#11602](https://github.com/leanprover-community/mathlib/pull/11602))
This defines the four main kinds of semimodular lattices:
* Weakly upper modular
* Weakly lower modular
* Upper modular
* Lower modular
#### Estimated changes
Modified docs/references.bib


Modified src/order/modular_lattice.lean
- \+ *lemma* covby_sup_of_inf_covby_left
- \+ *lemma* covby_sup_of_inf_covby_of_inf_covby_left
- \+ *lemma* covby_sup_of_inf_covby_of_inf_covby_right
- \+ *lemma* covby_sup_of_inf_covby_right
- \+ *lemma* inf_covby_of_covby_sup_left
- \+ *lemma* inf_covby_of_covby_sup_of_covby_sup_left
- \+ *lemma* inf_covby_of_covby_sup_of_covby_sup_right
- \+ *lemma* inf_covby_of_covby_sup_right



## [2022-07-11 14:26:39](https://github.com/leanprover-community/mathlib/commit/dfcbe85)
refactor(data/finite): move definition to a new file ([#15204](https://github.com/leanprover-community/mathlib/pull/15204))
The new file imports nothing but `logic.equiv.basic`.
#### Estimated changes
Modified src/data/finite/basic.lean
- \- *lemma* equiv.finite_iff
- \- *lemma* finite.exists_equiv_fin
- \- *lemma* finite.of_bijective
- \- *lemma* finite.of_equiv
- \- *lemma* finite.of_fintype
- \- *lemma* finite_iff_exists_equiv_fin

Added src/data/finite/defs.lean
- \+ *lemma* equiv.finite_iff
- \+ *lemma* finite.exists_equiv_fin
- \+ *lemma* finite.of_bijective
- \+ *lemma* finite.of_equiv
- \+ *lemma* finite_iff_exists_equiv_fin
- \+ *lemma* function.bijective.finite_iff



## [2022-07-11 14:26:38](https://github.com/leanprover-community/mathlib/commit/aae01cd)
data/multiset/range): add multiset.coe_range ([#15201](https://github.com/leanprover-community/mathlib/pull/15201))
#### Estimated changes
Modified src/data/multiset/range.lean
- \+ *theorem* multiset.coe_range



## [2022-07-11 14:26:37](https://github.com/leanprover-community/mathlib/commit/627bd0c)
chore(topology/basic): use `finite` in `locally_finite_of_finite` ([#15181](https://github.com/leanprover-community/mathlib/pull/15181))
Rename `locally_finite_of_fintype` to `locally_finite_of_finite`, use `[finite]` instead of `[fintype]`.
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* locally_finite_of_finite
- \- *lemma* locally_finite_of_fintype

Modified src/topology/paracompact.lean




## [2022-07-11 14:26:36](https://github.com/leanprover-community/mathlib/commit/7f837db)
feat(data/set/finite): add `multiset.finite_to_set` ([#15177](https://github.com/leanprover-community/mathlib/pull/15177))
* move `finset.finite_to_set` up;
* add `multiset.finite_to_set`, `multiset.finite_to_set_to_finset`, and `list.finite_to_set`;
* use new lemmas here and there.
#### Estimated changes
Modified src/data/set/finite.lean
- \+/\- *lemma* finset.finite_to_set
- \+/\- *lemma* finset.finite_to_set_to_finset
- \+ *lemma* list.finite_to_set
- \+ *lemma* multiset.finite_to_set
- \+ *lemma* multiset.finite_to_set_to_finset
- \- *lemma* set.range_find_greatest_subset

Modified src/field_theory/adjoin.lean


Modified src/field_theory/is_alg_closed/classification.lean


Modified src/field_theory/splitting_field.lean


Modified src/measure_theory/measure/haar.lean


Modified src/ring_theory/adjoin/fg.lean


Modified src/ring_theory/integral_closure.lean




## [2022-07-11 14:26:34](https://github.com/leanprover-community/mathlib/commit/ecd5234)
feat(linear_algebra): basis on R × R, and relation between matrices and linear maps in this basis  ([#15119](https://github.com/leanprover-community/mathlib/pull/15119))
#### Estimated changes
Modified src/algebra/big_operators/fin.lean
- \+/\- *theorem* fin.prod_univ_two

Modified src/linear_algebra/basis.lean
- \+ *lemma* basis.coe_fin_two_prod_repr
- \+ *lemma* basis.fin_two_prod_one
- \+ *lemma* basis.fin_two_prod_zero

Modified src/linear_algebra/determinant.lean
- \+ *lemma* linear_map.det_to_lin

Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* matrix.det_fin_one_mk
- \+ *lemma* matrix.det_fin_two_mk

Modified src/linear_algebra/matrix/to_lin.lean
- \+ *lemma* matrix.to_lin_fin_two_prod
- \+ *lemma* matrix.to_lin_fin_two_prod_apply

Modified src/topology/algebra/module/finite_dimension.lean
- \+ *lemma* linear_map.det_to_continuous_linear_map
- \+ *lemma* matrix.to_lin_fin_two_prod_to_continuous_linear_map



## [2022-07-11 14:26:33](https://github.com/leanprover-community/mathlib/commit/611dcca)
feat(analysis/inner_product_space): the Hellinger-Toeplitz theorem ([#15055](https://github.com/leanprover-community/mathlib/pull/15055))
Prove the Hellinger-Toeplitz theorem as a corollary of the closed graph theorem.
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+ *def* inner_product_space.is_self_adjoint.clm
- \+ *lemma* inner_product_space.is_self_adjoint.clm_apply
- \+ *lemma* inner_product_space.is_self_adjoint.continuous



## [2022-07-11 14:26:32](https://github.com/leanprover-community/mathlib/commit/0980bac)
chore(topological_space/sober): use `namespace` and `variables`, golf ([#15042](https://github.com/leanprover-community/mathlib/pull/15042))
#### API
* Add `is_generic_point_iff_specializes`, `is_generic_point.specializes_iff_mem`.
* Make `is_generic_point.is_closed` etc `protected`.
#### Style
* Use `namespace is_generic_point`.
* Move implicit arguments to `variables`.
* Move explicit `(h : is_generic_point x S)` from `variables` to each lemma.
* Golf some proofs.
#### Estimated changes
Modified src/data/set/lattice.lean


Modified src/topology/sober.lean
- \+/\- *lemma* is_generic_point.disjoint_iff
- \- *lemma* is_generic_point.eq
- \- *lemma* is_generic_point.image
- \- *lemma* is_generic_point.is_closed
- \- *lemma* is_generic_point.is_irreducible
- \+/\- *lemma* is_generic_point.mem
- \+/\- *lemma* is_generic_point.mem_closed_set_iff
- \+/\- *lemma* is_generic_point.mem_open_set_iff
- \+/\- *lemma* is_generic_point.specializes
- \+ *lemma* is_generic_point.specializes_iff_mem
- \+/\- *lemma* is_generic_point_iff_forall_closed
- \+ *lemma* is_generic_point_iff_specializes



## [2022-07-11 14:26:30](https://github.com/leanprover-community/mathlib/commit/902e351)
feat(data/set/pointwise): `list` and `multiset` versions of n-ary lemmas ([#14928](https://github.com/leanprover-community/mathlib/pull/14928))
These lemmas are generalizations of the existing lemmas about `finset.prod` and `finset.sum`, but for the `list` and `multiset` versions.
The finset ones can now be proved in terms of the multiset ones.
#### Estimated changes
Modified src/data/set/pointwise.lean
- \+ *lemma* set.list_prod_mem_list_prod
- \+ *lemma* set.list_prod_singleton
- \+ *lemma* set.list_prod_subset_list_prod
- \+ *lemma* set.multiset_prod_mem_multiset_prod
- \+ *lemma* set.multiset_prod_singleton
- \+ *lemma* set.multiset_prod_subset_multiset_prod



## [2022-07-11 14:26:29](https://github.com/leanprover-community/mathlib/commit/b762695)
feat(algebraic_geometry/projective_spectrum): forward direction of homeomorphism between top_space of Proj and top_space of Spec ([#13397](https://github.com/leanprover-community/mathlib/pull/13397))
This pr is the start of showing that Proj is a scheme. In this pr, it will be shown that the locally on basic open set, there is a continuous function from the underlying topological space of Proj restricted to this open set to Spec of degree zero part of some localised ring. In the near future, it will be shown that this function is a homeomorphism.
#### Estimated changes
Modified src/algebraic_geometry/projective_spectrum/scheme.lean
- \+ *def* algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.carrier
- \+ *lemma* algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.carrier_ne_top
- \+ *lemma* algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.disjoint
- \+ *lemma* algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.mem_carrier.clear_denominator
- \+ *lemma* algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff
- \+ *lemma* algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.preimage_eq
- \+ *def* algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.to_fun
- \+ *def* algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec
- \+ *lemma* algebraic_geometry.degree_zero_part.coe_mul
- \+/\- *def* algebraic_geometry.degree_zero_part.deg
- \+/\- *lemma* algebraic_geometry.degree_zero_part.eq
- \- *lemma* algebraic_geometry.degree_zero_part.mul_val
- \+/\- *def* algebraic_geometry.degree_zero_part.num
- \+/\- *lemma* algebraic_geometry.degree_zero_part.num_mem

Modified src/algebraic_geometry/projective_spectrum/structure_sheaf.lean




## [2022-07-11 09:33:58](https://github.com/leanprover-community/mathlib/commit/cea2769)
chore(category_theory/adjunction/*): making arguments implicit in adjuction.comp and two small lemmas about mates ([#15062](https://github.com/leanprover-community/mathlib/pull/15062))
Working on adjunctions between monads and comonads, I noticed that adjunction.comp was defined with having the functors of one of the adjunctions explicit as well as the adjunction. However in the library, only `adjunction.comp _ _` ever appears. Thus I found it natural to make these two arguments implicit, so that composition of adjunctions can now be written as `adj1.comp adj2` instead of `adj1.comp _ _ adj2`. 
Furthermore, I provide two lemmas about mates of natural transformations to and from the identity functor. The application I have in mind is to the unit/counit of a monad/comonad in case of an adjunction of monads and comonads, as studied already by Eilenberg and Moore.
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/mates.lean
- \+ *lemma* category_theory.transfer_nat_trans_self_adjunction_id
- \+ *lemma* category_theory.transfer_nat_trans_self_adjunction_id_symm

Modified src/category_theory/adjunction/over.lean


Modified src/category_theory/closed/functor.lean


Modified src/category_theory/limits/over.lean


Modified src/category_theory/sites/adjunction.lean


Modified src/category_theory/sites/cover_preserving.lean


Modified src/category_theory/subobject/mono_over.lean




## [2022-07-11 09:33:57](https://github.com/leanprover-community/mathlib/commit/4e19dab)
chore(algebra/order/ring): Normalize `_left`/`_right` ([#14985](https://github.com/leanprover-community/mathlib/pull/14985))
Swap the `left` and `right` variants of
* `nonneg_of_mul_nonneg_`
* `pos_of_mul_pos_`
* `neg_of_mul_pos_`
* `neg_of_mul_neg_`
#### Estimated changes
Modified archive/imo/imo1988_q6.lean


Modified archive/imo/imo2013_q5.lean


Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/order/invertible.lean


Modified src/algebra/order/monoid_lemmas_zero_lt.lean
- \+/\- *lemma* zero_lt.pos_of_mul_pos_left
- \+/\- *lemma* zero_lt.pos_of_mul_pos_right

Modified src/algebra/order/ring.lean
- \+/\- *lemma* neg_of_mul_neg_left
- \+/\- *lemma* neg_of_mul_neg_right
- \+/\- *lemma* neg_of_mul_pos_left
- \+/\- *lemma* neg_of_mul_pos_right
- \+/\- *lemma* nonneg_of_mul_nonneg_left
- \+/\- *lemma* nonneg_of_mul_nonneg_right
- \+/\- *lemma* nonpos_of_mul_nonpos_left
- \+/\- *lemma* nonpos_of_mul_nonpos_right
- \+/\- *lemma* pos_of_mul_pos_left
- \+/\- *lemma* pos_of_mul_pos_right

Modified src/algebra/order/smul.lean


Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/calculus/darboux.lean


Modified src/analysis/inner_product_space/projection.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/seminorm.lean


Modified src/combinatorics/simple_graph/regularity/bound.lean


Modified src/data/fin/basic.lean


Modified src/data/int/basic.lean


Modified src/data/rat/floor.lean


Modified src/data/rat/order.lean


Modified src/geometry/euclidean/triangle.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/order/filter/at_top_bot.lean


Modified src/ring_theory/polynomial/cyclotomic/eval.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/unit_interval.lean




## [2022-07-11 09:33:56](https://github.com/leanprover-community/mathlib/commit/40fdf72)
feat(category_theory/endofunctor/algebra): Define coalgebras over an endofunctor and prove an equivalence ([#14834](https://github.com/leanprover-community/mathlib/pull/14834))
This PR dualises the definition of an algebra over an endofunctor to that of a coalgebra over an endofunctor. Furthermore, it proves that if an endofunctor `F` is left adjoint to an endofunctor `G`, then the category of algebras over `F` is equivalent to the category of coalgebras over `G`.
#### Estimated changes
Modified src/category_theory/endofunctor/algebra.lean
- \+ *def* category_theory.endofunctor.adjunction.alg_coalg_equiv.counit_iso
- \+ *def* category_theory.endofunctor.adjunction.alg_coalg_equiv.unit_iso
- \+ *lemma* category_theory.endofunctor.adjunction.algebra.hom_equiv_naturality_str
- \+ *def* category_theory.endofunctor.adjunction.algebra.to_coalgebra_of
- \+ *def* category_theory.endofunctor.adjunction.algebra_coalgebra_equiv
- \+ *lemma* category_theory.endofunctor.adjunction.coalgebra.hom_equiv_naturality_str_symm
- \+ *def* category_theory.endofunctor.adjunction.coalgebra.to_algebra_of
- \+ *lemma* category_theory.endofunctor.coalgebra.comp_eq_comp
- \+ *lemma* category_theory.endofunctor.coalgebra.comp_f
- \+ *def* category_theory.endofunctor.coalgebra.equiv_of_nat_iso
- \+ *def* category_theory.endofunctor.coalgebra.forget
- \+ *def* category_theory.endofunctor.coalgebra.functor_of_nat_trans
- \+ *def* category_theory.endofunctor.coalgebra.functor_of_nat_trans_comp
- \+ *def* category_theory.endofunctor.coalgebra.functor_of_nat_trans_eq
- \+ *def* category_theory.endofunctor.coalgebra.functor_of_nat_trans_id
- \+ *def* category_theory.endofunctor.coalgebra.hom.comp
- \+ *def* category_theory.endofunctor.coalgebra.hom.id
- \+ *lemma* category_theory.endofunctor.coalgebra.id_eq_id
- \+ *lemma* category_theory.endofunctor.coalgebra.id_f
- \+ *def* category_theory.endofunctor.coalgebra.iso_mk
- \+ *lemma* category_theory.endofunctor.coalgebra.iso_of_iso



## [2022-07-11 09:33:55](https://github.com/leanprover-community/mathlib/commit/f7baecb)
feat(category_theory/functor): preserving/reflecting monos/epis ([#14829](https://github.com/leanprover-community/mathlib/pull/14829))
#### Estimated changes
Modified src/algebra/category/Group/abelian.lean


Modified src/algebra/category/Group/adjunctions.lean


Modified src/algebraic_geometry/open_immersion.lean


Modified src/category_theory/adjunction/evaluation.lean


Modified src/category_theory/concrete_category/basic.lean


Modified src/category_theory/epi_mono.lean
- \- *lemma* category_theory.faithful_reflects_epi
- \- *lemma* category_theory.faithful_reflects_mono
- \- *lemma* category_theory.left_adjoint_preserves_epi
- \- *lemma* category_theory.right_adjoint_preserves_mono

Added src/category_theory/functor/epi_mono.lean
- \+ *lemma* category_theory.functor.epi_of_epi_map
- \+ *lemma* category_theory.functor.mono_of_mono_map
- \+ *lemma* category_theory.functor.preserves_epimorphisms.iso_iff
- \+ *lemma* category_theory.functor.preserves_epimorphisms.of_iso
- \+ *lemma* category_theory.functor.preserves_epimorphsisms_of_adjunction
- \+ *lemma* category_theory.functor.preserves_monomorphisms.iso_iff
- \+ *lemma* category_theory.functor.preserves_monomorphisms.of_iso
- \+ *lemma* category_theory.functor.preserves_monomorphisms_of_adjunction
- \+ *lemma* category_theory.functor.reflects_epimorphisms.iso_iff
- \+ *lemma* category_theory.functor.reflects_epimorphisms.of_iso
- \+ *lemma* category_theory.functor.reflects_monomorphisms.iso_iff
- \+ *lemma* category_theory.functor.reflects_monomorphisms.of_iso

Modified src/category_theory/glue_data.lean


Modified src/category_theory/limits/constructions/epi_mono.lean
- \+ *lemma* category_theory.preserves_epi_of_preserves_colimit
- \+ *lemma* category_theory.preserves_mono_of_preserves_limit
- \- *lemma* category_theory.reflects_epi
- \+ *lemma* category_theory.reflects_epi_of_reflects_colimit
- \- *lemma* category_theory.reflects_mono
- \+ *lemma* category_theory.reflects_mono_of_reflects_limit

Modified src/category_theory/over.lean


Modified src/topology/category/CompHaus/default.lean


Modified src/topology/category/Profinite/default.lean


Modified src/topology/category/Top/adjunctions.lean


Modified src/topology/category/Top/epi_mono.lean




## [2022-07-11 09:33:54](https://github.com/leanprover-community/mathlib/commit/3536347)
feat(combinatorics/set_family/harris_kleitman): The Harris-Kleitman inequality ([#14497](https://github.com/leanprover-community/mathlib/pull/14497))
Lower/upper sets in `finset α` are (anti)correlated.
#### Estimated changes
Added src/combinatorics/set_family/harris_kleitman.lean
- \+ *lemma* finset.card_member_subfamily_add_card_non_member_subfamily
- \+ *lemma* finset.mem_member_subfamily
- \+ *lemma* finset.mem_non_member_subfamily
- \+ *def* finset.member_subfamily
- \+ *lemma* finset.member_subfamily_inter
- \+ *def* finset.non_member_subfamily
- \+ *lemma* finset.non_member_subfamily_inter
- \+ *lemma* is_lower_set.card_inter_le_finset
- \+ *lemma* is_lower_set.le_card_inter_finset'
- \+ *lemma* is_lower_set.le_card_inter_finset
- \+ *lemma* is_lower_set.member_subfamily
- \+ *lemma* is_lower_set.member_subfamily_subset_non_member_subfamily
- \+ *lemma* is_lower_set.non_member_subfamily
- \+ *lemma* is_upper_set.card_inter_le_finset
- \+ *lemma* is_upper_set.le_card_inter_finset

Modified src/order/upper_lower.lean
- \+ *lemma* is_lower_set_compl
- \+ *lemma* is_upper_set_compl



## [2022-07-11 09:33:53](https://github.com/leanprover-community/mathlib/commit/f5170fc)
feat(order/bounded_order): Codisjointness ([#14195](https://github.com/leanprover-community/mathlib/pull/14195))
Define `codisjoint`, the dual notion of `disjoint`. This is already used without a name in `is_compl`, and will soon be used for Heyting algebras.
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/sesquilinear_form.lean


Modified src/order/bounded_order.lean
- \+ *lemma* bot_codisjoint
- \+ *lemma* codisjoint.comm
- \+ *lemma* codisjoint.dual
- \+ *lemma* codisjoint.eq_top
- \+ *lemma* codisjoint.eq_top_of_ge
- \+ *lemma* codisjoint.eq_top_of_le
- \+ *lemma* codisjoint.inf_left
- \+ *lemma* codisjoint.inf_right
- \+ *lemma* codisjoint.left_le_of_le_inf_left
- \+ *lemma* codisjoint.left_le_of_le_inf_right
- \+ *lemma* codisjoint.mono
- \+ *lemma* codisjoint.mono_left
- \+ *lemma* codisjoint.mono_right
- \+ *lemma* codisjoint.ne
- \+ *lemma* codisjoint.of_codisjoint_sup_of_le'
- \+ *lemma* codisjoint.of_codisjoint_sup_of_le
- \+ *lemma* codisjoint.sup_left'
- \+ *lemma* codisjoint.sup_left
- \+ *lemma* codisjoint.sup_right'
- \+ *lemma* codisjoint.sup_right
- \+ *lemma* codisjoint.symm
- \+ *def* codisjoint
- \+ *lemma* codisjoint_assoc
- \+ *lemma* codisjoint_bot
- \+ *lemma* codisjoint_iff
- \+ *lemma* codisjoint_inf_left
- \+ *lemma* codisjoint_inf_right
- \+ *lemma* codisjoint_of_dual_iff
- \+ *lemma* codisjoint_self
- \+ *lemma* codisjoint_to_dual_iff
- \+ *lemma* codisjoint_top_left
- \+ *lemma* codisjoint_top_right
- \+ *lemma* disjoint.dual
- \+ *lemma* disjoint_of_dual_iff
- \+ *lemma* disjoint_to_dual_iff
- \+/\- *lemma* is_compl.of_eq
- \+/\- *lemma* is_compl.sup_eq_top
- \+ *lemma* symmetric_codisjoint

Modified src/order/compactly_generated.lean


Modified src/order/filter/basic.lean


Modified src/order/hom/basic.lean
- \+ *lemma* codisjoint.map_order_iso
- \+ *lemma* codisjoint_map_order_iso_iff
- \+/\- *lemma* order_embedding.le_map_sup
- \+/\- *lemma* order_embedding.map_inf_le
- \+/\- *lemma* order_iso.map_inf
- \+/\- *lemma* order_iso.map_sup

Modified src/order/hom/lattice.lean
- \+ *lemma* codisjoint.map
- \+/\- *lemma* is_compl.map



## [2022-07-11 08:26:44](https://github.com/leanprover-community/mathlib/commit/b7148c4)
feat(analysis/special_functions/pow): Rational powers are dense ([#15002](https://github.com/leanprover-community/mathlib/pull/15002))
There is a rational square between any two positive elements of an archimedean ordered field.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* real.exists_rat_pow_btwn
- \+ *lemma* real.exists_rat_pow_btwn_rat
- \+ *lemma* real.exists_rat_pow_btwn_rat_aux

Modified src/data/real/sqrt.lean
- \+ *lemma* real.lt_sq_of_sqrt_lt



## [2022-07-11 02:42:30](https://github.com/leanprover-community/mathlib/commit/e3e4cc6)
feat(data/nat/basic): split `exists_lt_and_lt_iff_not_dvd` into `if` and `iff` lemmas ([#15099](https://github.com/leanprover-community/mathlib/pull/15099))
Pull out from `exists_lt_and_lt_iff_not_dvd` ("`n` is not divisible by `a` iff it is between `a * k` and `a * (k + 1)` for some `k`") a separate lemma proving the forward direction (which doesn't need the `0 < a` assumption) and use this to golf the `iff` lemma.
Also renames the lemma to the more descriptive `not_dvd_{of,iff}_between_consec_multiples`.
#### Estimated changes
Modified src/data/nat/basic.lean
- \- *lemma* nat.exists_lt_and_lt_iff_not_dvd
- \+ *lemma* nat.not_dvd_iff_between_consec_multiples
- \+ *lemma* nat.not_dvd_of_between_consec_multiples

Modified src/data/nat/multiplicity.lean




## [2022-07-11 02:42:29](https://github.com/leanprover-community/mathlib/commit/67779f7)
feat(algebra/category/BoolRing): The equivalence between Boolean rings and Boolean algebras ([#15019](https://github.com/leanprover-community/mathlib/pull/15019))
as the categorical equivalence `BoolRing ≌ BoolAlg`.
#### Estimated changes
Modified src/algebra/category/BoolRing.lean
- \+ *def* BoolRing_equiv_BoolAlg



## [2022-07-11 00:36:10](https://github.com/leanprover-community/mathlib/commit/b18b71c)
refactor(data/finset/lattice): respell `finset.max/finset.min` using `sup/inf coe` ([#15217](https://github.com/leanprover-community/mathlib/pull/15217))
This PR simply redefines
* `finset.max s` with the defeq `finset.sup s coe`,
* `finset.min s` with the defeq `finset.sup/inf s coe`.
This arose from PR [#15212](https://github.com/leanprover-community/mathlib/pull/15212).
#### Estimated changes
Modified src/data/finset/lattice.lean




## [2022-07-10 19:29:29](https://github.com/leanprover-community/mathlib/commit/ad08001)
feat(category_theory/limits): opposites of limit pullback cones ([#14526](https://github.com/leanprover-community/mathlib/pull/14526))
Among other similar statements, this PR associates a `pullback_cone f g` to a `pushout_cocone f.op g.op`, and it is a limit pullback cone if the original cocone is a colimit cocone.
#### Estimated changes
Modified src/category_theory/limits/opposites.lean
- \+ *def* category_theory.limits.cospan_op
- \+ *def* category_theory.limits.op_cospan
- \+ *def* category_theory.limits.op_span
- \+ *def* category_theory.limits.pullback_cone.is_limit_equiv_is_colimit_op
- \+ *def* category_theory.limits.pullback_cone.is_limit_equiv_is_colimit_unop
- \+ *def* category_theory.limits.pullback_cone.op
- \+ *lemma* category_theory.limits.pullback_cone.op_inl
- \+ *lemma* category_theory.limits.pullback_cone.op_inr
- \+ *def* category_theory.limits.pullback_cone.op_unop
- \+ *def* category_theory.limits.pullback_cone.unop
- \+ *lemma* category_theory.limits.pullback_cone.unop_inl
- \+ *lemma* category_theory.limits.pullback_cone.unop_inr
- \+ *def* category_theory.limits.pullback_cone.unop_op
- \+ *def* category_theory.limits.pushout_cocone.is_colimit_equiv_is_limit_op
- \+ *def* category_theory.limits.pushout_cocone.is_colimit_equiv_is_limit_unop
- \+ *def* category_theory.limits.pushout_cocone.op
- \+ *lemma* category_theory.limits.pushout_cocone.op_fst
- \+ *lemma* category_theory.limits.pushout_cocone.op_snd
- \+ *def* category_theory.limits.pushout_cocone.op_unop
- \+ *def* category_theory.limits.pushout_cocone.unop
- \+ *lemma* category_theory.limits.pushout_cocone.unop_fst
- \+ *def* category_theory.limits.pushout_cocone.unop_op
- \+ *lemma* category_theory.limits.pushout_cocone.unop_snd
- \+ *def* category_theory.limits.span_op

Modified src/category_theory/limits/shapes/pullbacks.lean




## [2022-07-10 17:43:04](https://github.com/leanprover-community/mathlib/commit/f4f0f67)
feat(set_theory/zfc): simp lemmas for `arity` and `const` ([#15214](https://github.com/leanprover-community/mathlib/pull/15214))
#### Estimated changes
Modified src/set_theory/zfc.lean
- \+ *theorem* arity.const_succ
- \+ *theorem* arity.const_succ_apply
- \+ *theorem* arity.const_zero
- \+ *theorem* arity_succ
- \+ *theorem* arity_zero



## [2022-07-10 17:43:03](https://github.com/leanprover-community/mathlib/commit/cf4783f)
feat(set_theory/zfc): basic lemmas on `pSet.equiv` ([#15211](https://github.com/leanprover-community/mathlib/pull/15211))
We unfold the complex definition into something easier to use.
#### Estimated changes
Modified src/set_theory/zfc.lean
- \+ *theorem* pSet.exists_equiv_left
- \+ *theorem* pSet.exists_equiv_right



## [2022-07-10 17:43:01](https://github.com/leanprover-community/mathlib/commit/4b6ec60)
lint(topology/algebra/order/basic): use `finite` instead of `fintype` ([#15203](https://github.com/leanprover-community/mathlib/pull/15203))
#### Estimated changes
Modified src/topology/algebra/order/basic.lean




## [2022-07-10 15:28:36](https://github.com/leanprover-community/mathlib/commit/f51aaab)
feat(algebra/order/monoid) Add zero_le_three and zero_le_four ([#15219](https://github.com/leanprover-community/mathlib/pull/15219))
#### Estimated changes
Modified src/algebra/order/monoid.lean
- \+ *lemma* zero_le_four
- \+ *lemma* zero_le_three



## [2022-07-10 15:28:35](https://github.com/leanprover-community/mathlib/commit/e5b8d09)
feat(data/finset/lattice): add three*2 lemmas about `finset.max/min` ([#15212](https://github.com/leanprover-community/mathlib/pull/15212))
The three lemmas are
* `mem_le_max: ↑a ≤ s.max`,
* `max_mono : s.max ≤ t.max`,
* `max_le : s.max ≤ M`,
and
* `min_le_coe_of_mem : s.min`,
* `min_mono : t.min ≤ s.min`,
* `le_min : m ≤ s.min`.
~~I feel that I did not get the hang of `finset.max`: probably a lot of golfing is possible, at least for `max_mono`!~~
Luckily, Eric looked at the PR and now the proofs have been shortened!
I also golfed `le_max_of_mem` and `min_le_of_mem`.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.coe_le_max_of_mem
- \+ *lemma* finset.le_min
- \+ *lemma* finset.max_le
- \+ *lemma* finset.max_mono
- \+ *lemma* finset.min_le_coe_of_mem
- \+ *lemma* finset.min_mono



## [2022-07-10 15:28:34](https://github.com/leanprover-community/mathlib/commit/5305d39)
feat(data/pnat/basic): `succ` as an order isomorphism between `ℕ` and `ℕ+` ([#15183](https://github.com/leanprover-community/mathlib/pull/15183))
Couldn't find this in the library. Asked on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/order.20isomorphism.20between.20.E2.84.95.20and.20.E2.84.95.2B/near/288891689) in case anyone knew of this already.
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *def* pnat.succ_order_iso



## [2022-07-10 14:02:39](https://github.com/leanprover-community/mathlib/commit/37c2777)
feat(order/filter/ultrafilter): `pure`, `map`, and `comap` lemmas ([#15187](https://github.com/leanprover-community/mathlib/pull/15187))
A handful of simple lemmas.
#### Estimated changes
Modified src/order/filter/ultrafilter.lean
- \+/\- *lemma* ultrafilter.coe_comap
- \+ *lemma* ultrafilter.coe_pure
- \+ *lemma* ultrafilter.comap_comap
- \+ *lemma* ultrafilter.comap_id
- \+ *lemma* ultrafilter.comap_pure
- \- *lemma* ultrafilter.eq_principal_of_finite_mem
- \+ *lemma* ultrafilter.eq_pure_of_finite_mem
- \+ *lemma* ultrafilter.eq_pure_of_fintype
- \+ *lemma* ultrafilter.map_id'
- \+ *lemma* ultrafilter.map_id
- \+ *lemma* ultrafilter.map_map
- \+ *lemma* ultrafilter.map_pure
- \+ *lemma* ultrafilter.pure_injective



## [2022-07-09 19:44:03](https://github.com/leanprover-community/mathlib/commit/861589f)
feat(linear_algebra/unitary_group): better constructor ([#15209](https://github.com/leanprover-community/mathlib/pull/15209))
`A ∈ matrix.unitary_group n α` means by definition (for reasons of agreement with something more general) that `A * star A = 1` and `star A * A = 1`.  But either condition implies the other, so we provide a lemma to reduce to the first.
#### Estimated changes
Modified src/linear_algebra/unitary_group.lean
- \+ *lemma* matrix.mem_orthogonal_group_iff
- \+ *lemma* matrix.mem_unitary_group_iff



## [2022-07-09 16:05:22](https://github.com/leanprover-community/mathlib/commit/983fdd6)
chore(set_theory/ordinal/arithmetic): review cast API ([#14757](https://github.com/leanprover-community/mathlib/pull/14757))
This PR does the following:
- swap the direction of `nat_cast_succ` to match `nat.cast_succ`.
- make various arguments explicit.
- remove `lift_type_fin`, as it's a trivial consequence of `type_fin` and `lift_nat_cast`.
- tag various theorems as `norm_cast`.
- golf or otherwise cleanup various proofs.
#### Estimated changes
Modified src/set_theory/cardinal/cofinality.lean


Modified src/set_theory/ordinal/arithmetic.lean
- \+/\- *theorem* ordinal.add_le_add_iff_right
- \+/\- *theorem* ordinal.lift_nat_cast
- \- *theorem* ordinal.lift_type_fin
- \+/\- *theorem* ordinal.nat_cast_div
- \+/\- *theorem* ordinal.nat_cast_eq_zero
- \+/\- *theorem* ordinal.nat_cast_inj
- \+/\- *theorem* ordinal.nat_cast_le
- \+/\- *theorem* ordinal.nat_cast_lt
- \+/\- *theorem* ordinal.nat_cast_mod
- \+/\- *theorem* ordinal.nat_cast_mul
- \+/\- *theorem* ordinal.nat_cast_opow
- \+/\- *theorem* ordinal.nat_cast_pos
- \+/\- *theorem* ordinal.nat_cast_sub
- \+/\- *theorem* ordinal.nat_cast_succ

Modified src/set_theory/ordinal/notation.lean




## [2022-07-09 14:09:58](https://github.com/leanprover-community/mathlib/commit/6d245b2)
feat(set_theory/ordinal/basic): order type of naturals is `ω` ([#15178](https://github.com/leanprover-community/mathlib/pull/15178))
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean
- \+ *theorem* ordinal.type_nat_lt



## [2022-07-09 13:17:49](https://github.com/leanprover-community/mathlib/commit/7cf0ae6)
feat(combinatorics/simple_graph/subgraph): add `subgraph.comap` and subgraph of subgraph coercion ([#14877](https://github.com/leanprover-community/mathlib/pull/14877))
#### Estimated changes
Modified src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* simple_graph.subgraph.coe_subgraph_injective
- \+ *lemma* simple_graph.subgraph.comap_monotone
- \+ *lemma* simple_graph.subgraph.map_le_iff_le_comap
- \+ *lemma* simple_graph.subgraph.restrict_coe_subgraph



## [2022-07-09 07:26:23](https://github.com/leanprover-community/mathlib/commit/d3d3539)
Removed unnecessary assumption in `map_injective_of_injective` ([#15184](https://github.com/leanprover-community/mathlib/pull/15184))
Removed assumption in `map_injective_of_injective`
#### Estimated changes
Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/localization/basic.lean
- \+/\- *lemma* localization_algebra_injective



## [2022-07-09 04:08:50](https://github.com/leanprover-community/mathlib/commit/f26a0a3)
feat(logic/equiv/set): define `equiv.set.pi` ([#15176](https://github.com/leanprover-community/mathlib/pull/15176))
#### Estimated changes
Modified src/logic/equiv/set.lean




## [2022-07-09 01:15:44](https://github.com/leanprover-community/mathlib/commit/c5b6fe5)
feat(analysis/locally_convex/basic): a few lemmas about balanced sets ([#14876](https://github.com/leanprover-community/mathlib/pull/14876))
Add new lemmas about unions and intersection and membership of balanced sets.
#### Estimated changes
Modified src/analysis/locally_convex/basic.lean
- \+/\- *lemma* absorbs.add
- \+ *lemma* absorbs.neg
- \+ *lemma* absorbs.sub
- \+/\- *lemma* absorbs_Union_finset
- \+/\- *lemma* balanced.add
- \+ *lemma* balanced.mem_smul_iff
- \+ *lemma* balanced.neg
- \+ *lemma* balanced.neg_mem_iff
- \+/\- *lemma* balanced.smul
- \+ *lemma* balanced.sub
- \+ *lemma* balanced_Inter
- \+ *lemma* balanced_Inter₂
- \+ *lemma* balanced_Union
- \+ *lemma* balanced_Union₂
- \+ *lemma* balanced_empty
- \+/\- *lemma* balanced_univ
- \+/\- *lemma* set.finite.absorbs_Union



## [2022-07-08 22:50:34](https://github.com/leanprover-community/mathlib/commit/fefd449)
feat(set_theory/ordinal/arithmetic): tweak `type_add` and `type_mul` ([#15193](https://github.com/leanprover-community/mathlib/pull/15193))
This renames `type_mul` to the more accurate `type_prod_lex`, and renames `type_add` to `type_sum_lex` and reverses the order of the equality so that the two lemmas match.
#### Estimated changes
Modified src/set_theory/ordinal/arithmetic.lean
- \- *theorem* ordinal.type_mul
- \+ *theorem* ordinal.type_prod_lex

Modified src/set_theory/ordinal/basic.lean
- \- *theorem* ordinal.type_add
- \+ *theorem* ordinal.type_sum_lex



## [2022-07-08 20:54:25](https://github.com/leanprover-community/mathlib/commit/f39bd5f)
feat(analysis/normed_space/star/basic): make starₗᵢ apply to normed star groups ([#15173](https://github.com/leanprover-community/mathlib/pull/15173))
#### Estimated changes
Modified src/analysis/normed_space/star/basic.lean




## [2022-07-08 20:54:25](https://github.com/leanprover-community/mathlib/commit/8a38a69)
feat(combinatorics/simple_graph/hasse): The Hasse diagram of `α × β` ([#14978](https://github.com/leanprover-community/mathlib/pull/14978))
... is the box product of the Hasse diagrams of `α` and `β`.
#### Estimated changes
Modified src/combinatorics/simple_graph/hasse.lean
- \+ *lemma* simple_graph.hasse_prod

Modified src/combinatorics/simple_graph/prod.lean
- \+/\- *lemma* simple_graph.box_prod_adj



## [2022-07-08 20:54:24](https://github.com/leanprover-community/mathlib/commit/1a54e4d)
feat(combinatorics/additive/ruzsa_covering): The Ruzsa covering lemma ([#14697](https://github.com/leanprover-community/mathlib/pull/14697))
Prove the Ruzsa covering lemma, which says that a finset `s` can be covered using at most $\frac{|s + t|}{|t|}$ copies of `t - t`.
#### Estimated changes
Added src/combinatorics/additive/ruzsa_covering.lean
- \+ *lemma* finset.exists_subset_mul_div



## [2022-07-08 18:50:17](https://github.com/leanprover-community/mathlib/commit/2d5b45c)
chore(data/zmod/defs): shuffle files around ([#15142](https://github.com/leanprover-community/mathlib/pull/15142))
This is to prepare to fix `char_p` related diamonds. No new lemmas were added, stuff was just moved around.
#### Estimated changes
Modified src/algebra/char_p/basic.lean


Modified src/algebra/ne_zero.lean


Modified src/data/zmod/basic.lean
- \- *lemma* zmod.card
- \- *def* zmod

Added src/data/zmod/defs.lean
- \+ *lemma* zmod.card
- \+ *def* zmod

Modified src/data/zmod/quotient.lean


Modified src/ring_theory/roots_of_unity.lean




## [2022-07-08 18:50:16](https://github.com/leanprover-community/mathlib/commit/11cdccb)
feat(data/rat/defs): add denominator as pnat ([#15101](https://github.com/leanprover-community/mathlib/pull/15101))
Option to bundle `x.denom` and `x.pos` into a pnat, which can be useful in defining functions using the denominator.
#### Estimated changes
Modified src/data/rat/defs.lean
- \+ *lemma* rat.coe_pnat_denom
- \+ *lemma* rat.mk_pnat_pnat_denom_eq
- \+ *def* rat.pnat_denom
- \+ *lemma* rat.pnat_denom_eq_iff_denom_eq



## [2022-07-08 17:45:40](https://github.com/leanprover-community/mathlib/commit/feb34df)
chore(data/nat/squarefree): fix a tactic doc typo for norm num extension ([#15189](https://github.com/leanprover-community/mathlib/pull/15189))
#### Estimated changes
Modified src/data/nat/squarefree.lean




## [2022-07-08 14:49:24](https://github.com/leanprover-community/mathlib/commit/5a5d290)
fix(data/fintype/basic): move card_subtype_mono into the fintype namespace ([#15185](https://github.com/leanprover-community/mathlib/pull/15185))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \- *theorem* card_subtype_mono
- \+ *theorem* fintype.card_subtype_mono



## [2022-07-08 13:36:19](https://github.com/leanprover-community/mathlib/commit/1937dff)
feat(analysis/normed_space/lp_space): normed_algebra structure ([#15086](https://github.com/leanprover-community/mathlib/pull/15086))
This also golfs the `normed_ring` instance to go via `subring.to_ring`, as this saves us from having to build the power, nat_cast, and int_cast structures manually.
We also rename `lp.lp_submodule` to `lp_submodule` to avoid unhelpful repetition.
#### Estimated changes
Modified src/analysis/normed_space/lp_space.lean
- \+ *lemma* algebra_map_mem_ℓp_infty
- \- *def* lp.lp_submodule
- \+ *def* lp_infty_subalgebra
- \+ *def* lp_infty_subring
- \+ *def* lp_submodule
- \+/\- *lemma* nat_cast_mem_ℓp_infty



## [2022-07-08 11:29:27](https://github.com/leanprover-community/mathlib/commit/e74e534)
doc(tactic/wlog): use markdown lists rather than indentation ([#15113](https://github.com/leanprover-community/mathlib/pull/15113))
The indentation used in this docstring was lost in the web docs.
#### Estimated changes
Modified src/tactic/wlog.lean




## [2022-07-08 11:29:26](https://github.com/leanprover-community/mathlib/commit/0bc51f0)
feat(topology/metric_space/hausdorff_distance): Thickening a compact inside an open ([#14926](https://github.com/leanprover-community/mathlib/pull/14926))
If a compact set is contained in an open set, then we can find a (closed) thickening of it still contained in the open.
#### Estimated changes
Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* is_compact.exists_cthickening_subset_open
- \+ *lemma* is_compact.exists_thickening_subset_open



## [2022-07-08 11:29:25](https://github.com/leanprover-community/mathlib/commit/93be74b)
feat(combinatorics/simple_graph/prod): Box product ([#14867](https://github.com/leanprover-community/mathlib/pull/14867))
Define `simple_graph.box_prod`, the box product of simple graphs. Show that it's commutative and associative, and prove its connectivity properties.
#### Estimated changes
Modified src/combinatorics/simple_graph/connectivity.lean


Added src/combinatorics/simple_graph/prod.lean
- \+ *def* simple_graph.box_prod
- \+ *lemma* simple_graph.box_prod_adj
- \+ *lemma* simple_graph.box_prod_adj_left
- \+ *lemma* simple_graph.box_prod_adj_right
- \+ *def* simple_graph.box_prod_assoc
- \+ *def* simple_graph.box_prod_comm
- \+ *lemma* simple_graph.box_prod_connected
- \+ *def* simple_graph.box_prod_left
- \+ *def* simple_graph.box_prod_right
- \+ *def* simple_graph.walk.of_box_prod_left
- \+ *lemma* simple_graph.walk.of_box_prod_left_box_prod_left
- \+ *lemma* simple_graph.walk.of_box_prod_left_box_prod_right
- \+ *def* simple_graph.walk.of_box_prod_right



## [2022-07-08 09:53:26](https://github.com/leanprover-community/mathlib/commit/7c070c4)
feat(data/finset/basic): Coercion of a product of finsets ([#15011](https://github.com/leanprover-community/mathlib/pull/15011))
`↑(∏ i in s, f i) : set α) = ∏ i in s, ↑(f i)` for `f : ι → finset α`.
#### Estimated changes
Modified src/data/finset/pointwise.lean
- \+ *lemma* finset.coe_coe_monoid_hom
- \+ *def* finset.coe_monoid_hom
- \+ *lemma* finset.coe_monoid_hom_apply
- \+/\- *lemma* finset.coe_pow
- \+ *lemma* finset.coe_prod

Modified src/data/polynomial/ring_division.lean




## [2022-07-08 05:24:53](https://github.com/leanprover-community/mathlib/commit/d34b330)
feat(data/set/basic,order/filter/basic): add semiconj lemmas about images and maps ([#14970](https://github.com/leanprover-community/mathlib/pull/14970))
This adds `function.commute` and `function.semiconj` lemmas, and replaces all the uses of `_comm` lemmas with the `semiconj` version as it turns out that only this generality is needed.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* function.commute.finset_image
- \+ *lemma* function.commute.finset_map
- \+ *lemma* function.semiconj.finset_image
- \+ *lemma* function.semiconj.finset_map

Modified src/data/finset/pointwise.lean


Modified src/data/set/basic.lean
- \+ *lemma* function.commute.set_image
- \+ *lemma* function.semiconj.set_image

Modified src/data/set/pointwise.lean
- \+/\- *lemma* set.image_op_inv

Modified src/order/filter/basic.lean
- \+ *lemma* commute.filter_comap
- \+ *lemma* commute.filter_map
- \+ *lemma* function.semiconj.filter_comap
- \+ *lemma* function.semiconj.filter_map

Modified src/order/filter/pointwise.lean
- \+/\- *lemma* filter.map_inv'

Modified src/topology/algebra/field.lean




## [2022-07-08 05:24:52](https://github.com/leanprover-community/mathlib/commit/563a51a)
chore(topology/algebra/semigroup): golf file ([#14957](https://github.com/leanprover-community/mathlib/pull/14957))
#### Estimated changes
Modified src/topology/algebra/semigroup.lean




## [2022-07-08 05:24:52](https://github.com/leanprover-community/mathlib/commit/ba9f346)
feat(topology/algebra/uniform_group): `uniform_group` is preserved by Inf and comap ([#14889](https://github.com/leanprover-community/mathlib/pull/14889))
This is the uniform version of [#11720](https://github.com/leanprover-community/mathlib/pull/11720)
#### Estimated changes
Modified src/topology/algebra/uniform_group.lean
- \+ *lemma* uniform_group_Inf
- \+ *lemma* uniform_group_comap
- \+ *lemma* uniform_group_inf
- \+ *lemma* uniform_group_infi

Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* uniform_continuous_iff



## [2022-07-08 02:55:33](https://github.com/leanprover-community/mathlib/commit/6eeb941)
refactor(set_theory/cardinal/basic): migrate from `fintype` to `finite` ([#15175](https://github.com/leanprover-community/mathlib/pull/15175))
* add `finite_iff_exists_equiv_fin`;
* add `cardinal.mk_eq_nat_iff` and `cardinal.lt_aleph_0_iff_finite`;
* rename the old `cardinal.lt_aleph_0_iff_finite` to `cardinal.lt_aleph_0_iff_finite_set`;
* rename `cardinal.lt_aleph_0_of_fintype` to `cardinal.lt_aleph_0_of_finite`, assume `[finite]` instead of `[fintype]`;
* add an alias `set.finite.lt_aleph_0`;
* rename `W_type.cardinal_mk_le_max_aleph_0_of_fintype` to `W_type.cardinal_mk_le_max_aleph_0_of_finite`, fix assumption.
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified src/data/W/cardinal.lean
- \+ *lemma* W_type.cardinal_mk_le_max_aleph_0_of_finite
- \- *lemma* W_type.cardinal_mk_le_max_aleph_0_of_fintype

Modified src/data/finite/basic.lean
- \+ *lemma* finite_iff_exists_equiv_fin

Modified src/data/mv_polynomial/cardinal.lean


Modified src/data/polynomial/cardinal.lean


Modified src/field_theory/finiteness.lean


Modified src/field_theory/is_alg_closed/classification.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/set_theory/cardinal/basic.lean
- \+/\- *theorem* cardinal.lt_aleph_0_iff_finite
- \+ *theorem* cardinal.lt_aleph_0_iff_set_finite
- \+ *theorem* cardinal.lt_aleph_0_of_finite
- \- *theorem* cardinal.lt_aleph_0_of_fintype
- \+ *theorem* cardinal.mk_eq_nat_iff

Modified src/set_theory/game/short.lean




## [2022-07-08 02:55:32](https://github.com/leanprover-community/mathlib/commit/a3c647b)
feat(set_theory/ordinal/arithmetic): tweak theorems about `0` and `1` ([#15174](https://github.com/leanprover-community/mathlib/pull/15174))
We add a few basic theorems on the `0` and `1` ordinals. We rename `one_eq_type_unit` to `type_unit`, and remove `one_eq_lift_type_unit` by virtue of being a trivial consequence of `type_unit` and `lift_one`.
#### Estimated changes
Modified src/set_theory/ordinal/arithmetic.lean


Modified src/set_theory/ordinal/basic.lean
- \+/\- *theorem* ordinal.lift_one
- \+/\- *theorem* ordinal.lift_zero
- \- *theorem* ordinal.one_eq_lift_type_unit
- \- *theorem* ordinal.one_eq_type_unit
- \+ *theorem* ordinal.type_empty
- \+ *theorem* ordinal.type_eq_one_iff_unique
- \+ *theorem* ordinal.type_eq_one_of_unique
- \+ *theorem* ordinal.type_pempty
- \+ *theorem* ordinal.type_punit
- \+ *theorem* ordinal.type_unit



## [2022-07-08 02:55:31](https://github.com/leanprover-community/mathlib/commit/f0f4070)
feat(topology/algebra/infinite_sum): Double sum is equal to a single value ([#15157](https://github.com/leanprover-community/mathlib/pull/15157))
A generalized version of `tsum_eq_single` that works for a double indexed sum, when all but one summand is zero.
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* tsum_tsum_eq_single



## [2022-07-08 02:55:30](https://github.com/leanprover-community/mathlib/commit/8927a02)
chore(tactic/lift): move a proof to `subtype.exists_pi_extension` ([#15098](https://github.com/leanprover-community/mathlib/pull/15098))
* Move `_can_lift` attr to the bottom of the file, just before the
  rest of meta code.
* Use `ι → Sort*` instead of `Π i : ι, Sort*`.
* Move `pi_subtype.can_lift.prf` to a separate lemma.
#### Estimated changes
Modified src/tactic/lift.lean
- \+ *lemma* subtype.exists_pi_extension



## [2022-07-08 02:55:29](https://github.com/leanprover-community/mathlib/commit/0e3184f)
feat(data/fin/tuple/basic): add lemmas for rewriting exists and forall over `n+1`-tuples ([#15048](https://github.com/leanprover-community/mathlib/pull/15048))
The lemma names `fin.forall_fin_succ_pi` and `fin.exists_fin_succ_pi` mirror the existing `fin.forall_fin_succ` and `fin.exists_fin_succ`.
#### Estimated changes
Modified src/data/fin/tuple/basic.lean
- \+ *lemma* fin.exists_fin_succ_pi
- \+ *lemma* fin.exists_fin_zero_pi
- \+ *lemma* fin.forall_fin_succ_pi
- \+ *lemma* fin.forall_fin_zero_pi



## [2022-07-08 02:55:28](https://github.com/leanprover-community/mathlib/commit/2a7ceb0)
perf(linear_algebra): speed up `graded_algebra` instances ([#14967](https://github.com/leanprover-community/mathlib/pull/14967))
Reduce `elaboration of graded_algebra` in:
+ `exterior_algebra.graded_algebra` from ~20s to 3s-
+ `tensor_algebra.graded_algebra` from 7s+ to 2s-
+ `clifford_algebra.graded_algebra` from 14s+ to 4s-
(These numbers were before `lift_ι` and `lift_ι_eq` were extracted from `exterior_algebra.graded_algebra` and `lift_ι_eq` was extracted from `clifford_algebra.graded_algebra` in [#12182](https://github.com/leanprover-community/mathlib/pull/12182).)
Fix [timeout reported on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/deterministic.20timeout/near/286996731)
Also shorten the statements of the first two without reducing clarity (I think).
#### Estimated changes
Modified src/linear_algebra/clifford_algebra/grading.lean


Modified src/linear_algebra/exterior_algebra/grading.lean


Modified src/linear_algebra/tensor_algebra/grading.lean




## [2022-07-08 02:55:27](https://github.com/leanprover-community/mathlib/commit/a5a6865)
feat(combinatorics/set_family/intersecting): Intersecting families ([#14475](https://github.com/leanprover-community/mathlib/pull/14475))
Define intersecting families, prove that intersecting families in `α` have size at most `card α / 2` and that all maximal intersecting families are this size.
#### Estimated changes
Modified docs/references.bib


Added src/combinatorics/set_family/intersecting.lean
- \+ *lemma* set.intersecting.card_le
- \+ *lemma* set.intersecting.exists_card_eq
- \+ *lemma* set.intersecting.exists_mem_finset
- \+ *lemma* set.intersecting.exists_mem_set
- \+ *lemma* set.intersecting.insert
- \+ *lemma* set.intersecting.is_max_iff_card_eq
- \+ *lemma* set.intersecting.is_upper_set'
- \+ *lemma* set.intersecting.mono
- \+ *lemma* set.intersecting.ne_bot
- \+ *lemma* set.intersecting.not_bot_mem
- \+ *lemma* set.intersecting.not_compl_mem
- \+ *lemma* set.intersecting.not_mem
- \+ *def* set.intersecting
- \+ *lemma* set.intersecting_empty
- \+ *lemma* set.intersecting_iff_eq_empty_of_subsingleton
- \+ *lemma* set.intersecting_iff_pairwise_not_disjoint
- \+ *lemma* set.intersecting_insert
- \+ *lemma* set.intersecting_singleton

Modified src/order/upper_lower.lean
- \+ *lemma* is_lower_set.bot_mem
- \+ *lemma* is_lower_set.not_bot_mem
- \+ *lemma* is_lower_set.top_mem
- \+ *lemma* is_upper_set.bot_mem
- \+ *lemma* is_upper_set.not_top_mem
- \+ *lemma* is_upper_set.top_mem



## [2022-07-08 02:55:26](https://github.com/leanprover-community/mathlib/commit/70a2708)
feat(topology/continuous_function): Any T0 space embeds in a product of copies of the Sierpinski space ([#14036](https://github.com/leanprover-community/mathlib/pull/14036))
Any T0 space embeds in a product of copies of the Sierpinski space
#### Estimated changes
Added src/topology/continuous_function/t0_sierpinski.lean
- \+ *lemma* topological_space.eq_induced_by_maps_to_sierpinski
- \+ *def* topological_space.product_of_mem_opens
- \+ *theorem* topological_space.product_of_mem_opens_embedding
- \+ *lemma* topological_space.product_of_mem_opens_inducing
- \+ *lemma* topological_space.product_of_mem_opens_injective

Modified src/topology/sets/opens.lean
- \+ *lemma* topological_space.opens.mem_mk



## [2022-07-08 00:21:19](https://github.com/leanprover-community/mathlib/commit/646028a)
refactor(data/finset/lattice): finset.{min,max} away from option ([#15163](https://github.com/leanprover-community/mathlib/pull/15163))
Switch to a `with_top`/`with_bot` based API. This avoids exposing `option`
as implementation detail.
Redefines `polynomial.degree` to use `coe` instead of `some`
#### Estimated changes
Modified archive/100-theorems-list/73_ascending_descending_sequences.lean


Modified src/combinatorics/simple_graph/basic.lean


Modified src/data/finset/lattice.lean
- \+/\- *theorem* finset.le_max'
- \+/\- *theorem* finset.le_max_of_mem
- \+/\- *theorem* finset.max_empty
- \+ *theorem* finset.max_eq_bot
- \- *theorem* finset.max_eq_none
- \+/\- *theorem* finset.max_of_mem
- \+/\- *theorem* finset.max_of_nonempty
- \+/\- *theorem* finset.max_singleton
- \+/\- *theorem* finset.mem_of_max
- \+/\- *theorem* finset.mem_of_min
- \+/\- *theorem* finset.min'_le
- \+/\- *theorem* finset.min_empty
- \- *theorem* finset.min_eq_none
- \+ *theorem* finset.min_eq_top
- \+/\- *theorem* finset.min_le_of_mem
- \+/\- *theorem* finset.min_of_mem
- \+/\- *theorem* finset.min_of_nonempty
- \+/\- *theorem* finset.min_singleton

Modified src/data/mv_polynomial/equiv.lean


Modified src/data/polynomial/degree/definitions.lean
- \+/\- *def* polynomial.degree

Modified src/data/polynomial/degree/trailing_degree.lean


Modified src/order/bounded_order.lean
- \+ *lemma* with_bot.rec_bot_coe_bot
- \+ *lemma* with_bot.rec_bot_coe_coe
- \+ *def* with_bot.unbot'
- \+ *lemma* with_bot.unbot'_bot
- \+ *lemma* with_bot.unbot'_coe
- \+ *lemma* with_top.rec_top_coe_coe
- \+ *lemma* with_top.rec_top_coe_top
- \+ *def* with_top.untop'
- \+ *lemma* with_top.untop'_coe
- \+ *lemma* with_top.untop'_top

Modified src/ring_theory/polynomial/basic.lean




## [2022-07-07 22:47:30](https://github.com/leanprover-community/mathlib/commit/8a80759)
feat(order/filter/basic): add `map_le_map` and `map_injective` ([#15128](https://github.com/leanprover-community/mathlib/pull/15128))
* Add `filter.map_le_map`, an `iff` version of `filter.map_mono`.
* Add `filter.map_injective`, a `function.injective` version of `filter.map_inj`.
#### Estimated changes
Modified src/order/filter/basic.lean
- \- *lemma* filter.eq_of_map_eq_map_inj'
- \- *lemma* filter.le_of_map_le_map_inj'
- \- *lemma* filter.le_of_map_le_map_inj_iff
- \+ *lemma* filter.map_eq_map_iff_of_inj_on
- \+/\- *lemma* filter.map_inj
- \+ *lemma* filter.map_injective
- \+ *lemma* filter.map_le_map_iff
- \+ *lemma* filter.map_le_map_iff_of_inj_on



## [2022-07-07 19:22:46](https://github.com/leanprover-community/mathlib/commit/b4979cb)
chore(data/rat): split `field ℚ` instance from definition of `ℚ` ([#14893](https://github.com/leanprover-community/mathlib/pull/14893))
I want to refer to the rational numbers in the definition of a field, meaning we can't define the field structure on `ℚ` in the same file as `ℚ` itself.
This PR moves everything in `data/rat/basic.lean` that does not depend on `algebra/field/basic.lean` into a new file `data/rat/defs.lean`: definition of the type `ℚ`, the operations giving its algebraic structure, and the coercions from integers and natural numbers. Basically, everything except the actual `field ℚ` instance.
It turns out our basic lemmas on rational numbers only require a `comm_ring`, `comm_group_with_zero` and `is_domain` instance, so I defined those instances in `defs.lean` could leave all lemmas intact.
As a consequence, the transitive imports provided by `data.rat.basic` are somewhat smaller: no `linear_ordered_field` is needed until `data.rat.order`. I see this as a bonus but can also re-import `algebra.order.field` in `data.rat.basic` if desired.
#### Estimated changes
Modified counterexamples/pseudoelement.lean


Modified src/algebra/field/basic.lean


Added src/data/rat/basic.lean


Modified src/data/rat/defs.lean


Modified src/data/rat/order.lean


Modified src/number_theory/number_field.lean


Modified test/rat.lean




## [2022-07-07 16:57:16](https://github.com/leanprover-community/mathlib/commit/7428bd9)
refactor(data/finite/set,data/set/finite): move most contents of one file to another ([#15166](https://github.com/leanprover-community/mathlib/pull/15166))
* move most content of `data.finite.set` to `data.set.finite`;
* use `casesI nonempty_fintype _` instead of `letI := fintype.of_finite`; sometimes it lets us avoid `classical.choice`;
* merge `set.finite.of_fintype`, `set.finite_of_fintype`, and `set.finite_of_finite` into `set.to_finite`;
* rewrite `set.finite_univ_iff` and `finite.of_finite_univ` in terms of `set.finite`;
* replace some assumptions `[fintype (plift _)]` with `[finite _]`;
* generalize `set.cod_restrict` and some lemmas to allow domain in `Sort*`, use it for `finite.of_injective_finite.range`.
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified src/algebra/big_operators/finprod.lean


Modified src/analysis/box_integral/partition/measure.lean


Modified src/data/finite/basic.lean
- \+/\- *def* fintype.of_finite
- \+ *lemma* nonempty_fintype

Modified src/data/finite/set.lean
- \- *lemma* finite.of_finite_univ
- \+/\- *lemma* finite.of_injective_finite_range
- \- *lemma* finite.set.finite_bUnion
- \- *lemma* set.finite_iff_finite
- \- *theorem* set.finite_of_finite
- \- *lemma* set.finite_univ_iff

Modified src/data/polynomial/ring_division.lean


Modified src/data/set/finite.lean
- \+ *lemma* finite.set.finite_bUnion
- \+/\- *lemma* finset.finite_to_set
- \- *theorem* set.finite.of_fintype
- \+/\- *lemma* set.finite.of_subsingleton
- \+/\- *theorem* set.finite_Union
- \+ *lemma* set.finite_coe_iff
- \+/\- *theorem* set.finite_empty
- \+/\- *lemma* set.finite_le_nat
- \+/\- *lemma* set.finite_lt_nat
- \+/\- *theorem* set.finite_mem_finset
- \- *theorem* set.finite_of_fintype
- \+/\- *theorem* set.finite_pure
- \+/\- *theorem* set.finite_range
- \+/\- *theorem* set.finite_singleton
- \+/\- *theorem* set.finite_univ
- \+ *theorem* set.finite_univ_iff
- \+ *theorem* set.to_finite

Modified src/data/set/function.lean
- \+/\- *def* set.cod_restrict
- \+/\- *lemma* set.coe_cod_restrict_apply
- \+/\- *lemma* set.injective_cod_restrict
- \+/\- *lemma* set.restrict_comp_cod_restrict

Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/matrix/diagonal.lean


Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/integral/divergence_theorem.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/measure_theory/probability_mass_function/basic.lean


Modified src/order/atoms.lean


Modified src/order/compactly_generated.lean


Modified src/order/locally_finite.lean
- \+/\- *lemma* set.finite_Icc
- \+/\- *lemma* set.finite_Ici
- \+/\- *lemma* set.finite_Ico
- \+/\- *lemma* set.finite_Iic
- \+/\- *lemma* set.finite_Iio
- \+/\- *lemma* set.finite_Ioc
- \+/\- *lemma* set.finite_Ioi
- \+/\- *lemma* set.finite_Ioo

Modified src/order/well_founded_set.lean
- \+/\- *theorem* set.fintype.is_pwo

Modified src/set_theory/cardinal/ordinal.lean


Modified src/topology/algebra/const_mul_action.lean


Modified src/topology/algebra/order/basic.lean


Modified src/topology/basic.lean


Modified src/topology/separation.lean




## [2022-07-07 16:57:15](https://github.com/leanprover-community/mathlib/commit/691f04f)
feat(order/rel_iso): two reflexive/irreflexive relations on a unique type are isomorphic ([#14760](https://github.com/leanprover-community/mathlib/pull/14760))
We also rename `not_rel` to the more descriptive name `not_rel_of_subsingleton`.
#### Estimated changes
Modified src/order/rel_classes.lean
- \- *lemma* not_rel
- \+ *lemma* not_rel_of_subsingleton
- \+ *lemma* rel_of_subsingleton

Modified src/order/rel_iso.lean
- \+ *def* rel_iso.rel_iso_of_unique_of_irrefl
- \+ *def* rel_iso.rel_iso_of_unique_of_refl



## [2022-07-07 14:49:11](https://github.com/leanprover-community/mathlib/commit/6df59d6)
feat(data/list/basic): nth_le_enum ([#15139](https://github.com/leanprover-community/mathlib/pull/15139))
Fill out some of the `enum` and `enum_from` API
Link the two via `map_fst_add_enum_eq_enum_from`.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.enum_append
- \+ *lemma* list.enum_cons
- \+ *lemma* list.enum_from_append
- \+ *lemma* list.enum_from_cons
- \+ *lemma* list.enum_from_nil
- \+ *lemma* list.enum_from_singleton
- \+ *lemma* list.enum_nil
- \+ *lemma* list.enum_singleton
- \+ *lemma* list.map_fst_add_enum_eq_enum_from
- \+ *lemma* list.map_fst_add_enum_from_eq_enum_from
- \+ *lemma* list.nth_le_enum
- \+ *lemma* list.nth_le_enum_from



## [2022-07-07 13:45:33](https://github.com/leanprover-community/mathlib/commit/5852568)
feat(combinatorics/simple_graph/{basic,subgraph,clique,coloring}): add induced graphs, characterization of cliques, and bounds for colorings ([#14034](https://github.com/leanprover-community/mathlib/pull/14034))
This adds `simple_graph.map`, `simple_graph.comap`, and induced graphs and subgraphs. There are renamings: `simple_graph.subgraph.map` to `simple_graph.subgraph.inclusion`, `simple_graph.subgraph.map_top` to `simple_graph.subgraph.hom`, and `simple_graph.subgraph.map_spanning_top` to `simple_graph.subgraph.spanning_hom`. These changes originated to be able to express that a clique is a set of vertices whose induced subgraph is complete, which gives some clique-based bounds for chromatic numbers.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* simple_graph.comap_map_eq
- \+ *lemma* simple_graph.comap_monotone
- \+ *lemma* simple_graph.comap_surjective
- \+ *lemma* simple_graph.hom.injective_of_top_hom
- \+ *def* simple_graph.induce
- \+ *lemma* simple_graph.induce_spanning_coe
- \+ *lemma* simple_graph.iso.to_embedding_complete_graph
- \+ *lemma* simple_graph.left_inverse_comap_map
- \+ *lemma* simple_graph.map_adj
- \+ *lemma* simple_graph.map_comap_le
- \+ *lemma* simple_graph.map_injective
- \+ *lemma* simple_graph.map_le_iff_le_comap
- \+ *lemma* simple_graph.map_monotone
- \+ *def* simple_graph.spanning_coe
- \+ *lemma* simple_graph.spanning_coe_induce_le

Modified src/combinatorics/simple_graph/clique.lean
- \+ *lemma* simple_graph.clique_free_iff
- \+ *lemma* simple_graph.clique_free_of_card_lt
- \+ *lemma* simple_graph.is_clique_iff_induce_eq
- \+ *lemma* simple_graph.not_clique_free_card_of_top_embedding
- \+ *lemma* simple_graph.not_clique_free_iff
- \+ *lemma* simple_graph.not_clique_free_of_top_embedding
- \+ *def* simple_graph.top_embedding_of_not_clique_free

Modified src/combinatorics/simple_graph/coloring.lean
- \+ *lemma* simple_graph.clique_free_of_chromatic_number_lt
- \+ *lemma* simple_graph.colorable.clique_free
- \+ *lemma* simple_graph.is_clique.card_le_chromatic_number
- \+ *lemma* simple_graph.is_clique.card_le_of_colorable
- \+ *lemma* simple_graph.is_clique.card_le_of_coloring

Modified src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* simple_graph.induce_eq_coe_induce_top
- \+ *lemma* simple_graph.subgraph.hom.injective
- \+ *lemma* simple_graph.subgraph.inclusion.injective
- \+ *def* simple_graph.subgraph.inclusion
- \+ *def* simple_graph.subgraph.induce
- \+ *lemma* simple_graph.subgraph.induce_empty
- \+ *lemma* simple_graph.subgraph.induce_mono
- \+ *lemma* simple_graph.subgraph.induce_mono_left
- \+ *lemma* simple_graph.subgraph.induce_mono_right
- \- *lemma* simple_graph.subgraph.map.injective
- \- *def* simple_graph.subgraph.map
- \+ *lemma* simple_graph.subgraph.map_monotone
- \- *lemma* simple_graph.subgraph.map_spanning_top.injective
- \- *def* simple_graph.subgraph.map_spanning_top
- \- *lemma* simple_graph.subgraph.map_top.injective
- \- *def* simple_graph.subgraph.map_top
- \- *lemma* simple_graph.subgraph.map_top_to_fun
- \+ *lemma* simple_graph.subgraph.spanning_hom.injective
- \+ *def* simple_graph.subgraph.spanning_hom



## [2022-07-07 08:40:00](https://github.com/leanprover-community/mathlib/commit/1422d38)
feat(order/succ_pred): expand API on `with_bot` and `with_top` ([#15016](https://github.com/leanprover-community/mathlib/pull/15016))
We add a bunch of `simp` lemmas for successor and predecessors on `with_bot` and `with_top`, and golf some proofs.
#### Estimated changes
Modified src/order/succ_pred/basic.lean
- \+ *lemma* with_bot.pred_coe
- \+ *lemma* with_bot.pred_coe_bot
- \+ *lemma* with_bot.pred_coe_of_ne_bot
- \+ *lemma* with_bot.succ_bot
- \+ *lemma* with_bot.succ_coe
- \+ *lemma* with_top.pred_coe
- \+ *lemma* with_top.pred_top
- \+ *lemma* with_top.succ_coe
- \+ *lemma* with_top.succ_coe_of_ne_top
- \+ *lemma* with_top.succ_coe_top



## [2022-07-07 06:45:03](https://github.com/leanprover-community/mathlib/commit/0d18630)
chore(ring_theory/norm): generalise a couple of lemmas ([#15160](https://github.com/leanprover-community/mathlib/pull/15160))
Using the generalisation linter
#### Estimated changes
Modified src/ring_theory/norm.lean
- \+/\- *lemma* algebra.norm_eq_prod_embeddings_gen
- \+/\- *lemma* algebra.norm_eq_zero_iff'
- \+/\- *lemma* algebra.norm_eq_zero_iff
- \+/\- *lemma* algebra.prod_embeddings_eq_finrank_pow



## [2022-07-07 05:04:33](https://github.com/leanprover-community/mathlib/commit/bf735cd)
chore(set_theory/ordinal/basic): remove `rel_iso_out` ([#15145](https://github.com/leanprover-community/mathlib/pull/15145))
This is just a specific application of `rel_iso.cast`. Moreover, it's unused.
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean
- \- *def* ordinal.rel_iso_out



## [2022-07-07 05:04:32](https://github.com/leanprover-community/mathlib/commit/9b2755b)
chore(*): add missing `to_fun → apply` configurations for `simps` ([#15112](https://github.com/leanprover-community/mathlib/pull/15112))
This improves the names of some generated lemmas for `continuous_map` and `quadratic_form`.
#### Estimated changes
Modified src/analysis/fourier.lean


Modified src/linear_algebra/quadratic_form/basic.lean


Modified src/linear_algebra/quadratic_form/prod.lean


Modified src/order/hom/bounded.lean


Modified src/topology/continuous_function/basic.lean


Modified src/topology/continuous_function/polynomial.lean


Modified src/topology/continuous_function/stone_weierstrass.lean


Modified src/topology/gluing.lean




## [2022-07-07 05:04:31](https://github.com/leanprover-community/mathlib/commit/ab99fd1)
chore(data/nat): rename oddly named lemma odd_gt_zero ([#13040](https://github.com/leanprover-community/mathlib/pull/13040))
#### Estimated changes
Modified archive/imo/imo1998_q2.lean


Modified src/data/nat/parity.lean
- \- *lemma* nat.odd_gt_zero
- \+ *lemma* nat.pos_of_odd



## [2022-07-07 02:38:11](https://github.com/leanprover-community/mathlib/commit/6d02dac)
feat(order/lattice, order/lattice_intervals): coe inf/sup lemmas ([#15136](https://github.com/leanprover-community/mathlib/pull/15136))
This PR adds simp lemmas for coercions of inf/sup in order instances on intervals. We also change the order of some arguments in instances/lemmas, by removing `variables` commands, so that typeclass arguments precede others.
#### Estimated changes
Modified src/order/lattice.lean
- \+ *lemma* subtype.coe_inf
- \+ *lemma* subtype.coe_sup
- \+ *lemma* subtype.mk_inf_mk
- \+ *lemma* subtype.mk_sup_mk

Modified src/order/lattice_intervals.lean




## [2022-07-07 00:12:50](https://github.com/leanprover-community/mathlib/commit/418373e)
feat(combinatorics/simple_graph/basic): `dart.to_prod` is injective ([#15150](https://github.com/leanprover-community/mathlib/pull/15150))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* simple_graph.dart.to_prod_injective



## [2022-07-07 00:12:49](https://github.com/leanprover-community/mathlib/commit/3e52000)
feat(data/quot): `is_equiv` instance for quotient equivalence ([#15148](https://github.com/leanprover-community/mathlib/pull/15148))
#### Estimated changes
Modified src/data/quot.lean




## [2022-07-07 00:12:47](https://github.com/leanprover-community/mathlib/commit/e034eb0)
feat(order/rel_iso): add `rel_iso.cast` ([#15144](https://github.com/leanprover-community/mathlib/pull/15144))
#### Estimated changes
Modified src/order/rel_iso.lean




## [2022-07-07 00:12:46](https://github.com/leanprover-community/mathlib/commit/e335a41)
refactor(group_theory/congruence): use `quotient.map` ([#15130](https://github.com/leanprover-community/mathlib/pull/15130))
Also add explicit universe levels in `algebra.category.Module.monoidal`.
#### Estimated changes
Modified src/algebra/category/Module/monoidal.lean
- \+/\- *def* Module.monoidal_category.associator
- \+/\- *lemma* Module.monoidal_category.tensor_id

Modified src/group_theory/congruence.lean


Modified src/group_theory/quotient_group.lean




## [2022-07-07 00:12:45](https://github.com/leanprover-community/mathlib/commit/fdfc222)
feat(measure_theory/integral): Circle integral transform ([#13885](https://github.com/leanprover-community/mathlib/pull/13885))
Some basic definitions and results related to circle integrals of a function. These form part of [#13500](https://github.com/leanprover-community/mathlib/pull/13500)
#### Estimated changes
Modified src/measure_theory/integral/circle_integral.lean
- \+ *lemma* continuous_circle_map_inv

Added src/measure_theory/integral/circle_integral_transform.lean
- \+ *lemma* complex.abs_circle_transform_bounding_function_le
- \+ *def* complex.circle_transform
- \+ *def* complex.circle_transform_bounding_function
- \+ *def* complex.circle_transform_deriv
- \+ *lemma* complex.circle_transform_deriv_bound
- \+ *lemma* complex.circle_transform_deriv_eq
- \+ *lemma* complex.circle_transform_deriv_periodic
- \+ *lemma* complex.continuous_circle_transform
- \+ *lemma* complex.continuous_circle_transform_deriv
- \+ *lemma* complex.continuous_on_abs_circle_transform_bounding_function
- \+ *lemma* complex.continuous_on_prod_circle_transform_function
- \+ *lemma* complex.integral_circle_transform



## [2022-07-06 21:58:37](https://github.com/leanprover-community/mathlib/commit/0a89f18)
chore(set_theory/ordinal/basic): clean up `ordinal.card` API ([#15147](https://github.com/leanprover-community/mathlib/pull/15147))
We tweak some spacing throughout this section of the file, and golf a few theorems/definitions.
Conflicts and is inspired by [#15137](https://github.com/leanprover-community/mathlib/pull/15137).
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean
- \+/\- *def* ordinal.card
- \+/\- *theorem* ordinal.card_type
- \+ *lemma* ordinal.ne_zero_of_out_nonempty
- \+/\- *theorem* ordinal.type_ne_zero_iff_nonempty



## [2022-07-06 21:58:36](https://github.com/leanprover-community/mathlib/commit/a54e63d)
feat(set_theory/ordinal/basic): basic lemmas on `ordinal.lift`  ([#15146](https://github.com/leanprover-community/mathlib/pull/15146))
We add some missing instances for preimages, and missing theorems for `ordinal.lift`. We remove `ordinal.lift_type`, as it was just a worse way of stating `ordinal.type_ulift`.
We also tweak some spacing and golf a few theorems.
This conflicts with (and is inspired by) some of the changes of [#15137](https://github.com/leanprover-community/mathlib/pull/15137).
#### Estimated changes
Modified src/order/rel_iso.lean


Modified src/set_theory/cardinal/cofinality.lean


Modified src/set_theory/ordinal/basic.lean
- \- *theorem* ordinal.lift_type
- \+/\- *theorem* ordinal.lift_zero
- \+ *theorem* ordinal.type_lift_preimage
- \+ *theorem* ordinal.type_preimage
- \+ *theorem* ordinal.type_ulift
- \+ *theorem* rel_iso.ordinal_lift_type_eq



## [2022-07-06 19:18:30](https://github.com/leanprover-community/mathlib/commit/b758104)
feat(order/basic): a symmetric relation implies equality when it implies less-equal ([#15149](https://github.com/leanprover-community/mathlib/pull/15149))
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* rel_imp_eq_of_rel_imp_le



## [2022-07-06 15:08:32](https://github.com/leanprover-community/mathlib/commit/d45a8ac)
refactor(topology/separation): redefine `t0_space` ([#15046](https://github.com/leanprover-community/mathlib/pull/15046))
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+ *def* prime_spectrum.nhds_order_embedding

Modified src/topology/alexandroff.lean
- \+ *lemma* alexandroff.inseparable_coe
- \+ *lemma* alexandroff.inseparable_iff
- \+ *lemma* alexandroff.not_inseparable_coe_infty
- \+ *lemma* alexandroff.not_inseparable_infty_coe
- \+ *lemma* alexandroff.not_specializes_infty_coe
- \+ *lemma* alexandroff.specializes_coe

Modified src/topology/separation.lean
- \- *lemma* t0_space_def
- \+ *lemma* t0_space_iff_exists_is_open_xor_mem
- \+ *lemma* t1_space_iff_specializes_imp_eq

Modified src/topology/uniform_space/separation.lean




## [2022-07-06 13:12:54](https://github.com/leanprover-community/mathlib/commit/71b1be6)
feat(analysis/inner_product_space): add simple lemmas for the orthogonal complement ([#15020](https://github.com/leanprover-community/mathlib/pull/15020))
We show that the orthogonal complement of a dense subspace is trivial.
#### Estimated changes
Modified src/analysis/inner_product_space/projection.lean
- \+ *lemma* submodule.topological_closure_eq_top_iff
- \+ *lemma* submodule.triorthogonal_eq_orthogonal

Modified src/topology/algebra/module/basic.lean
- \+ *lemma* is_closed.submodule_topological_closure_eq
- \+ *lemma* submodule.dense_iff_topological_closure_eq_top



## [2022-07-06 11:16:59](https://github.com/leanprover-community/mathlib/commit/f09322b)
feat(geometry/manifold/local_invariant_properties): simplify definitions and proofs ([#15116](https://github.com/leanprover-community/mathlib/pull/15116))
* Simplify the sets in `local_invariant_prop` and `lift_prop_within_at`
* Simplify many proofs in `local_invariant_properties.lean`
* Reorder the intersection in `cont_diff_within_at_prop` to be more consistent with all lemmas in `smooth_manifold_with_corners.lean`
* New lemmas, such as `cont_mdiff_within_at_iff_of_mem_source` and properties of `local_invariant_prop`
* I expect that some lemmas in `cont_mdiff.lean` can be simplified using the new definitions, but I don't do that in this PR.
* Lemma renamings:
```
cont_mdiff_within_at_iff -> cont_mdiff_within_at_iff'
cont_mdiff_within_at_iff' -> cont_mdiff_within_at_iff_of_mem_source'
cont_mdiff_within_at_iff'' -> cont_mdiff_within_at_iff [or iff.rfl]
```
#### Estimated changes
Modified src/geometry/manifold/charted_space.lean
- \+ *lemma* chart_source_mem_nhds
- \+ *lemma* chart_target_mem_nhds

Modified src/geometry/manifold/cont_mdiff.lean
- \- *lemma* cont_diff_within_at_local_invariant_prop_id
- \- *lemma* cont_diff_within_at_local_invariant_prop_mono
- \+/\- *def* cont_diff_within_at_prop
- \+ *lemma* cont_diff_within_at_prop_id
- \+ *lemma* cont_diff_within_at_prop_mono
- \+/\- *lemma* cont_mdiff_at_ext_chart_at
- \+ *lemma* cont_mdiff_at_iff
- \+ *lemma* cont_mdiff_at_iff_of_mem_source
- \- *lemma* cont_mdiff_within_at_iff''
- \+/\- *lemma* cont_mdiff_within_at_iff'
- \+ *lemma* cont_mdiff_within_at_iff_of_mem_source'
- \+ *lemma* cont_mdiff_within_at_iff_of_mem_source

Modified src/geometry/manifold/diffeomorph.lean


Modified src/geometry/manifold/local_invariant_properties.lean
- \+/\- *def* charted_space.lift_prop
- \+/\- *def* charted_space.lift_prop_at
- \+ *lemma* charted_space.lift_prop_at_iff
- \+ *lemma* charted_space.lift_prop_iff
- \+/\- *def* charted_space.lift_prop_on
- \+/\- *def* charted_space.lift_prop_within_at
- \+/\- *lemma* structure_groupoid.lift_prop_on_univ
- \+/\- *lemma* structure_groupoid.lift_prop_within_at_univ
- \+ *lemma* structure_groupoid.local_invariant_prop.congr'
- \+ *lemma* structure_groupoid.local_invariant_prop.congr
- \+ *lemma* structure_groupoid.local_invariant_prop.congr_iff
- \+ *lemma* structure_groupoid.local_invariant_prop.congr_iff_nhds_within
- \+ *lemma* structure_groupoid.local_invariant_prop.congr_nhds_within'
- \+ *lemma* structure_groupoid.local_invariant_prop.congr_nhds_within
- \+ *lemma* structure_groupoid.local_invariant_prop.congr_set
- \+ *lemma* structure_groupoid.local_invariant_prop.is_local_nhds
- \+ *lemma* structure_groupoid.local_invariant_prop.left_invariance
- \+/\- *lemma* structure_groupoid.local_invariant_prop.lift_prop_of_locally_lift_prop_on
- \+/\- *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_congr_iff
- \+/\- *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_congr_iff_of_eventually_eq
- \+ *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_iff

Modified src/topology/continuous_on.lean
- \+ *lemma* mem_nhds_within_iff_eventually
- \+ *lemma* mem_nhds_within_iff_eventually_eq
- \+ *lemma* nhds_within_eq_iff_eventually_eq

Modified src/topology/local_homeomorph.lean
- \+ *lemma* local_homeomorph.eventually_nhds'
- \+ *lemma* local_homeomorph.eventually_nhds
- \+ *lemma* local_homeomorph.eventually_nhds_within'
- \+ *lemma* local_homeomorph.eventually_nhds_within
- \+ *lemma* local_homeomorph.preimage_eventually_eq_target_inter_preimage_inter



## [2022-07-06 08:41:41](https://github.com/leanprover-community/mathlib/commit/8ff5e11)
feat(analysis/special_functions/complex/arg): add complex.abs_eq_one_iff ([#15125](https://github.com/leanprover-community/mathlib/pull/15125))
This is a simpler formulation of `complex.range_exp_mul_I` below.
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* complex.abs_eq_one_iff



## [2022-07-06 08:41:40](https://github.com/leanprover-community/mathlib/commit/d908bc0)
chore(data/fintype): drop a `decidable_pred` assumption ([#14971](https://github.com/leanprover-community/mathlib/pull/14971))
OTOH, now the proof depends on `classical.choice`.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+/\- *def* fintype_of_fintype_ne



## [2022-07-06 07:46:32](https://github.com/leanprover-community/mathlib/commit/a95b442)
feat(probability/martingale): Doob's maximal inequality ([#14737](https://github.com/leanprover-community/mathlib/pull/14737))
#### Estimated changes
Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_theory.set_integral_ge_of_const_le

Modified src/measure_theory/lattice.lean
- \+ *lemma* finset.measurable_range_sup''
- \+ *lemma* finset.measurable_range_sup'
- \+ *lemma* finset.measurable_sup'

Modified src/probability/hitting_time.lean
- \+ *lemma* measure_theory.stopped_value_hitting_mem

Modified src/probability/martingale.lean
- \+ *lemma* measure_theory.maximal_ineq
- \+ *lemma* measure_theory.smul_le_stopped_value_hitting



## [2022-07-06 07:04:08](https://github.com/leanprover-community/mathlib/commit/bd9c307)
doc(overview): add probability theory ([#15114](https://github.com/leanprover-community/mathlib/pull/15114))
Also:
* Add convolutions to overview and undergrad
* Add some other probability notions to undergrad
* Minor cleanup in probability module docs
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/probability/cond_count.lean


Modified src/probability/moments.lean




## [2022-07-06 02:26:24](https://github.com/leanprover-community/mathlib/commit/93e97d1)
feat(analysis/convex/function): Variants of `convex_on.le_right_of_left_le` ([#14821](https://github.com/leanprover-community/mathlib/pull/14821))
This PR adds four variants of `convex_on.le_right_of_left_le` that are useful when dealing with convex functions on the real numbers.
#### Estimated changes
Modified src/analysis/convex/function.lean
- \- *lemma* concave_on.le_right_of_left_le'
- \- *lemma* concave_on.le_right_of_left_le
- \+ *lemma* concave_on.left_le_of_le_right''
- \+ *lemma* concave_on.right_le_of_le_left''
- \+ *lemma* concave_on.right_le_of_le_left'
- \+ *lemma* concave_on.right_le_of_le_left
- \+ *lemma* convex_on.le_left_of_right_le''
- \+ *lemma* convex_on.le_right_of_left_le''



## [2022-07-05 23:18:42](https://github.com/leanprover-community/mathlib/commit/71e11de)
chore(analysis/normed/field/basic): add `@[simp]` to `real.norm_eq_abs ([#15006](https://github.com/leanprover-community/mathlib/pull/15006))
* mark `real.norm_eq_abs` and `abs_nonneg` as `simp` lemmas;
* add `abs` versions of `is_o.norm_left` etc;
* add `inner_product_geometry.angle_smul_smul` and `linear_isometry.angle_map`.
#### Estimated changes
Modified archive/imo/imo1972_q5.lean


Modified counterexamples/seminorm_lattice_not_distrib.lean


Modified src/algebra/order/group.lean
- \+/\- *lemma* abs_nonneg

Modified src/analysis/asymptotics/asymptotics.lean
- \+ *theorem* asymptotics.is_O_abs_abs
- \+ *theorem* asymptotics.is_O_abs_left
- \+ *theorem* asymptotics.is_O_abs_right
- \+ *theorem* asymptotics.is_O_with_abs_abs
- \+ *theorem* asymptotics.is_O_with_abs_left
- \+ *theorem* asymptotics.is_O_with_abs_right
- \+ *theorem* asymptotics.is_o_abs_abs
- \+ *theorem* asymptotics.is_o_abs_left
- \+ *theorem* asymptotics.is_o_abs_right

Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/complex/basic.lean
- \+/\- *def* complex.im_clm
- \+/\- *def* complex.re_clm

Modified src/analysis/normed/group/basic.lean
- \+/\- *lemma* real.norm_eq_abs

Modified src/analysis/normed_space/basic.lean


Modified src/analysis/special_functions/log/deriv.lean


Modified src/geometry/euclidean/basic.lean
- \+ *lemma* inner_product_geometry.angle_smul_smul
- \+ *lemma* linear_isometry.angle_map

Modified src/geometry/euclidean/inversion.lean


Modified src/geometry/euclidean/sphere.lean


Modified src/geometry/manifold/instances/sphere.lean


Modified src/measure_theory/function/l1_space.lean


Modified src/measure_theory/function/l2_space.lean


Modified src/measure_theory/integral/bochner.lean


Modified src/measure_theory/integral/circle_integral.lean


Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/number_theory/padics/hensel.lean


Modified src/topology/tietze_extension.lean




## [2022-07-05 23:18:41](https://github.com/leanprover-community/mathlib/commit/071dc90)
feat(probability/martingale): positive part of a submartingale is also a submartingale ([#14932](https://github.com/leanprover-community/mathlib/pull/14932))
#### Estimated changes
Modified src/measure_theory/function/ae_eq_of_integral.lean
- \+ *lemma* measure_theory.ae_le_of_forall_set_integral_le

Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_le.le_sup_of_le_left
- \+ *lemma* filter.eventually_le.le_sup_of_le_right
- \+ *lemma* filter.eventually_le.sup
- \+ *lemma* filter.eventually_le.sup_le

Modified src/probability/martingale.lean




## [2022-07-05 19:14:55](https://github.com/leanprover-community/mathlib/commit/f10d0ab)
feat(*): add lemmas about sigma types ([#15085](https://github.com/leanprover-community/mathlib/pull/15085))
* move `set.range_sigma_mk` to `data.set.sigma`;
* add `set.preimage_image_sigma_mk_of_ne`, `set.image_sigma_mk_preimage_sigma_map_subset`, and `set.image_sigma_mk_preimage_sigma_map`;
* add `function.injective.of_sigma_map` and `function.injective.sigma_map_iff`;
* don't use pattern matching in the definition of `prod.to_sigma`;
* add `filter.map_sigma_mk_comap`
#### Estimated changes
Modified src/data/set/basic.lean
- \- *theorem* set.range_sigma_mk

Modified src/data/set/sigma.lean
- \+ *lemma* set.image_sigma_mk_preimage_sigma_map
- \+ *lemma* set.image_sigma_mk_preimage_sigma_map_subset
- \+ *theorem* set.preimage_image_sigma_mk_of_ne
- \+ *theorem* set.range_sigma_mk

Modified src/data/sigma/basic.lean
- \+ *lemma* function.injective.of_sigma_map
- \+ *lemma* function.injective.sigma_map_iff
- \+/\- *lemma* prod.fst_to_sigma
- \+/\- *lemma* prod.snd_to_sigma
- \+/\- *def* prod.to_sigma
- \+ *lemma* prod.to_sigma_mk

Modified src/order/filter/bases.lean
- \+ *lemma* filter.map_sigma_mk_comap



## [2022-07-05 16:26:49](https://github.com/leanprover-community/mathlib/commit/527afb3)
feat(topology/sets/compacts): prod constructions ([#15118](https://github.com/leanprover-community/mathlib/pull/15118))
#### Estimated changes
Modified src/topology/sets/compacts.lean
- \+ *lemma* topological_space.compact_opens.coe_prod
- \+ *lemma* topological_space.compacts.carrier_eq_coe
- \+ *lemma* topological_space.compacts.coe_prod
- \+ *lemma* topological_space.nonempty_compacts.carrier_eq_coe
- \+ *lemma* topological_space.nonempty_compacts.coe_prod
- \+ *lemma* topological_space.positive_compacts.carrier_eq_coe
- \+ *lemma* topological_space.positive_compacts.coe_prod



## [2022-07-05 15:04:58](https://github.com/leanprover-community/mathlib/commit/db9cb46)
feat(analysis/complex): equiv_real_prod_symm_apply ([#15122](https://github.com/leanprover-community/mathlib/pull/15122))
Plus some minor lemmas for [#15106](https://github.com/leanprover-community/mathlib/pull/15106).
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* complex.arg_lt_pi_iff

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* real.continuous_at_rpow_const

Modified src/data/complex/basic.lean
- \+/\- *def* complex.equiv_real_prod
- \+ *lemma* complex.equiv_real_prod_symm_apply

Modified src/topology/separation.lean
- \+ *lemma* is_open_ne_fun



## [2022-07-05 15:04:57](https://github.com/leanprover-community/mathlib/commit/68ae182)
feat(measure_theory/group/measure): a product of Haar measures is a Haar measure ([#15120](https://github.com/leanprover-community/mathlib/pull/15120))
#### Estimated changes
Modified src/measure_theory/constructions/prod.lean
- \+ *lemma* measure_theory.integrable_prod_mul
- \+ *lemma* measure_theory.integral_prod_mul
- \+ *lemma* measure_theory.set_integral_prod_mul

Modified src/measure_theory/function/jacobian.lean
- \+ *theorem* measure_theory.integral_target_eq_integral_abs_det_fderiv_smul

Modified src/measure_theory/group/measure.lean


Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* integrable_on_Ici_iff_integrable_on_Ioi'
- \+ *lemma* integrable_on_Ici_iff_integrable_on_Ioi

Modified src/measure_theory/measure/haar.lean
- \+ *lemma* measure_theory.measure.measure_preserving_inv



## [2022-07-05 12:32:49](https://github.com/leanprover-community/mathlib/commit/365e30d)
chore(data/set/*,order/*): add missing lemmas about `monotone_on` etc ([#14943](https://github.com/leanprover-community/mathlib/pull/14943))
* Add `monotone_on`/`antitone`/`antitone_on` versions of existing `monotone` lemmas for `id`/`const`, `inf`/`sup`/`min`/`max`, `inter`/`union`, and intervals.
* Drop `set.monotone_prod`, leave `monotone.set_prod` only.
* Golf some proofs that were broken by removal of `set.monotone_prod`.
#### Estimated changes
Modified src/data/set/intervals/monotone.lean


Modified src/data/set/lattice.lean
- \+ *theorem* antitone_on.inter
- \+ *theorem* antitone_on.union
- \+ *theorem* monotone_on.inter
- \+ *theorem* monotone_on.union
- \- *theorem* set.monotone_prod

Modified src/data/set/prod.lean
- \+ *theorem* antitone.set_prod
- \+ *theorem* antitone_on.set_prod
- \+ *theorem* monotone.set_prod
- \+ *theorem* monotone_on.set_prod

Modified src/order/filter/lift.lean


Modified src/order/lattice.lean


Modified src/order/monotone.lean
- \+ *theorem* antitone_on_const
- \+ *theorem* monotone_on_const
- \+ *lemma* monotone_on_id
- \+ *lemma* strict_anti_of_le_iff_le
- \+ *lemma* strict_mono_on_id

Modified src/tactic/monotonicity/lemmas.lean


Modified src/topology/uniform_space/basic.lean
- \+ *lemma* nhds_eq_uniformity'



## [2022-07-05 10:10:27](https://github.com/leanprover-community/mathlib/commit/dba3dce)
feat(measure_theory/function/conditional_expectation): monotonicity of the conditional expectation ([#15024](https://github.com/leanprover-community/mathlib/pull/15024))
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean
- \+ *lemma* measure_theory.condexp_L1_mono
- \+ *lemma* measure_theory.condexp_L2_indicator_nonneg
- \+ *lemma* measure_theory.condexp_ind_nonneg
- \+ *lemma* measure_theory.condexp_ind_smul_nonneg
- \+ *lemma* measure_theory.condexp_mono
- \+ *lemma* measure_theory.set_integral_condexp_L2_indicator



## [2022-07-05 10:10:26](https://github.com/leanprover-community/mathlib/commit/676e772)
refactor(analysis/convex/specific_functions): Remove hypothesis from `deriv_sqrt_mul_log` ([#15015](https://github.com/leanprover-community/mathlib/pull/15015))
This PR removes the `hx : 0 < x` hypothesis from `deriv_sqrt_mul_log`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_within_at.congr_of_mem
- \+ *theorem* has_deriv_within_at.deriv_eq_zero

Modified src/analysis/convex/specific_functions.lean
- \+/\- *lemma* deriv2_sqrt_mul_log
- \+ *lemma* deriv_sqrt_mul_log'
- \+/\- *lemma* deriv_sqrt_mul_log
- \+ *lemma* has_deriv_at_sqrt_mul_log

Modified src/topology/continuous_on.lean
- \+ *theorem* eventually_mem_nhds_within



## [2022-07-05 08:48:19](https://github.com/leanprover-community/mathlib/commit/83eda07)
refactor(data/real/ennreal): golf, generalize ([#14996](https://github.com/leanprover-community/mathlib/pull/14996))
## Add new lemmas
* `ennreal.bit0_strict_mono`, `ennreal.bit0_injective`, `ennreal.bit0_lt_bit0`, `ennreal.bit0_le_bit0`, `ennreal.bit0_top`;
* `ennreal.bit1_strict_mono`, `ennreal.bit1_injective`, `ennreal.bit1_lt_bit1`, `ennreal.bit1_le_bit1`, `ennreal.bit1_top`;
* `ennreal.div_eq_inv_mul`, `ennreal.of_real_mul'`;
* `filter.eventually.prod_nhds`.
## Generalize lemmas
* Drop unneeded assumption in `real.to_nnreal_bit0` and `ennreal.of_real_bit0`.
## Rename lemmas
* `ennreal.mul_div_cancel` → `ennreal.div_mul_cancel`, fixing a TODO;
* `prod_is_open.mem_nhds` → `prod_mem_nhds`: there are no open sets in the statement.
## Other changes
* Golf some proofs.
* Avoid non-final `simp`s here and there.
* Move `mul_inv_cancel` etc up to use them in other proofs.
* Move some `to_nnreal` lemmas above `to_real` lemmas, use them in `to_real` lemmas.
* Use `to_dual` in `order_iso.inv_ennreal`.
#### Estimated changes
Modified src/analysis/mean_inequalities_pow.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.bit0_eq_top_iff
- \+/\- *lemma* ennreal.bit0_eq_zero_iff
- \+/\- *lemma* ennreal.bit0_inj
- \+ *lemma* ennreal.bit0_injective
- \+ *lemma* ennreal.bit0_le_bit0
- \+ *lemma* ennreal.bit0_lt_bit0
- \+ *lemma* ennreal.bit0_strict_mono
- \+ *lemma* ennreal.bit0_top
- \+/\- *lemma* ennreal.bit1_eq_one_iff
- \+/\- *lemma* ennreal.bit1_eq_top_iff
- \+/\- *lemma* ennreal.bit1_inj
- \+ *lemma* ennreal.bit1_injective
- \+ *lemma* ennreal.bit1_le_bit1
- \+ *lemma* ennreal.bit1_lt_bit1
- \+/\- *lemma* ennreal.bit1_ne_zero
- \+ *lemma* ennreal.bit1_strict_mono
- \+ *lemma* ennreal.bit1_top
- \+ *lemma* ennreal.div_eq_inv_mul
- \+ *lemma* ennreal.div_mul_cancel
- \+/\- *lemma* ennreal.inv_le_iff_le_mul
- \+/\- *lemma* ennreal.inv_le_inv
- \+/\- *lemma* ennreal.inv_lt_inv
- \+ *lemma* ennreal.inv_strict_anti
- \- *lemma* ennreal.mul_div_cancel
- \+/\- *lemma* ennreal.mul_div_le
- \+/\- *lemma* ennreal.of_real_bit0
- \+ *lemma* ennreal.of_real_mul'
- \+/\- *lemma* ennreal.to_nnreal_mul
- \+/\- *lemma* ennreal.to_nnreal_mul_top
- \+/\- *lemma* ennreal.to_nnreal_pow
- \+/\- *lemma* ennreal.to_nnreal_prod
- \+/\- *lemma* ennreal.to_nnreal_top_mul
- \+/\- *lemma* ennreal.to_real_mul
- \+/\- *lemma* ennreal.to_real_mul_top
- \+/\- *lemma* ennreal.to_real_pow
- \+/\- *lemma* ennreal.to_real_prod
- \+/\- *lemma* ennreal.to_real_top_mul
- \+/\- *lemma* order_iso.inv_ennreal_symm_apply

Modified src/data/real/nnreal.lean
- \+/\- *lemma* real.to_nnreal_bit0

Modified src/number_theory/liouville/measure.lean


Modified src/topology/algebra/order/basic.lean


Modified src/topology/constructions.lean
- \+ *lemma* filter.eventually.prod_nhds
- \- *lemma* prod_is_open.mem_nhds
- \+ *lemma* prod_mem_nhds

Modified src/topology/instances/ennreal.lean


Modified src/topology/uniform_space/compact_separated.lean




## [2022-07-04 23:23:06](https://github.com/leanprover-community/mathlib/commit/1886093)
chore(analysis/calculus/deriv): make the exponent explicit in pow lemmas ([#15117](https://github.com/leanprover-community/mathlib/pull/15117))
This is useful to build derivatives for explicit functions using dot notation.
#### Estimated changes
Modified archive/100-theorems-list/9_area_of_a_circle.lean


Modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* deriv_pow'
- \+/\- *lemma* deriv_pow

Modified src/analysis/complex/phragmen_lindelof.lean


Modified src/analysis/convex/specific_functions.lean


Modified src/analysis/special_functions/integrals.lean




## [2022-07-04 21:37:31](https://github.com/leanprover-community/mathlib/commit/73d15d7)
feat(number_theory/wilson): add Wilson's Theorem ([#14717](https://github.com/leanprover-community/mathlib/pull/14717))
The previous "Wilson's lemma" (zmod.wilsons_lemma) was a single direction of the iff for Wilson's Theorem. This finishes the proof by adding the (admittedly, much simpler) direction where, if the congruence is satisfied for `n`, then `n` is prime.
#### Estimated changes
Added src/number_theory/wilson.lean
- \+ *theorem* nat.prime_iff_fac_equiv_neg_one
- \+ *lemma* nat.prime_of_fac_equiv_neg_one



## [2022-07-04 20:40:33](https://github.com/leanprover-community/mathlib/commit/06ac34b)
feat(analysis/special_functions/complex/arg): `continuous_at_arg_coe_angle` ([#14980](https://github.com/leanprover-community/mathlib/pull/14980))
Add the lemma that `complex.arg`, coerced to `real.angle`, is
continuous except at 0.
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* complex.continuous_at_arg_coe_angle



## [2022-07-04 19:58:37](https://github.com/leanprover-community/mathlib/commit/8f391f5)
feat(geometry/euclidean/basic): `continuous_at_angle` ([#15021](https://github.com/leanprover-community/mathlib/pull/15021))
Add lemmas that (unoriented) angles are continuous, as a function of a
pair of vectors or a triple of points, except where one of the vectors
is zero or one of the end points equals the middle point.
#### Estimated changes
Modified src/geometry/euclidean/basic.lean
- \+ *lemma* euclidean_geometry.continuous_at_angle
- \+ *lemma* inner_product_geometry.continuous_at_angle



## [2022-07-04 17:12:28](https://github.com/leanprover-community/mathlib/commit/407f39b)
chore(ring_theory/matrix_algebra): golf using `matrix.map` ([#15040](https://github.com/leanprover-community/mathlib/pull/15040))
This replaces terms of the form `λ i j, a * algebra_map R A (m i j)` with the defeq `a • m.map (algebra_map R A)`, as then we get access to the API about `map`.
This also leverages existing bundled maps to avoid reproving linearity in the auxiliary constructions, removing `to_fun` and `to_fun_right_linear` as we can construct `to_fun_bilinear` directly with ease.
#### Estimated changes
Modified src/ring_theory/matrix_algebra.lean
- \- *def* matrix_equiv_tensor.to_fun
- \+ *lemma* matrix_equiv_tensor.to_fun_bilinear_apply
- \- *def* matrix_equiv_tensor.to_fun_right_linear



## [2022-07-04 01:38:58](https://github.com/leanprover-community/mathlib/commit/051dffa)
refactor(data/nat/parity): `nat.even_succ` -> `nat.even_add_one` ([#14917](https://github.com/leanprover-community/mathlib/pull/14917))
Change `nat.even_succ` to be analogous to `int.even_add_one`.
#### Estimated changes
Modified archive/100-theorems-list/70_perfect_numbers.lean


Modified src/algebra/geom_sum.lean


Modified src/analysis/special_functions/log/deriv.lean


Modified src/data/nat/parity.lean
- \+ *theorem* nat.even_add_one
- \- *theorem* nat.even_succ



## [2022-07-03 17:11:19](https://github.com/leanprover-community/mathlib/commit/46344b4)
feat(category_theory/limits): bilimit from kernel ([#14452](https://github.com/leanprover-community/mathlib/pull/14452))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *def* category_theory.limits.binary_cofan.is_colimit.mk
- \+ *def* category_theory.limits.binary_fan.is_limit.mk

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.binary_bicone.is_bilimit_of_cokernel_fst
- \+ *def* category_theory.limits.binary_bicone.is_bilimit_of_cokernel_snd
- \+ *def* category_theory.limits.binary_bicone.is_bilimit_of_kernel_inl
- \+ *def* category_theory.limits.binary_bicone.is_bilimit_of_kernel_inr



## [2022-07-03 11:47:31](https://github.com/leanprover-community/mathlib/commit/024a423)
refactor(category_theory): generalise universe levels in preservation statements ([#15067](https://github.com/leanprover-community/mathlib/pull/15067))
This big refactoring of universe levels in the category theory library allows to express limit preservation statements like exactness of functors which are between categories that are not necessarily in the same universe level. For this change to make sense for fixed diagrams (like coequalizers or binary products), the corresponding index categories, the universe of which so far was pinned to the category they were used for, is now fixed to `Type`.
#### Estimated changes
Modified src/algebra/category/FinVect/limits.lean


Modified src/algebra/category/Group/biproducts.lean
- \+/\- *def* AddCommGroup.biproduct_iso_pi
- \+/\- *lemma* AddCommGroup.biproduct_iso_pi_inv_comp_π

Modified src/algebra/category/Module/biproducts.lean


Modified src/algebra/category/Ring/constructions.lean


Modified src/algebraic_geometry/Spec.lean
- \+/\- *def* algebraic_geometry.Spec.to_PresheafedSpace

Modified src/algebraic_geometry/locally_ringed_space/has_colimits.lean


Modified src/algebraic_geometry/open_immersion.lean
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.is_open_immersion.SheafedSpace_to_SheafedSpace

Modified src/algebraic_geometry/presheafed_space.lean
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.as_coe
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.coe_to_fun_eq
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.comp_base
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.comp_c_app
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.congr_app
- \+/\- *def* algebraic_geometry.PresheafedSpace.forget
- \+/\- *def* algebraic_geometry.PresheafedSpace.id
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.id_base
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.id_c
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.id_c_app
- \+/\- *def* algebraic_geometry.PresheafedSpace.of_restrict
- \+/\- *def* algebraic_geometry.PresheafedSpace.restrict
- \+/\- *def* algebraic_geometry.PresheafedSpace.Γ
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.Γ_map_op
- \+/\- *def* category_theory.functor.map_presheaf
- \+/\- *lemma* category_theory.functor.map_presheaf_map_c
- \+/\- *lemma* category_theory.functor.map_presheaf_map_f

Modified src/algebraic_geometry/presheafed_space/gluing.lean


Modified src/algebraic_geometry/presheafed_space/has_colimits.lean
- \+/\- *def* algebraic_geometry.PresheafedSpace.colimit
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.colimit_carrier
- \+/\- *def* algebraic_geometry.PresheafedSpace.colimit_cocone
- \+/\- *def* algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc
- \+/\- *def* algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_c_app
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_c_naturality
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_fac
- \+/\- *def* algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.colimit_presheaf
- \+/\- *def* algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_hom_π
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_inv_ι_app
- \+/\- *def* algebraic_geometry.PresheafedSpace.componentwise_diagram
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.map_comp_c_app
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.map_id_c_app
- \+/\- *def* algebraic_geometry.PresheafedSpace.pushforward_diagram_to_colimit

Modified src/algebraic_geometry/sheafed_space.lean
- \+/\- *lemma* algebraic_geometry.SheafedSpace.as_coe
- \+/\- *def* algebraic_geometry.SheafedSpace.forget_to_PresheafedSpace
- \- *def* algebraic_geometry.SheafedSpace.punit
- \+ *def* algebraic_geometry.SheafedSpace.unit

Modified src/algebraic_geometry/stalks.lean
- \+/\- *def* algebraic_geometry.PresheafedSpace.restrict_stalk_iso
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.restrict_stalk_iso_hom_eq_germ
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.restrict_stalk_iso_inv_eq_germ
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.restrict_stalk_iso_inv_eq_of_restrict
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.stalk_map.comp
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.stalk_map.congr
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.stalk_map.congr_hom
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.stalk_map.congr_point
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.stalk_map.id
- \+/\- *def* algebraic_geometry.PresheafedSpace.stalk_map.stalk_iso
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.stalk_map.stalk_specializes_stalk_map
- \+/\- *def* algebraic_geometry.PresheafedSpace.stalk_map
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.stalk_map_germ

Modified src/algebraic_topology/cech_nerve.lean


Modified src/category_theory/abelian/right_derived.lean


Modified src/category_theory/closed/functor.lean


Modified src/category_theory/closed/ideal.lean


Modified src/category_theory/closed/types.lean


Modified src/category_theory/discrete_category.lean
- \+ *def* category_theory.discrete.functor_comp

Modified src/category_theory/filtered.lean


Modified src/category_theory/fin_category.lean


Modified src/category_theory/functor/flat.lean


Modified src/category_theory/functor/left_derived.lean


Modified src/category_theory/graded_object.lean


Modified src/category_theory/idempotents/biproducts.lean
- \+/\- *def* category_theory.idempotents.karoubi.biproducts.bicone

Modified src/category_theory/is_connected.lean


Modified src/category_theory/limits/colimit_limit.lean


Modified src/category_theory/limits/comma.lean


Modified src/category_theory/limits/concrete_category.lean
- \+/\- *def* category_theory.limits.concrete.multiequalizer_equiv
- \+/\- *lemma* category_theory.limits.concrete.multiequalizer_equiv_apply
- \+/\- *lemma* category_theory.limits.concrete.multiequalizer_ext
- \+/\- *lemma* category_theory.limits.concrete.wide_pullback_ext'
- \+/\- *lemma* category_theory.limits.concrete.wide_pullback_ext

Modified src/category_theory/limits/cone_category.lean


Modified src/category_theory/limits/constructions/finite_products_of_binary_products.lean
- \+/\- *def* category_theory.extend_cofan
- \+/\- *def* category_theory.extend_cofan_is_colimit
- \+/\- *def* category_theory.extend_fan
- \+/\- *def* category_theory.extend_fan_is_limit
- \+ *def* category_theory.preserves_shape_fin_of_preserves_binary_and_initial
- \+ *def* category_theory.preserves_shape_fin_of_preserves_binary_and_terminal
- \- *def* category_theory.preserves_ulift_fin_of_preserves_binary_and_initial
- \- *def* category_theory.preserves_ulift_fin_of_preserves_binary_and_terminal

Modified src/category_theory/limits/constructions/limits_of_products_and_equalizers.lean
- \+/\- *def* category_theory.limits.colimit_quotient_coproduct
- \+/\- *def* category_theory.limits.limit_subobject_product

Modified src/category_theory/limits/constructions/over/default.lean


Modified src/category_theory/limits/constructions/over/products.lean
- \+/\- *def* category_theory.over.construct_products.cones_equiv_functor
- \+/\- *def* category_theory.over.construct_products.cones_equiv_inverse
- \+/\- *def* category_theory.over.construct_products.cones_equiv_inverse_obj
- \+/\- *lemma* category_theory.over.construct_products.over_products_of_wide_pullbacks
- \+/\- *def* category_theory.over.construct_products.wide_pullback_diagram_of_diagram_over

Modified src/category_theory/limits/constructions/weakly_initial.lean
- \+/\- *lemma* category_theory.has_initial_of_weakly_initial_and_has_wide_equalizers
- \+/\- *lemma* category_theory.has_weakly_initial_of_weakly_initial_set_and_has_products

Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean


Modified src/category_theory/limits/has_limits.lean
- \- *lemma* category_theory.limits.has_smallest_colimits_of_has_colimits
- \- *lemma* category_theory.limits.has_smallest_limits_of_has_limits

Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/limits/opposites.lean
- \+/\- *lemma* category_theory.limits.has_finite_coproducts_opposite
- \+/\- *lemma* category_theory.limits.has_finite_products_opposite

Modified src/category_theory/limits/preserves/basic.lean
- \+ *def* category_theory.limits.preserves_colimits_of_size_shrink
- \+ *def* category_theory.limits.preserves_limits_of_size_shrink
- \+ *def* category_theory.limits.preserves_smallest_colimits_of_preserves_colimits
- \+ *def* category_theory.limits.preserves_smallest_limits_of_preserves_limits
- \+ *def* category_theory.limits.reflects_colimits_of_shape_of_equiv
- \+ *def* category_theory.limits.reflects_colimits_of_size_shrink
- \+ *def* category_theory.limits.reflects_limits_of_shape_of_equiv
- \+ *def* category_theory.limits.reflects_limits_of_size_shrink
- \+ *def* category_theory.limits.reflects_smallest_colimits_of_reflects_colimits
- \+ *def* category_theory.limits.reflects_smallest_limits_of_reflects_limits

Modified src/category_theory/limits/preserves/finite.lean
- \+ *def* category_theory.limits.preserves_finite_colimits_of_preserves_finite_colimits_of_size
- \+ *def* category_theory.limits.preserves_finite_limits_of_preserves_finite_limits_of_size

Modified src/category_theory/limits/preserves/shapes/binary_products.lean


Modified src/category_theory/limits/preserves/shapes/biproducts.lean
- \+ *lemma* category_theory.functor.map_bicone_whisker
- \+ *def* category_theory.limits.preserves_biproducts_shrink

Modified src/category_theory/limits/preserves/shapes/equalizers.lean


Modified src/category_theory/limits/preserves/shapes/kernels.lean


Modified src/category_theory/limits/preserves/shapes/products.lean


Modified src/category_theory/limits/preserves/shapes/pullbacks.lean


Modified src/category_theory/limits/preserves/shapes/terminal.lean
- \+/\- *lemma* category_theory.limits.has_initial_of_has_initial_of_preserves_colimit
- \+/\- *lemma* category_theory.limits.has_terminal_of_has_terminal_of_preserves_limit
- \+/\- *def* category_theory.limits.is_colimit_of_has_initial_of_preserves_colimit
- \+/\- *def* category_theory.limits.is_initial.is_initial_obj
- \+/\- *def* category_theory.limits.is_initial.is_initial_of_obj
- \+/\- *def* category_theory.limits.is_limit_of_has_terminal_of_preserves_limit
- \+/\- *def* category_theory.limits.is_terminal.is_terminal_obj
- \+/\- *def* category_theory.limits.is_terminal.is_terminal_of_obj

Modified src/category_theory/limits/preserves/shapes/zero.lean


Modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *lemma* category_theory.limits.coprod.map_comp_inl_inr_codiag
- \+/\- *def* category_theory.limits.pair
- \+/\- *lemma* category_theory.limits.prod.diag_map_fst_snd_comp

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.bicone.whisker
- \+ *def* category_theory.limits.bicone.whisker_is_bilimit_iff
- \+ *def* category_theory.limits.bicone.whisker_to_cocone
- \+ *def* category_theory.limits.bicone.whisker_to_cone
- \+/\- *def* category_theory.limits.biproduct.reindex

Modified src/category_theory/limits/shapes/comm_sq.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+/\- *def* category_theory.limits.parallel_pair.ext
- \+/\- *def* category_theory.limits.parallel_pair
- \+/\- *def* category_theory.limits.walking_parallel_pair_op
- \+/\- *def* category_theory.limits.walking_parallel_pair_op_equiv

Modified src/category_theory/limits/shapes/finite_limits.lean
- \+ *lemma* category_theory.limits.has_finite_colimits_of_has_finite_colimits_of_size
- \+ *lemma* category_theory.limits.has_finite_limits_of_has_finite_limits_of_size

Modified src/category_theory/limits/shapes/finite_products.lean
- \+/\- *lemma* category_theory.limits.has_finite_coproducts_of_has_coproducts
- \+/\- *lemma* category_theory.limits.has_finite_products_of_has_products

Modified src/category_theory/limits/shapes/functor_category.lean


Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/limits/shapes/multiequalizer.lean


Modified src/category_theory/limits/shapes/products.lean
- \+/\- *lemma* category_theory.limits.has_products_of_limit_fans
- \+ *lemma* category_theory.limits.has_smallest_coproducts_of_has_coproducts
- \+ *lemma* category_theory.limits.has_smallest_products_of_has_products

Modified src/category_theory/limits/shapes/pullbacks.lean
- \- *def* category_theory.limits.walking_cospan_equiv
- \- *def* category_theory.limits.walking_cospan_functor
- \- *lemma* category_theory.limits.walking_cospan_functor_id
- \- *lemma* category_theory.limits.walking_cospan_functor_inl
- \- *lemma* category_theory.limits.walking_cospan_functor_inr
- \- *lemma* category_theory.limits.walking_cospan_functor_left
- \- *lemma* category_theory.limits.walking_cospan_functor_one
- \- *lemma* category_theory.limits.walking_cospan_functor_right
- \- *def* category_theory.limits.walking_span_equiv
- \- *def* category_theory.limits.walking_span_functor
- \- *lemma* category_theory.limits.walking_span_functor_fst
- \- *lemma* category_theory.limits.walking_span_functor_id
- \- *lemma* category_theory.limits.walking_span_functor_left
- \- *lemma* category_theory.limits.walking_span_functor_right
- \- *lemma* category_theory.limits.walking_span_functor_snd
- \- *lemma* category_theory.limits.walking_span_functor_zero

Modified src/category_theory/limits/shapes/split_coequalizer.lean


Modified src/category_theory/limits/shapes/terminal.lean
- \+/\- *def* category_theory.limits.as_empty_cocone
- \+/\- *def* category_theory.limits.as_empty_cone
- \+/\- *def* category_theory.limits.is_initial_equiv_unique
- \+/\- *def* category_theory.limits.is_terminal_equiv_unique

Modified src/category_theory/limits/shapes/types.lean


Modified src/category_theory/limits/shapes/wide_equalizers.lean


Modified src/category_theory/limits/shapes/wide_pullbacks.lean
- \+ *lemma* category_theory.limits.has_wide_pullbacks_shrink
- \+ *def* category_theory.limits.wide_pullback_shape.equivalence_of_equiv
- \+ *def* category_theory.limits.wide_pullback_shape.ulift_equivalence

Modified src/category_theory/limits/shapes/zero_morphisms.lean


Modified src/category_theory/limits/small_complete.lean


Renamed src/category_theory/limits/punit.lean to src/category_theory/limits/unit.lean


Modified src/category_theory/limits/yoneda.lean
- \+/\- *def* category_theory.coyoneda_jointly_reflects_limits
- \+/\- *def* category_theory.yoneda_jointly_reflects_limits

Modified src/category_theory/monoidal/preadditive.lean
- \+/\- *def* category_theory.left_distributor
- \+/\- *lemma* category_theory.left_distributor_assoc
- \+/\- *lemma* category_theory.left_distributor_hom
- \+/\- *lemma* category_theory.left_distributor_inv
- \+/\- *def* category_theory.right_distributor
- \+/\- *lemma* category_theory.right_distributor_assoc
- \+/\- *lemma* category_theory.right_distributor_hom
- \+/\- *lemma* category_theory.right_distributor_inv

Modified src/category_theory/preadditive/Mat.lean


Modified src/category_theory/preadditive/biproducts.lean


Modified src/category_theory/preadditive/hom_orthogonal.lean


Modified src/category_theory/sites/left_exact.lean


Modified src/category_theory/sites/sheaf.lean


Modified src/category_theory/subobject/lattice.lean


Modified src/order/category/omega_complete_partial_order.lean


Modified src/topology/category/Top/limits.lean
- \+/\- *lemma* Top.coequalizer_is_open_iff

Modified src/topology/sheaves/forget.lean


Modified src/topology/sheaves/functors.lean


Modified src/topology/sheaves/limits.lean
- \+/\- *lemma* Top.is_sheaf_of_is_limit
- \+/\- *lemma* Top.limit_is_sheaf

Modified src/topology/sheaves/presheaf.lean
- \+/\- *lemma* Top.presheaf.pullback_obj_eq_pullback_obj
- \+/\- *def* Top.presheaf.pushforward.comp
- \+/\- *lemma* Top.presheaf.pushforward.comp_eq
- \+/\- *lemma* Top.presheaf.pushforward.comp_hom_app
- \+/\- *lemma* Top.presheaf.pushforward.comp_inv_app
- \+/\- *lemma* Top.presheaf.pushforward_eq'
- \+/\- *def* Top.presheaf.pushforward_eq
- \+/\- *lemma* Top.presheaf.pushforward_eq_eq
- \+/\- *lemma* Top.presheaf.pushforward_eq_rfl
- \+/\- *def* Top.presheaf.pushforward_map
- \+/\- *def* Top.presheaf.pushforward_obj
- \+/\- *lemma* Top.presheaf.pushforward_obj_map
- \+/\- *lemma* Top.presheaf.pushforward_obj_obj
- \+/\- *def* Top.presheaf

Modified src/topology/sheaves/sheaf.lean
- \+/\- *def* Top.presheaf.is_sheaf
- \- *lemma* Top.presheaf.is_sheaf_punit
- \+ *lemma* Top.presheaf.is_sheaf_unit
- \+/\- *def* Top.sheaf

Modified src/topology/sheaves/sheaf_condition/equalizer_products.lean
- \+/\- *def* Top.presheaf.sheaf_condition_equalizer_products.diagram

Modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean


Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean


Modified src/topology/sheaves/sheaf_condition/sites.lean




## [2022-07-03 09:05:56](https://github.com/leanprover-community/mathlib/commit/6e8f25e)
chore(ring_theory/dedekind_domain/ideal): fix style of a lemma statement  ([#15097](https://github.com/leanprover-community/mathlib/pull/15097))
#### Estimated changes
Modified src/ring_theory/dedekind_domain/ideal.lean
- \+/\- *lemma* ideal_factors_fun_of_quot_hom_comp



## [2022-07-02 14:14:01](https://github.com/leanprover-community/mathlib/commit/9e701b9)
feat(ring_theory/dedekind_domain): If `R/I` is isomorphic to `S/J` then the factorisations of `I` and `J` have the same shape ([#11053](https://github.com/leanprover-community/mathlib/pull/11053))
In this PR, we show that given Dedekind domains `R` and `S` with ideals `I` and `J`respectively, if quotients `R/I` and `S/J` are isomorphic, then the prime factorizations of `I` and `J` have the same shape, i.e. they have the same number of prime factors and up to permutation these prime factors have the same multiplicities. We can then get [the Dedekind-Kummer theorem](https://kconrad.math.uconn.edu/blurbs/gradnumthy/dedekindf.pdf) as a corollary of this statement. 
For previous discussion concerning the structure of this PR and the results it proves, see [#9345](https://github.com/leanprover-community/mathlib/pull/9345)
#### Estimated changes
Modified src/algebra/hom/equiv.lean
- \+ *lemma* mul_equiv.of_bijective_apply_symm_apply

Modified src/data/nat/enat.lean
- \+ *lemma* enat.not_dom_iff_eq_top

Modified src/ring_theory/chain_of_divisors.lean
- \+ *lemma* coe_factor_order_iso_map_eq_one_iff
- \+ *lemma* factor_order_iso_map_one_eq_bot
- \+ *lemma* map_prime_of_factor_order_iso
- \+ *lemma* mem_normalized_factors_factor_dvd_iso_of_mem_normalized_factors
- \+ *lemma* mem_normalized_factors_factor_order_iso_of_mem_normalized_factors
- \+ *def* mk_factor_order_iso_of_factor_dvd_equiv
- \+ *lemma* multiplicity_eq_multiplicity_factor_dvd_iso_of_mem_normalized_factor
- \+ *lemma* multiplicity_prime_eq_multiplicity_image_by_factor_order_iso
- \+/\- *lemma* multiplicity_prime_le_multiplicity_image_by_factor_order_iso
- \+/\- *lemma* pow_image_of_prime_by_factor_order_iso_dvd

Modified src/ring_theory/dedekind_domain/ideal.lean
- \+ *def* ideal_factors_equiv_of_quot_equiv
- \+ *def* ideal_factors_fun_of_quot_hom
- \+ *lemma* ideal_factors_fun_of_quot_hom_comp
- \+ *lemma* ideal_factors_fun_of_quot_hom_id

Modified src/ring_theory/multiplicity.lean
- \+ *lemma* multiplicity.multiplicity_mk_eq_multiplicity



## [2022-07-02 12:02:23](https://github.com/leanprover-community/mathlib/commit/4823da2)
feat(data/nat/basic): add `mul_div_mul_comm_of_dvd_dvd` ([#15031](https://github.com/leanprover-community/mathlib/pull/15031))
Add lemma `mul_div_mul_comm_of_dvd_dvd (hac : c ∣ a) (hbd : d ∣ b) : (a * b) / (c * d) = (a / c) * (b / d)`
(Compare with `mul_div_mul_comm`, which holds for a `division_comm_monoid`)
Also adds the same lemma for a `euclidean_domain`.
#### Estimated changes
Modified src/algebra/euclidean_domain.lean
- \+ *lemma* euclidean_domain.mul_div_mul_comm_of_dvd_dvd

Modified src/data/nat/basic.lean
- \+ *lemma* nat.mul_div_mul_comm_of_dvd_dvd



## [2022-07-02 10:12:17](https://github.com/leanprover-community/mathlib/commit/2d76f56)
chore(algebra/associated): make `irreducible` not a class ([#14713](https://github.com/leanprover-community/mathlib/pull/14713))
This functionality was rarely used and doesn't align with how `irreducible` is used in practice.
In a future PR, we can remove some `unfreezingI`s caused by this.
#### Estimated changes
Modified src/algebra/associated.lean
- \- *lemma* irreducible.not_unit

Modified src/algebra/module/pid.lean


Modified src/field_theory/adjoin.lean


Modified src/field_theory/normal.lean


Modified src/field_theory/separable_degree.lean
- \+ *lemma* irreducible.has_separable_contraction
- \- *lemma* polynomial.irreducible_has_separable_contraction

Modified src/field_theory/splitting_field.lean
- \+ *lemma* polynomial.fact_irreducible_factor
- \+ *lemma* polynomial.irreducible_factor

Modified src/number_theory/number_field.lean


Modified src/ring_theory/adjoin_root.lean
- \+ *lemma* adjoin_root.coe_injective'
- \+/\- *lemma* adjoin_root.coe_injective
- \+/\- *lemma* adjoin_root.mul_div_root_cancel



## [2022-07-02 04:29:20](https://github.com/leanprover-community/mathlib/commit/855ed5c)
chore(scripts): update nolints.txt ([#15090](https://github.com/leanprover-community/mathlib/pull/15090))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-07-01 20:56:46](https://github.com/leanprover-community/mathlib/commit/5654410)
chore(group_theory/group_action/opposite): add a missed smul/scalar rename ([#15082](https://github.com/leanprover-community/mathlib/pull/15082))
…ename
#### Estimated changes
Modified scripts/nolints.txt


Modified src/data/matrix/basic.lean


Modified src/group_theory/group_action/opposite.lean




## [2022-07-01 20:56:45](https://github.com/leanprover-community/mathlib/commit/774e680)
feat(data/fintype/basic): add noncomputable equivalences between finsets as fintypes and `fin s.card`, etc. ([#15080](https://github.com/leanprover-community/mathlib/pull/15080))
As `s.card` is not defeq to `fintype.card s`, it is convenient to have these definitions in addition to `fintype.equiv_fin` and others (though we omit the computable ones).
#### Estimated changes
Modified src/data/fintype/basic.lean




## [2022-07-01 20:56:44](https://github.com/leanprover-community/mathlib/commit/9fcf391)
chore(group_theory/group_action/basic): relax monoid to mul_one_class ([#15051](https://github.com/leanprover-community/mathlib/pull/15051))
#### Estimated changes
Modified src/group_theory/group_action/defs.lean
- \+/\- *lemma* smul_one_mul



## [2022-07-01 20:56:43](https://github.com/leanprover-community/mathlib/commit/e94e5c0)
feat(topology/uniform_space/basic): uniform continuity from/to an infimum of uniform spaces ([#14892](https://github.com/leanprover-community/mathlib/pull/14892))
This adds uniform versions of various topological lemmas about continuity from/to infimas of topological spaces
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+ *lemma* uniform_continuous_Inf_dom
- \+ *lemma* uniform_continuous_Inf_dom₂
- \+ *lemma* uniform_continuous_Inf_rng
- \+ *lemma* uniform_continuous_inf_dom_left
- \+ *lemma* uniform_continuous_inf_dom_left₂
- \+ *lemma* uniform_continuous_inf_dom_right
- \+ *lemma* uniform_continuous_inf_dom_right₂
- \+ *lemma* uniform_continuous_inf_rng
- \+ *lemma* uniform_continuous_infi_dom
- \+ *lemma* uniform_continuous_infi_rng



## [2022-07-01 18:31:15](https://github.com/leanprover-community/mathlib/commit/ff5e97a)
feat(order/lattice, data/set): some helper lemmas ([#14789](https://github.com/leanprover-community/mathlib/pull/14789))
This PR provides lemmas describing when `s ∪ a = t ∪ a`, in both necessary and iff forms, as well as intersection and lattice versions.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.inter_eq_inter_iff_subset_subset
- \+ *lemma* set.inter_eq_inter_of_subset_of_subset
- \+ *lemma* set.union_eq_union_iff_subset_subset
- \+ *lemma* set.union_eq_union_of_subset_of_subset

Modified src/order/lattice.lean
- \+ *lemma* inf_eq_inf_iff_le_le
- \+ *lemma* inf_eq_inf_of_le_of_le
- \+ *lemma* sup_eq_sup_iff_le_le
- \+ *lemma* sup_eq_sup_of_le_of_le



## [2022-07-01 18:31:14](https://github.com/leanprover-community/mathlib/commit/7f95e22)
feat(linear_algebra/*): add lemma `linear_independent.finite_of_is_noetherian` ([#14714](https://github.com/leanprover-community/mathlib/pull/14714))
This replaces `fintype_of_is_noetherian_linear_independent` which gave the same
conclusion except demanded `strong_rank_condition R` instead of just `nontrivial R`.
Also some other minor gaps filled.
#### Estimated changes
Modified src/algebra/module/torsion.lean
- \+ *lemma* ideal.complete_lattice.independent.linear_independent'
- \+ *lemma* ideal.torsion_of_eq_bot_iff_of_no_zero_smul_divisors
- \+ *lemma* ideal.torsion_of_eq_top_iff
- \+ *lemma* ideal.torsion_of_zero

Modified src/analysis/box_integral/partition/measure.lean


Modified src/data/finite/set.lean
- \+ *lemma* finite.of_injective_finite_range

Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/dfinsupp.lean
- \+ *lemma* complete_lattice.independent_iff_linear_independent_of_ne_zero

Modified src/linear_algebra/dimension.lean
- \- *lemma* finite_of_is_noetherian_linear_independent
- \+ *lemma* linear_independent.finite_of_is_noetherian
- \+ *lemma* linear_independent.set_finite_of_is_noetherian

Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent.independent_span_singleton

Modified src/linear_algebra/matrix/diagonal.lean


Modified src/linear_algebra/span.lean
- \+/\- *lemma* linear_map.to_span_singleton_one
- \+ *lemma* linear_map.to_span_singleton_zero
- \+/\- *lemma* submodule.span_eq_supr_of_singleton_spans
- \+ *lemma* submodule.span_range_eq_supr

Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/integral/divergence_theorem.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/order/compactly_generated.lean
- \+ *lemma* complete_lattice.well_founded.finite_of_independent

Modified src/order/sup_indep.lean
- \+ *lemma* complete_lattice.independent.comp'
- \+/\- *lemma* complete_lattice.independent.comp
- \+ *lemma* complete_lattice.independent.injective
- \+/\- *lemma* complete_lattice.independent.mono
- \+ *lemma* complete_lattice.independent.set_independent_range
- \+/\- *theorem* complete_lattice.independent_def''
- \+/\- *theorem* complete_lattice.independent_def'



## [2022-07-01 14:39:25](https://github.com/leanprover-community/mathlib/commit/2ae2065)
chore(data/set,topology): fix 2 lemma names ([#15079](https://github.com/leanprover-community/mathlib/pull/15079))
* rename `set.quot_mk_range_eq` to `set.range_quotient_mk`;
* rename `is_closed_infi_iff` to `is_closed_supr_iff`.
#### Estimated changes
Modified src/data/set/basic.lean
- \- *theorem* set.quot_mk_range_eq
- \+ *theorem* set.range_quotient_mk

Modified src/topology/order.lean
- \- *lemma* is_closed_infi_iff
- \+ *lemma* is_closed_supr_iff



## [2022-07-01 14:39:24](https://github.com/leanprover-community/mathlib/commit/8b69a4b)
feat(ring_theory): Some missing lemmas ([#15064](https://github.com/leanprover-community/mathlib/pull/15064))
#### Estimated changes
Modified src/algebra/algebra/subalgebra/basic.lean


Modified src/linear_algebra/span.lean
- \+ *lemma* submodule.closure_le_to_add_submonoid_span
- \+ *lemma* submodule.closure_subset_span
- \+ *lemma* submodule.span_closure

Modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* algebra.adjoin_span

Modified src/ring_theory/finiteness.lean
- \+ *lemma* algebra.finite_type.is_noetherian_ring
- \+ *lemma* subalgebra.fg_iff_finite_type

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* submodule.smul_inf_le

Modified src/ring_theory/noetherian.lean
- \+ *lemma* submodule.fg_bsupr
- \+ *lemma* submodule.fg_finset_sup
- \+ *lemma* submodule.fg_supr



## [2022-07-01 14:39:22](https://github.com/leanprover-community/mathlib/commit/36ee9af)
feat(topology/separation): `separation_quotient α` is a T₀ space ([#15043](https://github.com/leanprover-community/mathlib/pull/15043))
#### Estimated changes
Modified src/topology/separation.lean




## [2022-07-01 14:39:20](https://github.com/leanprover-community/mathlib/commit/0369f20)
feat(order/locally_finite): make `fintype.to_locally_finite_order` computable ([#14733](https://github.com/leanprover-community/mathlib/pull/14733))
#### Estimated changes
Modified src/data/set/intervals/basic.lean


Modified src/order/locally_finite.lean
- \+ *def* fintype.to_locally_finite_order

Modified test/instance_diamonds.lean




## [2022-07-01 12:26:35](https://github.com/leanprover-community/mathlib/commit/0522ee0)
refactor(ring_theory/jacobson): remove unnecessary `fintype.trunc_equiv_fin` ([#15077](https://github.com/leanprover-community/mathlib/pull/15077))
#### Estimated changes
Modified src/ring_theory/jacobson.lean




## [2022-07-01 12:26:34](https://github.com/leanprover-community/mathlib/commit/640955c)
refactor(ring_theory/finiteness): remove unnecessary `fintype.trunc_equiv_fin` ([#15076](https://github.com/leanprover-community/mathlib/pull/15076))
#### Estimated changes
Modified src/ring_theory/finiteness.lean




## [2022-07-01 12:26:33](https://github.com/leanprover-community/mathlib/commit/f9b939c)
feat(data/nat/enat): simple lemmas on `enat` ([#15029](https://github.com/leanprover-community/mathlib/pull/15029))
#### Estimated changes
Modified src/data/nat/enat.lean
- \+ *lemma* enat.eq_zero_iff
- \+ *lemma* enat.ne_zero_iff
- \+ *lemma* enat.not_is_max_coe



## [2022-07-01 12:26:32](https://github.com/leanprover-community/mathlib/commit/6e362f6)
chore(algebra/order/monoid): golf proofs, fix docs ([#14728](https://github.com/leanprover-community/mathlib/pull/14728))
#### Estimated changes
Modified src/algebra/order/monoid.lean




## [2022-07-01 10:20:04](https://github.com/leanprover-community/mathlib/commit/9e97baa)
feat(data/list/basic): add filter_map_join ([#14777](https://github.com/leanprover-community/mathlib/pull/14777))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.filter_map_join



## [2022-07-01 10:20:03](https://github.com/leanprover-community/mathlib/commit/e73ac94)
feat (analysis/normed_space/lp_space):add l_infinity ring instances ([#14104](https://github.com/leanprover-community/mathlib/pull/14104))
We define pointwise multiplication on `lp E ∞` and give it has_mul, non_unital_ring, non_unital_normed_ring, ring, normed_ring, comm_ring and normed_comm_ring instances under the appropriate assumptions.
#### Estimated changes
Modified src/analysis/normed_space/lp_space.lean
- \+ *lemma* int_cast_mem_ℓp_infty
- \+ *lemma* lp.infty_coe_fn_int_cast
- \+ *lemma* lp.infty_coe_fn_mul
- \+ *lemma* lp.infty_coe_fn_nat_cast
- \+ *lemma* lp.infty_coe_fn_one
- \+ *lemma* lp.infty_coe_fn_pow
- \+ *lemma* mem_ℓp.infty_mul
- \+ *lemma* mem_ℓp.infty_pow
- \+ *lemma* nat_cast_mem_ℓp_infty
- \+ *lemma* one_mem_ℓp_infty



## [2022-07-01 08:11:22](https://github.com/leanprover-community/mathlib/commit/ce332c1)
refactor(algebra/group_power): split ring lemmas into a separate file ([#15032](https://github.com/leanprover-community/mathlib/pull/15032))
This doesn't actually stop `algebra.ring.basic` being imported into `group_power.basic` yet, but it makes it easier to make that change in future. Two ~300 line files are also slightly easier to manage than one ~600 line file, and ring/add_group feels like a natural place to draw the line
All lemmas have just been moved, and none have been renamed. Some lemmas have had their `R` variables renamed to `M` to better reflect that they apply to monoids with zero.
By grouping together the `monoid_with_zero` lemmas from separate files, it become apparent that there's some overlap.
This PR does not attempt to clean this up, in the interest of limiting the the scope of this change to just moves.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \- *lemma* add_sq'
- \- *lemma* add_sq
- \- *lemma* coe_pow_monoid_with_zero_hom
- \- *lemma* eq_or_eq_neg_of_sq_eq_sq
- \- *lemma* min_pow_dvd_add
- \- *lemma* mul_neg_one_pow_eq_zero_iff
- \- *theorem* neg_one_pow_eq_or
- \- *lemma* neg_one_pow_mul_eq_zero_iff
- \- *lemma* neg_one_sq
- \- *theorem* neg_pow
- \- *theorem* neg_pow_bit0
- \- *theorem* neg_pow_bit1
- \- *lemma* neg_sq
- \- *lemma* pow_dvd_pow_iff
- \- *theorem* pow_eq_zero
- \- *lemma* pow_eq_zero_iff'
- \- *lemma* pow_eq_zero_iff
- \- *lemma* pow_eq_zero_of_le
- \- *def* pow_monoid_with_zero_hom
- \- *lemma* pow_monoid_with_zero_hom_apply
- \- *theorem* pow_ne_zero
- \- *lemma* pow_ne_zero_iff
- \- *lemma* sq_eq_one_iff
- \- *lemma* sq_eq_sq_iff_eq_or_eq_neg
- \- *theorem* sq_eq_zero_iff
- \- *lemma* sq_ne_one_iff
- \- *lemma* sq_sub_sq
- \- *lemma* sub_sq'
- \- *lemma* sub_sq
- \- *lemma* zero_pow
- \- *lemma* zero_pow_eq

Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/group_power/order.lean


Added src/algebra/group_power/ring.lean
- \+ *lemma* add_sq'
- \+ *lemma* add_sq
- \+ *lemma* coe_pow_monoid_with_zero_hom
- \+ *lemma* eq_or_eq_neg_of_sq_eq_sq
- \+ *lemma* min_pow_dvd_add
- \+ *lemma* mul_neg_one_pow_eq_zero_iff
- \+ *lemma* ne_zero_pow
- \+ *theorem* neg_one_pow_eq_or
- \+ *lemma* neg_one_pow_mul_eq_zero_iff
- \+ *lemma* neg_one_sq
- \+ *theorem* neg_pow
- \+ *theorem* neg_pow_bit0
- \+ *theorem* neg_pow_bit1
- \+ *lemma* neg_sq
- \+ *lemma* pow_dvd_pow_iff
- \+ *theorem* pow_eq_zero
- \+ *lemma* pow_eq_zero_iff'
- \+ *lemma* pow_eq_zero_iff
- \+ *lemma* pow_eq_zero_of_le
- \+ *def* pow_monoid_with_zero_hom
- \+ *lemma* pow_monoid_with_zero_hom_apply
- \+ *theorem* pow_ne_zero
- \+ *lemma* pow_ne_zero_iff
- \+ *lemma* ring.inverse_pow
- \+ *lemma* sq_eq_one_iff
- \+ *lemma* sq_eq_sq_iff_eq_or_eq_neg
- \+ *theorem* sq_eq_zero_iff
- \+ *lemma* sq_ne_one_iff
- \+ *lemma* sq_sub_sq
- \+ *lemma* sub_sq'
- \+ *lemma* sub_sq
- \+ *lemma* zero_pow'
- \+ *lemma* zero_pow
- \+ *lemma* zero_pow_eq
- \+ *lemma* zero_pow_eq_zero

Modified src/algebra/group_with_zero/power.lean
- \- *lemma* ne_zero_pow
- \- *lemma* ring.inverse_pow
- \- *lemma* zero_pow'
- \- *lemma* zero_pow_eq_zero



## [2022-07-01 04:21:43](https://github.com/leanprover-community/mathlib/commit/7e244d8)
feat(algebra/category/Module): upgrade `free : Type ⥤ Module R` to a monoidal functor ([#14328](https://github.com/leanprover-community/mathlib/pull/14328))
#### Estimated changes
Modified src/algebra/category/Module/adjunctions.lean
- \+ *lemma* Module.free.ε_apply
- \+/\- *def* Module.free.μ
- \+ *def* Module.monoidal_free

