## [2021-01-31 18:12:02](https://github.com/leanprover-community/mathlib/commit/a15e64a)
refactor(data/polynomial/degree/definitions): rw -> exact, use term mode proof ([#5946](https://github.com/leanprover-community/mathlib/pull/5946))
Co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean




## [2021-01-31 06:59:28](https://github.com/leanprover-community/mathlib/commit/4f4a9b5)
feat(analysis/analytic/inverse): inverse of a formal multilinear series ([#5852](https://github.com/leanprover-community/mathlib/pull/5852))
We construct the left inverse and a right inverse of a formal multilinear series with invertible first term, and we show that they coincide.
#### Estimated changes
Modified src/analysis/analytic/composition.lean


Created src/analysis/analytic/inverse.lean
- \+ *lemma* left_inv_coeff_zero
- \+ *lemma* left_inv_coeff_one
- \+ *lemma* left_inv_remove_zero
- \+ *lemma* left_inv_comp
- \+ *lemma* right_inv_coeff_zero
- \+ *lemma* right_inv_coeff_one
- \+ *lemma* right_inv_remove_zero
- \+ *lemma* comp_right_inv_aux1
- \+ *lemma* comp_right_inv_aux2
- \+ *lemma* comp_right_inv
- \+ *lemma* right_inv_coeff
- \+ *theorem* left_inv_eq_right_inv



## [2021-01-31 01:46:38](https://github.com/leanprover-community/mathlib/commit/1ea538b)
chore(scripts): update nolints.txt ([#5976](https://github.com/leanprover-community/mathlib/pull/5976))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-30 22:44:52](https://github.com/leanprover-community/mathlib/commit/ae1b530)
chore(algebra/algebra/basic): add simp lemma about `algebra_map ℚ` ([#5970](https://github.com/leanprover-community/mathlib/pull/5970))
Since there is a subsingleton instance over ring_homs, we may as well let the simplifier replace `algebra_map` with `id`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *theorem* algebra_map_rat_rat



## [2021-01-30 22:44:50](https://github.com/leanprover-community/mathlib/commit/f596077)
feat(geometry/manifold/instances): sphere is a topological manifold ([#5591](https://github.com/leanprover-community/mathlib/pull/5591))
Construct stereographic projection, as a local homeomorphism from the unit sphere in an inner product space `E` to a hyperplane in `E`.  Make a charted space instance for the sphere, with these stereographic projections as the atlas.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *lemma* abs_sq_eq

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_on.inv
- \+ *lemma* times_cont_diff.inv
- \+ *lemma* times_cont_diff_on.div

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* coe_norm

Modified src/analysis/normed_space/inner_product.lean
- \+/\- *lemma* findim_orthogonal_span_singleton
- \+ *def* linear_isometry_equiv.from_orthogonal_span_singleton

Created src/geometry/manifold/instances/sphere.lean
- \+ *lemma* stereo_to_fun_apply
- \+ *lemma* times_cont_diff_on_stereo_to_fun
- \+ *lemma* continuous_on_stereo_to_fun
- \+ *lemma* stereo_inv_fun_aux_apply
- \+ *lemma* stereo_inv_fun_aux_mem
- \+ *lemma* times_cont_diff_stereo_inv_fun_aux
- \+ *lemma* stereo_inv_fun_apply
- \+ *lemma* stereo_inv_fun_ne_north_pole
- \+ *lemma* continuous_stereo_inv_fun
- \+ *lemma* stereo_left_inv
- \+ *lemma* stereo_right_inv
- \+ *lemma* stereographic_source
- \+ *lemma* stereographic_target
- \+ *lemma* stereographic'_source
- \+ *lemma* stereographic'_target
- \+ *def* stereo_to_fun
- \+ *def* stereo_inv_fun_aux
- \+ *def* stereo_inv_fun
- \+ *def* stereographic
- \+ *def* stereographic'

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_on.smul



## [2021-01-30 20:09:59](https://github.com/leanprover-community/mathlib/commit/a6c0442)
feat(field_theory/normal): Restriction is surjective ([#5960](https://github.com/leanprover-community/mathlib/pull/5960))
Proves surjectivity of `alg_equiv.restrict_normal_hom`.
Also proves a bijectivity lemma which gives a cleaner construction of `alg_equiv.restrict_normal`.
#### Estimated changes
Modified src/field_theory/normal.lean
- \+ *lemma* alg_hom.normal_bijective
- \+/\- *lemma* alg_hom.restrict_normal_commutes
- \+/\- *lemma* alg_equiv.restrict_normal_commutes
- \+ *lemma* alg_hom.lift_normal_commutes
- \+ *lemma* alg_hom.restrict_lift_normal
- \+ *lemma* alg_equiv.lift_normal_commutes
- \+ *lemma* alg_equiv.restrict_lift_normal
- \+ *lemma* alg_equiv.restrict_normal_hom_surjective



## [2021-01-30 20:09:57](https://github.com/leanprover-community/mathlib/commit/48d0592)
feat(algebra/lie/basic): define derived length and semisimple Lie algebras ([#5930](https://github.com/leanprover-community/mathlib/pull/5930))
We also provide proofs of some basic characterisations
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/lie/basic.lean
- \+ *lemma* bijective
- \+ *lemma* injective
- \+ *lemma* surjective
- \+ *lemma* function.injective.is_lie_abelian
- \+ *lemma* function.surjective.is_lie_abelian
- \+ *lemma* lie_abelian_iff_equiv_lie_abelian
- \+/\- *lemma* ext_iff
- \+ *lemma* coe_zero_iff_zero
- \+ *lemma* ext_iff'
- \+ *lemma* hom_of_le_injective
- \+ *lemma* lie_abelian_iff_lie_self_eq_bot
- \+ *lemma* derived_series_of_bot_eq_bot
- \+ *lemma* abelian_iff_derived_one_eq_bot
- \+ *lemma* abelian_iff_derived_succ_eq_bot
- \+ *lemma* trivial_iff_lower_central_eq_bot
- \+ *lemma* ker_eq_bot
- \+ *lemma* bot_of_map_eq_bot
- \+ *lemma* coe_hom_of_le
- \+ *lemma* hom_of_le_apply
- \+ *lemma* derived_series_map_le_derived_series
- \+ *lemma* top_equiv_self_apply
- \+ *lemma* is_solvable_of_injective
- \+ *lemma* le_solvable_ideal_solvable
- \+ *lemma* derived_series_of_derived_length_succ
- \+ *lemma* derived_length_zero
- \+ *lemma* derived_length_eq_derived_length_of_ideal
- \+ *lemma* is_lie_abelian_bot
- \+ *lemma* abelian_derived_abelian_of_ideal
- \+ *lemma* abelian_of_solvable_ideal_eq_bot_iff
- \+ *lemma* of_abelian_is_solvable
- \+ *lemma* lie_ideal.solvable_iff_le_radical
- \+ *lemma* is_semisimple_iff_no_solvable_ideals
- \+ *lemma* is_semisimple_iff_no_abelian_ideals
- \- *lemma* trivial_iff_derived_eq_bot
- \+ *def* hom_of_le
- \+ *def* top_equiv_self

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* nonempty_of_pos_Inf
- \+ *lemma* nonempty_of_Inf_eq_succ
- \+ *lemma* eq_Ici_of_nonempty_of_upward_closed
- \+ *lemma* Inf_upward_closed_eq_succ_iff



## [2021-01-30 18:21:17](https://github.com/leanprover-community/mathlib/commit/539550d)
feat(topology/instances/nnreal): add has_sum_nat_add_iff and module docstring ([#5716](https://github.com/leanprover-community/mathlib/pull/5716))
#### Estimated changes
Modified src/topology/instances/nnreal.lean
- \+ *lemma* has_sum_nat_add_iff



## [2021-01-30 14:50:34](https://github.com/leanprover-community/mathlib/commit/d6fe605)
chore(*): split some long lines ([#5959](https://github.com/leanprover-community/mathlib/pull/5959))
#### Estimated changes
Modified src/category_theory/elements.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/is_connected.lean
- \+/\- *lemma* is_connected.of_induct

Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/preserves/basic.lean


Modified src/data/bitvec/basic.lean


Modified src/data/complex/exponential.lean
- \+/\- *theorem* cos_add_sin_mul_I_pow

Modified src/data/equiv/mul_add.lean


Modified src/data/holor.lean


Modified src/data/matrix/pequiv.lean
- \+/\- *lemma* single_mul_single_right
- \+/\- *lemma* equiv_to_pequiv_to_matrix

Modified src/data/multiset/basic.lean
- \+/\- *lemma* bind_congr
- \+/\- *lemma* exists_mem_of_rel_of_mem
- \+/\- *theorem* erase_cons_tail
- \+/\- *theorem* map_map
- \+/\- *theorem* map_congr
- \+/\- *theorem* eq_of_mem_map_const
- \+/\- *theorem* foldl_cons
- \+/\- *theorem* foldl_add
- \+/\- *theorem* foldr_cons
- \+/\- *theorem* foldr_add
- \+/\- *theorem* card_product
- \+/\- *theorem* map_union
- \+/\- *theorem* count_erase_self
- \+/\- *theorem* count_erase_of_ne
- \+/\- *theorem* count_union
- \+/\- *theorem* count_inter

Modified src/group_theory/free_abelian_group.lean
- \+/\- *lemma* map_add
- \+/\- *lemma* map_sub
- \+/\- *lemma* add_bind
- \+/\- *lemma* neg_bind
- \+/\- *lemma* sub_bind
- \+/\- *lemma* add_seq
- \+/\- *lemma* neg_seq
- \+/\- *lemma* sub_seq
- \+/\- *lemma* seq_add
- \+/\- *lemma* seq_neg
- \+/\- *lemma* seq_sub

Modified src/ring_theory/polynomial/basic.lean
- \+/\- *theorem* coeff_restriction
- \+/\- *theorem* coeff_restriction'
- \+/\- *theorem* nat_degree_restriction

Modified src/topology/algebra/group.lean


Modified src/topology/algebra/module.lean
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_sub

Modified src/topology/metric_space/emetric_space.lean
- \+/\- *lemma* diam_union
- \+/\- *theorem* uniformity_dist_of_mem_uniformity

Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified test/general_recursion.lean
- \+/\- *theorem* tree_map.cont
- \+/\- *theorem* tree_map.equations.eqn_1
- \+/\- *theorem* tree_map.equations.eqn_2
- \+/\- *theorem* tree_map'.cont
- \+/\- *def* tree_map.intl
- \+/\- *def* tree_map'.intl



## [2021-01-30 10:07:38](https://github.com/leanprover-community/mathlib/commit/8069521)
feat(measure_theory): Absolute continuity ([#5948](https://github.com/leanprover-community/mathlib/pull/5948))
* Define absolute continuity between measures (@mzinkevi)
* State monotonicity of `ae_measurable` w.r.t. absolute continuity
* Weaken some `measurable` assumptions in `prod.lean` to `ae_measurable`
* Some docstring fixes
* Some cleanup
#### Estimated changes
Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/group.lean


Modified src/measure_theory/haar_measure.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/measure_space.lean
- \+ *lemma* preimage_null_of_map_null
- \+ *lemma* absolutely_continuous.mk
- \+ *lemma* absolutely_continuous.refl
- \+ *lemma* absolutely_continuous.rfl
- \+ *lemma* absolutely_continuous_of_eq
- \+ *lemma* absolutely_continuous.trans
- \+ *lemma* ae_eq_comp'
- \+ *lemma* comp_measurable'
- \+/\- *def* to_measurable
- \+ *def* absolutely_continuous

Modified src/measure_theory/prod.lean
- \+ *lemma* prod_fst_absolutely_continuous
- \+ *lemma* prod_snd_absolutely_continuous
- \+/\- *lemma* ae_measurable.prod_swap
- \+ *lemma* ae_measurable.fst
- \+ *lemma* ae_measurable.snd
- \+ *lemma* lintegral_prod_of_measurable
- \+/\- *lemma* lintegral_prod
- \+/\- *lemma* lintegral_prod_mul
- \- *lemma* lintegral_prod'

Modified src/measure_theory/prod_group.lean


Modified src/topology/subset_properties.lean
- \+/\- *lemma* compact_pi_infinite
- \+/\- *lemma* compact_univ_pi



## [2021-01-30 08:05:04](https://github.com/leanprover-community/mathlib/commit/cf21863)
doc(group_theory/order_of_element): Adding doc string ([#5936](https://github.com/leanprover-community/mathlib/pull/5936))
#### Estimated changes
Modified src/group_theory/order_of_element.lean




## [2021-01-30 06:47:28](https://github.com/leanprover-community/mathlib/commit/cbcbaa0)
feat(topology/category): compact hausdorff spaces are reflective in Top ([#5955](https://github.com/leanprover-community/mathlib/pull/5955))
Show explicitly that `CompHaus_to_Top` is a reflective functor via the Stone-Cech compactification.
#### Estimated changes
Modified src/topology/category/CompHaus.lean
- \+ *lemma* Top_to_CompHaus_obj
- \+ *def* StoneCech_obj



## [2021-01-30 01:48:52](https://github.com/leanprover-community/mathlib/commit/b44e9dd)
chore(scripts): update nolints.txt ([#5965](https://github.com/leanprover-community/mathlib/pull/5965))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-29 21:16:04](https://github.com/leanprover-community/mathlib/commit/686d005)
chore(*): fix some "line too long" lint errors by rewriting proofs/statements ([#5958](https://github.com/leanprover-community/mathlib/pull/5958))
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/composition.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/topology/algebra/group.lean




## [2021-01-29 19:10:11](https://github.com/leanprover-community/mathlib/commit/e8e0526)
feat(field_theory/polynomial_galois_group): New file ([#5861](https://github.com/leanprover-community/mathlib/pull/5861))
This PR adds the file `polynomial_galois_group`. It contains some of the groundwork needed for proving the Abel-Ruffini theorem.
#### Estimated changes
Modified src/data/polynomial/field_division.lean
- \+ *lemma* mem_root_set

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* root_set_def
- \+ *lemma* root_set_zero
- \+ *def* root_set

Modified src/field_theory/normal.lean
- \+/\- *lemma* normal.of_is_splitting_field

Created src/field_theory/polynomial_galois_group.lean
- \+ *lemma* map_roots_bijective
- \+ *lemma* restrict_smul
- \+ *lemma* gal_action_hom_injective
- \+ *lemma* restrict_prod_injective
- \+ *lemma* card_of_separable
- \+ *lemma* prime_degree_dvd_card
- \+ *def* gal
- \+ *def* restrict
- \+ *def* map_roots
- \+ *def* roots_equiv_roots
- \+ *def* gal_action_hom
- \+ *def* restrict_dvd
- \+ *def* restrict_prod

Modified src/field_theory/splitting_field.lean
- \+ *theorem* adjoin_root_set



## [2021-01-29 17:21:20](https://github.com/leanprover-community/mathlib/commit/62cf420)
ci(lint-style): adjust output to integrate with github ([#5952](https://github.com/leanprover-community/mathlib/pull/5952))
#### Estimated changes
Modified scripts/lint-style.py
- \+ *def* output_message(path,

Modified scripts/lint_style_sanity_test.py




## [2021-01-29 17:21:18](https://github.com/leanprover-community/mathlib/commit/657cfeb)
doc(algebra/polynomial/big_operators): add / fix docstrings and lint ([#5950](https://github.com/leanprover-community/mathlib/pull/5950))
#### Estimated changes
Modified src/algebra/polynomial/big_operators.lean




## [2021-01-29 17:21:16](https://github.com/leanprover-community/mathlib/commit/aabb843)
feat(analysis/normed_space/inner_product): existence of isometry to Euclidean space ([#5949](https://github.com/leanprover-community/mathlib/pull/5949))
A finite-dimensional inner product space admits an isometry (expressed using the new `linear_isometry_equiv` structure of [#5867](https://github.com/leanprover-community/mathlib/pull/5867), cc @urkud) to Euclidean space.
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* orthonormal.inner_right_fintype
- \+ *lemma* orthonormal.inner_left_fintype
- \+ *lemma* orthonormal.comp
- \+ *lemma* pi_Lp.inner_apply
- \+ *lemma* is_R_or_C.inner_apply
- \+ *lemma* exists_is_orthonormal_basis'
- \+ *def* is_basis.isometry_euclidean_of_orthonormal
- \+ *def* linear_isometry_equiv.of_inner_product_space
- \- *def* is_basis.equiv_fun_euclidean

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* equiv_fin_of_dim_eq



## [2021-01-29 17:21:14](https://github.com/leanprover-community/mathlib/commit/0d18179)
chore(analysis/normed_space/multilinear): rename variables ([#5929](https://github.com/leanprover-community/mathlib/pull/5929))
Use `E` and `E'` for indexed types and `G` and `G'` for `Type*`s.
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean
- \+/\- *lemma* restr_norm_le
- \+/\- *lemma* bounds_nonempty
- \+/\- *lemma* bounds_bdd_below
- \+/\- *lemma* norm_image_sub_le'
- \+/\- *lemma* norm_image_sub_le
- \+/\- *lemma* continuous_eval_left
- \+/\- *lemma* multilinear_map.mk_continuous_norm_le
- \+/\- *lemma* norm_restr
- \+/\- *lemma* mk_pi_field_apply
- \+/\- *lemma* mk_pi_field_apply_one_eq_self
- \+/\- *lemma* continuous_multilinear_map.curry0_apply
- \+/\- *lemma* continuous_multilinear_map.uncurry0_apply
- \+/\- *lemma* continuous_multilinear_map.apply_zero_curry0
- \+/\- *lemma* continuous_multilinear_map.uncurry0_curry0
- \+/\- *lemma* continuous_multilinear_map.curry0_uncurry0
- \+/\- *lemma* continuous_multilinear_map.uncurry0_norm
- \+/\- *lemma* continuous_multilinear_map.fin0_apply_norm
- \+/\- *lemma* continuous_multilinear_map.curry0_norm
- \+/\- *lemma* continuous_multilinear_curry_fin0_apply
- \+/\- *lemma* continuous_multilinear_curry_fin0_symm_apply
- \+/\- *lemma* continuous_multilinear_curry_fin1_apply
- \+/\- *def* restr
- \+/\- *def* continuous_multilinear_map.curry0
- \+/\- *def* continuous_multilinear_curry_fin0_aux
- \+/\- *def* continuous_multilinear_curry_fin0
- \+/\- *def* continuous_multilinear_curry_fin1



## [2021-01-29 15:28:07](https://github.com/leanprover-community/mathlib/commit/9c5064c)
chore(linear_algebra/linear_independent): relax requirements to semiring and division_ring ([#5953](https://github.com/leanprover-community/mathlib/pull/5953))
No lemma names or proofs were changed, this just reordered some lemmas so that they could be put into sections with weaker requirements.
#### Estimated changes
Modified src/linear_algebra/linear_independent.lean
- \+/\- *lemma* linear_independent_of_finite
- \+/\- *lemma* linear_independent_Union_of_directed
- \+/\- *lemma* linear_independent_sUnion_of_directed
- \+/\- *lemma* linear_independent_bUnion_of_directed
- \+/\- *lemma* linear_independent.injective
- \+/\- *theorem* linear_independent_iff_injective_total
- \+/\- *theorem* linear_independent.to_subtype_range
- \+/\- *theorem* linear_independent.to_subtype_range'
- \+/\- *theorem* linear_independent.image



## [2021-01-29 14:19:09](https://github.com/leanprover-community/mathlib/commit/783e11a)
fix(scripts): fix mixing absolute and relative paths to the linter ([#5810](https://github.com/leanprover-community/mathlib/pull/5810))
Fix providing either relative or absolute paths to the linter.
Make the linter emit outputted paths corresponding to the ones passed on the command line -- relative if relative, absolute if absolute.
Also adds a short set of tests.
Reported in: https://leanprover.zulipchat.com/#narrow/stream/208328-IMO-grand-challenge/topic/2013.20Q5 (and introduced in [#5721](https://github.com/leanprover-community/mathlib/pull/5721)).
#### Estimated changes
Modified .github/workflows/build.yml


Modified scripts/lint-style.py
- \+/\- *def* small_alpha_vrachy_check(lines,
- \+/\- *def* reserved_notation_check(lines,
- \+/\- *def* set_option_check(lines,
- \+/\- *def* long_lines_check(lines,
- \+/\- *def* import_only_check(lines,
- \+/\- *def* regular_check(lines,
- \+ *def* lint(path):
- \- *def* lint(fn):

Created scripts/lint_style_sanity_test.py




## [2021-01-29 11:30:18](https://github.com/leanprover-community/mathlib/commit/41decdb)
chore(combinatorics/simple_graph/basic): remove classical locale ([#5951](https://github.com/leanprover-community/mathlib/pull/5951))
This completes the simple graph part of the refactor that removed classical fintype instances.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+/\- *lemma* degree_lt_card_verts
- \+/\- *lemma* card_common_neighbors_le_degree_left
- \+/\- *lemma* card_common_neighbors_le_degree_right
- \+/\- *lemma* card_common_neighbors_lt_card_verts
- \+/\- *lemma* adj.card_common_neighbors_lt_degree



## [2021-01-29 11:30:16](https://github.com/leanprover-community/mathlib/commit/15217c2)
refactor(topology/local_homeomorph): simplify `prod_trans` ([#5915](https://github.com/leanprover-community/mathlib/pull/5915))
10X faster elaboration
(pretty-printed) proof term length 14637 -> 2046
Co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/topology/local_homeomorph.lean




## [2021-01-29 09:42:09](https://github.com/leanprover-community/mathlib/commit/bbec099)
refactor(data/real/nnreal): shorter proof of `div_lt_iff` ([#5945](https://github.com/leanprover-community/mathlib/pull/5945))
Co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/data/real/nnreal.lean




## [2021-01-29 06:49:21](https://github.com/leanprover-community/mathlib/commit/145f127)
feat(ring_theory/polynomial/chebyshev/defs): Chebyshev polynomials of the second kind ([#5793](https://github.com/leanprover-community/mathlib/pull/5793))
This will define Chebyshev polynomials of the second kind and introduce some basic properties:
- [x] Define Chebyshev polynomials of the second kind.
- [x] Relate Chebyshev polynomials of the first and second kind through recursive formulae
- [x] Prove trigonometric identity regarding Chebyshev polynomials of the second kind
- [x] Compute the derivative of the Chebyshev polynomials of the first kind in terms of the Chebyshev polynomials of the second kind. 
- [x] Compute the derivative of the Chebyshev polynomials of the second kind in terms of the Chebyshev polynomials of the first kind.
#### Estimated changes
Modified docs/references.bib


Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* chebyshev₂_complex_cos
- \+ *lemma* sin_nat_succ_mul

Modified src/ring_theory/polynomial/chebyshev/defs.lean
- \+ *lemma* chebyshev₂_zero
- \+ *lemma* chebyshev₂_one
- \+ *lemma* chebyshev₂_two
- \+ *lemma* chebyshev₂_add_two
- \+ *lemma* chebyshev₂_of_two_le
- \+ *lemma* chebyshev₂_eq_X_mul_chebyshev₂_add_chebyshev₁
- \+ *lemma* chebyshev₁_eq_chebyshev₂_sub_X_mul_chebyshev₂
- \+ *lemma* chebyshev₁_eq_X_mul_chebyshev₁_sub_pol_chebyshev₂
- \+ *lemma* one_sub_X_pow_two_mul_chebyshev₂_eq_pol_in_chebyshev₁
- \+ *lemma* map_chebyshev₂
- \+ *lemma* chebyshev₁_derivative_eq_chebyshev₂
- \+ *lemma* one_sub_X_pow_two_mul_derivative_chebyshev₁_eq_poly_in_chebyshev₁
- \+ *lemma* add_one_mul_chebyshev₁_eq_poly_in_chebyshev₂



## [2021-01-29 04:36:40](https://github.com/leanprover-community/mathlib/commit/1edd85c)
chore(scripts): update nolints.txt ([#5947](https://github.com/leanprover-community/mathlib/pull/5947))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-29 01:34:13](https://github.com/leanprover-community/mathlib/commit/4dca6e1)
chore(data/fintype/basic): Remove duplicate instance ([#5943](https://github.com/leanprover-community/mathlib/pull/5943))
We already have `subtype.fintype`, there is no need for `fintype.subtype_of_fintype` which does the same thing
#### Estimated changes
Modified src/data/fintype/basic.lean




## [2021-01-28 23:59:53](https://github.com/leanprover-community/mathlib/commit/69e7f14)
chore(combinatorics/simple_graph): generalise decidability proofs ([#5938](https://github.com/leanprover-community/mathlib/pull/5938))
This generalises the decidable instances so they're more applicable, and also golfs the proofs.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean




## [2021-01-28 20:36:43](https://github.com/leanprover-community/mathlib/commit/2cbaa9c)
feat(data/list/basic): add diff_erase ([#5941](https://github.com/leanprover-community/mathlib/pull/5941))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* diff_cons_right
- \+ *lemma* diff_erase



## [2021-01-28 19:15:38](https://github.com/leanprover-community/mathlib/commit/2870212)
chore(data/sym2): golf decidability proofs ([#5940](https://github.com/leanprover-community/mathlib/pull/5940))
This golfs the decidable instances, and removes a redundant one (`from_rel.decidable_as_set` is automatically inferred from `from_rel.decidable_pred`)
#### Estimated changes
Modified src/data/sym2.lean




## [2021-01-28 16:36:05](https://github.com/leanprover-community/mathlib/commit/645dc60)
refactor(analysis/calculus/inverse): inverse of C^k functions over R or C ([#5926](https://github.com/leanprover-community/mathlib/pull/5926))
Some results on the local inverse of smooth functions are currently formulated only for real functions, but they work as well for complex functions. We formulate them uniformly, assuming `is_R_or_C`.
#### Estimated changes
Modified src/analysis/calculus/inverse.lean


Modified src/analysis/calculus/mean_value.lean
- \+ *theorem* is_R_or_C.norm_image_sub_le_of_norm_has_fderiv_within_le'

Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/complex/basic.lean
- \+ *lemma* re_to_complex
- \+ *lemma* im_to_complex
- \+ *lemma* conj_to_complex
- \+ *lemma* I_to_complex
- \+ *lemma* norm_sq_to_complex
- \+ *lemma* abs_to_complex
- \- *theorem* has_deriv_at.real_of_complex
- \- *theorem* times_cont_diff_at.real_of_complex
- \- *theorem* times_cont_diff.real_of_complex

Created src/analysis/complex/real_deriv.lean
- \+ *theorem* has_deriv_at.real_of_complex
- \+ *theorem* times_cont_diff_at.real_of_complex
- \+ *theorem* times_cont_diff.real_of_complex

Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/data/complex/is_R_or_C.lean
- \- *lemma* re_to_complex
- \- *lemma* im_to_complex
- \- *lemma* conj_to_complex
- \- *lemma* I_to_complex
- \- *lemma* norm_sq_to_complex
- \- *lemma* abs_to_complex

Modified src/geometry/euclidean/basic.lean




## [2021-01-28 13:17:00](https://github.com/leanprover-community/mathlib/commit/c43c709)
fix(data/dfinsupp): fix overly strict type-class arguments ([#5935](https://github.com/leanprover-community/mathlib/pull/5935))
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+/\- *lemma* map_dfinsupp_prod
- \+/\- *lemma* coe_dfinsupp_prod
- \+/\- *lemma* dfinsupp_prod_apply



## [2021-01-28 08:12:08](https://github.com/leanprover-community/mathlib/commit/82481e3)
feat(analysis/normed_space/inner_product): existence of orthonormal basis ([#5734](https://github.com/leanprover-community/mathlib/pull/5734))
Define `orthonormal` sets (indexed) of vectors in an inner product space `E`.  Show that a finite-dimensional inner product space has an orthonormal basis.
Co-authored by: Busiso Chisala
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/algebra/group_power/basic.lean
- \+ *lemma* eq_of_pow_two_eq_pow_two

Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* finsupp.sum_inner
- \+ *lemma* finsupp.inner_sum
- \+ *lemma* inner_self_eq_norm_sq_to_K
- \+ *lemma* orthonormal_iff_ite
- \+ *lemma* orthonormal.inner_right_finsupp
- \+ *lemma* orthonormal.inner_left_finsupp
- \+ *lemma* orthonormal.linear_independent
- \+ *lemma* orthonormal.inner_finsupp_eq_zero
- \+ *lemma* orthonormal_empty
- \+ *lemma* orthonormal_Union_of_directed
- \+ *lemma* orthonormal_sUnion_of_directed
- \+ *lemma* exists_maximal_orthonormal
- \+ *lemma* orthonormal.ne_zero
- \+ *lemma* is_basis_of_orthonormal_of_card_eq_findim
- \+ *lemma* submodule.coe_inner
- \+ *lemma* submodule.inf_orthogonal_eq_bot
- \+/\- *lemma* submodule.orthogonal_disjoint
- \+ *lemma* maximal_orthonormal_iff_orthogonal_complement_eq_bot
- \+ *lemma* maximal_orthonormal_iff_dense_span
- \+ *lemma* exists_subset_is_orthonormal_dense_span
- \+ *lemma* exists_is_orthonormal_dense_span
- \+ *lemma* maximal_orthonormal_iff_is_basis_of_finite_dimensional
- \+ *lemma* exists_subset_is_orthonormal_basis
- \+ *lemma* exists_is_orthonormal_basis
- \+ *theorem* orthonormal_subtype_iff_ite
- \+ *def* orthonormal
- \+ *def* is_basis.equiv_fun_euclidean

Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* norm_smul_inv_norm

Modified src/data/finsupp/basic.lean
- \+/\- *lemma* prod_ite_eq
- \+ *lemma* sum_ite_self_eq
- \+/\- *lemma* prod_ite_eq'
- \+ *lemma* sum_ite_self_eq'



## [2021-01-28 01:39:54](https://github.com/leanprover-community/mathlib/commit/9545445)
chore(scripts): update nolints.txt ([#5931](https://github.com/leanprover-community/mathlib/pull/5931))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-27 23:19:08](https://github.com/leanprover-community/mathlib/commit/6585eff)
feat(archive/imo): formalize IMO 2013 problem Q5 ([#5787](https://github.com/leanprover-community/mathlib/pull/5787))
#### Estimated changes
Created archive/imo/imo2013_q5.lean
- \+ *lemma* le_of_all_pow_lt_succ
- \+ *lemma* le_of_all_pow_lt_succ'
- \+ *lemma* f_pos_of_pos
- \+ *lemma* fx_gt_xm1
- \+ *lemma* pow_f_le_f_pow
- \+ *lemma* fixed_point_of_pos_nat_pow
- \+ *lemma* fixed_point_of_gt_1
- \+ *theorem* imo2013_q5



## [2021-01-27 21:59:34](https://github.com/leanprover-community/mathlib/commit/3e59960)
feat(ring_theory/nullstellensatz): Classical Nullstellensatz ([#5760](https://github.com/leanprover-community/mathlib/pull/5760))
This file states and proves Hilbert's classical nullstellensatz for multi-variate polynomials over an algebraically closed field.
#### Estimated changes
Modified docs/overview.yaml


Modified src/field_theory/algebraic_closure.lean
- \+ *lemma* algebra_map_surjective_of_is_integral'

Modified src/ring_theory/jacobson.lean


Created src/ring_theory/nullstellensatz.lean
- \+ *lemma* mem_zero_locus_iff
- \+ *lemma* zero_locus_anti_mono
- \+ *lemma* zero_locus_bot
- \+ *lemma* zero_locus_top
- \+ *lemma* mem_vanishing_ideal_iff
- \+ *lemma* vanishing_ideal_anti_mono
- \+ *lemma* vanishing_ideal_empty
- \+ *lemma* le_vanishing_ideal_zero_locus
- \+ *lemma* zero_locus_vanishing_ideal_le
- \+ *lemma* mem_vanishing_ideal_singleton_iff
- \+ *lemma* radical_le_vanishing_ideal_zero_locus
- \+ *lemma* vanishing_ideal_point_to_point
- \+ *lemma* point_to_point_zero_locus_le
- \+ *lemma* is_maximal_iff_eq_vanishing_ideal_singleton
- \+ *lemma* is_prime.vanishing_ideal_zero_locus
- \+ *theorem* zero_locus_vanishing_ideal_galois_connection
- \+ *theorem* vanishing_ideal_zero_locus_eq_radical
- \+ *def* zero_locus
- \+ *def* vanishing_ideal
- \+ *def* point_to_point



## [2021-01-27 18:19:45](https://github.com/leanprover-community/mathlib/commit/4cc0d52)
refactor(data/set/basic): simpler proofs ([#5920](https://github.com/leanprover-community/mathlib/pull/5920))
This replaces many uses of `simp` and `finish` with direct term proofs
to speed up the overall compilation of the file.
This PR is WIP in the sense that not all of `set.basic` is converted,
but there are no dependencies between the changes so this can be merged
at any point.
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *lemma* empty_not_nonempty
- \+/\- *lemma* eq_empty_or_nonempty
- \+/\- *lemma* univ_eq_empty_iff
- \+/\- *lemma* ne_insert_of_not_mem
- \+/\- *lemma* eq_singleton_iff_unique_mem
- \+/\- *lemma* sep_univ
- \+/\- *lemma* compl_subset_compl
- \+/\- *lemma* inter_compl_nonempty_iff
- \+/\- *theorem* mem_of_mem_of_subset
- \+/\- *theorem* eq_of_subset_of_subset
- \+/\- *theorem* mem_of_subset_of_mem
- \+/\- *theorem* not_subset
- \+/\- *theorem* eq_or_ssubset_of_subset
- \+/\- *theorem* not_mem_empty
- \+/\- *theorem* not_not_mem
- \+/\- *theorem* nonempty.not_subset_empty
- \+/\- *theorem* nonempty.ne_empty
- \+/\- *theorem* empty_subset
- \+/\- *theorem* eq_empty_iff_forall_not_mem
- \+/\- *theorem* eq_empty_of_subset_empty
- \+/\- *theorem* ne_empty_iff_nonempty
- \+/\- *theorem* ball_empty_iff
- \+/\- *theorem* eq_univ_of_univ_subset
- \+/\- *theorem* union_self
- \+/\- *theorem* union_empty
- \+/\- *theorem* empty_union
- \+/\- *theorem* union_comm
- \+/\- *theorem* union_assoc
- \+/\- *theorem* union_subset_union
- \+/\- *theorem* mem_inter
- \+/\- *theorem* mem_of_mem_inter_left
- \+/\- *theorem* mem_of_mem_inter_right
- \+/\- *theorem* inter_self
- \+/\- *theorem* inter_empty
- \+/\- *theorem* empty_inter
- \+/\- *theorem* inter_comm
- \+/\- *theorem* inter_assoc
- \+/\- *theorem* inter_subset_left
- \+/\- *theorem* inter_subset_right
- \+/\- *theorem* subset_inter
- \+ *theorem* subset_iff_inter_eq_left
- \+ *theorem* subset_iff_inter_eq_right
- \+/\- *theorem* inter_eq_self_of_subset_left
- \+/\- *theorem* inter_eq_self_of_subset_right
- \+/\- *theorem* inter_univ
- \+/\- *theorem* univ_inter
- \+/\- *theorem* inter_subset_inter
- \+/\- *theorem* inter_subset_inter_left
- \+/\- *theorem* inter_subset_inter_right
- \+/\- *theorem* subset_insert
- \+/\- *theorem* mem_insert
- \+/\- *theorem* mem_of_mem_insert_of_ne
- \+/\- *theorem* mem_insert_iff
- \+/\- *theorem* insert_subset_insert
- \+/\- *theorem* insert_union
- \+/\- *theorem* union_insert
- \+/\- *theorem* insert_nonempty
- \+/\- *theorem* forall_of_forall_insert
- \+/\- *theorem* forall_insert_of_forall
- \+/\- *theorem* singleton_def
- \+/\- *theorem* mem_singleton_iff
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* eq_of_mem_singleton
- \+/\- *theorem* mem_singleton_of_eq
- \+/\- *theorem* insert_eq
- \+/\- *theorem* pair_eq_singleton
- \+/\- *theorem* pair_comm
- \+/\- *theorem* singleton_subset_iff
- \+/\- *theorem* set_compr_eq_eq_singleton
- \+/\- *theorem* singleton_union
- \+/\- *theorem* union_singleton
- \+/\- *theorem* singleton_inter_eq_empty
- \+/\- *theorem* inter_singleton_eq_empty
- \+/\- *theorem* mem_sep_eq
- \+/\- *theorem* eq_sep_of_subset
- \+/\- *theorem* sep_subset
- \+/\- *theorem* forall_not_of_sep_empty
- \+/\- *theorem* union_compl_self
- \+/\- *theorem* compl_union_self
- \+/\- *theorem* compl_comp_compl
- \+/\- *theorem* compl_subset_comm
- \+/\- *theorem* nonempty_diff
- \+/\- *theorem* diff_subset
- \- *theorem* subset_iff_inter_eq_self

Modified src/logic/basic.lean
- \+ *theorem* and_congr_left
- \+ *theorem* and_congr_left'
- \+ *theorem* and_congr_right'
- \+ *theorem* or_congr_left
- \+ *theorem* or_congr_right
- \+ *theorem* bex_eq_left
- \+ *theorem* ball_or_left_distrib
- \+ *theorem* bex_or_left_distrib



## [2021-01-27 18:19:43](https://github.com/leanprover-community/mathlib/commit/8af7e08)
feat(data/fintype/basic): make subtype_of_fintype computable ([#5919](https://github.com/leanprover-community/mathlib/pull/5919))
This smokes out a few places downstream that are missing decidability hypotheses needed for the fintype instance to exist.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean


Modified src/combinatorics/simple_graph/degree_sum.lean
- \+/\- *lemma* odd_card_odd_degree_vertices_ne
- \+/\- *lemma* exists_ne_odd_degree_of_exists_odd_degree
- \+/\- *theorem* even_card_odd_degree_vertices

Modified src/data/fintype/basic.lean


Modified src/data/fintype/card.lean


Modified src/field_theory/galois.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/subgroup.lean


Modified src/group_theory/subgroup.lean
- \+/\- *lemma* eq_top_of_card_eq



## [2021-01-27 18:19:41](https://github.com/leanprover-community/mathlib/commit/f45dee4)
feat(algebra/*,linear_algebra/basic,ring_theory/ideal): lemmas about span of finite subsets and nontrivial maximal ideals ([#5641](https://github.com/leanprover-community/mathlib/pull/5641))
#### Estimated changes
Modified src/algebra/algebra/operations.lean
- \+ *lemma* mem_span_mul_finite_of_mem_span_mul
- \+ *lemma* mem_span_mul_finite_of_mem_mul

Modified src/algebra/pointwise.lean
- \+ *lemma* subset_mul

Modified src/linear_algebra/basic.lean
- \+ *lemma* mem_span_finite_of_mem_span

Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* ne_bot_of_is_maximal_of_not_is_field



## [2021-01-27 18:19:40](https://github.com/leanprover-community/mathlib/commit/32fdb81)
feat(data/zsqrtd/to_real): Add `to_real` ([#5640](https://github.com/leanprover-community/mathlib/pull/5640))
Also adds `norm_eq_zero`, and replaces some calls to simp with direct lemma applications
#### Estimated changes
Modified src/data/zsqrtd/basic.lean
- \+ *lemma* norm_eq_zero
- \+ *lemma* hom_ext
- \+ *lemma* lift_injective
- \+ *theorem* dmuld
- \+ *def* lift

Modified src/data/zsqrtd/gaussian_int.lean


Created src/data/zsqrtd/to_real.lean
- \+ *lemma* to_real_injective



## [2021-01-27 16:19:52](https://github.com/leanprover-community/mathlib/commit/1011601)
feat(algebra/continued_fractions): add termination iff rat lemmas ([#4867](https://github.com/leanprover-community/mathlib/pull/4867))
### What
Show that the computation of a continued fraction terminates if and only if we compute the continued fraction of a rational number.
### How
1. Show that every intermediate operation involved in the computation of a continued fraction returns a value that has a rational counterpart. This then shows that a terminating continued fraction corresponds to a rational value.
2. Show that the operations involved in the computation of a continued fraction for rational numbers only return results that can be lifted to the result of the same operations done on an equal value in a suitable linear ordered, archimedean field with a floor function.
3. Show that the continued fraction of a rational number terminates.
4. Set up the needed coercions to express the results above starting from [here](https://github.com/leanprover-community/mathlib/compare/kappelmann_termination_iff_rat?expand=1#diff-1dbcf8473152b2d8fca024352bd899af37669b8af18792262c2d5d6f31148971R129). I did not know where to put these lemmas. Please let me know your opinion.
4. Extract 4 auxiliary lemmas that are not specific to continued fraction but more generally about rational numbers, integers, and natural numbers starting from [here](https://github.com/leanprover-community/mathlib/compare/kappelmann_termination_iff_rat?expand=1#diff-1dbcf8473152b2d8fca024352bd899af37669b8af18792262c2d5d6f31148971R28). Again, I did not know where to put these. Please let me know your opinion.
#### Estimated changes
Modified src/algebra/continued_fractions/basic.lean
- \+ *def* map
- \- *def* seq.coe_to_seq

Modified src/algebra/continued_fractions/computation/basic.lean
- \+ *def* mapFr

Created src/algebra/continued_fractions/computation/terminates_iff_rat.lean
- \+ *lemma* exists_gcf_pair_rat_eq_of_nth_conts_aux
- \+ *lemma* exists_gcf_pair_rat_eq_nth_conts
- \+ *lemma* exists_rat_eq_nth_numerator
- \+ *lemma* exists_rat_eq_nth_denominator
- \+ *lemma* exists_rat_eq_nth_convergent
- \+ *lemma* coe_of_rat_eq
- \+ *lemma* coe_stream_nth_rat_eq
- \+ *lemma* coe_stream_rat_eq
- \+ *lemma* coe_of_h_rat_eq
- \+ *lemma* coe_of_s_nth_rat_eq
- \+ *lemma* coe_of_s_rat_eq
- \+ *lemma* of_terminates_iff_of_rat_terminates
- \+ *lemma* of_inv_fr_num_lt_num_of_pos
- \+ *lemma* stream_succ_nth_fr_num_lt_nth_fr_num_rat
- \+ *lemma* stream_nth_fr_num_le_fr_num_sub_n_rat
- \+ *lemma* exists_nth_stream_eq_none_of_rat
- \+ *theorem* exists_rat_eq_of_terminates
- \+ *theorem* terminates_of_rat
- \+ *theorem* terminates_iff_rat



## [2021-01-27 12:14:38](https://github.com/leanprover-community/mathlib/commit/9adf9bb)
feat(order/ideal): add partial_order instance to order.ideal ([#5909](https://github.com/leanprover-community/mathlib/pull/5909))
Add some instances for `order.ideal`, some of them conditional on
having extra structure on the carrier preorder `P`:
* In all cases, `ideal P` is a partial order.
* If `P` has a bottom element, so does `ideal P`.
* If `P` has a top element, so does `ideal P`.
  (Although this could be weekened to `P` being directed.)
Also, add some `@[ext]`, `@[simp]`, `@[trans]` lemmas.
#### Estimated changes
Modified src/order/ideal.lean
- \+ *lemma* ext
- \+ *lemma* mem_of_mem_of_le
- \+ *lemma* principal_le_iff
- \+ *lemma* bot_mem
- \+ *lemma* sup_mem
- \+ *lemma* sup_mem_iff



## [2021-01-27 12:14:36](https://github.com/leanprover-community/mathlib/commit/7244b43)
refactor(topology/local_homeomorph): simpler proof of `prod_symm` ([#5906](https://github.com/leanprover-community/mathlib/pull/5906))
17X smaller proof
co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/topology/local_homeomorph.lean




## [2021-01-27 12:14:34](https://github.com/leanprover-community/mathlib/commit/a859f10)
refactor(computability/primrec): simpler proof of `primrec.of_equiv` ([#5905](https://github.com/leanprover-community/mathlib/pull/5905))
12X smaller proof term
co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/computability/primrec.lean




## [2021-01-27 12:14:32](https://github.com/leanprover-community/mathlib/commit/35638ed)
refactor(data/set/basic): simpler proof of `union_subset_iff` ([#5904](https://github.com/leanprover-community/mathlib/pull/5904))
12X smaller proof term
co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/data/set/basic.lean




## [2021-01-27 12:14:30](https://github.com/leanprover-community/mathlib/commit/c64aa13)
chore(*): bump to lean-3.26.0 ([#5895](https://github.com/leanprover-community/mathlib/pull/5895))
#### Estimated changes
Modified leanpkg.toml


Modified src/control/traversable/derive.lean


Modified src/data/nat/digits.lean


Modified src/data/padics/padic_numbers.lean


Modified src/logic/nontrivial.lean


Modified src/meta/expr.lean


Modified src/meta/rb_map.lean


Modified src/ring_theory/witt_vector/is_poly.lean


Modified src/tactic/abel.lean


Modified src/tactic/choose.lean


Modified src/tactic/field_simp.lean


Modified src/tactic/finish.lean


Modified src/tactic/group.lean


Modified src/tactic/lint/simp.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/norm_cast.lean


Modified src/tactic/norm_num.lean


Modified src/tactic/reassoc_axiom.lean


Modified src/tactic/ring.lean


Modified src/tactic/simp_rw.lean


Modified src/tactic/simpa.lean


Modified src/tactic/simps.lean


Modified src/tactic/split_ifs.lean


Modified src/tactic/squeeze.lean


Modified src/tactic/zify.lean


Modified test/squeeze.lean




## [2021-01-27 12:14:28](https://github.com/leanprover-community/mathlib/commit/78a518a)
feat(measure_theory/independence): define independence of sets of sets, measurable spaces, sets, functions ([#5848](https://github.com/leanprover-community/mathlib/pull/5848))
This first PR about independence contains definitions, a few lemmas about independence of unions/intersections of sets of sets, and a proof that two measurable spaces are independent iff generating pi-systems are independent (included in this PR to demonstrate usability of the definitions).
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure.smul_finite
- \+ *lemma* ext_on_measurable_space_of_generate_finite

Created src/probability_theory/independence.lean
- \+ *lemma* indep_sets.symm
- \+ *lemma* indep.symm
- \+ *lemma* indep_sets_of_indep_sets_of_le_left
- \+ *lemma* indep_sets_of_indep_sets_of_le_right
- \+ *lemma* indep_of_indep_of_le_left
- \+ *lemma* indep_of_indep_of_le_right
- \+ *lemma* indep_sets.union
- \+ *lemma* indep_sets.union_iff
- \+ *lemma* indep_sets.Union
- \+ *lemma* indep_sets.inter
- \+ *lemma* indep_sets.Inter
- \+ *lemma* Indep_sets.indep_sets
- \+ *lemma* Indep.indep
- \+ *lemma* Indep.Indep_sets
- \+ *lemma* indep.indep_sets
- \+ *lemma* indep_sets.indep
- \+ *def* Indep_sets
- \+ *def* indep_sets
- \+ *def* Indep
- \+ *def* indep
- \+ *def* Indep_set
- \+ *def* indep_set
- \+ *def* Indep_fun
- \+ *def* indep_fun



## [2021-01-27 08:42:04](https://github.com/leanprover-community/mathlib/commit/e5f9409)
refactor(category_theory/abelian): golf `mono_of_kernel_ι_eq_zero` ([#5914](https://github.com/leanprover-community/mathlib/pull/5914))
Co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/category_theory/abelian/basic.lean




## [2021-01-27 08:41:59](https://github.com/leanprover-community/mathlib/commit/1688b3e)
refactor(data/complex/exponential): simplify proof of `tan_eq_sin_div_cos` ([#5913](https://github.com/leanprover-community/mathlib/pull/5913))
Co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/data/complex/exponential.lean




## [2021-01-27 08:41:57](https://github.com/leanprover-community/mathlib/commit/e927930)
refactor(data/holor): simp -> refl ([#5912](https://github.com/leanprover-community/mathlib/pull/5912))
Co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/data/holor.lean




## [2021-01-27 08:41:55](https://github.com/leanprover-community/mathlib/commit/38f6e05)
refactor(algebra/category/Group/limits): simp -> refl ([#5911](https://github.com/leanprover-community/mathlib/pull/5911))
Co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/algebra/category/Group/limits.lean




## [2021-01-27 08:41:53](https://github.com/leanprover-community/mathlib/commit/6eae630)
refactor(data/real/golden_ratio): simpler proof of `gold_pos` ([#5910](https://github.com/leanprover-community/mathlib/pull/5910))
13X smaller (pretty-printed) proof term
Co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/data/real/golden_ratio.lean




## [2021-01-27 08:41:51](https://github.com/leanprover-community/mathlib/commit/e9a1e2b)
refactor(data/pequiv): simpler proof of `pequiv.of_set_univ` ([#5907](https://github.com/leanprover-community/mathlib/pull/5907))
17X smaller proof
co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/data/pequiv.lean
- \+/\- *lemma* of_set_univ



## [2021-01-27 08:41:50](https://github.com/leanprover-community/mathlib/commit/fd55e57)
refactor(algebra/group/basic): simp -> rw in `sub_eq_sub_iff_sub_eq_sub` ([#5903](https://github.com/leanprover-community/mathlib/pull/5903))
co-authors: `lean-gptf`, Yuhuai Wu
#### Estimated changes
Modified src/algebra/group/basic.lean




## [2021-01-27 08:41:48](https://github.com/leanprover-community/mathlib/commit/1cd2286)
chore(data/finset/preimage): add missing simp lemmas ([#5902](https://github.com/leanprover-community/mathlib/pull/5902))
#### Estimated changes
Modified src/data/finset/preimage.lean
- \+ *lemma* preimage_empty
- \+ *lemma* preimage_univ
- \+ *lemma* preimage_inter
- \+ *lemma* preimage_union
- \+ *lemma* preimage_compl



## [2021-01-27 08:41:46](https://github.com/leanprover-community/mathlib/commit/20d6b6a)
chore(*): add more simp lemmas, refactor theorems about `fintype.sum` ([#5888](https://github.com/leanprover-community/mathlib/pull/5888))
* `finset.prod_sum_elim`, `finset.sum_sum_elim`: use `finset.map`
  instead of `finset.image`;
* add `multilinear_map.coe_mk_continuous`,
  `finset.order_emb_of_fin_mem`, `fintype.univ_sum_type`,
  `fintype.prod_sum_elim`, `sum.update_elim_inl`,
  `sum.update_elim_inr`, `sum.update_inl_comp_inl`,
  `sum.update_inl_comp_inr`, `sum.update_inr_comp_inl`,
  `sum.update_inr_comp_inr` and `apply` versions of `sum.*_comp_*` lemmas,
* move some lemmas about `function.update` from `data.set.function` to `logic.function.basic`;
* rename `sum.elim_injective` to `function.injective.sum_elim`
* `simps` lemmas for `function.embedding.inl` and
  `function.embedding.inr`;
* for `e : α ≃o β`, simplify `e.to_equiv.symm` to `e.symm_to_equiv`;
* add `continuous_multilinear_map.to_multilinear_map_add`,
  `continuous_multilinear_map.to_multilinear_map_smul`, and `simps`
  for `continuous_multilinear_map.to_multilinear_map_linear`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* coe_mk_continuous

Modified src/data/equiv/basic.lean


Modified src/data/finset/sort.lean
- \+ *lemma* order_emb_of_fin_mem

Modified src/data/fintype/basic.lean
- \+ *lemma* univ_sum_type

Modified src/data/fintype/card.lean
- \+ *lemma* fintype.prod_sum_elim

Modified src/data/set/function.lean
- \- *lemma* update_comp_eq_of_injective'
- \- *lemma* update_comp_eq_of_injective

Modified src/data/sum.lean
- \+ *lemma* update_elim_inl
- \+ *lemma* update_elim_inr
- \+ *lemma* update_inl_comp_inl
- \+ *lemma* update_inl_apply_inl
- \+ *lemma* update_inl_comp_inr
- \+ *lemma* update_inl_apply_inr
- \+ *lemma* update_inr_comp_inl
- \+ *lemma* update_inr_apply_inl
- \+ *lemma* update_inr_comp_inr
- \+ *lemma* update_inr_apply_inr
- \+ *lemma* injective.sum_elim
- \- *lemma* elim_injective

Modified src/linear_algebra/multilinear.lean


Modified src/logic/embedding.lean
- \+/\- *def* inl
- \+/\- *def* inr

Modified src/logic/function/basic.lean
- \+ *lemma* update_comp_eq_of_forall_ne'
- \+ *lemma* update_comp_eq_of_forall_ne
- \+ *lemma* update_comp_eq_of_injective'
- \+ *lemma* update_comp_eq_of_injective
- \- *lemma* update_comp

Modified src/order/rel_iso.lean
- \+ *lemma* to_equiv_symm

Modified src/topology/algebra/multilinear.lean
- \+ *lemma* to_multilinear_map_add
- \+ *lemma* to_multilinear_map_smul
- \+/\- *def* to_multilinear_map_linear



## [2021-01-27 08:41:44](https://github.com/leanprover-community/mathlib/commit/21e9d42)
feat(algebra/euclidean_domain): Unify occurences of div_add_mod and mod_add_div ([#5884](https://github.com/leanprover-community/mathlib/pull/5884))
Adding the corresponding commutative version at several places (euclidean domain, nat, pnat, int) whenever there is the other version. 
In subsequent PRs other proofs in the library which now use some version of `add_comm, exact div_add_mod` or `add_comm, exact mod_add_div` should be golfed.
Trying to address issue [#1534](https://github.com/leanprover-community/mathlib/pull/1534)
#### Estimated changes
Modified src/algebra/euclidean_domain.lean
- \+ *lemma* mod_add_div

Modified src/data/int/basic.lean
- \+ *theorem* div_add_mod

Modified src/data/pnat/basic.lean
- \+/\- *theorem* mod_add_div
- \+ *theorem* div_add_mod



## [2021-01-27 08:41:42](https://github.com/leanprover-community/mathlib/commit/688772e)
refactor(ring_theory/ideal ring_theory/jacobson): allow `ideal` in a `comm_semiring` ([#5879](https://github.com/leanprover-community/mathlib/pull/5879))
At the moment, `ideal` requires the underlying ring to be a `comm_ring`.  This changes in this PR and the underlying ring can now be a `comm_semiring`.  There is a discussion about merits and issues in this Zulip chat:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/(comm_)semiring.3A.20examples.3F
At the moment, this PR changes the definition and adapts, mostly `ring_theory/jacobson`, to avoid deterministic timeouts.  In future PRs, I will start changing hypotheses on lemmas involving `ideal` to use the more general framework.
A note: the file `ring_theory/jacobson` might require further improvements.  If possible, I would like this change to push through without cluttering it with changes to that file.  If there is a way of accepting this change and then proceeding to the changes in `jacobson`, that would be ideal!  If it needs to be done at the same time, then so be it!
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+/\- *def* ideal

Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* quotient_map_comp_mk

Modified src/ring_theory/ideal/prod.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/jacobson.lean
- \+ *lemma* injective_quotient_le_comap_map
- \+ *lemma* quotient_mk_maps_eq
- \+/\- *lemma* disjoint_powers_iff_not_mem
- \+/\- *lemma* is_integral_localization_map_polynomial_quotient
- \+/\- *lemma* jacobson_bot_of_integral_localization
- \+ *lemma* is_jacobson_polynomial_of_is_jacobson
- \+ *lemma* is_maximal_comap_C_of_is_maximal
- \+/\- *lemma* quotient_mk_comp_C_is_integral_of_jacobson
- \+/\- *lemma* is_maximal_comap_C_of_is_jacobson
- \+/\- *lemma* comp_C_integral_of_surjective_of_jacobson
- \+/\- *lemma* is_jacobson_mv_polynomial_fin
- \+/\- *theorem* is_jacobson_polynomial_iff_is_jacobson
- \+/\- *def* is_jacobson



## [2021-01-27 08:41:40](https://github.com/leanprover-community/mathlib/commit/b2c5d9b)
feat(ring_theory/noetherian, linear_algebra/basic): Show that finitely generated submodules are the compact elements in the submodule lattice ([#5871](https://github.com/leanprover-community/mathlib/pull/5871))
Show that a submodule is finitely generated if and only if it is a compact lattice element. Add lemma showing that any submodule is the supremum of the spans of its elements.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* sup_finset_image

Modified src/linear_algebra/basic.lean
- \+ *lemma* span_eq_supr_of_singleton_spans

Modified src/order/compactly_generated.lean
- \+ *lemma* finset_sup_compact_of_compact

Modified src/ring_theory/noetherian.lean
- \+ *lemma* singleton_span_is_compact_element
- \+ *theorem* fg_iff_compact



## [2021-01-27 08:41:39](https://github.com/leanprover-community/mathlib/commit/7f04253)
feat(field_theory/adjoin): Generalize alg_hom_mk_adjoin_splits to infinite sets ([#5860](https://github.com/leanprover-community/mathlib/pull/5860))
This PR uses Zorn's lemma to generalize `alg_hom_mk_adjoin_splits` to infinite sets.
The proof is rather long, but I think that the result is worth it. It should allow me to prove that if E/F is any normal extension then any automorphism of F lifts to an automorphism of E.
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* lifts.eq_of_le
- \+ *lemma* lifts.exists_max_two
- \+ *lemma* lifts.exists_max_three
- \+ *lemma* lifts.exists_upper_bound
- \+ *lemma* lifts.le_lifts_of_splits
- \+ *lemma* lifts.mem_lifts_of_splits
- \+ *lemma* lifts.exists_lift_of_splits
- \+/\- *lemma* alg_hom_mk_adjoin_splits'
- \+ *def* lifts
- \+ *def* lifts.upper_bound_intermediate_field

Modified src/field_theory/normal.lean




## [2021-01-27 08:41:36](https://github.com/leanprover-community/mathlib/commit/e95928c)
feat(field_theory/normal): Restrict to normal subfield ([#5845](https://github.com/leanprover-community/mathlib/pull/5845))
Now that we know that splitting fields are normal, it makes sense to move the results of [#5562](https://github.com/leanprover-community/mathlib/pull/5562) to `normal.lean`.
#### Estimated changes
Modified src/field_theory/normal.lean
- \+ *lemma* alg_hom.restrict_normal_commutes
- \+ *lemma* alg_hom.restrict_normal_comp
- \+ *lemma* alg_equiv.restrict_normal_commutes
- \+ *lemma* alg_equiv.restrict_normal_trans
- \+ *def* alg_hom.restrict_normal_aux
- \+ *def* alg_hom.restrict_normal
- \+ *def* alg_equiv.restrict_normal
- \+ *def* alg_equiv.restrict_normal_hom

Modified src/field_theory/splitting_field.lean
- \- *lemma* is_splitting_field.range_to_alg_hom
- \- *lemma* alg_hom.restrict_is_splitting_field_commutes
- \- *lemma* alg_hom.restrict_is_splitting_field_comp
- \- *lemma* alg_equiv.restrict_is_splitting_field_commutes
- \- *lemma* alg_equiv.restrict_is_splitting_field_trans
- \- *def* alg_hom.restrict_is_splitting_field_aux
- \- *def* alg_hom.restrict_is_splitting_field
- \- *def* alg_equiv.restrict_is_splitting_field
- \- *def* alg_equiv.restict_is_splitting_field_hom



## [2021-01-27 08:41:35](https://github.com/leanprover-community/mathlib/commit/61491ca)
feat(linear_algebra/matrix): A vector is zero iff its dot product with every vector is zero ([#5837](https://github.com/leanprover-community/mathlib/pull/5837))
#### Estimated changes
Modified src/linear_algebra/matrix.lean
- \+ *lemma* matrix.dot_product_std_basis_eq_mul
- \+ *lemma* matrix.dot_product_std_basis_one
- \+ *lemma* matrix.dot_product_eq
- \+ *lemma* matrix.dot_product_eq_iff
- \+ *lemma* matrix.dot_product_eq_zero
- \+ *lemma* matrix.dot_product_eq_zero_iff



## [2021-01-27 08:41:33](https://github.com/leanprover-community/mathlib/commit/31edca8)
chore(data/finsupp,data/dfinsupp,algebra/big_operators): add missing lemmas about sums of bundled functions ([#5834](https://github.com/leanprover-community/mathlib/pull/5834))
This adds missing lemmas about how `{finset,finsupp,dfinsupp}.{prod,sum}` acts on {coercion,application,evaluation} of `{add_monoid_hom,monoid_hom,linear_map}`. Specifically, it:
* adds the lemmas:
  * `monoid_hom.coe_prod`
  * `monoid_hom.map_dfinsupp_prod`
  * `monoid_hom.dfinsupp_prod_apply`
  * `monoid_hom.finsupp_prod_apply`
  * `monoid_hom.coe_dfinsupp_prod`
  * `monoid_hom.coe_finsupp_prod`
  * that are the additive versions of the above for `add_monoid_hom`.
  * `linear_map.map_dfinsupp_sum`
  * `linear_map.dfinsupp_sum_apply`
  * `linear_map.finsupp_sum_apply`
  * `linear_map.coe_dfinsupp_sum`
  * `linear_map.coe_finsupp_sum`
* Renames `linear_map.finsupp_sum` to `linear_map.map_finsupp_sum` for consistency with `linear_map.map_sum`.
* Adds a new `monoid_hom.coe_fn` definition
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* monoid_hom.coe_prod
- \+ *lemma* monoid_hom.finset_prod_apply

Modified src/algebra/big_operators/pi.lean
- \- *lemma* monoid_hom.finset_prod_apply

Modified src/algebra/group/pi.lean
- \+ *def* monoid_hom.coe_fn

Modified src/data/dfinsupp.lean
- \+ *lemma* map_dfinsupp_prod
- \+ *lemma* coe_dfinsupp_prod
- \+ *lemma* dfinsupp_prod_apply

Modified src/data/finsupp/basic.lean
- \+ *lemma* monoid_hom.coe_finsupp_prod
- \+ *lemma* monoid_hom.finsupp_prod_apply

Modified src/linear_algebra/basic.lean
- \+ *lemma* map_finsupp_sum
- \+ *lemma* coe_finsupp_sum
- \+ *lemma* finsupp_sum_apply
- \+ *lemma* map_dfinsupp_sum
- \+ *lemma* coe_dfinsupp_sum
- \+ *lemma* dfinsupp_sum_apply
- \- *lemma* finsupp_sum



## [2021-01-27 08:41:30](https://github.com/leanprover-community/mathlib/commit/aa8980d)
chore(category_theory/monad): comonadic adjunction ([#5770](https://github.com/leanprover-community/mathlib/pull/5770))
Defines comonadic adjunctions dual to what's already there
#### Estimated changes
Modified src/category_theory/monad/adjunction.lean
- \+ *def* comparison
- \+ *def* comparison_forget



## [2021-01-27 08:41:28](https://github.com/leanprover-community/mathlib/commit/3b6d6d7)
chore(data/fintype/basic): Add simp lemma about finset.univ ([#5708](https://github.com/leanprover-community/mathlib/pull/5708))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* univ_filter_exists
- \+ *lemma* univ_filter_mem_range



## [2021-01-27 08:41:26](https://github.com/leanprover-community/mathlib/commit/00b88eb)
feat(data/polynomial/denominators): add file denominators ([#5587](https://github.com/leanprover-community/mathlib/pull/5587))
The main goal of this PR is to establish that `b^deg(f)*f(a/b)` is an expression not involving denominators.
The first lemma, `induction_with_nat_degree_le` is an induction principle for polynomials, where the inductive hypothesis has a bound on the degree of the polynomial.  This allows to build the proof by tearing apart a polynomial into its monomials, while remembering the overall degree of the polynomial itself.  This lemma might be a better fit for the file `data.polynomial.induction`.
#### Estimated changes
Created src/data/polynomial/denoms_clearable.lean
- \+ *lemma* denoms_clearable_zero
- \+ *lemma* denoms_clearable_C_mul_X_pow
- \+ *lemma* denoms_clearable.add
- \+ *lemma* denoms_clearable_of_nat_degree_le
- \+ *theorem* denoms_clearable_nat_degree
- \+ *def* denoms_clearable

Modified src/data/polynomial/erase_lead.lean
- \+ *lemma* induction_with_nat_degree_le



## [2021-01-27 05:12:41](https://github.com/leanprover-community/mathlib/commit/394d357)
refactor(data/nat/factorial): simpler proof of `mul_factorial_pred` ([#5917](https://github.com/leanprover-community/mathlib/pull/5917))
Co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/data/nat/factorial.lean




## [2021-01-27 05:12:39](https://github.com/leanprover-community/mathlib/commit/d41781c)
refactor(topology/metric_space): simplify `dist_triangle` proofs ([#5916](https://github.com/leanprover-community/mathlib/pull/5916))
Co-authors: `lean-gptf`, Stanislas Polu
#### Estimated changes
Modified src/topology/metric_space/basic.lean




## [2021-01-27 05:12:37](https://github.com/leanprover-community/mathlib/commit/4e4298e)
chore(*): split long lines ([#5908](https://github.com/leanprover-community/mathlib/pull/5908))
#### Estimated changes
Modified archive/100-theorems-list/73_ascending_descending_sequences.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/category_theory/types.lean
- \+/\- *lemma* map_comp_apply
- \+/\- *lemma* hcomp
- \+/\- *lemma* equiv_equiv_iso_hom
- \+/\- *lemma* equiv_equiv_iso_inv

Modified src/computability/tm_computable.lean
- \+/\- *def* evals_to_in_time.refl
- \+/\- *def* tm2_outputs_in_time
- \+/\- *def* tm2_computable_in_time.to_tm2_computable
- \+/\- *def* id_computable_in_poly_time

Modified src/data/fintype/card.lean
- \+/\- *theorem* fin.sum_univ_succ_above

Modified src/data/list/basic.lean


Modified src/data/list/nodup.lean


Modified src/data/list/pairwise.lean
- \+/\- *theorem* pw_filter_map

Modified src/data/list/perm.lean
- \+/\- *theorem* perm.inter_append

Modified src/data/list/range.lean


Modified src/data/list/sections.lean
- \+/\- *lemma* rel_sections

Modified src/data/list/sigma.lean
- \+/\- *lemma* sizeof_kerase
- \+/\- *lemma* sizeof_erase_dupkeys

Modified src/data/matrix/basic.lean
- \+/\- *lemma* smul_apply
- \+/\- *lemma* col_smul
- \+/\- *lemma* row_smul
- \+/\- *lemma* update_column_apply

Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* support_sum_monomial_coeff

Modified src/data/mv_polynomial/monad.lean
- \+/\- *lemma* bind₂_bind₂
- \+/\- *lemma* eval₂_hom_bind₁
- \+/\- *lemma* eval₂_hom_bind₂

Modified src/geometry/manifold/mfderiv.lean
- \+/\- *lemma* unique_mdiff_on.inter
- \+/\- *lemma* has_mfderiv_within_at.has_mfderiv_at
- \+/\- *def* mfderiv_within

Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+/\- *lemma* model_with_corners.to_local_equiv_coe

Modified src/group_theory/archimedean.lean


Modified src/group_theory/coset.lean


Modified src/topology/algebra/continuous_functions.lean


Modified src/topology/algebra/floor_ring.lean


Modified src/topology/algebra/group_completion.lean
- \+/\- *lemma* is_add_group_hom_extension

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* continuous_within_at_Ico_iff_Iio
- \+/\- *lemma* continuous_within_at_Ioo_iff_Iio

Modified src/topology/algebra/uniform_group.lean
- \+/\- *lemma* to_uniform_space_eq

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/constructions.lean
- \+/\- *lemma* prod_generate_from_generate_from_eq

Modified src/topology/continuous_on.lean
- \+/\- *lemma* continuous_within_at.tendsto
- \+/\- *theorem* continuous_within_at_iff_continuous_at_restrict

Modified src/topology/dense_embedding.lean
- \+/\- *lemma* tendsto_comap_nhds_nhds

Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* diam_union
- \+/\- *theorem* closed_ball_subset_closed_ball

Modified src/topology/opens.lean


Modified src/topology/order.lean
- \+/\- *lemma* coinduced_le_iff_le_induced

Modified src/topology/path_connected.lean
- \+/\- *lemma* truncate_zero_zero
- \+/\- *lemma* truncate_one_one
- \+/\- *lemma* joined.mem_path_component



## [2021-01-27 05:12:35](https://github.com/leanprover-community/mathlib/commit/47e2f80)
chore(*): Replace integral_domain assumptions with no_zero_divisors ([#5877](https://github.com/leanprover-community/mathlib/pull/5877))
This removes unnecessary `nontrivial` assumptions, and reduces some `comm_ring` requirements to `comm_semiring`.
This also adds some missing `nontrivial` and `no_zero_divisors` instances.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/char_p/basic.lean
- \+/\- *theorem* frobenius_inj

Modified src/algebra/opposites.lean


Modified src/algebra/polynomial/big_operators.lean
- \+/\- *lemma* nat_degree_prod

Modified src/data/multiset/basic.lean
- \+/\- *theorem* prod_ne_zero

Modified src/data/polynomial/degree/definitions.lean
- \+/\- *lemma* degree_pow
- \+/\- *lemma* leading_coeff_X_add_C

Modified src/data/quaternion.lean
- \+/\- *lemma* conj_fixed

Modified src/linear_algebra/linear_independent.lean
- \+/\- *theorem* linear_independent_monoid_hom

Modified src/ring_theory/prime.lean


Modified src/ring_theory/subring.lean


Modified src/ring_theory/subsemiring.lean




## [2021-01-27 01:48:38](https://github.com/leanprover-community/mathlib/commit/19bb470)
chore(scripts): update nolints.txt ([#5918](https://github.com/leanprover-community/mathlib/pull/5918))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-27 01:48:34](https://github.com/leanprover-community/mathlib/commit/9173005)
chore(tactic/finish): Remove broken ifinish ([#5897](https://github.com/leanprover-community/mathlib/pull/5897))
See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/intuitionistic.20logic/near/224013270
#### Estimated changes
Modified src/tactic/finish.lean


Modified test/finish1.lean




## [2021-01-27 01:48:32](https://github.com/leanprover-community/mathlib/commit/1ddb93a)
feat(analysis/normed_space): define linear isometries ([#5867](https://github.com/leanprover-community/mathlib/pull/5867))
* define `linear_isometry` and `linear_isometry_equiv`;
* add `linear_map.ker_eq_bot_of_inverse`;
* replace `inv_fun_apply` lemmas with `inv_fun_eq_symm`;
* golf some proofs in `linear_algebra/finite_dimensional`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* inv_fun_eq_symm
- \- *lemma* inv_fun_apply

Modified src/algebra/module/linear_map.lean
- \+ *lemma* inv_fun_eq_symm
- \- *lemma* inv_fun_apply

Modified src/analysis/complex/basic.lean
- \+ *lemma* isometry_of_real
- \+/\- *lemma* continuous_of_real
- \- *lemma* continuous_linear_map.of_real_isometry
- \+ *def* linear_isometry.of_real
- \+/\- *def* continuous_linear_map.of_real

Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
- \+ *lemma* re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
- \+ *lemma* re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four
- \+ *lemma* im_inner_eq_norm_sub_I_smul_mul_self_sub_norm_add_I_smul_mul_self_div_four
- \+ *lemma* inner_eq_sum_norm_sq_div_four
- \+ *lemma* linear_isometry.inner_map_map
- \+ *lemma* linear_isometry_equiv.inner_map_map
- \+ *lemma* linear_map.coe_isometry_of_inner
- \+ *lemma* linear_map.isometry_of_inner_to_linear_map
- \+ *lemma* linear_equiv.coe_isometry_of_inner
- \+ *lemma* linear_equiv.isometry_of_inner_to_linear_equiv
- \+ *def* linear_map.isometry_of_inner
- \+ *def* linear_equiv.isometry_of_inner

Created src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* coe_to_linear_map
- \+ *lemma* to_linear_map_injective
- \+ *lemma* coe_fn_injective
- \+ *lemma* ext
- \+ *lemma* map_zero
- \+ *lemma* map_add
- \+ *lemma* map_sub
- \+ *lemma* map_smul
- \+ *lemma* norm_map
- \+ *lemma* nnnorm_map
- \+ *lemma* dist_map
- \+ *lemma* edist_map
- \+ *lemma* map_eq_iff
- \+ *lemma* map_ne
- \+ *lemma* ediam_image
- \+ *lemma* ediam_range
- \+ *lemma* diam_image
- \+ *lemma* diam_range
- \+ *lemma* coe_to_continuous_linear_map
- \+ *lemma* comp_continuous_iff
- \+ *lemma* coe_id
- \+ *lemma* coe_comp
- \+ *lemma* id_comp
- \+ *lemma* comp_id
- \+ *lemma* comp_assoc
- \+ *lemma* coe_one
- \+ *lemma* coe_mul
- \+ *lemma* coe_mk
- \+ *lemma* coe_to_linear_equiv
- \+ *lemma* to_linear_equiv_injective
- \+ *lemma* coe_refl
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+ *lemma* map_eq_zero_iff
- \+ *lemma* symm_symm
- \+ *lemma* coe_symm_to_linear_equiv
- \+ *lemma* coe_trans
- \+ *lemma* trans_refl
- \+ *lemma* refl_trans
- \+ *lemma* trans_symm
- \+ *lemma* symm_trans
- \+ *lemma* coe_symm_trans
- \+ *lemma* trans_assoc
- \+ *lemma* coe_inv
- \+ *def* to_continuous_linear_map
- \+ *def* id
- \+ *def* comp
- \+ *def* of_bounds
- \+ *def* to_linear_isometry
- \+ *def* to_isometric
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans
- \+ *def* to_continuous_linear_equiv

Modified src/analysis/normed_space/mazur_ulam.lean
- \+ *lemma* to_real_linear_isometry_equiv_symm_apply
- \- *lemma* to_real_linear_equiv_symm_apply
- \+ *def* to_real_linear_isometry_equiv_of_map_zero
- \+ *def* to_real_linear_isometry_equiv
- \- *def* to_real_linear_equiv_of_map_zero
- \- *def* to_real_linear_equiv

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* isometry_iff_norm
- \+ *lemma* linear_isometry.norm_to_continuous_linear_map
- \- *lemma* add_monoid_hom.isometry_of_norm
- \- *lemma* isometry_iff_norm_image_eq_norm

Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* I_mul_re

Modified src/linear_algebra/basic.lean
- \+ *theorem* ker_eq_bot_of_inverse

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* coe_of_injective_endo
- \+/\- *lemma* of_injective_endo_right_inv
- \+/\- *lemma* of_injective_endo_left_inv
- \- *lemma* of_injective_endo_to_fun

Modified src/topology/metric_space/isometry.lean
- \+ *lemma* isometry_iff_norm
- \+ *lemma* isometry_of_norm
- \+/\- *lemma* coe_mul
- \+/\- *lemma* mul_apply



## [2021-01-27 01:48:30](https://github.com/leanprover-community/mathlib/commit/1eb1293)
feat(archive/imo): formalize IMO 2011 problem Q3 ([#5842](https://github.com/leanprover-community/mathlib/pull/5842))
#### Estimated changes
Created archive/imo/imo2011_q3.lean
- \+ *theorem* imo2011_q3



## [2021-01-26 22:43:47](https://github.com/leanprover-community/mathlib/commit/531bcd8)
feat(data/real/{nnreal,ennreal}, topology/instances/ennreal): add of_real_(sum/prod/tsum) for nnreal and ennreal ([#5896](https://github.com/leanprover-community/mathlib/pull/5896))
We remark that if all terms of a real sum are nonnegative, `nnreal.of_real` of the sum is equal to the sum of the `nnreal.of_real`. Idem for `ennreal.of_real`, for products and `tsum`.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* of_real_sum_of_nonneg
- \+ *lemma* of_real_prod_of_nonneg

Modified src/data/real/nnreal.lean
- \+ *lemma* of_real_sum_of_nonneg
- \+ *lemma* of_real_prod_of_nonneg

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.of_real_tsum_of_nonneg

Modified src/topology/instances/nnreal.lean
- \+ *lemma* has_sum_of_real_of_nonneg



## [2021-01-26 22:43:45](https://github.com/leanprover-community/mathlib/commit/8c732b2)
feat(data/finset/basic): card_subtype simp lemma ([#5894](https://github.com/leanprover-community/mathlib/pull/5894))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* card_subtype



## [2021-01-26 16:37:25](https://github.com/leanprover-community/mathlib/commit/547d67f)
feat(analysis/{analytic,calculus}): an analytic function is strictly differentiable ([#5878](https://github.com/leanprover-community/mathlib/pull/5878))
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+ *lemma* norm_le_div_pow_of_pos_of_lt_radius
- \+ *lemma* has_fpower_series_on_ball.has_sum_sub
- \+ *lemma* has_fpower_series_on_ball.is_O_image_sub_image_sub_deriv_principal
- \+ *lemma* has_fpower_series_on_ball.image_sub_sub_deriv_le
- \+ *lemma* has_fpower_series_at.is_O_image_sub_norm_mul_norm_sub

Modified src/analysis/asymptotics.lean
- \+ *lemma* is_O_with_principal
- \+ *lemma* is_O_principal

Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_fpower_series_at.has_strict_deriv_at
- \+ *lemma* has_fpower_series_at.has_deriv_at
- \+ *lemma* has_fpower_series_at.deriv

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fpower_series_at.has_strict_fderiv_at
- \+ *lemma* has_fpower_series_at.has_fderiv_at
- \+ *lemma* has_fpower_series_at.differentiable_at
- \+ *lemma* analytic_at.differentiable_at
- \+ *lemma* analytic_at.differentiable_within_at
- \+ *lemma* has_fpower_series_at.fderiv
- \+ *lemma* has_fpower_series_on_ball.differentiable_on

Modified src/data/pi.lean
- \+ *lemma* div_def
- \+ *lemma* subsingleton.pi_single_eq



## [2021-01-26 04:21:27](https://github.com/leanprover-community/mathlib/commit/44fd23d)
chore(data/finset): Rename bind to bUnion ([#5813](https://github.com/leanprover-community/mathlib/pull/5813))
This commit renames `finset.bind` to `finset.bUnion`.  While this is the monadic bind operation, conceptually it's doing a bounded union of an indexed family of finite sets.  This will help with discoverability of this function.
There was a name conflict in `data.finset.lattice` due to this, since there are a number of theorems about the `set` version of `bUnion`, and for these I prefixed the lemmas with `set_`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_bUnion
- \+ *lemma* card_bUnion
- \+ *lemma* card_bUnion_le
- \- *lemma* prod_bind
- \- *lemma* card_bind
- \- *lemma* card_bind_le

Modified src/algebra/big_operators/ring.lean


Modified src/algebra/monoid_algebra.lean


Modified src/category_theory/filtered.lean


Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean


Modified src/computability/turing_machine.lean


Modified src/data/dfinsupp.lean


Modified src/data/finset/basic.lean
- \+ *lemma* singleton_bUnion
- \+ *lemma* bUnion_mono
- \+ *lemma* bUnion_subset_bUnion_of_subset_left
- \+ *lemma* bUnion_singleton
- \+ *lemma* bUnion_singleton_eq_self
- \+ *lemma* bUnion_filter_eq_of_maps_to
- \+ *lemma* image_bUnion_filter_eq
- \+ *lemma* disjoint_bUnion_left
- \+ *lemma* disjoint_bUnion_right
- \- *lemma* singleton_bind
- \- *lemma* bind_mono
- \- *lemma* bind_subset_bind_of_subset_left
- \- *lemma* bind_singleton
- \- *lemma* bind_singleton_eq_self
- \- *lemma* bind_filter_eq_of_maps_to
- \- *lemma* image_bind_filter_eq
- \- *lemma* disjoint_bind_left
- \- *lemma* disjoint_bind_right
- \+ *theorem* bUnion_val
- \+ *theorem* bUnion_empty
- \+ *theorem* mem_bUnion
- \+ *theorem* bUnion_insert
- \+ *theorem* bUnion_inter
- \+ *theorem* inter_bUnion
- \+ *theorem* image_bUnion
- \+ *theorem* bUnion_image
- \+ *theorem* product_eq_bUnion
- \+ *theorem* sigma_eq_bUnion
- \- *theorem* bind_val
- \- *theorem* bind_empty
- \- *theorem* mem_bind
- \- *theorem* bind_insert
- \- *theorem* bind_inter
- \- *theorem* inter_bind
- \- *theorem* image_bind
- \- *theorem* bind_image
- \- *theorem* product_eq_bind
- \- *theorem* sigma_eq_bind

Modified src/data/finset/lattice.lean
- \+ *lemma* sup_eq_bUnion
- \+ *lemma* supr_bUnion
- \+ *lemma* infi_bUnion
- \+ *lemma* set_bUnion_preimage_singleton
- \+ *lemma* set_bUnion_option_to_finset
- \+ *lemma* set_bInter_option_to_finset
- \+ *lemma* set_bUnion_union
- \+ *lemma* set_bInter_inter
- \+ *lemma* set_bUnion_insert
- \+ *lemma* set_bInter_insert
- \+ *lemma* set_bUnion_finset_image
- \+ *lemma* set_bInter_finset_image
- \+ *lemma* set_bUnion_insert_update
- \+ *lemma* set_bInter_insert_update
- \+ *lemma* set_bUnion_bUnion
- \+ *lemma* set_bInter_bUnion
- \- *lemma* sup_eq_bind
- \- *lemma* supr_bind
- \- *lemma* infi_bind
- \- *lemma* bUnion_preimage_singleton
- \- *lemma* bUnion_option_to_finset
- \- *lemma* bInter_option_to_finset
- \- *lemma* bUnion_union
- \- *lemma* bInter_inter
- \- *lemma* bUnion_insert
- \- *lemma* bInter_insert
- \- *lemma* bUnion_finset_image
- \- *lemma* bInter_finset_image
- \- *lemma* bUnion_insert_update
- \- *lemma* bInter_insert_update
- \- *lemma* bUnion_bind
- \- *lemma* bInter_bind
- \+ *theorem* set_bUnion_coe
- \+ *theorem* set_bInter_coe
- \+ *theorem* set_bUnion_singleton
- \+ *theorem* set_bInter_singleton
- \- *theorem* bUnion_coe
- \- *theorem* bInter_coe
- \- *theorem* bUnion_singleton
- \- *theorem* bInter_singleton

Modified src/data/finset/pi.lean


Modified src/data/finsupp/basic.lean


Modified src/data/fintype/basic.lean


Modified src/data/indicator_function.lean


Modified src/data/mv_polynomial/basic.lean


Modified src/data/mv_polynomial/variables.lean
- \+ *lemma* vars_eq_support_bUnion_support
- \- *lemma* vars_eq_support_bind_support

Modified src/data/nat/totient.lean


Modified src/data/set/finite.lean
- \+ *lemma* coe_bUnion
- \- *lemma* coe_bind
- \+ *theorem* finite_bUnion
- \- *theorem* finite_bind
- \+ *def* fintype_set_bUnion
- \+/\- *def* fintype_bUnion
- \- *def* fintype_bind

Modified src/group_theory/order_of_element.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/measure_space.lean


Modified src/order/filter/bases.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/polynomial/chebyshev/basic.lean


Modified src/ring_theory/polynomial/cyclotomic.lean


Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* nth_roots_one_eq_bUnion_primitive_roots'
- \+ *lemma* nth_roots_one_eq_bUnion_primitive_roots
- \- *lemma* nth_roots_one_eq_bind_primitive_roots'
- \- *lemma* nth_roots_one_eq_bind_primitive_roots

Modified src/ring_theory/witt_vector/witt_polynomial.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean




## [2021-01-26 01:48:59](https://github.com/leanprover-community/mathlib/commit/01a7cde)
chore(scripts): update nolints.txt ([#5892](https://github.com/leanprover-community/mathlib/pull/5892))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-25 17:49:34](https://github.com/leanprover-community/mathlib/commit/5491c59)
feat(data/fintype/basic): add lemmas about finsets and cardinality ([#5886](https://github.com/leanprover-community/mathlib/pull/5886))
Add lemmas about finsets and cardinality. Part of [#5695](https://github.com/leanprover-community/mathlib/pull/5695) in order to prove Hall's marriage theorem.
Coauthors: @kmill @b-mehta
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* compl_ne_univ_iff_nonempty
- \+ *lemma* finset.card_eq_iff_eq_univ
- \+ *lemma* finset.card_lt_iff_ne_univ
- \+ *lemma* finset.card_compl_lt_iff_nonempty



## [2021-01-25 17:49:32](https://github.com/leanprover-community/mathlib/commit/7f25aa7)
chore(algebra/group_with_zero): correct instance name ([#5885](https://github.com/leanprover-community/mathlib/pull/5885))
The argument for this definition is `cancel_monoid_with_zero`, not `comm_cancel_monoid_with_zero`.
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean




## [2021-01-25 17:49:30](https://github.com/leanprover-community/mathlib/commit/3a16e9f)
feat(data/set/finite): add to_finset lemma ([#5883](https://github.com/leanprover-community/mathlib/pull/5883))
Add lemma stating that taking to_finset of the union of two sets is the same as taking the union of to_finset of the sets.
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* to_finset_union



## [2021-01-25 17:49:28](https://github.com/leanprover-community/mathlib/commit/ba87647)
feat(data/set/finite): add lemma about to_finset of complement of set ([#5881](https://github.com/leanprover-community/mathlib/pull/5881))
Add lemma stating that taking to_finset of the complement of a set is the same thing as taking the complement of to_finset of the set.
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* to_finset_compl



## [2021-01-25 17:49:25](https://github.com/leanprover-community/mathlib/commit/7188d80)
chore(algebra/pi_tensor_product): Replace use of classical with decidable_eq ([#5880](https://github.com/leanprover-community/mathlib/pull/5880))
This makes it consistent with `multilinear_map`, which also uses explicit decidability assumptions
#### Estimated changes
Modified src/linear_algebra/pi_tensor_product.lean




## [2021-01-25 17:49:23](https://github.com/leanprover-community/mathlib/commit/1dfa81a)
feat(analysis/normed_space/inner_product): double orthogonal complement is closure ([#5876](https://github.com/leanprover-community/mathlib/pull/5876))
Put a submodule structure on the closure (as a set in a topological space) of a submodule of a topological module.  Show that in a complete inner product space, the double orthogonal complement of a submodule is its closure.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* coe_mul_self_eq

Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* submodule.orthogonal_orthogonal_monotone
- \+ *lemma* submodule.orthogonal_orthogonal_eq_closure

Modified src/topology/algebra/module.lean
- \+ *lemma* submodule.closure_smul_self_subset
- \+ *lemma* submodule.closure_smul_self_eq
- \+ *lemma* submodule.submodule_topological_closure
- \+ *lemma* submodule.is_closed_topological_closure
- \+ *lemma* submodule.topological_closure_minimal
- \+ *def* submodule.topological_closure

Modified src/topology/algebra/monoid.lean
- \+ *lemma* submonoid.top_closure_mul_self_subset
- \+ *lemma* submonoid.top_closure_mul_self_eq
- \+ *lemma* submonoid.submonoid_topological_closure
- \+ *lemma* submonoid.is_closed_topological_closure
- \+ *lemma* submonoid.topological_closure_minimal
- \+ *def* submonoid.topological_closure



## [2021-01-25 17:49:21](https://github.com/leanprover-community/mathlib/commit/ee750e3)
chore(algebra): a few more `@[mono]` tags ([#5874](https://github.com/leanprover-community/mathlib/pull/5874))
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+/\- *lemma* pow_le_pow_of_le_left

Modified src/algebra/ordered_field.lean
- \+/\- *lemma* div_le_div_of_le
- \+/\- *lemma* div_le_div_of_le_left
- \+/\- *lemma* div_le_div



## [2021-01-25 16:06:54](https://github.com/leanprover-community/mathlib/commit/6d80634)
feat(measure_theory/{measure_space, borel_space, integration}): prove ae_measurable for various limits ([#5849](https://github.com/leanprover-community/mathlib/pull/5849))
For a sequence of `ae_measurable` functions verifying some pointwise property almost everywhere, introduce a sequence of measurable functions verifying the same property and use it to prove ae-measurability of `is_lub`, `is_glb`, `supr`, `infi`, and almost everywhere pointwise limit.
#### Estimated changes
Created src/measure_theory/ae_measurable_sequence.lean
- \+ *lemma* mk_eq_fun_of_mem_ae_seq_set
- \+ *lemma* ae_seq_eq_mk_of_mem_ae_seq_set
- \+ *lemma* ae_seq_eq_fun_of_mem_ae_seq_set
- \+ *lemma* prop_of_mem_ae_seq_set
- \+ *lemma* fun_prop_of_mem_ae_seq_set
- \+ *lemma* ae_seq_set_is_measurable
- \+ *lemma* measurable
- \+ *lemma* measure_compl_ae_seq_set_eq_zero
- \+ *lemma* ae_seq_eq_mk_ae
- \+ *lemma* ae_seq_eq_fun_ae
- \+ *lemma* ae_seq_n_eq_fun_n_ae
- \+ *lemma* supr
- \+ *def* ae_seq_set
- \+ *def* ae_seq

Modified src/measure_theory/borel_space.lean
- \+ *lemma* ae_measurable.is_lub
- \+ *lemma* ae_measurable.is_glb
- \+ *lemma* ae_measurable_supr
- \+ *lemma* ae_measurable_infi
- \+ *lemma* ae_measurable_bsupr
- \+ *lemma* ae_measurable_binfi
- \+ *lemma* ae_measurable_of_tendsto_metric_ae
- \+ *lemma* measurable_of_tendsto_metric_ae
- \+ *lemma* measurable_limit_of_tendsto_metric_ae

Modified src/measure_theory/integration.lean
- \+/\- *lemma* lintegral_mono_ae
- \+/\- *lemma* lintegral_congr_ae
- \+/\- *lemma* lintegral_congr
- \+/\- *lemma* set_lintegral_congr
- \+ *lemma* lintegral_liminf_le'
- \+/\- *lemma* lintegral_liminf_le
- \+ *theorem* lintegral_supr'

Modified src/measure_theory/measure_space.lean
- \+ *lemma* ite_ae_eq_of_measure_zero
- \+ *lemma* ite_ae_eq_of_measure_compl_zero
- \+ *lemma* ae_measurable_of_zero_measure



## [2021-01-25 14:56:46](https://github.com/leanprover-community/mathlib/commit/d6d4435)
chore(archive/sensitivity): split long lines ([#5882](https://github.com/leanprover-community/mathlib/pull/5882))
#### Estimated changes
Modified archive/sensitivity.lean




## [2021-01-25 05:26:45](https://github.com/leanprover-community/mathlib/commit/9117ad7)
feat(order/atoms): define (co)atomic, (co)atomistic lattices ([#5588](https://github.com/leanprover-community/mathlib/pull/5588))
Define (co)atomic, (co)atomistic lattices
Relate these lattice definitions
Provide basic subtype instances
#### Estimated changes
Modified src/order/atoms.lean
- \+ *lemma* is_atom.Iic
- \+ *lemma* is_atom.of_is_atom_coe_Iic
- \+ *lemma* is_coatom.Ici
- \+ *lemma* is_coatom.of_is_coatom_coe_Ici
- \+ *lemma* is_coatom_dual_iff_is_atom
- \+ *lemma* is_atom_dual_iff_is_coatom
- \+/\- *lemma* is_coatom_bot
- \- *lemma* is_atom_iff_is_coatom_dual
- \- *lemma* is_coatom_iff_is_atom_dual
- \+ *theorem* is_coatomic_dual_iff_is_atomic
- \+ *theorem* is_atomic_dual_iff_is_coatomic
- \+ *theorem* is_atomic_iff_forall_is_atomic_Iic
- \+ *theorem* is_coatomic_iff_forall_is_coatomic_Ici
- \+ *theorem* is_coatomistic_dual_iff_is_atomistic
- \+ *theorem* is_atomistic_dual_iff_is_coatomistic



## [2021-01-25 04:13:48](https://github.com/leanprover-community/mathlib/commit/87202fe)
chore(scripts): update nolints.txt ([#5873](https://github.com/leanprover-community/mathlib/pull/5873))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-25 01:08:37](https://github.com/leanprover-community/mathlib/commit/507c7ff)
feat(analysis/specific_limits): formula for `∑' n, n * r ^ n` ([#5835](https://github.com/leanprover-community/mathlib/pull/5835))
Also prove that `∑' n, n ^ k * r ^ n` is summable for any `k : ℕ`,
`∥r∥ < 1`.
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean


Modified src/analysis/asymptotics.lean
- \+ *lemma* summable_of_is_O
- \+ *lemma* summable_of_is_O_nat
- \+/\- *theorem* is_O_with_bot
- \+/\- *theorem* is_O_bot
- \+/\- *theorem* is_o_bot
- \+ *theorem* is_O_with.pow'
- \+ *theorem* is_O_with.pow
- \+ *theorem* is_O.pow
- \+ *theorem* is_o.pow

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* nat.norm_cast_le

Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/specific_limits.lean
- \+ *lemma* is_o_pow_const_const_pow_of_one_lt
- \+ *lemma* is_o_coe_const_pow_of_one_lt
- \+ *lemma* is_o_pow_const_mul_const_pow_const_pow_of_norm_lt
- \+ *lemma* tendsto_pow_const_div_const_pow_of_one_lt
- \+ *lemma* tendsto_pow_const_mul_const_pow_of_abs_lt_one
- \+ *lemma* summable_norm_pow_mul_geometric_of_norm_lt_1
- \+ *lemma* summable_pow_mul_geometric_of_norm_lt_1
- \+ *lemma* has_sum_coe_mul_geometric_of_norm_lt_1
- \+ *lemma* tsum_coe_mul_geometric_of_norm_lt_1

Modified src/data/nat/basic.lean
- \+ *lemma* rec_zero
- \+ *lemma* rec_add_one

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/instances/ennreal.lean
- \+ *lemma* nhds_within_Ioi_coe_ne_bot
- \+ *lemma* nhds_within_Ioi_zero_ne_bot



## [2021-01-24 23:21:23](https://github.com/leanprover-community/mathlib/commit/5222db0)
chore(linear_algebra/multilinear): Relax ring to semiring, add_comm_group to add_comm_monoid ([#5870](https://github.com/leanprover-community/mathlib/pull/5870))
#### Estimated changes
Modified src/linear_algebra/multilinear.lean




## [2021-01-24 20:25:01](https://github.com/leanprover-community/mathlib/commit/fbabe42)
feat(order/complete_well_founded, data/finset/lattice): introduce compact elements of a complete lattice and characterize compact lattices as those with all elements compact ([#5825](https://github.com/leanprover-community/mathlib/pull/5825))
Provide a definition of compact elements. Prove the equivalence of two characterizations of compact elements. Add "all elements are compact" to the equivalent characterizations of compact lattices. Introduce an auxiliary lemma about finite sups and directed sets.
<!--
A reference for the two equivalent definitions of compact element can be found [here](https://ncatlab.org/nlab/show/compact+element+in+a+lattice)
-->
#### Estimated changes
Modified src/algebra/lie/basic.lean


Modified src/data/finset/lattice.lean
- \+ *lemma* sup_le_of_le_directed

Created src/order/compactly_generated.lean
- \+ *lemma* well_founded.is_Sup_finite_compact
- \+ *lemma* is_Sup_finite_compact.is_sup_closed_compact
- \+ *lemma* is_sup_closed_compact.well_founded
- \+ *lemma* is_Sup_finite_compact_iff_all_elements_compact
- \+ *lemma* well_founded_characterisations
- \+ *lemma* well_founded_iff_is_Sup_finite_compact
- \+ *lemma* is_Sup_finite_compact_iff_is_sup_closed_compact
- \+ *lemma* is_sup_closed_compact_iff_well_founded
- \+ *lemma* compactly_generated_of_well_founded
- \+ *theorem* is_compact_element_iff_le_of_directed_Sup_le
- \+ *def* is_sup_closed_compact
- \+ *def* is_Sup_finite_compact
- \+ *def* is_compact_element
- \+ *def* is_compactly_generated

Deleted src/order/complete_well_founded.lean
- \- *lemma* well_founded.is_Sup_finite_compact
- \- *lemma* is_Sup_finite_compact.is_sup_closed_compact
- \- *lemma* is_sup_closed_compact.well_founded
- \- *lemma* well_founded_characterisations
- \- *lemma* well_founded_iff_is_Sup_finite_compact
- \- *lemma* is_Sup_finite_compact_iff_is_sup_closed_compact
- \- *lemma* is_sup_closed_compact_iff_well_founded
- \- *def* is_sup_closed_compact
- \- *def* is_Sup_finite_compact



## [2021-01-24 13:41:30](https://github.com/leanprover-community/mathlib/commit/5db7a18)
feat(data/nat/basic): add decidable_exists_lt deciding existence of a natural below a bound satisfying a predicate ([#5864](https://github.com/leanprover-community/mathlib/pull/5864))
Given a decidable predicate `P` on naturals it is decidable if there is a natural below any bound satisying the `P`.
closes [#5755](https://github.com/leanprover-community/mathlib/pull/5755)
#### Estimated changes
Modified src/data/nat/basic.lean




## [2021-01-24 10:50:05](https://github.com/leanprover-community/mathlib/commit/49c53d4)
feat(measure_theory/lp_space): define Lp, subtype of ae_eq_fun with finite norm ([#5853](https://github.com/leanprover-community/mathlib/pull/5853))
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm_ae_eq_fun
- \+ *lemma* mem_ℒp.snorm_mk_lt_top
- \+ *lemma* mem_ℒp.coe_fn_to_Lp
- \+ *lemma* mem_Lp_iff_snorm_lt_top
- \+ *lemma* antimono
- \+ *lemma* coe_fn_mk
- \+ *lemma* snorm_lt_top
- \+ *lemma* snorm_ne_top
- \+ *lemma* measurable
- \+ *lemma* ae_measurable
- \+ *lemma* mem_ℒp
- \+ *lemma* coe_fn_zero
- \+ *lemma* coe_fn_neg
- \+ *lemma* coe_fn_add
- \+ *lemma* coe_fn_sub
- \+ *lemma* mem_Lp_const
- \+ *lemma* norm_def
- \+ *lemma* norm_zero
- \+ *lemma* norm_eq_zero_iff
- \+ *lemma* norm_neg
- \+ *lemma* mem_Lp_const_smul
- \+ *lemma* coe_fn_smul
- \+ *lemma* norm_const_smul
- \+ *def* Lp
- \+ *def* mem_ℒp.to_Lp



## [2021-01-24 06:50:40](https://github.com/leanprover-community/mathlib/commit/aa744db)
feat(topology/subset_properties): a locally compact space with second countable topology is sigma compact ([#5689](https://github.com/leanprover-community/mathlib/pull/5689))
* add `set.subsingleton.induction_on`, `set.Union_eq_univ_iff`, and `set.bUnion_eq_univ_iff`;
* make `tactic.interactive.nontrivial` try `apply_instance` before
  `simp`;
* add `dense.inter_nhds_nonempty`;
* a subsingleton is compact (lemma for sets, instance for spaces);
* in a locally compact space, every point has a compact neighborhood;
* a compact space is sigma compact;
* a locally compact space with second countable topology is sigma
  compact;
* add `dense.bUnion_uniformity_ball`: the uniform neighborhoods of all
  points of a dense set cover the whole space
Some of these changes are leftovers from a failed attempt to prove a
wrong statement.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* subsingleton.induction_on

Modified src/data/set/lattice.lean
- \+ *lemma* Union_eq_univ_iff
- \+ *lemma* bUnion_eq_univ_iff

Modified src/logic/nontrivial.lean


Modified src/topology/algebra/group.lean


Modified src/topology/basic.lean
- \+ *lemma* dense.inter_nhds_nonempty

Modified src/topology/subset_properties.lean
- \+ *lemma* set.subsingleton.is_compact
- \+ *lemma* exists_compact_mem_nhds
- \+ *lemma* sigma_compact_space.of_countable
- \+ *lemma* sigma_compact_space_of_locally_compact_second_countable

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* dense.bUnion_uniformity_ball



## [2021-01-24 03:45:38](https://github.com/leanprover-community/mathlib/commit/f414fca)
feat(analysis/analytic/composition): filling small holes in existing API ([#5822](https://github.com/leanprover-community/mathlib/pull/5822))
This PR expands the existing API around the composition of formal multilinear series.
Also makes the `finset` argument to `finset.prod_subtype` and `finset.add_subtype` explicit instead of implicit.
#### Estimated changes
Modified src/analysis/analytic/composition.lean
- \+ *lemma* apply_composition_single
- \+ *lemma* remove_zero_apply_composition
- \+ *lemma* comp_continuous_linear_map_apply_composition
- \+ *lemma* comp_along_composition_aux_bound
- \+ *lemma* comp_along_composition_apply
- \+ *lemma* comp_coeff_one
- \+ *lemma* remove_zero_comp_of_pos
- \+ *lemma* comp_remove_zero
- \- *lemma* comp_along_composition_multilinear_bound
- \+/\- *theorem* id_comp
- \+ *def* comp_along_composition_aux
- \+ *def* comp_along_composition
- \- *def* comp_along_composition_multilinear

Modified src/analysis/calculus/formal_multilinear_series.lean
- \+ *lemma* remove_zero_coeff_zero
- \+ *lemma* remove_zero_coeff_succ
- \+ *lemma* remove_zero_of_pos
- \+ *lemma* comp_continuous_linear_map_apply
- \+ *def* remove_zero
- \+ *def* comp_continuous_linear_map

Modified src/combinatorics/composition.lean
- \+ *lemma* blocks_fun_mem_blocks
- \+ *lemma* one_le_blocks_fun
- \+ *lemma* eq_ones_iff_length
- \+ *lemma* eq_ones_iff_le_length
- \+ *lemma* eq_single_iff_length
- \+ *lemma* ne_single_iff
- \- *lemma* eq_single_iff
- \+/\- *def* blocks_fun

Modified src/data/fintype/basic.lean
- \+ *lemma* card_eq_one_of_forall_eq

Modified src/data/fintype/card.lean
- \+ *lemma* finset.prod_to_finset_eq_subtype

Modified src/ring_theory/integral_domain.lean




## [2021-01-24 02:20:04](https://github.com/leanprover-community/mathlib/commit/160d243)
chore(scripts): update nolints.txt ([#5865](https://github.com/leanprover-community/mathlib/pull/5865))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-23 13:02:18](https://github.com/leanprover-community/mathlib/commit/8da574f)
feat(algebra/pointwise): a lemma about pointwise addition/multiplication of bdd_above sets ([#5859](https://github.com/leanprover-community/mathlib/pull/5859))
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* bdd_above_mul



## [2021-01-23 13:02:16](https://github.com/leanprover-community/mathlib/commit/3a136f8)
refactor(analysis/analytic/composition): extend definition, extract a lemma from a proof ([#5850](https://github.com/leanprover-community/mathlib/pull/5850))
Extract a standalone lemma of the proof that the composition of two analytic functions is well-behaved, and extend a little bit the definition of the sets which are involved in the corresponding change of variables.
#### Estimated changes
Modified src/analysis/analytic/composition.lean
- \+/\- *lemma* mem_comp_partial_sum_source_iff
- \+/\- *lemma* mem_comp_partial_sum_target_iff
- \+ *lemma* comp_change_of_variables_sum
- \+/\- *def* comp_partial_sum_source
- \+/\- *def* comp_change_of_variables
- \+/\- *def* comp_partial_sum_target_set
- \+/\- *def* comp_partial_sum_target



## [2021-01-23 11:06:24](https://github.com/leanprover-community/mathlib/commit/74760f2)
chore(set_theory/ordinal): use rel_iso notation in ordinal ([#5857](https://github.com/leanprover-community/mathlib/pull/5857))
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+/\- *def* rel_iso_out



## [2021-01-23 07:40:00](https://github.com/leanprover-community/mathlib/commit/013b902)
feat(order/rel_iso): generalise several lemmas to assume only has_le not preorder ([#5858](https://github.com/leanprover-community/mathlib/pull/5858))
#### Estimated changes
Modified src/order/rel_iso.lean
- \+/\- *lemma* coe_to_order_embedding
- \+/\- *lemma* le_iff_le
- \+/\- *lemma* lt_iff_lt
- \+/\- *def* to_order_embedding



## [2021-01-23 02:17:47](https://github.com/leanprover-community/mathlib/commit/b0e874e)
chore(scripts): update nolints.txt ([#5856](https://github.com/leanprover-community/mathlib/pull/5856))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-22 21:50:00](https://github.com/leanprover-community/mathlib/commit/04972f6)
docs(undergrad.yaml): update with [#5724](https://github.com/leanprover-community/mathlib/pull/5724) and [#5788](https://github.com/leanprover-community/mathlib/pull/5788) ([#5855](https://github.com/leanprover-community/mathlib/pull/5855))
Add results from a couple of recent PRs.  Also correct an apparent oversight from the translation of the file.
#### Estimated changes
Modified docs/undergrad.yaml




## [2021-01-22 17:20:38](https://github.com/leanprover-community/mathlib/commit/3250fc3)
feat(analysis/mean_inequalities, measure_theory/lp_space): extend mem_Lp.add to all p in ennreal ([#5828](https://github.com/leanprover-community/mathlib/pull/5828))
Show `(a ^ q + b ^ q) ^ (1/q) ≤ (a ^ p + b ^ p) ^ (1/p)` for `a,b : ennreal` and `0 < p <= q`.
Use it to show that for `p <= 1`, if measurable functions `f` and `g` are in Lp, `f+g` is also in Lp (the case `1 <= p` is already done).
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *lemma* add_rpow_le_rpow_add
- \+ *lemma* rpow_add_rpow_le_add
- \+ *lemma* rpow_add_le_add_rpow
- \+ *theorem* rpow_add_rpow_le

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* div_rpow_of_nonneg
- \+ *lemma* rpow_le_self_of_le_one
- \+ *lemma* le_rpow_self_of_one_le

Modified src/measure_theory/integration.lean
- \+ *lemma* lintegral_count'
- \+ *lemma* lintegral_count

Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm_add_lt_top_of_one_le
- \+ *lemma* snorm'_add_lt_top_of_le_one
- \+ *lemma* snorm_add_lt_top
- \+/\- *lemma* mem_ℒp.add
- \+/\- *lemma* mem_ℒp.sub



## [2021-01-22 16:01:54](https://github.com/leanprover-community/mathlib/commit/f48ce7e)
feat(algebra/lie/basic): define the radical of a Lie algebra and prove it is solvable ([#5833](https://github.com/leanprover-community/mathlib/pull/5833))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+/\- *lemma* coe_to_submodule
- \+/\- *lemma* mem_carrier
- \+/\- *lemma* mem_coe_submodule
- \+/\- *lemma* mem_coe
- \+ *lemma* zero_mem
- \+/\- *lemma* ext
- \+/\- *lemma* coe_to_submodule_eq_iff
- \+ *lemma* of_bot_eq_bot
- \+ *lemma* unique_of_bot
- \+/\- *lemma* derived_series_add_eq_bot
- \+ *def* radical



## [2021-01-22 12:52:31](https://github.com/leanprover-community/mathlib/commit/cb618e0)
feat(analysis/analytic): a continuous linear map defines an analytic function ([#5840](https://github.com/leanprover-community/mathlib/pull/5840))
Also add convenience lemmas with conclusion `radius = ⊤`.
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+ *lemma* radius_eq_top_of_forall_nnreal_is_O
- \+ *lemma* radius_eq_top_of_eventually_eq_zero
- \+ *lemma* radius_eq_top_of_forall_image_add_eq_zero

Created src/analysis/analytic/linear.lean
- \+ *lemma* fpower_series_apply_add_two
- \+ *lemma* fpower_series_radius
- \+ *def* fpower_series

Modified src/data/real/ennreal.lean
- \+ *lemma* eq_top_of_forall_nnreal_le



## [2021-01-22 12:52:30](https://github.com/leanprover-community/mathlib/commit/faba9ce)
chore(algebra/group_power): generalize `semiring` version of Bernoulli's inequality ([#5831](https://github.com/leanprover-community/mathlib/pull/5831))
Now `one_add_mul_le_pow'` assumes `0 ≤ a * a`, `0 ≤ (1 + a) * (1 +
a)`, and `0 ≤ 2 + a`.
Also add a couple of convenience lemmas.
#### Estimated changes
Modified src/algebra/archimedean.lean


Modified src/algebra/group_power/lemmas.lean
- \+/\- *theorem* one_add_mul_le_pow'
- \+/\- *theorem* one_add_mul_le_pow
- \+ *theorem* one_add_mul_sub_le_pow
- \+ *theorem* nat.cast_le_pow_sub_div_sub
- \+ *theorem* nat.cast_le_pow_div_sub
- \- *theorem* one_add_sub_mul_le_pow



## [2021-01-22 12:52:28](https://github.com/leanprover-community/mathlib/commit/0feb1d2)
feat(measure_theory/interval_integral) : add integration by parts ([#5724](https://github.com/leanprover-community/mathlib/pull/5724))
A direct application of FTC-2 for interval_integral.
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* integral_congr
- \+ *lemma* integral_deriv_mul_eq_sub
- \+ *theorem* integral_mul_deriv_eq_deriv_mul

Modified src/measure_theory/measure_space.lean
- \+ *lemma* self_mem_ae_restrict



## [2021-01-22 12:52:26](https://github.com/leanprover-community/mathlib/commit/de10203)
feat(order/modular_lattice): define modular lattices ([#5564](https://github.com/leanprover-community/mathlib/pull/5564))
Defines modular lattices
Defines the diamond isomorphisms in a modular lattice
Places `is_modular_lattice` instances on a `distrib_lattice`, the lattice of `subgroup`s of a `comm_group`, and the lattice of `submodule`s of a `module`.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* mem_sup
- \+ *lemma* mem_sup'

Modified src/linear_algebra/basic.lean


Modified src/order/atoms.lean
- \+ *lemma* is_atom_iff_is_coatom
- \+ *lemma* is_coatom_iff_is_atom

Created src/order/modular_lattice.lean
- \+ *lemma* inf_sup_assoc_of_le
- \+ *theorem* sup_inf_assoc_of_le
- \+ *theorem* is_modular_lattice.sup_inf_sup_assoc
- \+ *theorem* is_modular_lattice_iff_sup_inf_sup_assoc
- \+ *def* inf_Icc_order_iso_Icc_sup
- \+ *def* Iic_order_iso_Ici



## [2021-01-22 09:40:49](https://github.com/leanprover-community/mathlib/commit/38ae9b3)
chore(data/nat/basic): reuse a proof, drop a duplicate ([#5836](https://github.com/leanprover-community/mathlib/pull/5836))
Drop `nat.div_mul_le_self'`, use `nat.div_mul_le_self` instead.
#### Estimated changes
Modified src/data/nat/basic.lean
- \- *theorem* div_mul_le_self'



## [2021-01-22 07:39:51](https://github.com/leanprover-community/mathlib/commit/8b4c455)
feat(data/polynomial/algebra_map): aeval_map ([#5843](https://github.com/leanprover-community/mathlib/pull/5843))
Proves `aeval_map`, which relates `aeval` within an `is_scalar_tower`.
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* aeval_map



## [2021-01-22 06:16:16](https://github.com/leanprover-community/mathlib/commit/bef50a4)
feat(field_theory/minpoly): Minimal polynomials of degree one ([#5844](https://github.com/leanprover-community/mathlib/pull/5844))
If the minimal polynomial has degree one then the element in question lies in the base ring.
#### Estimated changes
Modified src/field_theory/minpoly.lean
- \+ *lemma* eq_zero
- \+ *lemma* mem_range_of_degree_eq_one



## [2021-01-22 04:19:57](https://github.com/leanprover-community/mathlib/commit/6958d8c)
feat(topology/metric_space/{basic,emetric_space}): product of balls of the same size ([#5846](https://github.com/leanprover-community/mathlib/pull/5846))
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *theorem* ball_prod_same
- \+ *theorem* closed_ball_prod_same

Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* ball_prod_same
- \+ *theorem* closed_ball_prod_same



## [2021-01-22 02:55:27](https://github.com/leanprover-community/mathlib/commit/244b3ed)
chore(scripts): update nolints.txt ([#5841](https://github.com/leanprover-community/mathlib/pull/5841))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-21 23:47:37](https://github.com/leanprover-community/mathlib/commit/c681f48)
chore(analysis/analytic/composition): minor golfing ([#5839](https://github.com/leanprover-community/mathlib/pull/5839))
#### Estimated changes
Modified src/analysis/analytic/composition.lean




## [2021-01-21 23:47:32](https://github.com/leanprover-community/mathlib/commit/228c00b)
feat(computability/language): le on languages ([#5704](https://github.com/leanprover-community/mathlib/pull/5704))
#### Estimated changes
Modified src/computability/language.lean
- \+ *lemma* mem_one
- \+ *lemma* mem_add
- \+ *lemma* mem_mul
- \+ *lemma* mem_star
- \+/\- *lemma* add_self
- \+ *lemma* le_iff
- \+ *lemma* le_mul_congr
- \+ *lemma* le_add_congr
- \+ *lemma* supr_mul
- \+ *lemma* mul_supr
- \+ *lemma* supr_add
- \+ *lemma* add_supr
- \+ *lemma* star_eq_supr_pow
- \+ *lemma* mul_self_star_comm
- \+ *lemma* one_add_self_mul_star_eq_star
- \+ *lemma* one_add_star_mul_self_eq_star
- \+ *lemma* star_mul_le_right_of_mul_le_right
- \+ *lemma* star_mul_le_left_of_mul_le_left

Modified src/order/complete_lattice.lean
- \+ *lemma* supr_sup
- \+ *lemma* sup_supr



## [2021-01-21 20:47:04](https://github.com/leanprover-community/mathlib/commit/b2ca761)
chore(algebra/group_power): add `(a+b)^2=a^2+2ab+b^2` ([#5838](https://github.com/leanprover-community/mathlib/pull/5838))
Also generalize 2 lemmas from `comm_semiring` to `semiring`.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *lemma* add_pow_two

Modified src/algebra/ring/basic.lean
- \+/\- *theorem* dvd_add



## [2021-01-21 18:59:17](https://github.com/leanprover-community/mathlib/commit/fac0f25)
fix(tactic/default): make field_simp work with import tactic ([#5832](https://github.com/leanprover-community/mathlib/pull/5832))
#### Estimated changes
Modified src/tactic/default.lean




## [2021-01-21 14:01:20](https://github.com/leanprover-community/mathlib/commit/b52b304)
feat(algebra/lie/basic): show `I + J` is solvable if Lie ideals `I`, `J` are solvable ([#5819](https://github.com/leanprover-community/mathlib/pull/5819))
The key result is `lie_algebra.is_solvable_add`
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+/\- *lemma* derived_series_of_ideal_add
- \+/\- *lemma* derived_series_of_ideal_succ_le
- \+/\- *lemma* derived_series_of_ideal_le_self
- \+/\- *lemma* derived_series_of_ideal_mono
- \+/\- *lemma* derived_series_of_ideal_antimono
- \+ *lemma* derived_series_of_ideal_add_le_add
- \+ *lemma* lower_central_series_zero
- \+ *lemma* lower_central_series_succ
- \+ *lemma* derived_series_add_eq_bot
- \+/\- *def* derived_series_of_ideal
- \+/\- *def* lower_central_series

Modified src/order/preorder_hom.lean
- \+ *lemma* iterate_sup_le_sup_iff



## [2021-01-21 11:18:02](https://github.com/leanprover-community/mathlib/commit/3ef8281)
fix(group_theory/group_action/defs): fix minor typo ([#5827](https://github.com/leanprover-community/mathlib/pull/5827))
heirarchy -> hierarchy
#### Estimated changes
Modified src/group_theory/group_action/defs.lean




## [2021-01-21 11:17:59](https://github.com/leanprover-community/mathlib/commit/b3a2112)
chore(algebra/group/conj): move `conj_injective` and use existing proofs ([#5798](https://github.com/leanprover-community/mathlib/pull/5798))
#### Estimated changes
Modified src/algebra/group/conj.lean
- \+ *lemma* conj_injective

Modified src/group_theory/order_of_element.lean
- \- *lemma* conj_injective



## [2021-01-21 11:17:58](https://github.com/leanprover-community/mathlib/commit/d66d563)
feat(measure_theory/interval_integral): FTC-2 for the open set ([#5733](https://github.com/leanprover-community/mathlib/pull/5733))
A follow-up to [#4945](https://github.com/leanprover-community/mathlib/pull/4945). I replaced `integral_eq_sub_of_has_deriv_at'` with a stronger version that holds for functions that have a derivative on an `Ioo` (as opposed to an `Ico`). Inspired by [this](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/FTC-2.20on.20open.20set/near/222177308) conversation on Zulip.
I also emended docstrings to reflect changes made in [#5647](https://github.com/leanprover-community/mathlib/pull/5647).
#### Estimated changes
Modified src/measure_theory/interval_integral.lean




## [2021-01-21 08:15:25](https://github.com/leanprover-community/mathlib/commit/ce9bc68)
feat(ring_theory/polynomial): symmetric polynomials and elementary symmetric polynomials ([#5788](https://github.com/leanprover-community/mathlib/pull/5788))
Define symmetric polynomials and elementary symmetric polynomials, and prove some basic facts about them.
#### Estimated changes
Modified src/data/finset/powerset.lean
- \+ *lemma* powerset_len_zero

Created src/ring_theory/polynomial/symmetric.lean
- \+ *lemma* C
- \+ *lemma* zero
- \+ *lemma* one
- \+ *lemma* add
- \+ *lemma* mul
- \+ *lemma* smul
- \+ *lemma* map
- \+ *lemma* neg
- \+ *lemma* sub
- \+ *lemma* esymm_eq_sum_subtype
- \+ *lemma* esymm_eq_sum_monomial
- \+ *lemma* esymm_zero
- \+ *lemma* map_esymm
- \+ *lemma* rename_esymm
- \+ *lemma* esymm_is_symmetric
- \+ *def* is_symmetric
- \+ *def* esymm



## [2021-01-21 02:18:43](https://github.com/leanprover-community/mathlib/commit/a19e48b)
chore(scripts): update nolints.txt ([#5826](https://github.com/leanprover-community/mathlib/pull/5826))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-20 22:33:10](https://github.com/leanprover-community/mathlib/commit/b2d95c0)
feat(data/nat/modeq): Generalised version of the Chinese remainder theorem ([#5683](https://github.com/leanprover-community/mathlib/pull/5683))
That allows the moduli to not be coprime, assuming the necessary condition. Old crt is now in terms of this one
#### Estimated changes
Modified src/algebra/euclidean_domain.lean
- \+ *theorem* gcd_a_zero_left
- \+ *theorem* gcd_b_zero_left

Modified src/data/int/basic.lean
- \+ *lemma* sub_div_of_dvd
- \+ *lemma* sub_div_of_dvd_sub

Modified src/data/int/gcd.lean
- \+ *theorem* gcd_a_zero_left
- \+ *theorem* gcd_b_zero_left
- \+ *theorem* gcd_a_zero_right
- \+ *theorem* gcd_b_zero_right

Modified src/data/nat/gcd.lean
- \+ *theorem* gcd_eq_zero_iff
- \+ *theorem* lcm_ne_zero

Modified src/data/nat/modeq.lean
- \+ *theorem* modeq_one
- \+ *def* chinese_remainder'



## [2021-01-20 19:25:37](https://github.com/leanprover-community/mathlib/commit/8b6f541)
feat(field_theory/normal): Splitting field is normal ([#5768](https://github.com/leanprover-community/mathlib/pull/5768))
Proves that splitting fields are normal.
#### Estimated changes
Modified src/field_theory/normal.lean
- \+ *lemma* normal.of_is_splitting_field



## [2021-01-20 16:12:42](https://github.com/leanprover-community/mathlib/commit/7c89265)
chore(data/list/range): Add range_zero and rename range_concat to range_succ ([#5821](https://github.com/leanprover-community/mathlib/pull/5821))
The name `range_concat` was derived from `range'_concat`, where there are multiple possible expansions for `range' s n.succ`.
For `range` there is only one choice, and naming the lemma after the result rather than the statement makes it harder to find.
#### Estimated changes
Modified src/computability/partrec.lean


Modified src/computability/primrec.lean


Modified src/data/list/range.lean
- \+ *lemma* range_zero
- \+ *theorem* range_succ
- \- *theorem* range_concat

Modified src/data/multiset/range.lean




## [2021-01-20 14:40:22](https://github.com/leanprover-community/mathlib/commit/2ec396a)
chore(data/dfinsupp): add `dfinsupp.prod_comm` ([#5817](https://github.com/leanprover-community/mathlib/pull/5817))
This is the same lemma as `finsupp.prod_comm` but for dfinsupp
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* prod_comm



## [2021-01-20 11:51:00](https://github.com/leanprover-community/mathlib/commit/9cdffe9)
refactor(data/fin): shorter proof of `mk.inj_iff` ([#5811](https://github.com/leanprover-community/mathlib/pull/5811))
Co-authors: `lean-gptf`, Yuhuai Wu
#### Estimated changes
Modified src/data/fin.lean




## [2021-01-20 11:50:58](https://github.com/leanprover-community/mathlib/commit/c700791)
feat(data/list/range): nth_le_fin_range ([#5456](https://github.com/leanprover-community/mathlib/pull/5456))
#### Estimated changes
Modified src/data/list/range.lean
- \+ *lemma* nth_le_range'
- \+ *lemma* nth_le_fin_range



## [2021-01-20 11:50:56](https://github.com/leanprover-community/mathlib/commit/9ae3317)
feat(data/fin): add_comm_monoid and simp lemmas ([#5010](https://github.com/leanprover-community/mathlib/pull/5010))
Provide `add_comm_monoid` for `fin (n + 1)`, which makes proofs that have to do with `bit0`, `bit1`, and `nat.cast` and related happy. Provide the specialized lemmas as simp lemmas. Also provide various simp lemmas about multiplication, but without the associated `comm_monoid`.
#### Estimated changes
Modified src/data/fin.lean


Modified src/data/zmod/basic.lean
- \- *def* add_comm_semigroup



## [2021-01-20 09:51:08](https://github.com/leanprover-community/mathlib/commit/a7a4f34)
feat(algebraic_geometry/is_open_comap_C): add file is_open_comap_C, prove that Spec R[x] \to Spec R is an open map ([#5693](https://github.com/leanprover-community/mathlib/pull/5693))
This file is the first part of a proof of Chevalley's Theorem.  It contains a proof that the morphism Spec R[x] \to Spec R is open.  In a later PR, I hope to prove that, under the same morphism, the image of a closed set is constructible.
#### Estimated changes
Created src/algebraic_geometry/is_open_comap_C.lean
- \+ *lemma* is_open_image_of_Df
- \+ *lemma* comap_C_mem_image_of_Df
- \+ *lemma* image_of_Df_eq_comap_C_compl_zero_locus
- \+ *theorem* is_open_map_comap_C
- \+ *def* image_of_Df

Modified src/algebraic_geometry/prime_spectrum.lean
- \+ *lemma* mem_compl_zero_locus_iff_not_mem
- \+ *lemma* is_open_basic_open

Modified src/data/polynomial/coeff.lean
- \+ *lemma* span_le_of_coeff_mem_C_inverse
- \+ *lemma* mem_span_C_coeff
- \+ *lemma* exists_coeff_not_mem_C_inverse

Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* is_integral_domain_map_C_quotient
- \+ *lemma* is_prime_map_C_of_is_prime



## [2021-01-20 08:32:57](https://github.com/leanprover-community/mathlib/commit/0c57d1e)
feat(category_theory/monad): algebras for the coproduct monad ([#5679](https://github.com/leanprover-community/mathlib/pull/5679))
WIP, I'll fix it up when the dependent PRs merge
<!--
put comments you want to keep out of the PR commit here.
If this PR depends on other PRs, please list them below this comment,
using the following format:
- [ ] depends on: #abc [optional extra text]
- [ ] depends on: #xyz [optional extra text]
-->
- [x] depends on: [#5674](https://github.com/leanprover-community/mathlib/pull/5674)
- [x] depends on: [#5677](https://github.com/leanprover-community/mathlib/pull/5677) 
- [x] depends on: [#5678](https://github.com/leanprover-community/mathlib/pull/5678)
#### Estimated changes
Created src/category_theory/monad/products.lean
- \+ *def* coalgebra_to_over
- \+ *def* over_to_coalgebra
- \+ *def* coalgebra_equiv_over
- \+ *def* algebra_to_under
- \+ *def* under_to_algebra
- \+ *def* algebra_equiv_under



## [2021-01-20 06:40:59](https://github.com/leanprover-community/mathlib/commit/e41b917)
feat(char_p/quotient): Add a lemma to inherit char_p from the underlying ring ([#5809](https://github.com/leanprover-community/mathlib/pull/5809))
#### Estimated changes
Modified src/algebra/char_p/quotient.lean
- \+ *lemma* quotient'



## [2021-01-20 06:40:57](https://github.com/leanprover-community/mathlib/commit/385173d)
feat(ring_theory/ideal/operations): generalize quotient of algebras ([#5802](https://github.com/leanprover-community/mathlib/pull/5802))
I generalize [#5703](https://github.com/leanprover-community/mathlib/pull/5703) (that was merged earlier today... sorry for that, I should have thought more carefully about it) to be able to work with `S/I` as an `R`-algebra, where `S` is an `R`-algebra.  (In [#5703](https://github.com/leanprover-community/mathlib/pull/5703) only `R/I` was considered.) The proofs are the same.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* quotient.alg_map_eq
- \+/\- *lemma* quotient.mkₐ_to_ring_hom
- \+/\- *lemma* quotient.mkₐ_eq_mk
- \+/\- *lemma* quotient.mkₐ_surjective
- \+/\- *lemma* quotient.mkₐ_ker
- \+/\- *def* quotient.mkₐ



## [2021-01-20 06:40:55](https://github.com/leanprover-community/mathlib/commit/31fd5b5)
feat(category_theory/limits): preserve monomorphisms ([#5801](https://github.com/leanprover-community/mathlib/pull/5801))
A functor which preserves pullbacks also preserves monomorphisms.
#### Estimated changes
Created src/category_theory/limits/constructions/epi_mono.lean
- \+ *lemma* reflects_mono



## [2021-01-20 04:42:11](https://github.com/leanprover-community/mathlib/commit/a3ef65d)
feat(algebra/lie/basic): additional lemmas concerning `lie_algebra.derived_series_of_ideal` ([#5815](https://github.com/leanprover-community/mathlib/pull/5815))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* derived_series_of_ideal_add
- \+/\- *lemma* derived_series_of_ideal_le
- \+/\- *lemma* derived_series_of_ideal_succ_le
- \+ *lemma* derived_series_of_ideal_le_self
- \+ *lemma* derived_series_of_ideal_mono
- \+ *lemma* derived_series_of_ideal_antimono



## [2021-01-20 03:20:26](https://github.com/leanprover-community/mathlib/commit/b1d5673)
chore(scripts): update nolints.txt ([#5816](https://github.com/leanprover-community/mathlib/pull/5816))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-20 00:07:09](https://github.com/leanprover-community/mathlib/commit/d7a8709)
chore(algebra/group/hom): Add `mk_coe` lemmas ([#5812](https://github.com/leanprover-community/mathlib/pull/5812))
These are the counterparts to the `coe_mk` lemmas.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *theorem* mk_coe

Modified src/algebra/group/hom.lean
- \+ *lemma* one_hom.mk_coe
- \+ *lemma* mul_hom.mk_coe
- \+ *lemma* monoid_hom.mk_coe
- \+ *lemma* monoid_with_zero_hom.mk_coe

Modified src/algebra/module/linear_map.lean
- \+ *lemma* mk_coe

Modified src/algebra/ring/basic.lean
- \+ *lemma* mk_coe



## [2021-01-19 21:59:16](https://github.com/leanprover-community/mathlib/commit/b121429)
feat(measure_theory/lp_space): extend the definition of Lp seminorm to p ennreal ([#5808](https://github.com/leanprover-community/mathlib/pull/5808))
Rename the seminorm with real exponent to `snorm'`, introduce `snorm_ess_sup` for `L\infty`, equal to the essential supremum of the norm.
#### Estimated changes
Modified src/measure_theory/ess_sup.lean
- \+ *lemma* ae_le_ess_sup
- \+ *lemma* ess_sup_const_mul
- \+ *lemma* ess_sup_add_le
- \- *lemma* ennreal.ae_le_ess_sup
- \- *lemma* ennreal.ess_sup_const_mul
- \- *lemma* ennreal.ess_sup_add_le

Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm_eq_snorm'
- \+ *lemma* snorm_exponent_top
- \+ *lemma* lintegral_rpow_nnnorm_eq_rpow_snorm'
- \+/\- *lemma* mem_ℒp.snorm_lt_top
- \+/\- *lemma* mem_ℒp.snorm_ne_top
- \+ *lemma* lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top
- \+ *lemma* snorm'_exponent_zero
- \+/\- *lemma* snorm_exponent_zero
- \+ *lemma* mem_ℒp_zero_iff_ae_measurable
- \+ *lemma* snorm'_zero
- \+ *lemma* snorm'_zero'
- \+ *lemma* snorm_ess_sup_zero
- \+/\- *lemma* snorm_zero
- \+ *lemma* zero_mem_ℒp
- \+ *lemma* snorm'_measure_zero_of_pos
- \+ *lemma* snorm'_measure_zero_of_exponent_zero
- \+ *lemma* snorm'_measure_zero_of_neg
- \+ *lemma* snorm_ess_sup_measure_zero
- \+ *lemma* snorm_measure_zero
- \+ *lemma* snorm'_const
- \+ *lemma* snorm'_const'
- \+ *lemma* snorm_ess_sup_const
- \+ *lemma* snorm'_const_of_probability_measure
- \+/\- *lemma* snorm_const
- \+/\- *lemma* snorm_const'
- \+/\- *lemma* mem_ℒp_const
- \+ *lemma* snorm'_congr_ae
- \+ *lemma* snorm_ess_sup_congr_ae
- \+/\- *lemma* snorm_congr_ae
- \+/\- *lemma* mem_ℒp.ae_eq
- \+/\- *lemma* mem_ℒp_congr_ae
- \+ *lemma* snorm'_eq_zero_of_ae_zero
- \+ *lemma* snorm'_eq_zero_of_ae_zero'
- \+ *lemma* ae_eq_zero_of_snorm'_eq_zero
- \+ *lemma* snorm'_eq_zero_iff
- \+ *lemma* coe_nnnorm_ae_le_snorm_ess_sup
- \+ *lemma* snorm_ess_sup_eq_zero_iff
- \+/\- *lemma* snorm_eq_zero_iff
- \+ *lemma* snorm'_neg
- \+/\- *lemma* snorm_neg
- \+/\- *lemma* mem_ℒp.neg
- \+ *lemma* snorm'_le_snorm'_mul_rpow_measure_univ
- \+ *lemma* snorm'_le_snorm_ess_sup_mul_rpow_measure_univ
- \+ *lemma* snorm'_le_snorm'_of_exponent_le
- \+ *lemma* snorm'_le_snorm_ess_sup
- \+/\- *lemma* snorm_le_snorm_of_exponent_le
- \+ *lemma* snorm'_lt_top_of_snorm'_lt_top_of_exponent_le
- \+/\- *lemma* mem_ℒp.mem_ℒp_of_exponent_le
- \+/\- *lemma* mem_ℒp.integrable
- \+ *lemma* snorm'_add_le
- \+ *lemma* snorm_ess_sup_add_le
- \+/\- *lemma* snorm_add_le
- \+/\- *lemma* mem_ℒp.add
- \+/\- *lemma* mem_ℒp.sub
- \+ *lemma* snorm'_const_smul
- \+ *lemma* snorm_ess_sup_const_smul
- \+/\- *lemma* snorm_const_smul
- \+/\- *lemma* mem_ℒp.const_smul
- \+ *lemma* snorm'_smul_le_mul_snorm'
- \- *lemma* lintegral_rpow_nnnorm_eq_rpow_snorm
- \- *lemma* lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top
- \- *lemma* mem_ℒp_of_snorm_lt_top
- \- *lemma* zero_mem_ℒp_of_pos
- \- *lemma* zero_mem_ℒp_of_nonneg
- \- *lemma* snorm_zero'
- \- *lemma* snorm_measure_zero_of_pos
- \- *lemma* snorm_measure_zero_of_exponent_zero
- \- *lemma* snorm_measure_zero_of_neg
- \- *lemma* snorm_const_of_probability_measure
- \- *lemma* mem_ℒp_const_of_nonneg
- \- *lemma* mem_ℒp_const_of_ne_zero
- \- *lemma* snorm_eq_zero_of_ae_zero
- \- *lemma* snorm_eq_zero_of_ae_zero'
- \- *lemma* ae_eq_zero_of_snorm_eq_zero
- \- *lemma* snorm_le_snorm_mul_rpow_measure_univ
- \- *lemma* snorm_smul_le_mul_snorm
- \+ *def* snorm'
- \+ *def* snorm_ess_sup
- \+/\- *def* snorm
- \+/\- *def* mem_ℒp



## [2021-01-19 18:42:43](https://github.com/leanprover-community/mathlib/commit/9d14a5f)
chore(order/filter/basic): add `eventually_eq.rfl` and `eventually_le.rfl` ([#5805](https://github.com/leanprover-community/mathlib/pull/5805))
#### Estimated changes
Modified src/analysis/asymptotic_equivalent.lean


Modified src/measure_theory/interval_integral.lean


Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* ae_eq_refl

Modified src/order/filter/basic.lean
- \+ *lemma* eventually_eq.rfl
- \+ *lemma* eventually_le.rfl

Modified src/order/liminf_limsup.lean




## [2021-01-19 18:42:41](https://github.com/leanprover-community/mathlib/commit/21b0b01)
feat(analysis/normed_space,topology/metric_space): distance between diagonal vectors ([#5803](https://github.com/leanprover-community/mathlib/pull/5803))
Add formulas for (e|nn|)dist between `λ _, a` and `λ _, b` as well
as `∥(λ _, a)∥` and `nnnorm (λ _, a)`.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* pi_norm_const
- \+ *lemma* pi_nnnorm_const

Modified src/data/finset/basic.lean
- \+ *lemma* nonempty.forall_const

Modified src/data/finset/lattice.lean
- \+ *lemma* sup_const

Modified src/topology/metric_space/basic.lean
- \+ *lemma* dist_pi_const
- \+ *lemma* nndist_pi_const

Modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* edist_pi_const



## [2021-01-19 17:22:05](https://github.com/leanprover-community/mathlib/commit/da6e3c3)
feat(data/buffer/parser/numeral): numeral parser defs ([#5462](https://github.com/leanprover-community/mathlib/pull/5462))
#### Estimated changes
Created src/data/buffer/parser/numeral.lean
- \+ *def* get_fin
- \+ *def* numeral
- \+ *def* numeral.of_fintype
- \+ *def* numeral.from_one
- \+ *def* numeral.from_one.of_fintype
- \+ *def* numeral.char
- \+ *def* numeral.char.of_fintype



## [2021-01-19 13:11:48](https://github.com/leanprover-community/mathlib/commit/8b47563)
chore(category_theory/adjunction): move reflective functor lemmas ([#5800](https://github.com/leanprover-community/mathlib/pull/5800))
Moves a lemma and describes a generalisation.
#### Estimated changes
Modified src/category_theory/adjunction/reflective.lean
- \+ *lemma* unit_obj_eq_map_unit

Modified src/category_theory/monad/adjunction.lean
- \- *lemma* comparison_ess_surj_aux



## [2021-01-19 13:11:46](https://github.com/leanprover-community/mathlib/commit/90763c4)
feat(algebra/lie/basic): generalise the definition of `lie_algebra.derived_series` ([#5794](https://github.com/leanprover-community/mathlib/pull/5794))
This generalisation will make it easier to relate properties of the derived
series of a Lie algebra and the derived series of its ideals (regarded as Lie
algebras in their own right).
The key definition is `lie_algebra.derived_series_of_ideal` and the key result is `lie_ideal.derived_series_eq_bot_iff`.
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* map_zero
- \+ *lemma* zero_mem
- \+ *lemma* smul_mem
- \+ *lemma* add_mem
- \+ *lemma* lie_mem
- \+/\- *lemma* mem_coe
- \+/\- *lemma* mem_coe'
- \+/\- *lemma* coe_bracket
- \+ *lemma* mk_coe
- \+ *lemma* coe_injective
- \+ *lemma* to_submodule_injective
- \+ *lemma* coe_to_submodule_eq
- \+ *lemma* derived_series_of_ideal_zero
- \+ *lemma* derived_series_of_ideal_succ
- \+ *lemma* derived_series_def
- \+ *lemma* derived_series_of_ideal_succ_le
- \+ *lemma* derived_series_of_ideal_le
- \+/\- *lemma* map_mono
- \+/\- *lemma* comap_mono
- \+/\- *lemma* ker_coe_submodule
- \+/\- *lemma* mem_ker
- \+ *lemma* le_ker_iff
- \+ *lemma* map_bot_iff
- \+ *lemma* derived_series_eq_derived_series_of_ideal_comap
- \+ *lemma* derived_series_eq_derived_series_of_ideal_map
- \+ *lemma* derived_series_eq_bot_iff
- \- *lemma* coe_to_set_mk
- \- *lemma* coe_to_submodule_eq_iff
- \+ *theorem* coe_set_eq
- \- *theorem* coe_set_eq_iff
- \+ *def* derived_series_of_ideal
- \- *def* derived_series

Modified src/algebra/lie/classical.lean


Modified src/algebra/lie/skew_adjoint.lean




## [2021-01-19 13:11:44](https://github.com/leanprover-community/mathlib/commit/18841a9)
feat(data/list/basic): nth and nth_le for pmap ([#5451](https://github.com/leanprover-community/mathlib/pull/5451))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* nth_pmap
- \+ *lemma* nth_le_pmap



## [2021-01-19 13:11:42](https://github.com/leanprover-community/mathlib/commit/9777d1e)
feat(data/option/basic): map_bind and join_pmap lemmas ([#5445](https://github.com/leanprover-community/mathlib/pull/5445))
#### Estimated changes
Modified src/data/option/basic.lean
- \+/\- *lemma* bind_map_comm
- \+/\- *lemma* join_map_eq_map_join
- \+/\- *lemma* join_join
- \+/\- *lemma* mem_of_mem_join
- \+ *lemma* map_bind'
- \+ *lemma* join_pmap_eq_pmap_join



## [2021-01-19 11:40:25](https://github.com/leanprover-community/mathlib/commit/c37c64f)
chore(data/matrix/notation): Add some missing simp lemmas for sub, head, and tail ([#5807](https://github.com/leanprover-community/mathlib/pull/5807))
#### Estimated changes
Modified src/data/matrix/notation.lean
- \+ *lemma* head_add
- \+ *lemma* tail_add
- \+ *lemma* empty_sub_empty
- \+ *lemma* cons_sub
- \+ *lemma* sub_cons
- \+ *lemma* head_sub
- \+ *lemma* tail_sub
- \+ *lemma* head_neg
- \+ *lemma* tail_neg

Modified test/matrix.lean




## [2021-01-19 03:39:22](https://github.com/leanprover-community/mathlib/commit/190dd10)
chore(analysis/normed_space): golf some proofs ([#5804](https://github.com/leanprover-community/mathlib/pull/5804))
* add `pi_norm_lt_iff`;
* add `has_sum.norm_le_of_bounded`;
* add `multilinear_map.bound_of_shell`;
* rename `continuous_multilinear_map.norm_image_sub_le_of_bound` to
  `continuous_multilinear_map.norm_image_sub_le`, same with prime
  version;
* golf some proofs.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* pi_norm_lt_iff
- \+ *lemma* has_sum.norm_le_of_bounded
- \+/\- *lemma* norm_tsum_le_tsum_norm

Modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* bound_of_shell
- \+ *lemma* norm_image_sub_le'
- \+ *lemma* norm_image_sub_le
- \- *lemma* norm_image_sub_le_of_bound'
- \- *lemma* norm_image_sub_le_of_bound

Modified src/analysis/normed_space/operator_norm.lean




## [2021-01-19 02:19:31](https://github.com/leanprover-community/mathlib/commit/c9c3b6f)
chore(scripts): update nolints.txt ([#5806](https://github.com/leanprover-community/mathlib/pull/5806))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-18 23:02:32](https://github.com/leanprover-community/mathlib/commit/541688b)
feat(combinatorics/simple_graph/basic): add lemmas about cardinality of common neighbor set ([#5789](https://github.com/leanprover-community/mathlib/pull/5789))
Add lemmas about the cardinality of the set of common neighbors between two vertices. Add note in module docstring about naming convention. Part of [#5698](https://github.com/leanprover-community/mathlib/pull/5698) in order to prove facts about strongly regular graphs.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* card_common_neighbors_le_degree_left
- \+ *lemma* card_common_neighbors_le_degree_right
- \+ *lemma* card_common_neighbors_lt_card_verts
- \+ *lemma* adj.card_common_neighbors_lt_degree



## [2021-01-18 23:02:30](https://github.com/leanprover-community/mathlib/commit/77003ce)
refactor(field_theory|ring_theory|linear_algebra): minpoly A x ([#5774](https://github.com/leanprover-community/mathlib/pull/5774))
This PR refactors the definition of `minpoly` to
```
noncomputable def minpoly (x : B) : polynomial A := if hx : is_integral
A x then well_founded.min degree_lt_wf _ hx else 0
```
The benefit is that we can write `minpoly A x` instead of
`minpoly hx` for `hx : is_integral A x`. The resulting code is more
readable, and some lemmas are true without the `hx` assumption.
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+/\- *lemma* aeval_gen_minpoly
- \+/\- *lemma* card_alg_hom_adjoin_integral

Modified src/field_theory/algebraic_closure.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/galois.lean
- \+/\- *lemma* integral
- \+/\- *lemma* separable
- \+/\- *lemma* normal
- \+/\- *lemma* is_galois.tower_top_of_is_galois

Modified src/field_theory/minpoly.lean
- \+/\- *lemma* monic
- \+/\- *lemma* ne_zero
- \+/\- *lemma* aeval
- \+/\- *lemma* degree_pos
- \+/\- *lemma* eq_X_sub_C_of_algebra_map_inj
- \+/\- *lemma* not_is_unit
- \+/\- *lemma* aeval_ne_zero_of_dvd_not_unit_minpoly
- \+/\- *lemma* irreducible
- \+/\- *lemma* unique
- \+/\- *lemma* dvd
- \+/\- *lemma* dvd_map_of_is_scalar_tower
- \+ *lemma* eq_of_algebra_map_eq
- \+/\- *lemma* over_int_eq_over_rat
- \+/\- *lemma* eq_X_sub_C
- \+ *lemma* eq_X_sub_C'
- \+/\- *lemma* zero
- \+/\- *lemma* one
- \+/\- *lemma* prime
- \+/\- *lemma* root
- \+/\- *lemma* coeff_zero_eq_zero
- \+/\- *lemma* coeff_zero_ne_zero
- \+/\- *theorem* unique'

Modified src/field_theory/normal.lean
- \+/\- *lemma* normal.tower_top_of_normal
- \+/\- *theorem* normal.is_integral
- \+/\- *theorem* normal.splits

Modified src/field_theory/primitive_element.lean


Modified src/field_theory/separable.lean
- \+/\- *lemma* is_separable_tower_top_of_is_separable
- \+/\- *lemma* is_separable_tower_bot_of_is_separable
- \+/\- *lemma* is_separable.of_alg_hom

Modified src/field_theory/splitting_field.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/eigenspace.lean
- \+/\- *theorem* is_root_of_has_eigenvalue
- \+/\- *theorem* has_eigenvalue_of_is_root

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_integral_algebra_map_iff

Modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* cyclotomic_eq_minpoly
- \- *lemma* minpoly_primitive_root_eq_cyclotomic

Modified src/ring_theory/power_basis.lean
- \- *lemma* is_integral_algebra_map_iff
- \- *lemma* minpoly.eq_of_algebra_map_eq

Modified src/ring_theory/roots_of_unity.lean
- \+/\- *lemma* minpoly_dvd_X_pow_sub_one
- \+/\- *lemma* totient_le_degree_minpoly



## [2021-01-18 19:33:02](https://github.com/leanprover-community/mathlib/commit/725efb1)
doc(tactic/rewrite): Add an example for assoc_rw ([#5799](https://github.com/leanprover-community/mathlib/pull/5799))
#### Estimated changes
Modified src/tactic/rewrite.lean




## [2021-01-18 17:54:03](https://github.com/leanprover-community/mathlib/commit/b5e832e)
refactor(algebraic_geometry/prime_spectrum): simplify `comap_id`, `comap_comp` ([#5796](https://github.com/leanprover-community/mathlib/pull/5796))
faster proofs and smaller proof terms
Co-authors: `lean-gptf`, Yuhuai Wu
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean




## [2021-01-18 15:57:43](https://github.com/leanprover-community/mathlib/commit/57bc1da)
feat(order/limsup_liminf, order/filter/ennreal): add properties of limsup for ennreal-valued functions ([#5746](https://github.com/leanprover-community/mathlib/pull/5746))
#### Estimated changes
Created src/measure_theory/ess_sup.lean
- \+ *lemma* ess_sup_congr_ae
- \+ *lemma* ess_inf_congr_ae
- \+ *lemma* ess_sup_measure_zero
- \+ *lemma* ess_inf_measure_zero
- \+ *lemma* ess_sup_mono_ae
- \+ *lemma* ess_inf_mono_ae
- \+ *lemma* ess_sup_const
- \+ *lemma* ess_inf_const
- \+ *lemma* ess_sup_const_bot
- \+ *lemma* ess_inf_const_top
- \+ *lemma* order_iso.ess_sup_apply
- \+ *lemma* order_iso.ess_inf_apply
- \+ *lemma* ae_lt_of_ess_sup_lt
- \+ *lemma* ae_lt_of_lt_ess_inf
- \+ *lemma* ennreal.ae_le_ess_sup
- \+ *lemma* ess_sup_eq_zero_iff
- \+ *lemma* ennreal.ess_sup_const_mul
- \+ *lemma* ennreal.ess_sup_add_le
- \+ *def* ess_sup
- \+ *def* ess_inf

Created src/order/filter/ennreal.lean
- \+ *lemma* eventually_le_limsup
- \+ *lemma* limsup_eq_zero_iff
- \+ *lemma* limsup_const_mul_of_ne_top
- \+ *lemma* limsup_const_mul
- \+ *lemma* limsup_add_le

Modified src/order/liminf_limsup.lean
- \+ *lemma* limsup_const_bot
- \+ *lemma* liminf_const_top
- \+ *lemma* le_limsup_of_frequently_le
- \+ *lemma* liminf_le_of_frequently_le
- \+ *lemma* galois_connection.l_limsup_le
- \+ *lemma* order_iso.limsup_apply
- \+ *lemma* order_iso.liminf_apply



## [2021-01-18 10:20:56](https://github.com/leanprover-community/mathlib/commit/66e955e)
feat(algebra/lie/basic): results relating Lie algebra morphisms and ideal operations ([#5778](https://github.com/leanprover-community/mathlib/pull/5778))
The key results are `lie_ideal.comap_bracket_eq` and its corollary `lie_ideal.comap_bracket_incl`
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* mem_coe
- \+ *lemma* mem_coe'
- \+ *lemma* coe_bracket
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* coe_to_set_mk
- \+ *lemma* coe_to_submodule_eq_iff
- \+ *lemma* lie_subalgebra.range_incl
- \+ *lemma* lie_ideal.coe_to_subalgebra
- \+ *lemma* map_coe_submodule
- \+ *lemma* comap_coe_submodule
- \+ *lemma* map_le
- \+ *lemma* mem_map
- \+ *lemma* mem_comap
- \+/\- *lemma* map_le_iff_le_comap
- \+/\- *lemma* gc_map_comap
- \+ *lemma* map_comap_le
- \+ *lemma* comap_map_le
- \+ *lemma* map_mono
- \+ *lemma* comap_mono
- \+ *lemma* map_of_image
- \+ *lemma* is_ideal_morphism_def
- \+ *lemma* range_subset_ideal_range
- \+ *lemma* map_le_ideal_range
- \+ *lemma* ker_le_comap
- \+ *lemma* mem_ker
- \+ *lemma* mem_ideal_range
- \+ *lemma* mem_ideal_range_iff
- \+ *lemma* ker_coe_submodule
- \+ *lemma* map_sup_ker_eq_map
- \+ *lemma* map_comap_eq
- \+ *lemma* comap_map_eq
- \+/\- *lemma* incl_apply
- \+ *lemma* incl_coe
- \+ *lemma* comap_incl_self
- \+ *lemma* ker_incl
- \+ *lemma* incl_ideal_range
- \+ *lemma* incl_is_ideal_morphism
- \+ *lemma* map_bracket_le
- \+ *lemma* comap_bracket_le
- \+ *lemma* map_comap_incl
- \+ *lemma* comap_bracket_eq
- \+ *lemma* map_comap_bracket_eq
- \+ *lemma* comap_bracket_incl
- \+ *lemma* comap_bracket_incl_of_le
- \- *lemma* lie_subalgebra.mem_coe
- \- *lemma* lie_subalgebra.mem_coe'
- \- *lemma* lie_subalgebra.coe_bracket
- \- *lemma* lie_subalgebra.ext
- \- *lemma* lie_subalgebra.ext_iff
- \- *lemma* coe_to_subalgebra
- \+ *theorem* coe_set_eq_iff
- \+/\- *def* map
- \+/\- *def* comap
- \+ *def* ker
- \+ *def* ideal_range
- \+ *def* is_ideal_morphism
- \+/\- *def* incl



## [2021-01-18 08:58:39](https://github.com/leanprover-community/mathlib/commit/9381e37)
doc(data/buffer/parser/basic): fix typo ([#5792](https://github.com/leanprover-community/mathlib/pull/5792))
#### Estimated changes
Modified src/data/buffer/parser/basic.lean




## [2021-01-18 07:03:48](https://github.com/leanprover-community/mathlib/commit/8ab1a39)
chore(field_theory/minpoly): meaningful variable names ([#5773](https://github.com/leanprover-community/mathlib/pull/5773))
#### Estimated changes
Modified src/field_theory/minpoly.lean
- \+/\- *lemma* min
- \+/\- *lemma* ne_zero
- \+/\- *lemma* degree_pos
- \+/\- *lemma* eq_X_sub_C_of_algebra_map_inj
- \+/\- *lemma* aeval_ne_zero_of_dvd_not_unit_minpoly
- \+/\- *lemma* unique
- \+/\- *lemma* dvd
- \+/\- *lemma* dvd_map_of_is_scalar_tower
- \+/\- *lemma* gcd_domain_eq_field_fractions
- \+/\- *lemma* over_int_eq_over_rat
- \+/\- *lemma* gcd_domain_dvd
- \+/\- *lemma* integer_dvd
- \+/\- *lemma* eq_X_sub_C
- \+/\- *lemma* zero
- \+/\- *lemma* one
- \+/\- *lemma* root
- \+/\- *theorem* unique'



## [2021-01-18 07:03:45](https://github.com/leanprover-community/mathlib/commit/db617b3)
feat(ring_theory/ideal/operations): add algebra structure on quotient ([#5703](https://github.com/leanprover-community/mathlib/pull/5703))
I added very basic stuff about `R/I` as an `R`-algebra that are missing in mathlib.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* quotient.mkₐ_to_ring_hom
- \+ *lemma* quotient.mkₐ_eq_mk
- \+ *lemma* quotient.mkₐ_surjective
- \+ *lemma* quotient.mkₐ_ker
- \+ *def* quotient.mkₐ



## [2021-01-18 05:44:26](https://github.com/leanprover-community/mathlib/commit/f3d3d04)
chore(category_theory/monad): golf and lint monadic adjunctions ([#5769](https://github.com/leanprover-community/mathlib/pull/5769))
Some lintfixes and proof golfing using newer API
#### Estimated changes
Modified src/category_theory/monad/adjunction.lean
- \+/\- *lemma* comparison_ess_surj_aux
- \- *lemma* monad_η_app
- \- *lemma* monad_μ_app
- \- *lemma* comparison_map_f
- \- *lemma* comparison_obj_a
- \+/\- *def* comparison
- \+/\- *def* comparison_forget



## [2021-01-18 03:26:01](https://github.com/leanprover-community/mathlib/commit/3089b16)
chore(scripts): update nolints.txt ([#5790](https://github.com/leanprover-community/mathlib/pull/5790))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-18 00:03:46](https://github.com/leanprover-community/mathlib/commit/2f824aa)
feat(data/option/*): pmap and pbind defs and lemmas ([#5442](https://github.com/leanprover-community/mathlib/pull/5442))
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* mem_map_of_mem
- \+ *lemma* pbind_eq_bind
- \+ *lemma* map_bind
- \+ *lemma* map_pbind
- \+ *lemma* pbind_map
- \+ *lemma* pmap_none
- \+ *lemma* pmap_some
- \+ *lemma* mem_pmem
- \+ *lemma* pmap_map
- \+ *lemma* map_pmap
- \+ *lemma* pmap_eq_map
- \+ *lemma* pmap_bind
- \+ *lemma* bind_pmap
- \+ *lemma* pbind_eq_none
- \+ *lemma* pbind_eq_some
- \+ *lemma* pmap_eq_none_iff
- \+ *lemma* pmap_eq_some_iff

Modified src/data/option/defs.lean
- \+ *def* pbind
- \+ *def* pmap



## [2021-01-17 21:46:49](https://github.com/leanprover-community/mathlib/commit/c3639e9)
refactor(algebra/monoid_algebra) generalize from group to monoid algebras ([#5785](https://github.com/leanprover-community/mathlib/pull/5785))
There was a TODO in the monoid algebra file to generalize three statements from group to monoid algebras. It seemed to be solvable by just changing the assumptions, not the proofs.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean
- \+/\- *lemma* group_smul.linear_map_apply
- \+/\- *def* group_smul.linear_map



## [2021-01-17 14:43:58](https://github.com/leanprover-community/mathlib/commit/f29d1c3)
refactor(analysis/calculus/deriv): simpler proof of `differentiable_at.div_const` ([#5782](https://github.com/leanprover-community/mathlib/pull/5782))
Co-authors: `lean-gptf`, Yuhuai Wu
#### Estimated changes
Modified src/analysis/calculus/deriv.lean




## [2021-01-17 14:43:56](https://github.com/leanprover-community/mathlib/commit/83d44a3)
hack(manifold): disable subsingleton instances to speed up simp ([#5779](https://github.com/leanprover-community/mathlib/pull/5779))
Simp takes an enormous amount of time in manifold code looking for subsingleton instances (and in fact probably in the whole library, but manifolds are particularly simp-heavy). We disable two such instances in the `manifold` locale, to get serious speedups (for instance, `times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within` goes down from 27s to 10s on my computer).
This is *not* a proper fix. But it already makes a serious difference in this part of the library..
Zulip discussion at https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.235672.20breaks.20timeout/near/223001979
#### Estimated changes
Modified src/geometry/manifold/charted_space.lean


Modified src/geometry/manifold/times_cont_mdiff_map.lean




## [2021-01-17 11:37:27](https://github.com/leanprover-community/mathlib/commit/bf46986)
doc(tactic/auto_cases): fix typo ([#5784](https://github.com/leanprover-community/mathlib/pull/5784))
#### Estimated changes
Modified src/tactic/auto_cases.lean




## [2021-01-17 08:33:51](https://github.com/leanprover-community/mathlib/commit/289df3a)
feat(data/set/lattice): add lemmas set.Union_subtype and set.Union_of_singleton_coe ([#5691](https://github.com/leanprover-community/mathlib/pull/5691))
Add one simp lemma, following a suggestion on the Zulip chat:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/image_bUnion
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* Union_subtype
- \+ *lemma* Union_of_singleton_coe



## [2021-01-17 03:47:19](https://github.com/leanprover-community/mathlib/commit/2c4a516)
chore(topology/metric_space/isometry): a few more lemmas ([#5780](https://github.com/leanprover-community/mathlib/pull/5780))
Also reuse more proofs about `inducing` and `quotient_map` in
`topology/homeomorph`.
Non-bc change: rename `isometric.range_coe` to
`isometric.range_eq_univ` to match `equiv.range_eq_univ`.
#### Estimated changes
Modified src/topology/homeomorph.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/isometry.lean
- \+ *lemma* ediam_image
- \+ *lemma* range_eq_univ
- \+ *lemma* ediam_univ
- \+ *lemma* ediam_preimage
- \+ *lemma* comp_continuous_on_iff
- \+ *lemma* comp_continuous_iff
- \+ *lemma* comp_continuous_iff'
- \+ *lemma* diam_image
- \+ *lemma* diam_preimage
- \+ *lemma* diam_univ
- \- *lemma* range_coe



## [2021-01-17 02:21:15](https://github.com/leanprover-community/mathlib/commit/00e1f4c)
chore(scripts): update nolints.txt ([#5781](https://github.com/leanprover-community/mathlib/pull/5781))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-17 00:33:57](https://github.com/leanprover-community/mathlib/commit/dec44fe)
chore(group_theory/perm/{sign,cycles}): renaming for dot notation, linting, formatting ([#5777](https://github.com/leanprover-community/mathlib/pull/5777))
Declarations renamed in `group_theory/perm/sign.lean` (all of these are under `equiv.perm`):
- `disjoint_mul_comm` -> `disjoint.mul_comm`
- `disjoint_mul_left` -> `disjoint.mul_left`
- `disjoint_mul_right` -> `disjoint.mul_right`
- `is_swap_of_subtype` -> `is_swap.of_subtype_is_swap`
- `sign_eq_of_is_swap` -> `is_swap.sign_eq`
Declarations renamed in `group_theory/perm/cycles.lean` (all of these are under `equiv.perm`):
- `is_cycle_swap` -> `is_cycle.swap`
- `is_cycle_inv` -> `is_cycle.inv`
- `exists_gpow_eq_of_is_cycle` -> `is_cycle.exists_gpow_eq`
- `exists_pow_eq_of_is_cycle` -> `is_cycle.exists_pow_eq`
- `eq_swap_of_is_cycle_of_apply_apply_eq_self` -> `eq_swap_of_apply_apply_eq_self`
- `is_cycle_swap_mul` -> `is_cycle.swap_mul`
- `sign_cycle` -> `is_cycle.sign`
- `apply_eq_self_iff_of_same_cycle` -> `same_cycle.apply_eq_self_iff`
- `same_cycle_of_is_cycle` -> `is_cycle.same_cycle`
- `cycle_of_apply_of_same_cycle` -> `same_cycle.cycle_of_apply`
- `cycle_of_cycle` -> `is_cycle.cycle_of_eq`
I also added a basic module doc string to `group_theory/perm/cycles.lean`.
#### Estimated changes
Modified src/group_theory/perm/cycles.lean
- \+ *lemma* is_cycle.swap
- \+ *lemma* is_cycle.inv
- \+ *lemma* is_cycle.exists_gpow_eq
- \+ *lemma* is_cycle.exists_pow_eq
- \+/\- *lemma* is_cycle_swap_mul_aux₂
- \+ *lemma* is_cycle.eq_swap_of_apply_apply_eq_self
- \+ *lemma* is_cycle.swap_mul
- \+ *lemma* is_cycle.sign
- \+ *lemma* same_cycle.apply_eq_self_iff
- \+ *lemma* is_cycle.same_cycle
- \+ *lemma* same_cycle.cycle_of_apply
- \+ *lemma* is_cycle.cycle_of_eq
- \- *lemma* is_cycle_swap
- \- *lemma* is_cycle_inv
- \- *lemma* exists_gpow_eq_of_is_cycle
- \- *lemma* exists_pow_eq_of_is_cycle
- \- *lemma* eq_swap_of_is_cycle_of_apply_apply_eq_self
- \- *lemma* is_cycle_swap_mul
- \- *lemma* sign_cycle
- \- *lemma* apply_eq_self_iff_of_same_cycle
- \- *lemma* same_cycle_of_is_cycle
- \- *lemma* cycle_of_apply_of_same_cycle
- \- *lemma* cycle_of_cycle
- \+/\- *def* is_cycle
- \+/\- *def* same_cycle

Modified src/group_theory/perm/sign.lean
- \+/\- *lemma* subtype_perm_one
- \+ *lemma* disjoint.mul_comm
- \+ *lemma* disjoint.mul_left
- \+ *lemma* disjoint.mul_right
- \+/\- *lemma* of_subtype_subtype_perm
- \+/\- *lemma* of_subtype_apply_of_not_mem
- \+/\- *lemma* mem_iff_of_subtype_apply_mem
- \+ *lemma* is_swap.of_subtype_is_swap
- \+/\- *lemma* sign_bij_aux_mem
- \+ *lemma* is_swap.sign_eq
- \- *lemma* disjoint_mul_comm
- \- *lemma* disjoint_mul_left
- \- *lemma* disjoint_mul_right
- \- *lemma* is_swap_of_subtype
- \- *lemma* sign_eq_of_is_swap
- \+/\- *def* support
- \+/\- *def* is_swap



## [2021-01-17 00:33:55](https://github.com/leanprover-community/mathlib/commit/a2630fc)
chore(field_theory|ring_theory|linear_algebra): rename minimal_polynomial to minpoly ([#5771](https://github.com/leanprover-community/mathlib/pull/5771))
This PR renames:
* `minimal_polynomial` -> `minpoly`
* a similar substitution throughout the library for all names containing the substring `minimal_polynomial`
* `fixed_points.minpoly.minimal_polynomial` -> `fixed_points.minpoly_eq_minpoly`
This PR moves a file:
  src/field_theory/minimal_polynomial.lean -> src/field_theory/minpoly.lean
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified scripts/style-exceptions.txt


Modified src/field_theory/adjoin.lean
- \+ *lemma* aeval_gen_minpoly
- \+/\- *lemma* card_alg_hom_adjoin_integral
- \- *lemma* aeval_gen_minimal_polynomial

Modified src/field_theory/algebraic_closure.lean


Modified src/field_theory/fixed.lean
- \+ *theorem* minpoly_eq_minpoly
- \- *theorem* minpoly.minimal_polynomial

Modified src/field_theory/galois.lean


Renamed src/field_theory/minimal_polynomial.lean to src/field_theory/minpoly.lean
- \+/\- *lemma* monic
- \+/\- *lemma* aeval
- \+/\- *lemma* ne_zero
- \+/\- *lemma* degree_pos
- \+/\- *lemma* eq_X_sub_C_of_algebra_map_inj
- \+/\- *lemma* not_is_unit
- \+ *lemma* aeval_ne_zero_of_dvd_not_unit_minpoly
- \+/\- *lemma* irreducible
- \+/\- *lemma* prime
- \+/\- *lemma* coeff_zero_eq_zero
- \+/\- *lemma* coeff_zero_ne_zero
- \- *lemma* aeval_ne_zero_of_dvd_not_unit_minimal_polynomial

Modified src/field_theory/normal.lean


Modified src/field_theory/primitive_element.lean


Modified src/field_theory/separable.lean


Modified src/field_theory/splitting_field.lean
- \+ *def* alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly
- \- *def* alg_equiv.adjoin_singleton_equiv_adjoin_root_minimal_polynomial

Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/eigenspace.lean
- \+/\- *theorem* has_eigenvalue_of_is_root

Modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* minpoly_primitive_root_dvd_cyclotomic
- \+ *lemma* minpoly_primitive_root_eq_cyclotomic
- \- *lemma* minimal_polynomial_primitive_root_dvd_cyclotomic
- \- *lemma* minimal_polynomial_primitive_root_eq_cyclotomic

Modified src/ring_theory/power_basis.lean
- \+ *lemma* nat_degree_minpoly
- \+ *lemma* minpoly.eq_of_algebra_map_eq
- \- *lemma* nat_degree_minimal_polynomial
- \- *lemma* minimal_polynomial.eq_of_algebra_map_eq

Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* minpoly_dvd_X_pow_sub_one
- \+ *lemma* separable_minpoly_mod
- \+ *lemma* squarefree_minpoly_mod
- \+ *lemma* minpoly_dvd_expand
- \+ *lemma* minpoly_dvd_pow_mod
- \+ *lemma* minpoly_dvd_mod_p
- \+ *lemma* minpoly_eq_pow
- \+ *lemma* minpoly_eq_pow_coprime
- \+ *lemma* pow_is_root_minpoly
- \+ *lemma* is_roots_of_minpoly
- \+ *lemma* totient_le_degree_minpoly
- \- *lemma* minimal_polynomial_dvd_X_pow_sub_one
- \- *lemma* separable_minimal_polynomial_mod
- \- *lemma* squarefree_minimal_polynomial_mod
- \- *lemma* minimal_polynomial_dvd_expand
- \- *lemma* minimal_polynomial_dvd_pow_mod
- \- *lemma* minimal_polynomial_dvd_mod_p
- \- *lemma* minimal_polynomial_eq_pow
- \- *lemma* minimal_polynomial_eq_pow_coprime
- \- *lemma* pow_is_root_minimal_polynomial
- \- *lemma* is_roots_of_minimal_polynomial
- \- *lemma* totient_le_degree_minimal_polynomial



## [2021-01-16 23:11:28](https://github.com/leanprover-community/mathlib/commit/0cc93a1)
feat(category_theory/is_filtered): is_filtered_of_equiv ([#5485](https://github.com/leanprover-community/mathlib/pull/5485))
If `C` is filtered and there is a right adjoint functor `C => D`, then `D` is filtered. Also a category equivalent to a filtered category is filtered.
#### Estimated changes
Modified src/category_theory/filtered.lean
- \+ *lemma* of_right_adjoint
- \+ *lemma* of_is_right_adjoint
- \+ *lemma* of_equivalence



## [2021-01-16 21:37:58](https://github.com/leanprover-community/mathlib/commit/787e6b3)
feat(measure_theory/haar_measure): Prove uniqueness ([#5663](https://github.com/leanprover-community/mathlib/pull/5663))
Prove the uniqueness of Haar measure (up to a scalar) following  *Measure Theory* by Paul Halmos. This proof seems to contain an omission which we fix by adding an extra hypothesis to an intermediate lemma.
Add some lemmas about left invariant regular measures.
We add the file `measure_theory.prod_group` which contain various measure-theoretic properties of products of topological groups, needed for the uniqueness.
We add `@[to_additive]` to some declarations in `measure_theory`, but leave it out for many because of [#4210](https://github.com/leanprover-community/mathlib/pull/4210). This causes some renamings in concepts, like `is_left_invariant` -> `is_mul_left_invariant` and `measure.conj` -> `measure.inv` (though a better naming suggestion for this one is welcome).
#### Estimated changes
Modified docs/references.bib


Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* outer_regular_eq
- \+/\- *lemma* inner_regular_eq
- \+ *lemma* exists_compact_not_null

Modified src/measure_theory/content.lean
- \+ *lemma* is_mul_left_invariant_inner_content
- \+ *lemma* inner_content_pos_of_is_mul_left_invariant
- \+ *lemma* is_mul_left_invariant_of_content
- \+ *lemma* of_content_pos_of_is_mul_left_invariant
- \- *lemma* is_left_invariant_inner_content
- \- *lemma* inner_content_pos
- \- *lemma* is_left_invariant_of_content
- \- *lemma* of_content_pos_of_is_open

Modified src/measure_theory/group.lean
- \+ *lemma* inv_apply
- \+ *lemma* regular.inv
- \+ *lemma* regular_inv_iff
- \+ *lemma* is_mul_left_invariant.inv
- \+ *lemma* is_mul_right_invariant.inv
- \+ *lemma* is_mul_right_invariant_inv
- \+ *lemma* is_mul_left_invariant_inv
- \+ *lemma* is_mul_left_invariant.null_iff_empty
- \+ *lemma* is_mul_left_invariant.null_iff
- \+ *lemma* is_mul_left_invariant.measure_ne_zero_iff_nonempty
- \+ *lemma* lintegral_eq_zero_of_is_mul_left_invariant
- \- *lemma* conj_apply
- \- *lemma* conj_conj
- \- *lemma* regular.conj
- \- *lemma* regular_conj_iff
- \- *lemma* is_right_invariant_conj'
- \- *lemma* is_left_invariant_conj'
- \- *lemma* is_right_invariant_conj
- \- *lemma* is_left_invariant_conj
- \+ *def* is_mul_left_invariant
- \+ *def* is_mul_right_invariant
- \- *def* is_left_invariant
- \- *def* is_right_invariant

Modified src/measure_theory/haar_measure.lean
- \+ *lemma* is_mul_left_invariant_haar_measure
- \- *lemma* is_left_invariant_haar_measure
- \+ *theorem* haar_measure_unique
- \+ *theorem* regular_of_left_invariant

Modified src/measure_theory/measure_space.lean
- \+ *lemma* map_symm_map
- \+ *lemma* map_map_symm
- \+ *lemma* map_measurable_equiv_injective
- \+ *lemma* map_apply_eq_iff_map_symm_apply_eq

Created src/measure_theory/prod_group.lean
- \+ *lemma* map_prod_mul_eq
- \+ *lemma* map_prod_mul_eq_swap
- \+ *lemma* map_prod_inv_mul_eq
- \+ *lemma* map_prod_inv_mul_eq_swap
- \+ *lemma* map_prod_mul_inv_eq
- \+ *lemma* measure_null_of_measure_inv_null
- \+ *lemma* measure_inv_null
- \+ *lemma* measurable_measure_mul_right
- \+ *lemma* lintegral_lintegral_mul_inv
- \+ *lemma* measure_mul_right_null
- \+ *lemma* measure_mul_right_ne_zero
- \+ *lemma* measure_lintegral_div_measure
- \+ *lemma* measure_mul_measure_eq



## [2021-01-16 19:32:30](https://github.com/leanprover-community/mathlib/commit/23373d1)
chore(category_theory/limits): coproduct functor ([#5677](https://github.com/leanprover-community/mathlib/pull/5677))
Dualises a def already there.
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *def* coprod.functor
- \+ *def* coprod.functor_left_comp



## [2021-01-16 17:42:15](https://github.com/leanprover-community/mathlib/commit/e0f4142)
refactor(data/nat/fib): explicitly state fibonacci sequence is monotone ([#5776](https://github.com/leanprover-community/mathlib/pull/5776))
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/fib_mono
#### Estimated changes
Modified src/data/nat/fib.lean
- \+/\- *lemma* fib_mono



## [2021-01-16 17:42:12](https://github.com/leanprover-community/mathlib/commit/4155665)
refactor(linear_algebra/dual): replace dim<omega by finite_dimensional ([#5775](https://github.com/leanprover-community/mathlib/pull/5775))
#### Estimated changes
Modified src/linear_algebra/dual.lean
- \+/\- *lemma* erange_coe
- \+/\- *theorem* dual_dim_eq
- \+/\- *def* eval_equiv



## [2021-01-16 17:42:09](https://github.com/leanprover-community/mathlib/commit/d23dbfb)
feat(category_theory/adjunction): reflective functors ([#5680](https://github.com/leanprover-community/mathlib/pull/5680))
Extract reflective functors from monads, and show some properties of them
#### Estimated changes
Modified src/category_theory/adjunction/default.lean


Created src/category_theory/adjunction/reflective.lean
- \+ *lemma* mem_ess_image_of_unit_is_iso
- \+ *lemma* mem_ess_image_of_unit_split_mono
- \+ *def* functor.ess_image.unit_is_iso

Modified src/category_theory/monad/adjunction.lean




## [2021-01-16 17:42:07](https://github.com/leanprover-community/mathlib/commit/64abe5a)
feat(category_theory/sites): closed sieves ([#5282](https://github.com/leanprover-community/mathlib/pull/5282))
- closed sieves
- closure of a sieve
- subobject classifier in Sheaf (without proof of universal property)
- equivalent sheaf condition iff same topology
- closure operator induces topology
#### Estimated changes
Created src/category_theory/sites/closed.lean
- \+ *lemma* le_close
- \+ *lemma* covers_iff_mem_of_closed
- \+ *lemma* is_closed_pullback
- \+ *lemma* le_close_of_is_closed
- \+ *lemma* close_is_closed
- \+ *lemma* is_closed_iff_close_eq_self
- \+ *lemma* close_eq_self_of_is_closed
- \+ *lemma* pullback_close
- \+ *lemma* monotone_close
- \+ *lemma* close_close
- \+ *lemma* close_eq_top_iff_mem
- \+ *lemma* closed_iff_closed
- \+ *lemma* classifier_is_sheaf
- \+ *lemma* le_topology_of_closed_sieves_is_sheaf
- \+ *lemma* topology_eq_iff_same_sheaves
- \+ *lemma* topology_of_closure_operator_self
- \+ *lemma* topology_of_closure_operator_close
- \+ *def* close
- \+ *def* is_closed
- \+ *def* closure_operator
- \+ *def* functor.closed_sieves
- \+ *def* topology_of_closure_operator

Modified src/order/closure.lean
- \+ *def* mk'



## [2021-01-16 15:21:08](https://github.com/leanprover-community/mathlib/commit/e076a9c)
chore(topology/metric_space/gluing): use `⨅` notation ([#5772](https://github.com/leanprover-community/mathlib/pull/5772))
Also use `exists_lt_of_cinfi_lt` to golf one proof.
#### Estimated changes
Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff.lean




## [2021-01-16 15:21:06](https://github.com/leanprover-community/mathlib/commit/ba5d1f6)
feat(linear_algebra/basic): add comap span lemmas ([#5744](https://github.com/leanprover-community/mathlib/pull/5744))
We already had `map_span` but nothing for `comap`.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* span_preimage_le
- \+ *lemma* ker_le_iff
- \+/\- *lemma* range_prod_eq
- \+ *lemma* span_preimage_eq
- \+/\- *theorem* sub_mem_ker_iff
- \+/\- *theorem* disjoint_ker'
- \+/\- *theorem* inj_of_disjoint_ker
- \+/\- *theorem* ker_eq_bot



## [2021-01-16 15:21:04](https://github.com/leanprover-community/mathlib/commit/bd57804)
feat(algebraic_geometry/prime_spectrum): add lemma zero_locus_bUnion ([#5692](https://github.com/leanprover-community/mathlib/pull/5692))
Add a simple extension of a lemma, to be able to work with `bUnion`, instead of only `Union`.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean
- \+ *lemma* zero_locus_bUnion



## [2021-01-16 11:02:21](https://github.com/leanprover-community/mathlib/commit/55d5564)
feat(ring_theory/jacobson): Generalize proofs about Jacobson rings and polynomials ([#5520](https://github.com/leanprover-community/mathlib/pull/5520))
These changes are meant to make deriving the classical nullstellensatz from the generalized version about Jacobson rings much easier and much more direct.
`is_integral_localization_map_polynomial_quotient` already exists in the proof of a previous theorem, and this just pulls it out into an independent lemma.
`polynomial.quotient_mk_comp_C_is_integral_of_jacobson` and `mv_polynomial.quotient_mk_comp_C_is_integral_of_jacobson` are the two main new statements, most of the rest of the changes are just generalizations and reorganizations of the existing theorems.
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* C_surjective
- \+ *lemma* C_surjective_fin_0

Modified src/data/mv_polynomial/equiv.lean
- \+ *lemma* fin_succ_equiv_comp_C_eq_C

Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* exists_mem_ne_zero_iff_ne_bot
- \+ *lemma* exists_mem_ne_zero_of_ne_bot
- \+ *lemma* lift_comp_mk
- \+ *lemma* lift_surjective

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* quotient_map_injective'
- \+/\- *lemma* quotient_map_injective

Modified src/ring_theory/jacobson.lean
- \+ *lemma* is_integral_localization_map_polynomial_quotient
- \+ *lemma* quotient_mk_comp_C_is_integral_of_jacobson
- \+ *lemma* comp_C_integral_of_surjective_of_jacobson
- \+ *lemma* is_maximal_comap_C_of_is_jacobson
- \+/\- *theorem* is_jacobson_polynomial_iff_is_jacobson

Modified src/ring_theory/polynomial/basic.lean




## [2021-01-16 11:02:18](https://github.com/leanprover-community/mathlib/commit/05e7be9)
feat(algebra/category/Module): direct limit is a colimit ([#4756](https://github.com/leanprover-community/mathlib/pull/4756))
#### Estimated changes
Modified src/algebra/category/Module/limits.lean
- \+ *def* direct_limit_diagram
- \+ *def* direct_limit_cocone
- \+ *def* direct_limit_is_colimit



## [2021-01-16 09:11:40](https://github.com/leanprover-community/mathlib/commit/f03f5a9)
feat(ring_theory/algebra_tower): Restriction of adjoin ([#5767](https://github.com/leanprover-community/mathlib/pull/5767))
Two technical lemmas about restricting `algebra.adjoin` within an `is_scalar_tower`.
#### Estimated changes
Modified src/ring_theory/algebra_tower.lean
- \+ *lemma* adjoin_res
- \+ *lemma* adjoin_res_eq_adjoin_res



## [2021-01-16 09:11:38](https://github.com/leanprover-community/mathlib/commit/e95988a)
feat(field_theory/adjoin): Inductively construct algebra homomorphism ([#5765](https://github.com/leanprover-community/mathlib/pull/5765))
The lemma `alg_hom_mk_adjoin_splits` can be viewed as lifting an embedding F -> K to an embedding F(S) -> K.
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* alg_hom_mk_adjoin_splits
- \+ *lemma* alg_hom_mk_adjoin_splits'



## [2021-01-16 09:11:36](https://github.com/leanprover-community/mathlib/commit/9acd349)
feat(order/closure): closure operator from galois connection ([#5764](https://github.com/leanprover-community/mathlib/pull/5764))
Construct a closure operator from a galois connection
#### Estimated changes
Modified src/order/closure.lean
- \+ *lemma* closure_operator_gi_self
- \+ *def* galois_connection.closure_operator



## [2021-01-16 09:11:34](https://github.com/leanprover-community/mathlib/commit/51ffdd0)
refactor(ring_theory): change field instance on adjoin_root ([#5759](https://github.com/leanprover-community/mathlib/pull/5759))
This makes some things faster.
[Discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Slow.20instance/near/222839607)
#### Estimated changes
Modified src/ring_theory/adjoin_root.lean




## [2021-01-16 09:11:32](https://github.com/leanprover-community/mathlib/commit/dffb09a)
feat(linear_algebra/{clifford,exterior,tensor,free}_algebra): provide canonical images from larger algebras into smaller ones ([#5745](https://github.com/leanprover-community/mathlib/pull/5745))
This adds:
* `free_algebra.to_tensor`
* `tensor_algebra.to_exterior`
* `tensor_algebra.to_clifford`
Providing the injection in the other direction is more challenging, so is left as future work.
#### Estimated changes
Modified src/linear_algebra/clifford_algebra.lean
- \+ *lemma* to_clifford_ι
- \+ *def* to_clifford

Modified src/linear_algebra/exterior_algebra.lean
- \+ *lemma* to_exterior_ι
- \+ *def* to_exterior

Modified src/linear_algebra/tensor_algebra.lean
- \+ *lemma* to_tensor_ι
- \+ *def* to_tensor



## [2021-01-16 09:11:30](https://github.com/leanprover-community/mathlib/commit/bea7651)
feat(category_theory/monad): construct isomorphisms of algebras ([#5678](https://github.com/leanprover-community/mathlib/pull/5678))
#### Estimated changes
Modified src/category_theory/monad/algebra.lean
- \+ *def* iso_mk
- \+/\- *def* algebra_iso_of_iso
- \+ *def* coalgebra_iso_of_iso



## [2021-01-16 03:57:08](https://github.com/leanprover-community/mathlib/commit/592edb6)
chore(scripts): update nolints.txt ([#5763](https://github.com/leanprover-community/mathlib/pull/5763))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-01-16 03:57:02](https://github.com/leanprover-community/mathlib/commit/6351f01)
chore(algebra/group_with_zero): cleanup ([#5762](https://github.com/leanprover-community/mathlib/pull/5762))
* remove `classical,` from proofs: we have `open_locale classical` anyway;
* add a lemma `a / (a * a) = a⁻¹`, use it to golf some proofs in other files.
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* div_self_mul_self'

Modified src/analysis/special_functions/pow.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/data/zsqrtd/gaussian_int.lean




## [2021-01-16 03:57:00](https://github.com/leanprover-community/mathlib/commit/798024a)
chore(data/real/*): rename `le_of_forall_epsilon_le` to `le_of_forall_pos_le_add` ([#5761](https://github.com/leanprover-community/mathlib/pull/5761))
* generalize the `real` version to a `linear_ordered_add_comm_group`;
* rename `nnreal` and `ennreal` versions.
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* le_of_forall_pos_le_add

Modified src/analysis/calculus/fderiv.lean


Modified src/data/real/basic.lean
- \- *lemma* le_of_forall_epsilon_le

Modified src/data/real/ennreal.lean
- \+ *lemma* le_of_forall_pos_le_add
- \- *lemma* le_of_forall_epsilon_le

Modified src/data/real/nnreal.lean
- \+ *lemma* le_of_forall_pos_le_add
- \- *lemma* le_of_forall_epsilon_le

Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/outer_measure.lean


Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/isometry.lean




## [2021-01-16 00:47:54](https://github.com/leanprover-community/mathlib/commit/78493c9)
feat(data/nat/modeq): add missing lemmas for int and nat regarding dvd ([#5752](https://github.com/leanprover-community/mathlib/pull/5752))
Adding lemmas `(a+b)/c=a/c+b/c` if `c` divides `a` for `a b c : nat` and `a b c : int` after discussion on Zulip https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/nat_add_div
#### Estimated changes
Modified src/data/int/basic.lean
- \- *lemma* add_div_of_dvd

Modified src/data/nat/modeq.lean


Modified src/tactic/omega/coeffs.lean


Modified src/tactic/omega/term.lean




## [2021-01-16 00:47:52](https://github.com/leanprover-community/mathlib/commit/e4da493)
feat(group_theory/perm/sign): exists_pow_eq_of_is_cycle ([#5665](https://github.com/leanprover-community/mathlib/pull/5665))
Slight generalization of `exists_gpow_eq_of_is_cycle` in the case of a cycle on a finite set.
Also move the following from `group_theory/perm/sign.lean` to `group_theory/perm/cycles.lean`:
- is_cycle
- is_cycle_swap
- is_cycle_inv
- exists_gpow_eq_of_is_cycle
- is_cycle_swap_mul_aux₁
- is_cycle_swap_mul_aux₂
- eq_swap_of_is_cycle_of_apply_apply_eq_self
- is_cycle_swap_mul
- sign_cycle
#### Estimated changes
Modified src/group_theory/perm/cycles.lean
- \+ *lemma* is_cycle_swap
- \+ *lemma* is_cycle_inv
- \+ *lemma* exists_gpow_eq_of_is_cycle
- \+ *lemma* exists_pow_eq_of_is_cycle
- \+ *lemma* is_cycle_swap_mul_aux₁
- \+ *lemma* is_cycle_swap_mul_aux₂
- \+ *lemma* eq_swap_of_is_cycle_of_apply_apply_eq_self
- \+ *lemma* is_cycle_swap_mul
- \+ *lemma* sign_cycle
- \+ *def* is_cycle

Modified src/group_theory/perm/sign.lean
- \- *lemma* is_cycle_swap
- \- *lemma* is_cycle_inv
- \- *lemma* exists_gpow_eq_of_is_cycle
- \- *lemma* is_cycle_swap_mul_aux₁
- \- *lemma* is_cycle_swap_mul_aux₂
- \- *lemma* eq_swap_of_is_cycle_of_apply_apply_eq_self
- \- *lemma* is_cycle_swap_mul
- \- *lemma* sign_cycle
- \- *def* is_cycle



## [2021-01-15 21:05:36](https://github.com/leanprover-community/mathlib/commit/d43f202)
feat(analysis/analytic/basic): `f (x + y) - p.partial_sum n y = O(∥y∥ⁿ)` ([#5756](https://github.com/leanprover-community/mathlib/pull/5756))
### Lemmas about analytic functions
* add `has_fpower_series_on_ball.uniform_geometric_approx'`, a more
  precise version of `has_fpower_series_on_ball.uniform_geometric_approx`;
* add `has_fpower_series_at.is_O_sub_partial_sum_pow`, a version of
  the Taylor formula for an analytic function;
### Lemmas about `homeomorph` and topological groups
* add `simp` lemmas `homeomorph.coe_mul_left` and
  `homeomorph.mul_left_symm`;
* add `map_mul_left_nhds` and `map_mul_left_nhds_one`;
* add `homeomorph.to_equiv_injective` and `homeomorph.ext`;
### Lemmas about `is_O`/`is_o`
* add `simp` lemmas `asymptotics.is_O_with_map`,
  `asymptotics.is_O_map`, and `asymptotics.is_o_map`;
* add `asymptotics.is_o_norm_pow_norm_pow` and
  `asymptotics.is_o_norm_pow_id`;
### Misc changes
* rename `div_le_iff_of_nonneg_of_le` to `div_le_of_nonneg_of_le_mul`;
* add `continuous_linear_map.op_norm_le_of_nhds_zero`;
* golf some proofs.
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *lemma* div_le_of_nonneg_of_le_mul
- \+ *lemma* div_le_one_of_le
- \- *lemma* div_le_iff_of_nonneg_of_le

Modified src/analysis/analytic/basic.lean
- \+ *lemma* has_fpower_series_on_ball.uniform_geometric_approx'
- \+/\- *lemma* has_fpower_series_on_ball.uniform_geometric_approx
- \+ *lemma* has_fpower_series_at.is_O_sub_partial_sum_pow

Modified src/analysis/asymptotics.lean
- \+ *theorem* is_O_with_map
- \+ *theorem* is_O_map
- \+ *theorem* is_o_map
- \+ *theorem* is_o_norm_pow_norm_pow
- \+ *theorem* is_o_norm_pow_id

Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* op_norm_le_of_nhds_zero

Modified src/topology/algebra/group.lean
- \+ *lemma* homeomorph.coe_mul_left
- \+ *lemma* homeomorph.mul_left_symm
- \+ *lemma* map_mul_left_nhds
- \+ *lemma* map_mul_left_nhds_one

Modified src/topology/homeomorph.lean
- \+ *lemma* to_equiv_injective
- \+ *lemma* ext



## [2021-01-15 21:05:34](https://github.com/leanprover-community/mathlib/commit/bc5d5c9)
feat(data/matrix/notation,data/fin): head and append simp ([#5741](https://github.com/leanprover-community/mathlib/pull/5741))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin_append_apply_zero

Modified src/data/matrix/notation.lean
- \+ *lemma* head_fin_const
- \+ *lemma* vec_head_vec_alt0
- \+ *lemma* vec_head_vec_alt1



## [2021-01-15 21:05:30](https://github.com/leanprover-community/mathlib/commit/0104948)
feat(order/atoms): further facts about atoms, coatoms, and simple lattices ([#5493](https://github.com/leanprover-community/mathlib/pull/5493))
Provides possible instances of `bounded_distrib_lattice`, `boolean_algebra`, `complete_lattice`, and `complete_boolean_algebra` on a simple lattice
Relates the `is_atom` and `is_coatom` conditions to `is_simple_lattice` structures on intervals
Shows that all three conditions are preserved by `order_iso`s
Adds more instances on `bool`, including `is_simple_lattice`
#### Estimated changes
Modified src/data/bool.lean
- \+ *lemma* ff_le
- \+ *lemma* le_tt
- \+ *lemma* ff_lt_tt

Modified src/logic/nontrivial.lean


Modified src/order/atoms.lean
- \+ *lemma* univ
- \+ *lemma* card
- \+ *lemma* is_atom_iff
- \+ *lemma* is_coatom_iff
- \+ *lemma* is_simple_lattice_iff
- \+ *lemma* is_simple_lattice
- \+ *theorem* is_simple_lattice_Iic_iff_is_atom
- \+ *theorem* is_simple_lattice_Ici_iff_is_coatom
- \+ *def* order_iso_bool

Modified src/order/bounded_lattice.lean
- \+ *lemma* top_eq_tt
- \+ *lemma* bot_eq_ff

Modified src/order/lattice.lean




## [2021-01-15 17:48:45](https://github.com/leanprover-community/mathlib/commit/bc94d05)
fix(algebra/ordered_monoid): Ensure that `ordered_cancel_comm_monoid` can provide a `cancel_comm_monoid` instance ([#5713](https://github.com/leanprover-community/mathlib/pull/5713))
#### Estimated changes
Modified src/algebra/group/defs.lean


Modified src/algebra/ordered_monoid.lean




## [2021-01-15 16:03:27](https://github.com/leanprover-community/mathlib/commit/8b4b941)
feat(data/mv_polynomial): stronger `degrees_X` for `nontrivial R` ([#5758](https://github.com/leanprover-community/mathlib/pull/5758))
Also rename `degrees_X` to `degrees_X'` and mark `degrees_{zero,one}` with `simp`.
#### Estimated changes
Modified src/data/mv_polynomial/variables.lean
- \+ *lemma* degrees_X'
- \+/\- *lemma* degrees_X
- \+/\- *lemma* degrees_zero
- \+/\- *lemma* degrees_one

Modified src/field_theory/finite/polynomial.lean




## [2021-01-15 14:40:09](https://github.com/leanprover-community/mathlib/commit/c347c75)
feat(algebra/lie/basic): add a few `simp` lemmas ([#5757](https://github.com/leanprover-community/mathlib/pull/5757))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* morphism.map_smul
- \+ *lemma* morphism.map_add
- \+/\- *lemma* lie_algebra.morphism.range_bracket
- \+ *lemma* lie_algebra.morphism.range_coe
- \+ *lemma* coe_to_submodule_eq_iff
- \+ *lemma* coe_to_subalgebra
- \+ *lemma* bot_coe_submodule
- \+ *lemma* top_coe_submodule
- \+ *lemma* sup_coe_to_submodule
- \+ *lemma* inf_coe_to_submodule
- \+ *lemma* mem_inf
- \+ *lemma* lie_span_eq
- \+ *lemma* lie_inf
- \+ *lemma* inf_lie
- \- *lemma* coe_sup
- \+ *theorem* inf_coe
- \+/\- *def* lie_algebra.morphism.range
- \+/\- *def* lie_subalgebra.map



## [2021-01-15 10:58:03](https://github.com/leanprover-community/mathlib/commit/ed0ae3e)
feat(analysis/calculus/inverse): a map that has an invertible strict derivative at every point is an open map ([#5753](https://github.com/leanprover-community/mathlib/pull/5753))
More generally, the same is true for a map that is a local homeomorphism near every point.
#### Estimated changes
Modified src/analysis/calculus/inverse.lean
- \+ *lemma* map_nhds_eq
- \+ *lemma* open_map_of_strict_fderiv
- \+ *lemma* open_map_of_strict_deriv

Modified src/order/filter/basic.lean
- \+ *lemma* map_id'
- \+/\- *lemma* le_map
- \+ *lemma* le_map_of_right_inverse

Modified src/topology/local_homeomorph.lean
- \+ *lemma* map_nhds_eq

Modified src/topology/maps.lean
- \+/\- *lemma* is_open_range
- \+/\- *lemma* image_mem_nhds
- \+/\- *lemma* nhds_le
- \+ *lemma* of_nhds_le



## [2021-01-15 10:58:01](https://github.com/leanprover-community/mathlib/commit/4c1d12f)
feat(data/complex/basic): Adding `im_eq_sub_conj` ([#5750](https://github.com/leanprover-community/mathlib/pull/5750))
Adds `im_eq_sub_conj`, which I couldn't find in the library.
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *theorem* im_eq_sub_conj



## [2021-01-15 09:57:54](https://github.com/leanprover-community/mathlib/commit/94f45c7)
chore(linear_algebra/quadratic_form): Add missing simp lemmas about quadratic_form.polar ([#5748](https://github.com/leanprover-community/mathlib/pull/5748))
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* polar_neg_left
- \+ *lemma* polar_sub_left
- \+ *lemma* polar_neg_right
- \+ *lemma* polar_sub_right
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_neg



## [2021-01-15 08:35:59](https://github.com/leanprover-community/mathlib/commit/09c2345)
feat(category_theory/over): epis and monos in the over category ([#5684](https://github.com/leanprover-community/mathlib/pull/5684))
#### Estimated changes
Modified src/category_theory/over.lean
- \+ *lemma* epi_of_epi_left
- \+ *lemma* mono_of_mono_left



## [2021-01-15 08:35:56](https://github.com/leanprover-community/mathlib/commit/395eb2b)
feat(category_theory): subterminal objects ([#5669](https://github.com/leanprover-community/mathlib/pull/5669))
#### Estimated changes
Created src/category_theory/subterminal.lean
- \+ *lemma* is_subterminal.def
- \+ *lemma* is_subterminal.mono_is_terminal_from
- \+ *lemma* is_subterminal.mono_terminal_from
- \+ *lemma* is_subterminal_of_mono_is_terminal_from
- \+ *lemma* is_subterminal_of_mono_terminal_from
- \+ *lemma* is_subterminal_of_is_terminal
- \+ *lemma* is_subterminal_of_terminal
- \+ *lemma* is_subterminal_of_is_iso_diag
- \+ *def* is_subterminal
- \+ *def* is_subterminal.is_iso_diag
- \+ *def* is_subterminal.iso_diag
- \+ *def* subterminals
- \+ *def* subterminal_inclusion



## [2021-01-15 08:35:54](https://github.com/leanprover-community/mathlib/commit/f8db86a)
feat(category_theory/limits): finite products from binary products ([#5516](https://github.com/leanprover-community/mathlib/pull/5516))
Adds constructions for finite products from binary products and terminal object, and a preserves version
#### Estimated changes
Created src/category_theory/limits/shapes/constructions/finite_products_of_binary_products.lean
- \+ *lemma* has_finite_products_of_has_binary_and_terminal
- \+ *def* extend_fan
- \+ *def* extend_fan_is_limit
- \+ *def* preserves_ulift_fin_of_preserves_binary_and_terminal
- \+ *def* preserves_finite_products_of_preserves_binary_and_terminal



## [2021-01-15 05:41:26](https://github.com/leanprover-community/mathlib/commit/faf106a)
refactor(data/real/{e,}nnreal): reuse generic lemmas ([#5751](https://github.com/leanprover-community/mathlib/pull/5751))
* reuse `div_eq_mul_inv` and `one_div` from `div_inv_monoid`;
* reuse lemmas about `group_with_zero` instead of repeating them in the `nnreal` namespace;
* add `has_sum.div_const`.
#### Estimated changes
Modified src/analysis/analytic/radius_liminf.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/specific_limits.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* div_top
- \+/\- *lemma* top_div_coe
- \- *lemma* div_def
- \- *lemma* mul_div_assoc

Modified src/data/real/nnreal.lean
- \+/\- *lemma* div_pos
- \- *lemma* div_def
- \- *lemma* inv_zero
- \- *lemma* inv_eq_zero
- \- *lemma* inv_one
- \- *lemma* div_one
- \- *lemma* inv_mul_cancel
- \- *lemma* mul_inv_cancel
- \- *lemma* div_self
- \- *lemma* mul_div_cancel
- \- *lemma* mul_div_cancel'
- \- *lemma* inv_inv
- \- *lemma* mul_div_assoc'
- \- *lemma* inv_eq_one_div
- \- *lemma* div_mul_eq_mul_div
- \- *lemma* one_div
- \- *lemma* one_div_div
- \- *lemma* div_eq_mul_one_div
- \- *lemma* div_div_eq_mul_div
- \- *lemma* div_div_eq_div_mul
- \- *lemma* div_eq_div_iff
- \- *lemma* div_eq_iff
- \- *lemma* eq_div_iff
- \- *theorem* div_pow
- \- *theorem* pow_eq_zero
- \- *theorem* pow_ne_zero

Modified src/measure_theory/haar_measure.lean


Modified src/ring_theory/perfection.lean


Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum.div_const

Modified src/topology/metric_space/antilipschitz.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/lipschitz.lean




## [2021-01-15 05:41:24](https://github.com/leanprover-community/mathlib/commit/931182e)
chore(algebra/ordered_ring): add a few simp lemmas ([#5749](https://github.com/leanprover-community/mathlib/pull/5749))
* fix misleading names `neg_lt_iff_add_nonneg` → `neg_lt_iff_pos_add`,
  `neg_lt_iff_add_nonneg'` → `neg_lt_iff_pos_add'`;
* add `@[simp]` to `abs_mul_abs_self` and `abs_mul_self`;
* add lemmas `neg_le_self_iff`, `neg_lt_self_iff`, `le_neg_self_iff`,
  `lt_neg_self_iff`, `abs_eq_self`, `abs_eq_neg_self`.
#### Estimated changes
Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* abs_mul_abs_self
- \+/\- *lemma* abs_mul_self
- \+ *lemma* neg_le_self_iff
- \+ *lemma* neg_lt_self_iff
- \+ *lemma* le_neg_self_iff
- \+ *lemma* lt_neg_self_iff
- \+ *lemma* abs_eq_self
- \+ *lemma* abs_eq_neg_self
- \+/\- *lemma* neg_one_lt_zero



## [2021-01-15 02:19:33](https://github.com/leanprover-community/mathlib/commit/5d003d8)
chore(scripts): update nolints.txt ([#5754](https://github.com/leanprover-community/mathlib/pull/5754))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-15 02:19:31](https://github.com/leanprover-community/mathlib/commit/7151fb7)
chore(data/equiv/basic): equiv/perm_congr simp lemmas ([#5737](https://github.com/leanprover-community/mathlib/pull/5737))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv_congr_refl_left
- \+ *lemma* equiv_congr_refl_right
- \+ *lemma* perm_congr_def
- \+ *lemma* perm_congr_symm
- \+ *lemma* perm_congr_symm_apply



## [2021-01-14 22:10:57](https://github.com/leanprover-community/mathlib/commit/64a1b19)
feat(data/equiv/basic): subsingleton equiv and perm ([#5736](https://github.com/leanprover-community/mathlib/pull/5736))
#### Estimated changes
Modified src/category_theory/simple.lean


Modified src/data/equiv/basic.lean
- \+ *lemma* perm.subsingleton_eq_refl
- \+ *theorem* perm.coe_subsingleton



## [2021-01-14 22:10:54](https://github.com/leanprover-community/mathlib/commit/975f41a)
feat(order): closure operators ([#5524](https://github.com/leanprover-community/mathlib/pull/5524))
Adds closure operators on a partial order, as in [wikipedia](https://en.wikipedia.org/wiki/Closure_operator#Closure_operators_on_partially_ordered_sets). I made them bundled for no particular reason, I don't mind unbundling.
#### Estimated changes
Created src/order/closure.lean
- \+ *lemma* ext
- \+ *lemma* monotone
- \+ *lemma* le_closure
- \+ *lemma* idempotent
- \+ *lemma* le_closure_iff
- \+ *lemma* closure_top
- \+ *lemma* closure_inter_le
- \+ *lemma* closure_union_closure_le
- \+ *lemma* mem_closed_iff
- \+ *lemma* mem_closed_iff_closure_le
- \+ *lemma* closure_eq_self_of_mem_closed
- \+ *lemma* closure_is_closed
- \+ *lemma* closed_eq_range_close
- \+ *lemma* top_mem_closed
- \+ *lemma* closure_le_closed_iff_le
- \+ *def* id
- \+ *def* closed
- \+ *def* to_closed
- \+ *def* gi



## [2021-01-14 19:06:18](https://github.com/leanprover-community/mathlib/commit/0817e7f)
feat(measure_theory): absolute continuity of the integral ([#5743](https://github.com/leanprover-community/mathlib/pull/5743))
### API changes:
#### `ennreal`s and `nnreal`s:
* `ennreal.mul_le_mul` and `ennreal.mul_lt_mul` are now `mono` lemmas;
* rename `ennreal.sub_lt_sub_self` to `ennreal.sub_lt_self`: there is no `-` in the RHS;
* new lemmas `enrneal.mul_div_le`, `nnreal.sub_add_eq_max`, and `nnreal.add_sub_eq_max`;
* add new lemma `ennreal.bsupr_add`, use in in the proof of `ennreal.Sup_add`;
#### Complete lattice
* new lemma `supr_lt_iff`;
#### Simple functions
* new lemmas `simple_func.exists_forall_le`, `simple_func.map_add`,
  `simple_func.sub_apply`;
* weaker typeclass assumptions in `simple_func.coe_sub`;
* `monotone_eapprox` is now a `mono` lemma;
#### Integration
* new lemmas `exists_simple_func_forall_lintegral_sub_lt_of_pos`,
  `exists_pos_set_lintegral_lt_of_measure_lt`,
  `tendsto_set_lintegral_zero`, and
  `has_finite_integral.tendsto_set_integral_nhds_zero`.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+/\- *lemma* mul_le_mul
- \+/\- *lemma* mul_lt_mul
- \+ *lemma* mul_div_le

Modified src/data/real/nnreal.lean
- \+ *lemma* sub_add_eq_max
- \+ *lemma* add_sub_eq_max

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* has_finite_integral.tendsto_set_integral_nhds_zero
- \+ *lemma* integrable.tendsto_set_integral_nhds_zero

Modified src/measure_theory/content.lean


Modified src/measure_theory/integration.lean
- \+ *lemma* exists_forall_le
- \+/\- *lemma* coe_sub
- \+ *lemma* sub_apply
- \+/\- *lemma* monotone_eapprox
- \+ *lemma* exists_simple_func_forall_lintegral_sub_lt_of_pos
- \+ *lemma* exists_pos_set_lintegral_lt_of_measure_lt
- \+ *lemma* tendsto_set_lintegral_zero
- \+ *theorem* map_add

Modified src/order/complete_lattice.lean
- \+ *theorem* supr_lt_iff

Modified src/topology/instances/ennreal.lean
- \+ *lemma* bsupr_add



## [2021-01-14 19:06:16](https://github.com/leanprover-community/mathlib/commit/3b8cfdc)
feat(linear_algebra/{exterior,tensor,free}_algebra): provide left-inverses for `algebra_map` and `ι` ([#5722](https://github.com/leanprover-community/mathlib/pull/5722))
The strategy used for `algebra_map` here can't be used on `clifford_algebra` as the zero map does not satisfy `f m * f m = Q m`.
#### Estimated changes
Modified src/algebra/free_algebra.lean
- \+ *lemma* algebra_map_left_inverse
- \+ *def* algebra_map_inv

Modified src/algebra/triv_sq_zero_ext.lean
- \+ *def* snd_hom

Modified src/linear_algebra/exterior_algebra.lean
- \+ *lemma* algebra_map_left_inverse
- \+ *lemma* ι_left_inverse
- \- *lemma* ι_injective
- \+ *def* algebra_map_inv
- \+ *def* ι_inv

Modified src/linear_algebra/tensor_algebra.lean
- \+ *lemma* algebra_map_left_inverse
- \+ *lemma* ι_left_inverse
- \- *lemma* ι_injective
- \+ *def* algebra_map_inv
- \+ *def* ι_inv



## [2021-01-14 15:25:47](https://github.com/leanprover-community/mathlib/commit/91b099e)
chore(data/equiv/fin): simp definitional lemmas ([#5740](https://github.com/leanprover-community/mathlib/pull/5740))
#### Estimated changes
Modified src/data/equiv/fin.lean
- \+ *lemma* fin_succ_equiv_zero
- \+ *lemma* fin_succ_equiv_succ
- \+ *lemma* fin_succ_equiv_symm_none
- \+ *lemma* fin_succ_equiv_symm_some



## [2021-01-14 15:25:44](https://github.com/leanprover-community/mathlib/commit/7e9094b)
feat(control/equiv_functor): simp defn lemmas and injectivity ([#5739](https://github.com/leanprover-community/mathlib/pull/5739))
#### Estimated changes
Modified src/control/equiv_functor.lean
- \+/\- *lemma* map_equiv_symm_apply
- \+ *lemma* map_equiv_refl
- \+ *lemma* map_equiv_symm
- \+ *lemma* map_equiv_trans
- \+ *lemma* map_equiv.injective



## [2021-01-14 15:25:42](https://github.com/leanprover-community/mathlib/commit/e3cc92e)
chore(data/equiv/basic): swap symm and trans simp lemmas ([#5738](https://github.com/leanprover-community/mathlib/pull/5738))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *lemma* symm_trans_swap_trans
- \+ *lemma* trans_swap_trans_symm
- \+/\- *theorem* swap_self



## [2021-01-14 15:25:40](https://github.com/leanprover-community/mathlib/commit/de8b88f)
chore(group_theory/perm/sign): trans and symm simp ([#5735](https://github.com/leanprover-community/mathlib/pull/5735))
#### Estimated changes
Modified src/group_theory/perm/sign.lean
- \+ *lemma* sign_trans
- \+ *lemma* sign_symm
- \+/\- *lemma* sign_symm_trans_trans
- \+ *lemma* sign_trans_trans_symm



## [2021-01-14 15:25:37](https://github.com/leanprover-community/mathlib/commit/82532c1)
chore(data/set/basic): reuse some proofs about `boolean_algebra` ([#5728](https://github.com/leanprover-community/mathlib/pull/5728))
API changes:
* merge `set.compl_compl` with `compl_compl'`;
* add `is_compl.compl_eq_iff`, `compl_eq_top`, and `compl_eq_bot`;
* add `simp` attribute to `compl_le_compl_iff_le`;
* fix misleading name in `compl_le_iff_compl_le`, add a missing
  variant;
* add `simp` attribute to `compl_empty_iff` and `compl_univ_iff`;
* add `set.subset.eventually_le`.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/data/set/basic.lean
- \+/\- *lemma* compl_empty_iff
- \+/\- *lemma* compl_univ_iff
- \+/\- *theorem* inter_compl_self
- \+/\- *theorem* compl_inter_self
- \+/\- *theorem* compl_empty
- \+/\- *theorem* compl_union
- \+/\- *theorem* compl_inter
- \+/\- *theorem* compl_univ
- \- *theorem* compl_compl

Modified src/measure_theory/measurable_space.lean


Modified src/order/boolean_algebra.lean
- \+ *theorem* compl_compl
- \+ *theorem* is_compl.compl_eq_iff
- \+ *theorem* compl_eq_top
- \+ *theorem* compl_eq_bot
- \+/\- *theorem* compl_le_compl_iff_le
- \+ *theorem* le_compl_iff_le_compl
- \+/\- *theorem* compl_le_iff_compl_le
- \- *theorem* compl_compl'

Modified src/order/filter/basic.lean
- \+ *lemma* set.subset.eventually_le

Modified src/order/filter/ultrafilter.lean


Modified src/topology/separation.lean




## [2021-01-14 11:59:28](https://github.com/leanprover-community/mathlib/commit/3b3f9a2)
refactor(measure_theory): review def&API of the `dirac` measure ([#5732](https://github.com/leanprover-community/mathlib/pull/5732))
* use `set.indicator` instead of `⨆ a ∈ s, 1` in the definition.
* rename some theorems to `thm'`, add a version assuming
  `[measurable_singleton_class α]` but not
  `is_measurable s`/`measurable f` under the old name.
* rename some lemmas from `eventually` to `ae`.
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* integral_dirac'
- \+/\- *lemma* integral_dirac

Modified src/measure_theory/category/Meas.lean


Modified src/measure_theory/giry_monad.lean
- \- *lemma* map_dirac

Modified src/measure_theory/integration.lean
- \+ *lemma* lintegral_dirac'
- \+/\- *lemma* lintegral_dirac

Modified src/measure_theory/measure_space.lean
- \+ *lemma* le_dirac_apply
- \+/\- *lemma* dirac_apply'
- \+/\- *lemma* dirac_apply_of_mem
- \+/\- *lemma* dirac_apply
- \+ *lemma* map_dirac
- \+ *lemma* le_sum_apply
- \+ *lemma* le_count_apply
- \+/\- *lemma* count_apply_infinite
- \+ *lemma* mem_ae_dirac_iff
- \+ *lemma* ae_dirac_iff
- \+ *lemma* ae_dirac_eq
- \+ *lemma* ae_eq_dirac'
- \+ *lemma* ae_eq_dirac
- \- *lemma* mem_dirac_ae_iff
- \- *lemma* eventually_dirac
- \- *lemma* eventually_eq_dirac
- \- *lemma* dirac_ae_eq
- \- *lemma* eventually_eq_dirac'

Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/prod.lean


Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* finset.tsum_subtype'



## [2021-01-14 11:59:26](https://github.com/leanprover-community/mathlib/commit/8bc26d1)
feat(algebra/order): ne_iff_lt_iff_le
 
 ([#5731](https://github.com/leanprover-community/mathlib/pull/5731))
#### Estimated changes
Modified src/algebra/order.lean
- \+ *lemma* ne_iff_lt_iff_le

Modified src/data/buffer/parser/basic.lean
- \- *lemma* ne_iff_lt_iff_le
- \- *lemma* nat.le_of_sub_eq_pos



## [2021-01-14 08:39:13](https://github.com/leanprover-community/mathlib/commit/159542a)
chore(*): split some long lines ([#5742](https://github.com/leanprover-community/mathlib/pull/5742))
#### Estimated changes
Modified src/algebra/category/CommRing/basic.lean
- \+/\- *def* to_CommRing_iso

Modified src/algebra/category/CommRing/limits.lean


Modified src/algebra/category/Group/zero.lean


Modified src/algebra/category/Module/basic.lean
- \+/\- *def* linear_equiv_iso_Module_iso

Modified src/algebra/category/Mon/limits.lean


Modified src/algebra/direct_limit.lean
- \+/\- *lemma* of.zero_exact
- \+/\- *theorem* of.zero_exact

Modified src/algebra/free_algebra.lean


Modified src/algebra/group/defs.lean


Modified src/algebra/group_action_hom.lean
- \+/\- *theorem* is_invariant_subring.coe_subtype_hom

Modified src/algebra/group_power/basic.lean
- \+/\- *lemma* min_pow_dvd_add
- \+/\- *theorem* pow_eq_zero

Modified src/algebra/invertible.lean
- \+/\- *lemma* invertible_unique
- \+/\- *def* invertible.map

Modified src/algebra/lie/basic.lean
- \+/\- *lemma* coe_to_linear_equiv
- \+/\- *lemma* coe_to_lie_module_hom

Modified src/algebra/lie/classical.lean


Modified src/algebra/linear_recurrence.lean


Modified src/algebra/module/basic.lean


Modified src/algebra/module/ordered.lean


Modified src/algebra/module/pi.lean


Modified src/algebra/monoid_algebra.lean
- \+/\- *lemma* lift_nc_one
- \+/\- *def* lift_nc_alg_hom

Modified src/algebra/ring/pi.lean


Modified src/algebraic_geometry/Scheme.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/composition.lean
- \+/\- *lemma* comp_coeff_zero''
- \+/\- *lemma* length_sigma_composition_aux

Modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* has_deriv_within_at.union

Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* has_fderiv_within_at.union

Modified src/analysis/calculus/iterated_deriv.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/hofer.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* nnnorm_sum_le
- \+/\- *lemma* tsum_of_norm_bounded

Modified src/analysis/normed_space/inner_product.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/special_functions/trigonometric.lean
- \+/\- *lemma* cos_lt_cos_of_nonneg_of_le_pi_div_two
- \+/\- *lemma* deriv_within_arctan
- \+/\- *theorem* sin_eq_iff_eq_or_add_eq_pi

Modified src/category_theory/adjunction/basic.lean
- \+/\- *def* right_adjoint_of_nat_iso

Modified src/category_theory/concrete_category/basic.lean
- \+/\- *lemma* concrete_category.mono_of_injective
- \+/\- *lemma* concrete_category.epi_of_surjective
- \+/\- *def* concrete_category.has_coe_to_sort
- \+/\- *def* forget₂
- \+/\- *def* has_forget₂.mk'

Modified src/category_theory/eq_to_hom.lean
- \+/\- *lemma* eq_to_hom_op
- \+/\- *lemma* eq_to_hom_unop

Modified src/category_theory/graded_object.lean


Modified src/combinatorics/pigeonhole.lean


Modified src/control/uliftable.lean
- \+/\- *def* up_map
- \+/\- *def* down_map

Modified src/data/analysis/filter.lean
- \+/\- *theorem* of_equiv_σ
- \+/\- *theorem* tendsto_iff

Modified src/data/complex/is_R_or_C.lean


Modified src/data/equiv/local_equiv.lean
- \+/\- *lemma* restr_target
- \+/\- *lemma* refl_restr_source
- \+/\- *lemma* refl_restr_target
- \+/\- *lemma* of_set_symm
- \+/\- *lemma* trans_target
- \+/\- *lemma* refl_to_local_equiv

Modified src/data/fintype/basic.lean
- \+/\- *lemma* mem_of_mem_perms_of_list
- \+/\- *lemma* mem_perms_of_list_iff
- \+/\- *theorem* to_finset_inj
- \+/\- *def* of_surjective

Modified src/data/qpf/multivariate/basic.lean


Modified src/data/sym.lean
- \+/\- *lemma* cons_equiv_eq_equiv_cons

Modified src/data/typevec.lean
- \+/\- *lemma* typevec_cases_cons₂_append_fun
- \+/\- *lemma* const_append1
- \+/\- *lemma* repeat_eq_append1
- \+/\- *lemma* repeat_eq_iff_eq
- \+/\- *lemma* subtype_val_nil
- \+/\- *def* typevec_cases_nil₃
- \+/\- *def* typevec_cases_cons₂
- \+/\- *def* rel_last'
- \+/\- *def* to_subtype
- \+/\- *def* of_subtype

Modified src/testing/slim_check/functions.lean
- \+/\- *lemma* apply_id_injective
- \+/\- *def* perm.slice

Modified src/testing/slim_check/sampleable.lean
- \+/\- *def* sum.shrink

Modified src/topology/basic.lean
- \+/\- *lemma* interior_union_is_closed_of_interior_empty

Modified src/topology/metric_space/gromov_hausdorff.lean
- \+/\- *lemma* eq_to_GH_space_iff
- \+/\- *lemma* to_GH_space_eq_to_GH_space_iff_isometric

Modified src/topology/metric_space/hausdorff_distance.lean
- \+/\- *lemma* exists_edist_lt_of_Hausdorff_edist_lt
- \+/\- *lemma* Hausdorff_edist_le_ediam
- \+/\- *lemma* Hausdorff_edist_closure
- \+/\- *lemma* Hausdorff_edist_zero_iff_closure_eq_closure
- \+/\- *lemma* Hausdorff_dist_closure

Modified src/topology/metric_space/isometry.lean
- \+/\- *theorem* isometry.comp
- \+/\- *def* nonempty_compacts.Kuratowski_embedding

Modified src/topology/separation.lean
- \+/\- *lemma* nhds_inter_eq_singleton_of_mem_discrete
- \+/\- *lemma* is_compact.finite_compact_cover

Modified src/topology/sequences.lean
- \+/\- *lemma* is_compact.tendsto_subseq'

Modified src/topology/subset_properties.lean
- \+/\- *theorem* is_preconnected_iff_subset_of_disjoint_closed

Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/separation.lean
- \+/\- *lemma* separation_rel_comap
- \+/\- *lemma* eq_of_uniformity_inf_nhds



## [2021-01-14 07:15:46](https://github.com/leanprover-community/mathlib/commit/1509c29)
chore(archive/100-theorems-list): 83_friendship_graphs ([#5727](https://github.com/leanprover-community/mathlib/pull/5727))
Cleaned up some lint and put it in terms of the new `simple_graph.common_neighbors`.
#### Estimated changes
Modified archive/100-theorems-list/83_friendship_graphs.lean
- \+/\- *lemma* adj_matrix_sq_mod_p_of_regular
- \+/\- *lemma* adj_matrix_pow_mod_p_of_regular
- \+/\- *lemma* false_of_three_le_degree
- \- *lemma* mem_common_friends
- \+/\- *theorem* adj_matrix_sq_of_regular
- \+/\- *theorem* friendship_theorem
- \+/\- *def* friendship
- \- *def* common_friends

Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* mem_common_neighbors



## [2021-01-14 03:38:41](https://github.com/leanprover-community/mathlib/commit/c8c6d2e)
feat(ci): Emit error messages in a way understood by github ([#5726](https://github.com/leanprover-community/mathlib/pull/5726))
This uses the commands described [here](https://github.com/actions/toolkit/blob/master/docs/commands.md#log-level), for which [the implementation](https://github.com/actions/toolkit/blob/af821474235d3c5e1f49cee7c6cf636abb0874c4/packages/core/src/command.ts#L36-L94) provides a slightly clearer spec.
This means github now annotates broken lines, and highlights the error in red.
Originally I tried to implement this using "problem matchers", but these do not support multi-line error messages.
Supporting this in the linter is something that I'll leave for a follow-up PR.
#### Estimated changes
Modified scripts/detect_errors.py
- \+ *def* encode_msg_text_for_github(msg):



## [2021-01-14 03:38:39](https://github.com/leanprover-community/mathlib/commit/d11d83a)
feat(measure_theory/lebesgue_measure): volume of a box in `ℝⁿ` ([#5635](https://github.com/leanprover-community/mathlib/pull/5635))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+/\- *lemma* coe_nat
- \+ *lemma* of_real_coe_nat
- \+/\- *lemma* nat_ne_top
- \+/\- *lemma* top_ne_nat

Modified src/data/real/nnreal.lean
- \+ *lemma* mk_coe_nat
- \+ *lemma* of_real_coe_nat

Modified src/measure_theory/lebesgue_measure.lean
- \+ *lemma* volume_Ioi
- \+ *lemma* volume_Ici
- \+ *lemma* volume_Iio
- \+ *lemma* volume_Iic
- \+ *lemma* volume_Icc_pi
- \+ *lemma* volume_Icc_pi_to_real
- \+ *lemma* volume_pi_Ioo
- \+ *lemma* volume_pi_Ioo_to_real
- \+ *lemma* volume_pi_Ioc
- \+ *lemma* volume_pi_Ioc_to_real
- \+ *lemma* volume_pi_Ico
- \+ *lemma* volume_pi_Ico_to_real

Modified src/measure_theory/pi.lean
- \+/\- *lemma* volume_pi
- \+ *lemma* volume_pi_pi
- \- *lemma* measure_space.pi_def



## [2021-01-14 02:21:22](https://github.com/leanprover-community/mathlib/commit/c050452)
chore(scripts): update nolints.txt ([#5730](https://github.com/leanprover-community/mathlib/pull/5730))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-01-13 21:36:30](https://github.com/leanprover-community/mathlib/commit/71a3261)
feat(logic/basic): exists_eq simp lemmas without and.comm ([#5694](https://github.com/leanprover-community/mathlib/pull/5694))
#### Estimated changes
Modified src/control/traversable/instances.lean


Modified src/data/buffer/parser/basic.lean
- \- *lemma* exists_eq_right_right
- \- *lemma* exists_eq_right_right'

Modified src/data/list/perm.lean


Modified src/logic/basic.lean
- \+ *theorem* exists_eq_right_right
- \+ *theorem* exists_eq_right_right'



## [2021-01-13 21:36:28](https://github.com/leanprover-community/mathlib/commit/6397e14)
feat(data/nat/cast): add nat.bin_cast for faster casting ([#5664](https://github.com/leanprover-community/mathlib/pull/5664))
[As suggested](https://github.com/leanprover-community/mathlib/pull/5462#discussion_r553226279) by @gebner.
#### Estimated changes
Modified src/data/nat/cast.lean
- \+ *lemma* bin_cast_eq



## [2021-01-13 18:52:53](https://github.com/leanprover-community/mathlib/commit/69e9344)
feat(data/set/finite): add lemma with iff statement about when finite sets can be subsets ([#5725](https://github.com/leanprover-community/mathlib/pull/5725))
Part of [#5698](https://github.com/leanprover-community/mathlib/pull/5698) in order to prove statements about strongly regular graphs.
Co-author: @shingtaklam1324
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* subset_iff_to_finset_subset



## [2021-01-13 18:52:51](https://github.com/leanprover-community/mathlib/commit/0b9fbc4)
feat(combinatorics/simple_graph/basic): add definition of common neighbors and lemmas ([#5718](https://github.com/leanprover-community/mathlib/pull/5718))
Part of [#5698](https://github.com/leanprover-community/mathlib/pull/5698) in order to prove facts about strongly regular graphs
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* common_neighbors_eq
- \+ *lemma* common_neighbors_symm
- \+ *lemma* not_mem_common_neighbors_left
- \+ *lemma* not_mem_common_neighbors_right
- \+ *lemma* common_neighbors_subset_neighbor_set
- \+ *lemma* is_regular_of_degree_eq
- \+ *lemma* degree_lt_card_verts
- \+ *def* common_neighbors



## [2021-01-13 18:52:49](https://github.com/leanprover-community/mathlib/commit/7ce4717)
refactor(computability/reduce): define many-one degrees without parameter ([#2630](https://github.com/leanprover-community/mathlib/pull/2630))
The file `reduce.lean` defines many-one degrees for computable reductions.  At the moment every primcodable type `α` has a separate type of degrees `many_one_degree α`.  This is completely antithetical to the notion of degrees, which are introduced to classify problems up to many-one equivalence.
This PR defines a single `many_one_degree` type that lives in `Type 0`.  We use the `ulower` infrastructure from [#2574](https://github.com/leanprover-community/mathlib/pull/2574) which shows that every type is computably equivalent to a subset of natural numbers.  The function `many_one_degree.of` which assigns to every set of a primcodable type a degree is still universe polymorphic.  In particular, we show that `of p = of q ↔ many_one_equiv p q`, etc. in maximal generality, where `p` and `q` are subsets of different types in different universes.
See previous discussion at [#1203](https://github.com/leanprover-community/mathlib/pull/1203).
#### Estimated changes
Modified src/computability/partrec.lean
- \+ *theorem* option_get_or_else
- \+ *theorem* subtype_mk

Modified src/computability/reduce.lean
- \+ *lemma* ulower.down_computable
- \+ *lemma* many_one_equiv_up
- \+ *lemma* to_nat_many_one_reducible
- \+ *lemma* many_one_reducible_to_nat
- \+ *lemma* many_one_reducible_to_nat_to_nat
- \+ *lemma* to_nat_many_one_equiv
- \+ *lemma* many_one_equiv_to_nat
- \+ *lemma* of_eq_of
- \+ *lemma* of_le_of
- \+ *lemma* add_of
- \+/\- *theorem* reflexive_many_one_reducible
- \+/\- *theorem* transitive_many_one_reducible
- \+/\- *theorem* one_one_reducible.of_equiv
- \+/\- *theorem* one_one_reducible.of_equiv_symm
- \+/\- *theorem* reflexive_one_one_reducible
- \+/\- *theorem* transitive_one_one_reducible
- \+/\- *theorem* equivalence_of_many_one_equiv
- \- *theorem* many_one_degree.of_le_of
- \- *theorem* many_one_degree.of_le_of'
- \- *theorem* many_one_degree.le_refl
- \- *theorem* many_one_degree.le_antisymm
- \- *theorem* many_one_degree.le_trans
- \- *theorem* many_one_degree.le_comap_left
- \- *theorem* many_one_degree.le_comap_right
- \- *theorem* many_one_degree.add_le
- \- *theorem* many_one_degree.le_add_left
- \- *theorem* many_one_degree.le_add_right
- \- *theorem* many_one_degree.add_le'
- \- *theorem* many_one_degree.le_add_left'
- \- *theorem* many_one_degree.le_add_right'
- \+/\- *def* equiv.computable
- \+ *def* to_nat
- \+/\- *def* many_one_degree
- \+ *def* of
- \- *def* many_one_equiv_setoid
- \- *def* many_one_degree.le
- \- *def* many_one_degree.of
- \- *def* many_one_degree.comap
- \- *def* many_one_degree.add



## [2021-01-13 16:08:10](https://github.com/leanprover-community/mathlib/commit/d533fbb)
fix(finsupp/pointwise): Relax the ring requirement to semiring ([#5723](https://github.com/leanprover-community/mathlib/pull/5723))
#### Estimated changes
Modified src/data/finsupp/pointwise.lean




## [2021-01-13 16:08:07](https://github.com/leanprover-community/mathlib/commit/340ddf8)
chore(scripts): don't assume cwd when running lint-style. ([#5721](https://github.com/leanprover-community/mathlib/pull/5721))
Allows running the linter from any ol' directory.
#### Estimated changes
Modified scripts/lint-style.py




## [2021-01-13 16:08:04](https://github.com/leanprover-community/mathlib/commit/d351cfe)
feat(data/finset): sup_eq_bind ([#5717](https://github.com/leanprover-community/mathlib/pull/5717))
`finset.sup s f` is equal to `finset.bind s f` when `f : α → finset β` is an indexed family of finite sets.  This is a proof of that with a couple supporting lemmas.  (There might be a more direct proof through the definitions of `sup` and `bind`, which are eventually in terms of `multiset.foldr`.)
I also moved `finset.mem_sup` to `multiset.mem_sup` and gave a new `finset.mem_sup` for indexed families of `finset`, where the old one was for indexed families of `multiset`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* val_to_finset

Modified src/data/finset/lattice.lean
- \+ *lemma* sup_to_finset
- \+/\- *lemma* mem_sup
- \+ *lemma* sup_eq_bind

Modified src/data/mv_polynomial/variables.lean




## [2021-01-13 16:08:02](https://github.com/leanprover-community/mathlib/commit/3ac4bb2)
feat(combinatorics/simple_graph/basic): add definition of complement of simple graph ([#5697](https://github.com/leanprover-community/mathlib/pull/5697))
Add definition of the complement of a simple graph. Part of branch [strongly_regular_graph](https://github.com/leanprover-community/mathlib/tree/strongly_regular_graph), with the goal of proving facts about strongly regular graphs.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* compl_adj
- \+ *lemma* compl_compl
- \+ *lemma* compl_involutive
- \+ *lemma* compl_neighbor_set_disjoint
- \+ *lemma* neighbor_set_union_compl_neighbor_set_eq
- \+ *def* compl



## [2021-01-13 14:54:29](https://github.com/leanprover-community/mathlib/commit/c8574c8)
feat(analysis/special_functions/pow): add various lemmas about ennreal.rpow ([#5701](https://github.com/leanprover-community/mathlib/pull/5701))
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* rpow_eq_top_iff_of_pos
- \+ *lemma* rpow_le_rpow_iff
- \+ *lemma* rpow_lt_rpow_iff
- \+ *lemma* le_rpow_one_div_iff
- \+ *lemma* lt_rpow_one_div_iff
- \+ *lemma* rpow_pos_of_nonneg
- \+ *lemma* rpow_pos
- \+ *lemma* rpow_left_injective
- \+ *lemma* rpow_left_surjective
- \+ *lemma* rpow_left_bijective
- \+ *lemma* rpow_left_monotone_of_nonneg
- \+ *lemma* rpow_left_strict_mono_of_pos



## [2021-01-13 10:19:12](https://github.com/leanprover-community/mathlib/commit/b6cca97)
feat(linear_algebra/{exterior,tensor}_algebra): Prove that `ι` is injective ([#5712](https://github.com/leanprover-community/mathlib/pull/5712))
This strategy can't be used on `clifford_algebra`, and the obvious guess of trying to define a `less_triv_sq_quadratic_form_ext` leads to a non-associative multiplication; so for now, we just handle these two cases.
#### Estimated changes
Modified src/linear_algebra/exterior_algebra.lean
- \+ *lemma* ι_injective

Modified src/linear_algebra/tensor_algebra.lean
- \+ *lemma* ι_injective



## [2021-01-13 02:51:51](https://github.com/leanprover-community/mathlib/commit/b9b6b16)
chore(scripts): update nolints.txt ([#5720](https://github.com/leanprover-community/mathlib/pull/5720))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-13 02:51:48](https://github.com/leanprover-community/mathlib/commit/5a532ca)
fix(tactic/ring): fix loop in ring ([#5711](https://github.com/leanprover-community/mathlib/pull/5711))
This occurs because when we name the atoms in `A * B = 2`, `A` is the
first and `B` is the second, and once we put it in horner form it ends up
as `B * A = 2`; but then when we go to rewrite it again `B` is named atom
number 1 and `A` is atom number 2, so we write it the other way around
and end up back at `A * B = 2`. The solution implemented here is to
retain the atom map across calls to `ring.eval` while simp is driving
it, so we end up rewriting it to `B * A = 2` in the first place but in the
second pass we still think `B` is the second atom so we stick with the
`B * A` order.
Fixes [#2672](https://github.com/leanprover-community/mathlib/pull/2672)
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean


Modified src/data/pnat/xgcd.lean


Modified src/tactic/ring.lean


Modified test/ring.lean




## [2021-01-12 22:49:15](https://github.com/leanprover-community/mathlib/commit/fe5ec00)
doc(tactic/generalize_proofs): docs and test for generalize_proofs ([#5715](https://github.com/leanprover-community/mathlib/pull/5715))
As requested on Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Extracting.20un-named.20proofs.20from.20the.20goal.20state/near/222472426
#### Estimated changes
Modified src/tactic/generalize_proofs.lean


Created test/generalize_proofs.lean




## [2021-01-12 22:49:13](https://github.com/leanprover-community/mathlib/commit/a7b800e)
doc(overview): small reorganization of algebra/number theory ([#5707](https://github.com/leanprover-community/mathlib/pull/5707))
- adds Witt vectors
- adds perfection of a ring
- deduplicates Zariski topology
- moves some items to a new subsection "Number theory"
#### Estimated changes
Modified docs/overview.yaml




## [2021-01-12 19:31:47](https://github.com/leanprover-community/mathlib/commit/c1894c8)
chore(analysis|measure_theory|topology): give tsum notation precedence 67 ([#5709](https://github.com/leanprover-community/mathlib/pull/5709))
This saves us a lot of `()`
In particular, lean no longer thinks that `∑' i, f i = 37` is a tsum of propositions.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/units.lean


Modified src/analysis/p_series.lean


Modified src/analysis/specific_limits.lean
- \+/\- *lemma* tsum_geometric_of_lt_1
- \+/\- *lemma* tsum_geometric_two
- \+/\- *lemma* tsum_geometric_two'
- \+/\- *lemma* tsum_geometric_nnreal
- \+/\- *lemma* ennreal.tsum_geometric
- \+/\- *lemma* tsum_geometric_of_norm_lt_1
- \+/\- *lemma* tsum_geometric_of_abs_lt_1

Modified src/measure_theory/measure_space.lean
- \+/\- *theorem* measure_Union_le

Modified src/measure_theory/outer_measure.lean
- \+/\- *lemma* extend_Union_le_tsum_nat

Modified src/measure_theory/probability_mass_function.lean
- \+/\- *lemma* tsum_coe
- \+/\- *lemma* bind_apply

Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* tsum_eq_zero_of_not_summable
- \+/\- *lemma* has_sum.tsum_eq
- \+/\- *lemma* summable.has_sum_iff
- \+/\- *lemma* tsum_zero
- \+/\- *lemma* tsum_fintype
- \+/\- *lemma* tsum_ite_eq
- \+/\- *lemma* equiv.tsum_eq
- \+/\- *lemma* tsum_add
- \+/\- *lemma* tsum_neg
- \+/\- *lemma* tsum_sub
- \+/\- *lemma* summable.tsum_mul_left
- \+/\- *lemma* tsum_smul
- \+/\- *lemma* tsum_le_tsum
- \+/\- *lemma* tsum_nonneg
- \+/\- *lemma* tsum_nonpos
- \+/\- *lemma* tsum_eq_zero_iff

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* to_nnreal_apply_of_tsum_ne_top
- \+/\- *lemma* summable_to_nnreal_of_tsum_ne_top
- \+/\- *lemma* tsum_sub
- \+/\- *lemma* tendsto_sum_nat_add

Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* coe_tsum
- \+/\- *lemma* tsum_mul_left



## [2021-01-12 19:31:44](https://github.com/leanprover-community/mathlib/commit/0e7a921)
feat(data/buffer/parser/basic): lemmas describing parsers ([#5460](https://github.com/leanprover-community/mathlib/pull/5460))
#### Estimated changes
Created src/data/buffer/parser/basic.lean
- \+ *lemma* exists_eq_right_right
- \+ *lemma* exists_eq_right_right'
- \+ *lemma* ne_iff_lt_iff_le
- \+ *lemma* nat.le_of_sub_eq_pos
- \+ *lemma* fail_iff
- \+ *lemma* success_iff
- \+ *lemma* decorate_errors_fail
- \+ *lemma* decorate_errors_success
- \+ *lemma* decorate_error_fail
- \+ *lemma* decorate_error_success
- \+ *lemma* decorate_errors_eq_done
- \+ *lemma* decorate_error_eq_done
- \+ *lemma* decorate_errors_eq_fail
- \+ *lemma* decorate_error_eq_fail
- \+ *lemma* return_eq_pure
- \+ *lemma* pure_eq_done
- \+ *lemma* pure_ne_fail
- \+ *lemma* bind_eq_bind
- \+ *lemma* bind_eq_done
- \+ *lemma* bind_eq_fail
- \+ *lemma* and_then_eq_bind
- \+ *lemma* and_then_fail
- \+ *lemma* and_then_success
- \+ *lemma* map_eq_done
- \+ *lemma* map_eq_fail
- \+ *lemma* map_const_eq_done
- \+ *lemma* map_const_eq_fail
- \+ *lemma* map_const_rev_eq_done
- \+ *lemma* map_rev_const_eq_fail
- \+ *lemma* orelse_eq_orelse
- \+ *lemma* orelse_eq_done
- \+ *lemma* orelse_eq_fail_eq
- \+ *lemma* orelse_eq_fail_invalid_lt
- \+ *lemma* orelse_eq_fail_of_valid_ne
- \+ *lemma* failure_eq_failure
- \+ *lemma* failure_def
- \+ *lemma* not_failure_eq_done
- \+ *lemma* failure_eq_fail
- \+ *lemma* seq_eq_done
- \+ *lemma* seq_eq_fail
- \+ *lemma* seq_left_eq_done
- \+ *lemma* seq_left_eq_fail
- \+ *lemma* seq_right_eq_done
- \+ *lemma* seq_right_eq_fail
- \+ *lemma* mmap_eq_done
- \+ *lemma* mmap'_eq_done
- \+ *lemma* guard_eq_done
- \+ *lemma* guard_eq_fail
- \+ *lemma* mono_done
- \+ *lemma* mono_fail
- \+ *lemma* pure
- \+ *lemma* bind
- \+ *lemma* and_then
- \+ *lemma* map
- \+ *lemma* seq
- \+ *lemma* mmap
- \+ *lemma* mmap'
- \+ *lemma* failure
- \+ *lemma* guard
- \+ *lemma* orelse
- \+ *lemma* decorate_errors
- \+ *lemma* decorate_error
- \+ *lemma* any_char
- \+ *lemma* sat
- \+ *lemma* eps
- \+ *lemma* ch
- \+ *lemma* char_buf
- \+ *lemma* one_of
- \+ *lemma* one_of'
- \+ *lemma* str
- \+ *lemma* remaining
- \+ *lemma* eof
- \+ *lemma* foldr_core_zero
- \+ *lemma* foldr_core
- \+ *lemma* foldr
- \+ *lemma* foldl_core_zero
- \+ *lemma* foldl_core
- \+ *lemma* foldl
- \+ *lemma* many
- \+ *lemma* many_char
- \+ *lemma* many'
- \+ *lemma* many1
- \+ *lemma* many_char1
- \+ *lemma* sep_by1
- \+ *lemma* sep_by
- \+ *lemma* fix_core
- \+ *lemma* digit
- \+ *lemma* nat
- \+ *lemma* fix
- \+ *lemma* orelse_pure_eq_fail
- \+ *lemma* any_char_eq_done
- \+ *lemma* sat_eq_done
- \+ *lemma* eps_eq_done
- \+ *lemma* ch_eq_done
- \+ *lemma* one_of_eq_done
- \+ *lemma* one_of'_eq_done
- \+ *lemma* remaining_eq_done
- \+ *lemma* eof_eq_done
- \+ *lemma* foldr_core_zero_eq_done
- \+ *lemma* foldr_core_eq_done
- \+ *lemma* foldr_core_zero_eq_fail
- \+ *lemma* foldr_core_succ_eq_fail
- \+ *lemma* foldr_eq_done
- \+ *lemma* foldr_eq_fail_of_valid_at_end
- \+ *lemma* foldr_eq_fail
- \+ *lemma* foldl_core_zero_eq_done
- \+ *lemma* foldl_core_eq_done
- \+ *lemma* foldl_core_zero_eq_fail
- \+ *lemma* foldl_core_succ_eq_fail
- \+ *lemma* foldl_eq_done
- \+ *lemma* foldl_eq_fail
- \+ *lemma* many_eq_done_nil
- \+ *lemma* many_eq_done
- \+ *lemma* many_eq_fail
- \+ *lemma* many_char_eq_done_empty
- \+ *lemma* many_char_eq_done_not_empty
- \+ *lemma* many_char_eq_many_of_to_list
- \+ *lemma* many'_eq_done
- \+ *lemma* many1_ne_done_nil
- \+ *lemma* many1_eq_done
- \+ *lemma* many1_eq_fail
- \+ *lemma* many_char1_ne_empty
- \+ *lemma* many_char1_eq_done
- \+ *lemma* sep_by1_ne_done_nil
- \+ *lemma* sep_by1_eq_done
- \+ *lemma* sep_by_eq_done_nil
- \+ *lemma* fix_core_ne_done_zero
- \+ *lemma* fix_core_eq_done
- \+ *lemma* digit_eq_done
- \+ *def* parse_result.pos
- \+ *def* valid

Modified src/data/string/basic.lean
- \+ *lemma* nil_as_string_eq_empty
- \+ *lemma* to_list_empty
- \+ *lemma* as_string_inv_to_list
- \+ *lemma* to_list_singleton
- \+ *lemma* to_list_nonempty
- \+ *lemma* head_empty
- \+ *lemma* popn_empty
- \+ *lemma* list.to_list_inv_as_string
- \+ *lemma* list.as_string_inj
- \+ *lemma* list.as_string_eq

Modified src/data/string/defs.lean
- \+ *def* head



## [2021-01-12 16:10:51](https://github.com/leanprover-community/mathlib/commit/1025908)
chore(topology/algebra/infinite_sum): speedup has_sum_sum ([#5710](https://github.com/leanprover-community/mathlib/pull/5710))
this lemma was pretty slow, now it is pretty fast
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean




## [2021-01-12 16:10:48](https://github.com/leanprover-community/mathlib/commit/73ba460)
feat(submonoid/basic): subsingleton and nontrivial instances for {add_,}submonoid ([#5690](https://github.com/leanprover-community/mathlib/pull/5690))
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* subsingleton_iff
- \+ *lemma* nontrivial_iff

Modified src/group_theory/submonoid/basic.lean
- \+ *lemma* subsingleton_iff
- \+ *lemma* nontrivial_iff

Modified src/order/bounded_lattice.lean
- \+ *lemma* subsingleton_iff_bot_eq_top



## [2021-01-12 16:10:46](https://github.com/leanprover-community/mathlib/commit/e76fdb9)
docs(undergrad.yaml): analysis updates ([#5675](https://github.com/leanprover-community/mathlib/pull/5675))
Updates to `undergrad.yaml` (including reverting some changes from [#5638](https://github.com/leanprover-community/mathlib/pull/5638), after further discussion), and fix a docstring typo in `measure_theory.interval_integral`.
#### Estimated changes
Modified docs/100.yaml


Modified docs/undergrad.yaml


Modified src/measure_theory/interval_integral.lean




## [2021-01-12 16:10:44](https://github.com/leanprover-community/mathlib/commit/ce6a7eb)
feat(linear_algebra/multilinear_map): Add `range` and `map` ([#5658](https://github.com/leanprover-community/mathlib/pull/5658))
Note that unlike `linear_map`, `range` cannot return a submodule, only a `sub_mul_action`.
We also can't guarantee closure under `smul` unless the map has at least one argument, as there is nothing requiring the multilinear map of no arguments to be zero.
#### Estimated changes
Modified src/linear_algebra/multilinear.lean
- \+ *lemma* map_nonempty
- \+ *def* map
- \+ *def* range



## [2021-01-12 13:08:45](https://github.com/leanprover-community/mathlib/commit/3a3ec6c)
feat(measure_theory): each set has a measurable superset of the same measure ([#5688](https://github.com/leanprover-community/mathlib/pull/5688))
* generalize `outer_measure.exists_is_measurable_superset_of_trim_eq_zero`
  to `outer_measure.exists_is_measurable_superset_eq_trim`;
* generalize `exists_is_measurable_superset_of_null` to
  `exists_is_measurable_superset`;
* define `to_measurable mu s` to be a measurable superset `t ⊇ s`
	with `μ t = μ s`;
* prove `countable_cover_nhds`: in a `second_countable_topology`, if
  `f` sends each point `x` to a neighborhood of `x`, then some
  countable subfamily of neighborhoods `f x` cover the whole space.
* `sigma_finite_of_countable` no longer assumes that all sets `s ∈ S`
  are measurable.
#### Estimated changes
Modified src/data/set/countable.lean
- \+ *lemma* exists_seq_supr_eq_top_iff_countable
- \+ *lemma* exists_seq_cover_iff_countable

Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/measure_space.lean
- \+ *lemma* exists_is_measurable_superset
- \+ *lemma* subset_to_measurable
- \+ *lemma* is_measurable_to_measurable
- \+ *lemma* measure_to_measurable
- \+ *def* to_measurable

Modified src/measure_theory/outer_measure.lean
- \+ *lemma* exists_is_measurable_superset_eq_trim

Modified src/topology/bases.lean
- \+ *lemma* countable_cover_nhds



## [2021-01-12 13:08:41](https://github.com/leanprover-community/mathlib/commit/2671068)
feat(data/set/intervals): add 2 Icc ssubset lemmas ([#5617](https://github.com/leanprover-community/mathlib/pull/5617))
Add two strict subset lemmas for Icc, discussed in https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Icc_ssubset_Icc.
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* Icc_ssubset_Icc_left
- \+ *lemma* Icc_ssubset_Icc_right



## [2021-01-12 08:26:45](https://github.com/leanprover-community/mathlib/commit/cd7a8a1)
chore(category_theory/limits): move constructions folder ([#5681](https://github.com/leanprover-community/mathlib/pull/5681))
As mentioned here: https://github.com/leanprover-community/mathlib/pull/5516#issuecomment-753450199
The linter is giving new errors, so I might as well fix them in this PR.
#### Estimated changes
Modified src/category_theory/abelian/basic.lean


Renamed src/category_theory/limits/shapes/constructions/binary_products.lean to src/category_theory/limits/constructions/binary_products.lean


Renamed src/category_theory/limits/shapes/constructions/equalizers.lean to src/category_theory/limits/constructions/equalizers.lean


Renamed src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean to src/category_theory/limits/constructions/limits_of_products_and_equalizers.lean


Renamed src/category_theory/limits/shapes/constructions/over/connected.lean to src/category_theory/limits/constructions/over/connected.lean
- \+/\- *def* raised_cone_is_limit

Renamed src/category_theory/limits/shapes/constructions/over/default.lean to src/category_theory/limits/constructions/over/default.lean


Renamed src/category_theory/limits/shapes/constructions/over/products.lean to src/category_theory/limits/constructions/over/products.lean
- \+/\- *lemma* has_over_limit_discrete_of_wide_pullback_limit
- \+/\- *lemma* over_product_of_wide_pullback
- \+/\- *def* wide_pullback_diagram_of_diagram_over
- \+/\- *def* cones_equiv_unit_iso
- \+/\- *def* cones_equiv_counit_iso
- \+/\- *def* cones_equiv

Renamed src/category_theory/limits/shapes/constructions/pullbacks.lean to src/category_theory/limits/constructions/pullbacks.lean


Modified src/order/category/omega_complete_partial_order.lean




## [2021-01-12 08:26:43](https://github.com/leanprover-community/mathlib/commit/be75005)
fix(linear_algebra/tensor_product): Remove the priorities from the module structure ([#5667](https://github.com/leanprover-community/mathlib/pull/5667))
These were added originally so that `semimodule'` was lower priority than `semimodule`, as the `semimodule'` instance took too long to resolve.
However, this happens automatically anyway, since the former appears before the latter - the simple existence of the `semimodule` shortcut instances was enough to solve the long typeclass-resolution paths, their priority was a red herring.
The only effect of these attributes was to cause these instances to not take priority over `add_comm_monoid.nat_semimodule`, which was neither intended nor desirable.
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean




## [2021-01-12 07:23:33](https://github.com/leanprover-community/mathlib/commit/cd0d8c0)
chore(category_theory/limits/over): generalise, golf and document over limits ([#5674](https://github.com/leanprover-community/mathlib/pull/5674))
- Show that the forgetful functor `over X => C` creates colimits, generalising what was already there
- Golf the proofs using this new instance
- Add module doc
and duals of the above
#### Estimated changes
Modified src/category_theory/limits/over.lean
- \- *def* colimit
- \- *def* forget_colimit_is_colimit
- \- *def* limit
- \- *def* forget_limit_is_limit



## [2021-01-12 02:03:22](https://github.com/leanprover-community/mathlib/commit/9f9f85e)
chore(scripts): update nolints.txt ([#5705](https://github.com/leanprover-community/mathlib/pull/5705))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-11 21:22:16](https://github.com/leanprover-community/mathlib/commit/049f16a)
feat(measure_theory/pi): `ae_eq` lemmas about intervals in `Π i, α i` ([#5633](https://github.com/leanprover-community/mathlib/pull/5633))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* pi_inter_distrib

Modified src/data/set/lattice.lean
- \+/\- *lemma* pi_def
- \+ *lemma* pi_diff_pi_subset

Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/pi.lean
- \+/\- *lemma* pi_pi
- \+/\- *lemma* pi_eval_preimage_null
- \+/\- *lemma* pi_hyperplane
- \+ *lemma* ae_eval_ne
- \+ *lemma* tendsto_eval_ae_ae
- \+ *lemma* ae_pi_le_infi_comap
- \+ *lemma* ae_eq_pi
- \+ *lemma* ae_le_pi
- \+ *lemma* ae_le_set_pi
- \+ *lemma* ae_eq_set_pi
- \+ *lemma* pi_Iio_ae_eq_pi_Iic
- \+ *lemma* pi_Ioi_ae_eq_pi_Ici
- \+ *lemma* univ_pi_Iio_ae_eq_Iic
- \+ *lemma* univ_pi_Ioi_ae_eq_Ici
- \+ *lemma* pi_Ioo_ae_eq_pi_Icc
- \+ *lemma* univ_pi_Ioo_ae_eq_Icc
- \+ *lemma* pi_Ioc_ae_eq_pi_Icc
- \+ *lemma* univ_pi_Ioc_ae_eq_Icc
- \+ *lemma* pi_Ico_ae_eq_pi_Icc
- \+ *lemma* univ_pi_Ico_ae_eq_Icc
- \+ *lemma* pi_has_no_atoms



## [2021-01-11 10:10:45](https://github.com/leanprover-community/mathlib/commit/b537cc0)
feat(algebra/splitting_field): Restrict to splitting field ([#5562](https://github.com/leanprover-community/mathlib/pull/5562))
Restrict an alg_hom or alg_equiv to an is_splitting_field.
#### Estimated changes
Modified src/field_theory/splitting_field.lean
- \+ *lemma* is_splitting_field.range_to_alg_hom
- \+ *lemma* alg_hom.restrict_is_splitting_field_commutes
- \+ *lemma* alg_hom.restrict_is_splitting_field_comp
- \+ *lemma* alg_equiv.restrict_is_splitting_field_commutes
- \+ *lemma* alg_equiv.restrict_is_splitting_field_trans
- \+ *def* alg_hom.restrict_is_splitting_field_aux
- \+ *def* alg_hom.restrict_is_splitting_field
- \+ *def* alg_equiv.restrict_is_splitting_field
- \+ *def* alg_equiv.restict_is_splitting_field_hom



## [2021-01-11 01:59:51](https://github.com/leanprover-community/mathlib/commit/c112ad0)
chore(scripts): update nolints.txt ([#5699](https://github.com/leanprover-community/mathlib/pull/5699))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-10 22:38:07](https://github.com/leanprover-community/mathlib/commit/08800bb)
feat(analysis/special/functions/trigonometric): complex trig and some even/odd lemmas ([#5404](https://github.com/leanprover-community/mathlib/pull/5404))
Complex (and some real) trigonometry lemmas, parity propositions, and some field algebra.
#### Estimated changes
Modified src/algebra/field.lean
- \+ *lemma* same_add_div
- \+ *lemma* one_add_div
- \+ *lemma* div_add_same
- \+ *lemma* div_add_one
- \+ *lemma* same_sub_div
- \+ *lemma* one_sub_div
- \+ *lemma* div_sub_same
- \+ *lemma* div_sub_one

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* eq_of_norm_sub_le_zero

Modified src/analysis/special_functions/trigonometric.lean
- \+/\- *lemma* pi_ne_zero
- \+ *lemma* sin_ne_zero_iff
- \+/\- *lemma* exp_pi_mul_I
- \+ *lemma* sin_eq_zero_iff_cos_eq
- \+ *lemma* tan_eq_zero_iff
- \+ *lemma* tan_ne_zero_iff
- \+ *lemma* tan_int_mul_pi_div_two
- \+ *lemma* tan_int_mul_pi
- \+ *lemma* tan_add
- \+ *lemma* tan_add'
- \+ *lemma* tan_two_mul
- \+ *lemma* tan_add_mul_I
- \+ *lemma* tan_eq

Modified src/data/complex/exponential.lean
- \+ *lemma* tanh_mul_I
- \+ *lemma* cos_mul_I
- \+ *lemma* sin_mul_I
- \+ *lemma* tan_mul_I
- \+ *lemma* sin_add_mul_I
- \+ *lemma* sin_eq
- \+ *lemma* cos_add_mul_I
- \+ *lemma* cos_eq

Modified src/data/int/parity.lean
- \+ *lemma* not_odd_iff
- \+ *lemma* even_iff_not_odd
- \+ *lemma* even_or_odd
- \+ *lemma* even_or_odd'
- \+ *lemma* even_xor_odd
- \+ *lemma* even_xor_odd'

Modified src/data/nat/parity.lean
- \+ *lemma* not_odd_iff
- \+ *lemma* even_iff_not_odd
- \+ *lemma* even_or_odd'
- \+ *lemma* even_xor_odd
- \+ *lemma* even_xor_odd'



## [2021-01-10 19:12:03](https://github.com/leanprover-community/mathlib/commit/cc6f039)
feat(equiv|set|topology): various additions ([#5656](https://github.com/leanprover-community/mathlib/pull/5656))
define sigma_compact_space
update module doc for topology/subset_properties
define shearing
some lemmas in set.basic, equiv.mul_add and topology.instances.ennreal
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* prod_shear

Modified src/data/equiv/mul_add.lean
- \+ *lemma* mul_left_symm_apply
- \+ *lemma* mul_right_symm_apply

Modified src/data/set/basic.lean
- \+ *lemma* prod_preimage_left
- \+ *lemma* prod_preimage_right
- \+ *lemma* mk_preimage_prod
- \+ *lemma* mk_preimage_prod_left_fn_eq_if
- \+ *lemma* mk_preimage_prod_right_fn_eq_if

Modified src/topology/algebra/group.lean
- \+ *lemma* homeomorph.shear_mul_right_coe
- \+ *lemma* homeomorph.shear_mul_right_symm_coe

Modified src/topology/instances/ennreal.lean
- \+ *lemma* supr_eq_zero

Modified src/topology/subset_properties.lean
- \+ *lemma* is_compact_compact_covering
- \+ *lemma* Union_compact_covering
- \+ *def* compact_covering



## [2021-01-10 19:12:01](https://github.com/leanprover-community/mathlib/commit/62c1912)
chore(measure_theory/set_integral): use weaker assumptions here and there ([#5647](https://github.com/leanprover-community/mathlib/pull/5647))
* use `ae_measurable f (μ.restrict s)` in more lemmas;
* introduce `measurable_at_filter` and use it.
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* measure_integral_sub_linear_is_o_of_tendsto_ae
- \+/\- *lemma* integral_has_fderiv_at_of_tendsto_ae
- \+/\- *lemma* integral_has_fderiv_at
- \+/\- *lemma* fderiv_integral_of_tendsto_ae
- \+/\- *lemma* fderiv_integral

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* subsingleton.is_measurable
- \+/\- *lemma* subsingleton.measurable
- \+ *lemma* eventually.exists_measurable_mem_of_lift'

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_inter_eq_zero_of_restrict
- \+ *lemma* ae_zero
- \+ *lemma* ae_imp_of_ae_restrict
- \+ *lemma* le_ae_restrict
- \+ *lemma* subsingleton.ae_measurable
- \+ *lemma* ae_measurable_zero
- \+ *lemma* mono_set
- \+ *lemma* ae_mem_imp_eq_mk
- \+ *lemma* ae_inf_principal_eq_mk

Modified src/measure_theory/set_integral.lean
- \+ *lemma* measurable_at_bot
- \+ *lemma* ae_measurable.measurable_at_filter_of_mem
- \+/\- *lemma* measure.finite_at_filter.integrable_at_filter
- \+/\- *lemma* measure.finite_at_filter.integrable_at_filter_of_tendsto_ae
- \+/\- *lemma* measure.finite_at_filter.integrable_at_filter_of_tendsto
- \+ *lemma* set_integral_congr_ae
- \+ *lemma* set_integral_congr
- \+ *lemma* continuous_within_at.integral_sub_linear_is_o_ae
- \+/\- *lemma* continuous_at.integral_sub_linear_is_o_ae
- \+ *lemma* continuous_on.integrable_at_nhds_within
- \+ *lemma* continuous_on.integral_sub_linear_is_o_ae
- \+ *def* measurable_at_filter



## [2021-01-10 17:59:16](https://github.com/leanprover-community/mathlib/commit/3e7efd4)
feat(field_theory/separable): Remove hypothesis in irreducible.separable ([#5687](https://github.com/leanprover-community/mathlib/pull/5687))
An irreducible polynomial is nonzero, so this hypothesis is unnecessary.
#### Estimated changes
Modified src/field_theory/separable.lean




## [2021-01-10 17:59:14](https://github.com/leanprover-community/mathlib/commit/b72811f)
feat(order/complete_well_founded): characterise well-foundedness for complete lattices ([#5575](https://github.com/leanprover-community/mathlib/pull/5575))
#### Estimated changes
Created src/order/complete_well_founded.lean
- \+ *lemma* well_founded.is_Sup_finite_compact
- \+ *lemma* is_Sup_finite_compact.is_sup_closed_compact
- \+ *lemma* is_sup_closed_compact.well_founded
- \+ *lemma* well_founded_characterisations
- \+ *lemma* well_founded_iff_is_Sup_finite_compact
- \+ *lemma* is_Sup_finite_compact_iff_is_sup_closed_compact
- \+ *lemma* is_sup_closed_compact_iff_well_founded
- \+ *def* is_sup_closed_compact
- \+ *def* is_Sup_finite_compact



## [2021-01-10 14:47:11](https://github.com/leanprover-community/mathlib/commit/0d9cb85)
chore(order/filter): a few more lemmas about `eventually` and set operations ([#5686](https://github.com/leanprover-community/mathlib/pull/5686))
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *theorem* union_diff_left
- \+/\- *theorem* union_diff_right
- \+/\- *theorem* inter_diff_self
- \+/\- *theorem* inter_union_diff
- \+/\- *theorem* inter_union_compl

Modified src/data/set/disjointed.lean
- \+ *theorem* pairwise.mono

Modified src/order/filter/basic.lean
- \+ *lemma* eventually_le.inter
- \+ *lemma* eventually_le.union
- \+ *lemma* eventually_le.compl
- \+ *lemma* eventually_le.diff

Modified src/order/filter/countable_Inter.lean
- \+ *lemma* eventually_le.countable_Union
- \+ *lemma* eventually_eq.countable_Union
- \+ *lemma* eventually_le.countable_bUnion
- \+ *lemma* eventually_eq.countable_bUnion
- \+ *lemma* eventually_le.countable_Inter
- \+ *lemma* eventually_eq.countable_Inter
- \+ *lemma* eventually_le.countable_bInter
- \+ *lemma* eventually_eq.countable_bInter



## [2021-01-10 14:47:09](https://github.com/leanprover-community/mathlib/commit/b0c35d1)
chore(order/filter/basic): a few `simp` lemmas ([#5685](https://github.com/leanprover-community/mathlib/pull/5685))
### Changes in `order/filter/basic`
* add `filter.inter_mem_sets_iff`;
* rename `filter.Inter_mem_sets` to `filter.bInter_mem_sets`, make it
  an `iff` `[simp]` lemma;
* add a version `filter.bInter_finset_mem_sets` with a protected alias
  `finset.Inter_mem_sets`;
* rename `filter.sInter_mem_sets_of_finite` to
  `filter.sInter_mem_sets`, make it an `iff` `[simp]` lemma;
* rename `filter.Inter_mem_sets_of_fintype` to
  `filter.Inter_mem_sets`, make it an `iff` `[simp]` lemma
* add `eventually` versions of the `*Inter_mem_sets` lemmas.
### New `@[mono]` attributes
* `set.union_subset_union` and `set.inter_subset_inter` instead of
  `monotone_union` and `monotone_inter`; `mono*` failed to make a
  progress with `s ∩ t ⊆ s' ∩ t'` goal.
* `set.image2_subset`
* `closure_mono`
#### Estimated changes
Modified src/dynamics/omega_limit.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean
- \+ *lemma* inter_mem_sets_iff
- \+ *lemma* bInter_mem_sets
- \+ *lemma* bInter_finset_mem_sets
- \+ *lemma* sInter_mem_sets
- \+/\- *lemma* Inter_mem_sets
- \+ *lemma* eventually_all
- \+ *lemma* eventually_all_finite
- \+ *lemma* eventually_all_finset
- \- *lemma* sInter_mem_sets_of_finite
- \- *lemma* Inter_mem_sets_of_fintype

Modified src/tactic/monotonicity/lemmas.lean


Modified src/topology/basic.lean
- \+/\- *lemma* closure_mono

Modified src/topology/constructions.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean




## [2021-01-10 09:02:16](https://github.com/leanprover-community/mathlib/commit/1c4f2ae)
feat(data/equiv/basic, logic/embedding): swap commutes with injective functions ([#5636](https://github.com/leanprover-community/mathlib/pull/5636))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* function.injective.swap_apply
- \+ *lemma* function.injective.swap_comp

Modified src/logic/embedding.lean
- \+ *lemma* swap_apply
- \+ *lemma* swap_comp



## [2021-01-10 01:57:53](https://github.com/leanprover-community/mathlib/commit/a28602a)
chore(scripts): update nolints.txt ([#5682](https://github.com/leanprover-community/mathlib/pull/5682))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-09 16:50:50](https://github.com/leanprover-community/mathlib/commit/f60c184)
feat(algebra/lie/basic): Lie ideal operations are linear spans ([#5676](https://github.com/leanprover-community/mathlib/pull/5676))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* mem_coe
- \+ *lemma* submodule_span_le_lie_span
- \+ *lemma* lie_span_mono
- \+ *lemma* lie_ideal_oper_eq_linear_span



## [2021-01-09 15:06:06](https://github.com/leanprover-community/mathlib/commit/5faf34c)
feat(measure_theory/lp_space): add more lemmas about snorm ([#5644](https://github.com/leanprover-community/mathlib/pull/5644))
#### Estimated changes
Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm_exponent_zero
- \+ *lemma* zero_mem_ℒp_of_pos
- \+ *lemma* zero_mem_ℒp_of_nonneg
- \+ *lemma* snorm_zero'
- \+ *lemma* snorm_const
- \+ *lemma* snorm_const'
- \+ *lemma* snorm_const_of_probability_measure
- \+ *lemma* mem_ℒp_const
- \+ *lemma* mem_ℒp_const_of_nonneg
- \+ *lemma* mem_ℒp_const_of_ne_zero
- \+ *lemma* snorm_congr_ae
- \+ *lemma* mem_ℒp.ae_eq
- \+ *lemma* mem_ℒp_congr_ae
- \+/\- *lemma* snorm_eq_zero_of_ae_zero
- \+/\- *lemma* snorm_eq_zero_of_ae_zero'
- \+/\- *lemma* ae_eq_zero_of_snorm_eq_zero
- \+/\- *lemma* snorm_eq_zero_iff
- \+/\- *lemma* snorm_neg
- \+ *lemma* mem_ℒp.sub
- \+ *lemma* snorm_const_smul
- \- *lemma* zero_mem_ℒp



## [2021-01-09 12:23:44](https://github.com/leanprover-community/mathlib/commit/fdec90a)
chore(data/set/lattice): add a few simp lemmas ([#5671](https://github.com/leanprover-community/mathlib/pull/5671))
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* nonempty.of_sUnion
- \+ *lemma* nonempty.of_sUnion_eq_univ
- \+/\- *lemma* Union_empty
- \+/\- *lemma* Inter_univ
- \+ *lemma* Union_eq_empty
- \+ *lemma* Inter_eq_univ
- \+ *lemma* nonempty_Union
- \+ *theorem* sUnion_eq_empty
- \+ *theorem* sInter_eq_univ
- \+ *theorem* nonempty_sUnion



## [2021-01-09 12:23:42](https://github.com/leanprover-community/mathlib/commit/3166f4e)
feat(topology/separation, topology/metric_space/basic): add lemmas on discrete subsets of a topological space ([#5523](https://github.com/leanprover-community/mathlib/pull/5523))
These lemmas form part of a simplification of the proofs of [#5361](https://github.com/leanprover-community/mathlib/pull/5361).
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* exists_ball_inter_eq_singleton_of_mem_discrete
- \+ *lemma* exists_closed_ball_inter_eq_singleton_of_discrete

Modified src/topology/separation.lean
- \+ *lemma* singleton_mem_nhds_within_of_mem_discrete
- \+ *lemma* nhds_within_of_mem_discrete
- \+ *lemma* filter.has_basis.exists_inter_eq_singleton_of_mem_discrete
- \+ *lemma* nhds_inter_eq_singleton_of_mem_discrete
- \+ *lemma* disjoint_nhds_within_of_mem_discrete



## [2021-01-09 10:41:15](https://github.com/leanprover-community/mathlib/commit/a161256)
feat(topology/algebra/ordered): prove `tendsto.Icc` for pi-types ([#5639](https://github.com/leanprover-community/mathlib/pull/5639))
#### Estimated changes
Modified src/order/filter/interval.lean


Modified src/order/filter/lift.lean
- \+ *lemma* tendsto_lift
- \+ *lemma* tendsto_lift'
- \+ *lemma* lift'_infi_powerset

Modified src/topology/algebra/ordered.lean




## [2021-01-09 03:54:42](https://github.com/leanprover-community/mathlib/commit/faf1a98)
chore(scripts): update nolints.txt ([#5673](https://github.com/leanprover-community/mathlib/pull/5673))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-09 00:41:04](https://github.com/leanprover-community/mathlib/commit/1294500)
feat(category_theory/limits): preserving pullbacks ([#5668](https://github.com/leanprover-community/mathlib/pull/5668))
This touches multiple files but it's essentially the same thing as all my other PRs for preserving limits of special shapes - I can split it up if you'd like but hopefully this is alright?
#### Estimated changes
Modified src/category_theory/abelian/non_preadditive.lean


Created src/category_theory/limits/preserves/shapes/pullbacks.lean
- \+ *lemma* preserves_pullback.iso_hom
- \+ *def* is_limit_map_cone_pullback_cone_equiv
- \+ *def* is_limit_pullback_cone_map_of_is_limit
- \+ *def* is_limit_of_is_limit_pullback_cone_map
- \+ *def* is_limit_of_has_pullback_of_preserves_limit
- \+ *def* preserves_pullback.of_iso_comparison
- \+ *def* preserves_pullback.iso

Modified src/category_theory/limits/shapes/constructions/pullbacks.lean


Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* pullback_comparison_comp_fst
- \+ *lemma* pullback_comparison_comp_snd
- \+ *lemma* map_lift_pullback_comparison
- \+/\- *def* is_limit.mk
- \+/\- *def* is_colimit.mk
- \+ *def* pullback_is_pullback
- \+ *def* pullback_comparison



## [2021-01-09 00:41:01](https://github.com/leanprover-community/mathlib/commit/ce34ae6)
chore(linear_algebra/alternating): golf a proof ([#5666](https://github.com/leanprover-community/mathlib/pull/5666))
`sign_mul` seems to have been marked `simp` recently, making it not necessary to include in `simp` calls.
#### Estimated changes
Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/determinant.lean




## [2021-01-09 00:40:59](https://github.com/leanprover-community/mathlib/commit/0cd70d0)
chore(algebra/group/hom): fix additive version of docstring ([#5660](https://github.com/leanprover-community/mathlib/pull/5660))
#### Estimated changes
Modified src/algebra/group/hom.lean


Modified src/deprecated/group.lean




## [2021-01-08 21:30:46](https://github.com/leanprover-community/mathlib/commit/2b5344f)
chore(analysis/special_functions/trigonometric): adding `@[pp_nodot]` to complex.log ([#5670](https://github.com/leanprover-community/mathlib/pull/5670))
Added `@[pp_nodot]` to complex.log
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean




## [2021-01-08 21:30:44](https://github.com/leanprover-community/mathlib/commit/aab5994)
feat(data/finset/intervals, data/set/intervals/basic): intersection of finset.Ico, union of intervals for sets and finsets ([#5410](https://github.com/leanprover-community/mathlib/pull/5410))
#### Estimated changes
Modified src/data/finset/intervals.lean
- \+ *lemma* coe_eq_Ico
- \+ *lemma* union'
- \+ *lemma* union
- \+ *lemma* inter

Modified src/data/list/intervals.lean


Modified src/data/set/intervals/basic.lean
- \+ *lemma* Ioo_union_Ioi'
- \+ *lemma* Ioo_union_Ioi
- \+ *lemma* Ico_union_Ici'
- \+ *lemma* Ico_union_Ici
- \+ *lemma* Ioc_union_Ioi'
- \+ *lemma* Ioc_union_Ioi
- \+ *lemma* Icc_union_Ici'
- \+ *lemma* Icc_union_Ici
- \+ *lemma* Iio_union_Ico'
- \+ *lemma* Iio_union_Ico
- \+ *lemma* Iic_union_Ioc'
- \+ *lemma* Iic_union_Ioc
- \+ *lemma* Iio_union_Ioo'
- \+ *lemma* Iio_union_Ioo
- \+ *lemma* Iic_union_Icc'
- \+ *lemma* Iic_union_Icc
- \+ *lemma* Ico_union_Ico'
- \+ *lemma* Ico_union_Ico
- \+ *lemma* Ioc_union_Ioc'
- \+/\- *lemma* Ioc_union_Ioc
- \+ *lemma* Icc_union_Icc'
- \+ *lemma* Icc_union_Icc
- \+ *lemma* Ioo_union_Ioo'
- \+ *lemma* Ioo_union_Ioo



## [2021-01-08 17:23:08](https://github.com/leanprover-community/mathlib/commit/d935760)
feat(algebra/linear_ordered_comm_group_with_zero): Add linear_ordered_comm_monoid_with_zero and an instance for nat ([#5645](https://github.com/leanprover-community/mathlib/pull/5645))
This generalizes a lot of statements about `linear_ordered_comm_group_with_zero` to `linear_ordered_comm_monoid_with_zero`.
#### Estimated changes
Modified src/algebra/linear_ordered_comm_group_with_zero.lean
- \+/\- *lemma* ne_zero_of_lt
- \+/\- *lemma* zero_lt_one''

Modified src/algebra/ordered_monoid.lean


Modified src/data/nat/basic.lean




## [2021-01-08 17:23:06](https://github.com/leanprover-community/mathlib/commit/2bde21d)
feat(geometry/manifold/times_cont_mdiff): API for checking `times_cont_mdiff` ([#5631](https://github.com/leanprover-community/mathlib/pull/5631))
Two families of lemmas:
- to be `times_cont_mdiff`, it suffices to be `times_cont_mdiff` after postcomposition with any chart of the target
- projection notation to go from `times_cont_diff` (in a vector space) to `times_cont_mdiff`
#### Estimated changes
Modified src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* times_cont_mdiff_within_at_iff_target
- \+ *lemma* smooth_within_at_iff_target
- \+ *lemma* times_cont_mdiff_on_iff_target
- \+ *lemma* smooth_on_iff_target
- \+ *lemma* times_cont_mdiff_iff_target
- \+ *lemma* smooth_iff_target
- \+ *lemma* times_cont_diff_within_at.times_cont_mdiff_within_at
- \+ *lemma* times_cont_diff_at.times_cont_mdiff_at
- \+ *lemma* times_cont_diff_on.times_cont_mdiff_on
- \+ *lemma* times_cont_diff.times_cont_mdiff



## [2021-01-08 17:23:03](https://github.com/leanprover-community/mathlib/commit/bd9b03f)
feat(category_theory/closed): Frobenius reciprocity of cartesian closed categories ([#5624](https://github.com/leanprover-community/mathlib/pull/5624))
A re-do of [#4929](https://github.com/leanprover-community/mathlib/pull/4929). 
Re-defines the exponential comparison morphism (now as a natural transformation rather than a morphism with a naturality prop), and defines the Frobenius reciprocity morphism for an adjoint. In the case where the functor has a left adjoint, gives a sufficient condition for it to be cartesian closed, and a sufficient condition for a functor whose left adjoint preserves binary products to be cartesian closed (but doesn't show the necessity of this).
- [x] depends on: [#5623](https://github.com/leanprover-community/mathlib/pull/5623)
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean
- \- *lemma* exp_comparison_natural_left
- \- *lemma* exp_comparison_natural_right
- \- *def* exp_comparison

Created src/category_theory/closed/functor.lean
- \+ *lemma* exp_comparison_ev
- \+ *lemma* coev_exp_comparison
- \+ *lemma* uncurry_exp_comparison
- \+ *lemma* exp_comparison_whisker_left
- \+ *lemma* frobenius_morphism_mate
- \+ *def* frobenius_morphism
- \+ *def* exp_comparison
- \+ *def* frobenius_morphism_iso_of_exp_comparison_iso
- \+ *def* exp_comparison_iso_of_frobenius_morphism_iso
- \+ *def* cartesian_closed_functor_of_left_adjoint_preserves_binary_products

Modified src/category_theory/limits/shapes/binary_products.lean




## [2021-01-08 16:06:43](https://github.com/leanprover-community/mathlib/commit/0d7ca98)
feat(measure_theory/measure_space): ae_measurable and measurable are equivalent for complete measures ([#5643](https://github.com/leanprover-community/mathlib/pull/5643))
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* measurable.ae_eq
- \+ *lemma* ae_measurable_iff_measurable



## [2021-01-08 14:20:37](https://github.com/leanprover-community/mathlib/commit/9f066f1)
refactor(linear_algebra/alternating): Use unapplied maps when possible ([#5648](https://github.com/leanprover-community/mathlib/pull/5648))
Notably, this removes the need for a proof of `map_add` and `map_smul` in `def alternatization`, as the result is now already bundled with these proofs.
This also:
* Replaces `equiv.perm.sign p` with `p.sign` for brevity
* Makes `linear_map.comp_alternating_map` an `add_monoid_hom`
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *lemma* coe_dom_dom_congr
- \+ *lemma* alternatization_def
- \+/\- *def* comp_alternating_map



## [2021-01-08 09:47:21](https://github.com/leanprover-community/mathlib/commit/795d5ab)
chore(algebra/ordered_monoid): rename lemmas ([#5657](https://github.com/leanprover-community/mathlib/pull/5657))
I wanted to add the alias `pos_iff_ne_zero` for `zero_lt_iff_ne_zero`, but then I saw a note already in the library to do this renaming. So I went ahead.
`le_zero_iff_eq` -> `nonpos_iff_eq_zero`
`zero_lt_iff_ne_zero` -> `pos_iff_ne_zero`
`le_one_iff_eq` -> `le_one_iff_eq_one`
`measure.le_zero_iff_eq_zero'` -> `measure.nonpos_iff_eq_zero'`
There were various specific types that had their own custom `pos_iff_ne_zero`-lemma, which caused nameclashes. Therefore:
* remove `nat.pos_iff_ne_zero`
* Prove that `cardinal` forms a `canonically_ordered_semiring`, remove various special case lemmas
* There were lemmas `cardinal.le_add_[left|right]`. Generalized them to arbitrary canonically_ordered_monoids and renamed them to `self_le_add_[left|right]` (to avoid name clashes)
* I did not provide a canonically_ordered_monoid class for ordinal, since that requires quite some work (it's true, right?)
* `protect` various lemmas in `cardinal` and `ordinal` to avoid name clashes.
#### Estimated changes
Modified archive/imo/imo1988_q6.lean


Modified src/algebra/archimedean.lean


Modified src/algebra/char_p/basic.lean


Modified src/algebra/group_with_zero/power.lean


Modified src/algebra/invertible.lean


Modified src/algebra/ordered_monoid.lean
- \+ *lemma* self_le_mul_right
- \+ *lemma* self_le_mul_left
- \+ *lemma* le_one_iff_eq_one
- \+/\- *lemma* one_lt_iff_ne_one
- \- *lemma* le_one_iff_eq

Modified src/algebra/ordered_ring.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/convex/integral.lean


Modified src/analysis/p_series.lean


Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/combinatorics/composition.lean


Modified src/data/complex/exponential.lean


Modified src/data/finset/basic.lean


Modified src/data/list/basic.lean


Modified src/data/mv_polynomial/basic.lean


Modified src/data/nat/basic.lean
- \- *theorem* pos_iff_ne_zero

Modified src/data/nat/cast.lean


Modified src/data/nat/digits.lean


Modified src/data/nat/fib.lean


Modified src/data/nat/prime.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/pnat/basic.lean


Modified src/data/polynomial/degree/definitions.lean


Modified src/data/polynomial/degree/trailing_degree.lean


Modified src/data/polynomial/reverse.lean


Modified src/data/rat/floor.lean


Modified src/data/rat/sqrt.lean


Modified src/data/real/cardinality.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/nnreal.lean


Modified src/data/zmod/basic.lean


Modified src/field_theory/separable.lean


Modified src/group_theory/order_of_element.lean


Modified src/linear_algebra/dimension.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/content.lean


Modified src/measure_theory/haar_measure.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measure_space.lean
- \+ *lemma* nonpos_iff_eq_zero'
- \- *lemma* le_zero_iff_eq'

Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/simple_func_dense.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/int/basic.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean


Modified src/set_theory/cardinal.lean
- \+/\- *lemma* zero_power_le
- \+/\- *theorem* zero_lt_one
- \- *theorem* zero_le
- \- *theorem* le_zero
- \- *theorem* pos_iff_ne_zero
- \- *theorem* add_le_add
- \- *theorem* add_le_add_left
- \- *theorem* add_le_add_right
- \- *theorem* le_add_right
- \- *theorem* le_add_left
- \- *theorem* mul_le_mul
- \- *theorem* mul_le_mul_left
- \- *theorem* mul_le_mul_right
- \- *theorem* le_iff_exists_add

Modified src/set_theory/cardinal_ordinal.lean


Modified src/set_theory/cofinality.lean


Modified src/set_theory/game/state.lean


Modified src/set_theory/ordinal.lean
- \- *theorem* zero_le
- \- *theorem* le_zero
- \- *theorem* pos_iff_ne_zero

Modified src/set_theory/ordinal_arithmetic.lean


Modified src/set_theory/ordinal_notation.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/antilipschitz.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified test/library_search/nat.lean




## [2021-01-08 07:46:54](https://github.com/leanprover-community/mathlib/commit/611bc86)
feat(measure_theory/borel_space): locally finite measure is sigma finite ([#5634](https://github.com/leanprover-community/mathlib/pull/5634))
I forgot to add this to [#5604](https://github.com/leanprover-community/mathlib/pull/5604)
#### Estimated changes
Modified src/measure_theory/borel_space.lean




## [2021-01-08 05:13:37](https://github.com/leanprover-community/mathlib/commit/efdcab1)
refactor(algebra/module/basic): Clean up all the nat/int semimodule definitions ([#5654](https://github.com/leanprover-community/mathlib/pull/5654))
These were named inconsistently, and lots of proof was duplicated.
The name changes are largely making the API for `nsmul` consistent with the one for `gsmul`:
* For `ℕ`:
  * Replaces `nat.smul_def : n • x = n •ℕ x` with `nsmul_def : n •ℕ x = n • x`
  * Renames `semimodule.nsmul_eq_smul : n •ℕ b = (n : R) • b` to `nsmul_eq_smul_cast`
  * Removes `semimodule.smul_eq_smul : n • b = (n : R) • b`
  * Adds `nsmul_eq_smul : n •ℕ b = n • b` (this is different from `nsmul_def` as described in the docstring)
  * Renames the instances to be named more consistently and all live under `add_comm_monoid.nat_*`
* For `ℤ`:
  * Renames `gsmul_eq_smul : n •ℤ x = n • x` to `gsmul_def`
  * Renames `module.gsmul_eq_smul : n •ℤ x = n • x` to `gsmul_eq_smul`
  * Renames `module.gsmul_eq_smul_cast` to `gsmul_eq_smul_cast`
  * Renames the instances to be named more consistently and all live under `add_comm_group.int_*`
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *lemma* nsmul_def
- \+ *lemma* nsmul_eq_smul_cast
- \+ *lemma* nsmul_eq_smul
- \+ *lemma* gsmul_def
- \+ *lemma* gsmul_eq_smul_cast
- \+/\- *lemma* gsmul_eq_smul
- \+/\- *lemma* smul_nat_eq_zero
- \+/\- *lemma* eq_zero_of_smul_two_eq_zero
- \- *lemma* semimodule.smul_eq_smul
- \- *lemma* semimodule.nsmul_eq_smul
- \- *lemma* nat.smul_def
- \- *lemma* module.gsmul_eq_smul_cast
- \- *lemma* module.gsmul_eq_smul
- \+ *def* add_comm_monoid.nat_semimodule
- \+ *def* add_comm_group.int_module
- \- *def* nat_semimodule
- \- *def* int_module

Modified src/linear_algebra/alternating.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/representation_theory/maschke.lean




## [2021-01-08 03:36:08](https://github.com/leanprover-community/mathlib/commit/d89464d)
feat(topology/algebra): add additive/multiplicative instances ([#5662](https://github.com/leanprover-community/mathlib/pull/5662))
#### Estimated changes
Modified src/topology/algebra/group.lean


Modified src/topology/algebra/monoid.lean




## [2021-01-08 02:05:16](https://github.com/leanprover-community/mathlib/commit/7500b24)
chore(scripts): update nolints.txt ([#5661](https://github.com/leanprover-community/mathlib/pull/5661))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-08 02:05:14](https://github.com/leanprover-community/mathlib/commit/4c3c8d7)
feat(measure_theory): some additions ([#5653](https://github.com/leanprover-community/mathlib/pull/5653))
rename `exists_is_measurable_superset_of_measure_eq_zero` -> `exists_is_measurable_superset_of_null`
make `measure.prod` and `measure.pi` irreducible
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+ *lemma* homeomorph.to_measurable_equiv_coe
- \+ *lemma* homeomorph.to_measurable_equiv_symm_coe
- \+ *lemma* measurable_inv
- \+ *lemma* measurable_div
- \+ *lemma* measurable.ennreal_inv
- \+ *lemma* measurable.ennreal_div
- \+/\- *def* homeomorph.to_measurable_equiv

Modified src/measure_theory/integration.lean
- \+ *lemma* lintegral_one
- \+ *lemma* set_lintegral_const
- \+ *lemma* lintegral_lintegral_mul

Modified src/measure_theory/measurable_space.lean
- \+ *theorem* symm_comp_self
- \+ *theorem* self_comp_symm

Modified src/measure_theory/measure_space.lean
- \+ *lemma* exists_is_measurable_superset_of_null
- \- *lemma* exists_is_measurable_superset_of_measure_eq_zero

Modified src/measure_theory/pi.lean


Modified src/measure_theory/prod.lean
- \+ *lemma* lintegral_prod_mul



## [2021-01-07 23:12:07](https://github.com/leanprover-community/mathlib/commit/33a86cf)
chore(data/list/basic): tag mmap(') with simp ([#5443](https://github.com/leanprover-community/mathlib/pull/5443))
#### Estimated changes
Modified src/data/list/basic.lean




## [2021-01-07 21:43:48](https://github.com/leanprover-community/mathlib/commit/18ba69b)
feat(category_theory/sites): category of sheaves on the trivial topology  ([#5651](https://github.com/leanprover-community/mathlib/pull/5651))
Shows that the category of sheaves on the trivial topology is just the category of presheaves.
#### Estimated changes
Modified src/category_theory/sites/sheaf_of_types.lean
- \+ *lemma* is_sheaf_bot
- \+ *def* SheafOfTypes_bot_equiv



## [2021-01-07 21:43:46](https://github.com/leanprover-community/mathlib/commit/3c5d5c5)
feat(category_theory/monad): reflector preserves terminal object ([#5649](https://github.com/leanprover-community/mathlib/pull/5649))
#### Estimated changes
Modified src/category_theory/monad/limits.lean




## [2021-01-07 21:43:44](https://github.com/leanprover-community/mathlib/commit/a30c39e)
feat(measure_theory/borel_space): a compact set has finite measure ([#5628](https://github.com/leanprover-community/mathlib/pull/5628))
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_compact.measure_lt_top_of_nhds_within
- \+ *lemma* is_compact.measure_lt_top



## [2021-01-07 21:43:41](https://github.com/leanprover-community/mathlib/commit/4da8313)
feat(category_theory/closed): golf definition and proofs ([#5623](https://github.com/leanprover-community/mathlib/pull/5623))
Using the new mates framework, simplify the definition of `pre` and shorten proofs about it. 
To be more specific,
- `pre` is now explicitly a natural transformation, rather than indexed morphisms with a naturality property
- The new definition of `pre` means things like `pre_map` which I complained about before are easier to prove, and `pre_post_comm` is automatic
- There are now more lemmas relating `pre` to `coev`, `ev` and `uncurry`: `uncurry_pre` in particular was a hole in the API.
- `internal_hom` has a shorter construction. In particular I changed the type to `Cᵒᵖ ⥤ C ⥤ C`, which I think is better since the usual external hom functor is given as `Cᵒᵖ ⥤ C ⥤ Type*`, so this is consistent with that. 
In a subsequent PR I'll do the same for `exp_comparison`, but that's a bigger change with improved API so they're separate for now.
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean
- \+ *lemma* exp_adjunction_counit
- \+ *lemma* exp_adjunction_unit
- \+ *lemma* prod_map_pre_app_comp_ev
- \+ *lemma* uncurry_pre
- \+ *lemma* coev_app_comp_pre_app
- \+/\- *lemma* pre_id
- \+/\- *lemma* pre_map
- \- *lemma* pre_post_comm
- \+/\- *def* pre
- \+/\- *def* internal_hom



## [2021-01-07 21:43:39](https://github.com/leanprover-community/mathlib/commit/fdbcab6)
feat(category_theory/limits): the product comparison natural transformation ([#5621](https://github.com/leanprover-community/mathlib/pull/5621))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *def* prod_comparison_nat_trans
- \+ *def* prod_comparison_nat_iso



## [2021-01-07 19:12:12](https://github.com/leanprover-community/mathlib/commit/2894260)
feat(group_theory): add lemmas on solvability ([#5646](https://github.com/leanprover-community/mathlib/pull/5646))
Proves some basic lemmas about solvable groups: the subgroup of a solvable group is solvable, a quotient of a solvable group is solvable.
#### Estimated changes
Modified src/group_theory/solvable.lean
- \+ *lemma* map_commutator_eq_commutator_map
- \+ *lemma* commutator_le_map_commutator
- \+ *lemma* map_derived_series_le_derived_series
- \+ *lemma* derived_series_le_map_derived_series
- \+ *lemma* map_derived_series_eq
- \+ *lemma* is_solvable_def
- \+ *lemma* is_solvable_of_top_eq_bot
- \+ *lemma* solvable_of_solvable_injective
- \+ *lemma* solvable_of_surjective

Modified src/group_theory/subgroup.lean
- \+ *lemma* map_eq_bot_iff



## [2021-01-07 13:09:27](https://github.com/leanprover-community/mathlib/commit/66e02b3)
feat(docs/100): Add Masdeu's formalisation of Euler's Summation to 100.yaml ([#5655](https://github.com/leanprover-community/mathlib/pull/5655))
#### Estimated changes
Modified docs/100.yaml




## [2021-01-07 13:09:25](https://github.com/leanprover-community/mathlib/commit/7bc2e9e)
feat(ring_theory/polynomial/cyclotomic): add cyclotomic.irreducible ([#5642](https://github.com/leanprover-community/mathlib/pull/5642))
I proved irreducibility of cyclotomic polynomials, showing that `cyclotomic n Z` is the minimal polynomial of any primitive root of unity.
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+ *lemma* eq_of_monic_of_dvd_of_nat_degree_le

Modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* is_root_cyclotomic
- \+ *lemma* minimal_polynomial_primitive_root_dvd_cyclotomic
- \+ *lemma* minimal_polynomial_primitive_root_eq_cyclotomic
- \+ *lemma* cyclotomic.irreducible

Modified src/ring_theory/roots_of_unity.lean




## [2021-01-07 13:09:23](https://github.com/leanprover-community/mathlib/commit/b9da50a)
feat(ring_theory/*): Various lemmas used to prove classical nullstellensatz ([#5632](https://github.com/leanprover-community/mathlib/pull/5632))
#### Estimated changes
Modified src/field_theory/mv_polynomial.lean
- \+ *lemma* quotient_mk_comp_C_injective

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ring_equiv.bot_maximal_iff
- \+/\- *theorem* radical_idem

Modified src/ring_theory/jacobson_ideal.lean
- \+/\- *lemma* le_jacobson
- \+ *lemma* jacobson_idem
- \+/\- *lemma* radical_le_jacobson
- \+/\- *lemma* eq_radical_of_eq_jacobson
- \+/\- *lemma* jacobson_eq_bot
- \+/\- *lemma* jacobson_eq_self_of_is_maximal
- \+/\- *lemma* eq_jacobson_iff_not_mem
- \+/\- *lemma* map_jacobson_of_bijective
- \+ *lemma* jacobson_radical_eq_jacobson
- \+/\- *theorem* jacobson_eq_top_iff
- \+/\- *theorem* mem_jacobson_iff
- \+/\- *theorem* eq_jacobson_iff_Inf_maximal
- \+/\- *theorem* eq_jacobson_iff_Inf_maximal'
- \+/\- *theorem* map_jacobson_of_surjective
- \+/\- *theorem* jacobson_eq_iff_jacobson_quotient_eq_bot
- \+/\- *theorem* radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot

Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* map_mv_polynomial_eq_eval₂



## [2021-01-07 13:09:21](https://github.com/leanprover-community/mathlib/commit/3aea284)
feat(analysis/normed_space): affine map with findim domain is continuous ([#5627](https://github.com/leanprover-community/mathlib/pull/5627))
#### Estimated changes
Modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* affine_map.continuous_linear_iff

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* dist_eq_norm'

Modified src/analysis/normed_space/finite_dimension.lean
- \+ *theorem* affine_map.continuous_of_finite_dimensional

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* apply_apply



## [2021-01-07 13:09:18](https://github.com/leanprover-community/mathlib/commit/833e9a0)
chore(analysis/calculus): add `of_mem_nhds` versions of 2 lemmas ([#5626](https://github.com/leanprover-community/mathlib/pull/5626))
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* fderiv_within_of_mem_nhds
- \+/\- *lemma* fderiv_within_of_open

Modified src/analysis/calculus/tangent_cone.lean
- \+ *lemma* unique_diff_within_at_of_mem_nhds



## [2021-01-07 13:09:16](https://github.com/leanprover-community/mathlib/commit/e14d5eb)
feat(category_theory/limits): prod map is iso if components are ([#5620](https://github.com/leanprover-community/mathlib/pull/5620))
Show that if `f` and `g` are iso, then `prod.map f g` is an iso, and the dual.
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean




## [2021-01-07 13:09:14](https://github.com/leanprover-community/mathlib/commit/87ef7af)
feat(linear_algebra/pi_tensor_product): define the tensor product of an indexed family of semimodules ([#5311](https://github.com/leanprover-community/mathlib/pull/5311))
This PR defines the tensor product of an indexed family `s : ι → Type*` of semimodules over commutative semirings. We denote this space by `⨂[R] i, s i` and define it as `free_add_monoid (R × Π i, s i)` quotiented by the appropriate equivalence relation. The treatment follows very closely that of the binary tensor product in `linear_algebra/tensor_product.lean`.
#### Estimated changes
Created src/linear_algebra/pi_tensor_product.lean
- \+ *lemma* zero_tprod_coeff
- \+ *lemma* zero_tprod_coeff'
- \+ *lemma* add_tprod_coeff
- \+ *lemma* add_tprod_coeff'
- \+ *lemma* smul_tprod_coeff_aux
- \+ *lemma* smul_tprod_coeff
- \+ *lemma* smul_tprod_coeff'
- \+ *lemma* tprod_coeff_eq_smul_tprod
- \+ *lemma* lift_aux_tprod
- \+ *lemma* lift_aux_tprod_coeff
- \+ *lemma* lift_aux.smul
- \+ *lemma* lift.tprod
- \+ *theorem* ext
- \+ *theorem* lift.unique'
- \+ *theorem* lift.unique
- \+ *theorem* lift_tprod
- \+ *def* pi_tensor_product
- \+ *def* tprod_coeff
- \+ *def* lift_add_hom
- \+ *def* tprod
- \+ *def* lift_aux
- \+ *def* lift



## [2021-01-07 10:05:38](https://github.com/leanprover-community/mathlib/commit/47c6081)
chore(group_theory/perm/sign): remove classical for sign congr simp lemmas ([#5622](https://github.com/leanprover-community/mathlib/pull/5622))
Previously, some lemmas about how `perm.sign` simplifies across various congrs of permutations assumed `classical`, which prevented them from being applied by the simplifier. This makes the `decidable_eq` assumptions explicit.
#### Estimated changes
Modified src/group_theory/perm/sign.lean
- \+/\- *lemma* sign_prod_extend_right
- \+/\- *lemma* sign_prod_congr_right
- \+/\- *lemma* sign_prod_congr_left
- \+/\- *lemma* sign_perm_congr
- \+/\- *lemma* sign_sum_congr

Modified src/linear_algebra/determinant.lean




## [2021-01-07 10:05:35](https://github.com/leanprover-community/mathlib/commit/9dd1496)
chore(group_theory/perm/basic): Add some missing simp lemmas ([#5614](https://github.com/leanprover-community/mathlib/pull/5614))
`simp` can't find the appropriate `equiv` lemmas as they are about `refl` not `1`, even though those are defeq.
#### Estimated changes
Modified src/group_theory/perm/basic.lean
- \+ *lemma* trans_one
- \+ *lemma* mul_refl
- \+ *lemma* one_symm
- \+ *lemma* refl_inv
- \+ *lemma* one_trans
- \+ *lemma* refl_mul
- \+ *lemma* inv_trans
- \+ *lemma* mul_symm
- \+ *lemma* trans_inv
- \+ *lemma* symm_mul



## [2021-01-07 10:05:33](https://github.com/leanprover-community/mathlib/commit/2457287)
feat(algebra/subalgebra): Restrict injective algebra homomorphism to algebra isomorphism ([#5560](https://github.com/leanprover-community/mathlib/pull/5560))
The domain of an injective algebra homomorphism is isomorphic to its range.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* alg_equiv.of_injective_apply



## [2021-01-07 10:05:31](https://github.com/leanprover-community/mathlib/commit/2c8175f)
feat(algebra/algebra/ordered): ordered algebras ([#4683](https://github.com/leanprover-community/mathlib/pull/4683))
An ordered algebra is an ordered semiring, which is an algebra over an ordered commutative semiring,
for which scalar multiplication is "compatible" with the two orders.
#### Estimated changes
Created src/algebra/algebra/ordered.lean
- \+ *lemma* algebra_map_monotone

Modified src/algebra/ordered_ring.lean


Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex.mem_Icc
- \+/\- *lemma* concave_on.subset



## [2021-01-07 08:51:54](https://github.com/leanprover-community/mathlib/commit/95c7087)
chore(docs/100.yaml): Freek No. 15 ([#5638](https://github.com/leanprover-community/mathlib/pull/5638))
I've updated docs/100.yaml to reflect the fact that both FTC-1 and FTC-2 have been added to mathlib.
#### Estimated changes
Modified docs/100.yaml


Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/measure_theory/interval_integral.lean




## [2021-01-07 05:47:19](https://github.com/leanprover-community/mathlib/commit/a32e223)
refactor(analysis/special_functions/trigonometric): redefine arcsin and arctan ([#5300](https://github.com/leanprover-community/mathlib/pull/5300))
Redefine `arcsin` and `arctan` using `order_iso`, and prove that both of them are infinitely smooth.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *theorem* local_homeomorph.times_cont_diff_at_symm_deriv

Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* coe_sin_order_iso_apply
- \+ *lemma* sin_order_iso_apply
- \+ *lemma* arcsin_mem_Icc
- \+ *lemma* range_arcsin
- \+/\- *lemma* arcsin_le_pi_div_two
- \+/\- *lemma* neg_pi_div_two_le_arcsin
- \+ *lemma* arcsin_proj_Icc
- \+ *lemma* sin_arcsin'
- \+ *lemma* arcsin_sin'
- \+ *lemma* strict_mono_incr_on_arcsin
- \+ *lemma* monotone_arcsin
- \+ *lemma* inj_on_arcsin
- \+/\- *lemma* arcsin_inj
- \+ *lemma* continuous_arcsin
- \+ *lemma* continuous_at_arcsin
- \+ *lemma* arcsin_eq_of_sin_eq
- \+ *lemma* arcsin_of_one_le
- \+/\- *lemma* arcsin_neg_one
- \+ *lemma* arcsin_of_le_neg_one
- \+ *lemma* arcsin_le_iff_le_sin
- \+ *lemma* arcsin_le_iff_le_sin'
- \+ *lemma* le_arcsin_iff_sin_le
- \+ *lemma* le_arcsin_iff_sin_le'
- \+ *lemma* arcsin_lt_iff_lt_sin
- \+ *lemma* arcsin_lt_iff_lt_sin'
- \+ *lemma* lt_arcsin_iff_sin_lt
- \+ *lemma* lt_arcsin_iff_sin_lt'
- \+ *lemma* arcsin_eq_iff_eq_sin
- \+/\- *lemma* arcsin_nonneg
- \+/\- *lemma* arcsin_nonpos
- \+/\- *lemma* arcsin_eq_zero_iff
- \+ *lemma* zero_eq_arcsin_iff
- \+/\- *lemma* arcsin_pos
- \+ *lemma* arcsin_lt_zero
- \+ *lemma* arcsin_lt_pi_div_two
- \+ *lemma* neg_pi_div_two_lt_arcsin
- \+ *lemma* arcsin_eq_pi_div_two
- \+ *lemma* pi_div_two_eq_arcsin
- \+ *lemma* pi_div_two_le_arcsin
- \+ *lemma* arcsin_eq_neg_pi_div_two
- \+ *lemma* neg_pi_div_two_eq_arcsin
- \+ *lemma* arcsin_le_neg_pi_div_two
- \+ *lemma* maps_to_sin_Ioo
- \+/\- *lemma* cos_arcsin_nonneg
- \+/\- *lemma* cos_arcsin
- \+ *lemma* deriv_arcsin_aux
- \+ *lemma* has_deriv_at_arcsin
- \+ *lemma* times_cont_diff_at_arcsin
- \+ *lemma* has_deriv_within_at_arcsin_Ici
- \+ *lemma* has_deriv_within_at_arcsin_Iic
- \+ *lemma* differentiable_within_at_arcsin_Ici
- \+ *lemma* differentiable_within_at_arcsin_Iic
- \+ *lemma* differentiable_at_arcsin
- \+ *lemma* deriv_arcsin
- \+ *lemma* differentiable_on_arcsin
- \+ *lemma* times_cont_diff_on_arcsin
- \+ *lemma* times_cont_diff_at_arcsin_iff
- \+ *lemma* measurable_arcsin
- \+ *lemma* strict_mono_decr_on_arccos
- \+ *lemma* arccos_inj_on
- \+/\- *lemma* arccos_inj
- \+ *lemma* arccos_eq_zero
- \+ *lemma* arccos_eq_pi_div_two
- \+ *lemma* arccos_eq_pi
- \+/\- *lemma* arccos_neg
- \+ *lemma* continuous_arccos
- \+ *lemma* has_deriv_at_arccos
- \+ *lemma* times_cont_diff_at_arccos
- \+ *lemma* has_deriv_within_at_arccos_Ici
- \+ *lemma* has_deriv_within_at_arccos_Iic
- \+ *lemma* differentiable_within_at_arccos_Ici
- \+ *lemma* differentiable_within_at_arccos_Iic
- \+ *lemma* differentiable_at_arccos
- \+ *lemma* deriv_arccos
- \+ *lemma* differentiable_on_arccos
- \+ *lemma* times_cont_diff_on_arccos
- \+ *lemma* times_cont_diff_at_arccos_iff
- \+ *lemma* measurable_arccos
- \+/\- *lemma* tan_nonpos_of_nonpos_of_neg_pi_div_two_le
- \+/\- *lemma* tan_lt_tan_of_nonneg_of_lt_pi_div_two
- \+ *lemma* strict_mono_incr_on_tan
- \+ *lemma* inj_on_tan
- \+/\- *lemma* tan_inj_of_lt_of_lt_pi_div_two
- \+ *lemma* times_cont_diff_at_tan
- \+ *lemma* surj_on_tan
- \+/\- *lemma* tan_surjective
- \+ *lemma* image_tan_Ioo
- \+/\- *lemma* tan_arctan
- \+/\- *lemma* arctan_mem_Ioo
- \+/\- *lemma* arctan_tan
- \+ *lemma* cos_arctan_pos
- \+ *lemma* cos_sq_arctan
- \+/\- *lemma* sin_arctan
- \+/\- *lemma* cos_arctan
- \+/\- *lemma* arctan_lt_pi_div_two
- \+/\- *lemma* neg_pi_div_two_lt_arctan
- \+ *lemma* arctan_eq_arcsin
- \+/\- *lemma* arctan_zero
- \+ *lemma* arctan_eq_of_tan_eq
- \+/\- *lemma* arctan_one
- \+/\- *lemma* arctan_neg
- \+ *lemma* continuous_at_arctan
- \+ *lemma* coe_tan_local_homeomorph
- \+ *lemma* coe_tan_local_homeomorph_symm
- \+ *lemma* differentiable_arctan
- \+ *lemma* times_cont_diff_arctan
- \+ *lemma* measurable_arctan
- \+ *lemma* measurable.arctan
- \+/\- *lemma* deriv_within_arctan
- \+/\- *lemma* deriv_arctan
- \+ *lemma* has_fderiv_at.arctan
- \+ *lemma* has_fderiv_within_at.arctan
- \+ *lemma* fderiv_within_arctan
- \+ *lemma* fderiv_arctan
- \+ *lemma* times_cont_diff_at.arctan
- \+ *lemma* times_cont_diff.arctan
- \+ *lemma* times_cont_diff_within_at.arctan
- \+ *lemma* times_cont_diff_on.arctan
- \- *lemma* abs_div_sqrt_one_add_lt
- \- *lemma* div_sqrt_one_add_lt_one
- \- *lemma* neg_one_lt_div_sqrt_one_add
- \- *lemma* tan_homeomorph_inv_fun_eq_arctan
- \+ *def* sin_order_iso
- \+ *def* sin_local_homeomorph
- \+ *def* tan_order_iso
- \+ *def* tan_local_homeomorph
- \- *def* tan_homeomorph

Modified src/data/subtype.lean
- \+ *theorem* coe_eq_iff

Modified src/geometry/euclidean/basic.lean
- \+/\- *lemma* angle_eq_zero_iff
- \+/\- *lemma* angle_eq_pi_iff

Modified src/geometry/euclidean/triangle.lean


Modified src/topology/algebra/ordered.lean
- \- *lemma* coe_homeomorph_of_strict_mono_continuous
- \- *lemma* coe_homeomorph_of_strict_mono_continuous_Ioo



## [2021-01-07 02:28:43](https://github.com/leanprover-community/mathlib/commit/3f35961)
chore(scripts): update nolints.txt ([#5652](https://github.com/leanprover-community/mathlib/pull/5652))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-06 23:23:44](https://github.com/leanprover-community/mathlib/commit/f668be0)
feat(data/list/zip): parameterize zip_append more generally ([#5650](https://github.com/leanprover-community/mathlib/pull/5650))
zip_append should only require that each pair of lists is of the same type
#### Estimated changes
Modified src/data/list/zip.lean
- \+/\- *theorem* zip_append



## [2021-01-06 16:21:02](https://github.com/leanprover-community/mathlib/commit/f4128dc)
chore(ring_theory/ideal/basic): Make an argument to mul_mem_{left,right} explicit ([#5611](https://github.com/leanprover-community/mathlib/pull/5611))
Before this change, the lemmas with result `a * b ∈ I` did not have enough explicit arguments to determine both `a` and `b`, such as `I.mul_mem_left hb`.
This resulted in callers using `show`, `@`, or sometimes ignoring the API and using `smul_mem` which does have appropriate argument explicitness. These callers have been cleaned up accordingly.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/data/padics/ring_homs.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/ideal/basic.lean
- \+/\- *lemma* mul_mem_left
- \+/\- *lemma* mul_mem_right

Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/ideal/over.lean


Modified src/ring_theory/ideal/prod.lean


Modified src/ring_theory/jacobson_ideal.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/topology/algebra/ring.lean




## [2021-01-06 16:21:00](https://github.com/leanprover-community/mathlib/commit/91fcb48)
feat(linear_algebra/tensor_product,algebra/module/linear_map): Made tmul_smul and map_smul_of_tower work for int over semirings ([#5430](https://github.com/leanprover-community/mathlib/pull/5430))
With this change, ` ∀ (f : M →ₗ[S] M₂) (z : int) (x : M), f (z • x) = z • f x` can be proved with `linear_map.map_smul_of_tower` even when `S` is a semiring, and `z • (m ⊗ₜ n : M ⊗[S] N) = (r • m) ⊗ₜ n` can be proved with `tmul_smul`.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+/\- *lemma* map_smul_of_tower
- \+/\- *def* restrict_scalars

Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/tensor_product.lean
- \+/\- *lemma* smul_tmul
- \+/\- *lemma* tmul_smul
- \+/\- *theorem* smul_tmul'



## [2021-01-06 13:54:26](https://github.com/leanprover-community/mathlib/commit/eeb194d)
feat(analysis/normed_space/inner_product): facts about the span of a single vector, mostly in inner product spaces ([#5589](https://github.com/leanprover-community/mathlib/pull/5589))
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* orthogonal_projection_bot
- \+ *lemma* smul_orthogonal_projection_singleton
- \+ *lemma* orthogonal_projection_singleton
- \+ *lemma* orthogonal_projection_unit_singleton
- \+ *lemma* inner_right_of_mem_orthogonal_singleton
- \+ *lemma* inner_left_of_mem_orthogonal_singleton
- \+ *lemma* orthogonal_projection_orthogonal_complement_singleton_eq_zero
- \+ *lemma* findim_orthogonal_span_singleton

Modified src/linear_algebra/basic.lean
- \+ *lemma* span_zero_singleton

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* findim_span_singleton



## [2021-01-06 11:04:14](https://github.com/leanprover-community/mathlib/commit/186ad76)
feat(ring_theory/finiteness): add finitely presented algebra ([#5407](https://github.com/leanprover-community/mathlib/pull/5407))
This PR contains the definition of a finitely presented algebra and some very basic results. A lot of other fundamental results are missing (stability under composition, equivalence with finite type for noetherian rings ecc): I am ready to work on them, but I wanted some feedback. Feel free to convert to WIP if you think it's better to wait.
#### Estimated changes
Modified src/data/mv_polynomial/equiv.lean
- \+ *def* pempty_alg_equiv

Modified src/ring_theory/finiteness.lean
- \+ *lemma* of_finitely_presented
- \+ *lemma* equiv
- \+ *lemma* mv_polynomial
- \+ *lemma* self
- \+ *def* algebra.finitely_presented



## [2021-01-06 11:04:12](https://github.com/leanprover-community/mathlib/commit/35ff043)
feat(ring_theory/fractional_ideal): move inv to dedekind_domain ([#5053](https://github.com/leanprover-community/mathlib/pull/5053))
Remove all instances of `inv` and I^{-1}. The notation (1 / I) is the one used for the old I^{-1}.
#### Estimated changes
Modified src/ring_theory/dedekind_domain.lean
- \+ *lemma* inv_eq
- \+ *lemma* inv_zero'
- \+ *lemma* inv_nonzero
- \+ *lemma* coe_inv_of_nonzero
- \+ *lemma* map_inv
- \+ *lemma* span_singleton_inv
- \+ *lemma* mul_generator_self_inv
- \+ *lemma* invertible_of_principal
- \+ *lemma* invertible_iff_generator_nonzero
- \+ *lemma* is_principal_inv
- \+ *theorem* right_inverse_eq
- \+ *theorem* mul_inv_cancel_iff

Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* map_one_div
- \+/\- *lemma* div_span_singleton
- \+ *lemma* is_noetherian_span_singleton_inv_to_map_mul
- \- *lemma* inv_eq
- \- *lemma* inv_zero
- \- *lemma* inv_nonzero
- \- *lemma* coe_inv_of_nonzero
- \- *lemma* map_inv
- \- *lemma* mul_generator_self_inv
- \- *lemma* span_singleton_inv
- \- *lemma* invertible_of_principal
- \- *lemma* invertible_iff_generator_nonzero
- \- *lemma* is_principal_inv
- \- *lemma* is_noetherian_span_singleton_to_map_inv_mul
- \- *lemma* is_noetherian
- \+ *theorem* eq_one_div_of_mul_eq_one
- \+ *theorem* mul_div_self_cancel_iff
- \+ *theorem* is_noetherian
- \- *theorem* right_inverse_eq
- \- *theorem* mul_inv_cancel_iff



## [2021-01-06 11:04:08](https://github.com/leanprover-community/mathlib/commit/1db70a8)
feat(computability/regular_expressions): define regular expressions ([#5036](https://github.com/leanprover-community/mathlib/pull/5036))
Very basic definitions for regular expressions
#### Estimated changes
Created src/computability/regular_expressions.lean
- \+ *lemma* zero_def
- \+ *lemma* one_def
- \+ *lemma* plus_def
- \+ *lemma* comp_def
- \+ *lemma* matches_zero_def
- \+ *lemma* matches_epsilon_def
- \+ *lemma* matches_add_def
- \+ *lemma* matches_mul_def
- \+ *lemma* matches_star_def
- \+ *lemma* zero_rmatch
- \+ *lemma* one_rmatch_iff
- \+ *lemma* char_rmatch_iff
- \+ *lemma* add_rmatch_iff
- \+ *lemma* mul_rmatch_iff
- \+ *lemma* star_rmatch_iff
- \+ *lemma* rmatch_iff_matches
- \+ *def* matches
- \+ *def* match_epsilon
- \+ *def* deriv
- \+ *def* rmatch



## [2021-01-06 11:04:04](https://github.com/leanprover-community/mathlib/commit/137a6e0)
feat(tactic/rewrite_search): Automatically searching for chains of rewrites ([#4841](https://github.com/leanprover-community/mathlib/pull/4841))
This pull request is based on a branch originally developed by @semorrison , @khoek , and @jcommelin . The idea of rewrite_search is a tactic that will search through chains of potential rewrites to prove the goal, when the goal is an equality or iff statement. There are three key components: `discovery.lean` finds a bunch of rules that can be used to generate rewrites, `search.lean` runs a breadth-first-search algorithm on the two sides of the quality to find a path that connects them, and `explain.lean` generates Lean code from the resulting proof, so that you can replace the call to `rewrite_search` with the explicit steps for it.
I removed some functionality from the rewrite_search branch and simplified the data structures somewhat in order to get this pull request small enough to be reviewed. If there is functionality from that branch that people particularly wanted, let me know and I can either include it in this PR or in a subsequent one. In particular, most of the configuration options are omitted.
For data structures, the whole `table` data structure is gone, replaced by a `buffer` and `rb_map` for efficient lookup. Write access to the buffer is also append-only for efficiency. This seems to be a lot faster, although I haven't created specific performance benchmarks.
#### Estimated changes
Modified src/data/buffer/basic.lean


Modified src/meta/expr_lens.lean


Modified src/tactic/nth_rewrite/congr.lean


Modified src/tactic/nth_rewrite/default.lean


Created src/tactic/rewrite_search/default.lean


Created src/tactic/rewrite_search/discovery.lean


Created src/tactic/rewrite_search/explain.lean
- \+ *def* get
- \+ *def* set
- \+ *def* to_list
- \+ *def* to_string

Created src/tactic/rewrite_search/frontend.lean


Created src/tactic/rewrite_search/search.lean


Created src/tactic/rewrite_search/types.lean
- \+ *def* side.to_xhs

Created test/rewrite_search/rewrite_search.lean
- \+ *lemma* test_pathfinding
- \+ *lemma* test_linear_path
- \+ *lemma* test_algebra
- \+ *lemma* test_simpler_algebra
- \+ *lemma* test_pp_1
- \+ *lemma* test_pp_2
- \+ *def* idf



## [2021-01-06 08:30:32](https://github.com/leanprover-community/mathlib/commit/062f244)
feat(category_theory/monad): generalise limits lemma ([#5630](https://github.com/leanprover-community/mathlib/pull/5630))
A slight generalisation of a lemma already there.
#### Estimated changes
Modified src/category_theory/monad/limits.lean
- \+ *lemma* has_limit_of_reflective
- \+ *lemma* has_limits_of_shape_of_reflective



## [2021-01-06 08:30:30](https://github.com/leanprover-community/mathlib/commit/56ed5d7)
feat(category_theory/adjunction): mates ([#5599](https://github.com/leanprover-community/mathlib/pull/5599))
Adds some results on the calculus of mates.
#### Estimated changes
Created src/category_theory/adjunction/mates.lean
- \+ *lemma* transfer_nat_trans_counit
- \+ *lemma* unit_transfer_nat_trans
- \+ *lemma* transfer_nat_trans_self_counit
- \+ *lemma* unit_transfer_nat_trans_self
- \+ *lemma* transfer_nat_trans_self_id
- \+ *lemma* transfer_nat_trans_self_symm_id
- \+ *lemma* transfer_nat_trans_self_comp
- \+ *lemma* transfer_nat_trans_self_symm_comp
- \+ *lemma* transfer_nat_trans_self_comm
- \+ *lemma* transfer_nat_trans_self_symm_comm
- \+ *def* transfer_nat_trans
- \+ *def* transfer_nat_trans_self
- \+ *def* transfer_nat_trans_self_of_iso
- \+ *def* transfer_nat_trans_self_symm_of_iso



## [2021-01-06 08:30:28](https://github.com/leanprover-community/mathlib/commit/5f98a96)
feat(group_theory): add definition of solvable group ([#5565](https://github.com/leanprover-community/mathlib/pull/5565))
Defines solvable groups using the definition that a group is solvable if its nth commutator is eventually trivial. Defines the nth commutator of a group and provides some lemmas for working with it. More facts about solvable groups will come in future PRs.
#### Estimated changes
Modified src/algebra/lie/basic.lean


Created src/data/bracket.lean


Created src/group_theory/solvable.lean
- \+ *lemma* general_commutator_def
- \+ *lemma* general_commutator_mono
- \+ *lemma* general_commutator_def'
- \+ *lemma* general_commutator_le
- \+ *lemma* general_commutator_comm
- \+ *lemma* general_commutator_le_right
- \+ *lemma* general_commutator_le_left
- \+ *lemma* general_commutator_bot
- \+ *lemma* bot_general_commutator
- \+ *lemma* general_commutator_le_inf
- \+ *lemma* derived_series_zero
- \+ *lemma* derived_series_succ
- \+ *lemma* derived_series_normal
- \+ *lemma* general_commutator_eq_commutator
- \+ *lemma* commutator_def'
- \+ *lemma* derived_series_one
- \+ *def* derived_series

Modified src/group_theory/subgroup.lean
- \+ *theorem* le_normal_closure
- \+ *theorem* normal_closure_eq_self
- \+ *theorem* normal_closure_idempotent
- \+ *theorem* closure_le_normal_closure
- \+ *theorem* normal_closure_closure_eq_normal_closure



## [2021-01-06 08:30:25](https://github.com/leanprover-community/mathlib/commit/648ff21)
feat(algebra/lie/basic): the lattice of Lie submodules of a Noetherian Lie module is well-founded ([#5557](https://github.com/leanprover-community/mathlib/pull/5557))
The key result is: `well_founded_of_noetherian`
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* mem_coe_submodule
- \+ *lemma* coe_submodule_injective
- \+ *lemma* well_founded_of_noetherian



## [2021-01-06 05:36:16](https://github.com/leanprover-community/mathlib/commit/3892155)
fix(algebra/group/pi): use correct `div`/`sub` ([#5625](https://github.com/leanprover-community/mathlib/pull/5625))
Without an explicit `div := has_div.div`, `rw [pi.sub_apply]` fails sometimes.
#### Estimated changes
Modified src/algebra/group/pi.lean




## [2021-01-06 05:36:13](https://github.com/leanprover-community/mathlib/commit/3d6ba9a)
feat(data/list/chain): chain pmap ([#5438](https://github.com/leanprover-community/mathlib/pull/5438))
Two chain pmap lemmas
#### Estimated changes
Modified src/data/list/chain.lean
- \+ *theorem* chain_pmap_of_chain
- \+ *theorem* chain_of_chain_pmap



## [2021-01-06 02:30:13](https://github.com/leanprover-community/mathlib/commit/de73912)
chore(scripts): update nolints.txt ([#5629](https://github.com/leanprover-community/mathlib/pull/5629))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-01-06 02:30:10](https://github.com/leanprover-community/mathlib/commit/19d2ea7)
feat(order/atoms): Pairwise coprime ([#5596](https://github.com/leanprover-community/mathlib/pull/5596))
Don't really know what to call it, but it's the atom-level version of the statement that maximal ideals are pairwise coprime.
#### Estimated changes
Modified src/order/atoms.lean
- \+ *lemma* is_atom.inf_eq_bot_of_ne
- \+ *lemma* is_atom.disjoint_of_ne
- \+ *lemma* is_coatom.sup_eq_top_of_ne



## [2021-01-06 02:30:08](https://github.com/leanprover-community/mathlib/commit/9fdd703)
feat(linear_algebra/affine_space/midpoint): a few more lemmas ([#5571](https://github.com/leanprover-community/mathlib/pull/5571))
* simplify expressions like `midpoint R p₁ p₂ -ᵥ p₁` and
  `p₂ - midpoint R p₁ p₂`;
* fix a typo in `data/set/intervals/surj_on`.
#### Estimated changes
Modified src/data/set/intervals/surj_on.lean


Modified src/linear_algebra/affine_space/midpoint.lean
- \+ *lemma* midpoint_vsub_left
- \+ *lemma* midpoint_vsub_right
- \+ *lemma* left_vsub_midpoint
- \+ *lemma* right_vsub_midpoint
- \+ *lemma* midpoint_sub_left
- \+ *lemma* midpoint_sub_right
- \+ *lemma* left_sub_midpoint
- \+ *lemma* right_sub_midpoint



## [2021-01-06 02:30:06](https://github.com/leanprover-community/mathlib/commit/731c26f)
refactor(*): swap sides of `iff` in `{rel_embedding,order_embedding}.map_rel_iff` ([#5556](https://github.com/leanprover-community/mathlib/pull/5556))
This way RHS is "simpler" than LHS.
Other API changes (in `rel_embedding` and/or `ord_embedding` and/or `rel_iso` and/or `ord_iso` namespaces):
* drop `map_le_iff`, rename `apply_le_apply` to `le_iff_le`;
* drop `map_lt_iff`, rename `apply_lt_apply` to `lt_iff_lt`;
* rename `apply_eq_apply` to `eq_iff_eq`.
#### Estimated changes
Modified src/data/fin.lean


Modified src/data/finset/sort.lean


Modified src/data/finsupp/lattice.lean


Modified src/data/list/nodup_equiv_fin.lean


Modified src/data/nat/enat.lean


Modified src/data/setoid/basic.lean


Modified src/data/setoid/partition.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/group_theory/congruence.lean


Modified src/linear_algebra/basic.lean


Modified src/order/galois_connection.lean


Modified src/order/ord_continuous.lean


Modified src/order/order_iso_nat.lean


Modified src/order/rel_iso.lean
- \+ *lemma* eq_iff_eq
- \+ *lemma* le_iff_le
- \+ *lemma* lt_iff_lt
- \- *lemma* apply_le_apply
- \- *lemma* apply_lt_apply
- \- *lemma* apply_eq_apply
- \- *lemma* map_rel_iff''
- \+/\- *theorem* map_rel_iff
- \+ *theorem* le_iff_le
- \+ *theorem* lt_iff_lt
- \+/\- *theorem* coe_fn_mk
- \- *theorem* map_le_iff
- \- *theorem* map_lt_iff

Modified src/order/semiconj_Sup.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/localization.lean
- \+/\- *def* order_embedding

Modified src/ring_theory/noetherian.lean


Modified src/set_theory/cardinal_ordinal.lean


Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal.lean


Modified src/set_theory/ordinal_arithmetic.lean




## [2021-01-06 00:02:09](https://github.com/leanprover-community/mathlib/commit/8f424fc)
chore(measure_theory/pi): a few more lemmas ([#5604](https://github.com/leanprover-community/mathlib/pull/5604))
Also prove that a locally finite measure in a `second_countable_topology` is `sigma_finite`.
#### Estimated changes
Modified src/algebra/big_operators/order.lean


Modified src/measure_theory/measure_space.lean
- \+ *lemma* finite_at_filter.exists_mem_basis
- \+ *lemma* sigma_finite_of_not_nonempty
- \+ *lemma* sigma_finite_of_countable
- \+ *lemma* measure.exists_is_open_measure_lt_top

Modified src/measure_theory/pi.lean
- \+ *lemma* pi_eval_preimage_null
- \+ *lemma* pi_hyperplane
- \+ *lemma* measure_space.pi_def
- \+ *lemma* volume_pi



## [2021-01-05 20:33:53](https://github.com/leanprover-community/mathlib/commit/00d8617)
feat(analysis/normed_space/inner_product): inner product is continuous, norm squared is smooth ([#5600](https://github.com/leanprover-community/mathlib/pull/5600))
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* fderiv_inner_clm_apply
- \+ *lemma* has_fderiv_within_at.inner
- \+ *lemma* has_fderiv_at.inner
- \+ *lemma* has_deriv_within_at.inner
- \+ *lemma* has_deriv_at.inner
- \+ *lemma* fderiv_inner_apply
- \+ *lemma* deriv_inner_apply
- \+ *lemma* times_cont_diff_norm_square
- \+ *lemma* times_cont_diff.norm_square
- \+ *lemma* times_cont_diff_within_at.norm_square
- \+ *lemma* times_cont_diff_at.norm_square
- \+ *lemma* times_cont_diff_on.norm_square
- \+ *lemma* differentiable_at.norm_square
- \+ *lemma* differentiable.norm_square
- \+ *lemma* differentiable_within_at.norm_square
- \+ *lemma* differentiable_on.norm_square
- \+/\- *lemma* continuous_inner
- \+ *lemma* filter.tendsto.inner
- \+ *lemma* measurable.inner
- \+ *lemma* continuous_within_at.inner
- \+ *lemma* continuous_at.inner
- \+ *lemma* continuous_on.inner
- \+ *lemma* continuous.inner
- \+ *def* fderiv_inner_clm



## [2021-01-05 20:33:51](https://github.com/leanprover-community/mathlib/commit/0c8fffe)
fix(algebra/group/prod): fixes for [#5563](https://github.com/leanprover-community/mathlib/pull/5563) ([#5577](https://github.com/leanprover-community/mathlib/pull/5577))
* rename `prod.units` to `mul_equiv.prod_units`;
* rewrite it with better definitional equalities;
* now `@[to_additive]` works: fixes [#5566](https://github.com/leanprover-community/mathlib/pull/5566);
* make `M` and `N` implicit in `mul_equiv.prod_comm`
#### Estimated changes
Modified src/algebra/group/prod.lean
- \+/\- *lemma* coe_prod_comm
- \+ *def* prod_units
- \- *def* units

Modified src/algebra/group/units.lean
- \+ *lemma* inv_mk
- \+ *theorem* mk_coe

Modified src/algebra/ring/prod.lean
- \+/\- *lemma* coe_prod_comm
- \+/\- *lemma* coe_prod_comm_symm
- \- *lemma* coe_coe_prod_comm
- \- *lemma* coe_coe_prod_comm_symm

Modified src/ring_theory/ideal/prod.lean




## [2021-01-05 20:33:49](https://github.com/leanprover-community/mathlib/commit/7cf0a29)
feat(analysis/normed_space/inner_product): consequences of characterization of orthogonal projection ([#5558](https://github.com/leanprover-community/mathlib/pull/5558))
Reverse order of equality in the lemma `eq_orthogonal_projection_of_mem_of_inner_eq_zero`.  Add some variants.  Also add three consequences:
- the orthogonal projection onto `K` of an element of `K` is itself
- the orthogonal projection onto `K` of an element of `Kᗮ` is zero
- for a submodule `K` of an inner product space, the sum of the orthogonal projections onto `K` and `Kᗮ` is the identity.
Reverse order of `iff` in the lemma `submodule.eq_top_iff_orthogonal_eq_bot`, and rename to `submodule.orthogonal_eq_bot_iff`.
#### Estimated changes
Modified src/analysis/normed_space/dual.lean


Modified src/analysis/normed_space/inner_product.lean
- \+/\- *lemma* orthogonal_projection_fn_mem
- \+/\- *lemma* orthogonal_projection_fn_inner_eq_zero
- \+/\- *lemma* eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
- \+/\- *lemma* orthogonal_projection_fn_norm_sq
- \+/\- *lemma* orthogonal_projection_fn_eq
- \+/\- *lemma* orthogonal_projection_inner_eq_zero
- \+/\- *lemma* eq_orthogonal_projection_of_mem_of_inner_eq_zero
- \+/\- *lemma* eq_orthogonal_projection_of_eq_submodule
- \+ *lemma* orthogonal_projection_mem_subspace_eq_self
- \+/\- *lemma* orthogonal_projection_norm_le
- \+/\- *lemma* submodule.mem_orthogonal
- \+/\- *lemma* submodule.mem_orthogonal'
- \+/\- *lemma* submodule.inner_right_of_mem_orthogonal
- \+/\- *lemma* submodule.inner_left_of_mem_orthogonal
- \+/\- *lemma* submodule.orthogonal_disjoint
- \+/\- *lemma* orthogonal_eq_inter
- \+/\- *lemma* submodule.is_closed_orthogonal
- \+/\- *lemma* submodule.le_orthogonal_orthogonal
- \+/\- *lemma* submodule.sup_orthogonal_of_is_complete
- \+/\- *lemma* submodule.sup_orthogonal_of_complete_space
- \+/\- *lemma* submodule.exists_sum_mem_mem_orthogonal
- \+/\- *lemma* submodule.orthogonal_orthogonal
- \+/\- *lemma* submodule.is_compl_orthogonal_of_is_complete
- \+ *lemma* submodule.orthogonal_eq_bot_iff
- \+ *lemma* submodule.orthogonal_eq_top_iff
- \+ *lemma* eq_orthogonal_projection_of_mem_orthogonal
- \+ *lemma* eq_orthogonal_projection_of_mem_orthogonal'
- \+ *lemma* orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero
- \+ *lemma* orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero
- \+ *lemma* eq_sum_orthogonal_projection_self_orthogonal_complement
- \+ *lemma* id_eq_sum_orthogonal_projection_self_orthogonal_complement
- \- *lemma* submodule.eq_top_iff_orthogonal_eq_bot
- \+/\- *theorem* exists_norm_eq_infi_of_complete_subspace
- \+/\- *theorem* norm_eq_infi_iff_real_inner_eq_zero
- \+/\- *theorem* norm_eq_infi_iff_inner_eq_zero
- \+/\- *def* orthogonal_projection_fn
- \+/\- *def* orthogonal_projection
- \+/\- *def* submodule.orthogonal

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* submodule.subtype_continuous_apply
- \+ *def* submodule.subtype_continuous



## [2021-01-05 20:33:46](https://github.com/leanprover-community/mathlib/commit/82ec0cc)
feat(ring_theory/roots_of_unity): degree of minimal polynomial ([#5475](https://github.com/leanprover-community/mathlib/pull/5475))
This is the penultimate PR about roots of unity and cyclotomic polynomials: I prove that the degree of the minimal polynomial of a primitive `n`th root of unity is at least `nat.totient n`.
It's easy to prove now that it is actually `nat.totient n`, and indeed that the minimal polynomial is the cyclotomic polynomial (that it is hence irreducible). I decided to split the PR like this because I feel that it's better to put the remaining results in `ring_theory/polynomials/cyclotomic`.
#### Estimated changes
Modified src/data/polynomial/degree/lemmas.lean
- \+ *lemma* nat_degree_map_le

Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* minimal_polynomial_eq_pow_coprime
- \+ *lemma* pow_is_root_minimal_polynomial
- \+ *lemma* is_roots_of_minimal_polynomial
- \+ *lemma* totient_le_degree_minimal_polynomial



## [2021-01-05 18:04:53](https://github.com/leanprover-community/mathlib/commit/d1b2d6e)
fix(linear_algebra/tensor_algebra): Correct the precedence of `⊗ₜ[R]` ([#5619](https://github.com/leanprover-community/mathlib/pull/5619))
Previously, `a ⊗ₜ[R] b = c` was interpreted as `a ⊗ₜ[R] (b = c)` which was nonsense because `eq` is not in `Type`.
I'm not sure whether `:0` is necessary, but it seems harmless.
The `:100` is the crucial bugfix here.
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean
- \+/\- *lemma* zero_tmul
- \+/\- *lemma* tmul_zero

Modified src/ring_theory/polynomial_algebra.lean


Modified src/ring_theory/tensor_product.lean




## [2021-01-05 18:04:51](https://github.com/leanprover-community/mathlib/commit/01e17a9)
feat(scripts/lint-style.sh): check that Lean files don't have executable bit ([#5606](https://github.com/leanprover-community/mathlib/pull/5606))
#### Estimated changes
Modified scripts/lint-style.sh


Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/algebra/continued_fractions/computation/basic.lean


Modified src/algebra/continued_fractions/computation/correctness_terminating.lean


Modified src/algebra/continued_fractions/computation/translations.lean


Modified src/topology/path_connected.lean




## [2021-01-05 16:18:37](https://github.com/leanprover-community/mathlib/commit/a6633e5)
feat(analysis/normed_space/inner_product): new versions of Cauchy-Schwarz equality case ([#5586](https://github.com/leanprover-community/mathlib/pull/5586))
The existing version of the Cauchy-Schwarz equality case characterizes the pairs `x`, `y` with `abs ⟪x, y⟫ = ∥x∥ * ∥y∥`.  This PR provides a characterization, with converse, of pairs satisfying `⟪x, y⟫ = ∥x∥ * ∥y∥`, and some consequences.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_sub_eq_zero_iff

Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* real_inner_le_norm
- \+ *lemma* inner_eq_norm_mul_iff
- \+ *lemma* inner_eq_norm_mul_iff_real
- \+ *lemma* inner_eq_norm_mul_iff_of_norm_one
- \+ *lemma* inner_lt_norm_mul_iff_real
- \+ *lemma* inner_lt_one_iff_real_of_norm_one

Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* im_eq_zero_of_le
- \+ *lemma* re_eq_self_of_le



## [2021-01-05 14:50:35](https://github.com/leanprover-community/mathlib/commit/1de608d)
refactor(measure_theory): integrate almost everywhere measurable functions ([#5510](https://github.com/leanprover-community/mathlib/pull/5510))
Currently, the Bochner integral is only defined for measurable functions. This means that, if `f` is continuous on an interval `[a, b]`, to be able to make sense of `∫ x in a..b, f`, one has to add a global measurability assumption, which is very much unnatural.
This PR redefines the Bochner integral so that it makes sense for functions that are almost everywhere measurable, i.e., they coincide almost everywhere with a measurable function (This is equivalent to measurability for the completed measure, but we don't state or prove this as it is not needed to develop the theory).
#### Estimated changes
Modified src/analysis/convex/integral.lean
- \+/\- *lemma* convex.smul_integral_mem

Modified src/analysis/mean_inequalities.lean


Modified src/measure_theory/ae_eq_fun.lean
- \+/\- *lemma* mk_coe_fn
- \+/\- *lemma* one_def
- \- *lemma* quotient_out'_eq_coe_fn
- \+/\- *def* measure.ae_eq_setoid
- \+/\- *def* mk
- \+/\- *def* const

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* integral_non_ae_measurable
- \+/\- *lemma* integral_congr_ae
- \+/\- *lemma* integral_eq_lintegral_of_nonneg_ae
- \+/\- *lemma* integral_to_real
- \+ *lemma* tendsto_integral_approx_on_univ_of_measurable
- \+/\- *lemma* integral_add_measure
- \+ *lemma* integral_map_of_measurable
- \+/\- *lemma* integral_map
- \- *lemma* integral_non_measurable
- \- *lemma* tendsto_integral_approx_on_univ
- \- *lemma* integral_add_measure'

Modified src/measure_theory/haar_measure.lean


Modified src/measure_theory/integration.lean
- \+/\- *lemma* lintegral_mono_ae
- \+/\- *lemma* lintegral_congr_ae
- \+/\- *lemma* lintegral_congr
- \+/\- *lemma* set_lintegral_congr
- \+ *lemma* lintegral_add'
- \+ *lemma* lintegral_const_mul''
- \+ *lemma* lintegral_mul_const''
- \+ *lemma* lintegral_eq_zero_iff'
- \+ *lemma* tendsto_lintegral_of_dominated_convergence'
- \+ *lemma* lintegral_map'

Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* refl
- \+/\- *lemma* trans
- \+/\- *lemma* continuous_on.interval_integrable
- \+/\- *lemma* continuous_on.interval_integrable_of_Icc
- \+/\- *lemma* filter.tendsto.eventually_interval_integrable_ae
- \+/\- *lemma* filter.tendsto.eventually_interval_integrable
- \+ *lemma* integral_non_ae_measurable
- \+/\- *lemma* integral_comp_add_right
- \+/\- *lemma* integral_comp_mul_right
- \+/\- *lemma* integral_comp_neg
- \+/\- *lemma* measure_integral_sub_linear_is_o_of_tendsto_ae
- \+/\- *lemma* integral_has_strict_fderiv_at_of_tendsto_ae
- \+/\- *lemma* integral_has_strict_fderiv_at
- \+/\- *lemma* integral_has_strict_deriv_at_of_tendsto_ae_right
- \+/\- *lemma* integral_has_strict_deriv_at_right
- \+/\- *lemma* integral_has_strict_deriv_at_of_tendsto_ae_left
- \+/\- *lemma* integral_has_strict_deriv_at_left
- \+/\- *lemma* integral_has_fderiv_at_of_tendsto_ae
- \+/\- *lemma* integral_has_fderiv_at
- \+/\- *lemma* fderiv_integral_of_tendsto_ae
- \+/\- *lemma* fderiv_integral
- \+/\- *lemma* integral_has_deriv_at_of_tendsto_ae_right
- \+/\- *lemma* integral_has_deriv_at_right
- \+/\- *lemma* deriv_integral_of_tendsto_ae_right
- \+/\- *lemma* deriv_integral_right
- \+/\- *lemma* integral_has_deriv_at_of_tendsto_ae_left
- \+/\- *lemma* integral_has_deriv_at_left
- \+/\- *lemma* deriv_integral_of_tendsto_ae_left
- \+/\- *lemma* deriv_integral_left
- \+/\- *lemma* integral_has_fderiv_within_at_of_tendsto_ae
- \+/\- *lemma* integral_has_fderiv_within_at
- \+/\- *lemma* fderiv_within_integral_of_tendsto_ae
- \+/\- *lemma* integral_has_deriv_within_at_of_tendsto_ae_right
- \+/\- *lemma* integral_has_deriv_within_at_right
- \+/\- *lemma* deriv_within_integral_of_tendsto_ae_right
- \+/\- *lemma* deriv_within_integral_right
- \+/\- *lemma* integral_has_deriv_within_at_of_tendsto_ae_left
- \+/\- *lemma* integral_has_deriv_within_at_left
- \+/\- *lemma* deriv_within_integral_of_tendsto_ae_left
- \+/\- *lemma* deriv_within_integral_left
- \- *lemma* integral_non_measurable

Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable.ae_measurable
- \+/\- *lemma* integrable.mono
- \+/\- *lemma* integrable.mono'
- \+/\- *lemma* integrable.congr'
- \+/\- *lemma* integrable_congr'
- \+/\- *lemma* integrable.congr
- \+/\- *lemma* integrable_congr
- \+/\- *lemma* integrable_norm_iff
- \+/\- *lemma* integrable_mk
- \+/\- *lemma* mk_to_fun
- \+ *lemma* integrable_zero_measure
- \- *lemma* integrable.measurable
- \- *lemma* measurable.integrable_zero

Modified src/measure_theory/lp_space.lean
- \+/\- *lemma* mem_ℒp_of_snorm_lt_top
- \+/\- *lemma* snorm_add_le

Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/prod.lean
- \+ *lemma* ae_measurable.prod_swap
- \+ *lemma* ae_measurable.integral_prod_right'
- \+ *lemma* ae_measurable.prod_mk_left
- \+ *lemma* lintegral_prod'
- \+ *lemma* lintegral_prod_symm'
- \+ *lemma* has_finite_integral_prod_iff'
- \+/\- *lemma* integrable_prod_iff
- \+/\- *lemma* integrable_prod_iff'
- \+/\- *lemma* integral_fn_integral_add
- \+/\- *lemma* integral_fn_integral_sub

Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* integrable_on_empty
- \+/\- *lemma* integrable_on_finite_union
- \+/\- *lemma* integrable_on_finset_union
- \+ *lemma* ae_measurable_indicator_iff
- \+/\- *lemma* integrable_indicator_iff
- \+/\- *lemma* measure.finite_at_filter.integrable_at_filter
- \+/\- *lemma* measure.finite_at_filter.integrable_at_filter_of_tendsto_ae
- \+/\- *lemma* measure.finite_at_filter.integrable_at_filter_of_tendsto
- \+/\- *lemma* integral_indicator
- \+ *lemma* continuous_on.ae_measurable
- \+/\- *lemma* continuous_on.integrable_on_compact

Modified src/measure_theory/simple_func_dense.lean




## [2021-01-05 10:34:59](https://github.com/leanprover-community/mathlib/commit/8f9f5ca)
chore(linear_algebra/alternating): Use `have` instead of `simp only` ([#5618](https://github.com/leanprover-community/mathlib/pull/5618))
This makes the proof easier to read and less fragile to lemma changes.
#### Estimated changes
Modified src/linear_algebra/alternating.lean




## [2021-01-05 06:08:53](https://github.com/leanprover-community/mathlib/commit/78dc23f)
chore(scripts/*): rename files of the style linter ([#5605](https://github.com/leanprover-community/mathlib/pull/5605))
The style linter has been doing a bit more than just checking for
copyright headers, module docstrings, or line lengths.
So I thought it made sense to reflect that in the filenames.
#### Estimated changes
Modified .github/workflows/build.yml


Deleted scripts/lint-copy-mod-doc.sh


Renamed scripts/lint-copy-mod-doc.py to scripts/lint-style.py


Created scripts/lint-style.sh


Renamed scripts/copy-mod-doc-exceptions.txt to scripts/style-exceptions.txt


Renamed scripts/update-copy-mod-doc-exceptions.sh to scripts/update-style-exceptions.sh


Modified scripts/update_nolints.sh




## [2021-01-05 03:19:32](https://github.com/leanprover-community/mathlib/commit/6dcfa5c)
chore(scripts): update nolints.txt ([#5615](https://github.com/leanprover-community/mathlib/pull/5615))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2021-01-04 23:56:31](https://github.com/leanprover-community/mathlib/commit/12921e9)
feat(tactic/simps): some improvements ([#5541](https://github.com/leanprover-community/mathlib/pull/5541))
* `@[simps]` would previously fail if the definition is not a constructor application (with the suggestion to add option `{rhs_md := semireducible}` and maybe `simp_rhs := tt`). Now it automatically adds `{rhs_md := semireducible, simp_rhs := tt}` whenever it reaches this situation. 
* Remove all (now) unnecessary occurrences of `{rhs_md := semireducible}` from the library. There are still a couple left where the `simp_rhs := tt` is undesirable.
* `@[simps {simp_rhs := tt}]` now also applies `dsimp, simp` to the right-hand side of the lemmas it generates.
* Add some `@[simps]` in `category_theory/limits/cones.lean`
* `@[simps]` would not recursively apply projections of `prod` or `pprod`. This is now customizable with the `not_recursive` option.
* Add an option `trace.simps.debug` with some debugging information.
#### Estimated changes
Modified src/algebra/category/Algebra/limits.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Group/limits.lean


Modified src/algebraic_geometry/presheafed_space/has_colimits.lean


Modified src/category_theory/Fintype.lean


Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/currying.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/essential_image.lean


Modified src/category_theory/limits/cones.lean
- \+/\- *lemma* extend_ι
- \- *lemma* cones_obj
- \- *lemma* cones_map_app
- \- *lemma* cocones_obj
- \- *lemma* cocones_map_app
- \- *lemma* equivalence_of_reindexing_functor_obj
- \- *lemma* map_cone_X
- \- *lemma* map_cocone_X
- \- *lemma* map_cone_π
- \- *lemma* map_cocone_ι
- \- *lemma* cone_of_cocone_left_op_π_app
- \- *lemma* cocone_left_op_of_cone_ι_app
- \- *lemma* cone_left_op_of_cocone_π_app
- \+/\- *def* cone_of_cocone_left_op
- \+/\- *def* cocone_left_op_of_cone
- \+/\- *def* cocone_of_cone_left_op
- \+/\- *def* cone_left_op_of_cocone

Modified src/category_theory/limits/fubini.lean


Modified src/category_theory/limits/presheaf.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/split_coequalizer.lean


Modified src/category_theory/limits/shapes/types.lean


Modified src/category_theory/monad/algebra.lean


Modified src/category_theory/monad/coequalizer.lean


Modified src/category_theory/monad/limits.lean


Modified src/category_theory/monad/monadicity.lean


Modified src/category_theory/monoidal/CommMon_.lean


Modified src/category_theory/monoidal/Mon_.lean


Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/internal/functor_category.lean


Modified src/category_theory/monoidal/internal/limits.lean


Modified src/category_theory/monoidal/transport.lean


Modified src/category_theory/over.lean


Modified src/category_theory/pi/basic.lean


Modified src/category_theory/products/basic.lean


Modified src/category_theory/sigma/basic.lean


Modified src/category_theory/sites/sheaf_of_types.lean


Modified src/category_theory/sites/types.lean


Modified src/data/equiv/basic.lean


Modified src/order/omega_complete_partial_order.lean
- \+/\- *def* map

Modified src/tactic/simps.lean
- \- *lemma* {nm.append_suffix

Modified src/topology/category/CompHaus.lean


Modified src/topology/category/Profinite.lean


Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean


Modified test/simps.lean
- \- *lemma* specify.specify5_snd_snd.
- \+/\- *def* rfl2
- \+ *def* my_type_def
- \- *def* bar2
- \- *def* specify5



## [2021-01-04 22:10:37](https://github.com/leanprover-community/mathlib/commit/78d5bd3)
feat(analysis/normed_space/{finite_dimension, inner_product}): assorted finite-dimensionality lemmas ([#5580](https://github.com/leanprover-community/mathlib/pull/5580))
Two groups of lemmas about finite-dimensional normed spaces:
- normed spaces of the same finite dimension are continuously linearly equivalent (this is a continuation of [#5559](https://github.com/leanprover-community/mathlib/pull/5559))
- variations on the existing lemma `submodule.findim_add_inf_findim_orthogonal`, that the dimensions of a subspace and its orthogonal complement sum to the dimension of the full space.
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean
- \+ *theorem* finite_dimensional.nonempty_continuous_linear_equiv_of_findim_eq
- \+ *theorem* finite_dimensional.nonempty_continuous_linear_equiv_iff_findim_eq
- \+ *def* continuous_linear_equiv.of_findim_eq

Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* submodule.findim_add_inf_findim_orthogonal'
- \+ *lemma* submodule.findim_add_findim_orthogonal
- \+ *lemma* submodule.findim_add_findim_orthogonal'



## [2021-01-04 20:20:02](https://github.com/leanprover-community/mathlib/commit/7b825f2)
feat(linear_algebra/alternating): Add comp_alternating_map and lemmas ([#5476](https://github.com/leanprover-community/mathlib/pull/5476))
This is just `comp_multilinear_map` with the extra bundled proof
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *lemma* coe_comp_alternating_map
- \+ *lemma* comp_alternating_map_apply
- \+ *lemma* comp_multilinear_map_alternatization
- \+ *def* comp_alternating_map



## [2021-01-04 16:47:45](https://github.com/leanprover-community/mathlib/commit/2300b47)
chore(computability/*FA): remove unnecessary type variables ([#5613](https://github.com/leanprover-community/mathlib/pull/5613))
#### Estimated changes
Modified src/computability/DFA.lean


Modified src/computability/NFA.lean




## [2021-01-04 16:47:44](https://github.com/leanprover-community/mathlib/commit/9535f91)
feat(*): switch to lean 3.24 ([#5612](https://github.com/leanprover-community/mathlib/pull/5612))
#### Estimated changes
Modified leanpkg.toml




## [2021-01-04 16:47:42](https://github.com/leanprover-community/mathlib/commit/7d0b988)
chore(data/equiv/basic): Add refl / symm / trans lemmas for equiv_congr ([#5609](https://github.com/leanprover-community/mathlib/pull/5609))
We already have this triplet of lemmas for `sum_congr` and `sigma_congr`.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv_congr_refl
- \+ *lemma* equiv_congr_symm
- \+ *lemma* equiv_congr_trans



## [2021-01-04 16:47:40](https://github.com/leanprover-community/mathlib/commit/50beef2)
feat(data/set/basic): more lemmas about `set.pi` ([#5603](https://github.com/leanprover-community/mathlib/pull/5603))
#### Estimated changes
Modified src/data/pi.lean
- \+ *lemma* one_def

Modified src/data/set/basic.lean
- \+ *lemma* pi_univ
- \+ *lemma* pi_congr
- \+ *lemma* singleton_pi'
- \+ *lemma* union_pi
- \+ *lemma* pi_inter_compl
- \+ *lemma* pi_update_of_not_mem
- \+ *lemma* pi_update_of_mem
- \+ *lemma* univ_pi_update
- \+ *lemma* univ_pi_update_univ

Modified src/data/set/intervals/pi.lean
- \+ *lemma* pi_univ_Ioc_update_left
- \+ *lemma* pi_univ_Ioc_update_right
- \+ *lemma* disjoint_pi_univ_Ioc_update_left_right
- \+ *lemma* pi_univ_Ioc_update_union



## [2021-01-04 12:04:36](https://github.com/leanprover-community/mathlib/commit/3669cb3)
feat(data/real/ennreal): add `ennreal.prod_lt_top` ([#5602](https://github.com/leanprover-community/mathlib/pull/5602))
Also add `with_top.can_lift`, `with_top.mul_lt_top`, and `with_top.prod_lt_top`.
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+ *lemma* prod_lt_top

Modified src/algebra/ordered_ring.lean
- \+ *lemma* mul_lt_top

Modified src/data/real/ennreal.lean
- \+/\- *lemma* mul_ne_top
- \+ *lemma* prod_lt_top

Modified src/order/bounded_lattice.lean




## [2021-01-04 08:50:41](https://github.com/leanprover-community/mathlib/commit/4150136)
chore(logic/function): generalize `rel_update_iff` to `forall_update_iff` ([#5601](https://github.com/leanprover-community/mathlib/pull/5601))
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *lemma* forall_update_iff
- \- *lemma* rel_update_iff

Modified src/order/basic.lean




## [2021-01-04 08:50:39](https://github.com/leanprover-community/mathlib/commit/6acf99e)
fix(data/nat/basic): fix typos in docstrings ([#5592](https://github.com/leanprover-community/mathlib/pull/5592))
#### Estimated changes
Modified src/data/nat/basic.lean




## [2021-01-04 05:36:22](https://github.com/leanprover-community/mathlib/commit/afbf47d)
feat(data/*, order/*) supporting lemmas for characterising well-founded complete lattices ([#5446](https://github.com/leanprover-community/mathlib/pull/5446))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* eq_singleton_iff_nonempty_unique_mem
- \+ *theorem* not_nonempty_iff_eq_empty

Modified src/data/finset/lattice.lean
- \+ *lemma* sup_closed_of_sup_closed
- \+ *lemma* sup_eq_Sup
- \+ *lemma* inf_eq_Inf

Modified src/data/set/basic.lean
- \+ *lemma* eq_singleton_iff_nonempty_unique_mem

Modified src/data/set/finite.lean
- \+ *theorem* finite.preimage_embedding

Modified src/order/complete_lattice.lean
- \+ *lemma* eq_singleton_top_of_Inf_eq_top_of_nonempty
- \+ *lemma* eq_singleton_bot_of_Sup_eq_bot_of_nonempty

Modified src/order/rel_iso.lean
- \+ *lemma* map_inf
- \+ *lemma* map_sup



## [2021-01-04 02:31:40](https://github.com/leanprover-community/mathlib/commit/2434023)
chore(scripts): update nolints.txt ([#5598](https://github.com/leanprover-community/mathlib/pull/5598))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2021-01-03 23:19:01](https://github.com/leanprover-community/mathlib/commit/1503cf8)
doc(overview): add dynamics and `measure.pi` ([#5597](https://github.com/leanprover-community/mathlib/pull/5597))
#### Estimated changes
Modified docs/overview.yaml




## [2021-01-03 23:18:59](https://github.com/leanprover-community/mathlib/commit/4fcf65c)
fix(tactic/rcases): fix rcases? goal alignment ([#5576](https://github.com/leanprover-community/mathlib/pull/5576))
This fixes a bug in which `rcases?` will not align the goals correctly
in the same manner as `rcases`, leading to a situation where the hint
produced by `rcases?` does not work in `rcases`.
Also fixes a bug where missing names will be printed as `[anonymous]`
instead of `_`.
Fixes [#2794](https://github.com/leanprover-community/mathlib/pull/2794)
#### Estimated changes
Modified src/tactic/rcases.lean


Modified test/rcases.lean




## [2021-01-03 23:18:57](https://github.com/leanprover-community/mathlib/commit/96948e4)
feat(measure_theory): almost everywhere measurable functions ([#5568](https://github.com/leanprover-community/mathlib/pull/5568))
This PR introduces a notion of almost everywhere measurable function, i.e., a function which coincides almost everywhere with a measurable function, and builds a basic API around the notion. It will then be used in [#5510](https://github.com/leanprover-community/mathlib/pull/5510) to extend the Bochner integral. The main new definition in the PR is `h : ae_measurable f μ`. It comes with `h.mk f` building a measurable function that coincides almost everywhere with `f` (these assertions are respectively `h.measurable_mk` and `h.ae_eq_mk`).
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* ae_measurable.ennreal_rpow_const

Modified src/measure_theory/borel_space.lean
- \+ *lemma* ae_measurable.max
- \+ *lemma* ae_measurable.min
- \+ *lemma* continuous.ae_measurable2
- \+ *lemma* ae_measurable.smul
- \+ *lemma* ae_measurable.const_smul
- \+ *lemma* ae_measurable_const_smul_iff
- \+ *lemma* ae_measurable.mul
- \+ *lemma* ae_measurable.inv
- \+ *lemma* ae_measurable.sub
- \+ *lemma* ae_measurable_comp_iff_of_closed_embedding
- \+ *lemma* ae_measurable.edist
- \+ *lemma* ae_measurable.ennreal_coe
- \+ *lemma* ae_measurable.to_real
- \+ *lemma* ae_measurable.ennreal_mul
- \+ *lemma* ae_measurable.norm
- \+ *lemma* ae_measurable.nnnorm
- \+ *lemma* ae_measurable.ennnorm
- \+ *lemma* ae_measurable_smul_const
- \- *lemma* measurable.ennreal_add

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_of_not_nonempty

Modified src/measure_theory/measure_space.lean
- \+ *lemma* map_mono
- \+ *lemma* ae_eq_set
- \+ *lemma* ae_restrict_iff'
- \+ *lemma* ae_smul_measure_iff
- \+ *lemma* ae_eq_comp
- \+ *lemma* restrict_apply_of_is_null_measurable
- \+ *lemma* measurable.ae_measurable
- \+ *lemma* measurable_mk
- \+ *lemma* ae_eq_mk
- \+ *lemma* congr
- \+ *lemma* mono_measure
- \+ *lemma* add_measure
- \+ *lemma* smul_measure
- \+ *lemma* comp_measurable
- \+ *lemma* prod_mk
- \+ *lemma* is_null_measurable
- \+ *lemma* ae_measurable_congr
- \+ *lemma* ae_measurable_add_measure_iff
- \+ *lemma* ae_measurable_const
- \+ *lemma* ae_measurable_smul_measure_iff
- \+ *lemma* measurable.comp_ae_measurable
- \+ *theorem* is_null_measurable_iff_ae
- \+ *theorem* is_null_measurable_iff_sandwich
- \+ *def* ae_measurable
- \+ *def* mk



## [2021-01-03 23:18:53](https://github.com/leanprover-community/mathlib/commit/2967793)
feat(data/option/basic): join and associated lemmas ([#5426](https://github.com/leanprover-community/mathlib/pull/5426))
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* join_eq_some
- \+ *lemma* join_ne_none
- \+ *lemma* join_ne_none'
- \+ *lemma* bind_id_eq_join
- \+ *lemma* join_eq_join
- \+ *lemma* bind_eq_bind
- \+ *lemma* bind_map_comm
- \+ *lemma* join_map_eq_map_join
- \+ *lemma* join_join
- \+ *lemma* mem_of_mem_join

Modified src/data/option/defs.lean
- \+ *def* join



## [2021-01-03 23:18:51](https://github.com/leanprover-community/mathlib/commit/d04e034)
feat(measure_theory/interval_integral): FTC-2 ([#4945](https://github.com/leanprover-community/mathlib/pull/4945))
The second fundamental theorem of calculus and supporting lemmas
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean
- \+ *theorem* constant_of_has_deriv_right_zero
- \+ *theorem* constant_of_deriv_within_zero
- \+ *theorem* eq_of_has_deriv_right_eq
- \+ *theorem* eq_of_deriv_within_eq

Modified src/measure_theory/interval_integral.lean
- \+ *lemma* continuous_on.interval_integrable_of_Icc
- \+ *theorem* differentiable_on_integral_of_continuous
- \+ *theorem* continuous_on_integral_of_continuous
- \+ *theorem* integral_eq_sub_of_has_deriv_right_of_le
- \+ *theorem* integral_eq_sub_of_has_deriv_right
- \+ *theorem* integral_eq_sub_of_has_deriv_at'
- \+ *theorem* integral_eq_sub_of_has_deriv_at
- \+ *theorem* integral_deriv_eq_sub



## [2021-01-03 20:40:21](https://github.com/leanprover-community/mathlib/commit/46c35cc)
fix(algebra/module/basic): Do not attach the ℕ and ℤ `is_scalar_tower` and `smul_comm_class` instances to a specific definition of smul ([#5509](https://github.com/leanprover-community/mathlib/pull/5509))
These instances are in `Prop`, so the more the merrier.
Without this change, these instances are not available for alternative ℤ-module definitions.
An example of one of these alternate definitions is `linear_map.semimodule`, which provide a second non-defeq ℤ-module structure alongside `add_comm_group.int_module`.
With this PR, both semimodule structures are shown to satisfy `smul_comm_class` and `is_scalar_tower`; while before it, only `add_comm_group.int_module` was shown to satisfy these.
This PR makes the following work:
```lean
example {R : Type*} {M₁ M₂ M₃ : Type*}
  [comm_semiring R]
  [add_comm_monoid M₁] [semimodule R M₁]
  [add_comm_monoid M₂] [semimodule R M₂]
  [add_comm_monoid M₃] [semimodule R M₃]
(f : M₁ →ₗ[R] M₂ →ₗ[R] M₃) (x : M₁) (n : ℕ) : f (n • x) = n • f x :=
by simp
```
#### Estimated changes
Modified src/algebra/module/basic.lean




## [2021-01-03 18:36:11](https://github.com/leanprover-community/mathlib/commit/e1138b0)
feat(measure_theory/lp_space): snorm is zero iff the function is zero ae ([#5595](https://github.com/leanprover-community/mathlib/pull/5595))
Adds three lemmas, one for both directions of the iff, `snorm_zero_ae` and `snorm_eq_zero`, and the iff lemma `snorm_eq_zero_iff`.
#### Estimated changes
Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm_measure_zero_of_pos
- \+ *lemma* snorm_measure_zero_of_exponent_zero
- \+ *lemma* snorm_measure_zero_of_neg
- \+ *lemma* snorm_eq_zero_of_ae_zero
- \+ *lemma* snorm_eq_zero_of_ae_zero'
- \+ *lemma* ae_eq_zero_of_snorm_eq_zero
- \+ *lemma* snorm_eq_zero_iff



## [2021-01-03 16:58:07](https://github.com/leanprover-community/mathlib/commit/ae2c857)
feat(measure_theory/lp_space): add triangle inequality for the Lp seminorm ([#5594](https://github.com/leanprover-community/mathlib/pull/5594))
#### Estimated changes
Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm_add_le



## [2021-01-03 16:58:05](https://github.com/leanprover-community/mathlib/commit/384ba88)
feat(computability/*FA): Deterministic and Nondeterministic Finite Automata ([#5038](https://github.com/leanprover-community/mathlib/pull/5038))
Definition and equivalence of NFA's and DFA's
#### Estimated changes
Created src/computability/DFA.lean
- \+ *def* eval_from
- \+ *def* eval
- \+ *def* accepts

Created src/computability/NFA.lean
- \+ *lemma* mem_step_set
- \+ *lemma* to_DFA_correct
- \+ *lemma* to_NFA_eval_from_match
- \+ *lemma* to_NFA_correct
- \+ *def* step_set
- \+ *def* eval_from
- \+ *def* eval
- \+ *def* accepts
- \+ *def* to_DFA
- \+ *def* to_NFA



## [2021-01-03 14:06:47](https://github.com/leanprover-community/mathlib/commit/eb6d5f1)
feat(analysis/normed_space/basic): basic facts about the sphere ([#5590](https://github.com/leanprover-community/mathlib/pull/5590))
Basic lemmas about the sphere in a normed group or normed space.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *lemma* smul_nat_eq_zero
- \+ *lemma* eq_zero_of_smul_two_eq_zero
- \+ *lemma* eq_zero_of_eq_neg
- \+ *lemma* ne_neg_of_ne_zero

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* mem_sphere_iff_norm
- \+ *lemma* mem_sphere_zero_iff_norm
- \+ *lemma* norm_eq_of_mem_sphere
- \+ *lemma* nonzero_of_mem_sphere
- \+ *lemma* nonzero_of_mem_unit_sphere
- \+ *lemma* coe_neg_sphere
- \+ *lemma* ne_neg_of_mem_sphere
- \+ *lemma* ne_neg_of_mem_unit_sphere

Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* mem_closed_ball
- \+ *theorem* mem_sphere



## [2021-01-03 11:59:40](https://github.com/leanprover-community/mathlib/commit/0837fc3)
feat(measure_theory/pi): finite products of measures ([#5414](https://github.com/leanprover-community/mathlib/pull/5414))
See module doc of `measure_theory/pi.lean`
#### Estimated changes
Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_tprod_mk
- \+ *lemma* measurable_tprod_elim
- \+ *lemma* measurable_tprod_elim'
- \+ *lemma* is_measurable.tprod

Created src/measure_theory/pi.lean
- \+ *lemma* pi_premeasure_pi
- \+ *lemma* pi_premeasure_pi'
- \+ *lemma* pi_premeasure_pi_mono
- \+ *lemma* pi_premeasure_pi_eval
- \+ *lemma* pi_pi_le
- \+ *lemma* le_pi
- \+ *lemma* tprod_nil
- \+ *lemma* tprod_cons
- \+ *lemma* tprod_tprod
- \+ *lemma* tprod_tprod_le
- \+ *lemma* pi'_pi
- \+ *lemma* pi'_pi_le
- \+ *lemma* pi_caratheodory
- \+ *lemma* pi_pi
- \+ *def* pi_premeasure
- \+ *def* pi'



## [2021-01-03 08:56:55](https://github.com/leanprover-community/mathlib/commit/e350114)
feat(data/equiv/basic): rfl lemma for equiv_congr ([#5585](https://github.com/leanprover-community/mathlib/pull/5585))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv_congr_apply_apply



## [2021-01-03 05:59:33](https://github.com/leanprover-community/mathlib/commit/57c6d19)
feat(combinatorics/simple_graph): finitely many simple graphs on a finite type ([#5584](https://github.com/leanprover-community/mathlib/pull/5584))
Adds an `ext` lemma for simple graphs and an instance that there are finitely many if the vertex set is finite.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean




## [2021-01-03 05:59:31](https://github.com/leanprover-community/mathlib/commit/9fc7aa5)
feat(data/finset/basic): add `finset.piecewise_le_piecewise` ([#5572](https://github.com/leanprover-community/mathlib/pull/5572))
* add `finset.piecewise_le_piecewise` and `finset.piecewise_le_piecewise'`;
* add `finset.piecewise_compl`.
#### Estimated changes
Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/data/finset/basic.lean
- \+ *lemma* piecewise_le_piecewise'
- \+ *lemma* piecewise_le_piecewise

Modified src/data/fintype/basic.lean
- \+ *lemma* piecewise_compl



## [2021-01-03 02:24:46](https://github.com/leanprover-community/mathlib/commit/0a4fbd8)
chore(data/prod): add `prod.forall'` and `prod.exists'` ([#5570](https://github.com/leanprover-community/mathlib/pull/5570))
They work a bit better with curried functions.
#### Estimated changes
Modified src/data/prod.lean
- \+/\- *lemma* prod_map
- \+ *theorem* «forall»
- \+ *theorem* «exists»
- \+ *theorem* forall'
- \+ *theorem* exists'
- \- *theorem* prod.forall
- \- *theorem* prod.exists



## [2021-01-03 02:24:43](https://github.com/leanprover-community/mathlib/commit/0dc7a27)
feat(data/nat/fib): fib n is a strong divisibility sequence ([#5555](https://github.com/leanprover-community/mathlib/pull/5555))
#### Estimated changes
Modified src/data/nat/fib.lean
- \+ *lemma* fib_coprime_fib_succ
- \+ *lemma* fib_add
- \+ *lemma* gcd_fib_add_self
- \+ *lemma* gcd_fib_add_mul_self
- \+ *lemma* fib_gcd
- \+ *lemma* fib_dvd

Modified src/data/nat/gcd.lean
- \+ *lemma* gcd_add_mul_self



## [2021-01-03 02:24:41](https://github.com/leanprover-community/mathlib/commit/9f25244)
chore(data/finset/sort): upgrade `finset.mono_of_fin` to an `order_iso` ([#5495](https://github.com/leanprover-community/mathlib/pull/5495))
* Upgrade `finset.mono_of_fin` to an `order_embedding`.
* Drop some lemmas that now immediately follow from `order_embedding.*`.
* Upgrade `finset.mono_equiv_of_fin` to `order_iso`.
* Define `list.nodup.nth_le_equiv` and `list.sorted.nth_le_iso`.
* Upgrade `mono_equiv_of_fin` to an `order_iso`, make it `computable`.
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean


Modified src/combinatorics/composition.lean
- \+ *lemma* order_emb_of_fin_boundaries
- \+/\- *lemma* boundary_zero
- \- *lemma* mono_of_fin_boundaries
- \+/\- *def* boundary

Modified src/data/finset/basic.lean
- \+ *lemma* coe_fin_range

Modified src/data/finset/sort.lean
- \+ *lemma* coe_order_iso_of_fin_apply
- \+ *lemma* order_iso_of_fin_symm_apply
- \+ *lemma* order_emb_of_fin_apply
- \+ *lemma* range_order_emb_of_fin
- \+ *lemma* order_emb_of_fin_zero
- \+ *lemma* order_emb_of_fin_last
- \+ *lemma* order_emb_of_fin_singleton
- \+ *lemma* order_emb_of_fin_unique
- \+ *lemma* order_emb_of_fin_unique'
- \+ *lemma* order_emb_of_fin_eq_order_emb_of_fin_iff
- \- *lemma* mono_of_fin_strict_mono
- \- *lemma* mono_of_fin_bij_on
- \- *lemma* mono_of_fin_injective
- \- *lemma* mono_of_fin_zero
- \- *lemma* mono_of_fin_last
- \- *lemma* mono_of_fin_singleton
- \- *lemma* range_mono_of_fin
- \- *lemma* mono_of_fin_unique
- \- *lemma* mono_of_fin_unique'
- \- *lemma* mono_of_fin_eq_mono_of_fin_iff
- \+/\- *theorem* sort_sorted_lt
- \+ *def* order_iso_of_fin
- \+ *def* order_emb_of_fin
- \- *def* mono_of_fin

Modified src/data/fintype/sort.lean
- \+ *def* mono_equiv_of_fin

Created src/data/list/nodup_equiv_fin.lean
- \+ *lemma* coe_nth_le_equiv_apply
- \+ *lemma* coe_nth_le_equiv_symm_apply
- \+ *lemma* nth_le_mono
- \+ *lemma* nth_le_strict_mono
- \+ *lemma* coe_nth_le_iso_apply
- \+ *lemma* coe_nth_le_iso_symm_apply
- \+ *def* nth_le_equiv
- \+ *def* nth_le_iso

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* face_points'

Modified src/linear_algebra/multilinear.lean
- \+ *def* restr



## [2021-01-03 02:24:39](https://github.com/leanprover-community/mathlib/commit/9ea7e46)
feat(linear_algebra/alternating): Show the link to linear_independent ([#5477](https://github.com/leanprover-community/mathlib/pull/5477))
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *lemma* map_update_sum
- \+ *lemma* map_linear_dependent

Modified src/linear_algebra/multilinear.lean
- \+/\- *lemma* map_sum_finset_aux
- \+/\- *lemma* map_sum_finset
- \+/\- *lemma* map_sum
- \+ *lemma* map_update_sum



## [2021-01-03 02:24:36](https://github.com/leanprover-community/mathlib/commit/04f8fd7)
feat(group_theory/dihedral): add dihedral groups ([#5171](https://github.com/leanprover-community/mathlib/pull/5171))
Contains a subset of the content of [#1076](https://github.com/leanprover-community/mathlib/pull/1076) , but implemented slightly differently.
In [#1076](https://github.com/leanprover-community/mathlib/pull/1076), finite and infinite dihedral groups are implemented separately, but a side effect of what I did was that `dihedral 0` corresponds to the infinite dihedral group.
#### Estimated changes
Created src/group_theory/dihedral.lean
- \+ *lemma* r_mul_r
- \+ *lemma* r_mul_sr
- \+ *lemma* sr_mul_r
- \+ *lemma* sr_mul_sr
- \+ *lemma* one_def
- \+ *lemma* card
- \+ *lemma* r_one_pow
- \+ *lemma* r_one_pow_n
- \+ *lemma* sr_mul_self
- \+ *lemma* order_of_sr
- \+ *lemma* order_of_r_one
- \+ *lemma* order_of_r



## [2021-01-03 00:36:14](https://github.com/leanprover-community/mathlib/commit/ee2c963)
doc(overview): pluralization convention ([#5583](https://github.com/leanprover-community/mathlib/pull/5583))
Normalized pluralizations, according to the convention @PatrickMassot described
#### Estimated changes
Modified docs/overview.yaml




## [2021-01-03 00:36:12](https://github.com/leanprover-community/mathlib/commit/e698290)
doc(overview): Add alternating_map ([#5582](https://github.com/leanprover-community/mathlib/pull/5582))
#### Estimated changes
Modified docs/overview.yaml




## [2021-01-03 00:36:10](https://github.com/leanprover-community/mathlib/commit/1a39825)
doc(overview): combinatorics section ([#5581](https://github.com/leanprover-community/mathlib/pull/5581))
Added overview entries for simple graphs and some pigeonhole principles
#### Estimated changes
Modified docs/overview.yaml




## [2021-01-03 00:36:08](https://github.com/leanprover-community/mathlib/commit/5bff887)
doc(overview): add missing algebras to overview ([#5579](https://github.com/leanprover-community/mathlib/pull/5579))
#### Estimated changes
Modified docs/overview.yaml




## [2021-01-03 00:36:06](https://github.com/leanprover-community/mathlib/commit/e094606)
chore(topology/algebra/ordered,analysis/specific_limits): two more limits ([#5573](https://github.com/leanprover-community/mathlib/pull/5573))
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \+ *lemma* tendsto_pow_at_top_nhds_within_0_of_lt_1

Modified src/topology/algebra/ordered.lean
- \+ *lemma* filter.tendsto.div_at_top



## [2021-01-02 20:59:51](https://github.com/leanprover-community/mathlib/commit/aa88bb8)
feat(measure_theory/borel_space): the inverse of a closed embedding is measurable ([#5567](https://github.com/leanprover-community/mathlib/pull/5567))
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* preimage_inv_fun_of_mem
- \+ *lemma* preimage_inv_fun_of_not_mem

Modified src/measure_theory/borel_space.lean
- \+ *lemma* closed_embedding.measurable_inv_fun



## [2021-01-02 20:59:49](https://github.com/leanprover-community/mathlib/commit/a7d05c4)
chore(number_theory/bernoulli): refactor definition of bernoulli ([#5534](https://github.com/leanprover-community/mathlib/pull/5534))
A minor refactor of the definition of Bernoulli number, and I expanded the docstring.
#### Estimated changes
Modified src/number_theory/bernoulli.lean




## [2021-01-02 20:59:48](https://github.com/leanprover-community/mathlib/commit/12b5024)
feat(data/polynomial/erase_lead): add lemma erase_lead_card_support_eq ([#5529](https://github.com/leanprover-community/mathlib/pull/5529))
One further lemma to increase the API of `erase_lead`.  I use it to simplify the proof of the Liouville PR.  In particular, it is used in a step of the proof that you can "clear denominators" when evaluating a polynomial with integer coefficients at a rational number.
#### Estimated changes
Modified src/data/polynomial/erase_lead.lean
- \+ *lemma* erase_lead_card_support
- \+ *lemma* erase_lead_card_support'



## [2021-01-02 17:53:35](https://github.com/leanprover-community/mathlib/commit/fceb7c1)
chore(algebra/group,algebra/group_with_zero): a few more injective/surjective constructors ([#5547](https://github.com/leanprover-community/mathlib/pull/5547))
#### Estimated changes
Modified src/algebra/group/inj_surj.lean


Modified src/algebra/group_with_zero/basic.lean




## [2021-01-02 15:05:58](https://github.com/leanprover-community/mathlib/commit/e142c82)
feat(algebra/group/prod) Units of a product monoid ([#5563](https://github.com/leanprover-community/mathlib/pull/5563))
Just a simple seemingly missing def
#### Estimated changes
Modified src/algebra/group/prod.lean
- \+ *def* units



## [2021-01-02 10:18:26](https://github.com/leanprover-community/mathlib/commit/e35a703)
feat(algebra/ordered_{group,field}): more lemmas relating inv and mul inequalities ([#5561](https://github.com/leanprover-community/mathlib/pull/5561))
I also renamed `inv_le_iff_one_le_mul` to `inv_le_iff_one_le_mul'` for consistency with `div_le_iff` and `div_le_iff'` (unprimed lemmas involve multiplication on the right and primed lemmas involve multiplication on the left).
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/ordered_field.lean
- \+ *lemma* inv_pos_le_iff_one_le_mul
- \+ *lemma* inv_pos_le_iff_one_le_mul'
- \+ *lemma* inv_pos_lt_iff_one_lt_mul
- \+ *lemma* inv_pos_lt_iff_one_lt_mul'

Modified src/algebra/ordered_group.lean
- \+/\- *lemma* inv_le_iff_one_le_mul
- \+ *lemma* inv_le_iff_one_le_mul'
- \+ *lemma* inv_lt_iff_one_lt_mul
- \+ *lemma* inv_lt_iff_one_lt_mul'
- \+ *lemma* le_inv_iff_mul_le_one'
- \+ *lemma* lt_inv_iff_mul_lt_one
- \+ *lemma* lt_inv_iff_mul_lt_one'

Modified src/analysis/convex/cone.lean




## [2021-01-02 10:18:25](https://github.com/leanprover-community/mathlib/commit/f5f879e)
feat(linear_algebra/dimension): linear equiv iff eq dim ([#5559](https://github.com/leanprover-community/mathlib/pull/5559))
See related zulip discussion
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Classification.20of.20finite-dimensional.20vector.20spaces/near/221357275
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *lemma* linear_equiv_of_is_basis_comp
- \+ *lemma* linear_equiv_of_is_basis_refl
- \+ *lemma* linear_equiv_of_is_basis_trans_symm
- \+ *lemma* linear_equiv_of_is_basis_symm_trans
- \- *lemma* equiv_of_is_basis_comp
- \- *lemma* equiv_of_is_basis_refl
- \- *lemma* equiv_of_is_basis_trans_symm
- \- *lemma* equiv_of_is_basis_symm_trans
- \+ *def* linear_equiv_of_is_basis
- \+ *def* linear_equiv_of_is_basis'
- \- *def* equiv_of_is_basis
- \- *def* equiv_of_is_basis'

Modified src/linear_algebra/dimension.lean
- \+ *theorem* linear_equiv.lift_dim_eq
- \+ *theorem* nonempty_linear_equiv_of_lift_dim_eq
- \+ *theorem* nonempty_linear_equiv_of_dim_eq
- \+ *theorem* linear_equiv.nonempty_equiv_iff_lift_dim_eq
- \+ *theorem* linear_equiv.nonempty_equiv_iff_dim_eq
- \+ *def* linear_equiv.of_lift_dim_eq
- \+ *def* linear_equiv.of_dim_eq

Modified src/linear_algebra/finite_dimensional.lean
- \+ *theorem* nonempty_linear_equiv_of_findim_eq
- \+ *theorem* nonempty_linear_equiv_iff_findim_eq

Modified src/linear_algebra/matrix.lean




## [2021-01-02 10:18:22](https://github.com/leanprover-community/mathlib/commit/9f6300e)
chore(data/complex/basic): upgrade `complex.norm_sq` to a `monoid_with_zero_hom` ([#5553](https://github.com/leanprover-community/mathlib/pull/5553))
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* map_eq_zero
- \+/\- *lemma* map_inv'
- \+/\- *lemma* map_div

Modified src/analysis/normed_space/inner_product.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/data/complex/basic.lean
- \+ *lemma* norm_sq_apply
- \+/\- *lemma* norm_sq_zero
- \+/\- *lemma* norm_sq_one
- \+/\- *lemma* norm_sq_eq_zero
- \+/\- *lemma* norm_sq_mul
- \+/\- *def* norm_sq

Modified src/data/complex/is_R_or_C.lean
- \+/\- *lemma* norm_sq_eq_def'
- \+/\- *lemma* norm_sq_zero
- \+/\- *lemma* norm_sq_one
- \+/\- *def* norm_sq

Modified src/data/zsqrtd/gaussian_int.lean




## [2021-01-02 10:18:20](https://github.com/leanprover-community/mathlib/commit/9d3c05a)
feat(ring_theory/simple_module): simple modules and Schur's Lemma ([#5473](https://github.com/leanprover-community/mathlib/pull/5473))
Defines `is_simple_module` in terms of `is_simple_lattice`
Proves Schur's Lemma
Defines `division ring` structure on the endomorphism ring of a simple module
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *theorem* range_eq_bot

Created src/ring_theory/simple_module.lean
- \+ *theorem* is_simple_module.nontrivial
- \+ *theorem* injective_or_eq_zero
- \+ *theorem* injective_of_ne_zero
- \+ *theorem* surjective_or_eq_zero
- \+ *theorem* surjective_of_ne_zero
- \+ *theorem* bijective_or_eq_zero
- \+ *theorem* bijective_of_ne_zero



## [2021-01-02 10:18:18](https://github.com/leanprover-community/mathlib/commit/afc3f03)
feat(algebra/ordered_group): add linear_ordered_comm_group and linear_ordered_cancel_comm_monoid ([#5286](https://github.com/leanprover-community/mathlib/pull/5286))
We have `linear_ordered_add_comm_group` but we didn't have `linear_ordered_comm_group`. This PR adds it, as well as multiplicative versions of `canonically_ordered_add_monoid`, `canonically_linear_ordered_add_monoid` and `linear_ordered_cancel_add_comm_monoid`. I added multiplicative versions of the lemmas about these structures too. The motivation is that I want to slightly generalise the notion of a valuation.
[ also random other bits of tidying which I noticed along the way (docstring fixes, adding `norm_cast` attributes) ].
#### Estimated changes
Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_monoid.lean
- \+ *lemma* le_iff_exists_mul
- \+ *lemma* one_le
- \+ *lemma* bot_eq_one
- \+ *lemma* mul_eq_one_iff
- \+ *lemma* le_one_iff_eq
- \+ *lemma* one_lt_iff_ne_one
- \+ *lemma* exists_pos_mul_of_lt
- \+ *lemma* le_mul_left
- \+ *lemma* le_mul_right
- \+ *lemma* min_mul_mul_left
- \+ *lemma* min_mul_mul_right
- \+ *lemma* max_mul_mul_left
- \+ *lemma* max_mul_mul_right
- \+ *lemma* min_le_mul_of_one_le_right
- \+ *lemma* min_le_mul_of_one_le_left
- \+ *lemma* max_le_mul_of_one_le
- \- *lemma* le_iff_exists_add
- \- *lemma* zero_le
- \- *lemma* bot_eq_zero
- \- *lemma* add_eq_zero_iff
- \- *lemma* le_zero_iff_eq
- \- *lemma* zero_lt_iff_ne_zero
- \- *lemma* exists_pos_add_of_lt
- \- *lemma* le_add_left
- \- *lemma* le_add_right
- \- *lemma* min_add_add_left
- \- *lemma* min_add_add_right
- \- *lemma* max_add_add_left
- \- *lemma* max_add_add_right
- \- *lemma* min_le_add_of_nonneg_right
- \- *lemma* min_le_add_of_nonneg_left
- \- *lemma* max_le_add_of_nonneg



## [2021-01-02 07:10:53](https://github.com/leanprover-community/mathlib/commit/d94f0a2)
chore(data/list): a list sorted w.r.t. `(<)` has no duplicates ([#5550](https://github.com/leanprover-community/mathlib/pull/5550))
#### Estimated changes
Modified src/data/list/nodup.lean


Modified src/data/list/sort.lean


Modified src/order/rel_classes.lean
- \+ *lemma* ne_of_irrefl



## [2021-01-02 00:36:58](https://github.com/leanprover-community/mathlib/commit/409ea42)
chore(algebra/*): move some lemmas to `div_inv_monoid` ([#5552](https://github.com/leanprover-community/mathlib/pull/5552))
#### Estimated changes
Modified src/algebra/field.lean
- \- *lemma* mul_div_assoc'

Modified src/algebra/group/basic.lean
- \+ *lemma* mul_div_assoc
- \+ *lemma* mul_div_assoc'
- \+ *lemma* one_div
- \- *lemma* zero_sub

Modified src/algebra/group_with_zero/basic.lean
- \- *lemma* one_div
- \- *lemma* mul_div_assoc

Modified src/analysis/analytic/composition.lean


Modified src/data/complex/exponential.lean


Modified src/data/real/hyperreal.lean


Modified src/geometry/euclidean/monge_point.lean




## [2021-01-02 00:36:56](https://github.com/leanprover-community/mathlib/commit/06a11fd)
chore(data/fintype/card): generalize `equiv.prod_comp` to `function.bijective.prod_comp` ([#5551](https://github.com/leanprover-community/mathlib/pull/5551))
This way we can apply it to `add_equiv`, `mul_equiv`, `order_iso`, etc
without using `to_equiv`.
#### Estimated changes
Modified src/data/fintype/card.lean
- \+ *lemma* function.bijective.prod_comp



## [2021-01-02 00:36:54](https://github.com/leanprover-community/mathlib/commit/ea3815f)
feat(analysis/normed_space/inner_product): upgrade orthogonal projection to a continuous linear map ([#5543](https://github.com/leanprover-community/mathlib/pull/5543))
Upgrade the orthogonal projection, from a linear map `E →ₗ[𝕜] K` to a continuous linear map `E →L[𝕜] K`.
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* orthogonal_projection_fn_norm_sq
- \+ *lemma* orthogonal_projection_norm_le
- \+/\- *def* orthogonal_projection

Modified src/geometry/euclidean/basic.lean




## [2021-01-02 00:36:53](https://github.com/leanprover-community/mathlib/commit/b57d562)
feat(algebra/big_operators/nat_antidiagonal): add prod_antidiagonal_eq_prod_range_succ ([#5528](https://github.com/leanprover-community/mathlib/pull/5528))
Sometimes summing over nat.antidiagonal is nicer than summing over range(n+1).
#### Estimated changes
Modified src/algebra/big_operators/nat_antidiagonal.lean
- \+ *lemma* prod_antidiagonal_eq_prod_range_succ

Modified src/data/finset/basic.lean
- \+ *lemma* mem_range_succ_iff



## [2021-01-02 00:36:49](https://github.com/leanprover-community/mathlib/commit/c32efea)
feat(data/fin): there is at most one `order_iso` from `fin n` to `α` ([#5499](https://github.com/leanprover-community/mathlib/pull/5499))
* Define a `bounded_lattice` instance on `fin (n + 1)`.
* Prove that there is at most one `order_iso` from `fin n` to `α`.
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* mk_lt_of_lt_coe
- \+ *lemma* mk_le_of_le_coe
- \+/\- *lemma* coe_last
- \+/\- *lemma* last_val
- \+/\- *lemma* coe_cast
- \+ *lemma* coe_order_iso_apply
- \+ *lemma* strict_mono_unique
- \+ *lemma* order_embedding_eq
- \+/\- *theorem* le_last
- \+/\- *def* last



## [2021-01-01 21:26:00](https://github.com/leanprover-community/mathlib/commit/8aa2332)
chore(*): golf some proofs ([#5548](https://github.com/leanprover-community/mathlib/pull/5548))
Parts of [#5539](https://github.com/leanprover-community/mathlib/pull/5539)
#### Estimated changes
Modified src/algebra/big_operators/ring.lean


Modified src/algebra/group_power/basic.lean


Modified src/algebra/ordered_ring.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/hofer.lean


Modified src/data/rat/cast.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* add_eq_top
- \+/\- *lemma* add_lt_top
- \+ *lemma* mul_lt_mul

Modified src/field_theory/adjoin.lean


Modified src/topology/instances/ennreal.lean




## [2021-01-01 21:25:58](https://github.com/leanprover-community/mathlib/commit/e0030ff)
chore(data/real/cau_seq): golf some proofs ([#5545](https://github.com/leanprover-community/mathlib/pull/5545))
#### Estimated changes
Modified src/data/real/cau_seq.lean
- \+/\- *lemma* abv_pow
- \+/\- *theorem* abv_one
- \- *theorem* abv_one'
- \+ *def* abv_hom



## [2021-01-01 19:02:10](https://github.com/leanprover-community/mathlib/commit/b542cfb)
chore(linear_algebra/basic): notation for span of a singleton ([#5538](https://github.com/leanprover-community/mathlib/pull/5538))
Notation `∙` (`\.`) for the span of a single element of a module, so one can write `R ∙ x` instead of `span R {x}`.  This in itself does not save so many keystrokes, but it also seems to be a bit more robust: it works in settings where previously one had to type `span R ({x} : set M)` because the type of the singleton was not recognised.
[Zulip 1](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/New.20linear.20algebra.20notation), [Zulip 2](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Notation.20for.20span)
#### Estimated changes
Modified src/algebra/algebra/operations.lean
- \+/\- *theorem* one_eq_span

Modified src/algebra/algebra/subalgebra.lean
- \+/\- *theorem* to_submodule_bot

Modified src/analysis/normed_space/hahn_banach.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *def* to_span_nonzero_singleton

Modified src/geometry/euclidean/monge_point.lean


Modified src/linear_algebra/affine_space/affine_subspace.lean


Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* mem_span_singleton_self
- \+/\- *lemma* nontrivial_span_singleton
- \+/\- *lemma* mem_span_singleton
- \+/\- *lemma* span_singleton_eq_range
- \+/\- *lemma* span_singleton_smul_le
- \+/\- *lemma* span_singleton_eq_bot
- \+/\- *lemma* span_singleton_le_iff_mem
- \+/\- *lemma* lt_add_iff_not_mem
- \+/\- *lemma* coord_self
- \+/\- *def* to_span_nonzero_singleton

Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_submodule_le_one_iff
- \+/\- *lemma* dim_submodule_le_one_iff'

Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/linear_pmap.lean




## [2021-01-01 15:24:16](https://github.com/leanprover-community/mathlib/commit/fcbaf62)
doc(lint/type_classes): add has_coe_to_fun linter ([#5546](https://github.com/leanprover-community/mathlib/pull/5546))
#### Estimated changes
Modified src/logic/basic.lean


Modified src/tactic/lint/type_classes.lean




## [2021-01-01 01:33:29](https://github.com/leanprover-community/mathlib/commit/d2bde11)
chore(scripts): update nolints.txt ([#5554](https://github.com/leanprover-community/mathlib/pull/5554))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt


