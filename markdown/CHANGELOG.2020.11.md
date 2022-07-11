## [2020-11-30 18:13:09](https://github.com/leanprover-community/mathlib/commit/c3f4d1b)
refactor(combinatorics/simple_graph): move simple graph files to their own folder ([#5154](https://github.com/leanprover-community/mathlib/pull/5154))
Move the files into one folder with the goal of integrating material from the branch [simple_graphs2](https://github.com/leanprover-community/mathlib/tree/simple_graphs2)
#### Estimated changes
Modified archive/100-theorems-list/83_friendship_graphs.lean


Renamed src/combinatorics/adj_matrix.lean to src/combinatorics/simple_graph/adj_matrix.lean


Renamed src/combinatorics/simple_graph.lean to src/combinatorics/simple_graph/basic.lean




## [2020-11-30 12:04:56](https://github.com/leanprover-community/mathlib/commit/e3a699e)
feat(linear_algebra/determinant): Show that the determinant is a multilinear map ([#5142](https://github.com/leanprover-community/mathlib/pull/5142))
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *def* det_row_multilinear



## [2020-11-30 10:52:36](https://github.com/leanprover-community/mathlib/commit/9f955fe)
feat(ring_theory/integral_closure): Cleanup interface for ring_hom.is_integral ([#5144](https://github.com/leanprover-community/mathlib/pull/5144))
#### Estimated changes
Modified src/ring_theory/integral_closure.lean
- \+ *lemma* ring_hom.is_integral_map
- \+ *lemma* ring_hom.is_integral_of_mem_closure
- \+ *lemma* ring_hom.is_integral_zero
- \+ *lemma* ring_hom.is_integral_one
- \+ *lemma* ring_hom.is_integral_add
- \+ *lemma* ring_hom.is_integral_neg
- \+ *lemma* ring_hom.is_integral_sub
- \+ *lemma* ring_hom.is_integral_mul
- \+ *lemma* ring_hom.is_integral_of_is_integral_mul_unit
- \+/\- *lemma* ring_hom.is_integral_trans
- \+ *lemma* ring_hom.is_integral_of_surjective
- \+/\- *lemma* is_integral_of_surjective
- \+ *lemma* ring_hom.is_integral_tower_bot_of_is_integral
- \+ *lemma* ring_hom.is_integral_quotient_of_is_integral
- \+/\- *lemma* is_integral_quotient_of_is_integral
- \- *lemma* is_integral_of_surjective'
- \- *lemma* is_integral_tower_bot_of_is_integral'
- \- *lemma* is_integral_quotient_of_is_integral'
- \+/\- *theorem* is_integral_of_mem_closure
- \+/\- *theorem* is_integral_mul
- \+/\- *theorem* is_integral_of_is_integral_mul_unit
- \- *theorem* is_integral_of_is_integral_mul_unit'

Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/localization.lean
- \+ *lemma* ring_hom.is_integral_elem_localization_at_leading_coeff
- \+/\- *theorem* is_integral_localization_at_leading_coeff
- \- *theorem* is_integral_elem_localization_at_leading_coeff'



## [2020-11-29 02:33:01](https://github.com/leanprover-community/mathlib/commit/1f1ba58)
feat(category_theory/limits): reflexive coequalizers ([#5123](https://github.com/leanprover-community/mathlib/pull/5123))
Adds reflexive coequalizers. These are useful for [#5118](https://github.com/leanprover-community/mathlib/pull/5118) as well as for some monadicity theorems and other results.
#### Estimated changes
Created src/category_theory/limits/shapes/reflexive.lean
- \+ *lemma* is_reflexive_pair.mk'
- \+ *lemma* is_coreflexive_pair.mk'
- \+ *lemma* section_comp_left
- \+ *lemma* section_comp_right
- \+ *lemma* left_comp_retraction
- \+ *lemma* right_comp_retraction
- \+ *lemma* is_kernel_pair.is_reflexive_pair
- \+ *lemma* is_reflexive_pair.swap
- \+ *lemma* is_coreflexive_pair.swap
- \+ *lemma* has_coequalizer_of_common_section
- \+ *lemma* has_equalizer_of_common_retraction



## [2020-11-29 01:19:16](https://github.com/leanprover-community/mathlib/commit/5866812)
chore(scripts): update nolints.txt ([#5143](https://github.com/leanprover-community/mathlib/pull/5143))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-28 21:16:44](https://github.com/leanprover-community/mathlib/commit/fe7b407)
feat(tactic/explode): display exploded proofs as widgets ([#4718](https://github.com/leanprover-community/mathlib/pull/4718))
[#4094](https://github.com/leanprover-community/mathlib/pull/4094). This is a more advanced version of the expandable `#explode` diagram implemented in the [Mathematica-Lean Link](http://robertylewis.com/leanmm/lean_mm.pdf). The widget adds features such as jumping to definitions and exploding constants occurring in a proof term subsequently. Note that right now the [\<details\>](https://developer.mozilla.org/en-US/docs/Web/HTML/Element/details) tag simply hides the information. "Exploding on request" requires a bit more refactoring on `#explode` itself and is still on the way. 
Example usage:`#explode_widget iff_true_intro`. 
![explode_widget](https://user-images.githubusercontent.com/22624072/96630999-7cb62780-1361-11eb-977d-3eb34039ab41.png)
#### Estimated changes
Modified src/tactic/explode.lean


Created src/tactic/explode_widget.lean




## [2020-11-28 19:38:23](https://github.com/leanprover-community/mathlib/commit/ec82227)
chore(group_theory/perm/sign): Add swap_mul_involutive ([#5141](https://github.com/leanprover-community/mathlib/pull/5141))
This is just a bundled version of swap_mul_self_mul
#### Estimated changes
Modified src/group_theory/perm/sign.lean
- \+ *lemma* swap_mul_involutive



## [2020-11-28 17:42:18](https://github.com/leanprover-community/mathlib/commit/916bf74)
feat(category_theory/limits): images, equalizers and pullbacks imply functorial images ([#5140](https://github.com/leanprover-community/mathlib/pull/5140))
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean




## [2020-11-28 17:42:16](https://github.com/leanprover-community/mathlib/commit/b1d8b89)
chore(algebra/char_p): refactor char_p ([#5132](https://github.com/leanprover-community/mathlib/pull/5132))
#### Estimated changes
Renamed src/algebra/char_p.lean to src/algebra/char_p/basic.lean
- \+/\- *lemma* char_p.cast_card_eq_zero
- \+ *theorem* char_p.congr
- \+ *theorem* spec
- \+ *theorem* eq
- \+ *theorem* of_eq
- \+ *theorem* eq_iff
- \+ *theorem* dvd
- \+/\- *theorem* add_pow_char_of_commute
- \+/\- *theorem* add_pow_char_pow_of_commute
- \+/\- *theorem* add_pow_char
- \+/\- *theorem* add_pow_char_pow
- \+/\- *theorem* frobenius_nat_cast
- \- *theorem* ring_char.spec
- \- *theorem* ring_char.eq

Created src/algebra/char_p/default.lean


Created src/algebra/char_p/pi.lean


Created src/algebra/char_p/quotient.lean
- \+ *theorem* quotient

Created src/algebra/char_p/subring.lean


Modified src/algebra/invertible.lean


Modified src/data/matrix/char_p.lean


Modified src/data/zmod/basic.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/field_theory/perfect_closure.lean


Modified src/representation_theory/maschke.lean


Modified src/ring_theory/polynomial/basic.lean




## [2020-11-28 16:26:44](https://github.com/leanprover-community/mathlib/commit/137163a)
feat(analysis/normed_space/dual): Fréchet-Riesz representation for the dual of a Hilbert space ([#4379](https://github.com/leanprover-community/mathlib/pull/4379))
This PR defines `to_dual` which maps an element `x` of an inner product space to `λ y, ⟪x, y⟫`. We also give the Fréchet-Riesz representation, which states that every element of the dual of a Hilbert space `E` has the form `λ u, ⟪x, u⟫` for some `x : E`.
#### Estimated changes
Modified docs/overview.yaml


Modified docs/references.bib


Modified docs/undergrad.yaml


Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* linear_map.norm_apply_of_isometry
- \+ *def* continuous_linear_equiv.of_isometry

Modified src/analysis/normed_space/dual.lean
- \+ *lemma* to_dual'_apply
- \+ *lemma* norm_to_dual'_apply
- \+ *lemma* to_dual'_isometry
- \+ *lemma* to_dual'_surjective
- \+ *lemma* to_dual_map_apply
- \+ *lemma* norm_to_dual_map_apply
- \+ *lemma* to_dual_map_isometry
- \+ *lemma* to_dual_map_injective
- \+ *lemma* ker_to_dual_map
- \+ *lemma* to_dual_map_eq_iff_eq
- \+ *lemma* range_to_dual_map
- \+ *lemma* to_dual_apply
- \+ *lemma* to_dual_eq_iff_eq
- \+ *lemma* to_dual_eq_iff_eq'
- \+ *lemma* norm_to_dual_apply
- \+ *lemma* norm_to_dual_symm_apply
- \+ *def* to_dual'
- \+ *def* to_dual_map
- \+ *def* to_dual
- \+ *def* isometric.to_dual

Modified src/analysis/normed_space/inner_product.lean
- \+/\- *def* sesq_form_of_inner

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* add_monoid_hom.isometry_of_norm

Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* ring_equiv_apply



## [2020-11-28 01:26:41](https://github.com/leanprover-community/mathlib/commit/801dea9)
chore(scripts): update nolints.txt ([#5139](https://github.com/leanprover-community/mathlib/pull/5139))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-27 23:09:55](https://github.com/leanprover-community/mathlib/commit/ba43f6f)
doc(field_theory/finite/basic): update doc-strings ([#5134](https://github.com/leanprover-community/mathlib/pull/5134))
The documentation mentions `finite_field.is_cyclic` that does not exist (probably replaced by `subgroup_units_cyclic` in `ring_theory.integral_domain`).
#### Estimated changes
Modified src/field_theory/finite/basic.lean




## [2020-11-27 23:09:53](https://github.com/leanprover-community/mathlib/commit/b6f2309)
chore({ring,group}_theory/free_*): Add of_injective ([#5131](https://github.com/leanprover-community/mathlib/pull/5131))
This adds:
* `free_abelian_group.of_injective`
* `free_ring.of_injective`
* `free_comm_ring.of_injective`
* `free_algebra.of_injective`
following up from dcbec39a5bf9af5c6e065eea185f8776ac537d3b
#### Estimated changes
Modified src/algebra/free_algebra.lean
- \+ *lemma* ι_injective

Modified src/group_theory/free_abelian_group.lean
- \+ *lemma* of_injective

Modified src/ring_theory/free_comm_ring.lean
- \+ *lemma* of_injective

Modified src/ring_theory/free_ring.lean
- \+ *lemma* of_injective



## [2020-11-27 21:26:04](https://github.com/leanprover-community/mathlib/commit/4a153ed)
feat(ring_theory/polynomials/cyclotomic): add lemmas about cyclotomic polynomials ([#5122](https://github.com/leanprover-community/mathlib/pull/5122))
Two lemmas about cyclotomic polynomials:
`cyclotomic_of_prime` is the explicit formula for `cyclotomic p R` when `p` is prime;
`cyclotomic_coeff_zero` shows that the constant term of `cyclotomic n R` is `1` if `2 ≤ n`. I will use this to prove that there are infinitely many prime congruent to `1` modulo `n`, for all `n`.
#### Estimated changes
Modified src/algebra/polynomial/big_operators.lean
- \+ *lemma* coeff_zero_prod

Modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* eq_cyclotomic_iff
- \+ *lemma* cyclotomic_eq_geom_series
- \+ *lemma* cyclotomic_coeff_zero



## [2020-11-27 21:26:02](https://github.com/leanprover-community/mathlib/commit/14f2096)
feat(ring_theory/jacobson): generalized nullstellensatz - polynomials over a Jacobson ring are Jacobson ([#4962](https://github.com/leanprover-community/mathlib/pull/4962))
The main statements are `is_jacobson_polynomial_iff_is_jacobson ` and `is_jacobson_mv_polynomial`, saying that `polynomial` and `mv_polynomial` both preserve jacobson property of rings. 
This second statement is in some sense a general form of the classical nullstellensatz, since in a Jacobson ring the intersection of maximal ideals containing an ideal will be exactly the radical of that ideal (and so I(V(I)) = I.radical).
#### Estimated changes
Modified src/data/polynomial/eval.lean


Modified src/ring_theory/jacobson.lean
- \+ *lemma* is_jacobson_of_is_integral'
- \+ *lemma* jacobson_bot_of_integral_localization
- \+ *lemma* is_jacobson_mv_polynomial_fin
- \+ *theorem* is_jacobson_polynomial_iff_is_jacobson

Modified src/ring_theory/jacobson_ideal.lean
- \+ *lemma* map_jacobson_of_bijective
- \+ *lemma* mem_jacobson_bot
- \+ *lemma* jacobson_bot_polynomial_le_Inf_map_maximal
- \+ *lemma* jacobson_bot_polynomial_of_jacobson_bot



## [2020-11-27 18:30:26](https://github.com/leanprover-community/mathlib/commit/8d3e93f)
chore(category_theory/limits): golf a proof ([#5133](https://github.com/leanprover-community/mathlib/pull/5133))
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean




## [2020-11-27 18:30:24](https://github.com/leanprover-community/mathlib/commit/fb70419)
feat(algebra/group/basic): simplify composed assoc ops ([#5031](https://github.com/leanprover-community/mathlib/pull/5031))
New lemmas:
`comp_assoc_left`
`comp_assoc_right`
`comp_mul_left`
`comp_add_left`
`comp_mul_right`
`comp_add_right`
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* comp_assoc_left
- \+ *lemma* comp_assoc_right
- \+ *lemma* comp_mul_left
- \+ *lemma* comp_mul_right



## [2020-11-27 18:30:22](https://github.com/leanprover-community/mathlib/commit/73a2fd3)
feat(ring_theory/witt_vector/init_tail): adding disjoint witt vectors ([#4835](https://github.com/leanprover-community/mathlib/pull/4835))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Created src/ring_theory/witt_vector/init_tail.lean
- \+ *lemma* coeff_select
- \+ *lemma* select_is_poly
- \+ *lemma* select_add_select_not
- \+ *lemma* coeff_add_of_disjoint
- \+ *lemma* init_add_tail
- \+ *lemma* init_init
- \+ *lemma* init_add
- \+ *lemma* init_mul
- \+ *lemma* init_neg
- \+ *lemma* init_sub
- \+ *lemma* init_is_poly
- \+ *def* select
- \+ *def* select_poly
- \+ *def* init
- \+ *def* tail



## [2020-11-27 15:35:32](https://github.com/leanprover-community/mathlib/commit/396487f)
feat(topology/separation): Adds t2_space instances for disjoint unions (sums and sigma types). ([#5113](https://github.com/leanprover-community/mathlib/pull/5113))
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *theorem* range_inl_union_range_inr
- \+ *theorem* range_inl_inter_range_inr
- \+ *theorem* range_inr_union_range_inl
- \+ *theorem* range_inr_inter_range_inl
- \+ *theorem* preimage_inl_range_inr
- \+ *theorem* preimage_inr_range_inl

Modified src/topology/constructions.lean
- \+ *lemma* is_open_range_inl
- \+ *lemma* is_open_range_inr

Modified src/topology/separation.lean
- \+ *lemma* separated_by_continuous
- \+ *lemma* separated_by_open_embedding



## [2020-11-27 14:25:59](https://github.com/leanprover-community/mathlib/commit/876481e)
feat(field_theory/separable): add separable_of_X_pow_sub_C and squarefree_of_X_pow_sub_C ([#5052](https://github.com/leanprover-community/mathlib/pull/5052))
I've added that `X ^ n - a` is separable, and so `squarefree`.
#### Estimated changes
Modified src/field_theory/separable.lean
- \+ *lemma* separable_X_pow_sub_C
- \+ *lemma* squarefree_X_pow_sub_C



## [2020-11-27 14:25:57](https://github.com/leanprover-community/mathlib/commit/c82b708)
feat(category_theory/sites): the canonical topology on a category ([#4928](https://github.com/leanprover-community/mathlib/pull/4928))
Explicitly construct the finest topology for which the given presheaves are sheaves, and specialise to construct the canonical topology. 
Also one or two tiny changes which should have been there before
#### Estimated changes
Created src/category_theory/sites/canonical.lean
- \+ *lemma* is_sheaf_for_bind
- \+ *lemma* is_sheaf_for_trans
- \+ *lemma* sheaf_for_finest_topology
- \+ *lemma* le_finest_topology
- \+ *lemma* is_sheaf_yoneda_obj
- \+ *lemma* is_sheaf_of_representable
- \+ *lemma* of_yoneda_is_sheaf
- \+ *def* finest_topology_single
- \+ *def* finest_topology
- \+ *def* canonical_topology
- \+ *def* subcanonical

Modified src/category_theory/sites/sheaf.lean


Modified src/category_theory/sites/sieves.lean




## [2020-11-27 11:58:59](https://github.com/leanprover-community/mathlib/commit/0ac414a)
feat(data/fin): Add pred_{le,lt}_pred_iff ([#5121](https://github.com/leanprover-community/mathlib/pull/5121))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* pred_le_pred_iff
- \+ *lemma* pred_lt_pred_iff



## [2020-11-27 11:58:57](https://github.com/leanprover-community/mathlib/commit/8acd296)
chore(topology/path_connected): move `proj_Icc` to a separate file ([#5120](https://github.com/leanprover-community/mathlib/pull/5120))
Also use `min` and `max` in the definition to make, e.g., the proof of the continuity trivial.
#### Estimated changes
Created src/data/set/intervals/proj_Icc.lean
- \+ *lemma* proj_Icc_of_le_left
- \+ *lemma* proj_Icc_left
- \+ *lemma* proj_Icc_of_right_le
- \+ *lemma* proj_Icc_right
- \+ *lemma* proj_Icc_of_mem
- \+ *lemma* proj_Icc_coe
- \+ *lemma* proj_Icc_surj_on
- \+ *lemma* proj_Icc_surjective
- \+ *lemma* range_proj_Icc
- \+ *lemma* monotone_proj_Icc
- \+ *lemma* Icc_extend_range
- \+ *lemma* Icc_extend_of_le_left
- \+ *lemma* Icc_extend_left
- \+ *lemma* Icc_extend_of_right_le
- \+ *lemma* Icc_extend_right
- \+ *lemma* Icc_extend_of_mem
- \+ *lemma* Icc_extend_coe
- \+ *lemma* Icc_extend_monotone
- \+ *def* proj_Icc
- \+ *def* Icc_extend

Created src/topology/algebra/ordered/proj_Icc.lean
- \+ *lemma* continuous_proj_Icc
- \+ *lemma* quotient_map_proj_Icc
- \+ *lemma* continuous_Icc_extend_iff
- \+ *lemma* continuous.Icc_extend

Modified src/topology/basic.lean
- \+ *lemma* topological_space_eq_iff

Modified src/topology/maps.lean
- \+ *lemma* quotient_map_iff

Modified src/topology/path_connected.lean
- \+ *lemma* coe_mk
- \+ *lemma* extend_of_le_zero
- \+ *lemma* extend_of_one_le
- \- *lemma* proj_I_I
- \- *lemma* proj_I_zero
- \- *lemma* proj_I_one
- \- *lemma* surjective_proj_I
- \- *lemma* range_proj_I
- \- *lemma* continuous_proj_I
- \- *lemma* continuous.I_extend
- \- *lemma* I_extend_extends
- \- *lemma* I_extend_zero
- \- *lemma* I_extend_one
- \- *lemma* I_extend_range
- \- *lemma* extend_le_zero
- \- *lemma* extend_one_le
- \+/\- *def* extend
- \- *def* proj_I
- \- *def* I_extend



## [2020-11-27 09:16:37](https://github.com/leanprover-community/mathlib/commit/238c58c)
chore(category_theory/limits): golf a proof ([#5130](https://github.com/leanprover-community/mathlib/pull/5130))
#### Estimated changes
Modified src/category_theory/arrow.lean
- \+/\- *lemma* w

Modified src/category_theory/limits/shapes/images.lean




## [2020-11-27 09:16:35](https://github.com/leanprover-community/mathlib/commit/ff2aeae)
feat(logic/relation): trans_gen closure ([#5129](https://github.com/leanprover-community/mathlib/pull/5129))
Mechanical conversion of `refl_trans_gen` lemmas for just `trans_gen`.
#### Estimated changes
Modified src/logic/relation.lean
- \+ *lemma* trans_gen_eq_self
- \+ *lemma* transitive_trans_gen
- \+ *lemma* trans_gen_idem
- \+ *lemma* trans_gen_lift
- \+ *lemma* trans_gen_lift'
- \+ *lemma* trans_gen_closed



## [2020-11-27 09:16:33](https://github.com/leanprover-community/mathlib/commit/af7ba87)
feat(data/polynomial/eval): eval₂ f x (p * X) = eval₂ f x p * x ([#5110](https://github.com/leanprover-community/mathlib/pull/5110))
Also generalize `polynomial.eval₂_mul_noncomm` and
`polynomial.eval₂_list_prod_noncomm`.
This PR uses `add_monoid_algebra.lift_nc` to golf some proofs about
`eval₂`. I'm not ready to replace the definition of `eval₂` yet (e.g.,
because it breaks dot notation everywhere), so I added
a lemma `eval₂_eq_lift_nc` instead.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* single_apply_mem
- \+ *lemma* range_single_subset

Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/basic.lean
- \+ *lemma* coeff_X_of_ne_one

Modified src/data/polynomial/eval.lean
- \+ *lemma* eval₂_eq_lift_nc
- \+/\- *lemma* eval₂_mul_noncomm
- \+ *lemma* eval₂_mul_X
- \+ *lemma* eval₂_X_mul
- \+ *lemma* eval₂_mul_C'
- \+/\- *lemma* eval₂_list_prod_noncomm
- \+/\- *def* eval₂_ring_hom'

Modified src/linear_algebra/eigenspace.lean




## [2020-11-27 09:16:31](https://github.com/leanprover-community/mathlib/commit/8e09111)
chore(order/basic): add `strict_mono_??cr_on.dual` and `dual_right` ([#5107](https://github.com/leanprover-community/mathlib/pull/5107))
We can use these to avoid `@strict_mono_??cr_on (order_dual α) (order_dual β)`.
#### Estimated changes
Modified src/order/basic.lean
- \+/\- *lemma* injective_of_lt_imp_ne



## [2020-11-27 09:16:29](https://github.com/leanprover-community/mathlib/commit/a106102)
chore(category_theory/iso): golf and name consistency ([#5096](https://github.com/leanprover-community/mathlib/pull/5096))
Minor changes: makes the names consistent and simplifies proofs
#### Estimated changes
Modified src/category_theory/isomorphism.lean
- \+/\- *lemma* comp_inv_eq
- \+ *lemma* eq_comp_inv
- \- *lemma* comp_is_iso_eq



## [2020-11-27 09:16:27](https://github.com/leanprover-community/mathlib/commit/d078950)
feat(linear_algebra/bilinear_form): equivalence with matrices, given a basis ([#5095](https://github.com/leanprover-community/mathlib/pull/5095))
This PR defines the equivalence between bilinear forms on an arbitrary module and matrices, given a basis of that module. It updates the existing equivalence between bilinear forms on `n → R` so that the overall structure of the file matches that of `linear_algebra.matrix`, i.e. there are two pairs of equivs, one for `n → R` and one for any `M` with a basis.
Changes:
 - `bilin_form_equiv_matrix`, `bilin_form.to_matrix` and `matrix.to_bilin_form` have been consolidated as linear equivs `bilin_form.to_matrix'` and `matrix.to_bilin'`. Other declarations have been renamed accordingly.
 - `quadratic_form.to_matrix` and `matrix.to_quadratic_form` are renamed by analogy to `quadratic_form.to_matrix'` and `matrix.to_quadratic_form'`
 - replaced some `classical.decidable_eq` in lemma statements with instance parameters, because otherwise we have to use `congr` to apply these lemmas when a `decidable_eq` instance is available
Additions:
 - `bilin_form.to_matrix` and `matrix.to_bilin`: given a basis, the equivalences between bilinear forms on any module and matrices
 - lemmas from `to_matrix'` and `to_bilin'` have been ported to `to_matrix` and `to_bilin`
 - `bilin_form.congr`, a dependency of `bilin_form.to_matrix`, states that `bilin_form R M` and `bilin_form R M'` are linearly equivalent if `M` and `M'` are
 - assorted lemmas involving `std_basis`
Deletions:
 - `bilin_form.to_matrix_smul`: use `linear_equiv.map_smul` instead
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+/\- *lemma* linear_independent_std_basis
- \+/\- *lemma* is_basis_std_basis
- \+/\- *lemma* is_basis_fun₀
- \+/\- *lemma* is_basis_fun
- \+ *lemma* is_basis_fun_repr

Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* comp_comp
- \+ *lemma* congr_apply
- \+ *lemma* congr_symm
- \+ *lemma* congr_comp
- \+ *lemma* comp_congr
- \+ *lemma* ext_basis
- \+ *lemma* sum_repr_mul_repr_mul
- \+ *lemma* matrix.to_bilin'_aux_std_basis
- \+ *lemma* to_bilin'_aux_to_matrix_aux
- \+ *lemma* bilin_form.to_matrix_aux_std_basis
- \+ *lemma* matrix.to_bilin'_aux_eq
- \+ *lemma* matrix.to_bilin'_apply
- \+ *lemma* matrix.to_bilin'_std_basis
- \+ *lemma* bilin_form.to_matrix'_symm
- \+ *lemma* matrix.to_bilin'_symm
- \+ *lemma* matrix.to_bilin'_to_matrix'
- \+ *lemma* bilin_form.to_matrix'_to_bilin'
- \+ *lemma* bilin_form.to_matrix'_apply
- \+ *lemma* bilin_form.to_matrix'_comp
- \+ *lemma* bilin_form.to_matrix'_comp_left
- \+ *lemma* bilin_form.to_matrix'_comp_right
- \+ *lemma* bilin_form.mul_to_matrix'_mul
- \+ *lemma* bilin_form.mul_to_matrix'
- \+ *lemma* bilin_form.to_matrix'_mul
- \+ *lemma* matrix.to_bilin'_comp
- \+ *lemma* is_basis.equiv_fun_symm_std_basis
- \+/\- *lemma* bilin_form.to_matrix_apply
- \+ *lemma* matrix.to_bilin_apply
- \+ *lemma* bilinear_form.to_matrix_aux_eq
- \+ *lemma* bilin_form.to_matrix_symm
- \+ *lemma* matrix.to_bilin_symm
- \+ *lemma* matrix.to_bilin_is_basis_fun
- \+ *lemma* bilin_form.to_matrix_is_basis_fun
- \+ *lemma* matrix.to_bilin_to_matrix
- \+ *lemma* bilin_form.to_matrix_to_bilin
- \+/\- *lemma* bilin_form.to_matrix_comp
- \+/\- *lemma* bilin_form.to_matrix_comp_left
- \+/\- *lemma* bilin_form.to_matrix_comp_right
- \+/\- *lemma* bilin_form.mul_to_matrix_mul
- \+/\- *lemma* bilin_form.mul_to_matrix
- \+/\- *lemma* bilin_form.to_matrix_mul
- \+ *lemma* matrix.to_bilin_comp
- \+ *lemma* is_adjoint_pair_to_bilin'
- \+ *lemma* is_adjoint_pair_to_bilin
- \- *lemma* matrix.to_bilin_form_apply
- \- *lemma* bilin_form.to_matrix_smul
- \- *lemma* to_matrix_to_bilin_form
- \- *lemma* to_bilin_form_to_matrix
- \- *lemma* matrix.to_bilin_form_comp
- \- *lemma* matrix_is_adjoint_pair_bilin_form
- \+ *def* congr
- \+ *def* matrix.to_bilin'_aux
- \+ *def* bilin_form.to_matrix_aux
- \+ *def* bilin_form.to_matrix'
- \+ *def* matrix.to_bilin'
- \- *def* matrix.to_bilin_formₗ
- \- *def* matrix.to_bilin_form
- \- *def* bilin_form.to_matrixₗ
- \- *def* bilin_form.to_matrix
- \- *def* bilin_form_equiv_matrix

Modified src/linear_algebra/matrix.lean


Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* quadratic_form.to_matrix'_smul
- \+ *lemma* to_matrix'_comp
- \- *lemma* quadratic_form.to_matrix_smul
- \- *lemma* to_matrix_comp
- \+ *def* matrix.to_quadratic_form'
- \+ *def* quadratic_form.to_matrix'
- \+/\- *def* discr
- \- *def* matrix.to_quadratic_form
- \- *def* quadratic_form.to_matrix



## [2020-11-27 09:16:24](https://github.com/leanprover-community/mathlib/commit/c06c616)
feat(number_theory/arithmetic_function): Moebius inversion ([#5047](https://github.com/leanprover-community/mathlib/pull/5047))
Changes the way that zeta works with coercion
Proves Möbius inversion for functions to a general `comm_ring`
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* sum_int_cast

Modified src/number_theory/arithmetic_function.lean
- \+ *lemma* nat_coe_nat
- \+/\- *lemma* nat_coe_apply
- \+ *lemma* int_coe_int
- \+/\- *lemma* int_coe_apply
- \+/\- *lemma* coe_coe
- \+/\- *lemma* zeta_apply
- \+/\- *lemma* zeta_apply_ne
- \+/\- *lemma* pmul_zeta
- \+/\- *lemma* zeta_pmul
- \+/\- *lemma* is_multiplicative_zeta
- \+ *lemma* coe_moebius_mul_coe_zeta
- \+ *lemma* coe_zeta_mul_coe_moebius
- \+ *lemma* moebius_mul_coe_zeta
- \+ *lemma* coe_zeta_mul_moebius
- \+ *lemma* coe_zeta_unit
- \+ *lemma* inv_zeta_unit
- \- *lemma* moebius_mul_zeta
- \- *lemma* zeta_mul_moebius
- \+ *theorem* coe_zeta_mul_apply
- \+ *theorem* coe_mul_zeta_apply
- \+/\- *theorem* zeta_mul_apply
- \+/\- *theorem* mul_zeta_apply
- \+ *theorem* sum_eq_iff_sum_moebius_eq
- \+/\- *def* zeta
- \+ *def* zeta_unit



## [2020-11-27 09:16:21](https://github.com/leanprover-community/mathlib/commit/2bda184)
feat(field_theory): Prove the Galois correspondence ([#4786](https://github.com/leanprover-community/mathlib/pull/4786))
The proof leverages existing results from field_theory/fixed.lean and field_theory/primitive_element.lean.
We define Galois as normal + separable. Proving the various equivalent characterizations of Galois extensions is yet to be done.
#### Estimated changes
Modified docs/overview.yaml


Modified src/algebra/algebra/basic.lean


Modified src/data/fintype/basic.lean


Modified src/data/set/basic.lean
- \+ *lemma* eq_of_inclusion_surjective

Modified src/field_theory/adjoin.lean
- \+ *lemma* bot_equiv_def
- \+ *lemma* top_equiv_def
- \+ *def* subalgebra.equiv_of_eq

Modified src/field_theory/fixed.lean
- \+ *theorem* to_alg_hom_bijective
- \+ *def* to_alg_hom_equiv

Created src/field_theory/galois.lean
- \+ *lemma* integral
- \+ *lemma* separable
- \+ *lemma* normal
- \+ *lemma* intermediate_field.adjoin_simple.card_aut_eq_findim
- \+ *lemma* card_aut_eq_findim
- \+ *lemma* findim_fixed_field_eq_card
- \+ *lemma* le_iff_le
- \+ *lemma* card_fixing_subgroup_eq_findim
- \+ *lemma* is_separable_splitting_field
- \+ *theorem* fixing_subgroup_fixed_field
- \+ *theorem* fixed_field_fixing_subgroup
- \+ *def* is_galois
- \+ *def* fixed_field
- \+ *def* fixing_subgroup
- \+ *def* fixing_subgroup_equiv
- \+ *def* intermediate_field_equiv_subgroup
- \+ *def* galois_insertion_intermediate_field_subgroup
- \+ *def* galois_coinsertion_intermediate_field_subgroup

Modified src/field_theory/normal.lean
- \+ *lemma* normal.tower_top_of_normal

Modified src/linear_algebra/finite_dimensional.lean




## [2020-11-27 06:39:09](https://github.com/leanprover-community/mathlib/commit/2f939e9)
chore(data/equiv/basic): redefine `set.bij_on.equiv` ([#5128](https://github.com/leanprover-community/mathlib/pull/5128))
Now `set.bij_on.equiv` works for any `h : set.bij_on f s t`. The old
behaviour can be achieved using `(equiv.set_univ _).symm.trans _`.
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/data/finset/sort.lean


Modified src/data/set/function.lean
- \+ *theorem* bij_on.bijective



## [2020-11-27 06:39:07](https://github.com/leanprover-community/mathlib/commit/4715d99)
chore(data/set/function): add 3 trivial lemmas ([#5127](https://github.com/leanprover-community/mathlib/pull/5127))
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* strict_mono_incr_on.comp
- \+ *lemma* strict_mono.comp_strict_mono_incr_on
- \+ *theorem* inj_on.eq_iff



## [2020-11-27 06:39:04](https://github.com/leanprover-community/mathlib/commit/c1edbdd)
chore(data/complex/exponential): golf 2 proofs ([#5126](https://github.com/leanprover-community/mathlib/pull/5126))
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* abs_le_one_iff_mul_self_le_one

Modified src/data/complex/exponential.lean




## [2020-11-27 06:39:02](https://github.com/leanprover-community/mathlib/commit/cb9e5cf)
doc(data/equiv/basic): improve docstring of `equiv.sum_equiv_sigma_bool` ([#5119](https://github.com/leanprover-community/mathlib/pull/5119))
Also slightly improve defeq of the `to_fun` field by using `sum.elim` instead of a custom `match`.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *def* sum_equiv_sigma_bool



## [2020-11-27 06:39:00](https://github.com/leanprover-community/mathlib/commit/d3cc993)
chore(data/pprod): Add pprod.mk.eta ([#5114](https://github.com/leanprover-community/mathlib/pull/5114))
This is exactly the same as prod.mk.eta
#### Estimated changes
Created src/data/pprod.lean
- \+ *lemma* pprod.mk.eta



## [2020-11-27 04:12:29](https://github.com/leanprover-community/mathlib/commit/2c5d4a3)
chore(order/rel_iso): add a few lemmas ([#5106](https://github.com/leanprover-community/mathlib/pull/5106))
* add lemmas `order_iso.apply_eq_iff_eq` etc;
* define `order_iso.symm`.
#### Estimated changes
Modified src/data/finsupp/lattice.lean


Modified src/order/galois_connection.lean


Modified src/order/rel_iso.lean
- \+ *lemma* apply_le_apply
- \+ *lemma* apply_lt_apply
- \+ *lemma* apply_eq_iff_eq
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+ *lemma* order_iso.map_top
- \+ *lemma* order_embedding.map_inf_le
- \+ *lemma* order_iso.map_inf
- \+ *lemma* order_embedding.le_map_sup
- \+ *lemma* order_iso.map_sup
- \- *lemma* rel_iso.map_top
- \- *lemma* rel_embedding.map_inf_le
- \- *lemma* rel_iso.map_inf
- \- *lemma* rel_embedding.le_map_sup
- \- *lemma* rel_iso.map_sup
- \+ *def* symm



## [2020-11-27 01:21:04](https://github.com/leanprover-community/mathlib/commit/1a8089e)
chore(scripts): update nolints.txt ([#5125](https://github.com/leanprover-community/mathlib/pull/5125))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-26 17:19:04](https://github.com/leanprover-community/mathlib/commit/59717d6)
chore(data/sum): Add trivial simp lemmas ([#5112](https://github.com/leanprover-community/mathlib/pull/5112))
#### Estimated changes
Modified src/data/sum.lean
- \+ *lemma* elim_comp_inl
- \+ *lemma* elim_comp_inr
- \+ *lemma* elim_inl_inr
- \+ *lemma* comp_elim
- \+ *lemma* elim_comp_inl_inr



## [2020-11-26 09:59:56](https://github.com/leanprover-community/mathlib/commit/2d476e0)
chore(data/equiv/basic): Add comp_swap_eq_update ([#5091](https://github.com/leanprover-community/mathlib/pull/5091))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* swap_eq_update
- \+ *lemma* comp_swap_eq_update



## [2020-11-26 01:18:53](https://github.com/leanprover-community/mathlib/commit/98ebe5a)
chore(scripts): update nolints.txt ([#5117](https://github.com/leanprover-community/mathlib/pull/5117))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-25 16:13:58](https://github.com/leanprover-community/mathlib/commit/6e301c7)
chore(logic/function/basic): Add function.update_apply ([#5093](https://github.com/leanprover-community/mathlib/pull/5093))
This makes it easier to eliminate `dite`s in simple situations when only `ite` is needed.
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *lemma* update_apply



## [2020-11-25 15:09:50](https://github.com/leanprover-community/mathlib/commit/81207e0)
feat(algebra/triv_sq_zero_ext): trivial square-zero extension ([#5109](https://github.com/leanprover-community/mathlib/pull/5109))
#### Estimated changes
Created src/algebra/triv_sq_zero_ext.lean
- \+ *lemma* ext
- \+ *lemma* fst_inl
- \+ *lemma* snd_inl
- \+ *lemma* fst_inr
- \+ *lemma* snd_inr
- \+ *lemma* inl_injective
- \+ *lemma* inr_injective
- \+ *lemma* fst_zero
- \+ *lemma* snd_zero
- \+ *lemma* inl_zero
- \+ *lemma* inr_zero
- \+ *lemma* fst_add
- \+ *lemma* snd_add
- \+ *lemma* fst_neg
- \+ *lemma* snd_neg
- \+ *lemma* inl_add
- \+ *lemma* inr_add
- \+ *lemma* inl_fst_add_inr_snd_eq
- \+ *lemma* inl_neg
- \+ *lemma* inr_neg
- \+ *lemma* fst_smul
- \+ *lemma* snd_smul
- \+ *lemma* inr_smul
- \+ *lemma* fst_one
- \+ *lemma* snd_one
- \+ *lemma* inl_one
- \+ *lemma* fst_mul
- \+ *lemma* snd_mul
- \+ *lemma* inl_mul
- \+ *lemma* inl_mul_inl
- \+ *lemma* inl_mul_inr
- \+ *lemma* inr_mul_inl
- \+ *lemma* inr_mul_inr
- \+ *def* triv_sq_zero_ext
- \+ *def* inl
- \+ *def* inr
- \+ *def* fst
- \+ *def* snd
- \+ *def* inr_hom
- \+ *def* inl_hom
- \+ *def* fst_hom



## [2020-11-25 11:39:21](https://github.com/leanprover-community/mathlib/commit/4265f2c)
chore(data/int/basic): Add int.units_mul_self ([#5101](https://github.com/leanprover-community/mathlib/pull/5101))
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean


Modified src/data/int/basic.lean
- \+ *lemma* units_mul_self
- \+ *lemma* units_coe_mul_self

Modified src/linear_algebra/determinant.lean




## [2020-11-25 06:48:00](https://github.com/leanprover-community/mathlib/commit/0324935)
chore(data/equiv/basic): Add trivial simp lemma ([#5100](https://github.com/leanprover-community/mathlib/pull/5100))
With this in place, `⇑1 ∘ f` simplifies to `⇑f`
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* coe_one
- \+/\- *theorem* one_apply



## [2020-11-25 03:17:58](https://github.com/leanprover-community/mathlib/commit/0020077)
fix(algebra/ordered_group): remove workaround ([#5103](https://github.com/leanprover-community/mathlib/pull/5103))
The problem mentioned in the TODO has been solved so the workaround is no longer needed.
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \- *def* ordered_comm_group.mk'

Modified src/set_theory/game.lean




## [2020-11-25 01:28:51](https://github.com/leanprover-community/mathlib/commit/83f293e)
chore(scripts): update nolints.txt ([#5105](https://github.com/leanprover-community/mathlib/pull/5105))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-24 19:48:35](https://github.com/leanprover-community/mathlib/commit/7e66984)
fix(algebra/group_with_zero/power): remove duplicate lemmas ([#5083](https://github.com/leanprover-community/mathlib/pull/5083))
`pow_eq_zero` and `pow_eq_zero'` are syntactically equal, as are `pow_ne_zero` and `pow_ne_zero'`.
#### Estimated changes
Modified src/algebra/group_with_zero/power.lean
- \- *theorem* pow_eq_zero'
- \- *theorem* pow_ne_zero'

Modified src/ring_theory/unique_factorization_domain.lean




## [2020-11-24 13:18:42](https://github.com/leanprover-community/mathlib/commit/2ed4846)
chore(linear_algebra/multilinear_map): Add boring coercion lemmas copied from ring_hom ([#5099](https://github.com/leanprover-community/mathlib/pull/5099))
#### Estimated changes
Modified src/linear_algebra/multilinear.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_mk
- \+ *theorem* congr_fun
- \+ *theorem* congr_arg
- \+ *theorem* coe_inj
- \+ *theorem* ext_iff



## [2020-11-24 11:42:00](https://github.com/leanprover-community/mathlib/commit/943b129)
feat(analysis/special_functions/trigonometric): sin, cos, sinh, and cosh are infinitely smooth ([#5090](https://github.com/leanprover-community/mathlib/pull/5090))
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* times_cont_diff_sin
- \+ *lemma* times_cont_diff_cos
- \+ *lemma* times_cont_diff_sinh
- \+ *lemma* times_cont_diff_cosh
- \+/\- *lemma* measurable.ccos
- \+/\- *lemma* deriv_within_ccos
- \+/\- *lemma* deriv_ccos
- \+/\- *lemma* measurable.csin
- \+/\- *lemma* has_deriv_at.csin
- \+/\- *lemma* has_deriv_within_at.csin
- \+/\- *lemma* deriv_within_csin
- \+/\- *lemma* deriv_csin
- \+/\- *lemma* measurable.ccosh
- \+/\- *lemma* has_deriv_at.ccosh
- \+/\- *lemma* has_deriv_within_at.ccosh
- \+/\- *lemma* deriv_within_ccosh
- \+/\- *lemma* deriv_ccosh
- \+/\- *lemma* measurable.csinh
- \+/\- *lemma* has_deriv_at.csinh
- \+/\- *lemma* has_deriv_within_at.csinh
- \+/\- *lemma* deriv_within_csinh
- \+/\- *lemma* deriv_csinh
- \+ *lemma* has_fderiv_at.ccos
- \+ *lemma* has_fderiv_within_at.ccos
- \+ *lemma* fderiv_within_ccos
- \+ *lemma* fderiv_ccos
- \+ *lemma* times_cont_diff.ccos
- \+ *lemma* times_cont_diff_at.ccos
- \+ *lemma* times_cont_diff_on.ccos
- \+ *lemma* times_cont_diff_within_at.ccos
- \+ *lemma* has_fderiv_at.csin
- \+ *lemma* has_fderiv_within_at.csin
- \+ *lemma* fderiv_within_csin
- \+ *lemma* fderiv_csin
- \+ *lemma* times_cont_diff.csin
- \+ *lemma* times_cont_diff_at.csin
- \+ *lemma* times_cont_diff_on.csin
- \+ *lemma* times_cont_diff_within_at.csin
- \+ *lemma* has_fderiv_at.ccosh
- \+ *lemma* has_fderiv_within_at.ccosh
- \+ *lemma* fderiv_within_ccosh
- \+ *lemma* fderiv_ccosh
- \+ *lemma* times_cont_diff.ccosh
- \+ *lemma* times_cont_diff_at.ccosh
- \+ *lemma* times_cont_diff_on.ccosh
- \+ *lemma* times_cont_diff_within_at.ccosh
- \+ *lemma* has_fderiv_at.csinh
- \+ *lemma* has_fderiv_within_at.csinh
- \+ *lemma* fderiv_within_csinh
- \+ *lemma* fderiv_csinh
- \+ *lemma* times_cont_diff.csinh
- \+ *lemma* times_cont_diff_at.csinh
- \+ *lemma* times_cont_diff_on.csinh
- \+ *lemma* times_cont_diff_within_at.csinh
- \+/\- *lemma* measurable.cos
- \+/\- *lemma* deriv_within_cos
- \+/\- *lemma* deriv_cos
- \+/\- *lemma* measurable.sin
- \+/\- *lemma* has_deriv_at.sin
- \+/\- *lemma* has_deriv_within_at.sin
- \+/\- *lemma* deriv_within_sin
- \+/\- *lemma* deriv_sin
- \+/\- *lemma* measurable.cosh
- \+/\- *lemma* has_deriv_at.cosh
- \+/\- *lemma* has_deriv_within_at.cosh
- \+/\- *lemma* deriv_within_cosh
- \+/\- *lemma* deriv_cosh
- \+/\- *lemma* measurable.sinh
- \+/\- *lemma* has_deriv_at.sinh
- \+/\- *lemma* has_deriv_within_at.sinh
- \+/\- *lemma* deriv_within_sinh
- \+/\- *lemma* deriv_sinh
- \+ *lemma* has_fderiv_at.cos
- \+ *lemma* has_fderiv_within_at.cos
- \+ *lemma* fderiv_within_cos
- \+ *lemma* fderiv_cos
- \+ *lemma* times_cont_diff.cos
- \+ *lemma* times_cont_diff_at.cos
- \+ *lemma* times_cont_diff_on.cos
- \+ *lemma* times_cont_diff_within_at.cos
- \+ *lemma* has_fderiv_at.sin
- \+ *lemma* has_fderiv_within_at.sin
- \+ *lemma* fderiv_within_sin
- \+ *lemma* fderiv_sin
- \+ *lemma* times_cont_diff.sin
- \+ *lemma* times_cont_diff_at.sin
- \+ *lemma* times_cont_diff_on.sin
- \+ *lemma* times_cont_diff_within_at.sin
- \+ *lemma* has_fderiv_at.cosh
- \+ *lemma* has_fderiv_within_at.cosh
- \+ *lemma* fderiv_within_cosh
- \+ *lemma* fderiv_cosh
- \+ *lemma* times_cont_diff.cosh
- \+ *lemma* times_cont_diff_at.cosh
- \+ *lemma* times_cont_diff_on.cosh
- \+ *lemma* times_cont_diff_within_at.cosh
- \+ *lemma* has_fderiv_at.sinh
- \+ *lemma* has_fderiv_within_at.sinh
- \+ *lemma* fderiv_within_sinh
- \+ *lemma* fderiv_sinh
- \+ *lemma* times_cont_diff.sinh
- \+ *lemma* times_cont_diff_at.sinh
- \+ *lemma* times_cont_diff_on.sinh
- \+ *lemma* times_cont_diff_within_at.sinh



## [2020-11-24 09:15:42](https://github.com/leanprover-community/mathlib/commit/fe4abe0)
chore(algebra/lie/skew_adjoint): move logic for Lie algebras of skew-adjoint endomorphisms to own file ([#5098](https://github.com/leanprover-community/mathlib/pull/5098))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \- *lemma* bilin_form.is_skew_adjoint_bracket
- \- *lemma* skew_adjoint_lie_subalgebra_equiv_apply
- \- *lemma* skew_adjoint_lie_subalgebra_equiv_symm_apply
- \- *lemma* matrix.lie_transpose
- \- *lemma* matrix.is_skew_adjoint_bracket
- \- *lemma* mem_skew_adjoint_matrices_lie_subalgebra
- \- *lemma* skew_adjoint_matrices_lie_subalgebra_equiv_apply
- \- *lemma* skew_adjoint_matrices_lie_subalgebra_equiv_transpose_apply
- \- *lemma* mem_skew_adjoint_matrices_lie_subalgebra_unit_smul
- \- *def* skew_adjoint_lie_subalgebra
- \- *def* skew_adjoint_lie_subalgebra_equiv
- \- *def* skew_adjoint_matrices_lie_subalgebra
- \- *def* skew_adjoint_matrices_lie_subalgebra_equiv_transpose

Modified src/algebra/lie/classical.lean


Created src/algebra/lie/skew_adjoint.lean
- \+ *lemma* bilin_form.is_skew_adjoint_bracket
- \+ *lemma* skew_adjoint_lie_subalgebra_equiv_apply
- \+ *lemma* skew_adjoint_lie_subalgebra_equiv_symm_apply
- \+ *lemma* matrix.lie_transpose
- \+ *lemma* matrix.is_skew_adjoint_bracket
- \+ *lemma* mem_skew_adjoint_matrices_lie_subalgebra
- \+ *lemma* skew_adjoint_matrices_lie_subalgebra_equiv_apply
- \+ *lemma* skew_adjoint_matrices_lie_subalgebra_equiv_transpose_apply
- \+ *lemma* mem_skew_adjoint_matrices_lie_subalgebra_unit_smul
- \+ *def* skew_adjoint_lie_subalgebra
- \+ *def* skew_adjoint_lie_subalgebra_equiv
- \+ *def* skew_adjoint_matrices_lie_subalgebra
- \+ *def* skew_adjoint_matrices_lie_subalgebra_equiv_transpose



## [2020-11-24 02:14:31](https://github.com/leanprover-community/mathlib/commit/51e71e9)
chore(scripts): update nolints.txt ([#5097](https://github.com/leanprover-community/mathlib/pull/5097))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-23 23:33:18](https://github.com/leanprover-community/mathlib/commit/64b3e52)
feat(data/finset/basic): Finset subset induction ([#5087](https://github.com/leanprover-community/mathlib/pull/5087))
Induction on subsets of a given finset.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* induction_on'



## [2020-11-23 22:04:03](https://github.com/leanprover-community/mathlib/commit/434a34d)
feat(group_theory/perm/sign): Add swap_induction_on' ([#5092](https://github.com/leanprover-community/mathlib/pull/5092))
This also adds a docstring for swap_induction_on
#### Estimated changes
Modified src/group_theory/perm/sign.lean
- \+ *lemma* swap_induction_on'



## [2020-11-23 22:04:01](https://github.com/leanprover-community/mathlib/commit/2a49f4e)
feat(algebra/lie/direct_sum): direct sums of Lie modules ([#5063](https://github.com/leanprover-community/mathlib/pull/5063))
There are three things happening here:
  1. introduction of definitions of direct sums for Lie modules,
  2. introduction of definitions of morphisms, equivs for Lie modules,
  3. splitting out extant definition of direct sums for Lie algebras
     into a new file.
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* coe_mk
- \+ *lemma* coe_to_linear_map
- \+ *lemma* map_lie'
- \+ *lemma* coe_injective
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* comp_apply
- \+ *lemma* comp_coe
- \+ *lemma* coe_to_lie_module_hom
- \+ *lemma* coe_to_linear_equiv
- \+ *lemma* one_apply
- \+ *lemma* refl_apply
- \+ *lemma* symm_symm
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+ *lemma* trans_apply
- \+ *lemma* symm_trans_apply
- \- *lemma* bracket_apply
- \+ *def* comp
- \+ *def* inverse
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans

Created src/algebra/lie/direct_sum.lean
- \+ *lemma* lie_module_bracket_apply
- \+ *lemma* bracket_apply
- \+ *def* lie_module_of
- \+ *def* lie_module_component
- \+ *def* lie_algebra_of
- \+ *def* lie_algebra_component



## [2020-11-23 19:56:57](https://github.com/leanprover-community/mathlib/commit/fee93e9)
feat(ring_theory/*): Various lemmas about ideals, quotients, and localizations ([#5046](https://github.com/leanprover-community/mathlib/pull/5046))
Lemmas needed for the proof that is_jacobson is preserved under taking polynomials.
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* eval₂_C_X
- \+/\- *lemma* map_injective
- \+ *lemma* map_surjective
- \+ *lemma* coe_map_ring_hom
- \+ *def* map_ring_hom

Modified src/group_theory/submonoid/operations.lean
- \+/\- *lemma* mem_map_of_mem

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* radical_bot_of_integral_domain
- \+ *lemma* bot_quotient_is_maximal_iff
- \+ *lemma* quotient_map_mk
- \+ *lemma* quotient_map_injective
- \+ *lemma* comp_quotient_map_eq_of_comp_eq

Modified src/ring_theory/ideal/over.lean
- \+ *lemma* is_maximal_of_is_integral_of_is_maximal_comap'
- \+ *lemma* is_maximal_comap_of_is_integral_of_is_maximal'

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_integral_of_mem_closure'
- \+ *lemma* is_integral_of_mem_closure''
- \+ *lemma* ring_hom.is_integral_trans
- \+ *lemma* is_integral_of_surjective'
- \+ *lemma* is_integral_tower_bot_of_is_integral'
- \+ *lemma* is_integral_quotient_of_is_integral'
- \+ *theorem* is_integral_of_is_integral_mul_unit'

Modified src/ring_theory/localization.lean
- \+ *lemma* surjective_quotient_map_of_maximal_of_localization
- \+ *lemma* is_integral_localization'
- \+ *theorem* is_integral_elem_localization_at_leading_coeff'

Modified src/ring_theory/non_zero_divisors.lean
- \+ *lemma* powers_le_non_zero_divisors_of_domain
- \+ *lemma* map_le_non_zero_divisors_of_injective

Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* polynomial_mem_ideal_of_coeff_mem_ideal
- \+ *lemma* eq_zero_of_polynomial_mem_map_range
- \+/\- *def* polynomial_quotient_equiv_quotient_polynomial



## [2020-11-23 17:02:17](https://github.com/leanprover-community/mathlib/commit/96a2038)
chore(linear_algebra/bilinear_form): cleanup ([#5049](https://github.com/leanprover-community/mathlib/pull/5049))
- Generalize some defs and lemmas to semimodules over semirings
- Define the equiv between `bilin_form` and `linear_map` analogously to `linear_map.to_matrix / matrix.to_lin`
- Mark appropriate lemmas as `simp`
- Fix overlong lines, match style guide in other places too
- Make use of variables consistent throughout the file
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt


Modified src/linear_algebra/bilinear_form.lean
- \+/\- *lemma* zero_left
- \+/\- *lemma* zero_right
- \+/\- *lemma* neg_left
- \+/\- *lemma* neg_right
- \+/\- *lemma* sub_left
- \+/\- *lemma* sub_right
- \+/\- *lemma* ext
- \+/\- *lemma* neg_apply
- \+/\- *lemma* smul_apply
- \+ *lemma* linear_map.to_bilin_aux_eq
- \+ *lemma* linear_map.to_bilin_symm
- \+ *lemma* bilin_form.to_lin_symm
- \+ *lemma* to_linear_map_apply
- \+/\- *lemma* map_sum_left
- \+/\- *lemma* map_sum_right
- \+/\- *lemma* comp_apply
- \+/\- *lemma* comp_injective
- \+/\- *lemma* lin_mul_lin_comp
- \+/\- *lemma* lin_mul_lin_comp_left
- \+/\- *lemma* lin_mul_lin_comp_right
- \+/\- *lemma* ortho_zero
- \+/\- *lemma* matrix.to_bilin_form_apply
- \+/\- *lemma* bilin_form.to_matrix_apply
- \+/\- *lemma* bilin_form.to_matrix_smul
- \+/\- *lemma* bilin_form.to_matrix_comp
- \+/\- *lemma* bilin_form.to_matrix_comp_left
- \+/\- *lemma* bilin_form.to_matrix_comp_right
- \+/\- *lemma* bilin_form.mul_to_matrix_mul
- \+/\- *lemma* bilin_form.mul_to_matrix
- \+/\- *lemma* bilin_form.to_matrix_mul
- \+/\- *lemma* to_matrix_to_bilin_form
- \+/\- *lemma* to_bilin_form_to_matrix
- \+/\- *lemma* neg
- \+/\- *lemma* is_adjoint_pair.eq
- \+/\- *lemma* is_adjoint_pair_zero
- \+/\- *lemma* is_adjoint_pair.add
- \+/\- *lemma* is_adjoint_pair.sub
- \+/\- *lemma* is_adjoint_pair.smul
- \+/\- *lemma* is_adjoint_pair.comp
- \+/\- *lemma* mem_is_pair_self_adjoint_submodule
- \+/\- *lemma* is_pair_self_adjoint_equiv
- \+/\- *lemma* is_skew_adjoint_iff_neg_self_adjoint
- \+/\- *lemma* mem_self_adjoint_submodule
- \+/\- *lemma* mem_skew_adjoint_submodule
- \+/\- *lemma* matrix.is_adjoint_pair_equiv
- \- *lemma* coe_fn_to_linear_map
- \+ *theorem* is_ortho_smul_left
- \+ *theorem* is_ortho_smul_right
- \- *theorem* ortho_smul_left
- \- *theorem* ortho_smul_right
- \+ *def* linear_map.to_bilin_aux
- \+/\- *def* linear_map.to_bilin
- \+ *def* bilin_form.to_lin
- \+/\- *def* comp
- \+/\- *def* lin_mul_lin
- \+/\- *def* matrix.to_bilin_formₗ
- \+/\- *def* matrix.to_bilin_form
- \+/\- *def* bilin_form.to_matrixₗ
- \+/\- *def* bilin_form.to_matrix
- \+/\- *def* bilin_form_equiv_matrix
- \+/\- *def* is_adjoint_pair
- \+/\- *def* is_pair_self_adjoint
- \+/\- *def* is_pair_self_adjoint_submodule
- \+/\- *def* is_skew_adjoint
- \+/\- *def* self_adjoint_submodule
- \+/\- *def* skew_adjoint_submodule
- \+/\- *def* matrix.is_adjoint_pair
- \+/\- *def* pair_self_adjoint_matrices_submodule
- \+/\- *def* self_adjoint_matrices_submodule
- \+/\- *def* skew_adjoint_matrices_submodule
- \- *def* to_linear_map
- \- *def* bilin_linear_map_equiv



## [2020-11-23 15:20:48](https://github.com/leanprover-community/mathlib/commit/270fc31)
fix(ring_theory/discrete_valuation_ring): docstring typos ([#5085](https://github.com/leanprover-community/mathlib/pull/5085))
Clarify one docstring and fix two others.
#### Estimated changes
Modified src/ring_theory/discrete_valuation_ring.lean
- \+ *theorem* to_unique_factorization_monoid
- \- *theorem* ufd



## [2020-11-23 13:47:52](https://github.com/leanprover-community/mathlib/commit/e8c8ce9)
chore(category_theory/limits): move product isomorphisms ([#5057](https://github.com/leanprover-community/mathlib/pull/5057))
This PR moves some constructions and lemmas from `monoidal/of_has_finite_products` (back) to `limits/shapes/binary_products`. 
This reverts some changes made in https://github.com/leanprover-community/mathlib/commit/18246ac427c62348e7ff854965998cd9878c7692#diff-95871ea16bec862dfc4359f812b624a7a98e87b8c31c034e8a6e792332edb646. In particular, the purpose of that PR was to minimise imports in particular relating to `finite_limits`, but moving these particular definitions back doesn't make the imports any worse in that sense - other than that `binary_products` now imports `terminal` which I think doesn't make the import graph much worse.  On the other hand, these definitions are useful outside of the context of monoidal categories so I think they do genuinely belong in `limits/`.
I also changed some proofs from `tidy` to `simp` or a term-mode proof, and removed a `simp` attribute from a lemma which was already provable by `simp`.
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* braid_natural
- \+ *lemma* prod.symmetry'
- \+ *lemma* prod.symmetry
- \+ *lemma* prod.pentagon
- \+ *lemma* prod.associator_naturality
- \+ *lemma* prod.left_unitor_hom_naturality
- \+ *lemma* prod.left_unitor_inv_naturality
- \+ *lemma* prod.right_unitor_hom_naturality
- \+ *lemma* prod_right_unitor_inv_naturality
- \+ *lemma* prod.triangle
- \+ *lemma* coprod.symmetry'
- \+ *lemma* coprod.symmetry
- \+ *lemma* coprod.pentagon
- \+ *lemma* coprod.associator_naturality
- \+ *lemma* coprod.triangle
- \+ *def* prod.braiding
- \+ *def* prod.associator
- \+ *def* prod.left_unitor
- \+ *def* prod.right_unitor
- \+ *def* coprod.braiding
- \+ *def* coprod.associator
- \+ *def* coprod.left_unitor
- \+ *def* coprod.right_unitor
- \+ *def* prod.functor_left_comp

Modified src/category_theory/monoidal/of_has_finite_products.lean
- \- *lemma* braid_natural
- \- *lemma* prod.symmetry'
- \- *lemma* prod.symmetry
- \- *lemma* prod.pentagon
- \- *lemma* prod.associator_naturality
- \- *lemma* prod.left_unitor_hom_naturality
- \- *lemma* prod.left_unitor_inv_naturality
- \- *lemma* prod.right_unitor_hom_naturality
- \- *lemma* prod_right_unitor_inv_naturality
- \- *lemma* prod.triangle
- \- *lemma* coprod.symmetry'
- \- *lemma* coprod.symmetry
- \- *lemma* coprod.pentagon
- \- *lemma* coprod.associator_naturality
- \- *lemma* coprod.triangle
- \- *def* prod.braiding
- \- *def* prod.associator
- \- *def* prod.functor_left_comp
- \- *def* prod.left_unitor
- \- *def* prod.right_unitor
- \- *def* coprod.braiding
- \- *def* coprod.associator
- \- *def* coprod.left_unitor
- \- *def* coprod.right_unitor



## [2020-11-23 13:47:50](https://github.com/leanprover-community/mathlib/commit/a71901f)
feat(category_theory/limits): explicit binary product functor in Type ([#5043](https://github.com/leanprover-community/mathlib/pull/5043))
Adds `binary_product_functor`, the explicit product functor in Type, and `binary_product_iso_prod` which shows it is isomorphic to the one picked by choice (this is helpful eg to show Type is cartesian closed).
I also edited the definitions a little to use existing machinery instead - this seems to make `simp` and `tidy` stronger when working with the explicit product cone; but they're definitionally the same as the old ones.
#### Estimated changes
Modified src/category_theory/limits/shapes/types.lean
- \+ *lemma* binary_product_cone_fst
- \+ *lemma* binary_product_cone_snd
- \+ *def* binary_product_cone
- \+ *def* binary_product_limit
- \+ *def* binary_product_functor
- \+ *def* binary_coproduct_cocone
- \+ *def* binary_coproduct_colimit
- \+ *def* binary_coproduct_colimit_cocone
- \+ *def* coproduct_colimit_cocone
- \- *def* binary_coproduct_limit_cone
- \- *def* coproduct_limit_cone



## [2020-11-23 13:47:48](https://github.com/leanprover-community/mathlib/commit/562be70)
feat(field_theory/separable): a separable polynomial is squarefree ([#5039](https://github.com/leanprover-community/mathlib/pull/5039))
I prove that a separable polynomial is squarefree.
#### Estimated changes
Modified src/field_theory/separable.lean
- \+ *lemma* separable.squarefree



## [2020-11-23 13:47:44](https://github.com/leanprover-community/mathlib/commit/3c1cf60)
feat(category_theory/sigma): disjoint union of categories ([#5020](https://github.com/leanprover-community/mathlib/pull/5020))
#### Estimated changes
Created src/category_theory/sigma/basic.lean
- \+ *lemma* comp_def
- \+ *lemma* assoc
- \+ *lemma* id_comp
- \+ *lemma* comp_id
- \+ *lemma* incl_obj
- \+ *lemma* nat_trans_app
- \+ *lemma* desc_map_mk
- \+ *lemma* incl_desc_hom_app
- \+ *lemma* incl_desc_inv_app
- \+ *lemma* desc_uniq_hom_app
- \+ *lemma* desc_uniq_inv_app
- \+ *lemma* map_obj
- \+ *lemma* map_map
- \+ *def* id
- \+ *def* comp
- \+ *def* incl
- \+ *def* nat_trans
- \+ *def* desc_map
- \+ *def* desc
- \+ *def* incl_desc
- \+ *def* desc_uniq
- \+ *def* nat_iso
- \+ *def* map
- \+ *def* incl_comp_map
- \+ *def* map_id
- \+ *def* map_comp
- \+ *def* sigma



## [2020-11-23 13:47:42](https://github.com/leanprover-community/mathlib/commit/13b9478)
feat(combinatorics/colex): introduce colexicographical order ([#4858](https://github.com/leanprover-community/mathlib/pull/4858))
We define the colex ordering for finite sets, and give a couple of important lemmas and properties relating to it.
Part of [#2770](https://github.com/leanprover-community/mathlib/pull/2770), in order to prove the Kruskal-Katona theorem.
#### Estimated changes
Created src/combinatorics/colex.lean
- \+ *lemma* colex.eq_iff
- \+ *lemma* colex.lt_def
- \+ *lemma* colex.le_def
- \+ *lemma* nat.sum_pow_two_lt
- \+ *lemma* hom
- \+ *lemma* hom_fin
- \+ *lemma* lt_trans
- \+ *lemma* le_trans
- \+ *lemma* lt_trichotomy
- \+ *lemma* mem_le_of_singleton_le
- \+ *lemma* lt_singleton_iff_mem_lt
- \+ *lemma* singleton_lt_iff_lt
- \+ *lemma* forall_lt_of_colex_lt_of_forall_lt
- \+ *lemma* sdiff_lt_sdiff_iff_lt
- \+ *lemma* sum_pow_two_lt_iff_lt
- \+ *def* finset.colex
- \+ *def* finset.to_colex



## [2020-11-23 12:40:48](https://github.com/leanprover-community/mathlib/commit/83ec6e0)
feat(analysis/normed_space/inner_product): inner product is infinitely smooth ([#5089](https://github.com/leanprover-community/mathlib/pull/5089))
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* inner_smul_real_left
- \+ *lemma* inner_smul_real_right
- \+/\- *lemma* real_inner_eq_re_inner
- \+ *lemma* is_bounded_bilinear_map_inner
- \+ *lemma* times_cont_diff_inner
- \+ *lemma* times_cont_diff_at_inner
- \+ *lemma* differentiable_inner
- \+ *lemma* continuous_inner
- \+ *lemma* times_cont_diff_within_at.inner
- \+ *lemma* times_cont_diff_at.inner
- \+ *lemma* times_cont_diff_on.inner
- \+ *lemma* times_cont_diff.inner
- \+ *lemma* differentiable_within_at.inner
- \+ *lemma* differentiable_at.inner
- \+ *lemma* differentiable_on.inner
- \+ *lemma* differentiable.inner

Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* algebra_map_eq_of_real



## [2020-11-23 10:07:38](https://github.com/leanprover-community/mathlib/commit/fdabe9c)
feat(data/padics/padic_norm): add a little more API ([#5082](https://github.com/leanprover-community/mathlib/pull/5082))
A little more API for `padic_val_rat` and `padic_val_nat`.
#### Estimated changes
Modified src/data/padics/padic_norm.lean
- \+ *lemma* dvd_of_one_le_padic_val_nat
- \+ *theorem* sum_pos_of_pos



## [2020-11-23 09:03:09](https://github.com/leanprover-community/mathlib/commit/2f51659)
feat(analysis/special_functions/exp_log): `exp` is infinitely smooth ([#5086](https://github.com/leanprover-community/mathlib/pull/5086))
* Prove that `complex.exp` and `real.exp` are infinitely smooth.
* Generalize lemmas about `exp ∘ f` to `f : E → ℂ` or `f : E → ℝ`
  instead of `f : ℂ → ℂ` or `f : ℝ → ℝ`.
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* times_cont_diff_exp
- \+/\- *lemma* deriv_within_cexp
- \+/\- *lemma* deriv_cexp
- \+/\- *lemma* measurable.cexp
- \+ *lemma* has_fderiv_within_at.cexp
- \+ *lemma* has_fderiv_at.cexp
- \+ *lemma* times_cont_diff.cexp
- \+ *lemma* times_cont_diff_at.cexp
- \+ *lemma* times_cont_diff_on.cexp
- \+ *lemma* times_cont_diff_within_at.cexp
- \+/\- *lemma* deriv_within_exp
- \+/\- *lemma* deriv_exp
- \+/\- *lemma* measurable.exp
- \+ *lemma* times_cont_diff.exp
- \+ *lemma* times_cont_diff_at.exp
- \+ *lemma* times_cont_diff_on.exp
- \+ *lemma* times_cont_diff_within_at.exp
- \+ *lemma* has_fderiv_within_at.exp
- \+ *lemma* has_fderiv_at.exp
- \+ *lemma* fderiv_within_exp
- \+ *lemma* fderiv_exp



## [2020-11-23 03:24:34](https://github.com/leanprover-community/mathlib/commit/b9bd4a5)
chore(scripts): update nolints.txt ([#5088](https://github.com/leanprover-community/mathlib/pull/5088))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-23 01:00:25](https://github.com/leanprover-community/mathlib/commit/ce0498e)
feat(data/nat/basic): add injectivity and divisibility lemmas ([#5068](https://github.com/leanprover-community/mathlib/pull/5068))
Multiplication by a non-zero natural is injective. Also a simple criterion for non-divisibility which I couldn't find (0<b<a implies a doesn't divide b).
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* mul_left_injective
- \+ *lemma* mul_right_injective
- \+ *lemma* not_dvd_of_pos_of_lt



## [2020-11-22 22:06:40](https://github.com/leanprover-community/mathlib/commit/2252c3a)
chore(data/list/basic): Add pmap_map ([#5081](https://github.com/leanprover-community/mathlib/pull/5081))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* pmap_map



## [2020-11-22 22:06:38](https://github.com/leanprover-community/mathlib/commit/7f4286c)
chore(order/basic): add `le_update_iff` and `update_le_iff`  ([#5080](https://github.com/leanprover-community/mathlib/pull/5080))
Other changes:
* add `update_eq_iff`, `eq_update_iff` and a more general lemma `rel_update_iff`;
* remove `@[simps]` attributes on `pi.*_lattice` instances.
#### Estimated changes
Modified src/data/set/intervals/pi.lean
- \+ *lemma* Icc_diff_pi_univ_Ioo_subset
- \+/\- *lemma* Icc_diff_pi_univ_Ioc_subset

Modified src/logic/function/basic.lean
- \+ *lemma* rel_update_iff
- \+ *lemma* update_eq_iff
- \+ *lemma* eq_update_iff

Modified src/order/basic.lean
- \+ *lemma* le_update_iff
- \+ *lemma* update_le_iff

Modified src/order/bounded_lattice.lean




## [2020-11-22 22:06:36](https://github.com/leanprover-community/mathlib/commit/c4132e9)
chore(logic/unique): add `fin.inhabited` ([#5077](https://github.com/leanprover-community/mathlib/pull/5077))
#### Estimated changes
Modified src/data/fin.lean
- \- *lemma* default_fin_one

Modified src/logic/unique.lean
- \+ *lemma* fin.eq_zero
- \+ *lemma* fin.default_eq_zero
- \+ *def* pi.unique_of_empty



## [2020-11-22 22:06:34](https://github.com/leanprover-community/mathlib/commit/2044451)
chore(data/real/ennreal): add a few lemmas ([#5071](https://github.com/leanprover-community/mathlib/pull/5071))
Also swap LHS with RHS in `to_real_mul_to_real` and rename it to `to_real_mul`.
#### Estimated changes
Modified src/analysis/normed_space/enorm.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* none_eq_top
- \+/\- *lemma* to_nnreal_eq_zero_iff
- \+/\- *lemma* to_real_eq_zero_iff
- \+/\- *lemma* to_nnreal_add
- \+/\- *lemma* mul_eq_top
- \+/\- *lemma* mul_lt_top
- \+/\- *lemma* ne_top_of_mul_ne_top_left
- \+/\- *lemma* ne_top_of_mul_ne_top_right
- \+/\- *lemma* lt_top_of_mul_lt_top_left
- \+/\- *lemma* lt_top_of_mul_lt_top_right
- \+/\- *lemma* mul_lt_top_iff
- \+/\- *lemma* not_top_le_coe
- \+/\- *lemma* nat_ne_top
- \+/\- *lemma* top_ne_nat
- \+/\- *lemma* add_lt_add_iff_left
- \+/\- *lemma* add_lt_add_iff_right
- \+/\- *lemma* lt_add_right
- \+/\- *lemma* mul_eq_mul_left
- \+/\- *lemma* mul_le_mul_left
- \+/\- *lemma* mul_lt_mul_left
- \+/\- *lemma* sub_right_inj
- \+/\- *lemma* to_nnreal_sum
- \+/\- *lemma* to_real_sum
- \+/\- *lemma* mem_Iio_self_add
- \+/\- *lemma* mem_Ioo_self_sub_add
- \+/\- *lemma* inv_top
- \+/\- *lemma* inv_lt_top
- \+/\- *lemma* div_lt_top
- \+/\- *lemma* top_div_of_ne_top
- \+/\- *lemma* top_div_of_lt_top
- \+/\- *lemma* div_eq_top
- \+/\- *lemma* le_div_iff_mul_le
- \+/\- *lemma* div_le_iff_le_mul
- \+/\- *lemma* inv_le_iff_le_mul
- \+/\- *lemma* mul_inv_cancel
- \+/\- *lemma* mul_le_iff_le_inv
- \+/\- *lemma* div_zero_iff
- \+/\- *lemma* div_pos_iff
- \+/\- *lemma* half_lt_self
- \+ *lemma* exists_nat_pos_mul_gt
- \+/\- *lemma* exists_nat_mul_gt
- \+ *lemma* exists_nat_pos_inv_mul_lt
- \+ *lemma* exists_nnreal_pos_mul_lt
- \+/\- *lemma* to_real_add
- \+/\- *lemma* to_real_le_to_real
- \+/\- *lemma* to_real_lt_to_real
- \+/\- *lemma* to_real_max
- \+/\- *lemma* of_real_le_iff_le_to_real
- \+/\- *lemma* of_real_lt_iff_lt_to_real
- \+/\- *lemma* le_of_real_iff_to_real_le
- \+/\- *lemma* lt_of_real_iff_to_real_lt
- \+ *lemma* to_nnreal_mul_top
- \+ *lemma* to_nnreal_top_mul
- \+/\- *lemma* to_real_mul_top
- \+/\- *lemma* to_real_top_mul
- \+/\- *lemma* to_real_eq_to_real
- \+ *lemma* to_real_mul
- \+ *lemma* to_real_pow
- \+ *lemma* to_real_prod
- \+/\- *lemma* infi_mul
- \+/\- *lemma* mul_infi
- \+/\- *lemma* supr_coe_nat
- \- *lemma* to_real_mul_to_real
- \+ *def* to_nnreal_hom
- \+ *def* to_real_hom

Modified src/measure_theory/bochner_integration.lean




## [2020-11-22 22:06:32](https://github.com/leanprover-community/mathlib/commit/f627d76)
chore(data/set/basic): more simp lemmas ([#5070](https://github.com/leanprover-community/mathlib/pull/5070))
Motivated by [#4843](https://github.com/leanprover-community/mathlib/pull/4843)
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* image_inter_nonempty_iff
- \- *lemma* inter_singleton_nonempty
- \+/\- *theorem* singleton_inter_eq_empty
- \+/\- *theorem* inter_singleton_eq_empty
- \+ *theorem* singleton_inter_nonempty
- \+ *theorem* inter_singleton_nonempty

Modified src/data/set/function.lean
- \+ *theorem* maps_to_id



## [2020-11-22 22:06:30](https://github.com/leanprover-community/mathlib/commit/f5b967a)
feat(finset/basic): Add forall_mem_union ([#5064](https://github.com/leanprover-community/mathlib/pull/5064))
Part of [[#4943](https://github.com/leanprover-community/mathlib/pull/4943)](https://github.com/leanprover-community/mathlib/pull/4943), in order to prove theorems about antichains.
Lemma and proof supplied by [eric-wieser](https://github.com/eric-wieser)
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* forall_mem_union



## [2020-11-22 22:06:27](https://github.com/leanprover-community/mathlib/commit/17a6f6d)
refactor(analysis/normed_space/hahn_banach): use is_R_or_C instead of specific typeclass ([#5009](https://github.com/leanprover-community/mathlib/pull/5009))
In the current version, the proof of Hahn-Banach theorem is given over the reals, then over the complexes, and then to state the consequences uniformly a custom typeclass is defined. The proof over the complexes in fact works directly over any `is_R_or_C` field (i.e., reals or complexes), so we reformulate the proof in these terms, avoiding the custom typeclass.
It doesn't bring any new theorem to mathlib, but it may be helpful in the future (to prove results uniformly over reals and complexes using `is_R_or_C`) if we have Hahn-Banach readily available for this typeclass.
#### Estimated changes
Modified src/analysis/normed_space/dual.lean


Modified src/analysis/normed_space/extend.lean
- \+/\- *lemma* norm_bound

Modified src/analysis/normed_space/hahn_banach.lean
- \+ *theorem* exists_extension_norm_eq
- \- *theorem* complex.exists_extension_norm_eq

Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* re_lm_coe
- \+ *lemma* norm_re_clm
- \+ *lemma* re_clm_coe
- \+ *lemma* re_clm_apply



## [2020-11-22 19:31:23](https://github.com/leanprover-community/mathlib/commit/2a876b6)
chore(algebra/ordered_group): move monoid stuff to ordered_monoid.lean ([#5066](https://github.com/leanprover-community/mathlib/pull/5066))
Replace one 2000 line file with two 1000 line files: ordered group stuff in one, and ordered monoid stuff in the other.
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \- *lemma* mul_le_mul_left'
- \- *lemma* mul_le_mul_right'
- \- *lemma* lt_of_mul_lt_mul_left'
- \- *lemma* mul_le_mul'
- \- *lemma* mul_le_mul_three
- \- *lemma* le_mul_of_one_le_right'
- \- *lemma* le_mul_of_one_le_left'
- \- *lemma* lt_of_mul_lt_mul_right'
- \- *lemma* le_mul_of_one_le_of_le
- \- *lemma* le_mul_of_le_of_one_le
- \- *lemma* one_le_mul
- \- *lemma* one_lt_mul_of_lt_of_le'
- \- *lemma* one_lt_mul_of_le_of_lt'
- \- *lemma* one_lt_mul'
- \- *lemma* mul_le_one'
- \- *lemma* mul_le_of_le_one_of_le'
- \- *lemma* mul_le_of_le_of_le_one'
- \- *lemma* mul_lt_one_of_lt_one_of_le_one'
- \- *lemma* mul_lt_one_of_le_one_of_lt_one'
- \- *lemma* mul_lt_one'
- \- *lemma* lt_mul_of_one_le_of_lt'
- \- *lemma* lt_mul_of_lt_of_one_le'
- \- *lemma* lt_mul_of_one_lt_of_lt'
- \- *lemma* lt_mul_of_lt_of_one_lt'
- \- *lemma* mul_lt_of_le_one_of_lt'
- \- *lemma* mul_lt_of_lt_of_le_one'
- \- *lemma* mul_lt_of_lt_one_of_lt'
- \- *lemma* mul_lt_of_lt_of_lt_one'
- \- *lemma* mul_eq_one_iff'
- \- *lemma* monotone.mul'
- \- *lemma* monotone.mul_const'
- \- *lemma* monotone.const_mul'
- \- *lemma* bit0_pos
- \- *lemma* zero_le
- \- *lemma* zero_lt_coe
- \- *lemma* coe_lt_coe
- \- *lemma* coe_le_coe
- \- *lemma* mul_le_mul_left
- \- *lemma* lt_of_mul_lt_mul_left
- \- *lemma* coe_one
- \- *lemma* coe_eq_one
- \- *lemma* coe_add
- \- *lemma* coe_bit0
- \- *lemma* coe_bit1
- \- *lemma* add_top
- \- *lemma* top_add
- \- *lemma* add_eq_top
- \- *lemma* add_lt_top
- \- *lemma* add_eq_coe
- \- *lemma* coe_coe_add_hom
- \- *lemma* zero_lt_top
- \- *lemma* coe_zero
- \- *lemma* coe_eq_zero
- \- *lemma* bot_add
- \- *lemma* add_bot
- \- *lemma* le_iff_exists_add
- \- *lemma* bot_eq_zero
- \- *lemma* add_eq_zero_iff
- \- *lemma* le_zero_iff_eq
- \- *lemma* zero_lt_iff_ne_zero
- \- *lemma* exists_pos_add_of_lt
- \- *lemma* le_add_left
- \- *lemma* le_add_right
- \- *lemma* le_of_mul_le_mul_left'
- \- *lemma* mul_lt_mul_left'
- \- *lemma* mul_lt_mul_right'
- \- *lemma* mul_lt_mul'''
- \- *lemma* mul_lt_mul_of_le_of_lt
- \- *lemma* mul_lt_mul_of_lt_of_le
- \- *lemma* lt_mul_of_one_lt_right'
- \- *lemma* lt_mul_of_one_lt_left'
- \- *lemma* le_of_mul_le_mul_right'
- \- *lemma* mul_lt_one
- \- *lemma* mul_lt_one_of_lt_one_of_le_one
- \- *lemma* mul_lt_one_of_le_one_of_lt_one
- \- *lemma* lt_mul_of_one_lt_of_le
- \- *lemma* lt_mul_of_le_of_one_lt
- \- *lemma* mul_le_of_le_one_of_le
- \- *lemma* mul_le_of_le_of_le_one
- \- *lemma* mul_lt_of_lt_one_of_le
- \- *lemma* mul_lt_of_le_of_lt_one
- \- *lemma* lt_mul_of_one_le_of_lt
- \- *lemma* lt_mul_of_lt_of_one_le
- \- *lemma* lt_mul_of_one_lt_of_lt
- \- *lemma* lt_mul_of_lt_of_one_lt
- \- *lemma* mul_lt_of_le_one_of_lt
- \- *lemma* mul_lt_of_lt_of_le_one
- \- *lemma* mul_lt_of_lt_one_of_lt
- \- *lemma* mul_lt_of_lt_of_lt_one
- \- *lemma* mul_le_mul_iff_left
- \- *lemma* mul_le_mul_iff_right
- \- *lemma* mul_lt_mul_iff_left
- \- *lemma* mul_lt_mul_iff_right
- \- *lemma* le_mul_iff_one_le_right'
- \- *lemma* le_mul_iff_one_le_left'
- \- *lemma* lt_mul_iff_one_lt_right'
- \- *lemma* lt_mul_iff_one_lt_left'
- \- *lemma* mul_le_iff_le_one_left'
- \- *lemma* mul_le_iff_le_one_right'
- \- *lemma* mul_lt_iff_lt_one_right'
- \- *lemma* mul_lt_iff_lt_one_left'
- \- *lemma* mul_eq_one_iff_eq_one_of_one_le
- \- *lemma* monotone.mul_strict_mono'
- \- *lemma* strict_mono.mul_monotone'
- \- *lemma* strict_mono.mul_const'
- \- *lemma* strict_mono.const_mul'
- \- *lemma* with_top.add_lt_add_iff_left
- \- *lemma* with_bot.add_lt_add_iff_left
- \- *lemma* with_top.add_lt_add_iff_right
- \- *lemma* with_bot.add_lt_add_iff_right
- \- *lemma* fn_min_mul_fn_max
- \- *lemma* min_mul_max
- \- *lemma* min_add_add_left
- \- *lemma* min_add_add_right
- \- *lemma* max_add_add_left
- \- *lemma* max_add_add_right
- \- *lemma* min_le_add_of_nonneg_right
- \- *lemma* min_le_add_of_nonneg_left
- \- *lemma* max_le_add_of_nonneg
- \- *theorem* coe_le_coe
- \- *theorem* coe_lt_coe
- \- *theorem* max_coe
- \- *theorem* min_coe
- \- *theorem* one_eq_coe
- \- *theorem* top_ne_one
- \- *theorem* one_ne_top
- \- *def* ordered_add_comm_monoid
- \- *def* coe_add_hom

Created src/algebra/ordered_monoid.lean
- \+ *lemma* mul_le_mul_left'
- \+ *lemma* mul_le_mul_right'
- \+ *lemma* lt_of_mul_lt_mul_left'
- \+ *lemma* mul_le_mul'
- \+ *lemma* mul_le_mul_three
- \+ *lemma* le_mul_of_one_le_right'
- \+ *lemma* le_mul_of_one_le_left'
- \+ *lemma* lt_of_mul_lt_mul_right'
- \+ *lemma* le_mul_of_one_le_of_le
- \+ *lemma* le_mul_of_le_of_one_le
- \+ *lemma* one_le_mul
- \+ *lemma* one_lt_mul_of_lt_of_le'
- \+ *lemma* one_lt_mul_of_le_of_lt'
- \+ *lemma* one_lt_mul'
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
- \+ *lemma* bit0_pos
- \+ *lemma* zero_le
- \+ *lemma* zero_lt_coe
- \+ *lemma* coe_lt_coe
- \+ *lemma* coe_le_coe
- \+ *lemma* mul_le_mul_left
- \+ *lemma* lt_of_mul_lt_mul_left
- \+ *lemma* coe_one
- \+ *lemma* coe_eq_one
- \+ *lemma* coe_add
- \+ *lemma* coe_bit0
- \+ *lemma* coe_bit1
- \+ *lemma* add_top
- \+ *lemma* top_add
- \+ *lemma* add_eq_top
- \+ *lemma* add_lt_top
- \+ *lemma* add_eq_coe
- \+ *lemma* coe_coe_add_hom
- \+ *lemma* zero_lt_top
- \+ *lemma* coe_zero
- \+ *lemma* coe_eq_zero
- \+ *lemma* bot_add
- \+ *lemma* add_bot
- \+ *lemma* le_iff_exists_add
- \+ *lemma* bot_eq_zero
- \+ *lemma* add_eq_zero_iff
- \+ *lemma* le_zero_iff_eq
- \+ *lemma* zero_lt_iff_ne_zero
- \+ *lemma* exists_pos_add_of_lt
- \+ *lemma* le_add_left
- \+ *lemma* le_add_right
- \+ *lemma* le_of_mul_le_mul_left'
- \+ *lemma* mul_lt_mul_left'
- \+ *lemma* mul_lt_mul_right'
- \+ *lemma* mul_lt_mul'''
- \+ *lemma* mul_lt_mul_of_le_of_lt
- \+ *lemma* mul_lt_mul_of_lt_of_le
- \+ *lemma* lt_mul_of_one_lt_right'
- \+ *lemma* lt_mul_of_one_lt_left'
- \+ *lemma* le_of_mul_le_mul_right'
- \+ *lemma* mul_lt_one
- \+ *lemma* mul_lt_one_of_lt_one_of_le_one
- \+ *lemma* mul_lt_one_of_le_one_of_lt_one
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
- \+ *lemma* with_top.add_lt_add_iff_left
- \+ *lemma* with_bot.add_lt_add_iff_left
- \+ *lemma* with_top.add_lt_add_iff_right
- \+ *lemma* with_bot.add_lt_add_iff_right
- \+ *lemma* fn_min_mul_fn_max
- \+ *lemma* min_mul_max
- \+ *lemma* min_add_add_left
- \+ *lemma* min_add_add_right
- \+ *lemma* max_add_add_left
- \+ *lemma* max_add_add_right
- \+ *lemma* min_le_add_of_nonneg_right
- \+ *lemma* min_le_add_of_nonneg_left
- \+ *lemma* max_le_add_of_nonneg
- \+ *theorem* coe_le_coe
- \+ *theorem* coe_lt_coe
- \+ *theorem* max_coe
- \+ *theorem* min_coe
- \+ *theorem* one_eq_coe
- \+ *theorem* top_ne_one
- \+ *theorem* one_ne_top
- \+ *def* ordered_add_comm_monoid
- \+ *def* coe_add_hom



## [2020-11-22 14:51:30](https://github.com/leanprover-community/mathlib/commit/8d71ec9)
chore(data/fin): a few more lemmas about `fin.insert_nth` ([#5079](https://github.com/leanprover-community/mathlib/pull/5079))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* insert_nth_le_iff
- \+ *lemma* le_insert_nth_iff
- \+ *lemma* insert_nth_mem_Icc
- \+ *lemma* preimage_insert_nth_Icc_of_mem
- \+ *lemma* preimage_insert_nth_Icc_of_not_mem



## [2020-11-22 14:51:28](https://github.com/leanprover-community/mathlib/commit/c458724)
chore(topology/metric_space/isometry): add a missing simp lemma ([#5078](https://github.com/leanprover-community/mathlib/pull/5078))
#### Estimated changes
Modified src/topology/metric_space/isometry.lean
- \+ *lemma* coe_to_homeomorph_symm



## [2020-11-22 14:51:26](https://github.com/leanprover-community/mathlib/commit/a9b6b36)
chore(algebra/big_operators): add `finset.abs_prod` ([#5076](https://github.com/leanprover-community/mathlib/pull/5076))
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+ *lemma* abs_prod



## [2020-11-22 14:51:24](https://github.com/leanprover-community/mathlib/commit/2ba930e)
chore(measure_theory/borel_space): add some `simp` attrs ([#5075](https://github.com/leanprover-community/mathlib/pull/5075))
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* is_measurable_Ici
- \+/\- *lemma* is_measurable_Iic
- \+/\- *lemma* is_measurable_Icc
- \+/\- *lemma* is_measurable_Iio
- \+/\- *lemma* is_measurable_Ioi
- \+/\- *lemma* is_measurable_Ioo
- \+/\- *lemma* is_measurable_Ioc
- \+/\- *lemma* is_measurable_Ico



## [2020-11-22 14:51:21](https://github.com/leanprover-community/mathlib/commit/c59dbf3)
chore(topology/basic): add `cluster_pt.map`, rename `mem_closure` ([#5065](https://github.com/leanprover-community/mathlib/pull/5065))
* add `filter.prod_pure`, `filter.pure_prod`, `cluster_pt.map`, and `set.maps_to.closure`;
* rename `mem_closure` to `map_mem_closure`;
* rename `mem_closure2` to `map_mem_closure2`.
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* pure_prod
- \+ *lemma* prod_pure
- \+/\- *lemma* prod_pure_pure

Modified src/topology/algebra/ring.lean


Modified src/topology/basic.lean
- \+ *lemma* cluster_pt.map
- \+ *lemma* set.maps_to.closure
- \+ *lemma* map_mem_closure
- \- *lemma* mem_closure

Modified src/topology/constructions.lean
- \+ *lemma* map_mem_closure2
- \- *lemma* mem_closure2

Modified src/topology/metric_space/basic.lean




## [2020-11-22 12:03:14](https://github.com/leanprover-community/mathlib/commit/a649851)
chore(analysis/complex/basic): add `times_cont_diff.real_of_complex` ([#5073](https://github.com/leanprover-community/mathlib/pull/5073))
Also rename `has_deriv_at_real_of_complex` to `has_deriv_at.real_of_complex`.
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \- *lemma* has_deriv_at_real_of_complex_aux
- \+ *theorem* has_deriv_at.real_of_complex
- \+ *theorem* times_cont_diff_at.real_of_complex
- \+ *theorem* times_cont_diff.real_of_complex
- \- *theorem* has_deriv_at_real_of_complex

Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/special_functions/trigonometric.lean




## [2020-11-22 12:03:12](https://github.com/leanprover-community/mathlib/commit/87439b9)
chore(logic/basic): add `forall_apply_eq_imp_iff₂` ([#5072](https://github.com/leanprover-community/mathlib/pull/5072))
Other lemmas simplify `∀ y ∈ f '' s, p y` to the LHS of this lemma.
#### Estimated changes
Modified src/data/hash_map.lean


Modified src/data/multiset/basic.lean


Modified src/data/set/basic.lean
- \+/\- *theorem* ball_image_of_ball

Modified src/deprecated/submonoid.lean


Modified src/logic/basic.lean
- \+ *theorem* forall_apply_eq_imp_iff₂

Modified src/ring_theory/ideal/operations.lean




## [2020-11-22 10:15:37](https://github.com/leanprover-community/mathlib/commit/198f3e5)
chore(topology/homeomorph): add more simp lemmas ([#5069](https://github.com/leanprover-community/mathlib/pull/5069))
Also use implicit arguments in some `iff` lemmas.
#### Estimated changes
Modified src/topology/algebra/module.lean


Modified src/topology/homeomorph.lean
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+/\- *lemma* symm_comp_self
- \+/\- *lemma* self_comp_symm
- \+/\- *lemma* range_coe
- \+/\- *lemma* comp_continuous_on_iff
- \+/\- *lemma* comp_continuous_iff
- \+ *lemma* comp_continuous_iff'



## [2020-11-22 01:09:23](https://github.com/leanprover-community/mathlib/commit/8525aa9)
chore(scripts): update nolints.txt ([#5067](https://github.com/leanprover-community/mathlib/pull/5067))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-21 21:24:19](https://github.com/leanprover-community/mathlib/commit/79cd720)
feat(data/complex/is_R_or_C): Create a proper coercion from ℝ ([#4824](https://github.com/leanprover-community/mathlib/pull/4824))
This PR creates a proper coercion `ℝ → 𝕜` for `[is_R_or_C 𝕜]`, modelled on the code in `data/nat/cast`, as per the discussion [here](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Hilbert.20space.20is.20isometric.20to.20its.20dual).
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+/\- *lemma* inner_norm_sq_eq_inner_self
- \+/\- *lemma* inner_self_re_to_K
- \+/\- *lemma* inner_self_abs_to_K

Modified src/data/complex/is_R_or_C.lean
- \+/\- *lemma* of_real_alg
- \+/\- *lemma* re_add_im
- \+/\- *lemma* of_real_re
- \+/\- *lemma* of_real_im
- \+/\- *lemma* of_real_zero
- \+/\- *lemma* of_real_one
- \+/\- *lemma* of_real_add
- \+/\- *lemma* of_real_bit0
- \+/\- *lemma* of_real_bit1
- \+/\- *lemma* of_real_neg
- \+/\- *lemma* of_real_mul
- \+/\- *lemma* of_real_mul_re
- \+/\- *lemma* smul_re
- \+/\- *lemma* smul_im
- \+/\- *lemma* conj_of_real
- \+/\- *lemma* eq_conj_iff_real
- \+/\- *lemma* eq_conj_iff_re
- \+/\- *lemma* norm_sq_of_real
- \+/\- *lemma* of_real_sub
- \+/\- *lemma* of_real_pow
- \+/\- *lemma* of_real_inv
- \+/\- *lemma* of_real_div
- \+/\- *lemma* div_re_of_real
- \+/\- *lemma* of_real_fpow
- \+/\- *lemma* nat_cast_re
- \+/\- *lemma* nat_cast_im
- \+/\- *lemma* int_cast_re
- \+/\- *lemma* int_cast_im
- \+/\- *lemma* rat_cast_re
- \+/\- *lemma* rat_cast_im
- \+/\- *lemma* abs_of_real
- \+/\- *lemma* abs_of_nonneg
- \+/\- *lemma* abs_cast_nat
- \+/\- *lemma* conj_mul_eq_norm_sq_left
- \+ *lemma* of_real_prod
- \+ *lemma* of_real_sum
- \+ *lemma* of_real_finsupp_sum
- \+ *lemma* of_real_finsupp_prod
- \+ *lemma* coe_real_eq_id
- \- *lemma* inv_def
- \- *lemma* zero_re
- \- *lemma* zero_im
- \- *lemma* of_real_to_real
- \- *lemma* of_real_to_complex
- \+ *theorem* inv_def
- \+/\- *theorem* of_real_inj
- \+/\- *theorem* of_real_eq_zero
- \+/\- *theorem* mul_conj
- \+/\- *theorem* add_conj
- \+/\- *theorem* sub_conj
- \+/\- *theorem* of_real_nat_cast
- \+/\- *theorem* of_real_int_cast
- \+/\- *theorem* of_real_rat_cast
- \+/\- *theorem* re_eq_add_conj



## [2020-11-21 20:09:32](https://github.com/leanprover-community/mathlib/commit/556a725)
feat(data/nat/parity): lemmas about (-1)^n ([#5056](https://github.com/leanprover-community/mathlib/pull/5056))
I needed these twice recently, for two independent reasons, so I thought they were worth a PR.
#### Estimated changes
Modified src/data/nat/parity.lean
- \+ *lemma* even_or_odd
- \+ *theorem* neg_one_pow_two
- \+ *theorem* neg_one_pow_of_even
- \+ *theorem* neg_one_pow_of_odd



## [2020-11-21 17:37:55](https://github.com/leanprover-community/mathlib/commit/aff4669)
feat(group_theory/subgroup): add closure_eq_bot_iff ([#5055](https://github.com/leanprover-community/mathlib/pull/5055))
Add missing lemma
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* closure_eq_bot_iff



## [2020-11-21 01:13:36](https://github.com/leanprover-community/mathlib/commit/cff497f)
chore(scripts): update nolints.txt ([#5058](https://github.com/leanprover-community/mathlib/pull/5058))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-20 19:18:02](https://github.com/leanprover-community/mathlib/commit/006f84e)
feat(algebra/group_power/basic): add add le_of_pow_le_pow ([#5054](https://github.com/leanprover-community/mathlib/pull/5054))
add a random missing lemma
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *lemma* le_of_pow_le_pow



## [2020-11-20 16:41:58](https://github.com/leanprover-community/mathlib/commit/1fbdf77)
fix(linear_algebra/quadratic_form): nondegenerate -> anisotropic ([#5050](https://github.com/leanprover-community/mathlib/pull/5050))
I made a mistake by merging a PR that defined `nondegenerate`
but should have used the terminology `anisotropic` instead.
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* not_anisotropic_iff_exists
- \- *lemma* not_nondegenerate_iff_exists
- \+ *def* anisotropic
- \- *def* nondegenerate



## [2020-11-20 12:39:29](https://github.com/leanprover-community/mathlib/commit/498d497)
feat(measure_theory/lp_space): prove that neg and add are in Lp ([#5014](https://github.com/leanprover-community/mathlib/pull/5014))
For f and g in Lp, (-f) and (f+g) are also in Lp.
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *theorem* rpow_arith_mean_le_arith_mean2_rpow

Modified src/data/fin.lean
- \+ *lemma* default_fin_one

Modified src/measure_theory/integration.lean
- \+ *lemma* lintegral_mono_nnreal

Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm_neg
- \+ *lemma* mem_ℒp.neg
- \+ *lemma* mem_ℒp.add



## [2020-11-20 09:40:27](https://github.com/leanprover-community/mathlib/commit/32d1dfc)
feat(linear_algebra/quadratic_form): nondegenerate quadratic forms ([#5045](https://github.com/leanprover-community/mathlib/pull/5045))
No real lemmas about these, but `nondegenerate Q` is easier to read than `∀ x, Q x = 0 → x = 0`
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* not_nondegenerate_iff_exists
- \+ *def* nondegenerate



## [2020-11-20 07:52:25](https://github.com/leanprover-community/mathlib/commit/8d40e8d)
feat(analysis/special_functions/pow): add ennreal.to_nnreal_rpow ([#5042](https://github.com/leanprover-community/mathlib/pull/5042))
cut ennreal.to_real_rpow into two lemmas: to_nnreal_rpow and to_real_rpow
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* to_nnreal_rpow
- \+/\- *lemma* to_real_rpow



## [2020-11-20 06:44:00](https://github.com/leanprover-community/mathlib/commit/de76acd)
feat(number_theory/arithmetic_function): moebius is the inverse of zeta ([#5001](https://github.com/leanprover-community/mathlib/pull/5001))
Proves the most basic version of moebius inversion: that the moebius function is the inverse of the zeta function
#### Estimated changes
Modified src/algebra/squarefree.lean
- \+ *lemma* divisors_filter_squarefree
- \+ *lemma* sum_divisors_filter_squarefree

Modified src/number_theory/arithmetic_function.lean
- \+ *lemma* card_factors_one
- \+ *lemma* moebius_ne_zero_iff_eq_or
- \+ *lemma* moebius_mul_zeta
- \+ *lemma* zeta_mul_moebius

Modified src/ring_theory/int/basic.lean
- \+ *lemma* nat.factors_multiset_prod_of_irreducible



## [2020-11-20 01:04:58](https://github.com/leanprover-community/mathlib/commit/0e976d9)
chore(scripts): update nolints.txt ([#5048](https://github.com/leanprover-community/mathlib/pull/5048))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-19 15:34:57](https://github.com/leanprover-community/mathlib/commit/47542a0)
feat(ring_theory/witt_vector/verschiebung): verschiebung of witt vectors ([#4836](https://github.com/leanprover-community/mathlib/pull/4836))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Created src/ring_theory/witt_vector/verschiebung.lean
- \+ *lemma* verschiebung_fun_coeff
- \+ *lemma* verschiebung_fun_coeff_zero
- \+ *lemma* verschiebung_fun_coeff_succ
- \+ *lemma* ghost_component_zero_verschiebung_fun
- \+ *lemma* ghost_component_verschiebung_fun
- \+ *lemma* verschiebung_poly_zero
- \+ *lemma* aeval_verschiebung_poly'
- \+ *lemma* verschiebung_fun_is_poly
- \+ *lemma* verschiebung_is_poly
- \+ *lemma* map_verschiebung
- \+ *lemma* ghost_component_zero_verschiebung
- \+ *lemma* ghost_component_verschiebung
- \+ *lemma* verschiebung_coeff_zero
- \+ *lemma* verschiebung_coeff_add_one
- \+ *lemma* verschiebung_coeff_succ
- \+ *lemma* aeval_verschiebung_poly
- \+ *lemma* bind₁_verschiebung_poly_witt_polynomial
- \+ *def* verschiebung_fun
- \+ *def* verschiebung_poly
- \+ *def* verschiebung



## [2020-11-19 13:00:19](https://github.com/leanprover-community/mathlib/commit/3326510)
chore(field_theory/minimal_polynomial): generalize irreducible ([#5006](https://github.com/leanprover-community/mathlib/pull/5006))
I have removed the assumption that the base ring is a field for a minimal polynomial to be irreducible.
The proof is simple but long, it should be possible to use `wlog` to shorten it, but I do not understand how to do it...
#### Estimated changes
Modified src/field_theory/minimal_polynomial.lean
- \+/\- *lemma* degree_pos
- \+/\- *lemma* not_is_unit
- \+ *lemma* aeval_ne_zero_of_dvd_not_unit_minimal_polynomial
- \+/\- *lemma* irreducible
- \+ *lemma* gcd_domain_eq_field_fractions
- \- *lemma* degree_ne_zero

Modified src/field_theory/splitting_field.lean


Modified src/number_theory/sum_two_squares.lean




## [2020-11-19 13:00:17](https://github.com/leanprover-community/mathlib/commit/b479d3b)
feat(algebra/*): star_ring instances on free_algebra, free_monoid, ring_quot, and quaternion ([#4902](https://github.com/leanprover-community/mathlib/pull/4902))
#### Estimated changes
Modified src/algebra/free_algebra.lean
- \+ *lemma* star_ι
- \+ *lemma* star_algebra_map
- \+ *def* star_hom

Modified src/algebra/free_monoid.lean
- \+ *lemma* star_of
- \+ *lemma* star_one

Modified src/algebra/ring_quot.lean
- \+ *def* star_ring

Modified src/data/quaternion.lean
- \+ *lemma* star_def



## [2020-11-19 10:10:26](https://github.com/leanprover-community/mathlib/commit/700d576)
chore(algebra/group/defs): Remove shortcut instance definitions ([#4955](https://github.com/leanprover-community/mathlib/pull/4955))
This means that `group.to_left_cancel_semigroup` is now spelt `group.to_cancel_monoid.to_left_cancel_monoid.to_left_cancel_semigroup`.
The longer spelling shouldn't actually matter because type inference will do it anyway.
I don't know whether this matters, but this should slightly reduce the number of connections that instance resolution must check.
This shortcut wasn't added deliberately, it seems it just got added accidentally when [#3688](https://github.com/leanprover-community/mathlib/pull/3688) was introduced.
#### Estimated changes
Modified src/algebra/group/defs.lean




## [2020-11-19 06:43:23](https://github.com/leanprover-community/mathlib/commit/123c522)
feat(category_theory/limits): terminal comparison morphism ([#5025](https://github.com/leanprover-community/mathlib/pull/5025))
#### Estimated changes
Modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* terminal_comparison
- \+ *def* initial_comparison



## [2020-11-19 03:06:00](https://github.com/leanprover-community/mathlib/commit/b848b5b)
feat(algebra/squarefree): a squarefree element of a UFM divides a power iff it divides ([#5037](https://github.com/leanprover-community/mathlib/pull/5037))
Proves that if `x, y` are elements of a UFM such that `squarefree x`, then `x | y ^ n` iff `x | y`.
#### Estimated changes
Modified src/algebra/squarefree.lean
- \+/\- *lemma* squarefree_iff_nodup_factors
- \+ *lemma* dvd_pow_iff_dvd_of_squarefree

Modified src/data/multiset/basic.lean
- \+ *lemma* prod_dvd_prod
- \+ *lemma* mem_nsmul

Modified src/data/multiset/erase_dup.lean
- \+ *lemma* erase_dup_nsmul
- \+ *lemma* nodup.le_erase_dup_iff_le
- \+ *lemma* multiset.nodup.le_nsmul_iff_le

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* factors_zero
- \+ *lemma* factors_pow
- \+ *lemma* dvd_iff_factors_le_factors



## [2020-11-19 01:49:38](https://github.com/leanprover-community/mathlib/commit/87a6d95)
chore(scripts): update nolints.txt ([#5041](https://github.com/leanprover-community/mathlib/pull/5041))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-19 01:49:36](https://github.com/leanprover-community/mathlib/commit/68adaba)
chore(field_theory/separable): spell-check "seperable" to "separable" ([#5040](https://github.com/leanprover-community/mathlib/pull/5040))
Replacing instances of "seperable" with "separable"
#### Estimated changes
Modified src/field_theory/separable.lean
- \+ *lemma* multiplicity_le_one_of_separable
- \+ *lemma* root_multiplicity_le_one_of_separable
- \- *lemma* multiplicity_le_one_of_seperable
- \- *lemma* root_multiplicity_le_one_of_seperable



## [2020-11-18 23:23:59](https://github.com/leanprover-community/mathlib/commit/dcbec39)
feat(algebra/*): Add of_injective lemmas ([#5034](https://github.com/leanprover-community/mathlib/pull/5034))
This adds `free_monoid.of_injective`, `monoid_algebra.of_injective`, `add_monoid_algebra.of_injective`, and renames and restates `free_group.of.inj` to match these lemmas.
`function.injective (free_abelian_group.of)` is probably also true, but I wasn't able to prove it.
#### Estimated changes
Modified src/algebra/free_monoid.lean
- \+ *lemma* of_injective

Modified src/algebra/monoid_algebra.lean
- \+ *lemma* of_injective

Modified src/group_theory/free_group.lean
- \+ *theorem* of_injective
- \- *theorem* of.inj



## [2020-11-18 23:23:57](https://github.com/leanprover-community/mathlib/commit/2de8db4)
feat(analysis/special_functions/pow): prove measurability of rpow for ennreal ([#5026](https://github.com/leanprover-community/mathlib/pull/5026))
Prove measurability of rpow for an ennreal argument.
Also shorten the proof in the real case.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* coe_rpow_def
- \+ *lemma* ennreal.measurable_rpow
- \+ *lemma* measurable.ennreal_rpow
- \+ *lemma* ennreal.measurable_rpow_const
- \+ *lemma* measurable.ennreal_rpow_const

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable.ite



## [2020-11-18 21:10:00](https://github.com/leanprover-community/mathlib/commit/abb0b67)
refactor(*): make continuous a structure ([#5035](https://github.com/leanprover-community/mathlib/pull/5035))
Turn `continuous` into a structure, to make sure it is not unfolded too much by Lean.
After the change, inferring some types is harder to Lean (as it can not unfold further to find more information), so some help is needed at places. Especially, for `hf : continuous f` and `hg : continuous g`, I had to replace `hf.prod_mk hg` with `(hf.prod_mk hg : _)` a lot of times.
For `hf : continuous f` and `hs : is_open s`, the fact that `f^(-1) s` is open used to be `hf s hs`. Now, it is `hs.preimage hf`, just like it is for closed sets.
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean


Modified src/analysis/normed_space/add_torsor.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/seminorm.lean


Modified src/geometry/manifold/instances/real.lean


Modified src/geometry/manifold/mfderiv.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/haar_measure.lean


Modified src/topology/algebra/affine.lean


Modified src/topology/algebra/continuous_functions.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/basic.lean
- \+ *lemma* continuous_def
- \- *def* continuous

Modified src/topology/category/Compactum.lean


Modified src/topology/category/Top/limits.lean


Modified src/topology/category/Top/opens.lean
- \+/\- *lemma* map_obj

Modified src/topology/compact_open.lean


Modified src/topology/constructions.lean


Modified src/topology/continuous_on.lean


Modified src/topology/homeomorph.lean


Modified src/topology/instances/complex.lean


Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* tsum_sub

Modified src/topology/instances/real.lean


Modified src/topology/list.lean


Modified src/topology/maps.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/omega_complete_partial_order.lean


Modified src/topology/opens.lean


Modified src/topology/order.lean
- \+ *lemma* continuous.coinduced_le
- \+/\- *lemma* coinduced_le_iff_le_induced
- \+ *lemma* continuous.le_induced

Modified src/topology/subset_properties.lean


Modified src/topology/tactic.lean


Modified src/topology/uniform_space/basic.lean




## [2020-11-18 16:28:13](https://github.com/leanprover-community/mathlib/commit/38d2b53)
feat(algebra/free_algebra): Add a nontrivial instance ([#5033](https://github.com/leanprover-community/mathlib/pull/5033))
#### Estimated changes
Modified src/algebra/free_algebra.lean




## [2020-11-18 14:27:12](https://github.com/leanprover-community/mathlib/commit/0e09ada)
feat(category_theory/is_connected): zigzag lemmas ([#5024](https://github.com/leanprover-community/mathlib/pull/5024))
A few basic lemmas about connected categories and the zigzag relation
#### Estimated changes
Modified src/category_theory/is_connected.lean
- \+ *lemma* zigzag_equivalence
- \+ *lemma* zigzag_obj_of_zigzag
- \+ *lemma* zag_of_zag_obj
- \+ *def* zigzag.setoid



## [2020-11-18 12:44:52](https://github.com/leanprover-community/mathlib/commit/aff7727)
chore(data/complex/is_R_or_C): Remove two unnecessary axioms ([#5017](https://github.com/leanprover-community/mathlib/pull/5017))
`of_real` and `smul_coe_mul_ax` are already implied by the algebra structure.
The addition of `noncomputable` does not matter here, as both instances of `is_R_or_C` are marked non-computable anyway.
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean


Modified src/data/complex/is_R_or_C.lean
- \+/\- *lemma* of_real_alg
- \+/\- *lemma* of_real_zero
- \+/\- *lemma* zero_re'
- \+/\- *lemma* of_real_one
- \+/\- *lemma* norm_sq_of_real
- \+/\- *lemma* of_real_sub
- \+/\- *lemma* of_real_pow
- \- *def* of_real_hom



## [2020-11-18 09:32:12](https://github.com/leanprover-community/mathlib/commit/d22a878)
doc(algebra/module/linear_map): Explain where the ring instance is ([#5023](https://github.com/leanprover-community/mathlib/pull/5023))
#### Estimated changes
Modified src/algebra/module/linear_map.lean




## [2020-11-18 09:32:10](https://github.com/leanprover-community/mathlib/commit/dfdad99)
feat(category_theory): constant functor is faithful ([#5022](https://github.com/leanprover-community/mathlib/pull/5022))
#### Estimated changes
Modified src/category_theory/const.lean




## [2020-11-18 09:32:06](https://github.com/leanprover-community/mathlib/commit/dab2ae3)
feat(category_theory/is_connected): transfer across equivalence ([#5021](https://github.com/leanprover-community/mathlib/pull/5021))
Also renames some universes to match usual conventions
#### Estimated changes
Modified src/category_theory/is_connected.lean
- \+/\- *lemma* constant_of_preserves_morphisms
- \+ *lemma* is_preconnected_of_equivalent
- \+ *lemma* is_connected_of_equivalent
- \+/\- *def* iso_constant



## [2020-11-18 09:31:55](https://github.com/leanprover-community/mathlib/commit/a44b46c)
chore(*/sub*): Use the simp normal form for has_coe_to_sort ([#5019](https://github.com/leanprover-community/mathlib/pull/5019))
This reduces the need to start proofs on subtypes by applying `mem_coe`.
#### Estimated changes
Modified src/group_theory/submonoid/basic.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/subring.lean


Modified src/ring_theory/subsemiring.lean




## [2020-11-18 09:31:53](https://github.com/leanprover-community/mathlib/commit/0d3092b)
feat(number_theory/arithmetic_function): defining several more `arithmetic_function`s ([#4998](https://github.com/leanprover-community/mathlib/pull/4998))
Defines arithmetic functions `card_factors`, `card_distinct_factors`, and `moebius`
#### Estimated changes
Modified src/algebra/squarefree.lean


Modified src/number_theory/arithmetic_function.lean
- \+ *lemma* card_factors_apply
- \+ *lemma* card_factors_eq_one_iff_prime
- \+ *lemma* card_factors_mul
- \+ *lemma* card_factors_multiset_prod
- \+ *lemma* card_distinct_factors_zero
- \+ *lemma* card_distinct_factors_apply
- \+ *lemma* card_distinct_factors_eq_card_factors_iff_squarefree
- \+ *lemma* moebius_apply_of_squarefree
- \+ *lemma* moebius_eq_zero_of_not_squarefree
- \+ *lemma* moebius_ne_zero_iff_squarefree
- \+ *def* card_factors
- \+ *def* card_distinct_factors
- \+ *def* moebius

Modified src/ring_theory/multiplicity.lean
- \+ *lemma* multiplicity_zero_eq_zero_of_ne_zero



## [2020-11-18 09:31:50](https://github.com/leanprover-community/mathlib/commit/7cc6b53)
feat(category_theory/sites): sheaves on a grothendieck topology ([#4608](https://github.com/leanprover-community/mathlib/pull/4608))
Broken off from [#4577](https://github.com/leanprover-community/mathlib/pull/4577).
#### Estimated changes
Modified docs/references.bib


Modified src/category_theory/limits/shapes/types.lean
- \+ *lemma* type_equalizer_iff_unique

Created src/category_theory/sites/sheaf.lean
- \+ *lemma* pullback_compatible_iff
- \+ *lemma* family_of_elements.compatible.restrict
- \+ *lemma* family_of_elements.compatible.sieve_extend
- \+ *lemma* extend_agrees
- \+ *lemma* restrict_extend
- \+ *lemma* compatible_iff_sieve_compatible
- \+ *lemma* family_of_elements.compatible.to_sieve_compatible
- \+ *lemma* restrict_inj
- \+ *lemma* extend_restrict
- \+ *lemma* is_compatible_of_exists_amalgamation
- \+ *lemma* is_amalgamation_restrict
- \+ *lemma* is_amalgamation_sieve_extend
- \+ *lemma* is_separated_for.ext
- \+ *lemma* is_separated_for_iff_generate
- \+ *lemma* is_separated_for_top
- \+ *lemma* extension_iff_amalgamation
- \+ *lemma* yoneda_condition_iff_sheaf_condition
- \+ *lemma* is_separated_for_and_exists_is_amalgamation_iff_sheaf_for
- \+ *lemma* is_separated_for.is_sheaf_for
- \+ *lemma* is_sheaf_for.is_separated_for
- \+ *lemma* is_sheaf_for.is_amalgamation
- \+ *lemma* is_sheaf_for.valid_glue
- \+ *lemma* is_sheaf_for_iff_generate
- \+ *lemma* is_sheaf_for_singleton_iso
- \+ *lemma* is_sheaf_for_top_sieve
- \+ *lemma* is_sheaf_for_iso
- \+ *lemma* is_sheaf_for_subsieve_aux
- \+ *lemma* is_sheaf_for_subsieve
- \+ *lemma* is_sheaf_for_coarser_topology
- \+ *lemma* separated_of_sheaf
- \+ *lemma* is_sheaf_iso
- \+ *lemma* is_sheaf_yoneda
- \+ *lemma* is_sheaf_pretopology
- \+ *lemma* w
- \+ *lemma* compatible_iff
- \+ *lemma* equalizer_sheaf_condition
- \+ *lemma* sheaf_condition
- \+ *def* family_of_elements
- \+ *def* family_of_elements.restrict
- \+ *def* family_of_elements.compatible
- \+ *def* family_of_elements.pullback_compatible
- \+ *def* family_of_elements.sieve_compatible
- \+ *def* family_of_elements.is_amalgamation
- \+ *def* is_separated_for
- \+ *def* is_sheaf_for
- \+ *def* yoneda_sheaf_condition
- \+ *def* nat_trans_equiv_compatible_family
- \+ *def* is_separated
- \+ *def* is_sheaf
- \+ *def* first_obj
- \+ *def* first_obj_eq_family
- \+ *def* fork_map
- \+ *def* second_obj
- \+ *def* first_map
- \+ *def* second_map



## [2020-11-18 07:06:12](https://github.com/leanprover-community/mathlib/commit/fec1a59)
feat(data/list): map lemmas paralleling functor ([#5028](https://github.com/leanprover-community/mathlib/pull/5028))
Adding `comp_map` and `map_comp_map`.
Docstrings done to match docstrings for equivalent `prod.map_comp_map`.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* comp_map
- \+ *lemma* map_comp_map

Modified src/data/multiset/functor.lean




## [2020-11-18 01:08:16](https://github.com/leanprover-community/mathlib/commit/19e3302)
chore(scripts): update nolints.txt ([#5029](https://github.com/leanprover-community/mathlib/pull/5029))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-17 17:53:52](https://github.com/leanprover-community/mathlib/commit/e92b5ac)
feat(algebra/opposites): Provide semimodule instances and op_linear_equiv ([#4954](https://github.com/leanprover-community/mathlib/pull/4954))
We already have a `has_scalar` definition via an `algebra` definition.
The definition used there satisfies a handful of other typeclasses too, and also allows for `op_add_equiv` to be stated more strongly as `op_linear_equiv`.
This also cuts back the imports a little on `algebra.module.basic`, which means formerly-transitive imports have to be added to downstream files.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *lemma* op_smul

Modified src/algebra/category/Group/limits.lean


Modified src/algebra/category/Mon/limits.lean


Modified src/algebra/module/basic.lean


Created src/algebra/module/opposites.lean
- \+ *lemma* coe_op_linear_equiv
- \+ *lemma* coe_op_linear_equiv_symm
- \+ *lemma* coe_op_linear_equiv_to_linear_map
- \+ *lemma* coe_op_linear_equiv_symm_to_linear_map
- \+ *lemma* op_linear_equiv_to_add_equiv
- \+ *lemma* op_linear_equiv_symm_to_add_equiv
- \+ *def* op_linear_equiv

Modified src/algebra/opposites.lean
- \+ *lemma* op_smul
- \+ *lemma* unop_smul

Modified src/algebra/pointwise.lean


Modified src/category_theory/action.lean


Modified src/data/finsupp/basic.lean


Modified src/group_theory/monoid_localization.lean




## [2020-11-17 15:27:56](https://github.com/leanprover-community/mathlib/commit/97fc8ce)
refactor(algebra/lie/basic): unbundle the action in `lie_module` ([#4959](https://github.com/leanprover-community/mathlib/pull/4959))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+/\- *lemma* add_lie
- \+/\- *lemma* lie_add
- \+/\- *lemma* smul_lie
- \+/\- *lemma* lie_smul
- \+ *lemma* leibniz_lie
- \+/\- *lemma* lie_zero
- \+/\- *lemma* zero_lie
- \+/\- *lemma* lie_self
- \+/\- *lemma* lie_skew
- \+/\- *lemma* neg_lie
- \+/\- *lemma* lie_neg
- \+/\- *lemma* gsmul_lie
- \+/\- *lemma* lie_gsmul
- \+ *lemma* lie_lie
- \+ *lemma* lie_jacobi
- \+/\- *lemma* commutator
- \+ *lemma* of_associative_ring_bracket
- \+/\- *lemma* commutative_ring_iff_abelian_lie_ring
- \+/\- *lemma* of_associative_algebra_hom_id
- \+/\- *lemma* of_associative_algebra_hom_apply
- \+/\- *lemma* of_associative_algebra_hom_comp
- \+ *lemma* lie_algebra.ad_apply
- \+/\- *lemma* lie_mem_left
- \- *lemma* lie_ring.of_associative_ring_bracket
- \- *lemma* endo_algebra_bracket
- \- *lemma* lie_act
- \- *lemma* lie_quotient_action_apply
- \+/\- *def* of_associative_algebra_hom
- \+ *def* lie_module.to_endo_morphism
- \+ *def* lie_algebra.ad
- \+ *def* action_as_endo_map
- \+ *def* action_as_endo_map_bracket
- \- *def* ad
- \- *def* lie_module.of_endo_morphism

Modified src/algebra/lie/classical.lean
- \+/\- *lemma* sl_non_abelian

Modified src/linear_algebra/basic.lean
- \+ *lemma* mul_eq_comp

Deleted src/linear_algebra/linear_action.lean
- \- *lemma* zero_linear_action
- \- *lemma* linear_action_zero
- \- *lemma* linear_action_add_act
- \- *lemma* linear_action_act_add
- \- *lemma* linear_action_act_smul
- \- *lemma* linear_action_smul_act
- \- *def* of_endo_map
- \- *def* to_endo_map

Modified src/ring_theory/derivation.lean
- \+ *lemma* sub_apply
- \+/\- *lemma* commutator_coe_linear_map

Modified test/transport/basic.lean
- \- *def* lie_ring.map



## [2020-11-17 12:21:38](https://github.com/leanprover-community/mathlib/commit/47476ef)
docs(references.bib): adds Samuel's Théorie Algébrique des Nombres ([#5018](https://github.com/leanprover-community/mathlib/pull/5018))
Added Samuel's Théorie Algébrique des Nombres
#### Estimated changes
Modified docs/references.bib




## [2020-11-17 12:21:36](https://github.com/leanprover-community/mathlib/commit/a59e76b)
feat(ring_theory/noetherian): add two lemmas on products of prime ideals ([#5013](https://github.com/leanprover-community/mathlib/pull/5013))
Add two lemmas saying that in a noetherian ring (resp. _integral domain)_ every (_nonzero_) ideal contains a (_nonzero_) product of prime ideals.
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* not_is_prime_iff

Modified src/ring_theory/noetherian.lean
- \+ *lemma* is_noetherian.induction
- \+ *lemma* exists_prime_spectrum_prod_le
- \+ *lemma* exists_prime_spectrum_prod_le_and_ne_bot_of_domain



## [2020-11-17 12:21:33](https://github.com/leanprover-community/mathlib/commit/86b0971)
feat(algebra/group_with_zero): Bundled `monoid_with_zero_hom` ([#4995](https://github.com/leanprover-community/mathlib/pull/4995))
This adds, without notation, `monoid_with_zero_hom` as a variant of `A →* B` that also satisfies `f 0 = 0`.
As part of this, this change:
* Splits up `group_with_zero` into multiple files, so that the definitions can be used in the bundled homs before any of the lemmas start pulling in dependencies
* Adds `monoid_with_zero_hom` as a base class of `ring_hom`
* Changes some `monoid_hom` objects into `monoid_with_zero_hom` objects.
* Moves some lemmas about `valuation` into `monoid_hom`, since they apply more generally
* Add automatic coercions between `monoid_with_zero_hom` and `monoid_hom`
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt


Modified src/algebra/field.lean
- \+/\- *lemma* map_ne_zero
- \+/\- *lemma* map_eq_zero
- \+/\- *lemma* map_inv
- \+/\- *lemma* map_div

Modified src/algebra/field_power.lean


Modified src/algebra/gcd_monoid.lean
- \+/\- *lemma* normalize_zero
- \+/\- *def* normalize

Modified src/algebra/geom_sum.lean


Modified src/algebra/group/hom.lean
- \+ *lemma* monoid_hom.coe_eq_to_one_hom
- \+ *lemma* monoid_hom.coe_eq_to_mul_hom
- \+ *lemma* monoid_with_zero_hom.coe_eq_to_monoid_hom
- \+ *lemma* monoid_with_zero_hom.coe_eq_to_zero_hom
- \+ *lemma* monoid_with_zero_hom.to_fun_eq_coe
- \+ *lemma* monoid_with_zero_hom.coe_mk
- \+ *lemma* monoid_with_zero_hom.to_zero_hom_coe
- \+ *lemma* monoid_with_zero_hom.to_monoid_hom_coe
- \+ *lemma* monoid_with_zero_hom.coe_inj
- \+ *lemma* monoid_with_zero_hom.ext
- \+ *lemma* monoid_with_zero_hom.ext_iff
- \+ *lemma* monoid_with_zero_hom.map_one
- \+ *lemma* monoid_with_zero_hom.map_zero
- \+ *lemma* monoid_with_zero_hom.map_mul
- \+ *lemma* monoid_with_zero_hom.id_apply
- \+ *lemma* monoid_with_zero_hom.coe_comp
- \+ *lemma* monoid_with_zero_hom.comp_apply
- \+ *lemma* monoid_with_zero_hom.comp_assoc
- \+ *lemma* monoid_with_zero_hom.cancel_right
- \+ *lemma* monoid_with_zero_hom.cancel_left
- \+ *lemma* monoid_with_zero_hom.comp_id
- \+ *lemma* monoid_with_zero_hom.id_comp
- \+ *theorem* monoid_with_zero_hom.congr_fun
- \+ *theorem* monoid_with_zero_hom.congr_arg
- \+ *def* monoid_with_zero_hom.id
- \+ *def* monoid_with_zero_hom.comp

Renamed src/algebra/group_with_zero.lean to src/algebra/group_with_zero/basic.lean
- \+ *lemma* monoid_hom.map_units_inv
- \- *lemma* zero_mul
- \- *lemma* mul_zero
- \- *lemma* mul_left_cancel'
- \- *lemma* mul_right_cancel'
- \- *lemma* inv_zero
- \- *lemma* mul_inv_cancel
- \- *lemma* map_units_inv

Created src/algebra/group_with_zero/default.lean


Created src/algebra/group_with_zero/defs.lean
- \+ *lemma* zero_mul
- \+ *lemma* mul_zero
- \+ *lemma* mul_left_cancel'
- \+ *lemma* mul_right_cancel'
- \+ *lemma* inv_zero
- \+ *lemma* mul_inv_cancel

Renamed src/algebra/group_with_zero_power.lean to src/algebra/group_with_zero/power.lean
- \+ *lemma* monoid_with_zero_hom.map_fpow
- \- *lemma* monoid_hom.map_fpow

Modified src/algebra/linear_ordered_comm_group_with_zero.lean
- \+ *lemma* map_neg
- \+ *lemma* map_sub_swap
- \+ *theorem* map_neg_one

Modified src/algebra/ordered_field.lean


Modified src/algebra/ordered_ring.lean
- \+/\- *def* abs_hom

Modified src/algebra/ring/basic.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *def* norm_hom

Modified src/data/quaternion.lean
- \- *lemma* norm_sq_zero
- \+/\- *def* norm_sq

Modified src/deprecated/subfield.lean


Modified src/field_theory/perfect_closure.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/valuation/basic.lean
- \+/\- *lemma* coe_coe
- \+/\- *lemma* map
- \+/\- *theorem* unit_map_eq
- \- *theorem* map_neg_one
- \+/\- *def* map

Modified test/ring_exp.lean




## [2020-11-17 12:21:30](https://github.com/leanprover-community/mathlib/commit/7a70764)
feat(ring_theory/fractional_ideal): helper lemmas for Dedekind domains ([#4994](https://github.com/leanprover-community/mathlib/pull/4994))
An assortment of lemmas and refactoring related to `fractional_ideal`s, used in the Dedekind domain project.
    
The motivation for creating this PR is that we are planning to remove the general `has_inv` instance on `fractional_ideal` (reserving it only for Dedekind domains), and we don't want to do the resulting refactoring twice. So we make sure everything is in the master branch, do the refactoring there, then merge the changes back into the work in progress branch.
Overview of the changes in `localization.lean`:
 * more `is_integer` lemmas
 * a localization of a noetherian ring is noetherian
 * generalize a few lemmas from integral domains to nontrivial `comm_ring`s
 * `algebra A (fraction_ring A)` instance
Overview of the changes in `fractional_ideal.lean`:
 * generalize many lemmas from integral domains to (nontrivial) `comm_ring`s (now `R` is notation for a `comm_ring` and `R₁` for an integral domain) 
 * `is_fractional_of_le`, `is_fractional_span_iff` and `is_fractional_of_fg`
 * many `simp` and `norm_cast` results involving `coe : ideal -> fractional_ideal` and `coe : fractional_ideal -> submodule`: now should be complete for `0`, `1`, `+`, `*`, `/` and `≤`.
 * use `1 : submodule` as `simp` normal form instead of `coe_submodule (1 : ideal)`
 * make the multiplication operation irreducible
 * port `submodule.has_mul` lemmas to `fractional_ideal.has_mul`
 * `simp` lemmas for `canonical_equiv`, `span_singleton`
 * many ways to prove `is_noetherian`
Co-Authored-By: Ashvni <ashvni.n@gmail.com>
Co-Authored-By: faenuccio <filippo.nuccio@univ-st-etienne.fr>
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+/\- *lemma* coe_mk
- \+ *lemma* ext_iff
- \+ *lemma* is_fractional_of_le
- \+/\- *lemma* coe_coe_ideal
- \+ *lemma* mem_coe_ideal
- \+/\- *lemma* coe_zero
- \+ *lemma* coe_to_fractional_ideal_bot
- \+ *lemma* exists_mem_to_map_eq
- \+ *lemma* coe_to_fractional_ideal_injective
- \+ *lemma* coe_to_fractional_ideal_eq_zero
- \+ *lemma* coe_to_fractional_ideal_ne_zero
- \+ *lemma* coe_to_submodule_eq_bot
- \+ *lemma* coe_to_submodule_ne_bot
- \+ *lemma* coe_one_eq_coe_submodule_one
- \+/\- *lemma* coe_one
- \+ *lemma* le_iff_mem
- \+ *lemma* coe_le_coe
- \+ *lemma* le_zero_iff
- \+ *lemma* mul_eq_mul
- \+ *lemma* mul_mem_mul
- \+ *lemma* mul_le
- \+ *lemma* add_le_add_left
- \+ *lemma* mul_le_mul_left
- \+ *lemma* le_self_mul_self
- \+ *lemma* mul_self_le_self
- \+ *lemma* coe_ideal_le_one
- \+ *lemma* le_one_iff_exists_coe_ideal
- \+/\- *lemma* coe_map
- \+/\- *lemma* map_coe_ideal
- \+ *lemma* coe_fun_map_equiv
- \+/\- *lemma* map_equiv_apply
- \+ *lemma* map_equiv_symm
- \+ *lemma* is_fractional_span_iff
- \+ *lemma* is_fractional_of_fg
- \+ *lemma* mem_canonical_equiv_apply
- \+ *lemma* canonical_equiv_symm
- \+ *lemma* canonical_equiv_flip
- \+/\- *lemma* exists_ne_zero_mem_is_integer
- \+/\- *lemma* map_ne_zero
- \+/\- *lemma* map_eq_zero_iff
- \+/\- *lemma* inv_zero
- \+ *lemma* coe_div
- \+ *lemma* mem_div_iff_of_nonzero
- \+ *lemma* mul_one_div_le_one
- \+ *lemma* le_self_mul_one_div
- \+ *lemma* le_div_iff_of_nonzero
- \+ *lemma* le_div_iff_mul_le
- \+/\- *lemma* map_div
- \+/\- *lemma* map_inv
- \+ *lemma* is_fractional_span_singleton
- \+ *lemma* mem_span_singleton
- \+ *lemma* mem_span_singleton_self
- \+/\- *lemma* eq_span_singleton_of_principal
- \+ *lemma* span_singleton_ne_zero_iff
- \+ *lemma* canonical_equiv_span_singleton
- \+ *lemma* one_div_span_singleton
- \+ *lemma* span_singleton_inv
- \+ *lemma* invertible_of_principal
- \+ *lemma* invertible_iff_generator_nonzero
- \+ *lemma* is_principal_inv
- \+ *lemma* div_span_singleton
- \+ *lemma* is_noetherian_zero
- \+ *lemma* is_noetherian_iff
- \+ *lemma* is_noetherian_coe_to_fractional_ideal
- \+ *lemma* is_noetherian_span_singleton_to_map_inv_mul
- \+ *lemma* is_noetherian
- \- *lemma* mem_coe
- \- *lemma* coe_ne_bot_iff_nonzero
- \- *lemma* le_iff
- \- *lemma* span_fractional_iff
- \- *lemma* span_singleton_fractional
- \+ *def* mul

Modified src/ring_theory/localization.lean
- \+ *lemma* is_integer_zero
- \+ *lemma* is_integer_one
- \+ *lemma* is_noetherian_ring



## [2020-11-17 11:18:37](https://github.com/leanprover-community/mathlib/commit/ad286fb)
feat(tactic/fresh_names): add tactics for giving hyps fresh names ([#4987](https://github.com/leanprover-community/mathlib/pull/4987))
This commit adds a variant of `rename` which guarantees that the renamed
hypotheses receive fresh names. To implement this, we also add more flexible
variants of `get_unused_name`, `intro_fresh` and `intro_lst_fresh`.
#### Estimated changes
Created src/tactic/fresh_names.lean


Created test/fresh_names.lean




## [2020-11-17 02:15:30](https://github.com/leanprover-community/mathlib/commit/a2f3399)
chore(scripts): update nolints.txt ([#5016](https://github.com/leanprover-community/mathlib/pull/5016))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-16 23:47:31](https://github.com/leanprover-community/mathlib/commit/53f71f8)
feat(data/list): list last lemmas ([#5015](https://github.com/leanprover-community/mathlib/pull/5015))
list last lemmas letting lean learn little logical links
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* last_map
- \+ *lemma* last_pmap



## [2020-11-16 14:15:33](https://github.com/leanprover-community/mathlib/commit/b588fc4)
chore(*) Unused have statements in term mode ([#5012](https://github.com/leanprover-community/mathlib/pull/5012))
Remove unneeded have statements.
#### Estimated changes
Modified src/algebra/quadratic_discriminant.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/analysis/specific_limits.lean


Modified src/category_theory/abelian/non_preadditive.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/modeq.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/polynomial/div.lean


Modified src/data/real/hyperreal.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/basic.lean


Modified src/number_theory/pell.lean


Modified src/number_theory/sum_four_squares.lean




## [2020-11-16 09:03:03](https://github.com/leanprover-community/mathlib/commit/90fa510)
feat(analysis/special_functions/pow): rpow is measurable ([#5008](https://github.com/leanprover-community/mathlib/pull/5008))
Prove the measurability of rpow in two cases: real and nnreal.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* real.measurable_rpow
- \+ *lemma* measurable.rpow
- \+ *lemma* real.measurable_rpow_const
- \+ *lemma* measurable.rpow_const
- \+ *lemma* nnreal.measurable_rpow
- \+ *lemma* measurable.nnreal_rpow
- \+ *lemma* nnreal.measurable_rpow_const
- \+ *lemma* measurable.nnreal_rpow_const



## [2020-11-16 01:22:58](https://github.com/leanprover-community/mathlib/commit/4cd2438)
chore(scripts): update nolints.txt ([#5011](https://github.com/leanprover-community/mathlib/pull/5011))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-16 00:17:12](https://github.com/leanprover-community/mathlib/commit/470ac77)
feat(category_theory/monad): monadic functor really creates limits ([#4931](https://github.com/leanprover-community/mathlib/pull/4931))
Show that a monadic functor `creates_limits`, and a partial result for colimits.
#### Estimated changes
Modified src/category_theory/monad/limits.lean
- \- *lemma* monadic_creates_limits
- \+ *def* monadic_creates_limits
- \+ *def* monadic_creates_colimits_of_shape_of_preserves_colimits_of_shape
- \+ *def* monadic_creates_colimits_of_preserves_colimits



## [2020-11-15 14:10:11](https://github.com/leanprover-community/mathlib/commit/9631594)
feat(algebra/star): star monoids, rings and algebras ([#4886](https://github.com/leanprover-community/mathlib/pull/4886))
#### Estimated changes
Created src/algebra/star/algebra.lean
- \+ *lemma* star_smul

Created src/algebra/star/basic.lean
- \+ *lemma* star_star
- \+ *lemma* star_injective
- \+ *lemma* star_mul
- \+ *lemma* star_one
- \+ *lemma* star_add
- \+ *lemma* star_zero
- \+ *lemma* star_sum
- \+ *lemma* star_neg
- \+ *lemma* star_sub
- \+ *lemma* star_bit0
- \+ *lemma* star_bit1
- \+ *lemma* star_id_of_comm
- \+ *def* star
- \+ *def* star_mul_equiv
- \+ *def* star_add_equiv
- \+ *def* star_ring_equiv
- \+ *def* star_ring_of_comm

Modified src/data/complex/basic.lean


Modified src/data/matrix/basic.lean
- \+ *lemma* map_map
- \+ *lemma* star_apply

Modified src/data/real/basic.lean




## [2020-11-15 04:56:07](https://github.com/leanprover-community/mathlib/commit/9dd9b6b)
refactor(archive/imo/imo1969_q1): prove `infinite` statement, cleanup ([#4391](https://github.com/leanprover-community/mathlib/pull/4391))
The previous formalization didn't quite prove that there were infinitely many natural numbers with the desired property, but rather that for any natural number there's a larger one with the property. This PR changes the ending to prove that the set of integers described in the problem statement is `infinite`.
#### Estimated changes
Modified archive/imo/imo1969_q1.lean
- \+/\- *lemma* factorization
- \+/\- *lemma* left_factor_large
- \+/\- *lemma* right_factor_large
- \+/\- *lemma* int_large
- \+ *lemma* not_prime_of_int_mul'
- \+/\- *lemma* polynomial_not_prime
- \+ *lemma* a_choice_good
- \+ *lemma* a_choice_strict_mono
- \- *lemma* int_not_prime
- \+/\- *theorem* imo1969_q1
- \+ *def* good_nats
- \+ *def* a_choice

Modified src/data/int/basic.lean
- \+ *lemma* nat_abs_mul_nat_abs_eq

Created src/data/int/nat_prime.lean
- \+ *lemma* not_prime_of_int_mul

Modified src/data/nat/basic.lean
- \+ *lemma* strict_mono.nat_pow

Modified src/data/nat/prime.lean
- \+ *lemma* not_prime_mul'
- \+/\- *lemma* factors_unique
- \- *lemma* not_prime_helper

Modified src/data/set/finite.lean
- \+/\- *lemma* eq_finite_Union_of_finite_subset_Union
- \+ *theorem* infinite_image_iff
- \+ *theorem* infinite_of_inj_on_maps_to
- \+ *theorem* infinite_range_of_injective
- \+ *theorem* infinite_of_injective_forall_mem
- \+/\- *theorem* finite_Union



## [2020-11-15 01:46:16](https://github.com/leanprover-community/mathlib/commit/7e27d94)
chore(scripts): update nolints.txt ([#5007](https://github.com/leanprover-community/mathlib/pull/5007))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-15 01:46:14](https://github.com/leanprover-community/mathlib/commit/447b18f)
chore(data/polynomial/degree): consolidate all `polynomial.degree` files in one folder ([#5005](https://github.com/leanprover-community/mathlib/pull/5005))
Moves `data/polynomial/degree.lean` to `data/polynomial/degree`, which already exists, renames it `lemmas.lean`
Renames `data/polynomial/degree/basic.lean` to `definitions.lean`
Adds `data/polynomial/degree/default.lean`, which just imports `lemmas.lean`
#### Estimated changes
Modified src/data/polynomial/cancel_leads.lean


Created src/data/polynomial/degree/default.lean


Renamed src/data/polynomial/degree/basic.lean to src/data/polynomial/degree/definitions.lean


Renamed src/data/polynomial/degree.lean to src/data/polynomial/degree/lemmas.lean


Modified src/data/polynomial/degree/trailing_degree.lean


Modified src/data/polynomial/erase_lead.lean


Modified src/data/polynomial/eval.lean


Modified src/data/polynomial/lifts.lean




## [2020-11-15 01:46:12](https://github.com/leanprover-community/mathlib/commit/fca7eba)
chore(analysis/calculus/deriv): composition of `g : 𝕜 → 𝕜` with `f : E → 𝕜` ([#4871](https://github.com/leanprover-community/mathlib/pull/4871))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *theorem* has_deriv_at_filter.comp_has_fderiv_at_filter
- \+ *theorem* has_deriv_at.comp_has_fderiv_at
- \+ *theorem* has_deriv_at.comp_has_fderiv_within_at
- \+ *theorem* has_deriv_within_at.comp_has_fderiv_within_at

Modified src/topology/continuous_on.lean
- \+ *theorem* continuous_within_at.tendsto_nhds_within



## [2020-11-15 00:37:55](https://github.com/leanprover-community/mathlib/commit/e6e8275)
chore(linear_algebra/char_poly): put everything `char_poly` in one folder ([#5004](https://github.com/leanprover-community/mathlib/pull/5004))
Moves `char_poly` to `char_poly.basic`, because the folder already exists
#### Estimated changes
Renamed src/linear_algebra/char_poly.lean to src/linear_algebra/char_poly/basic.lean


Modified src/linear_algebra/char_poly/coeff.lean




## [2020-11-14 23:13:25](https://github.com/leanprover-community/mathlib/commit/6544244)
feat(data/polynomial) small refactor and golf ([#5002](https://github.com/leanprover-community/mathlib/pull/5002))
Factor out the lemma that roots of the normalization equal the roots of a polynomial and golf a proof a tiny bit.
#### Estimated changes
Modified src/data/polynomial/field_division.lean
- \+ *lemma* roots_normalize

Modified src/field_theory/splitting_field.lean
- \+/\- *lemma* C_leading_coeff_mul_prod_multiset_X_sub_C
- \+/\- *lemma* splits_iff_card_roots

Modified src/ring_theory/polynomial/cyclotomic.lean




## [2020-11-14 22:08:14](https://github.com/leanprover-community/mathlib/commit/0582237)
feat(analysis): seminorms and local convexity ([#4827](https://github.com/leanprover-community/mathlib/pull/4827))
#### Estimated changes
Modified docs/references.bib


Created src/analysis/seminorm.lean
- \+ *lemma* balanced.absorbs_self
- \+ *lemma* absorbent_nhds_zero
- \+ *lemma* balanced_zero_union_interior
- \+ *lemma* balanced.interior
- \+ *lemma* balanced.closure
- \+ *lemma* nonneg
- \+ *lemma* sub_rev
- \+ *lemma* mem_ball
- \+ *lemma* mem_ball_zero
- \+ *lemma* ball_zero_eq
- \+ *lemma* balanced_ball_zero
- \+ *def* absorbs
- \+ *def* absorbent
- \+ *def* balanced
- \+ *def* ball



## [2020-11-14 19:46:53](https://github.com/leanprover-community/mathlib/commit/633c2a6)
feat(ring_theory/gauss_lemma): two primitive polynomials divide iff they do in a fraction field ([#5003](https://github.com/leanprover-community/mathlib/pull/5003))
Shows `polynomial.is_primitive.dvd_iff_fraction_map_dvd_fraction_map`, that two primitive polynomials divide iff they do over a fraction field.
Shows `polynomial.is_primitive.int.dvd_iff_map_cast_dvd_map_cast`, the version for integers and rationals.
#### Estimated changes
Modified src/ring_theory/polynomial/gauss_lemma.lean
- \+ *lemma* is_primitive.dvd_of_fraction_map_dvd_fraction_map
- \+ *lemma* is_primitive.dvd_iff_fraction_map_dvd_fraction_map
- \+ *lemma* is_primitive.int.dvd_iff_map_cast_dvd_map_cast



## [2020-11-14 19:46:51](https://github.com/leanprover-community/mathlib/commit/0092414)
feat(data/nat/choose/sum): alternating binomial coefficient sums ([#4997](https://github.com/leanprover-community/mathlib/pull/4997))
Evaluates some sums related to binomial coefficients with alternating signs
#### Estimated changes
Modified src/data/finset/powerset.lean
- \+ *theorem* powerset_len_eq_filter

Modified src/data/nat/choose/sum.lean
- \+ *theorem* int.alternating_sum_range_choose
- \+ *theorem* int.alternating_sum_range_choose_of_ne
- \+ *theorem* sum_powerset_apply_card
- \+ *theorem* sum_powerset_neg_one_pow_card
- \+ *theorem* sum_powerset_neg_one_pow_card_of_nonempty



## [2020-11-14 18:20:15](https://github.com/leanprover-community/mathlib/commit/9b887d5)
feat(measure_theory/lp_space): Define Lp spaces ([#4993](https://github.com/leanprover-community/mathlib/pull/4993))
Define the space Lp of functions for which the norm raised to the power p has finite integral.
Define the seminorm on that space (without proof that it is a seminorm, for now).
Add three lemmas to analysis/special_functions/pow.lean about ennreal.rpow
<!--
put comments you want to keep out of the PR commit here.
If this PR depends on other PRs, please list them below this comment,
using the following format:
- [ ] depends on: #abc [optional extra text]
- [ ] depends on: #xyz [optional extra text]
-->
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* rpow_eq_top_of_nonneg
- \+ *lemma* rpow_ne_top_of_nonneg
- \+ *lemma* rpow_lt_top_of_nonneg

Created src/measure_theory/lp_space.lean
- \+ *lemma* lintegral_rpow_nnnorm_eq_rpow_snorm
- \+ *lemma* mem_ℒp_one_iff_integrable
- \+ *lemma* mem_ℒp.snorm_lt_top
- \+ *lemma* mem_ℒp.snorm_ne_top
- \+ *lemma* lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top
- \+ *lemma* mem_ℒp_of_snorm_lt_top
- \+ *lemma* zero_mem_ℒp
- \+ *lemma* snorm_zero
- \+ *def* mem_ℒp
- \+ *def* snorm



## [2020-11-14 12:34:53](https://github.com/leanprover-community/mathlib/commit/70ca6fd)
feat(ring_theory/power_basis): `equiv`s between algebras with the same power basis ([#4986](https://github.com/leanprover-community/mathlib/pull/4986))
`power_basis.lift` and `power_basis.equiv` use the power basis structure to define `alg_hom`s and `alg_equiv`s.
    
The main application in this PR is `power_basis.equiv_adjoin_simple`, which states that adjoining an element of a power basis of `L : K` gives `L` itself.
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* aeval_eq_sum_range
- \+ *lemma* aeval_eq_sum_range'

Modified src/data/polynomial/degree/basic.lean
- \+ *lemma* degree_add_eq_left_of_degree_lt
- \+ *lemma* degree_add_eq_right_of_degree_lt
- \+ *lemma* degree_sum_fin_lt
- \+ *lemma* degree_sub_eq_left_of_degree_lt
- \+ *lemma* degree_sub_eq_right_of_degree_lt
- \- *lemma* degree_add_eq_of_degree_lt

Modified src/data/polynomial/div.lean
- \+ *lemma* eval₂_mod_by_monic_eq_self_of_root

Modified src/data/polynomial/eval.lean
- \+ *lemma* eval₂_eq_sum_range'

Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/lifts.lean


Modified src/data/polynomial/monic.lean
- \+ *lemma* monic_add_of_left
- \+ *lemma* monic_add_of_right

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* aeval_mod_by_monic_eq_self_of_root

Modified src/field_theory/minimal_polynomial.lean
- \+/\- *lemma* ne_zero

Modified src/linear_algebra/char_poly/coeff.lean


Modified src/ring_theory/power_basis.lean
- \+ *lemma* dim_ne_zero
- \+ *lemma* exists_eq_aeval
- \+ *lemma* nat_degree_minpoly_gen
- \+ *lemma* minpoly_gen_monic
- \+ *lemma* aeval_minpoly_gen
- \+ *lemma* is_integral_gen
- \+ *lemma* dim_le_nat_degree_of_root
- \+ *lemma* nat_degree_minimal_polynomial
- \+ *lemma* nat_degree_lt_nat_degree
- \+ *lemma* constr_pow_aeval
- \+ *lemma* constr_pow_gen
- \+ *lemma* constr_pow_algebra_map
- \+ *lemma* constr_pow_mul
- \+ *lemma* lift_gen
- \+ *lemma* lift_aeval
- \+ *lemma* equiv_aeval
- \+ *lemma* equiv_gen
- \+ *lemma* equiv_symm
- \+ *lemma* adjoin.power_basis.gen_eq
- \+ *lemma* equiv_adjoin_simple_aeval
- \+ *lemma* equiv_adjoin_simple_gen
- \+ *lemma* equiv_adjoin_simple_symm_aeval
- \+ *lemma* equiv_adjoin_simple_symm_gen
- \- *lemma* finite_dimensional
- \- *lemma* findim



## [2020-11-14 12:34:51](https://github.com/leanprover-community/mathlib/commit/6bac899)
feat(category_theory/limits/preserves): functor product preserves colims ([#4941](https://github.com/leanprover-community/mathlib/pull/4941))
#### Estimated changes
Created src/category_theory/limits/preserves/functor_category.lean
- \+ *def* functor_category.prod_preserves_colimits



## [2020-11-14 12:34:49](https://github.com/leanprover-community/mathlib/commit/154d73d)
feat(category_theory/equivalence): equivalence of functor categories ([#4940](https://github.com/leanprover-community/mathlib/pull/4940))
#### Estimated changes
Modified src/category_theory/equivalence.lean
- \+ *def* congr_left
- \+ *def* congr_right



## [2020-11-14 12:34:46](https://github.com/leanprover-community/mathlib/commit/a0341a8)
feat(category_theory/limits/creates): transfer creating limits through nat iso ([#4938](https://github.com/leanprover-community/mathlib/pull/4938))
`creates` version of [#4934](https://github.com/leanprover-community/mathlib/pull/4934)
#### Estimated changes
Modified src/category_theory/limits/creates.lean
- \+ *def* creates_limit_of_nat_iso
- \+ *def* creates_limits_of_shape_of_nat_iso
- \+ *def* creates_limits_of_nat_iso
- \+ *def* creates_colimit_of_nat_iso
- \+ *def* creates_colimits_of_shape_of_nat_iso
- \+ *def* creates_colimits_of_nat_iso

Modified src/category_theory/limits/preserves/basic.lean




## [2020-11-14 12:34:45](https://github.com/leanprover-community/mathlib/commit/ccc1431)
feat(ring_theory/ideal_operations): prime avoidance ([#773](https://github.com/leanprover-community/mathlib/pull/773))
```lean
/-- Prime avoidance. Atiyah-Macdonald 1.11, Eisenbud 3.3, Stacks 10.14.2 (00DS), Matsumura Ex.1.6. -/
theorem subset_union_prime {s : finset ι} {f : ι → ideal R} (a b : ι)
  (hp : ∀ i ∈ s, i ≠ a → i ≠ b → is_prime (f i)) {I : ideal R} :
  (I : set R) ⊆ (⋃ i ∈ (↑s : set ι), f i) ↔ ∃ i ∈ s, I ≤ f i :=
```
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *theorem* prod_le_inf
- \+ *theorem* is_prime.mul_le
- \+ *theorem* is_prime.inf_le
- \+ *theorem* is_prime.prod_le
- \+ *theorem* is_prime.inf_le'
- \+ *theorem* subset_union
- \+ *theorem* subset_union_prime'
- \+ *theorem* subset_union_prime



## [2020-11-14 11:02:55](https://github.com/leanprover-community/mathlib/commit/5f15104)
feat(algebra/squarefree): Defines squarefreeness, proves several equivalences ([#4981](https://github.com/leanprover-community/mathlib/pull/4981))
Defines when a monoid element is `squarefree`
Proves basic lemmas to determine squarefreeness
Proves squarefreeness criteria in terms of `multiplicity`, `unique_factorization_monoid.factors`, and `nat.factors`
#### Estimated changes
Created src/algebra/squarefree.lean
- \+ *lemma* is_unit.squarefree
- \+ *lemma* squarefree_one
- \+ *lemma* not_squarefree_zero
- \+ *lemma* irreducible.squarefree
- \+ *lemma* prime.squarefree
- \+ *lemma* squarefree_of_dvd_of_squarefree
- \+ *lemma* squarefree_iff_multiplicity_le_one
- \+ *lemma* squarefree_iff_nodup_factors
- \+ *def* squarefree

Modified src/ring_theory/multiplicity.lean
- \+ *lemma* multiplicity_le_multiplicity_of_dvd



## [2020-11-14 01:13:48](https://github.com/leanprover-community/mathlib/commit/4db26af)
chore(scripts): update nolints.txt ([#4999](https://github.com/leanprover-community/mathlib/pull/4999))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-13 22:06:40](https://github.com/leanprover-community/mathlib/commit/9ed9e0f)
feat(tactic/has_variable_names): add tactic for type-based naming ([#4988](https://github.com/leanprover-community/mathlib/pull/4988))
When we name hypotheses or variables, we often do so in a type-directed fashion:
a hypothesis of type `ℕ` is called `n` or `m`; a hypothesis of type `list ℕ` is
called `ns`; etc. This commits adds a tactic which looks up typical variable
names for a given type. Typical variable names are registered by giving an
instance of the new type class `has_variable_names`. We also give instances of
this type class for many core types.
#### Estimated changes
Created src/tactic/has_variable_names.lean
- \+ *def* foo
- \+ *def* make_listlike_instance
- \+ *def* make_inheriting_instance



## [2020-11-13 19:42:11](https://github.com/leanprover-community/mathlib/commit/050b837)
feat(field_theory/adjoin): Adjoin integral element ([#4831](https://github.com/leanprover-community/mathlib/pull/4831))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+/\- *lemma* disjoint_to_finset
- \+ *theorem* to_finset_card_of_nodup

Modified src/field_theory/adjoin.lean
- \+ *lemma* adjoin_simple_to_subalgebra_of_integral
- \+ *lemma* card_alg_hom_adjoin_integral

Modified src/field_theory/fixed.lean




## [2020-11-13 17:59:05](https://github.com/leanprover-community/mathlib/commit/eeb2057)
feat(ring_theory/unique_factorization_domain): connecting `multiplicity` to `unique_factorization_domain.factors` ([#4980](https://github.com/leanprover-community/mathlib/pull/4980))
Connects multiplicity of an irreducible to the multiset of irreducible factors
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* associated_pow_pow

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* le_multiplicity_iff_repeat_le_factors
- \+ *lemma* multiplicity_eq_count_factors



## [2020-11-13 11:15:04](https://github.com/leanprover-community/mathlib/commit/1a233e0)
feat(analysis/calculus): derivative is measurable ([#4974](https://github.com/leanprover-community/mathlib/pull/4974))
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* fderiv_mem_iff

Created src/analysis/calculus/fderiv_measurable.lean
- \+ *lemma* measurable_apply
- \+ *lemma* measurable_apply'
- \+ *lemma* measurable_apply₂
- \+ *lemma* measurable_coe
- \+ *lemma* is_open_A
- \+ *lemma* is_open_B
- \+ *lemma* A_mono
- \+ *lemma* le_of_mem_A
- \+ *lemma* mem_A_of_differentiable
- \+ *lemma* norm_sub_le_of_mem_A
- \+ *lemma* differentiable_set_subset_D
- \+ *lemma* D_subset_differentiable_set
- \+ *lemma* measurable_fderiv
- \+ *lemma* measurable_fderiv_apply_const
- \+ *lemma* measurable_deriv
- \+ *theorem* differentiable_set_eq_D
- \+ *theorem* is_measurable_set_of_differentiable_at_of_is_complete
- \+ *theorem* is_measurable_set_of_differentiable_at
- \+ *def* A
- \+ *def* B
- \+ *def* D

Modified src/topology/metric_space/premetric_space.lean




## [2020-11-13 01:25:28](https://github.com/leanprover-community/mathlib/commit/140d8b4)
chore(scripts): update nolints.txt ([#4992](https://github.com/leanprover-community/mathlib/pull/4992))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-12 23:23:14](https://github.com/leanprover-community/mathlib/commit/6b3a2d1)
feat(archive/imo): formalize IMO 1964 problem 1 ([#4935](https://github.com/leanprover-community/mathlib/pull/4935))
This is an alternative approach to [#4369](https://github.com/leanprover-community/mathlib/pull/4369), where progress seems to have stalled. I avoid integers completely by working with `nat.modeq`, and deal with the cases of n mod 3 by simply breaking into three cases.
#### Estimated changes
Created archive/imo/imo1964_q1.lean
- \+ *lemma* two_pow_three_mul_mod_seven
- \+ *lemma* two_pow_three_mul_add_one_mod_seven
- \+ *lemma* two_pow_three_mul_add_two_mod_seven
- \+ *lemma* aux
- \+ *theorem* imo1964_q1a
- \+ *theorem* imo1964_q1b
- \+ *def* problem_predicate

Modified src/data/nat/modeq.lean
- \+ *theorem* modeq_pow



## [2020-11-12 16:36:44](https://github.com/leanprover-community/mathlib/commit/6e64df5)
chore(deprecated/group): Do not import `deprecated` from `equiv/mul_add` ([#4989](https://github.com/leanprover-community/mathlib/pull/4989))
This swaps the direction of the import, which makes the deprecated instances for `mul_equiv` be in the same place as the instances for `monoid_hom`.
#### Estimated changes
Modified src/data/equiv/mul_add.lean


Modified src/deprecated/group.lean




## [2020-11-12 16:36:42](https://github.com/leanprover-community/mathlib/commit/97a7f57)
chore(algebra/direct_limit): Use bundled morphisms ([#4964](https://github.com/leanprover-community/mathlib/pull/4964))
This introduced some ugliness in the form of `(λ i j h, f i j h)`, which is a little unfortunate
#### Estimated changes
Modified src/algebra/direct_limit.lean
- \+/\- *lemma* lift_unique
- \+/\- *lemma* of.zero_exact
- \- *lemma* of_zero
- \- *lemma* of_add
- \- *lemma* of_neg
- \- *lemma* of_sub
- \- *lemma* lift_zero
- \- *lemma* lift_add
- \- *lemma* lift_neg
- \- *lemma* lift_sub
- \- *lemma* of_one
- \- *lemma* of_mul
- \- *lemma* of_pow
- \- *lemma* lift_one
- \- *lemma* lift_mul
- \- *lemma* lift_pow
- \+/\- *theorem* of.zero_exact
- \+/\- *theorem* polynomial.exists_of
- \+/\- *theorem* of_injective
- \+/\- *theorem* lift_unique
- \+/\- *def* direct_limit
- \+/\- *def* of
- \+/\- *def* lift
- \- *def* lift_hom



## [2020-11-12 14:19:46](https://github.com/leanprover-community/mathlib/commit/34215fc)
feat(group_theory/sub{monoid,group}): Add `closure_induction'` for subtypes ([#4984](https://github.com/leanprover-community/mathlib/pull/4984))
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* closure_induction'

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* closure_induction'



## [2020-11-12 12:14:35](https://github.com/leanprover-community/mathlib/commit/7404f0e)
feat(algebra/pointwise): lemmas relating to submonoids ([#4960](https://github.com/leanprover-community/mathlib/pull/4960))
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* mul_subset
- \+ *lemma* mul_subset_closure



## [2020-11-12 08:28:56](https://github.com/leanprover-community/mathlib/commit/593013d)
feat(algebra/quandle): Bundle `rack.to_envel_group.map` into an equiv ([#4978](https://github.com/leanprover-community/mathlib/pull/4978))
This also cleans up some non-terminal simp tactics
#### Estimated changes
Modified src/algebra/quandle.lean
- \+/\- *def* to_envel_group.map



## [2020-11-12 04:06:42](https://github.com/leanprover-community/mathlib/commit/3f575d7)
feat(group_theory/subgroup) top is a normal subgroup ([#4982](https://github.com/leanprover-community/mathlib/pull/4982))
#### Estimated changes
Modified src/group_theory/subgroup.lean




## [2020-11-12 02:51:51](https://github.com/leanprover-community/mathlib/commit/509a224)
chore(scripts): update nolints.txt ([#4983](https://github.com/leanprover-community/mathlib/pull/4983))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-12 00:24:20](https://github.com/leanprover-community/mathlib/commit/f6c8d81)
feat(algebra/group/with_one): Use an equiv for `lift` ([#4975](https://github.com/leanprover-community/mathlib/pull/4975))
#### Estimated changes
Modified src/algebra/group/with_one.lean
- \+/\- *def* lift



## [2020-11-12 00:24:16](https://github.com/leanprover-community/mathlib/commit/49cf28f)
feat(data/matrix): little lemmas on `map` ([#4874](https://github.com/leanprover-community/mathlib/pull/4874))
I had a couple of expressions involving mapping matrices, that the simplifier didn't `simp` away. It turns out the missing lemmas already existed, just not with the correct form / hypotheses. So here they are.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_hom_map_one
- \+ *lemma* alg_equiv_map_one
- \+ *lemma* alg_hom_map_zero
- \+ *lemma* alg_equiv_map_zero

Modified src/data/matrix/basic.lean
- \+ *lemma* ring_hom_map_one
- \+ *lemma* ring_equiv_map_one
- \+ *lemma* zero_hom_map_zero
- \+ *lemma* add_monoid_hom_map_zero
- \+ *lemma* add_equiv_map_zero
- \+ *lemma* linear_map_map_zero
- \+ *lemma* linear_equiv_map_zero
- \+ *lemma* ring_hom_map_zero
- \+ *lemma* ring_equiv_map_zero



## [2020-11-11 22:13:41](https://github.com/leanprover-community/mathlib/commit/67309a4)
refactor(group_theory/group_action): Break the file into three pieces ([#4936](https://github.com/leanprover-community/mathlib/pull/4936))
I found myself fighting import cycles when trying to define `has_scalar` instances in files that are early in the import tree.
By creating a separate `defs` file with minimal dependencies, this ought to become easier.
This also adds documentation.
None of the proofs or lemma statements have been touched.
#### Estimated changes
Modified src/algebra/group_action_hom.lean


Modified src/algebra/group_ring_action.lean


Deleted src/group_theory/group_action.lean
- \- *lemma* smul_comm_class.symm
- \- *lemma* smul_smul
- \- *lemma* units.inv_smul_smul
- \- *lemma* units.smul_inv_smul
- \- *lemma* units.smul_left_cancel
- \- *lemma* units.smul_eq_iff_eq_inv_smul
- \- *lemma* is_unit.smul_left_cancel
- \- *lemma* inv_smul_smul'
- \- *lemma* smul_inv_smul'
- \- *lemma* inv_smul_eq_iff'
- \- *lemma* eq_inv_smul_iff'
- \- *lemma* ite_smul
- \- *lemma* smul_ite
- \- *lemma* smul_assoc
- \- *lemma* smul_one_smul
- \- *lemma* mem_orbit_iff
- \- *lemma* mem_orbit
- \- *lemma* mem_orbit_self
- \- *lemma* mem_stabilizer_iff
- \- *lemma* mem_fixed_points
- \- *lemma* mem_fixed_by
- \- *lemma* mem_fixed_points'
- \- *lemma* to_fun_apply
- \- *lemma* inv_smul_smul
- \- *lemma* smul_inv_smul
- \- *lemma* inv_smul_eq_iff
- \- *lemma* eq_inv_smul_iff
- \- *lemma* orbit_eq_iff
- \- *lemma* mem_orbit_smul
- \- *lemma* smul_mem_orbit_smul
- \- *lemma* const_smul_hom_apply
- \- *lemma* list.smul_sum
- \- *lemma* multiset.smul_sum
- \- *lemma* finset.smul_sum
- \- *theorem* one_smul
- \- *theorem* fixed_eq_Inter_fixed_by
- \- *theorem* of_quotient_stabilizer_mk
- \- *theorem* of_quotient_stabilizer_mem_orbit
- \- *theorem* of_quotient_stabilizer_smul
- \- *theorem* injective_of_quotient_stabilizer
- \- *theorem* orbit_equiv_quotient_stabilizer_symm_apply
- \- *theorem* smul_add
- \- *theorem* smul_zero
- \- *theorem* units.smul_eq_zero
- \- *theorem* units.smul_ne_zero
- \- *theorem* is_unit.smul_eq_zero
- \- *theorem* smul_neg
- \- *theorem* smul_sub
- \- *def* units.smul_perm_hom
- \- *def* regular
- \- *def* orbit
- \- *def* stabilizer_carrier
- \- *def* fixed_points
- \- *def* fixed_by
- \- *def* comp_hom
- \- *def* stabilizer.submonoid
- \- *def* to_fun
- \- *def* stabilizer
- \- *def* to_perm
- \- *def* stabilizer.subgroup
- \- *def* orbit_rel
- \- *def* mul_left_cosets
- \- *def* of_quotient_stabilizer
- \- *def* const_smul_hom

Created src/group_theory/group_action/basic.lean
- \+ *lemma* mem_orbit_iff
- \+ *lemma* mem_orbit
- \+ *lemma* mem_orbit_self
- \+ *lemma* mem_stabilizer_iff
- \+ *lemma* mem_fixed_points
- \+ *lemma* mem_fixed_by
- \+ *lemma* mem_fixed_points'
- \+ *lemma* orbit_eq_iff
- \+ *lemma* mem_orbit_smul
- \+ *lemma* smul_mem_orbit_smul
- \+ *lemma* list.smul_sum
- \+ *lemma* multiset.smul_sum
- \+ *lemma* finset.smul_sum
- \+ *theorem* fixed_eq_Inter_fixed_by
- \+ *theorem* of_quotient_stabilizer_mk
- \+ *theorem* of_quotient_stabilizer_mem_orbit
- \+ *theorem* of_quotient_stabilizer_smul
- \+ *theorem* injective_of_quotient_stabilizer
- \+ *theorem* orbit_equiv_quotient_stabilizer_symm_apply
- \+ *def* orbit
- \+ *def* stabilizer_carrier
- \+ *def* fixed_points
- \+ *def* fixed_by
- \+ *def* stabilizer.submonoid
- \+ *def* stabilizer
- \+ *def* stabilizer.subgroup
- \+ *def* orbit_rel
- \+ *def* mul_left_cosets
- \+ *def* of_quotient_stabilizer

Created src/group_theory/group_action/default.lean


Created src/group_theory/group_action/defs.lean
- \+ *lemma* smul_comm_class.symm
- \+ *lemma* smul_assoc
- \+ *lemma* smul_smul
- \+ *lemma* ite_smul
- \+ *lemma* smul_ite
- \+ *lemma* to_fun_apply
- \+ *lemma* smul_one_smul
- \+ *lemma* const_smul_hom_apply
- \+ *theorem* one_smul
- \+ *theorem* smul_add
- \+ *theorem* smul_zero
- \+ *theorem* smul_neg
- \+ *theorem* smul_sub
- \+ *def* regular
- \+ *def* to_fun
- \+ *def* comp_hom
- \+ *def* const_smul_hom

Created src/group_theory/group_action/group.lean
- \+ *lemma* units.inv_smul_smul
- \+ *lemma* units.smul_inv_smul
- \+ *lemma* units.smul_left_cancel
- \+ *lemma* units.smul_eq_iff_eq_inv_smul
- \+ *lemma* is_unit.smul_left_cancel
- \+ *lemma* inv_smul_smul'
- \+ *lemma* smul_inv_smul'
- \+ *lemma* inv_smul_eq_iff'
- \+ *lemma* eq_inv_smul_iff'
- \+ *lemma* inv_smul_smul
- \+ *lemma* smul_inv_smul
- \+ *lemma* inv_smul_eq_iff
- \+ *lemma* eq_inv_smul_iff
- \+ *theorem* units.smul_eq_zero
- \+ *theorem* units.smul_ne_zero
- \+ *theorem* is_unit.smul_eq_zero
- \+ *def* units.smul_perm_hom
- \+ *def* mul_action.to_perm



## [2020-11-11 19:36:52](https://github.com/leanprover-community/mathlib/commit/743a104)
chore(algebra): trivial lemmas on powers ([#4977](https://github.com/leanprover-community/mathlib/pull/4977))
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_lt_pow_iff

Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* pow_lt_pow_iff_of_lt_one

Modified src/algebra/group_with_zero_power.lean
- \+ *lemma* inv_fpow'

Modified src/analysis/calculus/darboux.lean


Modified src/analysis/calculus/extend_deriv.lean




## [2020-11-11 18:01:44](https://github.com/leanprover-community/mathlib/commit/5f098cf)
chore(topology): 2 trivial lemmas ([#4968](https://github.com/leanprover-community/mathlib/pull/4968))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* mem_ball_iff_norm
- \+ *lemma* mem_ball_iff_norm'
- \+ *lemma* mem_closed_ball_iff_norm
- \+ *lemma* mem_closed_ball_iff_norm'

Modified src/topology/bases.lean
- \+ *lemma* is_topological_basis.nhds_has_basis

Modified src/topology/metric_space/basic.lean
- \+ *lemma* eventually_nhds_iff_ball
- \+ *theorem* mem_closed_ball'
- \+ *theorem* eventually_nhds_iff



## [2020-11-11 15:13:36](https://github.com/leanprover-community/mathlib/commit/d4aabf9)
doc(type_classes): Explain the use of {} instance arguments ([#4976](https://github.com/leanprover-community/mathlib/pull/4976))
Closes gh-4660
#### Estimated changes
Modified src/algebra/ring/basic.lean


Modified src/data/finsupp/basic.lean


Modified src/deprecated/group.lean


Modified src/tactic/lint/type_classes.lean




## [2020-11-11 13:39:21](https://github.com/leanprover-community/mathlib/commit/60234d1)
chore(algebra/archimedean): add `exists_pow_lt_of_lt_1` ([#4970](https://github.com/leanprover-community/mathlib/pull/4970))
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+/\- *lemma* exists_int_pow_near
- \+/\- *lemma* exists_int_pow_near'
- \+ *lemma* exists_pow_lt_of_lt_one
- \+ *lemma* exists_nat_pow_near_of_lt_one

Modified src/analysis/specific_limits.lean
- \+ *lemma* uniformity_basis_dist_pow_of_lt_1



## [2020-11-11 13:39:18](https://github.com/leanprover-community/mathlib/commit/4bf7ae4)
refactor(analysis/normed_space): use `lt` in rescale_to_shell, DRY ([#4969](https://github.com/leanprover-community/mathlib/pull/4969))
* Use strict inequality for the upper bound in `rescale_to_shell`.
* Deduplicate some proofs about operator norm.
* Add `linear_map.bound_of_shell`, `continuous_linear_map.op_norm_le_of_shell`, and `continuous_linear_map.op_norm_le_of_shell'`.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* linear_map.bound_of_shell
- \+ *lemma* op_norm_le_of_shell
- \+ *lemma* op_norm_le_of_shell'
- \+ *theorem* le_of_op_norm_le



## [2020-11-11 13:39:16](https://github.com/leanprover-community/mathlib/commit/e1560a3)
feat(measure_theory/borel_space): continuity set of a function is measurable ([#4967](https://github.com/leanprover-community/mathlib/pull/4967))
* Move the definition of `is_Gδ` and basic lemmas to a separate file.
* Prove that `{x | continuous_at f x}` is a Gδ set provided that the
  codomain is a uniform space with countable basis of the uniformity
  filter (e.g., an `emetric_space`). In particular, this set is
  measurable.
* Rename `nhds_le_uniformity` to `supr_nhds_le_uniformity`.
* Add new `nhds_le_uniformity` without `⨆` in the statement.
* Add `uniform.continuous_at_iff_prod`.
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_Gδ.is_measurable
- \+ *lemma* is_measurable_set_of_continuous_at

Created src/topology/G_delta.lean
- \+ *lemma* is_open.is_Gδ
- \+ *lemma* is_Gδ_univ
- \+ *lemma* is_Gδ_bInter_of_open
- \+ *lemma* is_Gδ_Inter_of_open
- \+ *lemma* is_Gδ_sInter
- \+ *lemma* is_Gδ_Inter
- \+ *lemma* is_Gδ_bInter
- \+ *lemma* is_Gδ.inter
- \+ *lemma* is_Gδ.union
- \+ *lemma* is_Gδ_set_of_continuous_at_of_countably_generated_uniformity
- \+ *lemma* is_Gδ_set_of_continuous_at
- \+ *def* is_Gδ
- \+ *def* residual

Modified src/topology/metric_space/baire.lean
- \- *lemma* is_open.is_Gδ
- \- *lemma* is_Gδ_univ
- \- *lemma* is_Gδ_bInter_of_open
- \- *lemma* is_Gδ_Inter_of_open
- \- *lemma* is_Gδ_sInter
- \- *lemma* is_Gδ_Inter
- \- *lemma* is_Gδ_bInter
- \- *lemma* is_Gδ.inter
- \- *lemma* is_Gδ.union
- \- *def* is_Gδ
- \- *def* residual

Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* nhds_le_uniformity
- \+ *lemma* supr_nhds_le_uniformity
- \+ *theorem* continuous_at_iff_prod

Modified src/topology/uniform_space/compact_separated.lean




## [2020-11-11 10:50:27](https://github.com/leanprover-community/mathlib/commit/02cdc33)
chore(algebra/group/hom): Add missing simp lemmas ([#4958](https://github.com/leanprover-community/mathlib/pull/4958))
These are named in the same pattern as `linear_map.to_add_monoid_hom_coe`
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* monoid_hom.to_one_hom_coe
- \+ *lemma* monoid_hom.to_mul_hom_coe



## [2020-11-11 10:50:25](https://github.com/leanprover-community/mathlib/commit/3d6291e)
chore(algebra/group/with_one): Use bundled morphisms ([#4957](https://github.com/leanprover-community/mathlib/pull/4957))
The comment "We have no bundled semigroup homomorphisms" has become false, these exist as `mul_hom`.
This also adds `with_one.coe_mul_hom` and `with_zero.coe_add_hom`
#### Estimated changes
Modified src/algebra/group/hom.lean


Modified src/algebra/group/with_one.lean
- \+/\- *lemma* lift_coe
- \+/\- *lemma* lift_one
- \+/\- *theorem* lift_unique
- \+ *def* coe_mul_hom
- \+/\- *def* lift
- \+/\- *def* map



## [2020-11-11 08:22:46](https://github.com/leanprover-community/mathlib/commit/f30200e)
refactor(algebra/free_algebra): Make `lift` an equiv ([#4908](https://github.com/leanprover-community/mathlib/pull/4908))
This can probably lead to some API cleanup down the line
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean


Modified src/algebra/free_algebra.lean
- \+ *lemma* lift_aux_eq
- \+ *lemma* lift_symm_apply
- \+/\- *def* lift

Modified src/algebra/lie/universal_enveloping.lean
- \+ *lemma* lift_symm_apply
- \+/\- *lemma* ι_comp_lift
- \+/\- *def* lift

Modified src/algebra/ring_quot.lean
- \+/\- *def* lift
- \+/\- *def* lift_alg_hom

Modified src/linear_algebra/clifford_algebra.lean
- \+/\- *theorem* comp_ι_square_scalar
- \+/\- *def* lift

Modified src/linear_algebra/exterior_algebra.lean
- \+/\- *theorem* comp_ι_square_zero
- \+/\- *theorem* hom_ext
- \+/\- *def* lift

Modified src/linear_algebra/tensor_algebra.lean
- \+/\- *def* lift



## [2020-11-11 01:33:41](https://github.com/leanprover-community/mathlib/commit/c20ecef)
chore(scripts): update nolints.txt ([#4965](https://github.com/leanprover-community/mathlib/pull/4965))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-10 23:30:00](https://github.com/leanprover-community/mathlib/commit/5c9e3ef)
feat(ring_theory/adjoin_root): Dimension of adjoin_root ([#4830](https://github.com/leanprover-community/mathlib/pull/4830))
Adds `adjoin_root.degree_lt_linear_equiv`, the restriction of `adjoin_root.mk f`
to the polynomials of degree less than `f`, viewed as a isomorphism between
vector spaces over `K` and uses it to prove that `adjoin_root f` has dimension
`f.nat_degree`. Also renames `adjoin_root.alg_hom` to `adjoin_root.lift_hom`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* map_pow

Modified src/field_theory/adjoin.lean
- \+ *lemma* aeval_gen_minimal_polynomial
- \+ *lemma* adjoin_root_equiv_adjoin_apply_root

Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/adjoin_root.lean
- \+ *lemma* coe_lift_hom
- \+ *lemma* aeval_alg_hom_eq_zero
- \+ *lemma* lift_hom_eq_alg_hom
- \- *lemma* coe_alg_hom
- \+ *def* lift_hom
- \+ *def* equiv
- \- *def* alg_hom

Modified src/ring_theory/power_basis.lean
- \+/\- *lemma* finite_dimensional
- \+ *lemma* findim
- \+/\- *lemma* power_basis_is_basis
- \+ *lemma* adjoin.finite_dimensional
- \+ *lemma* adjoin.findim
- \- *lemma* adjoin_simple.exists_eq_aeval_gen



## [2020-11-10 20:04:41](https://github.com/leanprover-community/mathlib/commit/19bcf65)
chore(data/set/basic): Simp `(⊤ : set α)` to `set.univ` ([#4963](https://github.com/leanprover-community/mathlib/pull/4963))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* top_eq_univ



## [2020-11-10 11:25:41](https://github.com/leanprover-community/mathlib/commit/d3fff8a)
feat(data/fin): define `fin.insert_nth` ([#4947](https://github.com/leanprover-community/mathlib/pull/4947))
Also rename `fin.succ_above_descend` to `fin.succ_above_pred_above`.
#### Estimated changes
Modified src/data/fin.lean
- \+/\- *lemma* succ_above_lt_iff
- \+ *lemma* succ_above_pred_above
- \+ *lemma* forall_iff_succ_above
- \+ *lemma* tuple0_le
- \+ *lemma* le_cons
- \+ *lemma* cons_le
- \+ *lemma* insert_nth_apply_same
- \+ *lemma* insert_nth_apply_succ_above
- \+ *lemma* insert_nth_comp_succ_above
- \+ *lemma* insert_nth_eq_iff
- \+ *lemma* eq_insert_nth_iff
- \+ *lemma* insert_nth_zero
- \+ *lemma* insert_nth_zero'
- \+ *lemma* insert_nth_last
- \+ *lemma* insert_nth_last'
- \- *lemma* succ_above_descend
- \+ *theorem* pred_above_zero
- \+ *def* insert_nth

Modified src/data/fintype/basic.lean




## [2020-11-10 11:25:39](https://github.com/leanprover-community/mathlib/commit/ecbcd38)
feat(category_theory/closed): cartesian closed category with zero object is trivial ([#4924](https://github.com/leanprover-community/mathlib/pull/4924))
#### Estimated changes
Created src/category_theory/closed/zero.lean
- \+ *def* unique_homset_of_initial_iso_terminal
- \+ *def* unique_homset_of_zero
- \+ *def* equiv_punit



## [2020-11-10 10:21:55](https://github.com/leanprover-community/mathlib/commit/55a28c1)
feat(ring_theory/witt_vector/mul_p): multiplication by p as operation on witt vectors ([#4837](https://github.com/leanprover-community/mathlib/pull/4837))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Created src/ring_theory/witt_vector/mul_p.lean
- \+ *lemma* mul_n_coeff
- \+ *lemma* mul_n_is_poly
- \+ *lemma* bind₁_witt_mul_n_witt_polynomial
- \+ *def* witt_mul_n



## [2020-11-10 08:10:37](https://github.com/leanprover-community/mathlib/commit/34b7361)
feat(algebra/*): Add ring instances to clifford_algebra and exterior_algebra ([#4916](https://github.com/leanprover-community/mathlib/pull/4916))
To do this, this removes the `irreducible` attributes.
These attributes were present to try and "insulate" the quotient / generator based definitions, and force downstream proofs to use the universal property.
Unfortunately, this irreducibility created massive headaches in typeclass resolution, and the tradeoff for neatness vs usability just isn't worth it.
If someone wants to add back the `irreducible` attributes in future, they now have test-cases that force them not to break the `ring` instances when doing so.
#### Estimated changes
Modified src/algebra/free_algebra.lean


Modified src/algebra/lie/universal_enveloping.lean


Modified src/algebra/ring_quot.lean


Modified src/linear_algebra/clifford_algebra.lean


Modified src/linear_algebra/exterior_algebra.lean


Modified src/linear_algebra/tensor_algebra.lean


Created test/free_algebra.lean




## [2020-11-10 01:07:17](https://github.com/leanprover-community/mathlib/commit/1ada09b)
chore(scripts): update nolints.txt ([#4961](https://github.com/leanprover-community/mathlib/pull/4961))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-09 22:52:35](https://github.com/leanprover-community/mathlib/commit/e8758ae)
feat(measure_theory/*): a few lemmas about `(is_)measurable` in `Π i, π i` ([#4948](https://github.com/leanprover-community/mathlib/pull/4948))
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+ *lemma* pi_le_borel_pi

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* is_measurable_pi

Modified src/measure_theory/measure_space.lean
- \- *lemma* measure_diff_of_ae_le



## [2020-11-09 13:01:10](https://github.com/leanprover-community/mathlib/commit/09afb04)
feat(ring_theory/polynomial/content): Gauss's Lemma (irreducibility criterion) ([#4861](https://github.com/leanprover-community/mathlib/pull/4861))
Proves that a primitive polynomial is irreducible iff it is irreducible over the fraction field
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+ *lemma* monic.irreducible_of_irreducible_map
- \- *lemma* irreducible_of_irreducible_map

Modified src/field_theory/algebraic_closure.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial/content.lean
- \+ *lemma* is_primitive.is_primitive_of_dvd

Created src/ring_theory/polynomial/gauss_lemma.lean
- \+ *lemma* is_primitive.is_unit_iff_is_unit_map_of_injective
- \+ *lemma* is_primitive.irreducible_of_irreducible_map_of_injective
- \+ *lemma* is_primitive.is_unit_iff_is_unit_map
- \+ *lemma* is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part
- \+ *theorem* is_primitive.irreducible_iff_irreducible_map_fraction_map
- \+ *theorem* is_primitive.int.irreducible_iff_irreducible_map_cast



## [2020-11-09 10:48:50](https://github.com/leanprover-community/mathlib/commit/fdbfe75)
chore(group_theory/group_action): Rename some group_action lemmas ([#4946](https://github.com/leanprover-community/mathlib/pull/4946))
This renames
* These lemmas about `group α`, for consistency with `smul_neg` etc, which are in the global scope:
  * `mul_action.inv_smul_smul` → `inv_smul_smul`
  * `mul_action.smul_inv_smul` → `smul_inv_smul`
  * `mul_action.inv_smul_eq_iff` → `inv_smul_eq_iff`
  * `mul_action.eq_inv_smul_iff` → `eq_inv_smul_iff`
* These lemmas about `group_with_zero α`, for consistency with `smul_inv_smul'` etc, which have trailing `'`s (and were added in [#2693](https://github.com/leanprover-community/mathlib/pull/2693), while the `'`-less ones were added later):
  * `inv_smul_eq_iff` → `inv_smul_eq_iff'`
  * `eq_inv_smul_iff` → `eq_inv_smul_iff'`
#### Estimated changes
Modified src/algebra/pointwise.lean


Modified src/algebra/polynomial/group_ring_action.lean


Modified src/group_theory/group_action.lean
- \+ *lemma* inv_smul_eq_iff'
- \+ *lemma* eq_inv_smul_iff'
- \- *lemma* inv_smul_eq_iff
- \- *lemma* eq_inv_smul_iff



## [2020-11-09 05:45:56](https://github.com/leanprover-community/mathlib/commit/22b61b2)
feat(topology/subset_properties): separated of discrete ([#4952](https://github.com/leanprover-community/mathlib/pull/4952))
As [requested on Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/totally.20disconnected.20of.20discrete/near/216021581).
#### Estimated changes
Modified src/topology/subset_properties.lean




## [2020-11-09 03:25:54](https://github.com/leanprover-community/mathlib/commit/e1c333d)
chore(data/finset/basic): remove inter_eq_sdiff_sdiff ([#4953](https://github.com/leanprover-community/mathlib/pull/4953))
This is a duplicate of sdiff_sdiff_self_left
#### Estimated changes
Modified archive/imo/imo1998_q2.lean


Modified src/data/finset/basic.lean
- \- *lemma* inter_eq_sdiff_sdiff



## [2020-11-09 00:48:26](https://github.com/leanprover-community/mathlib/commit/40f673e)
feat(data/set/intervals/pi): lemmas about intervals in `Π i, π i` ([#4951](https://github.com/leanprover-community/mathlib/pull/4951))
Also add missing lemmas `Ixx_mem_nhds` and lemmas `pi_Ixx_mem_nhds`.
For each `pi_Ixx_mem_nhds` I add a non-dependent version
`pi_Ixx_mem_nhds'` because sometimes Lean fails to unify different
instances while trying to apply the dependent version to `ι → ℝ`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* pi_mono

Created src/data/set/intervals/pi.lean
- \+ *lemma* pi_univ_Ici
- \+ *lemma* pi_univ_Iic
- \+ *lemma* pi_univ_Icc
- \+ *lemma* pi_univ_Ioi_subset
- \+ *lemma* pi_univ_Iio_subset
- \+ *lemma* pi_univ_Ioo_subset
- \+ *lemma* pi_univ_Ioc_subset
- \+ *lemma* pi_univ_Ico_subset
- \+ *lemma* Icc_diff_pi_univ_Ioc_subset

Modified src/order/basic.lean
- \+ *lemma* pi.le_def

Modified src/topology/algebra/ordered.lean
- \+ *lemma* Iic_mem_nhds
- \+ *lemma* Ici_mem_nhds
- \+ *lemma* Ioc_mem_nhds
- \+ *lemma* Ico_mem_nhds
- \+ *lemma* Icc_mem_nhds
- \+ *lemma* pi_Iic_mem_nhds
- \+ *lemma* pi_Iic_mem_nhds'
- \+ *lemma* pi_Ici_mem_nhds
- \+ *lemma* pi_Ici_mem_nhds'
- \+ *lemma* pi_Icc_mem_nhds
- \+ *lemma* pi_Icc_mem_nhds'
- \+ *lemma* pi_Iio_mem_nhds
- \+ *lemma* pi_Iio_mem_nhds'
- \+ *lemma* pi_Ioi_mem_nhds
- \+ *lemma* pi_Ioi_mem_nhds'
- \+ *lemma* pi_Ioc_mem_nhds
- \+ *lemma* pi_Ioc_mem_nhds'
- \+ *lemma* pi_Ico_mem_nhds
- \+ *lemma* pi_Ico_mem_nhds'
- \+ *lemma* pi_Ioo_mem_nhds
- \+ *lemma* pi_Ioo_mem_nhds'

Modified src/topology/constructions.lean
- \+ *lemma* set_pi_mem_nhds

Modified src/topology/instances/real.lean
- \+ *lemma* compact_pi_Icc



## [2020-11-08 18:51:05](https://github.com/leanprover-community/mathlib/commit/dcb8576)
chore(data/finset/basic): trivial simp lemmas ([#4950](https://github.com/leanprover-community/mathlib/pull/4950))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+/\- *theorem* singleton_nonempty
- \+ *theorem* insert_nonempty



## [2020-11-08 18:51:03](https://github.com/leanprover-community/mathlib/commit/de2f1b2)
feat(data/set/intervals/basic): collection of lemmas of the form I??_of_I?? ([#4918](https://github.com/leanprover-community/mathlib/pull/4918))
Some propositions about intervals that I thought may be useful (despite their simplicity).
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* mem_Icc_of_Ioo
- \+ *lemma* mem_Ico_of_Ioo
- \+ *lemma* mem_Ioc_of_Ioo
- \+ *lemma* mem_Icc_of_Ico
- \+ *lemma* mem_Icc_of_Ioc
- \+ *lemma* mem_Ici_of_Ioi
- \+ *lemma* mem_Iic_of_Iio



## [2020-11-08 16:26:23](https://github.com/leanprover-community/mathlib/commit/14a7c39)
chore(data/finset/basic): use `has_coe_t` for coercion of `finset` to `set` ([#4917](https://github.com/leanprover-community/mathlib/pull/4917))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+/\- *lemma* mem_coe
- \+/\- *lemma* set_of_mem
- \+/\- *lemma* coe_mem
- \+/\- *lemma* mk_coe
- \+/\- *lemma* coe_ssubset
- \+/\- *lemma* coe_nonempty
- \+/\- *lemma* coe_empty
- \+/\- *lemma* coe_singleton
- \+/\- *lemma* coe_union
- \+/\- *lemma* coe_inter
- \+/\- *lemma* coe_erase
- \+/\- *lemma* coe_sdiff
- \+/\- *lemma* piecewise_coe
- \+/\- *theorem* coe_inj

Modified src/data/polynomial/monic.lean




## [2020-11-08 01:11:01](https://github.com/leanprover-community/mathlib/commit/26e4f15)
chore(scripts): update nolints.txt ([#4944](https://github.com/leanprover-community/mathlib/pull/4944))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-07 21:27:41](https://github.com/leanprover-community/mathlib/commit/e7d40ef)
refactor(*): Move an instance to a more appropriate file ([#4939](https://github.com/leanprover-community/mathlib/pull/4939))
In its former location, this instance related neither to the section it was the sole resident of, nor even to the file.
#### Estimated changes
Modified src/algebra/group_ring_action.lean


Modified src/group_theory/coset.lean




## [2020-11-07 20:15:40](https://github.com/leanprover-community/mathlib/commit/5fed35b)
chore(docs/100): fix typo ([#4937](https://github.com/leanprover-community/mathlib/pull/4937))
#### Estimated changes
Modified docs/100.yaml




## [2020-11-07 20:15:38](https://github.com/leanprover-community/mathlib/commit/c2ab384)
feat(category_theory/limits/preserves): convenience defs for things already there ([#4933](https://github.com/leanprover-community/mathlib/pull/4933))
#### Estimated changes
Modified src/category_theory/limits/preserves/basic.lean
- \+ *def* is_limit_of_reflects
- \+ *def* is_colimit_of_reflects
- \+ *def* preserves_limits_of_shape_of_reflects_of_preserves
- \+ *def* preserves_limits_of_reflects_of_preserves
- \+ *def* preserves_colimits_of_shape_of_reflects_of_preserves
- \+ *def* preserves_colimits_of_reflects_of_preserves



## [2020-11-07 19:06:12](https://github.com/leanprover-community/mathlib/commit/9a0ba08)
feat(category_theory/limits/preserves): transfer preserving limits through nat iso ([#4932](https://github.com/leanprover-community/mathlib/pull/4932))
- Move two defs higher in the file
- Shorten some proofs using newer lemmas
- Show that we can transfer preservation of limits through natural isomorphism in the functor.
#### Estimated changes
Modified src/category_theory/limits/preserves/basic.lean
- \+/\- *def* is_limit_of_preserves
- \+/\- *def* is_colimit_of_preserves
- \+ *def* preserves_limit_of_iso_diagram
- \+ *def* preserves_limit_of_nat_iso
- \+ *def* preserves_limits_of_shape_of_nat_iso
- \+ *def* preserves_limits_of_nat_iso
- \+ *def* preserves_colimit_of_iso_diagram
- \+ *def* preserves_colimit_of_nat_iso
- \+ *def* preserves_colimits_of_shape_of_nat_iso
- \+ *def* preserves_colimits_of_nat_iso
- \- *def* preserves_limit_of_iso
- \- *def* preserves_colimit_of_iso

Modified src/category_theory/limits/shapes/constructions/preserve_binary_products.lean




## [2020-11-07 19:06:10](https://github.com/leanprover-community/mathlib/commit/c494db5)
feat(category_theory/limits/shapes/equalizers): equalizer comparison map ([#4927](https://github.com/leanprover-community/mathlib/pull/4927))
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* equalizer_comparison_comp_π
- \+ *lemma* map_lift_equalizer_comparison
- \+ *lemma* ι_comp_coequalizer_comparison
- \+ *lemma* coequalizer_comparison_map_desc
- \+ *def* equalizer_comparison
- \+ *def* coequalizer_comparison



## [2020-11-07 18:00:08](https://github.com/leanprover-community/mathlib/commit/11368e1)
feat(category_theory/limits/preserves): transfer reflecting limits through nat iso ([#4934](https://github.com/leanprover-community/mathlib/pull/4934))
#### Estimated changes
Modified src/category_theory/limits/preserves/basic.lean
- \+ *def* reflects_limit_of_nat_iso
- \+ *def* reflects_limits_of_shape_of_nat_iso
- \+ *def* reflects_limits_of_nat_iso
- \+ *def* reflects_colimit_of_nat_iso
- \+ *def* reflects_colimits_of_shape_of_nat_iso
- \+ *def* reflects_colimits_of_nat_iso



## [2020-11-07 08:45:59](https://github.com/leanprover-community/mathlib/commit/655b617)
feat(category_theory/limits/preserves/shapes/products): preserve products ([#4857](https://github.com/leanprover-community/mathlib/pull/4857))
A smaller part of [#4716](https://github.com/leanprover-community/mathlib/pull/4716), for just products.
This also renames the file `preserves/shapes.lean` to `preserves/shapes/products.lean`, since I want a similar API for other special shapes and it'd get too big otherwise. 
Of the declarations which were already present: `preserves_products_iso`, `preserves_products_iso_hom_π`, `map_lift_comp_preserves_products_iso_hom`, the first is still there but with weaker assumptions, and the other two are now provable by simp (under weaker assumptions again).
#### Estimated changes
Deleted src/category_theory/limits/preserves/shapes.lean
- \- *lemma* preserves_products_iso_hom_π
- \- *lemma* map_lift_comp_preserves_products_iso_hom
- \- *def* preserves_products_iso

Created src/category_theory/limits/preserves/shapes/products.lean
- \+ *lemma* preserves_products_iso_hom
- \+ *def* fan_map_cone_limit
- \+ *def* map_is_limit_of_preserves_of_is_limit
- \+ *def* is_limit_of_reflects_of_map_is_limit
- \+ *def* is_limit_of_has_product_of_preserves_limit
- \+ *def* preserves_product_of_iso_comparison
- \+ *def* preserves_products_iso

Modified src/category_theory/limits/shapes/products.lean
- \+ *def* product_is_product

Modified src/topology/sheaves/forget.lean




## [2020-11-07 01:11:14](https://github.com/leanprover-community/mathlib/commit/c4e8d74)
chore(scripts): update nolints.txt ([#4926](https://github.com/leanprover-community/mathlib/pull/4926))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-06 20:34:51](https://github.com/leanprover-community/mathlib/commit/8ba0dde)
chore(data/polynomial/monic): speedup next_coeff_mul ([#4920](https://github.com/leanprover-community/mathlib/pull/4920))
#### Estimated changes
Modified src/data/polynomial/monic.lean




## [2020-11-06 20:34:49](https://github.com/leanprover-community/mathlib/commit/e0cf0d3)
fix(meta/expr): adjust is_likely_generated_binder_name to lean[#490](https://github.com/leanprover-community/mathlib/pull/490) ([#4915](https://github.com/leanprover-community/mathlib/pull/4915))
Lean PR 490 changed Lean's strategy for generating binder names. This PR adapts
`name.is_likely_generated_binder_name`, which checks whether a binder name was
likely generated by Lean (rather than given by the user).
#### Estimated changes
Modified src/meta/expr.lean


Created test/likely_generated_name.lean




## [2020-11-06 19:17:20](https://github.com/leanprover-community/mathlib/commit/b6b41c1)
feat(category_theory/limits/creates): composition creates limits ([#4922](https://github.com/leanprover-community/mathlib/pull/4922))
#### Estimated changes
Modified src/category_theory/limits/creates.lean




## [2020-11-06 19:17:18](https://github.com/leanprover-community/mathlib/commit/4f673bd)
feat(category_theory/limits/preserves): instances for composition preserving limits ([#4921](https://github.com/leanprover-community/mathlib/pull/4921))
A couple of quick instances. I'm pretty sure these instances don't cause clashes since they're for subsingleton classes, and they shouldn't cause loops since they're just other versions of instances already there.
#### Estimated changes
Modified src/category_theory/limits/preserves/basic.lean




## [2020-11-06 16:08:51](https://github.com/leanprover-community/mathlib/commit/bddc5c9)
feat(category_theory/limits): equivalence creates colimits ([#4923](https://github.com/leanprover-community/mathlib/pull/4923))
Dualises and tidy proofs already there
#### Estimated changes
Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/limits/limits.lean
- \+ *def* map_cocone_equiv



## [2020-11-06 14:57:51](https://github.com/leanprover-community/mathlib/commit/91f8e68)
feat(src/ring_theory/polynomial/cyclotomic): cyclotomic polynomials ([#4914](https://github.com/leanprover-community/mathlib/pull/4914))
I have added some basic results about cyclotomic polynomials. I defined them as the polynomial, with integer coefficients, that lifts the complex polynomial ∏ μ in primitive_roots n ℂ, (X - C μ). I proved that the degree of cyclotomic n is totient n and the product formula for X ^ n - 1. I plan to prove the irreducibility in the near future.
This was in [4869](https://github.com/leanprover-community/mathlib/pull/4869) before I splitted that PR. Compared to it, I added the definition of `cyclotomic n R` for any ring `R` (still using the polynomial with coefficients in `ℤ`) and some easy lemmas, especially `cyclotomic_of_ring_hom`, `cyclotomic'_eq_X_pow_sub_one_div` `cyclotomic_eq_X_pow_sub_one_div`, and `cycl_eq_cycl'`.
#### Estimated changes
Modified docs/undergrad.yaml


Created src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* cyclotomic'_zero
- \+ *lemma* cyclotomic'_one
- \+ *lemma* cyclotomic'_two
- \+ *lemma* cyclotomic'.monic
- \+ *lemma* cyclotomic'_ne_zero
- \+ *lemma* nat_degree_cyclotomic'
- \+ *lemma* degree_cyclotomic'
- \+ *lemma* roots_of_cyclotomic
- \+ *lemma* X_pow_sub_one_eq_prod
- \+ *lemma* cyclotomic'_splits
- \+ *lemma* X_pow_sub_one_splits
- \+ *lemma* prod_cyclotomic'_eq_X_pow_sub_one
- \+ *lemma* cyclotomic'_eq_X_pow_sub_one_div
- \+ *lemma* int_coeff_of_cyclotomic
- \+ *lemma* unique_int_coeff_of_cycl
- \+ *lemma* int_cyclotomic_rw
- \+ *lemma* map_cyclotomic_int
- \+ *lemma* int_cyclotomic_spec
- \+ *lemma* int_cyclotomic_unique
- \+ *lemma* map_cyclotomic
- \+ *lemma* cyclotomic_zero
- \+ *lemma* cyclotomic_one
- \+ *lemma* cyclotomic_two
- \+ *lemma* cyclotomic.monic
- \+ *lemma* cyclotomic_ne_zero
- \+ *lemma* degree_cyclotomic
- \+ *lemma* nat_degree_cyclotomic
- \+ *lemma* prod_cyclotomic_eq_X_pow_sub_one
- \+ *lemma* cyclotomic_eq_X_pow_sub_one_div
- \+ *lemma* cyclotomic_eq_prod_X_sub_primitive_roots
- \+ *def* cyclotomic'
- \+ *def* cyclotomic

Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* primitive_roots_one
- \- *lemma* primitive_root_one



## [2020-11-06 10:17:40](https://github.com/leanprover-community/mathlib/commit/747aaae)
chore(algebra/lie/basic): Add some missing simp lemmas about A →ₗ⁅R⁆ B ([#4912](https://github.com/leanprover-community/mathlib/pull/4912))
These are mostly inspired by lemmas in linear_map. All the proofs are either `rfl` or copied from a proof for `linear_map`.
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *lemma* coe_mk
- \+ *lemma* morphism.coe_injective
- \+ *lemma* morphism.ext_iff
- \+/\- *lemma* morphism.comp_apply
- \+ *lemma* morphism.comp_coe
- \+ *lemma* of_associative_algebra_hom_apply



## [2020-11-06 01:10:55](https://github.com/leanprover-community/mathlib/commit/fd3212c)
chore(scripts): update nolints.txt ([#4919](https://github.com/leanprover-community/mathlib/pull/4919))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-05 18:57:18](https://github.com/leanprover-community/mathlib/commit/a12d677)
feat(ring_theory): define a `power_basis` structure ([#4905](https://github.com/leanprover-community/mathlib/pull/4905))
This PR defines a structure `power_basis`. If `S` is an `R`-algebra, `pb : power_basis R S` states that `S` (as `R`-module) has basis `1`, `pb.gen`, ..., `pb.gen ^ (pb.dim - 1)`. Since there are multiple possible choices, I decided to not make it a typeclass.
Three constructors for `power_basis` are included: `algebra.adjoin`, `intermediate_field.adjoin` and `adjoin_root`. Each of these is of the form `power_basis K _` with `K` a field, at least until `minimal_polynomial` gets better support for rings.
#### Estimated changes
Created src/ring_theory/power_basis.lean
- \+ *lemma* finite_dimensional
- \+ *lemma* polynomial.mem_supported_range
- \+ *lemma* mem_span_pow'
- \+ *lemma* mem_span_pow
- \+ *lemma* is_integral_algebra_map_iff
- \+ *lemma* minimal_polynomial.eq_of_algebra_map_eq
- \+ *lemma* mem_span_power_basis
- \+ *lemma* linear_independent_power_basis
- \+ *lemma* power_basis_is_basis
- \+ *lemma* adjoin_simple.exists_eq_aeval_gen



## [2020-11-05 17:06:55](https://github.com/leanprover-community/mathlib/commit/246df99)
feat(category_theory/limits): Any small complete category is a preorder ([#4907](https://github.com/leanprover-community/mathlib/pull/4907))
Show that any small complete category has subsingleton homsets.
Not sure if this is useful for anything - maybe it shouldn't be an instance
#### Estimated changes
Created src/category_theory/limits/small_complete.lean




## [2020-11-05 17:06:53](https://github.com/leanprover-community/mathlib/commit/4024597)
feat(category_theory/limits/presheaf): left adjoint if preserves colimits ([#4896](https://github.com/leanprover-community/mathlib/pull/4896))
#### Estimated changes
Modified src/category_theory/limits/presheaf.lean
- \+ *def* is_left_adjoint_of_preserves_colimits



## [2020-11-05 17:06:51](https://github.com/leanprover-community/mathlib/commit/6a1ce57)
chore(algebra/module/linear_map): Derive linear_map from mul_action_hom ([#4888](https://github.com/leanprover-community/mathlib/pull/4888))
Note that this required some stuff about polynomials to move to cut import cycles.
#### Estimated changes
Modified src/algebra/group_action_hom.lean
- \- *theorem* coe_polynomial

Modified src/algebra/group_ring_action.lean
- \- *lemma* coeff_smul'
- \- *lemma* smul_C
- \- *lemma* smul_X
- \- *theorem* smul_eval_smul
- \- *theorem* eval_smul'
- \- *theorem* smul_eval
- \- *theorem* prod_X_sub_smul.monic
- \- *theorem* prod_X_sub_smul.eval
- \- *theorem* prod_X_sub_smul.smul
- \- *theorem* prod_X_sub_smul.coeff

Modified src/algebra/module/linear_map.lean


Created src/algebra/polynomial/group_ring_action.lean
- \+ *lemma* coeff_smul'
- \+ *lemma* smul_C
- \+ *lemma* smul_X
- \+ *theorem* smul_eval_smul
- \+ *theorem* eval_smul'
- \+ *theorem* smul_eval
- \+ *theorem* prod_X_sub_smul.monic
- \+ *theorem* prod_X_sub_smul.eval
- \+ *theorem* prod_X_sub_smul.smul
- \+ *theorem* prod_X_sub_smul.coeff
- \+ *theorem* coe_polynomial

Modified src/field_theory/fixed.lean


Modified src/group_theory/sylow.lean




## [2020-11-05 15:43:26](https://github.com/leanprover-community/mathlib/commit/2f07ff2)
chore(topology/metric_space): more `norm_cast` lemmas, golf proofs ([#4911](https://github.com/leanprover-community/mathlib/pull/4911))
#### Estimated changes
Modified src/data/real/nnreal.lean


Modified src/topology/metric_space/basic.lean
- \+ *lemma* ennreal_coe_nndist
- \+ *lemma* edist_lt_coe
- \+ *lemma* edist_le_coe
- \+ *lemma* coe_nndist
- \+ *lemma* dist_lt_coe
- \+ *lemma* dist_le_coe
- \+ *lemma* nndist_pi_def
- \+ *lemma* nndist_le_pi_nndist
- \+ *lemma* dist_le_pi_dist

Modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* edist_pi_def



## [2020-11-05 01:07:58](https://github.com/leanprover-community/mathlib/commit/834d491)
chore(scripts): update nolints.txt ([#4910](https://github.com/leanprover-community/mathlib/pull/4910))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-04 21:59:56](https://github.com/leanprover-community/mathlib/commit/189063b)
chore(data/W): rename `W` to `W_type` ([#4909](https://github.com/leanprover-community/mathlib/pull/4909))
Having a single character identifier in the root namespace is inconvenient.
closes leanprover-community/doc-gen[#83](https://github.com/leanprover-community/mathlib/pull/83)
#### Estimated changes
Modified archive/examples/prop_encodable.lean


Modified docs/overview.yaml


Modified src/data/W.lean
- \+/\- *lemma* depth_pos
- \+/\- *lemma* depth_lt_depth_mk
- \+/\- *def* depth

Modified src/data/pfunctor/univariate/basic.lean
- \+/\- *def* W



## [2020-11-04 18:37:41](https://github.com/leanprover-community/mathlib/commit/5a61ef1)
feat(ring_theory/witt_vector/teichmuller): Teichmuller representatives ([#4690](https://github.com/leanprover-community/mathlib/pull/4690))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Created src/ring_theory/witt_vector/teichmuller.lean
- \+ *lemma* teichmuller_coeff_zero
- \+ *lemma* teichmuller_coeff_pos
- \+ *lemma* teichmuller_zero
- \+ *lemma* map_teichmuller
- \+ *lemma* ghost_component_teichmuller
- \+ *def* teichmuller_fun



## [2020-11-04 16:04:42](https://github.com/leanprover-community/mathlib/commit/211b0c0)
feat(logic/basic): forall2_congr lemmas ([#4904](https://github.com/leanprover-community/mathlib/pull/4904))
Some helpful lemmas for working with quantifiers, just other versions of what's already there.
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* forall₂_congr
- \+ *lemma* forall₃_congr
- \+ *lemma* forall₄_congr
- \+ *lemma* exists₂_congr
- \+ *lemma* exists₃_congr
- \+ *lemma* exists₄_congr



## [2020-11-04 16:04:40](https://github.com/leanprover-community/mathlib/commit/0081a5a)
feat(ring_theory/algebraic): if `L / K` is algebraic, then the subalgebras are fields ([#4903](https://github.com/leanprover-community/mathlib/pull/4903))
#### Estimated changes
Modified src/field_theory/intermediate_field.lean
- \+ *lemma* to_subalgebra_to_intermediate_field
- \+ *lemma* to_intermediate_field_to_subalgebra
- \+ *lemma* mem_subalgebra_equiv_intermediate_field
- \+ *lemma* mem_subalgebra_equiv_intermediate_field_symm
- \+ *def* subalgebra_equiv_intermediate_field

Modified src/ring_theory/algebra_tower.lean
- \+ *lemma* aeval_coe

Modified src/ring_theory/algebraic.lean
- \+ *lemma* inv_eq_of_aeval_div_X_ne_zero
- \+ *lemma* inv_eq_of_root_of_coeff_zero_ne_zero
- \+ *lemma* subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero
- \+ *lemma* subalgebra.inv_mem_of_algebraic
- \+ *lemma* subalgebra.is_field_of_algebraic



## [2020-11-04 14:06:15](https://github.com/leanprover-community/mathlib/commit/e303a7d)
feat(linear_algebra/tensor_product): tensoring linear maps with modules ([#4771](https://github.com/leanprover-community/mathlib/pull/4771))
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean
- \+ *lemma* ltensor_tmul
- \+ *lemma* rtensor_tmul
- \+ *lemma* coe_ltensor_hom
- \+ *lemma* coe_rtensor_hom
- \+ *lemma* ltensor_add
- \+ *lemma* rtensor_add
- \+ *lemma* ltensor_zero
- \+ *lemma* rtensor_zero
- \+ *lemma* ltensor_smul
- \+ *lemma* rtensor_smul
- \+ *lemma* ltensor_comp
- \+ *lemma* rtensor_comp
- \+ *lemma* ltensor_id
- \+ *lemma* rtensor_id
- \+ *lemma* ltensor_comp_rtensor
- \+ *lemma* rtensor_comp_ltensor
- \+ *lemma* map_comp_rtensor
- \+ *lemma* map_comp_ltensor
- \+ *lemma* rtensor_comp_map
- \+ *lemma* ltensor_comp_map
- \+ *lemma* ltensor_sub
- \+ *lemma* rtensor_sub
- \+ *lemma* ltensor_neg
- \+ *lemma* rtensor_neg
- \+ *def* ltensor
- \+ *def* rtensor
- \+ *def* ltensor_hom
- \+ *def* rtensor_hom



## [2020-11-04 08:09:46](https://github.com/leanprover-community/mathlib/commit/6f72c22)
chore(data/finset): add a few lemmas ([#4901](https://github.com/leanprover-community/mathlib/pull/4901))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* insert_sdiff_insert
- \+ *lemma* sdiff_insert_of_not_mem
- \+ *lemma* piecewise_piecewise_of_subset_left
- \+ *lemma* piecewise_idem_left
- \+ *lemma* piecewise_piecewise_of_subset_right
- \+ *lemma* piecewise_idem_right
- \+ *lemma* piecewise_mem_Icc_of_mem_of_mem
- \+ *lemma* piecewise_mem_Icc
- \+ *lemma* piecewise_mem_Icc'



## [2020-11-04 08:09:42](https://github.com/leanprover-community/mathlib/commit/0877077)
chore(analysis/calculus/times_cont_diff): a few missing lemmas ([#4900](https://github.com/leanprover-community/mathlib/pull/4900))
* add `times_cont_diff_within_at_iff_forall_nat_le` and `times_cont_diff_on_iff_forall_nat_le`;
* add `times_cont_diff_on_all_iff_nat` and `times_cont_diff_all_iff_nat`;
* rename `times_cont_diff_at.differentiable` to `times_cont_diff_at.differentiable_at`;
* add `times_cont_diff.div_const`;
* add `times_cont_diff_succ_iff_deriv`
* move some `of_le` lemmas up to support minor golfing of proofs.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+/\- *lemma* times_cont_diff_within_at.of_le
- \+ *lemma* times_cont_diff_within_at_iff_forall_nat_le
- \+/\- *lemma* times_cont_diff_on.of_le
- \+ *lemma* times_cont_diff_on_iff_forall_nat_le
- \+ *lemma* times_cont_diff_on_all_iff_nat
- \+ *lemma* times_cont_diff_at.differentiable_at
- \+ *lemma* times_cont_diff_all_iff_nat
- \+/\- *lemma* times_cont_diff_on.mul
- \+ *lemma* times_cont_diff_within_at.div_const
- \+ *lemma* times_cont_diff_at.div_const
- \+ *lemma* times_cont_diff_on.div_const
- \+ *lemma* times_cont_diff.div_const
- \- *lemma* times_cont_diff_at.differentiable
- \+ *theorem* times_cont_diff_succ_iff_deriv



## [2020-11-04 08:09:40](https://github.com/leanprover-community/mathlib/commit/beb6831)
feat(analysis/calculus/times_cont_diff): add `restrict_scalars` ([#4899](https://github.com/leanprover-community/mathlib/pull/4899))
Add `restrict_scalars` lemmas to `has_ftaylor_series_up_to_on`,
`times_cont_diff_within_at`, `times_cont_diff_on`,
`times_cont_diff_at`, and `times_cont_diff`.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* has_ftaylor_series_up_to_on.restrict_scalars
- \+ *lemma* times_cont_diff_within_at.restrict_scalars
- \+ *lemma* times_cont_diff_on.restrict_scalars
- \+ *lemma* times_cont_diff_at.restrict_scalars
- \+ *lemma* times_cont_diff.restrict_scalars
- \+ *def* formal_multilinear_series.restrict_scalars



## [2020-11-04 08:09:38](https://github.com/leanprover-community/mathlib/commit/b7991c0)
feat(category_theory/limits/cones): map_cone and postcompose lemmas ([#4894](https://github.com/leanprover-community/mathlib/pull/4894))
#### Estimated changes
Modified src/category_theory/limits/cones.lean
- \+ *def* functoriality_comp_postcompose
- \+ *def* postcompose_whisker_left_map_cone
- \+ *def* functoriality_comp_precompose
- \+ *def* precompose_whisker_left_map_cocone



## [2020-11-04 08:09:36](https://github.com/leanprover-community/mathlib/commit/7d6f37d)
feat(category_theory/closed/cartesian): product preserves colimits ([#4893](https://github.com/leanprover-community/mathlib/pull/4893))
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean




## [2020-11-04 08:09:35](https://github.com/leanprover-community/mathlib/commit/e1d60fd)
feat(data/equiv): exists unique congr ([#4890](https://github.com/leanprover-community/mathlib/pull/4890))
#### Estimated changes
Modified src/data/equiv/basic.lean




## [2020-11-04 08:09:31](https://github.com/leanprover-community/mathlib/commit/d88042c)
feat(order/filter/at_top_bot): lemmas about `map/comap` of `at_top`/`at_bot` ([#4878](https://github.com/leanprover-community/mathlib/pull/4878))
* Redefine `at_top`/`at_bot` using `Ici`/`Iic`.
* Add lemmas about `map`/`comap` of `at_top`/`at_bot` under `coe : s → α`, where `s` is one of `Ici a`, `Iic a`, `Ioi a`, `Iio a`.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* map_coe_at_top_of_Ici_subset
- \+ *lemma* map_coe_Ici_at_top
- \+ *lemma* map_coe_Ioi_at_top
- \+ *lemma* at_top_Ioi_eq
- \+ *lemma* at_top_Ici_eq
- \+ *lemma* map_coe_Iio_at_bot
- \+ *lemma* at_bot_Iio_eq
- \+ *lemma* map_coe_Iic_at_bot
- \+ *lemma* at_bot_Iic_eq
- \+/\- *def* at_top
- \+/\- *def* at_bot

Modified src/order/filter/basic.lean
- \+ *lemma* set.eq_on.eventually_eq_of_mem



## [2020-11-04 05:43:18](https://github.com/leanprover-community/mathlib/commit/7ab3ca8)
feat(data/quaternion): define quaternions and prove some basic properties ([#2339](https://github.com/leanprover-community/mathlib/pull/2339))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* op_smul
- \+ *lemma* algebra_map_apply

Modified src/algebra/big_operators/basic.lean
- \+ *lemma* op_sum
- \+ *lemma* unop_sum

Modified src/algebra/big_operators/order.lean
- \- *lemma* op_sum
- \- *lemma* unop_sum

Modified src/algebra/module/linear_map.lean
- \+ *lemma* coe_of_involutive
- \+ *def* of_involutive

Modified src/algebra/opposites.lean
- \+ *lemma* coe_op_add_equiv
- \+ *lemma* coe_op_add_equiv_symm
- \+ *lemma* op_add_equiv_to_equiv
- \+ *lemma* ring_hom.coe_to_opposite
- \- *lemma* coe_op_add_hom
- \- *lemma* coe_unop_add_hom
- \+ *def* op_add_equiv
- \+ *def* ring_hom.to_opposite
- \- *def* op_add_hom
- \- *def* unop_add_hom

Modified src/analysis/normed_space/inner_product.lean


Created src/analysis/quaternion.lean
- \+ *lemma* inner_self
- \+ *lemma* inner_def
- \+ *lemma* norm_sq_eq_norm_square
- \+ *lemma* norm_mul
- \+ *lemma* norm_coe
- \+ *lemma* coe_complex_re
- \+ *lemma* coe_complex_im_i
- \+ *lemma* coe_complex_im_j
- \+ *lemma* coe_complex_im_k
- \+ *lemma* coe_complex_add
- \+ *lemma* coe_complex_mul
- \+ *lemma* coe_complex_zero
- \+ *lemma* coe_complex_one
- \+ *lemma* coe_complex_smul
- \+ *lemma* coe_complex_coe
- \+ *lemma* coe_of_complex
- \+ *def* of_complex

Created src/data/quaternion.lean
- \+ *lemma* mk.eta
- \+ *lemma* coe_re
- \+ *lemma* coe_im_i
- \+ *lemma* coe_im_j
- \+ *lemma* coe_im_k
- \+ *lemma* coe_injective
- \+ *lemma* coe_inj
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* mk_add_mk
- \+ *lemma* neg_mk
- \+ *lemma* mk_mul_mk
- \+ *lemma* mk_sub_mk
- \+ *lemma* smul_re
- \+ *lemma* smul_im_i
- \+ *lemma* smul_im_j
- \+ *lemma* smul_im_k
- \+ *lemma* coe_add
- \+ *lemma* coe_sub
- \+ *lemma* coe_neg
- \+ *lemma* coe_mul
- \+ *lemma* coe_commutes
- \+ *lemma* coe_commute
- \+ *lemma* coe_mul_eq_smul
- \+ *lemma* mul_coe_eq_smul
- \+ *lemma* coe_algebra_map
- \+ *lemma* smul_coe
- \+ *lemma* re_conj
- \+ *lemma* im_i_conj
- \+ *lemma* im_j_conj
- \+ *lemma* im_k_conj
- \+ *lemma* conj_conj
- \+ *lemma* conj_add
- \+ *lemma* conj_mul
- \+ *lemma* conj_conj_mul
- \+ *lemma* conj_mul_conj
- \+ *lemma* self_add_conj'
- \+ *lemma* self_add_conj
- \+ *lemma* conj_add_self'
- \+ *lemma* conj_add_self
- \+ *lemma* conj_eq_two_re_sub
- \+ *lemma* commute_conj_self
- \+ *lemma* commute_self_conj
- \+ *lemma* commute_conj_conj
- \+ *lemma* conj_coe
- \+ *lemma* conj_smul
- \+ *lemma* conj_one
- \+ *lemma* eq_re_of_eq_coe
- \+ *lemma* eq_re_iff_mem_range_coe
- \+ *lemma* conj_fixed
- \+ *lemma* conj_mul_eq_coe
- \+ *lemma* mul_conj_eq_coe
- \+ *lemma* conj_zero
- \+ *lemma* conj_neg
- \+ *lemma* conj_sub
- \+ *lemma* coe_conj_alg_equiv
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* zero_re
- \+ *lemma* zero_im_i
- \+ *lemma* zero_im_j
- \+ *lemma* zero_im_k
- \+ *lemma* one_re
- \+ *lemma* one_im_i
- \+ *lemma* one_im_j
- \+ *lemma* one_im_k
- \+ *lemma* add_re
- \+ *lemma* add_im_i
- \+ *lemma* add_im_j
- \+ *lemma* add_im_k
- \+ *lemma* neg_re
- \+ *lemma* neg_im_i
- \+ *lemma* neg_im_j
- \+ *lemma* neg_im_k
- \+ *lemma* sub_re
- \+ *lemma* sub_im_i
- \+ *lemma* sub_im_j
- \+ *lemma* sub_im_k
- \+ *lemma* mul_re
- \+ *lemma* mul_im_i
- \+ *lemma* mul_im_j
- \+ *lemma* mul_im_k
- \+ *lemma* algebra_map_def
- \+ *lemma* conj_re
- \+ *lemma* conj_im_i
- \+ *lemma* conj_im_j
- \+ *lemma* conj_im_k
- \+ *lemma* norm_sq_def
- \+ *lemma* norm_sq_def'
- \+ *lemma* norm_sq_coe
- \+ *lemma* norm_sq_zero
- \+ *lemma* norm_sq_neg
- \+ *lemma* self_mul_conj
- \+ *lemma* conj_mul_self
- \+ *lemma* coe_norm_sq_add
- \+ *lemma* norm_sq_eq_zero
- \+ *lemma* norm_sq_ne_zero
- \+ *lemma* norm_sq_nonneg
- \+ *lemma* norm_sq_le_zero
- \+ *lemma* norm_sq_inv
- \+ *lemma* norm_sq_div
- \+ *def* conj
- \+ *def* conj_alg_equiv
- \+ *def* quaternion
- \+ *def* norm_sq

Modified src/number_theory/arithmetic_function.lean




## [2020-11-04 01:36:53](https://github.com/leanprover-community/mathlib/commit/16e3871)
chore(scripts): update nolints.txt ([#4898](https://github.com/leanprover-community/mathlib/pull/4898))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt


Modified scripts/nolints.txt




## [2020-11-04 00:20:10](https://github.com/leanprover-community/mathlib/commit/23a2767)
feat(category_theory/yoneda): type level yoneda equivalence ([#4889](https://github.com/leanprover-community/mathlib/pull/4889))
Broken off from [#4608](https://github.com/leanprover-community/mathlib/pull/4608).
#### Estimated changes
Modified src/category_theory/yoneda.lean
- \+ *lemma* yoneda_equiv_naturality
- \+ *lemma* yoneda_equiv_apply
- \+ *lemma* yoneda_equiv_symm_app_apply
- \+ *def* yoneda_equiv



## [2020-11-03 21:30:18](https://github.com/leanprover-community/mathlib/commit/505097f)
feat(order): countable categoricity of dense linear orders ([#2860](https://github.com/leanprover-community/mathlib/pull/2860))
We construct an order isomorphism between any two countable, nonempty, dense linear orders without endpoints, using the back-and-forth method.
#### Estimated changes
Modified src/algebra/order.lean
- \+ *lemma* cmp_eq_lt_iff
- \+ *lemma* cmp_eq_eq_iff
- \+ *lemma* cmp_eq_gt_iff
- \+ *lemma* cmp_self_eq_eq
- \+ *lemma* cmp_eq_cmp_symm
- \+ *lemma* lt_iff_lt_of_cmp_eq_cmp
- \+ *lemma* le_iff_le_of_cmp_eq_cmp

Created src/order/countable_dense_linear_order.lean
- \+ *lemma* exists_between_finsets
- \+ *lemma* exists_across
- \+ *def* partial_iso
- \+ *def* defined_at_left
- \+ *def* defined_at_right
- \+ *def* fun_of_ideal
- \+ *def* inv_of_ideal
- \+ *def* embedding_from_countable_to_dense
- \+ *def* iso_of_countable_dense

Modified src/order/rel_iso.lean
- \+ *def* of_strict_mono
- \+ *def* of_cmp_eq_cmp



## [2020-11-03 20:37:43](https://github.com/leanprover-community/mathlib/commit/712a0b7)
chore(algebra/lie): adjoint rep of lie algebra uses lowercase `ad` ([#4891](https://github.com/leanprover-community/mathlib/pull/4891))
The uppercase is for Lie groups
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *def* ad
- \- *def* Ad



## [2020-11-03 17:56:57](https://github.com/leanprover-community/mathlib/commit/e88a5bb)
feat(*): assorted prereqs for cyclotomic polynomials ([#4887](https://github.com/leanprover-community/mathlib/pull/4887))
This is hopefully my last preparatory PR for cyclotomic polynomials. It was in [4869](https://github.com/leanprover-community/mathlib/pull/4869) .
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* mem_nth_roots_finset
- \+/\- *def* nth_roots_finset

Modified src/number_theory/divisors.lean
- \+/\- *lemma* filter_dvd_eq_divisors

Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* primitive_roots_zero
- \+ *lemma* primitive_root_one
- \+/\- *lemma* card_nth_roots
- \+/\- *lemma* nth_roots_nodup
- \+/\- *lemma* card_nth_roots_finset
- \+ *lemma* nth_roots_one_eq_bind_primitive_roots'
- \+/\- *lemma* nth_roots_one_eq_bind_primitive_roots



## [2020-11-03 17:56:54](https://github.com/leanprover-community/mathlib/commit/b37d4a3)
feat(category_theory/limits/types): ext iff lemma ([#4883](https://github.com/leanprover-community/mathlib/pull/4883))
A little lemma which sometimes makes it easier to work with limits in type.
#### Estimated changes
Modified src/category_theory/limits/types.lean
- \+ *lemma* limit_ext_iff



## [2020-11-03 17:56:52](https://github.com/leanprover-community/mathlib/commit/6bed7d4)
fix(tactic/interactive): issue where long term tooltips break layout ([#4882](https://github.com/leanprover-community/mathlib/pull/4882))
For issue description see https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/widget.20v.20long.20term.20names
Basically the problem is that if the little 'argument pills' in the tooltip are too long, then there is a fight between the expression linebreaking algorithm and the pill linebreaking algorithm and something gets messed up.
A first attempt to fix this is to use flexbox for laying out the pills.
Still some issues with expressions linebreaking weirdly to sort out before this should be pulled.
Need to find a mwe that I can put in a file without a huge dependency tree.
#### Estimated changes
Modified src/tactic/interactive_expr.lean




## [2020-11-03 17:56:50](https://github.com/leanprover-community/mathlib/commit/4f8c490)
feat(tactic/mk_iff_of_inductive_prop): mk_iff attribute ([#4863](https://github.com/leanprover-community/mathlib/pull/4863))
This attribute should make `mk_iff_of_inductive_prop` easier to use.
#### Estimated changes
Modified archive/imo/imo1981_q3.lean


Modified src/data/multiset/basic.lean


Modified src/field_theory/perfect_closure.lean


Modified src/logic/relation.lean


Modified src/tactic/core.lean


Modified src/tactic/mk_iff_of_inductive_prop.lean
- \+ *def* list_option_merge

Modified test/mk_iff_of_inductive.lean




## [2020-11-03 15:50:10](https://github.com/leanprover-community/mathlib/commit/918e28c)
feat(category_theory/limits/types): explicit description of equalizers in Type ([#4880](https://github.com/leanprover-community/mathlib/pull/4880))
Cf https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/concrete.20limits.20in.20Type.
Adds equivalent conditions for a fork in Type to be a equalizer, and a proof that the subtype is an equalizer.
(cc: @adamtopaz @kbuzzard)
#### Estimated changes
Modified src/category_theory/limits/shapes/types.lean
- \+ *lemma* unique_of_type_equalizer
- \+ *def* equalizer_limit



## [2020-11-03 15:50:08](https://github.com/leanprover-community/mathlib/commit/34c3668)
chore(data/set/intervals/ord_connected): make it more useful as a typeclass ([#4879](https://github.com/leanprover-community/mathlib/pull/4879))
* Add `protected lemma set.Icc_subset` that looks for
  `ord_connected s` instance.
* Add `instance` versions to more lemmas.
* Add `ord_connected_pi`.
#### Estimated changes
Modified src/data/set/intervals/ord_connected.lean
- \+ *lemma* ord_connected_pi
- \+/\- *lemma* ord_connected_Ici
- \+/\- *lemma* ord_connected_Iic
- \+/\- *lemma* ord_connected_Ioi
- \+/\- *lemma* ord_connected_Iio
- \+/\- *lemma* ord_connected_Icc
- \+/\- *lemma* ord_connected_Ico
- \+/\- *lemma* ord_connected_Ioc
- \+/\- *lemma* ord_connected_Ioo
- \+/\- *lemma* ord_connected_singleton
- \+/\- *lemma* ord_connected_empty
- \+/\- *lemma* ord_connected_univ
- \+/\- *lemma* ord_connected_interval



## [2020-11-03 15:50:06](https://github.com/leanprover-community/mathlib/commit/9851a88)
feat(*/multilinear): define `(continuous_)multilinear_map.restrict_scalars` ([#4872](https://github.com/leanprover-community/mathlib/pull/4872))
I'm going to use these definitions to prove
`times_cont_diff_at.restrict_scalars` etc.
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean
- \+/\- *lemma* op_norm_smul_le
- \+ *lemma* norm_restrict_scalars
- \+ *lemma* continuous_restrict_scalars
- \+ *def* restrict_scalars_linear

Modified src/linear_algebra/multilinear.lean
- \+ *lemma* coe_restrict_scalars
- \+/\- *lemma* smul_apply
- \+ *def* restrict_scalars

Modified src/topology/algebra/multilinear.lean
- \+ *lemma* coe_restrict_scalars
- \+/\- *lemma* smul_apply
- \+/\- *lemma* comp_continuous_multilinear_map_coe
- \+ *def* restrict_scalars



## [2020-11-03 15:50:04](https://github.com/leanprover-community/mathlib/commit/63d109f)
chore(category_theory/limits): Use `lim_map` over `lim.map` ([#4856](https://github.com/leanprover-community/mathlib/pull/4856))
Modify the simp-normal form for `lim.map` to be `lim_map` instead, and express lemmas in terms of `lim_map` instead, as well as use it in special shapes so that the assumptions can be weakened.
#### Estimated changes
Modified src/category_theory/limits/colimit_limit.lean


Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* limit.lift_map
- \+/\- *lemma* limit.pre_π
- \+/\- *lemma* limit.post_π
- \+ *lemma* lim_map_eq_lim_map
- \- *lemma* limit.map_π

Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/types.lean


Modified src/category_theory/monoidal/limits.lean


Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/sheaf_condition/equalizer_products.lean




## [2020-11-03 15:50:02](https://github.com/leanprover-community/mathlib/commit/b26fc59)
feat(category_theory/limits/shapes/products): pi comparison morphism ([#4855](https://github.com/leanprover-community/mathlib/pull/4855))
#### Estimated changes
Modified src/category_theory/limits/shapes/products.lean
- \+ *lemma* pi_comparison_comp_π
- \+ *lemma* map_lift_pi_comparison
- \+ *lemma* ι_comp_sigma_comparison
- \+ *lemma* sigma_comparison_map_desc
- \+ *def* pi_comparison
- \+ *def* sigma_comparison



## [2020-11-03 14:17:25](https://github.com/leanprover-community/mathlib/commit/5275628)
feat(algebra/operations): add three lemmas ([#4864](https://github.com/leanprover-community/mathlib/pull/4864))
Add lemmas `one_le_inv`, `self_le_self_inv` and `self_inv_le_one`
#### Estimated changes
Modified src/algebra/algebra/operations.lean
- \+ *lemma* one_le_one_div
- \+ *lemma* le_self_mul_one_div
- \+ *lemma* mul_one_div_le_one



## [2020-11-03 09:26:45](https://github.com/leanprover-community/mathlib/commit/c2b6220)
feat(linear_algebra/matrix): `det (reindex e e A) = det A` ([#4875](https://github.com/leanprover-community/mathlib/pull/4875))
This PR includes four flavours of this lemma: `det_reindex_self'` is the `simp` lemma that doesn't include the actual term `reindex` as a subexpression (because that would be already `simp`ed away by `reindex_apply`). `det_reindex_self`, `det_reindex_linear_equiv_self` and `det_reindex_alg_equiv` include their respective function in the lemma statement.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* perm_congr_apply

Modified src/group_theory/perm/sign.lean
- \+ *lemma* sign_perm_congr

Modified src/linear_algebra/matrix.lean
- \+ *lemma* det_reindex_self'
- \+ *lemma* det_reindex_self
- \+ *lemma* det_reindex_linear_equiv_self
- \+ *lemma* det_reindex_alg_equiv



## [2020-11-03 01:06:41](https://github.com/leanprover-community/mathlib/commit/57ee216)
chore(scripts): update nolints.txt ([#4884](https://github.com/leanprover-community/mathlib/pull/4884))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-02 22:24:06](https://github.com/leanprover-community/mathlib/commit/0e4f8f4)
chore(scripts): typo in yaml_check ([#4881](https://github.com/leanprover-community/mathlib/pull/4881))
#### Estimated changes
Modified scripts/yaml_check.lean




## [2020-11-02 22:24:05](https://github.com/leanprover-community/mathlib/commit/dae87bc)
chore(data/finsupp/basic): Remove finsupp.leval which duplicates finsupp.lapply ([#4876](https://github.com/leanprover-community/mathlib/pull/4876))
#### Estimated changes
Modified src/algebra/big_operators/finsupp.lean


Modified src/data/finsupp/basic.lean
- \- *lemma* eval_add_hom_apply
- \- *lemma* coe_leval'
- \- *lemma* coe_leval
- \+ *def* apply_add_hom
- \- *def* eval_add_hom
- \- *def* leval'
- \- *def* leval

Modified src/data/polynomial/coeff.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/finsupp.lean




## [2020-11-02 20:27:42](https://github.com/leanprover-community/mathlib/commit/5334f48)
chore(data/fintype/card): add a few lemmas ([#4877](https://github.com/leanprover-community/mathlib/pull/4877))
Prove a few versions of `(∏ i in s, f i) * (∏ i in sᶜ, f i) = ∏ i, f i`
#### Estimated changes
Modified src/data/fintype/card.lean
- \+ *lemma* is_compl.prod_mul_prod
- \+ *lemma* finset.prod_mul_prod_compl
- \+ *lemma* finset.prod_compl_mul_prod



## [2020-11-02 18:45:02](https://github.com/leanprover-community/mathlib/commit/13a104d)
chore({data,linear_algebra}/dfinsupp): Move linear_algebra stuff to its own file ([#4873](https://github.com/leanprover-community/mathlib/pull/4873))
This makes the layout of files about `dfinsupp` resemble those of `finsupp` a little better.
This also:
* Renames type arguments to match the names of those in finsupp
* Adjusts argument explicitness to match those in finsupp
* Adds `dfinsupp.lapply` to match `finsupp.lapply`
#### Estimated changes
Modified src/data/dfinsupp.lean
- \- *lemma* lhom_ext
- \- *lemma* lhom_ext'
- \- *lemma* lmk_apply
- \- *lemma* lsingle_apply
- \- *def* lmk
- \- *def* lsingle
- \- *def* lsum

Created src/linear_algebra/dfinsupp.lean
- \+ *lemma* lhom_ext
- \+ *lemma* lhom_ext'
- \+ *lemma* lmk_apply
- \+ *lemma* lsingle_apply
- \+ *lemma* lapply_apply
- \+ *def* lmk
- \+ *def* lsingle
- \+ *def* lapply
- \+ *def* lsum

Modified src/linear_algebra/direct_sum_module.lean


Modified src/linear_algebra/finsupp.lean




## [2020-11-02 17:17:23](https://github.com/leanprover-community/mathlib/commit/6587e84)
feat(algebra/algebra/subalgebra): subalgebras, when seen as submodules, are idempotent ([#4854](https://github.com/leanprover-community/mathlib/pull/4854))
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *theorem* mul_self



## [2020-11-02 14:44:02](https://github.com/leanprover-community/mathlib/commit/0aa6aed)
chore(order/basic): move `strict_mono_coe`to `subtype` NS ([#4870](https://github.com/leanprover-community/mathlib/pull/4870))
Also add `subtype.mono_coe`
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* subtype.mono_coe
- \+ *lemma* subtype.strict_mono_coe
- \- *lemma* strict_mono_coe

Modified src/order/conditionally_complete_lattice.lean




## [2020-11-02 04:55:03](https://github.com/leanprover-community/mathlib/commit/309df10)
refactor(data/list/basic,...): more explicit args ([#4866](https://github.com/leanprover-community/mathlib/pull/4866))
This makes the `p` in most lemmas involving the following functions explicit, following the usual explicitness conventions:
- `list.filter`,
- `list.countp`,
- `list.take_while`,
- `multiset.filter`,
- `multiset.countp`,
- `finset.filter`
#### Estimated changes
Modified src/algebra/big_operators/basic.lean


Modified src/algebra/monoid_algebra.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/caratheodory.lean


Modified src/combinatorics/partition.lean


Modified src/data/finset/basic.lean
- \+/\- *lemma* filter_empty
- \+/\- *theorem* filter_subset
- \+/\- *theorem* mem_filter
- \+/\- *theorem* filter_filter
- \+/\- *theorem* filter_union
- \+/\- *theorem* filter_union_right
- \+/\- *theorem* filter_inter
- \+/\- *theorem* inter_filter
- \+/\- *def* filter

Modified src/data/finsupp/basic.lean


Modified src/data/fintype/basic.lean


Modified src/data/list/basic.lean
- \+/\- *theorem* filter_filter
- \+/\- *theorem* span_eq_take_drop
- \+/\- *theorem* take_while_append_drop
- \+/\- *theorem* countp_nil

Modified src/data/list/perm.lean


Modified src/data/multiset/basic.lean
- \+/\- *theorem* coe_filter
- \+/\- *theorem* filter_zero
- \+/\- *theorem* filter_add
- \+/\- *theorem* filter_le_filter
- \+/\- *theorem* filter_cons_of_pos
- \+/\- *theorem* filter_cons_of_neg
- \+/\- *theorem* filter_filter
- \+/\- *theorem* filter_add_filter
- \+/\- *theorem* filter_map_eq_filter
- \+/\- *theorem* filter_map_filter
- \+/\- *theorem* countp_zero
- \+/\- *theorem* countp_filter
- \+/\- *theorem* countp_pos
- \+/\- *theorem* countp_pos_of_mem
- \+/\- *theorem* coe_count
- \+/\- *def* filter
- \+/\- *def* countp

Modified src/data/nat/totient.lean


Modified src/linear_algebra/determinant.lean


Modified src/measure_theory/prod.lean


Modified src/topology/algebra/infinite_sum.lean




## [2020-11-02 04:55:01](https://github.com/leanprover-community/mathlib/commit/556079b)
feat(ring_theory/polynomial/content): monic polynomials are primitive ([#4862](https://github.com/leanprover-community/mathlib/pull/4862))
Adds the lemma `monic.is_primitive`.
#### Estimated changes
Modified src/ring_theory/polynomial/content.lean
- \+ *lemma* monic.is_primitive



## [2020-11-02 02:10:46](https://github.com/leanprover-community/mathlib/commit/ecdc319)
fix(tactic/simpa): reflect more simp errors ([#4865](https://github.com/leanprover-community/mathlib/pull/4865))
fixes [#2061](https://github.com/leanprover-community/mathlib/pull/2061)
#### Estimated changes
Modified src/algebra/continued_fractions/convergents_equiv.lean


Modified src/analysis/normed_space/inner_product.lean


Modified src/category_theory/abelian/pseudoelements.lean


Modified src/data/matrix/char_p.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/tactic/omega/nat/neg_elim.lean


Modified src/tactic/simpa.lean




## [2020-11-02 01:12:55](https://github.com/leanprover-community/mathlib/commit/7c8868d)
chore(scripts): update nolints.txt ([#4868](https://github.com/leanprover-community/mathlib/pull/4868))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-11-01 17:55:51](https://github.com/leanprover-community/mathlib/commit/4aa087a)
doc(*): work around markdown2 bug for now ([#4842](https://github.com/leanprover-community/mathlib/pull/4842))
#### Estimated changes
Modified src/category_theory/natural_isomorphism.lean


Modified src/control/monad/writer.lean


Modified src/tactic/localized.lean


Modified src/tactic/simps.lean




## [2020-11-01 01:07:16](https://github.com/leanprover-community/mathlib/commit/7a624b8)
chore(scripts): update nolints.txt ([#4860](https://github.com/leanprover-community/mathlib/pull/4860))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt


