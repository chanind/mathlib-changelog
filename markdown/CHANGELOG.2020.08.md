## [2020-08-31 22:41:43](https://github.com/leanprover-community/mathlib/commit/036527a)
feat(linear_algebra/finite_dimensional): eq_of_le_of_findim_eq ([#4005](https://github.com/leanprover-community/mathlib/pull/4005))
Add a variant of `eq_top_of_findim_eq`, where instead of proving a
submodule equal to `⊤`, it's shown equal to another finite-dimensional
submodule with the same dimension that contains it.  The two lemmas
are related by the `comap_subtype` lemmas, so the proof is short, but
it still seems useful to have this form.
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* eq_of_le_of_findim_eq



## [2020-08-31 22:11:18](https://github.com/leanprover-community/mathlib/commit/be3b175)
feat(analysis/normed_space/real_inner_product): inner_add_sub_eq_zero_iff ([#4004](https://github.com/leanprover-community/mathlib/pull/4004))
Add a lemma that the sum and difference of two vectors are orthogonal
if and only if they have the same norm.  (This can be interpreted
geometrically as saying e.g. that a median of a triangle from a vertex
is orthogonal to the opposite edge if and only if the triangle is
isosceles at that vertex.)
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean
- \+ *lemma* inner_add_sub_eq_zero_iff



## [2020-08-31 19:25:35](https://github.com/leanprover-community/mathlib/commit/d0a8cc4)
feat(analysis/special_functions/trigonometric): ranges of `real.sin` and `real.cos` ([#3998](https://github.com/leanprover-community/mathlib/pull/3998))
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* exists_cos_eq
- \+ *lemma* range_cos
- \+ *lemma* range_sin



## [2020-08-31 17:07:43](https://github.com/leanprover-community/mathlib/commit/d4484a4)
fix(widget): workaround for webview rendering bug ([#3997](https://github.com/leanprover-community/mathlib/pull/3997))
See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/extension.20performance
The bug seems to go away if we collapse the extra nested spans made by `block` in to one span.
Still should do some tests to make sure this doesn't break anything else.
Minimal breaking example is:
```
import tactic.interactive_expr
example :
0+1+2+3+4+5+6+7+8+9 +
0+1+2+3+4+5+6+7+8+9 =
0+1+2+3+4+5+6+7+8+9 :=
by skip
```
#### Estimated changes
Modified src/tactic/interactive_expr.lean




## [2020-08-31 15:32:01](https://github.com/leanprover-community/mathlib/commit/d2b18a1)
feat(algebra/field, ring_theory/ideal/basic): an ideal is maximal iff the quotient is a field ([#3986](https://github.com/leanprover-community/mathlib/pull/3986))
One half of the theorem was already proven (the implication maximal
ideal implies that the quotient is a field), but the other half was not,
mainly because it was missing a necessary predicate.
I added the predicate is_field that can be used to tell Lean that the
usual ring structure on the quotient extends to a field. The predicate
along with proofs to move between is_field and field were provided by
Kevin Buzzard. I also added a lemma that the inverse is unique in
is_field.
At the end I also added the iff statement of the theorem.
#### Estimated changes
Modified src/algebra/field.lean
- \+ *lemma* field.to_is_field
- \+ *lemma* uniq_inv_of_is_field

Modified src/ring_theory/ideal/basic.lean
- \+ *theorem* maximal_of_is_field
- \+ *theorem* maximal_ideal_iff_is_field_quotient



## [2020-08-31 14:45:05](https://github.com/leanprover-community/mathlib/commit/8089f50)
chore(category_theory/limits): some simp lemmas ([#3993](https://github.com/leanprover-community/mathlib/pull/3993))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* binary_fan.π_app_left
- \+ *lemma* binary_fan.π_app_right
- \+ *lemma* binary_cofan.ι_app_left
- \+ *lemma* binary_cofan.ι_app_right



## [2020-08-31 13:17:44](https://github.com/leanprover-community/mathlib/commit/9e9e318)
feat(data/fin): simplify fin.mk ([#3996](https://github.com/leanprover-community/mathlib/pull/3996))
After the recent changes to make `fin n` a subtype, expressions
involving `fin.mk` were not getting simplified as they used to be,
since the `simp` lemmas are for the anonymous constructor, which is
`subtype.mk` not `fin.mk`.  Add a `simp` lemma converting `fin.mk` to
the anonymous constructor.
In particular, unsimplified expressions involving `fin.mk` were coming
out of `fin_cases` (I think this comes from `fin_range` in
`data/list/range.lean` using `fin.mk`).  I don't know if that should
be avoiding creating the `fin.mk` expressions in the first place, but
simplifying them seems a good idea in any case.
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* mk_eq_subtype_mk



## [2020-08-31 08:47:27](https://github.com/leanprover-community/mathlib/commit/10ebb71)
feat(measure_theory): induction principles in measure theory ([#3978](https://github.com/leanprover-community/mathlib/pull/3978))
This commit adds three induction principles for measure theory
* To prove something for arbitrary simple functions
* To prove something for arbitrary measurable functions into `ennreal`
* To prove something for arbitrary measurable + integrable functions.
This also adds some basic lemmas to various files. Not all of them are used in this PR, some will be used by near-future PRs.
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+ *lemma* const_one
- \+ *lemma* comp_one
- \+ *lemma* one_comp

Modified src/data/indicator_function.lean
- \+ *lemma* piecewise_eq_indicator
- \+ *lemma* indicator_zero'
- \+ *lemma* comp_indicator
- \+/\- *lemma* indicator_comp_of_zero
- \+ *lemma* indicator_add_eq_left
- \+ *lemma* indicator_add_eq_right

Modified src/data/list/indexes.lean


Modified src/data/real/ennreal.lean
- \+ *lemma* not_lt_top
- \+/\- *lemma* mul_eq_top
- \+/\- *lemma* mul_ne_top
- \+/\- *lemma* mul_lt_top
- \+ *lemma* ne_top_of_mul_ne_top_left
- \+ *lemma* ne_top_of_mul_ne_top_right
- \+ *lemma* lt_top_of_mul_lt_top_left
- \+ *lemma* lt_top_of_mul_lt_top_right
- \+/\- *lemma* mul_pos
- \+/\- *lemma* div_zero_iff
- \+/\- *lemma* div_pos_iff
- \+/\- *lemma* to_real_eq_to_real
- \+/\- *lemma* to_real_mul_to_real

Modified src/data/set/basic.lean
- \+ *lemma* eq.subset
- \+ *lemma* diff_diff_comm
- \+ *lemma* image_diff_preimage
- \+ *lemma* image_preimage_eq_iff
- \+ *lemma* range_subset_singleton
- \+/\- *lemma* image_compl_preimage

Modified src/data/set/function.lean
- \+ *lemma* comp_piecewise
- \+ *lemma* piecewise_same
- \+ *lemma* range_piecewise

Modified src/logic/function/basic.lean
- \+/\- *lemma* comp_apply
- \+ *lemma* const_apply
- \+ *lemma* const_comp
- \+ *lemma* comp_const
- \+/\- *lemma* injective.of_comp
- \+/\- *lemma* surjective.of_comp
- \+/\- *theorem* left_inverse.comp
- \+/\- *theorem* right_inverse.comp

Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/integration.lean
- \+ *theorem* measurable.ennreal_induction

Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/set_integral.lean
- \+ *lemma* integrable_add
- \+ *lemma* integrable.induction



## [2020-08-31 08:11:24](https://github.com/leanprover-community/mathlib/commit/bf7487b)
fix(algebraic_geometry/Spec): inline TeX in heading ([#3992](https://github.com/leanprover-community/mathlib/pull/3992))
#### Estimated changes
Modified src/algebraic_geometry/Spec.lean




## [2020-08-31 05:09:37](https://github.com/leanprover-community/mathlib/commit/b79fc03)
feature(algebraic_geometry/Scheme): the category of schemes ([#3961](https://github.com/leanprover-community/mathlib/pull/3961))
The definition of a `Scheme`, and the category of schemes as the full subcategory of locally ringed spaces.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* is_unit_map

Created src/algebraic_geometry/Scheme.lean
- \+ *def* to_LocallyRingedSpace
- \+ *def* empty

Created src/algebraic_geometry/Spec.lean
- \+ *def* Spec.SheafedSpace
- \+ *def* Spec.PresheafedSpace

Created src/algebraic_geometry/locally_ringed_space.lean
- \+ *lemma* hom_ext
- \+ *def* to_Top
- \+ *def* 𝒪
- \+ *def* hom
- \+ *def* stalk
- \+ *def* stalk_map
- \+ *def* id
- \+ *def* comp
- \+ *def* forget_to_SheafedSpace
- \+ *def* restrict

Modified src/algebraic_geometry/presheafed_space.lean
- \+/\- *lemma* as_coe
- \+/\- *lemma* mk_coe
- \+ *lemma* map_presheaf_obj_presheaf
- \- *lemma* map_presheaf_obj_𝒪
- \+ *def* const
- \+ *def* restrict

Modified src/algebraic_geometry/prime_spectrum.lean
- \+ *lemma* punit
- \+ *lemma* basic_open_open
- \+ *def* basic_open

Created src/algebraic_geometry/sheafed_space.lean
- \+ *lemma* as_coe
- \+ *lemma* mk_coe
- \+ *lemma* id_base
- \+ *lemma* id_c
- \+ *lemma* id_c_app
- \+ *lemma* comp_base
- \+ *lemma* comp_c_app
- \+ *def* sheaf
- \+ *def* punit
- \+ *def* forget_to_PresheafedSpace
- \+ *def* forget
- \+ *def* restrict

Modified src/algebraic_geometry/stalks.lean
- \+/\- *def* stalk
- \+ *def* restrict_stalk_iso

Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *lemma* structure_sheaf_stalk_to_fiber_surjective
- \+ *lemma* structure_sheaf_stalk_to_fiber_injective
- \+ *def* stalk_iso_Type
- \+ *def* compare_stalks
- \+ *def* stalk_to_fiber_ring_hom
- \+ *def* stalk_iso

Modified src/category_theory/limits/types.lean
- \+ *lemma* jointly_surjective'

Modified src/data/equiv/transfer_instance.lean


Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* local_of_surjective
- \+ *lemma* is_unit_map_iff

Modified src/ring_theory/localization.lean


Modified src/topology/category/Top/opens.lean
- \+ *lemma* inclusion_open_embedding
- \+ *def* inclusion
- \+ *def* is_open_map.functor

Modified src/topology/opens.lean
- \+ *lemma* le_def
- \+ *lemma* mk_inf_mk
- \+ *lemma* coe_inf
- \+ *lemma* supr_mk

Modified src/topology/sheaves/local_predicate.lean
- \+ *lemma* prelocal_predicate.sheafify_of

Modified src/topology/sheaves/sheaf.lean
- \+ *def* cover.of_open_embedding
- \+ *def* pi_opens.iso_of_open_embedding
- \+ *def* pi_inters.iso_of_open_embedding
- \+ *def* diagram.iso_of_open_embedding
- \+ *def* fork.iso_of_open_embedding

Modified src/topology/sheaves/stalks.lean
- \+ *lemma* germ_exist



## [2020-08-30 23:20:13](https://github.com/leanprover-community/mathlib/commit/e88843c)
feat(data/finset/sort): range_mono_of_fin ([#3987](https://github.com/leanprover-community/mathlib/pull/3987))
Add a `simp` lemma giving the range of `mono_of_fin`.
#### Estimated changes
Modified src/data/finset/sort.lean
- \+ *lemma* range_mono_of_fin



## [2020-08-30 18:40:35](https://github.com/leanprover-community/mathlib/commit/861f182)
feat(widget): add go to definition button. ([#3982](https://github.com/leanprover-community/mathlib/pull/3982))
Now you can hit a new button in the tooltip and it will reveal the definition location in the editor!
#### Estimated changes
Modified src/tactic/interactive_expr.lean




## [2020-08-30 17:12:27](https://github.com/leanprover-community/mathlib/commit/f9ee416)
feat(topology/tactic): optionally make `continuity` verbose with `?` ([#3962](https://github.com/leanprover-community/mathlib/pull/3962))
#### Estimated changes
Modified src/topology/tactic.lean




## [2020-08-30 15:37:08](https://github.com/leanprover-community/mathlib/commit/1073204)
feat(logic/nontrivial): function.injective.exists_ne ([#3983](https://github.com/leanprover-community/mathlib/pull/3983))
Add a lemma that an injective function from a nontrivial type has an
argument at which it does not take a given value.
#### Estimated changes
Modified src/logic/nontrivial.lean




## [2020-08-30 11:24:28](https://github.com/leanprover-community/mathlib/commit/942c779)
feat(meta/widget): Add css classes for indentation as required by group and nest. ([#3764](https://github.com/leanprover-community/mathlib/pull/3764))
this is a transplant of https://github.com/leanprover-community/lean/pull/439
the relevant css section looks more or less like this:
```css
        .indent-code {
            text-indent: calc(var(--indent-level) * -1ch);
            padding-left: calc(var(--indent-level) * 1ch);
        }
```
For details, one can play around here: https://jsfiddle.net/xbzhL60m/45/
#### Estimated changes
Modified src/tactic/interactive_expr.lean




## [2020-08-30 05:38:17](https://github.com/leanprover-community/mathlib/commit/ffce8f6)
feat(data/complex/is_R_or_C): add typeclass for real or complex ([#3934](https://github.com/leanprover-community/mathlib/pull/3934))
#### Estimated changes
Created src/data/complex/is_R_or_C.lean
- \+ *lemma* of_real_alg
- \+ *lemma* re_add_im
- \+ *lemma* of_real_re
- \+ *lemma* of_real_im
- \+ *lemma* mul_re
- \+ *lemma* mul_im
- \+ *lemma* zero_re
- \+ *lemma* zero_im
- \+ *lemma* of_real_zero
- \+ *lemma* of_real_one
- \+ *lemma* one_re
- \+ *lemma* one_im
- \+ *lemma* bit0_re
- \+ *lemma* bit1_re
- \+ *lemma* bit0_im
- \+ *lemma* bit1_im
- \+ *lemma* of_real_add
- \+ *lemma* of_real_bit0
- \+ *lemma* of_real_bit1
- \+ *lemma* two_ne_zero
- \+ *lemma* of_real_neg
- \+ *lemma* of_real_mul
- \+ *lemma* smul_re
- \+ *lemma* smul_im
- \+ *lemma* smul_re'
- \+ *lemma* smul_im'
- \+ *lemma* I_re
- \+ *lemma* I_im
- \+ *lemma* I_mul_I
- \+ *lemma* conj_re
- \+ *lemma* conj_im
- \+ *lemma* conj_of_real
- \+ *lemma* conj_bit0
- \+ *lemma* conj_bit1
- \+ *lemma* conj_neg_I
- \+ *lemma* conj_conj
- \+ *lemma* conj_involutive
- \+ *lemma* conj_bijective
- \+ *lemma* conj_inj
- \+ *lemma* conj_eq_zero
- \+ *lemma* eq_conj_iff_real
- \+ *lemma* eq_conj_iff_re
- \+ *lemma* norm_sq_eq_def
- \+ *lemma* norm_sq_eq_def'
- \+ *lemma* norm_sq_of_real
- \+ *lemma* norm_sq_zero
- \+ *lemma* norm_sq_one
- \+ *lemma* norm_sq_nonneg
- \+ *lemma* norm_sq_eq_zero
- \+ *lemma* norm_sq_pos
- \+ *lemma* norm_sq_neg
- \+ *lemma* norm_sq_conj
- \+ *lemma* norm_sq_mul
- \+ *lemma* norm_sq_add
- \+ *lemma* re_sq_le_norm_sq
- \+ *lemma* im_sq_le_norm_sq
- \+ *lemma* of_real_sub
- \+ *lemma* of_real_pow
- \+ *lemma* norm_sq_sub
- \+ *lemma* inv_def
- \+ *lemma* inv_re
- \+ *lemma* inv_im
- \+ *lemma* of_real_inv
- \+ *lemma* div_re
- \+ *lemma* div_im
- \+ *lemma* of_real_div
- \+ *lemma* of_real_fpow
- \+ *lemma* I_mul_I_of_nonzero
- \+ *lemma* div_I
- \+ *lemma* inv_I
- \+ *lemma* norm_sq_inv
- \+ *lemma* norm_sq_div
- \+ *lemma* nat_cast_re
- \+ *lemma* nat_cast_im
- \+ *lemma* int_cast_re
- \+ *lemma* int_cast_im
- \+ *lemma* rat_cast_re
- \+ *lemma* rat_cast_im
- \+ *lemma* char_zero_R_or_C
- \+ *lemma* abs_of_real
- \+ *lemma* abs_of_nonneg
- \+ *lemma* abs_of_nat
- \+ *lemma* mul_self_abs
- \+ *lemma* abs_zero
- \+ *lemma* abs_one
- \+ *lemma* abs_two
- \+ *lemma* abs_nonneg
- \+ *lemma* abs_eq_zero
- \+ *lemma* abs_ne_zero
- \+ *lemma* abs_conj
- \+ *lemma* abs_mul
- \+ *lemma* abs_re_le_abs
- \+ *lemma* abs_im_le_abs
- \+ *lemma* re_le_abs
- \+ *lemma* im_le_abs
- \+ *lemma* abs_add
- \+ *lemma* abs_abs
- \+ *lemma* abs_pos
- \+ *lemma* abs_neg
- \+ *lemma* abs_sub
- \+ *lemma* abs_sub_le
- \+ *lemma* abs_abs_sub_le_abs_sub
- \+ *lemma* abs_re_div_abs_le_one
- \+ *lemma* abs_im_div_abs_le_one
- \+ *lemma* abs_cast_nat
- \+ *lemma* norm_sq_eq_abs
- \+ *lemma* is_cau_seq_abs
- \+ *lemma* re_to_real
- \+ *lemma* im_to_real
- \+ *lemma* conj_to_real
- \+ *lemma* I_to_real
- \+ *lemma* of_real_to_real
- \+ *lemma* norm_sq_to_real
- \+ *lemma* abs_to_real
- \+ *lemma* re_to_complex
- \+ *lemma* im_to_complex
- \+ *lemma* conj_to_complex
- \+ *lemma* I_to_complex
- \+ *lemma* of_real_to_complex
- \+ *lemma* norm_sq_to_complex
- \+ *lemma* abs_to_complex
- \+ *theorem* ext_iff
- \+ *theorem* ext
- \+ *theorem* of_real_inj
- \+ *theorem* of_real_eq_zero
- \+ *theorem* mul_conj
- \+ *theorem* add_conj
- \+ *theorem* sub_conj
- \+ *theorem* of_real_nat_cast
- \+ *theorem* of_real_int_cast
- \+ *theorem* of_real_rat_cast
- \+ *theorem* re_eq_add_conj
- \+ *theorem* abs_inv
- \+ *theorem* abs_div
- \+ *theorem* is_cau_seq_re
- \+ *theorem* is_cau_seq_im
- \+ *def* norm_sq
- \+ *def* of_real_hom



## [2020-08-30 04:53:26](https://github.com/leanprover-community/mathlib/commit/a18f142)
feat(set_theory/game): computation of grundy_value (nim n + nim m) ([#3977](https://github.com/leanprover-community/mathlib/pull/3977))
#### Estimated changes
Modified src/data/nat/bitwise.lean
- \+ *lemma* lxor_trichotomy

Modified src/set_theory/game/nim.lean
- \+ *lemma* exists_ordinal_move_left_eq
- \+ *lemma* exists_move_left_eq
- \+/\- *lemma* equiv_nim_iff_grundy_value_eq
- \+ *lemma* equiv_iff_grundy_value_eq
- \+ *lemma* grundy_value_zero
- \+ *lemma* equiv_zero_iff_grundy_value
- \+ *lemma* grundy_value_nim_add_nim
- \+ *lemma* nim_add_nim_equiv
- \+ *lemma* grundy_value_add

Modified src/set_theory/pgame.lean
- \+ *theorem* equiv_congr_left
- \+ *theorem* equiv_congr_right



## [2020-08-30 01:59:33](https://github.com/leanprover-community/mathlib/commit/dfdb38a)
feat(data/fin): nontrivial instance ([#3979](https://github.com/leanprover-community/mathlib/pull/3979))
Add an instance `nontrivial (fin (n + 2))`.
#### Estimated changes
Modified src/data/fin.lean




## [2020-08-29 17:36:23](https://github.com/leanprover-community/mathlib/commit/14e7fe8)
feat(linear_algebra/char_poly/coeff,*): prerequisites for friendship theorem ([#3953](https://github.com/leanprover-community/mathlib/pull/3953))
adds several assorted lemmas about matrices and `zmod p`
proves that if `M` is a square matrix with entries in `zmod p`, then `tr M^p = tr M`, needed for friendship theorem
#### Estimated changes
Modified src/algebra/char_p.lean
- \+ *theorem* add_pow_char_pow_of_commute
- \+ *theorem* sub_pow_char_of_commute
- \+ *theorem* sub_pow_char_pow_of_commute
- \+/\- *theorem* add_pow_char
- \+ *theorem* add_pow_char_pow
- \+ *theorem* sub_pow_char
- \+ *theorem* sub_pow_char_pow
- \+ *theorem* iterate_frobenius

Modified src/data/matrix/basic.lean
- \+ *lemma* map_sub
- \+ *lemma* subsingleton_of_empty_left
- \+ *lemma* subsingleton_of_empty_right
- \+ *lemma* scalar_inj

Created src/data/matrix/char_p.lean


Modified src/data/polynomial/basic.lean
- \+ *lemma* commute_X

Modified src/field_theory/finite.lean
- \+/\- *lemma* pow_card_sub_one_eq_one
- \+ *lemma* pow_card
- \+ *lemma* expand_card
- \+ *lemma* card_units
- \+ *theorem* frobenius_pow
- \+ *theorem* units_pow_card_sub_one_eq_one
- \+ *theorem* pow_card_sub_one_eq_one

Modified src/field_theory/separable.lean
- \+ *theorem* map_expand
- \+ *theorem* expand_char
- \+ *theorem* map_expand_pow_char

Modified src/linear_algebra/char_poly/coeff.lean
- \+ *lemma* finite_field.char_poly_pow_card
- \+ *lemma* zmod.char_poly_pow_card
- \+ *lemma* finite_field.trace_pow_card
- \+ *lemma* zmod.trace_pow_card

Modified src/number_theory/quadratic_reciprocity.lean
- \- *lemma* card_units
- \- *theorem* fermat_little_units
- \- *theorem* fermat_little



## [2020-08-29 17:36:21](https://github.com/leanprover-community/mathlib/commit/4c4243c)
feat(linear_algebra): determinant of vectors in a basis ([#3919](https://github.com/leanprover-community/mathlib/pull/3919))
From the sphere eversion project, define the determinant of a family of vectors with respects to a basis. 
The main result is `is_basis.iff_det` asserting a family of vectors is a basis iff its determinant in some basis is invertible.
Also renames `equiv_fun_basis` to `is_basis.equiv_fun` and `equiv_fun_basis_symm_apply` to `is_basis.equiv_fun_symm_apply`, in order to use dot notation.
#### Estimated changes
Modified src/algebra/big_operators/pi.lean
- \+ *lemma* fintype.prod_apply

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/linear_algebra/basic.lean
- \+ *lemma* map_sum

Modified src/linear_algebra/basis.lean
- \+ *lemma* is_basis.repr_self_apply
- \+ *lemma* is_basis.equiv_fun_symm_apply
- \+ *lemma* is_basis.equiv_fun_apply
- \+ *lemma* is_basis.equiv_fun_total
- \+ *lemma* is_basis.equiv_fun_self
- \- *lemma* equiv_fun_basis_symm_apply
- \+ *def* is_basis.equiv_fun
- \- *def* equiv_fun_basis

Modified src/linear_algebra/matrix.lean
- \+ *lemma* to_matrix_apply
- \+ *lemma* to_matrix_self
- \+ *lemma* to_matrix_update
- \+ *lemma* is_basis.det_apply
- \+ *lemma* is_basis.det_self
- \+ *lemma* is_basis.iff_det
- \+ *def* is_basis.to_matrix
- \+ *def* to_matrix_equiv
- \+ *def* is_basis.det



## [2020-08-29 15:59:15](https://github.com/leanprover-community/mathlib/commit/94b1292)
doc(topology/sheaves): update module docs ([#3971](https://github.com/leanprover-community/mathlib/pull/3971))
#### Estimated changes
Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/sheaf_of_functions.lean




## [2020-08-29 15:59:13](https://github.com/leanprover-community/mathlib/commit/ba41f0a)
feat(data/nat): API for test_bit and bitwise operations ([#3964](https://github.com/leanprover-community/mathlib/pull/3964))
#### Estimated changes
Modified src/data/bool.lean
- \+ *theorem* bxor_ff_left
- \+ *theorem* bxor_ff_right

Modified src/data/nat/basic.lean
- \- *lemma* bitwise_comm
- \- *lemma* lor_comm
- \- *lemma* land_comm
- \- *lemma* lxor_comm

Created src/data/nat/bitwise.lean
- \+ *lemma* bit_ff
- \+ *lemma* bit_tt
- \+ *lemma* zero_of_test_bit_eq_ff
- \+ *lemma* zero_test_bit
- \+ *lemma* eq_of_test_bit_eq
- \+ *lemma* exists_most_significant_bit
- \+ *lemma* lt_of_test_bit
- \+ *lemma* bitwise_comm
- \+ *lemma* lor_comm
- \+ *lemma* land_comm
- \+ *lemma* lxor_comm
- \+ *lemma* zero_lxor
- \+ *lemma* lxor_zero
- \+ *lemma* zero_land
- \+ *lemma* land_zero
- \+ *lemma* zero_lor
- \+ *lemma* lor_zero
- \+ *lemma* lxor_assoc
- \+ *lemma* land_assoc
- \+ *lemma* lor_assoc
- \+ *lemma* lxor_self
- \+ *lemma* lxor_right_inj
- \+ *lemma* lxor_left_inj
- \+ *lemma* lxor_eq_zero



## [2020-08-29 14:16:16](https://github.com/leanprover-community/mathlib/commit/faf1df4)
chore(topology/sheaves/sheaf_of_functions): rely less on defeq ([#3972](https://github.com/leanprover-community/mathlib/pull/3972))
This backports some changes from the `prop_limits` branch.
#### Estimated changes
Modified src/category_theory/limits/shapes/types.lean
- \+ *lemma* lift_π_apply'

Modified src/topology/category/Top/opens.lean


Modified src/topology/sheaves/sheaf_of_functions.lean




## [2020-08-29 14:16:14](https://github.com/leanprover-community/mathlib/commit/fd4628f)
chore(*): bump to lean 3.19.0c, fin is now a subtype ([#3955](https://github.com/leanprover-community/mathlib/pull/3955))
* Some `decidable.*` order theorems have been moved to core.
* `fin` is now a subtype. 
This means that the whnf of `fin n` is now `{i // i < n}`.
Also, the coercion `fin n → nat` is now preferred over `subtype.val`.
The entire library has been refactored accordingly. (Although I probably missed some cases.)
* `in_current_file'` was removed since the bug in 
`in_current_file` was fixed in core.
* The syntax of `guard_hyp` in core was changed from
`guard_hyp h := t` to `guard_hyp h : t`, so the syntax
for the related `guard_hyp'`, `match_hyp` and
`guard_hyp_strict` tactics in `tactic.interactive` was changed as well.
#### Estimated changes
Modified archive/100-theorems-list/73_ascending_descending_sequences.lean


Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified leanpkg.toml


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/linear_recurrence.lean


Modified src/algebra/order.lean
- \- *lemma* not_lt
- \- *lemma* not_le
- \- *lemma* lt_or_eq_of_le
- \- *lemma* eq_or_lt_of_le
- \- *lemma* le_iff_lt_or_eq
- \- *lemma* le_of_not_lt
- \- *lemma* lt_or_le
- \- *lemma* le_or_lt
- \- *lemma* lt_trichotomy
- \- *lemma* lt_or_gt_of_ne
- \- *lemma* ne_iff_lt_or_gt
- \- *lemma* le_imp_le_of_lt_imp_lt
- \- *def* lt_by_cases

Modified src/analysis/analytic/composition.lean


Modified src/combinatorics/composition.lean
- \+/\- *lemma* lt_size_up_to_index_succ
- \+/\- *lemma* lt_length
- \+/\- *lemma* lt_length'

Modified src/computability/primrec.lean
- \+/\- *theorem* fin_val

Modified src/data/array/lemmas.lean
- \+/\- *theorem* write_to_list

Modified src/data/bitvec/basic.lean
- \+/\- *lemma* to_fin_val

Modified src/data/equiv/fin.lean


Modified src/data/fin.lean
- \+ *lemma* is_lt
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* coe_injective
- \+ *lemma* mk_coe
- \+ *lemma* val_eq_coe
- \+ *lemma* coe_add
- \+ *lemma* coe_mul
- \+ *lemma* coe_one'
- \+/\- *lemma* mk_zero
- \+/\- *lemma* mk_one
- \+/\- *lemma* coe_val_eq_self
- \+ *lemma* lt_iff_coe_lt_coe
- \+ *lemma* le_iff_coe_le_coe
- \+ *lemma* coe_succ
- \+/\- *lemma* succ_pos
- \+ *lemma* coe_pred
- \+ *lemma* coe_cast
- \+ *lemma* coe_cast_succ
- \+ *lemma* coe_cast_lt
- \+ *lemma* coe_cast_le
- \+ *lemma* coe_cast_add
- \+/\- *lemma* last_val
- \+/\- *lemma* cast_succ_cast_lt
- \+/\- *lemma* cast_lt_cast_succ
- \+ *lemma* coe_sub_nat
- \+ *lemma* coe_add_nat
- \+/\- *lemma* cast_succ_lt_last
- \+/\- *lemma* eq_last_of_not_lt
- \+ *lemma* coe_clamp
- \+ *lemma* coe_of_nat_eq_mod
- \+ *lemma* coe_of_nat_eq_mod'
- \- *lemma* val_injective
- \- *lemma* lt_iff_val_lt_val
- \- *lemma* le_iff_val_le_val
- \- *lemma* succ_val
- \- *lemma* pred_val
- \- *lemma* cast_val
- \- *lemma* cast_succ_val
- \- *lemma* cast_lt_val
- \- *lemma* cast_le_val
- \- *lemma* cast_add_val
- \- *lemma* sub_nat_val
- \- *lemma* add_nat_val
- \- *lemma* clamp_val
- \- *lemma* val_of_nat_eq_mod
- \- *lemma* val_of_nat_eq_mod'
- \- *lemma* function.embedding.coe_fin
- \+/\- *def* sub_nat
- \+/\- *def* clamp
- \- *def* function.embedding.fin

Modified src/data/finset/basic.lean


Modified src/data/finset/sort.lean


Modified src/data/finsupp/basic.lean


Modified src/data/fintype/card.lean


Modified src/data/hash_map.lean


Modified src/data/list/of_fn.lean
- \+/\- *theorem* of_fn_nth_le

Modified src/data/vector2.lean


Modified src/data/zmod/basic.lean


Modified src/group_theory/perm/sign.lean


Modified src/meta/expr.lean


Modified src/order/rel_iso.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/game/short.lean


Modified src/set_theory/pgame.lean


Modified src/tactic/choose.lean


Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Modified src/tactic/lint/frontend.lean


Modified src/topology/list.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified test/apply_fun.lean


Modified test/choose.lean


Modified test/equiv_rw.lean


Modified test/fin_cases.lean


Modified test/generalizes.lean


Modified test/lint.lean


Modified test/norm_cast.lean


Modified test/packaged_goal.lean


Modified test/push_neg.lean


Modified test/rcases.lean


Modified test/rename_var.lean


Modified test/rewrite.lean


Modified test/set.lean


Modified test/tactics.lean


Modified test/trunc_cases.lean


Modified test/wlog.lean


Modified test/zify.lean




## [2020-08-29 13:43:16](https://github.com/leanprover-community/mathlib/commit/17c4651)
feat(algebraic_geometry): structure sheaf on Spec R ([#3907](https://github.com/leanprover-community/mathlib/pull/3907))
This defines the structure sheaf on Spec R, following Hartshorne, as a sheaf in `CommRing` on `prime_spectrum R`.
We still need to show at the stalk at a point is just the localization; this is another page of Hartshorne, and will come in a subsequent PR.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean


Created src/algebraic_geometry/structure_sheaf.lean
- \+ *lemma* is_locally_fraction_pred
- \+ *def* Spec.Top
- \+ *def* localizations
- \+ *def* is_fraction
- \+ *def* is_fraction_prelocal
- \+ *def* is_locally_fraction
- \+ *def* sections_subring
- \+ *def* structure_sheaf_in_Type
- \+ *def* structure_presheaf_in_CommRing
- \+ *def* structure_presheaf_comp_forget
- \+ *def* structure_sheaf



## [2020-08-29 11:21:31](https://github.com/leanprover-community/mathlib/commit/84d47a0)
refactor(set_theory/game): make impartial a class ([#3974](https://github.com/leanprover-community/mathlib/pull/3974))
* Misc. style cleanups and code golf
* Changed naming and namespace to adhere more closely to the naming convention
* Changed `impartial` to be a `class`. I am aware that @semorrison explicitly requested not to make `impartial` a class in the [#3855](https://github.com/leanprover-community/mathlib/pull/3855), but after working with the definition a bit I concluded that making it a class is worth it, simply because writing `impartial_add (nim_impartial _) (nim_impartial _)` gets annoying quite quickly, but also because you tend to get goal states of the form `Grundy_value _ = Grundy_value _`. By making `impartial` a class and making the game argument explicit, these goal states look like `grundy_value G = grundy_value H`, which is much nicer to work with.
#### Estimated changes
Modified src/set_theory/game/impartial.lean
- \+ *lemma* neg_equiv_self
- \+ *lemma* winner_cases
- \+ *lemma* not_first_wins
- \+ *lemma* not_first_loses
- \+ *lemma* add_self
- \+/\- *lemma* equiv_iff_sum_first_loses
- \+ *lemma* le_zero_iff
- \+ *lemma* lt_zero_iff
- \+ *lemma* first_loses_symm
- \+ *lemma* first_wins_symm
- \+ *lemma* first_loses_symm'
- \+ *lemma* first_wins_symm'
- \+/\- *lemma* no_good_left_moves_iff_first_loses
- \+/\- *lemma* no_good_right_moves_iff_first_loses
- \+/\- *lemma* good_left_move_iff_first_wins
- \+/\- *lemma* good_right_move_iff_first_wins
- \- *lemma* zero_impartial
- \- *lemma* impartial_neg_equiv_self
- \- *lemma* impartial_move_left_impartial
- \- *lemma* impartial_move_right_impartial
- \- *lemma* impartial_add
- \- *lemma* impartial_neg
- \- *lemma* impartial_winner_cases
- \- *lemma* impartial_not_first_wins
- \- *lemma* impartial_not_first_loses
- \- *lemma* impartial_add_self
- \- *lemma* impartial_first_loses_symm
- \- *lemma* impartial_first_wins_symm
- \- *lemma* impartial_first_loses_symm'
- \- *lemma* impartial_first_wins_symm'
- \+/\- *def* impartial

Modified src/set_theory/game/nim.lean
- \+ *lemma* zero_first_loses
- \+ *lemma* non_zero_first_wins
- \+ *lemma* sum_first_loses_iff_eq
- \+ *lemma* sum_first_wins_iff_neq
- \+ *lemma* equiv_iff_eq
- \+ *lemma* grundy_value_def
- \+ *lemma* equiv_nim_iff_grundy_value_eq
- \+ *lemma* nim.grundy_value
- \- *lemma* nim_impartial
- \- *lemma* nim_zero_first_loses
- \- *lemma* nim_non_zero_first_wins
- \- *lemma* nim_sum_first_loses_iff_eq
- \- *lemma* nim_sum_first_wins_iff_neq
- \- *lemma* nim_equiv_iff_eq
- \- *lemma* Grundy_value_def
- \- *lemma* equiv_nim_iff_Grundy_value_eq
- \- *lemma* Grundy_value_nim
- \+ *theorem* equiv_nim_grundy_value
- \- *theorem* Sprague_Grundy

Modified src/set_theory/game/winner.lean
- \+/\- *theorem* star_first_wins



## [2020-08-29 04:30:09](https://github.com/leanprover-community/mathlib/commit/ea177c2)
feat(analysis/convex): add correspondence between convex cones and ordered semimodules ([#3931](https://github.com/leanprover-community/mathlib/pull/3931))
This shows that a convex cone defines an ordered semimodule and vice-versa.
#### Estimated changes
Modified src/algebra/module/ordered.lean


Modified src/analysis/convex/cone.lean
- \+ *lemma* pointed_iff_not_blunt
- \+ *lemma* salient_iff_not_flat
- \+ *lemma* salient_of_blunt
- \+ *lemma* salient_of_positive_cone
- \+ *lemma* pointed_of_positive_cone
- \+ *def* to_ordered_semimodule
- \+ *def* pointed
- \+ *def* blunt
- \+ *def* flat
- \+ *def* salient
- \+ *def* to_preorder
- \+ *def* to_partial_order
- \+ *def* to_ordered_add_comm_group
- \+ *def* positive_cone



## [2020-08-29 02:58:36](https://github.com/leanprover-community/mathlib/commit/53275f4)
chore(algebra/group_with_zero): adjust some instance priorities ([#3968](https://github.com/leanprover-community/mathlib/pull/3968))
Use priority 100 for these `extends` instances.
#### Estimated changes
Modified src/algebra/group_with_zero.lean




## [2020-08-29 00:44:57](https://github.com/leanprover-community/mathlib/commit/2d3530d)
chore(scripts): update nolints.txt ([#3969](https://github.com/leanprover-community/mathlib/pull/3969))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-28 16:07:49](https://github.com/leanprover-community/mathlib/commit/4ccbb51)
feat(linear_algebra): eigenspaces of linear maps ([#3927](https://github.com/leanprover-community/mathlib/pull/3927))
Add eigenspaces and eigenvalues of linear maps. Add lemma that in a
finite-dimensional vector space over an algebraically closed field,
eigenvalues exist. Add lemma that eigenvectors belonging to distinct
eigenvalues are linearly independent.
This is a rework of [#3864](https://github.com/leanprover-community/mathlib/pull/3864), following Cyril's suggestion. Generalized
eigenspaces will come in a subsequent PR.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* mem_support_on_finset
- \+ *lemma* support_on_finset

Modified src/data/multiset/basic.lean
- \+ *lemma* to_list_zero
- \+ *lemma* coe_to_list
- \+ *lemma* mem_to_list
- \+ *lemma* prod_eq_zero

Modified src/field_theory/algebraic_closure.lean
- \+ *lemma* degree_eq_one_of_irreducible

Modified src/field_theory/splitting_field.lean
- \+ *lemma* degree_eq_one_of_irreducible_of_splits

Modified src/group_theory/submonoid/basic.lean
- \+ *lemma* is_unit.mem_submonoid_iff
- \+ *def* is_unit.submonoid

Created src/linear_algebra/eigenspace.lean
- \+ *lemma* mem_eigenspace_iff
- \+ *lemma* eigenspace_div
- \+ *lemma* eigenspace_eval₂_polynomial_degree_1
- \+ *lemma* ker_eval₂_ring_hom_noncomm_unit_polynomial
- \+ *lemma* exists_eigenvalue
- \+ *lemma* eigenvectors_linear_independent
- \+ *def* eigenspace
- \+ *def* has_eigenvector
- \+ *def* has_eigenvalue

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* not_linear_independent_of_infinite

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* total_on_finset

Modified src/ring_theory/algebra.lean
- \+ *lemma* algebra_map_End_eq_smul_id
- \+ *lemma* algebra_map_End_apply
- \+ *lemma* ker_algebra_map_End

Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* linear_independent_powers_iff_eval₂

Modified src/ring_theory/principal_ideal_domain.lean
- \+ *lemma* ne_zero_of_mem_factors
- \+ *lemma* mem_submonoid_of_factors_subset_of_units_subset
- \+ *lemma* ring_hom_mem_submonoid_of_factors_subset_of_units_subset



## [2020-08-28 15:21:57](https://github.com/leanprover-community/mathlib/commit/1353b7e)
chore(group_theory/perm/sign): speed up proofs ([#3963](https://github.com/leanprover-community/mathlib/pull/3963))
fixes [#3958](https://github.com/leanprover-community/mathlib/pull/3958) 
based on my completely unscientific test methods, this went from 40 seconds to ~~19~~ 17 seconds (on my laptop).
What I've done here is just `squeeze_simp`, but further speedup is definitely possible. Suggestions for what to do with `simp [*, eq_inv_iff_eq] at * <|> cc` are welcome, and should speed this file up a bit more.
#### Estimated changes
Modified src/group_theory/perm/sign.lean




## [2020-08-28 14:46:42](https://github.com/leanprover-community/mathlib/commit/d77798a)
doc(representation_theory/maschke): fix latex ([#3965](https://github.com/leanprover-community/mathlib/pull/3965))
#### Estimated changes
Modified src/representation_theory/maschke.lean




## [2020-08-28 14:11:16](https://github.com/leanprover-community/mathlib/commit/31db0bd)
feat(category_theory/limits): add kernel pairs ([#3925](https://github.com/leanprover-community/mathlib/pull/3925))
Add a subsingleton data structure expressing that a parallel pair of morphisms is a kernel pair of a given morphism.
Another PR from my topos project. A pretty minimal API since I didn't need much there - I also didn't introduce anything like `has_kernel_pairs` largely because I didn't need it, but also because I don't know that it's useful for anyone, and it might conflict with ideas in the prop-limits branch.
#### Estimated changes
Created src/category_theory/limits/shapes/kernel_pair.lean
- \+ *def* id_of_mono
- \+ *def* lift'
- \+ *def* cancel_right
- \+ *def* cancel_right_of_mono
- \+ *def* comp_of_mono
- \+ *def* to_coequalizer



## [2020-08-28 10:25:09](https://github.com/leanprover-community/mathlib/commit/a08fb2f)
feat(tactic/congr): additions to the congr' tactic ([#3936](https://github.com/leanprover-community/mathlib/pull/3936))
This PR gives a way to apply `ext` after `congr'`.
`congr' 3 with x y : 2` is a new notation for `congr' 3; ext x y : 2`.
New tactic `rcongr` that recursively keeps applying `congr'` and `ext`.
Move `congr'` and every tactic depending on it from `tactic/interactive` to a new file `tactic/congr`.
The original `tactic.interactive.congr'` is now best called as `tactic.congr'`. 
Other than the tactics `congr'` and `rcongr` no tactics have been (essentially) changed.
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/algebra/big_operators/ring.lean


Modified src/algebra/group_action_hom.lean


Modified src/algebra/linear_recurrence.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/hofer.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/special_functions/exp_log.lean


Modified src/category_theory/limits/limits.lean


Modified src/computability/turing_machine.lean


Modified src/control/monad/cont.lean


Modified src/data/finset/lattice.lean


Modified src/data/list/func.lean


Modified src/data/list/sigma.lean


Modified src/data/monoid_algebra.lean


Modified src/data/mv_polynomial.lean


Modified src/data/pfunctor/multivariate/M.lean


Modified src/data/pfunctor/multivariate/basic.lean


Modified src/data/pfunctor/univariate/M.lean
- \+/\- *lemma* ext'

Modified src/data/polynomial/identities.lean


Modified src/data/polynomial/integral_normalization.lean


Modified src/data/qpf/multivariate/constructions/cofix.lean


Modified src/data/qpf/univariate/basic.lean


Modified src/data/set/basic.lean


Modified src/data/setoid/basic.lean


Modified src/geometry/euclidean/basic.lean


Modified src/geometry/euclidean/circumcenter.lean


Modified src/geometry/euclidean/monge_point.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/monoid_localization.lean


Modified src/linear_algebra/affine_space/basic.lean


Modified src/linear_algebra/affine_space/combination.lean


Modified src/linear_algebra/affine_space/independent.lean


Modified src/linear_algebra/matrix.lean


Modified src/linear_algebra/multilinear.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean


Modified src/order/liminf_limsup.lean


Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/ideal/basic.lean


Modified src/ring_theory/polynomial_algebra.lean


Modified src/tactic/basic.lean


Created src/tactic/congr.lean


Modified src/tactic/ext.lean


Modified src/tactic/interactive.lean


Modified src/topology/algebra/multilinear.lean


Modified src/topology/bases.lean


Modified src/topology/opens.lean


Modified src/topology/uniform_space/compact_separated.lean


Created test/congr.lean


Modified test/tactics.lean


Modified test/trunc_cases.lean




## [2020-08-28 07:24:16](https://github.com/leanprover-community/mathlib/commit/ceacf54)
feat(category_theory/filtered): filtered categories, and filtered colimits in `Type` ([#3960](https://github.com/leanprover-community/mathlib/pull/3960))
This is some work @rwbarton did last year. I've merged master, written some comments, and satisfied the linter.
#### Estimated changes
Created src/category_theory/filtered.lean


Modified src/category_theory/limits/types.lean
- \+ *lemma* ι_desc_apply
- \+ *lemma* jointly_surjective
- \+ *lemma* colimit_eq_iff
- \+ *lemma* is_colimit_eq_iff

Modified src/data/quot.lean
- \+ *lemma* quot.eq



## [2020-08-28 05:18:40](https://github.com/leanprover-community/mathlib/commit/513f740)
feat(topology/sheaves): checking the sheaf condition under a forgetful functor ([#3609](https://github.com/leanprover-community/mathlib/pull/3609))
# Checking the sheaf condition on the underlying presheaf of types.
If `G : C ⥤ D` is a functor which reflects isomorphisms and preserves limits
(we assume all limits exist in both `C` and `D`),
then checking the sheaf condition for a presheaf `F : presheaf C X`
is equivalent to checking the sheaf condition for `F ⋙ G`.
The important special case is when
`C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphisms.
Then to check the sheaf condition it suffices
to check it on the underlying sheaf of types.
## References
* https://stacks.math.columbia.edu/tag/0073
#### Estimated changes
Created src/topology/sheaves/forget.lean
- \+ *def* diagram_comp_preserves_limits
- \+ *def* map_cone_fork
- \+ *def* sheaf_condition_equiv_sheaf_condition_comp



## [2020-08-28 03:16:37](https://github.com/leanprover-community/mathlib/commit/7e6393f)
feat(topology/sheaves): the sheaf condition for functions satisfying a local predicate ([#3906](https://github.com/leanprover-community/mathlib/pull/3906))
Functions satisfying a local predicate form a sheaf.
This sheaf has a natural map from the stalk to the original fiber, and we give conditions for this map to be injective or surjective.
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* fork.ext
- \+ *def* cofork.ext

Modified src/category_theory/limits/shapes/products.lean


Modified src/data/set/basic.lean
- \+ *lemma* inclusion_right

Modified src/topology/category/Top/open_nhds.lean
- \+/\- *lemma* inclusion_obj
- \+/\- *def* open_nhds
- \+/\- *def* inclusion

Created src/topology/sheaves/local_predicate.lean
- \+ *lemma* stalk_to_fiber_germ
- \+ *lemma* stalk_to_fiber_surjective
- \+ *lemma* stalk_to_fiber_injective
- \+ *def* continuous_prelocal
- \+ *def* continuous_local
- \+ *def* prelocal_predicate.sheafify
- \+ *def* subpresheaf_to_Types
- \+ *def* subtype
- \+ *def* diagram_subtype
- \+ *def* sheaf_condition
- \+ *def* subsheaf_to_Types
- \+ *def* stalk_to_fiber
- \+ *def* subpresheaf_continuous_prelocal_iso_presheaf_to_Top
- \+ *def* sheaf_to_Top

Modified src/topology/sheaves/presheaf_of_functions.lean
- \+ *lemma* presheaf_to_Types_obj
- \+ *lemma* presheaf_to_Types_map
- \+ *lemma* presheaf_to_Top_obj
- \+/\- *def* presheaf_to_Types

Modified src/topology/sheaves/sheaf.lean
- \+ *def* pi_opens.iso_of_iso
- \+ *def* pi_inters.iso_of_iso
- \+ *def* diagram.iso_of_iso
- \+ *def* fork.iso_of_iso
- \+ *def* sheaf_condition_equiv_of_iso

Modified src/topology/sheaves/sheaf_of_functions.lean
- \+ *def* sheaf_to_Types
- \+ *def* sheaf_to_Type
- \- *def* forget_continuity
- \- *def* to_Top

Modified src/topology/sheaves/stalks.lean
- \+/\- *lemma* stalk_functor_obj
- \+ *lemma* germ_res
- \+ *lemma* germ_res_apply
- \+ *def* germ



## [2020-08-27 20:30:40](https://github.com/leanprover-community/mathlib/commit/eaaac99)
feat(geometry/euclidean/basic): reflection ([#3932](https://github.com/leanprover-community/mathlib/pull/3932))
Define the reflection of a point in an affine subspace, as a bundled
isometry, in terms of the orthogonal projection onto that subspace,
and prove some basic lemmas about it.
#### Estimated changes
Modified src/geometry/euclidean/basic.lean
- \+ *lemma* orthogonal_projection_linear
- \+ *lemma* orthogonal_projection_orthogonal_projection
- \+ *lemma* reflection_apply
- \+ *lemma* reflection_symm
- \+ *lemma* reflection_reflection
- \+ *lemma* reflection_involutive
- \+ *lemma* reflection_eq_self_iff
- \+ *lemma* reflection_eq_iff_orthogonal_projection_eq
- \+ *lemma* dist_reflection
- \+ *lemma* dist_reflection_eq_of_mem
- \+ *def* reflection



## [2020-08-27 18:31:26](https://github.com/leanprover-community/mathlib/commit/359261e)
feat(data/nat): commutativity of bitwise operations ([#3956](https://github.com/leanprover-community/mathlib/pull/3956))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* bitwise_comm
- \+ *lemma* lor_comm
- \+ *lemma* land_comm
- \+ *lemma* lxor_comm



## [2020-08-27 14:44:42](https://github.com/leanprover-community/mathlib/commit/6b556cf)
feat(combinatorics/adjacency_matrix): defines adjacency matrices of simple graphs ([#3672](https://github.com/leanprover-community/mathlib/pull/3672))
defines the adjacency matrix of a simple graph
proves lemmas about adjacency matrix that will form the bulk of the proof of the friendship theorem (freek 83)
#### Estimated changes
Created src/combinatorics/adj_matrix.lean
- \+ *lemma* adj_matrix_apply
- \+ *lemma* adj_matrix_dot_product
- \+ *lemma* dot_product_adj_matrix
- \+ *lemma* adj_matrix_mul_vec_apply
- \+ *lemma* adj_matrix_vec_mul_apply
- \+ *lemma* adj_matrix_mul_apply
- \+ *lemma* mul_adj_matrix_apply
- \+ *lemma* adj_matrix_mul_vec_const_apply
- \+ *lemma* adj_matrix_mul_vec_const_apply_of_regular
- \+ *theorem* transpose_adj_matrix
- \+ *theorem* trace_adj_matrix
- \+ *theorem* adj_matrix_mul_self_apply_self
- \+ *def* adj_matrix



## [2020-08-27 06:25:31](https://github.com/leanprover-community/mathlib/commit/ea9bf31)
refactor(analysis/normed_space/real_inner_product,geometry/euclidean): orthogonal projection hypotheses ([#3952](https://github.com/leanprover-community/mathlib/pull/3952))
As advised by Patrick in [#3932](https://github.com/leanprover-community/mathlib/pull/3932), define `orthogonal_projection` (for
both real inner product spaces and Euclidean affine spaces) without
taking hypotheses of the subspace being nonempty and complete,
defaulting to the identity map if those conditions are not satisfied,
so making `orthogonal_projection` more convenient to use with those
properties only being needed on lemmas but not simply to refer to the
orthogonal projection at all.
The hypotheses are removed from lemmas that don't need them because
they are still true with the identity map.  Some `nonempty` hypotheses
are also removed where they follow from another hypothesis that gives
a point or a nonempty set of points in the subspace.
The unbundled `orthogonal_projection_fn` that's used only to prove
properties needed to define a bundled linear or affine map still takes
the original hypotheses, then a bundled map taking those hypotheses is
defined under a new name, then that map is used to define plain
`orthogonal_projection` which does not take any of those hypotheses
and is the version expected to be used in all lemmas after it has been
defined.
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean
- \+ *lemma* orthogonal_projection_def
- \+/\- *lemma* orthogonal_projection_inner_eq_zero
- \+ *def* orthogonal_projection_of_complete
- \+/\- *def* orthogonal_projection

Modified src/geometry/euclidean/basic.lean
- \+ *lemma* orthogonal_projection_def
- \+ *lemma* orthogonal_projection_of_nonempty_of_complete_eq
- \+/\- *lemma* orthogonal_projection_mem_orthogonal
- \+/\- *lemma* orthogonal_projection_vsub_mem_direction_orthogonal
- \+/\- *lemma* vsub_orthogonal_projection_mem_direction_orthogonal
- \+ *def* orthogonal_projection_of_nonempty_of_complete
- \+/\- *def* orthogonal_projection

Modified src/geometry/euclidean/circumcenter.lean
- \+/\- *lemma* dist_eq_iff_dist_orthogonal_projection_eq
- \+/\- *lemma* dist_set_eq_iff_dist_orthogonal_projection_eq
- \+/\- *lemma* exists_unique_dist_eq_of_insert



## [2020-08-27 00:47:46](https://github.com/leanprover-community/mathlib/commit/5627aed)
chore(scripts): update nolints.txt ([#3954](https://github.com/leanprover-community/mathlib/pull/3954))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-26 20:24:56](https://github.com/leanprover-community/mathlib/commit/c147894)
feat(data/fin): flesh out API for fin ([#3769](https://github.com/leanprover-community/mathlib/pull/3769))
Provide more API for `fin n`. Lemma names chosen to match equivalent lemmas in `nat`. Does not develop docstrings for the lemmas.
New lemmas:
iff lemmas for comparison
`ne_iff_vne`
`eq_mk_iff_coe_eq`
`succ_le_succ_iff`
`succ_lt_succ_iff`
lemmas about explicit numerals
`val_zero'`
`mk_zero`
`mk_one`
`mk_bit0`
`mk_bit1`
`cast_succ_zero`
`succ_zero_eq_one`
`zero_ne_one`
`pred_one`
lemmas about order
`zero_le`
`succ_pos`
`mk_succ_pos`
`one_pos`
`one_lt_succ_succ`
`succ_succ_ne_one`
`pred_mk_succ`
`cast_succ_lt_last`
`cast_succ_lt_succ`
`lt_succ`
`last_pos`
`le_coe_last`
coe lemmas:
`coe_eq_cast_succ`
`coe_succ_eq_succ`
`coe_nat_eq_last`
succ_above API:
`succ_above_below`
`succ_above_zero`
`succ_above_last`
`succ_above_above`
`succ_above_pos`
addition API:
`add_one_pos`
`pred_add_one`
Co-authored by: Yury Kudryashov urkud@ya.ru
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean


Modified src/data/fin.lean
- \+ *lemma* ne_iff_vne
- \+ *lemma* eq_mk_iff_coe_eq
- \+ *lemma* val_zero'
- \+ *lemma* mk_zero
- \+ *lemma* mk_one
- \+ *lemma* mk_bit0
- \+ *lemma* mk_bit1
- \+/\- *lemma* zero_le
- \+ *lemma* succ_pos
- \+ *lemma* succ_le_succ_iff
- \+ *lemma* succ_lt_succ_iff
- \+ *lemma* succ_zero_eq_one
- \+ *lemma* mk_succ_pos
- \+ *lemma* one_lt_succ_succ
- \+ *lemma* succ_succ_ne_one
- \+ *lemma* pred_mk_succ
- \+ *lemma* cast_succ_lt_last
- \+ *lemma* cast_succ_zero
- \+ *lemma* last_pos
- \+ *lemma* coe_nat_eq_last
- \+ *lemma* le_coe_last
- \+ *lemma* add_one_pos
- \+ *lemma* one_pos
- \+ *lemma* zero_ne_one
- \+ *lemma* cast_succ_lt_succ
- \+ *lemma* coe_eq_cast_succ
- \+ *lemma* coe_succ_eq_succ
- \+ *lemma* lt_succ
- \+ *lemma* pred_one
- \+ *lemma* pred_add_one
- \+ *lemma* succ_above_below
- \+ *lemma* succ_above_zero
- \+ *lemma* succ_above_last
- \+ *lemma* succ_above_above
- \+ *lemma* succ_above_pos
- \- *lemma* zero_val
- \- *lemma* cast_succ_ne_last

Modified src/data/fintype/card.lean


Modified src/data/matrix/notation.lean
- \+/\- *lemma* cons_val_zero'

Modified src/linear_algebra/multilinear.lean




## [2020-08-26 18:55:44](https://github.com/leanprover-community/mathlib/commit/26dfea5)
feat(algebra/big_operators): sum of two products ([#3944](https://github.com/leanprover-community/mathlib/pull/3944))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_inter_mul_prod_diff
- \+ *lemma* mul_prod_diff_singleton
- \+ *lemma* prod_add_prod_eq

Modified src/algebra/big_operators/order.lean
- \+ *lemma* prod_add_prod_le
- \+ *lemma* prod_add_prod_le'

Modified src/algebra/group_with_zero_power.lean
- \+ *lemma* zero_pow_eq_zero

Modified src/algebra/ordered_ring.lean
- \+ *lemma* mul_le_mul_left'
- \+ *lemma* mul_le_mul_right'



## [2020-08-26 18:55:42](https://github.com/leanprover-community/mathlib/commit/64aad5b)
feat(category_theory/adjunction): uniqueness of adjunctions ([#3940](https://github.com/leanprover-community/mathlib/pull/3940))
Co-authored by @thjread
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/opposites.lean
- \+ *def* left_adjoints_coyoneda_equiv
- \+ *def* left_adjoint_uniq
- \+ *def* right_adjoint_uniq



## [2020-08-26 18:55:40](https://github.com/leanprover-community/mathlib/commit/080746f)
feat(algebra/category/*/limits): don't rely on definitions ([#3873](https://github.com/leanprover-community/mathlib/pull/3873))
This is a second attempt (which works **much** better) at [#3860](https://github.com/leanprover-community/mathlib/pull/3860), after @TwoFX explained how to do it properly.
This PR takes the constructions of limits in the concrete categories `(Add)(Comm)[Mon|Group]`, `(Comm)(Semi)Ring`, `Module R`, and `Algebra R`, and makes sure that they never rely on the actual definitions of limits in "prior" categories.
Of course, at this stage the `has_limit` typeclasses still contain data, so it's hard to judge whether we're really not relying on the definitions. I've marked all the `has_limits` instances in these files as irreducible, but the real proof is just that this same code is working over on the `prop_limits` branch.
#### Estimated changes
Modified src/algebra/category/Algebra/limits.lean
- \+ *def* limit_cone
- \+ *def* limit_cone_is_limit
- \+ *def* forget₂_Ring_preserves_limits_aux
- \+ *def* forget₂_Module_preserves_limits_aux
- \- *def* limit
- \- *def* limit_is_limit

Modified src/algebra/category/CommRing/limits.lean
- \+ *def* limit_cone
- \+ *def* limit_cone_is_limit
- \+ *def* forget₂_CommSemiRing_preserves_limits_aux
- \- *def* limit
- \- *def* limit_is_limit

Modified src/algebra/category/Group/limits.lean
- \+ *lemma* lift_π_apply
- \+ *def* limit_cone
- \+ *def* limit_cone_is_limit

Modified src/algebra/category/Module/limits.lean
- \+ *def* limit_cone
- \+ *def* limit_cone_is_limit
- \+ *def* forget₂_AddCommGroup_preserves_limits_aux
- \- *def* limit
- \- *def* limit_is_limit

Modified src/algebra/category/Mon/limits.lean
- \+ *def* limit_cone
- \+ *def* limit_cone_is_limit
- \- *def* limit
- \- *def* limit_is_limit

Modified src/topology/category/Top/limits.lean
- \+ *def* limit_cone
- \+ *def* limit_cone_is_limit
- \+ *def* colimit_cocone
- \+ *def* colimit_cocone_is_colimit
- \- *def* limit
- \- *def* limit_is_limit
- \- *def* colimit
- \- *def* colimit_is_colimit



## [2020-08-26 17:53:30](https://github.com/leanprover-community/mathlib/commit/2d9ab61)
feat(ring_theory/ideal/basic): R/I is an ID iff I is prime ([#3951](https://github.com/leanprover-community/mathlib/pull/3951))
`is_integral_domain_iff_prime (I : ideal α) : is_integral_domain I.quotient ↔ I.is_prime`
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* is_integral_domain_iff_prime



## [2020-08-26 16:20:07](https://github.com/leanprover-community/mathlib/commit/2b6924d)
feat(topology/algebra/ordered): conditions for a strictly monotone function to be a homeomorphism ([#3843](https://github.com/leanprover-community/mathlib/pull/3843))
If a strictly monotone function between linear orders is surjective, it is a homeomorphism.
If a strictly monotone function between conditionally complete linear orders is continuous, and tends to `+∞` at `+∞` and to `-∞` at `-∞`, then it is a homeomorphism.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Order.20topology)
Co-authored by: Yury Kudryashov <urkud@ya.ru>
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* Ici_singleton_of_top
- \+ *lemma* Iic_singleton_of_bot
- \+ *lemma* Ici_top
- \+ *lemma* Ici_bot

Created src/data/set/intervals/surj_on.lean
- \+ *lemma* surj_on_Ioo_of_monotone_surjective
- \+ *lemma* surj_on_Ico_of_monotone_surjective
- \+ *lemma* surj_on_Ioc_of_monotone_surjective
- \+ *lemma* surj_on_Icc_of_monotone_surjective
- \+ *lemma* surj_on_Ioi_of_monotone_surjective
- \+ *lemma* surj_on_Iio_of_monotone_surjective
- \+ *lemma* surj_on_Ici_of_monotone_surjective
- \+ *lemma* surj_on_Iic_of_monotone_surjective

Modified src/order/basic.lean
- \+ *lemma* top_preimage_top
- \+ *lemma* bot_preimage_bot

Modified src/order/bounded_lattice.lean
- \+ *lemma* strict_mono.top_preimage_top'
- \+ *lemma* strict_mono.bot_preimage_bot'

Modified src/topology/algebra/ordered.lean
- \+ *lemma* continuous_right_of_strict_mono_surjective
- \+ *lemma* continuous_left_of_strict_mono_surjective
- \+ *lemma* surjective_of_continuous
- \+ *lemma* surjective_of_continuous'
- \+ *lemma* continuous_at_of_strict_mono_surjective
- \+ *lemma* continuous_of_strict_mono_surjective
- \+ *lemma* continuous_inv_of_strict_mono_equiv
- \+ *lemma* coe_homeomorph_of_strict_mono_surjective
- \+ *lemma* coe_homeomorph_of_strict_mono_continuous



## [2020-08-26 14:45:52](https://github.com/leanprover-community/mathlib/commit/f4f0854)
feat(ring_theory/bundled_subring): add bundled subrings ([#3886](https://github.com/leanprover-community/mathlib/pull/3886))
#### Estimated changes
Modified src/algebra/category/CommRing/limits.lean


Created src/deprecated/subring.lean
- \+ *lemma* is_subring.coe_subtype
- \+ *lemma* is_subring_Union_of_directed
- \+ *lemma* image_closure
- \+ *theorem* exists_list_of_mem_closure
- \+ *theorem* mem_closure
- \+ *theorem* subset_closure
- \+ *theorem* closure_subset
- \+ *theorem* closure_subset_iff
- \+ *theorem* closure_mono
- \+ *def* ring_hom.cod_restrict
- \+ *def* is_subring.subtype
- \+ *def* closure

Modified src/field_theory/subfield.lean


Modified src/group_theory/subgroup.lean
- \+ *lemma* coe_supr_of_directed
- \+ *def* cod_restrict

Modified src/linear_algebra/basic.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/subring.lean
- \+ *lemma* coe_mk'
- \+ *lemma* mem_mk'
- \+ *lemma* mk'_to_submonoid
- \+ *lemma* mk'_to_add_subgroup
- \+ *lemma* list_prod_mem
- \+ *lemma* list_sum_mem
- \+ *lemma* multiset_prod_mem
- \+ *lemma* multiset_sum_mem
- \+ *lemma* prod_mem
- \+ *lemma* sum_mem
- \+ *lemma* pow_mem
- \+ *lemma* gsmul_mem
- \+ *lemma* coe_int_mem
- \+ *lemma* coe_add
- \+ *lemma* coe_neg
- \+ *lemma* coe_mul
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* le_def
- \+ *lemma* coe_subset_coe
- \+ *lemma* coe_ssubset_coe
- \+ *lemma* mem_coe
- \+ *lemma* coe_coe
- \+ *lemma* mem_to_submonoid
- \+ *lemma* coe_to_submonoid
- \+ *lemma* mem_to_add_subgroup
- \+ *lemma* coe_to_add_subgroup
- \+ *lemma* mem_top
- \+ *lemma* coe_top
- \+ *lemma* coe_comap
- \+ *lemma* mem_comap
- \+ *lemma* comap_comap
- \+ *lemma* coe_map
- \+ *lemma* mem_map
- \+ *lemma* map_map
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* gc_map_comap
- \+ *lemma* coe_range
- \+ *lemma* mem_range
- \+ *lemma* map_range
- \+ *lemma* coe_bot
- \+ *lemma* mem_bot
- \+ *lemma* coe_inf
- \+ *lemma* mem_inf
- \+ *lemma* coe_Inf
- \+ *lemma* mem_Inf
- \+ *lemma* Inf_to_submonoid
- \+ *lemma* Inf_to_add_subgroup
- \+ *lemma* mem_closure
- \+ *lemma* subset_closure
- \+ *lemma* closure_le
- \+ *lemma* closure_mono
- \+ *lemma* closure_eq_of_le
- \+ *lemma* closure_induction
- \+ *lemma* mem_closure_iff
- \+ *lemma* closure_eq
- \+ *lemma* closure_empty
- \+ *lemma* closure_univ
- \+ *lemma* closure_union
- \+ *lemma* closure_Union
- \+ *lemma* closure_sUnion
- \+ *lemma* map_sup
- \+ *lemma* map_supr
- \+ *lemma* comap_inf
- \+ *lemma* comap_infi
- \+ *lemma* map_bot
- \+ *lemma* comap_top
- \+ *lemma* coe_prod
- \+ *lemma* mem_prod
- \+ *lemma* prod_mono
- \+ *lemma* prod_mono_right
- \+ *lemma* prod_mono_left
- \+ *lemma* prod_top
- \+ *lemma* top_prod
- \+ *lemma* top_prod_top
- \+ *lemma* mem_supr_of_directed
- \+ *lemma* coe_supr_of_directed
- \+ *lemma* mem_Sup_of_directed_on
- \+ *lemma* coe_Sup_of_directed_on
- \+ *lemma* restrict_apply
- \+ *lemma* coe_range_restrict
- \+ *lemma* range_top_iff_surjective
- \+ *lemma* range_top_of_surjective
- \+ *lemma* eq_on_set_closure
- \+ *lemma* eq_of_eq_on_set_top
- \+ *lemma* eq_of_eq_on_set_dense
- \+ *lemma* closure_preimage_le
- \+ *lemma* map_closure
- \+ *lemma* range_subtype
- \+ *lemma* range_fst
- \+ *lemma* range_snd
- \+ *lemma* prod_bot_sup_bot_prod
- \- *lemma* is_subring.coe_subtype
- \- *lemma* is_subring_Union_of_directed
- \- *lemma* image_closure
- \+ *theorem* ext'
- \+ *theorem* ext
- \+ *theorem* one_mem
- \+ *theorem* zero_mem
- \+ *theorem* mul_mem
- \+ *theorem* add_mem
- \+ *theorem* neg_mem
- \+ *theorem* coe_subtype
- \+/\- *theorem* exists_list_of_mem_closure
- \- *theorem* mem_closure
- \- *theorem* subset_closure
- \- *theorem* closure_subset
- \- *theorem* closure_subset_iff
- \- *theorem* closure_mono
- \+ *def* to_submonoid
- \+ *def* subsemiring.to_subring
- \+ *def* to_comm_ring
- \+ *def* subtype
- \+ *def* comap
- \+ *def* map
- \+ *def* range
- \+ *def* cod_restrict'
- \+ *def* subset_comm_ring
- \+/\- *def* closure
- \+ *def* prod
- \+ *def* prod_equiv
- \+ *def* restrict
- \+ *def* range_restrict
- \+ *def* eq_locus
- \+ *def* inclusion
- \+ *def* subring_congr
- \- *def* ring_hom.cod_restrict
- \- *def* is_subring.subtype

Modified src/ring_theory/valuation/basic.lean




## [2020-08-26 14:45:50](https://github.com/leanprover-community/mathlib/commit/0d67a02)
feat(ring_theory/noetherian): maximal among set iff Noetherian ([#3846](https://github.com/leanprover-community/mathlib/pull/3846))
Main theorem is `set_has_maximal_iff_noetherian,` which relates well foundedness of `<` to being noetherian.
Most notably a result of
`well_founded.well_founded_iff_has_max'` provides the fact that on a partial ordering, `well_founded >` is equivalent to each nonempty set having a maximal element.
`well_founded.well_founded_iff_has_min` provides an analogous fact for `well_founded <`.
Some other miscellaneous lemmas are as follows
`localization_map.integral_domain_of_local_at_prime` is the localization of an integral domain at a prime's complement is an integral domain
`ideal.mul_eq_bot` is the fact that in an integral domain if I*J = 0, then at least one is 0.
`submodule.nonzero_mem_of_gt_bot` is that if ⊥ < J, then J has a nonzero member.
`lt_add_iff_not_mem` is that b is not a member of J iff J < J+(b).
`bot_prime` states that 0 is a prime ideal of an integral domain.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* nonzero_mem_of_bot_lt
- \+ *lemma* lt_add_iff_not_mem

Modified src/order/rel_classes.lean
- \+ *lemma* eq_iff_not_lt_of_le
- \+ *theorem* well_founded_iff_has_min
- \+ *theorem* well_founded_iff_has_max'
- \+ *theorem* well_founded_iff_has_min'

Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* bot_prime

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* mul_eq_bot

Modified src/ring_theory/localization.lean


Modified src/ring_theory/noetherian.lean
- \+ *theorem* set_has_maximal_iff_noetherian



## [2020-08-26 13:12:40](https://github.com/leanprover-community/mathlib/commit/187bfa5)
feat(set/basic): additions to prod ([#3943](https://github.com/leanprover-community/mathlib/pull/3943))
Also add one lemma about `Inter`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* univ_prod
- \+ *lemma* prod_univ
- \+ *lemma* mk_preimage_prod_left_eq_empty
- \+ *lemma* mk_preimage_prod_right_eq_empty
- \+ *lemma* mk_preimage_prod_left_eq_if
- \+ *lemma* mk_preimage_prod_right_eq_if
- \+/\- *theorem* insert_prod
- \+/\- *theorem* prod_insert
- \+/\- *theorem* prod_eq_empty_iff

Modified src/data/set/lattice.lean
- \+ *lemma* Inter_set_of



## [2020-08-26 13:12:38](https://github.com/leanprover-community/mathlib/commit/fb6046e)
feat(*/category/*): add coe_of simp lemmas ([#3938](https://github.com/leanprover-community/mathlib/pull/3938))
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean
- \+ *lemma* coe_of
- \- *lemma* of_apply

Modified src/algebra/category/CommRing/basic.lean
- \+ *lemma* coe_of

Modified src/algebra/category/Group/basic.lean
- \+ *lemma* coe_of

Modified src/algebra/category/Module/basic.lean
- \+ *lemma* coe_of
- \- *lemma* of_apply

Modified src/algebra/category/Mon/basic.lean
- \+ *lemma* coe_of

Modified src/measure_theory/category/Meas.lean
- \+ *lemma* coe_of

Modified src/topology/category/Top/basic.lean
- \+ *lemma* coe_of

Modified src/topology/category/TopCommRing.lean
- \+ *lemma* coe_of

Modified src/topology/category/UniformSpace.lean
- \+ *lemma* coe_of



## [2020-08-26 11:39:01](https://github.com/leanprover-community/mathlib/commit/206673e)
chore(*): trivial golfing using dec_trivial tactic ([#3949](https://github.com/leanprover-community/mathlib/pull/3949))
#### Estimated changes
Modified src/data/nat/prime.lean


Modified src/data/zsqrtd/gaussian_int.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/ring_theory/multiplicity.lean




## [2020-08-26 10:32:55](https://github.com/leanprover-community/mathlib/commit/dd742dc)
feat(finsupp/basic): add hom_ext ([#3941](https://github.com/leanprover-community/mathlib/pull/3941))
Two R-module homs from finsupp X R which agree on `single x 1` agree everywhere.
```
lemma hom_ext [semiring β] [add_comm_monoid γ] [semimodule β γ] (φ ψ : (α →₀ β) →ₗ[β] γ)
  (h : ∀ a : α, φ (single a 1) = ψ (single a 1)) : φ = ψ
```
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* smul_single_one
- \+ *lemma* hom_ext



## [2020-08-26 09:56:27](https://github.com/leanprover-community/mathlib/commit/a31096d)
fix(set_theory/game): remove stray #lint introduced in [#3939](https://github.com/leanprover-community/mathlib/pull/3939) ([#3948](https://github.com/leanprover-community/mathlib/pull/3948))
#### Estimated changes
Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/nim.lean




## [2020-08-26 00:44:38](https://github.com/leanprover-community/mathlib/commit/da47548)
chore(scripts): update nolints.txt ([#3945](https://github.com/leanprover-community/mathlib/pull/3945))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-25 19:52:43](https://github.com/leanprover-community/mathlib/commit/666a2e2)
feat(algebra/group/with_one): more API for with_zero ([#3716](https://github.com/leanprover-community/mathlib/pull/3716))
#### Estimated changes
Modified src/algebra/group/with_one.lean
- \+ *lemma* some_eq_coe

Modified src/algebra/ordered_group.lean
- \+ *lemma* zero_le
- \+ *lemma* zero_lt_coe
- \+ *lemma* coe_lt_coe
- \+ *lemma* coe_le_coe
- \+ *lemma* mul_le_mul_left
- \+ *lemma* lt_of_mul_lt_mul_left

Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/mean_inequalities.lean


Modified src/topology/instances/ennreal.lean




## [2020-08-25 16:55:18](https://github.com/leanprover-community/mathlib/commit/4478719)
feat(data/padic/padic_integers): homs to zmod(p ^ n) ([#3882](https://github.com/leanprover-community/mathlib/pull/3882))
This is the next PR in a series of PRs on the padic numbers/integers that should culminate in a proof that Z_p is isomorphic to the ring of Witt vectors of zmod p.
In this PR we build ring homs from Z_p to zmod (p ^ n).
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* to_nat_zero_of_neg

Modified src/data/padics/padic_integers.lean
- \+ *lemma* coe_coe_int
- \+ *lemma* coe_int_eq
- \+ *lemma* padic_norm_z_of_int
- \+ *lemma* pow_p_dvd_int_iff
- \+ *lemma* valuation_p_pow_mul
- \+/\- *lemma* maximal_ideal_eq_span_p
- \+ *lemma* norm_int_lt_one_iff_dvd
- \+ *lemma* norm_lt_one_iff_dvd
- \+ *lemma* is_unit_denom
- \+ *lemma* norm_sub_mod_part_aux
- \+ *lemma* mod_part_lt_p
- \+ *lemma* mod_part_nonneg
- \+ *lemma* norm_sub_mod_part
- \+ *lemma* zmod_congr_of_sub_mem_span_aux
- \+ *lemma* zmod_congr_of_sub_mem_span
- \+ *lemma* zmod_congr_of_sub_mem_max_ideal
- \+ *lemma* exists_mem_range
- \+ *lemma* zmod_repr_spec
- \+ *lemma* zmod_repr_lt_p
- \+ *lemma* sub_zmod_repr_mem
- \+ *lemma* to_zmod_spec
- \+ *lemma* ker_to_zmod
- \+ *lemma* appr_lt
- \+ *lemma* appr_spec
- \+ *lemma* ker_to_zmod_pow
- \+ *def* mod_part
- \+ *def* zmod_repr
- \+ *def* to_zmod_hom
- \+ *def* to_zmod
- \+ *def* to_zmod_pow

Modified src/data/padics/padic_norm.lean
- \+ *lemma* dvd_iff_norm_le
- \- *lemma* le_of_dvd

Modified src/data/padics/padic_numbers.lean
- \+ *lemma* norm_int_lt_one_iff_dvd
- \+ *lemma* norm_int_lt_pow_iff_dvd
- \+ *theorem* norm_int_le_one

Modified src/data/zmod/basic.lean
- \+ *lemma* coe_to_nat

Modified src/ring_theory/discrete_valuation_ring.lean
- \+ *lemma* unit_mul_pow_congr_pow
- \+ *lemma* unit_mul_pow_congr_unit



## [2020-08-25 14:36:42](https://github.com/leanprover-community/mathlib/commit/b03ce61)
chore(set_theory/game): various cleanup and code golf ([#3939](https://github.com/leanprover-community/mathlib/pull/3939))
#### Estimated changes
Modified src/set_theory/game/impartial.lean
- \+ *lemma* impartial_not_first_wins
- \+ *lemma* impartial_not_first_loses

Modified src/set_theory/game/nim.lean
- \+/\- *lemma* nim_def
- \+/\- *lemma* nim_zero_first_loses

Modified src/set_theory/game/winner.lean
- \+ *lemma* not_first_wins_of_first_loses
- \+ *lemma* not_first_loses_of_first_wins



## [2020-08-25 14:36:40](https://github.com/leanprover-community/mathlib/commit/878c44f)
feat(category_theory/adjunction): restrict adjunction to full subcategory ([#3924](https://github.com/leanprover-community/mathlib/pull/3924))
Blocked by [#3923](https://github.com/leanprover-community/mathlib/pull/3923).
#### Estimated changes
Modified src/category_theory/adjunction/fully_faithful.lean
- \+ *def* adjunction.restrict_fully_faithful



## [2020-08-25 13:04:30](https://github.com/leanprover-community/mathlib/commit/a5a9858)
feat(data/sigma/basic): cleanup ([#3933](https://github.com/leanprover-community/mathlib/pull/3933))
Use namespaces
Add `sigma.ext_iff`, `psigma.ext` and `sigma.ext_iff`
#### Estimated changes
Modified src/data/pfunctor/multivariate/basic.lean


Modified src/data/sigma/basic.lean
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+/\- *lemma* sigma_mk_injective
- \- *lemma* sigma.ext
- \+ *theorem* mk.inj_iff
- \+ *theorem* eta
- \+ *theorem* «forall»
- \+ *theorem* «exists»
- \+ *theorem* elim_val
- \- *theorem* sigma.mk.inj_iff
- \- *theorem* sigma.eta
- \- *theorem* sigma.forall
- \- *theorem* sigma.exists
- \- *theorem* psigma.elim_val
- \- *theorem* psigma.mk.inj_iff
- \+ *def* map
- \+ *def* elim
- \- *def* sigma.map
- \- *def* psigma.elim
- \- *def* psigma.map



## [2020-08-25 12:10:39](https://github.com/leanprover-community/mathlib/commit/3409388)
doc(ring_theory/*): add some module docstrings ([#3880](https://github.com/leanprover-community/mathlib/pull/3880))
#### Estimated changes
Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/algebra_operations.lean


Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/free_comm_ring.lean
- \+/\- *lemma* coe_lift_hom
- \+/\- *lemma* lift_comp_of
- \+/\- *lemma* lift_hom_comp_of
- \+/\- *def* lift
- \+/\- *def* lift_hom

Modified src/ring_theory/free_ring.lean
- \+/\- *lemma* lift_comp_of
- \+/\- *def* lift
- \+/\- *def* lift_hom

Modified src/ring_theory/integral_closure.lean




## [2020-08-24 23:25:19](https://github.com/leanprover-community/mathlib/commit/d4d33de)
feat(combinatorics): define simple graphs ([#3458](https://github.com/leanprover-community/mathlib/pull/3458))
adds basic definition of `simple_graph`s
#### Estimated changes
Created src/combinatorics/simple_graph.lean
- \+ *lemma* ne_of_adj
- \+ *lemma* mem_edge_set
- \+ *lemma* adj_iff_exists_edge
- \+ *lemma* edge_other_ne
- \+ *lemma* mem_edge_finset
- \+ *lemma* irrefl
- \+ *lemma* edge_symm
- \+ *lemma* mem_neighbor_set
- \+ *lemma* mem_neighbor_finset
- \+ *lemma* card_neighbor_set_eq_degree
- \+ *lemma* neighbor_finset_eq_filter
- \+ *lemma* complete_graph_degree
- \+ *lemma* complete_graph_is_regular
- \+ *def* complete_graph
- \+ *def* neighbor_set
- \+ *def* edge_set
- \+ *def* edge_finset
- \+ *def* neighbor_finset
- \+ *def* degree
- \+ *def* locally_finite
- \+ *def* is_regular_of_degree

Modified src/data/sym2.lean
- \+ *lemma* mk_has_mem_right
- \+/\- *lemma* mem_iff
- \+ *lemma* elems_iff_eq
- \+ *lemma* rel_bool_spec
- \+/\- *def* sym2
- \+ *def* rel_bool



## [2020-08-24 19:17:49](https://github.com/leanprover-community/mathlib/commit/8af1579)
refactor(geometry/euclidean): split up file ([#3926](https://github.com/leanprover-community/mathlib/pull/3926))
Split up `geometry/euclidean.lean` into four smaller files in
`geometry/euclidean`.  There should be no changes to any of the
individual definitions, or to the set of definitions present, but
module doc strings have been expanded.
Various definitions in `geometry/euclidean/basic.lean` are not used by
all the other files, so it would be possible to split it up further,
but that doesn't seem necessary for now, and more of those things may
be used by more other files in future.  (For example,
`geometry/euclidean/circumcenter.lean` doesn't make any use of angles
at present.  But a version of the law of sines involving the
circumradius would naturally go in
`geometry/euclidean/circumcenter.lean`, and would introduce such a
dependency.)
#### Estimated changes
Deleted src/geometry/euclidean.lean
- \- *lemma* cos_angle
- \- *lemma* angle_comm
- \- *lemma* angle_neg_neg
- \- *lemma* angle_nonneg
- \- *lemma* angle_le_pi
- \- *lemma* angle_neg_right
- \- *lemma* angle_neg_left
- \- *lemma* angle_zero_left
- \- *lemma* angle_zero_right
- \- *lemma* angle_self
- \- *lemma* angle_self_neg_of_nonzero
- \- *lemma* angle_neg_self_of_nonzero
- \- *lemma* angle_smul_right_of_pos
- \- *lemma* angle_smul_left_of_pos
- \- *lemma* angle_smul_right_of_neg
- \- *lemma* angle_smul_left_of_neg
- \- *lemma* cos_angle_mul_norm_mul_norm
- \- *lemma* sin_angle_mul_norm_mul_norm
- \- *lemma* angle_eq_zero_iff
- \- *lemma* angle_eq_pi_iff
- \- *lemma* angle_add_angle_eq_pi_of_angle_eq_pi
- \- *lemma* inner_eq_zero_iff_angle_eq_pi_div_two
- \- *lemma* norm_add_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two
- \- *lemma* norm_add_square_eq_norm_square_add_norm_square'
- \- *lemma* norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two
- \- *lemma* norm_sub_square_eq_norm_square_add_norm_square'
- \- *lemma* norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_cos_angle
- \- *lemma* angle_sub_eq_angle_sub_rev_of_norm_eq
- \- *lemma* norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi
- \- *lemma* cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle
- \- *lemma* sin_angle_sub_add_angle_sub_rev_eq_sin_angle
- \- *lemma* cos_angle_add_angle_sub_add_angle_sub_eq_neg_one
- \- *lemma* sin_angle_add_angle_sub_add_angle_sub_eq_zero
- \- *lemma* angle_add_angle_sub_add_angle_sub_eq_pi
- \- *lemma* angle_eq_left
- \- *lemma* angle_eq_right
- \- *lemma* angle_eq_of_ne
- \- *lemma* angle_eq_zero_of_angle_eq_pi_left
- \- *lemma* angle_eq_zero_of_angle_eq_pi_right
- \- *lemma* angle_eq_angle_of_angle_eq_pi
- \- *lemma* dist_square_eq_dist_square_add_dist_square_iff_angle_eq_pi_div_two
- \- *lemma* dist_square_eq_dist_square_add_dist_square_sub_two_mul_dist_mul_dist_mul_cos_angle
- \- *lemma* angle_eq_angle_of_dist_eq
- \- *lemma* dist_eq_of_angle_eq_angle_of_angle_ne_pi
- \- *lemma* angle_add_angle_add_angle_eq_pi
- \- *lemma* inner_weighted_vsub
- \- *lemma* dist_affine_combination
- \- *lemma* inter_eq_singleton_orthogonal_projection_fn
- \- *lemma* is
- \- *lemma* orthogonal_projection_fn_mem
- \- *lemma* orthogonal_projection_fn_mem_orthogonal
- \- *lemma* orthogonal_projection_fn_vsub_mem_direction_orthogonal
- \- *lemma* orthogonal_projection_fn_eq
- \- *lemma* inter_eq_singleton_orthogonal_projection
- \- *lemma* orthogonal_projection_mem
- \- *lemma* orthogonal_projection_mem_orthogonal
- \- *lemma* orthogonal_projection_vsub_mem_direction
- \- *lemma* vsub_orthogonal_projection_mem_direction
- \- *lemma* orthogonal_projection_eq_self_iff
- \- *lemma* dist_orthogonal_projection_eq_zero_iff
- \- *lemma* dist_orthogonal_projection_ne_zero_of_not_mem
- \- *lemma* orthogonal_projection_vsub_mem_direction_orthogonal
- \- *lemma* vsub_orthogonal_projection_mem_direction_orthogonal
- \- *lemma* orthogonal_projection_vadd_eq_self
- \- *lemma* orthogonal_projection_vadd_smul_vsub_orthogonal_projection
- \- *lemma* dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
- \- *lemma* dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd
- \- *lemma* dist_eq_iff_dist_orthogonal_projection_eq
- \- *lemma* dist_set_eq_iff_dist_orthogonal_projection_eq
- \- *lemma* exists_dist_eq_iff_exists_dist_orthogonal_projection_eq
- \- *lemma* exists_unique_dist_eq_of_insert
- \- *lemma* exists_unique_dist_eq_of_affine_independent
- \- *lemma* circumcenter_circumradius_unique_dist_eq
- \- *lemma* circumcenter_mem_affine_span
- \- *lemma* dist_circumcenter_eq_circumradius
- \- *lemma* dist_circumcenter_eq_circumradius'
- \- *lemma* eq_circumcenter_of_dist_eq
- \- *lemma* eq_circumradius_of_dist_eq
- \- *lemma* sum_points_with_circumcenter
- \- *lemma* points_with_circumcenter_point
- \- *lemma* points_with_circumcenter_eq_circumcenter
- \- *lemma* sum_point_weights_with_circumcenter
- \- *lemma* point_eq_affine_combination_of_points_with_circumcenter
- \- *lemma* sum_centroid_weights_with_circumcenter
- \- *lemma* centroid_eq_affine_combination_of_points_with_circumcenter
- \- *lemma* sum_circumcenter_weights_with_circumcenter
- \- *lemma* circumcenter_eq_affine_combination_of_points_with_circumcenter
- \- *lemma* monge_point_eq_smul_vsub_vadd_circumcenter
- \- *lemma* monge_point_mem_affine_span
- \- *lemma* sum_monge_point_weights_with_circumcenter
- \- *lemma* monge_point_eq_affine_combination_of_points_with_circumcenter
- \- *lemma* monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub
- \- *lemma* sum_monge_point_vsub_face_centroid_weights_with_circumcenter
- \- *lemma* monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter
- \- *lemma* inner_monge_point_vsub_face_centroid_vsub
- \- *lemma* monge_plane_def
- \- *lemma* monge_plane_comm
- \- *lemma* monge_point_mem_monge_plane
- \- *lemma* direction_monge_plane
- \- *lemma* eq_monge_point_of_forall_mem_monge_plane
- \- *lemma* altitude_def
- \- *lemma* orthocenter_eq_monge_point
- \- *lemma* orthocenter_eq_smul_vsub_vadd_circumcenter
- \- *lemma* orthocenter_mem_affine_span
- \- *lemma* altitude_eq_monge_plane
- \- *lemma* orthocenter_mem_altitude
- \- *lemma* eq_orthocenter_of_forall_mem_altitude
- \- *def* angle
- \- *def* orthogonal_projection_fn
- \- *def* orthogonal_projection
- \- *def* circumcenter_circumradius
- \- *def* circumcenter
- \- *def* circumradius
- \- *def* point_index_embedding
- \- *def* points_with_circumcenter
- \- *def* point_weights_with_circumcenter
- \- *def* centroid_weights_with_circumcenter
- \- *def* circumcenter_weights_with_circumcenter
- \- *def* monge_point
- \- *def* monge_point_weights_with_circumcenter
- \- *def* monge_point_vsub_face_centroid_weights_with_circumcenter
- \- *def* monge_plane
- \- *def* altitude
- \- *def* orthocenter

Created src/geometry/euclidean/basic.lean
- \+ *lemma* cos_angle
- \+ *lemma* angle_comm
- \+ *lemma* angle_neg_neg
- \+ *lemma* angle_nonneg
- \+ *lemma* angle_le_pi
- \+ *lemma* angle_neg_right
- \+ *lemma* angle_neg_left
- \+ *lemma* angle_zero_left
- \+ *lemma* angle_zero_right
- \+ *lemma* angle_self
- \+ *lemma* angle_self_neg_of_nonzero
- \+ *lemma* angle_neg_self_of_nonzero
- \+ *lemma* angle_smul_right_of_pos
- \+ *lemma* angle_smul_left_of_pos
- \+ *lemma* angle_smul_right_of_neg
- \+ *lemma* angle_smul_left_of_neg
- \+ *lemma* cos_angle_mul_norm_mul_norm
- \+ *lemma* sin_angle_mul_norm_mul_norm
- \+ *lemma* angle_eq_zero_iff
- \+ *lemma* angle_eq_pi_iff
- \+ *lemma* angle_add_angle_eq_pi_of_angle_eq_pi
- \+ *lemma* inner_eq_zero_iff_angle_eq_pi_div_two
- \+ *lemma* angle_eq_left
- \+ *lemma* angle_eq_right
- \+ *lemma* angle_eq_of_ne
- \+ *lemma* angle_eq_zero_of_angle_eq_pi_left
- \+ *lemma* angle_eq_zero_of_angle_eq_pi_right
- \+ *lemma* angle_eq_angle_of_angle_eq_pi
- \+ *lemma* inner_weighted_vsub
- \+ *lemma* dist_affine_combination
- \+ *lemma* inter_eq_singleton_orthogonal_projection_fn
- \+ *lemma* is
- \+ *lemma* orthogonal_projection_fn_mem
- \+ *lemma* orthogonal_projection_fn_mem_orthogonal
- \+ *lemma* orthogonal_projection_fn_vsub_mem_direction_orthogonal
- \+ *lemma* orthogonal_projection_fn_eq
- \+ *lemma* inter_eq_singleton_orthogonal_projection
- \+ *lemma* orthogonal_projection_mem
- \+ *lemma* orthogonal_projection_mem_orthogonal
- \+ *lemma* orthogonal_projection_vsub_mem_direction
- \+ *lemma* vsub_orthogonal_projection_mem_direction
- \+ *lemma* orthogonal_projection_eq_self_iff
- \+ *lemma* dist_orthogonal_projection_eq_zero_iff
- \+ *lemma* dist_orthogonal_projection_ne_zero_of_not_mem
- \+ *lemma* orthogonal_projection_vsub_mem_direction_orthogonal
- \+ *lemma* vsub_orthogonal_projection_mem_direction_orthogonal
- \+ *lemma* orthogonal_projection_vadd_eq_self
- \+ *lemma* orthogonal_projection_vadd_smul_vsub_orthogonal_projection
- \+ *lemma* dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
- \+ *lemma* dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd
- \+ *def* angle
- \+ *def* orthogonal_projection_fn
- \+ *def* orthogonal_projection

Created src/geometry/euclidean/circumcenter.lean
- \+ *lemma* dist_eq_iff_dist_orthogonal_projection_eq
- \+ *lemma* dist_set_eq_iff_dist_orthogonal_projection_eq
- \+ *lemma* exists_dist_eq_iff_exists_dist_orthogonal_projection_eq
- \+ *lemma* exists_unique_dist_eq_of_insert
- \+ *lemma* exists_unique_dist_eq_of_affine_independent
- \+ *lemma* circumcenter_circumradius_unique_dist_eq
- \+ *lemma* circumcenter_mem_affine_span
- \+ *lemma* dist_circumcenter_eq_circumradius
- \+ *lemma* dist_circumcenter_eq_circumradius'
- \+ *lemma* eq_circumcenter_of_dist_eq
- \+ *lemma* eq_circumradius_of_dist_eq
- \+ *lemma* sum_points_with_circumcenter
- \+ *lemma* points_with_circumcenter_point
- \+ *lemma* points_with_circumcenter_eq_circumcenter
- \+ *lemma* sum_point_weights_with_circumcenter
- \+ *lemma* point_eq_affine_combination_of_points_with_circumcenter
- \+ *lemma* sum_centroid_weights_with_circumcenter
- \+ *lemma* centroid_eq_affine_combination_of_points_with_circumcenter
- \+ *lemma* sum_circumcenter_weights_with_circumcenter
- \+ *lemma* circumcenter_eq_affine_combination_of_points_with_circumcenter
- \+ *def* circumcenter_circumradius
- \+ *def* circumcenter
- \+ *def* circumradius
- \+ *def* point_index_embedding
- \+ *def* points_with_circumcenter
- \+ *def* point_weights_with_circumcenter
- \+ *def* centroid_weights_with_circumcenter
- \+ *def* circumcenter_weights_with_circumcenter

Created src/geometry/euclidean/default.lean


Created src/geometry/euclidean/monge_point.lean
- \+ *lemma* monge_point_eq_smul_vsub_vadd_circumcenter
- \+ *lemma* monge_point_mem_affine_span
- \+ *lemma* sum_monge_point_weights_with_circumcenter
- \+ *lemma* monge_point_eq_affine_combination_of_points_with_circumcenter
- \+ *lemma* monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub
- \+ *lemma* sum_monge_point_vsub_face_centroid_weights_with_circumcenter
- \+ *lemma* monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter
- \+ *lemma* inner_monge_point_vsub_face_centroid_vsub
- \+ *lemma* monge_plane_def
- \+ *lemma* monge_plane_comm
- \+ *lemma* monge_point_mem_monge_plane
- \+ *lemma* direction_monge_plane
- \+ *lemma* eq_monge_point_of_forall_mem_monge_plane
- \+ *lemma* altitude_def
- \+ *lemma* orthocenter_eq_monge_point
- \+ *lemma* orthocenter_eq_smul_vsub_vadd_circumcenter
- \+ *lemma* orthocenter_mem_affine_span
- \+ *lemma* altitude_eq_monge_plane
- \+ *lemma* orthocenter_mem_altitude
- \+ *lemma* eq_orthocenter_of_forall_mem_altitude
- \+ *def* monge_point
- \+ *def* monge_point_weights_with_circumcenter
- \+ *def* monge_point_vsub_face_centroid_weights_with_circumcenter
- \+ *def* monge_plane
- \+ *def* altitude
- \+ *def* orthocenter

Created src/geometry/euclidean/triangle.lean
- \+ *lemma* norm_add_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two
- \+ *lemma* norm_add_square_eq_norm_square_add_norm_square'
- \+ *lemma* norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two
- \+ *lemma* norm_sub_square_eq_norm_square_add_norm_square'
- \+ *lemma* norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_cos_angle
- \+ *lemma* angle_sub_eq_angle_sub_rev_of_norm_eq
- \+ *lemma* norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi
- \+ *lemma* cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle
- \+ *lemma* sin_angle_sub_add_angle_sub_rev_eq_sin_angle
- \+ *lemma* cos_angle_add_angle_sub_add_angle_sub_eq_neg_one
- \+ *lemma* sin_angle_add_angle_sub_add_angle_sub_eq_zero
- \+ *lemma* angle_add_angle_sub_add_angle_sub_eq_pi
- \+ *lemma* dist_square_eq_dist_square_add_dist_square_iff_angle_eq_pi_div_two
- \+ *lemma* dist_square_eq_dist_square_add_dist_square_sub_two_mul_dist_mul_dist_mul_cos_angle
- \+ *lemma* angle_eq_angle_of_dist_eq
- \+ *lemma* dist_eq_of_angle_eq_angle_of_angle_ne_pi
- \+ *lemma* angle_add_angle_add_angle_eq_pi



## [2020-08-24 16:57:27](https://github.com/leanprover-community/mathlib/commit/1404ad8)
feat(algebra/add_torsor): vsub_vadd_comm ([#3928](https://github.com/leanprover-community/mathlib/pull/3928))
Add another (commutative) `add_torsor` rearrangement lemma.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* vsub_vadd_comm



## [2020-08-24 16:23:09](https://github.com/leanprover-community/mathlib/commit/96b559c)
feat(set_theory/game): grundy number of single-heap nim ([#3930](https://github.com/leanprover-community/mathlib/pull/3930))
#### Estimated changes
Modified src/set_theory/game/nim.lean
- \+ *lemma* nim_equiv_iff_eq
- \+ *lemma* equiv_nim_iff_Grundy_value_eq
- \+ *lemma* Grundy_value_nim



## [2020-08-24 01:55:42](https://github.com/leanprover-community/mathlib/commit/1ccdbb9)
feat(category_theory/images): unique image ([#3921](https://github.com/leanprover-community/mathlib/pull/3921))
Show that the strong-epi mono factorisation of a morphism is unique.
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* image.iso_strong_epi_mono_hom_comp_ι
- \+ *lemma* image.iso_strong_epi_mono_inv_comp_mono
- \+ *def* image.iso_strong_epi_mono



## [2020-08-24 01:55:40](https://github.com/leanprover-community/mathlib/commit/685d9dd)
feat(category_theory): cancel fully faithful functor ([#3920](https://github.com/leanprover-community/mathlib/pull/3920))
Construct the natural isomorphism between `F` and `G` given a natural iso between `F ⋙ H` and `G ⋙ H` for a fully faithful `H`.
#### Estimated changes
Modified src/category_theory/fully_faithful.lean
- \+ *lemma* fully_faithful_cancel_right_hom_app
- \+ *lemma* fully_faithful_cancel_right_inv_app
- \+ *def* fully_faithful_cancel_right



## [2020-08-24 01:00:11](https://github.com/leanprover-community/mathlib/commit/ebd3351)
chore(category_theory/conj): add a new simp lemma ([#3922](https://github.com/leanprover-community/mathlib/pull/3922))
Mark a new simp lemma which I think is helpful and simplify some proofs using it.
#### Estimated changes
Modified src/category_theory/conj.lean




## [2020-08-24 01:00:09](https://github.com/leanprover-community/mathlib/commit/f230409)
feat(category_theory/adjunction): opposite adjunctions ([#3899](https://github.com/leanprover-community/mathlib/pull/3899))
Add two constructions for adjoints for opposite functors.
#### Estimated changes
Created src/category_theory/adjunction/opposites.lean
- \+ *def* adjoint_of_op_adjoint_op
- \+ *def* adjoint_unop_of_adjoint_op
- \+ *def* unop_adjoint_of_op_adjoint
- \+ *def* unop_adjoint_unop_of_adjoint
- \+ *def* op_adjoint_op_of_adjoint
- \+ *def* adjoint_op_of_adjoint_unop
- \+ *def* op_adjoint_of_unop_adjoint
- \+ *def* adjoint_of_unop_adjoint_unop

Modified src/category_theory/opposites.lean
- \+ *lemma* op_equiv_apply
- \+ *lemma* op_equiv_symm_apply
- \+ *def* op_equiv'
- \+ *def* op_equiv''
- \+ *def* op_equiv'''
- \+ *def* op_equiv



## [2020-08-24 01:00:07](https://github.com/leanprover-community/mathlib/commit/bfc8c66)
feat(category_theory/limits/shapes/finite*): finite limits from limits ([#3800](https://github.com/leanprover-community/mathlib/pull/3800))
Add some missing derivations in the new has_limits hierarchy
#### Estimated changes
Modified src/category_theory/limits/shapes/finite_limits.lean
- \+ *def* has_finite_limits_of_has_limits
- \+ *def* has_finite_colimits_of_has_colimits

Modified src/category_theory/limits/shapes/finite_products.lean
- \+ *def* has_finite_products_of_has_finite_limits
- \+ *def* has_finite_coproducts_of_has_finite_colimits



## [2020-08-23 23:56:34](https://github.com/leanprover-community/mathlib/commit/bf6cd28)
feat(category_theory/fully_faithful): equivalence of homsets ([#3923](https://github.com/leanprover-community/mathlib/pull/3923))
I was *so sure* I'd already made this PR but I can't find it nor this construction, so here it is.
#### Estimated changes
Modified src/category_theory/fully_faithful.lean
- \+ *lemma* equiv_of_fully_faithful_apply
- \+ *lemma* equiv_of_fully_faithful_symm_apply
- \+ *def* equiv_of_fully_faithful



## [2020-08-23 16:22:06](https://github.com/leanprover-community/mathlib/commit/7d4f773)
feat(ring_theory/jacobson): Proof that if a ring is a Jacobson Ring then so is its localization at a single element ([#3651](https://github.com/leanprover-community/mathlib/pull/3651))
The main result here is that the localization of a Jacobson ring to a single element is also a Jacobson ring, which is one of the things needed for the proof that `R` is Jacobson if and only if `R[x]` is Jacobson.
Two characterization of Jacobson rings in terms of their quotient rings are also included, again needed to prove `R[x]` is Jacobson.
#### Estimated changes
Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* mem_closure_singleton_self

Modified src/linear_algebra/basic.lean
- \+ *lemma* mk_surjective

Modified src/order/complete_lattice.lean
- \+ *theorem* Sup_le_Sup_of_subset_instert_bot
- \+ *theorem* Inf_le_Inf_of_subset_insert_top

Modified src/ring_theory/ideal/basic.lean
- \+ *theorem* unit_mul_mem_iff_mem
- \+ *theorem* mul_unit_mem_iff_mem

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* comap_Inf'
- \+ *lemma* ker_eq_comap_bot
- \+ *lemma* mk_ker
- \+ *theorem* comap_is_prime
- \+ *theorem* comap_is_maximal_of_surjective
- \+ *theorem* map_is_prime_of_surjective
- \+ *theorem* map_radical_of_surjective
- \- *theorem* comap.is_maximal

Modified src/ring_theory/jacobson.lean
- \+ *lemma* is_jacobson_iff_Inf_maximal'
- \+ *lemma* disjoint_closure_singleton_iff_not_mem
- \+ *lemma* is_maximal_iff_is_maximal_disjoint
- \+ *lemma* is_maximal_of_is_maximal_disjoint
- \+ *lemma* is_jacobson_localization
- \+ *def* order_iso_of_maximal

Modified src/ring_theory/jacobson_ideal.lean
- \+ *lemma* radical_le_jacobson
- \+ *lemma* eq_radical_of_eq_jacobson
- \+ *lemma* jacobson_eq_self_of_is_maximal
- \+ *lemma* eq_jacobson_iff_not_mem
- \- *lemma* jacobson.is_maximal
- \+ *theorem* eq_jacobson_iff_Inf_maximal
- \+ *theorem* eq_jacobson_iff_Inf_maximal'
- \+ *theorem* map_jacobson_of_surjective
- \+ *theorem* comap_jacobson_of_surjective
- \+ *theorem* jacobson_eq_iff_jacobson_quotient_eq_bot
- \+ *theorem* radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot

Modified src/ring_theory/localization.lean
- \+ *lemma* mk'_mem_iff
- \+ *lemma* is_prime_iff_is_prime_disjoint
- \+ *lemma* is_prime_of_is_prime_disjoint
- \+ *theorem* mem_map_to_map_iff
- \+ *theorem* comap_map_of_is_prime_disjoint
- \+ *def* order_iso_of_prime



## [2020-08-23 15:35:50](https://github.com/leanprover-community/mathlib/commit/e216755)
feat(linear_algebra/affine_space): more lemmas ([#3918](https://github.com/leanprover-community/mathlib/pull/3918))
Add some more affine space lemmas.  In particular, this includes
lemmas about the dimension of the span of a finite affinely
independent family.
#### Estimated changes
Modified src/linear_algebra/affine_space/basic.lean
- \+ *lemma* direction_eq_top_iff_of_nonempty

Modified src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* findim_vector_span_of_affine_independent
- \+ *lemma* vector_span_eq_top_of_affine_independent_of_card_eq_findim_add_one
- \+ *lemma* affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* injective_of_affine_independent
- \+ *lemma* affine_independent_set_of_affine_independent



## [2020-08-23 14:51:36](https://github.com/leanprover-community/mathlib/commit/d80f3ef)
feat(geometry/euclidean): Monge point and orthocenter ([#3872](https://github.com/leanprover-community/mathlib/pull/3872))
The main purpose of this PR is to define the orthocenter of a
triangle.
Simplices in more than two dimensions do not in general have an
orthocenter: the altitudes are not necessarily concurrent.  However,
there is a n-dimensional generalization of the orthocenter in the form
of the Monge point of a simplex.  Define a Monge plane to be an
(n-1)-dimensional subspace that passes through the centroid of an
(n-2)-dimensional face of the simplex and is orthogonal to the
opposite edge.  Then the Monge planes of a simplex are always
concurrent, and their point of concurrence is known as the Monge point
of the simplex.  Furthermore, the circumcenter O, centroid G and Monge
point M are collinear in that order on the Euler line, with OG : GM =
(n-1) : 2.
Here, we use that ratio as a convenient way to define the Monge point
in terms of the existing definitions of the circumcenter and the
centroid.  First we set up some infrastructure for dealing with affine
combinations of the vertices of a simplex together with its
circumcenter, which can be convenient for computations rather than
dealing with combinations of the vertices alone; the use of an
inductive type `points_with_circumcenter_index` seemed to be more
convenient than other options for how to index such combinations.
Then, a straightforward calculation using `inner_weighted_vsub` shows
that the point defined in terms of the circumcenter and the centroid
does indeed lie in the Monge planes, so justifying the definition as
being a definition of the Monge point.  It is then shown to be the
only point in that intersection (in fact, the only point in the
intersection of all the Monge planes where one of the two vertices
needed to specify a Monge plane is fixed).
The altitudes of a simplex are then defined.  In the case of a
triangle, the orthocenter is defined to be the Monge point, the
altitudes are shown to equal the Monge planes (mathematically trivial,
but involves quite a bit of fiddling around with `fin 3`) and thus the
orthocenter is shown to lie in the altitudes and to be the unique
point lying in any two of them (again, involves various fiddling
around with `fin 3` to link up with the previous lemmas).  Because of
the definition chosen for the Monge point, the position of the
orthocenter on the Euler line of the triangle comes for free (not
quite `rfl`, but two rewrites of `rfl` lemmas plus `norm_num`).
#### Estimated changes
Modified src/geometry/euclidean.lean
- \+ *lemma* sum_points_with_circumcenter
- \+ *lemma* points_with_circumcenter_point
- \+ *lemma* points_with_circumcenter_eq_circumcenter
- \+ *lemma* sum_point_weights_with_circumcenter
- \+ *lemma* point_eq_affine_combination_of_points_with_circumcenter
- \+ *lemma* sum_centroid_weights_with_circumcenter
- \+ *lemma* centroid_eq_affine_combination_of_points_with_circumcenter
- \+ *lemma* sum_circumcenter_weights_with_circumcenter
- \+ *lemma* circumcenter_eq_affine_combination_of_points_with_circumcenter
- \+ *lemma* monge_point_eq_smul_vsub_vadd_circumcenter
- \+ *lemma* monge_point_mem_affine_span
- \+ *lemma* sum_monge_point_weights_with_circumcenter
- \+ *lemma* monge_point_eq_affine_combination_of_points_with_circumcenter
- \+ *lemma* monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub
- \+ *lemma* sum_monge_point_vsub_face_centroid_weights_with_circumcenter
- \+ *lemma* monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter
- \+ *lemma* inner_monge_point_vsub_face_centroid_vsub
- \+ *lemma* monge_plane_def
- \+ *lemma* monge_plane_comm
- \+ *lemma* monge_point_mem_monge_plane
- \+ *lemma* direction_monge_plane
- \+ *lemma* eq_monge_point_of_forall_mem_monge_plane
- \+ *lemma* altitude_def
- \+ *lemma* orthocenter_eq_monge_point
- \+ *lemma* orthocenter_eq_smul_vsub_vadd_circumcenter
- \+ *lemma* orthocenter_mem_affine_span
- \+ *lemma* altitude_eq_monge_plane
- \+ *lemma* orthocenter_mem_altitude
- \+ *lemma* eq_orthocenter_of_forall_mem_altitude
- \+ *def* point_index_embedding
- \+ *def* points_with_circumcenter
- \+ *def* point_weights_with_circumcenter
- \+ *def* centroid_weights_with_circumcenter
- \+ *def* circumcenter_weights_with_circumcenter
- \+ *def* monge_point
- \+ *def* monge_point_weights_with_circumcenter
- \+ *def* monge_point_vsub_face_centroid_weights_with_circumcenter
- \+ *def* monge_plane
- \+ *def* altitude
- \+ *def* orthocenter



## [2020-08-23 13:21:25](https://github.com/leanprover-community/mathlib/commit/588e46c)
feat(tactic/*,meta/expr): refactor and extend binder matching functions ([#3830](https://github.com/leanprover-community/mathlib/pull/3830))
This PR deals with meta functions that deconstruct expressions starting
with pi or lambda binders. Core defines `mk_local_pis` to deconstruct pi
binders and `tactic.core` used to contain some ad-hoc variations of its
functionality. This PR unifies all these variations and adds several
more, for both pi and lambda binders. Specifically:
- We remove `mk_local_pis_whnf`. Use `whnf e md >>= mk_local_pis` instead.
  Note: we reuse the name for another function with different semantics;
  see below.
- We add `mk_{meta,local}_{pis,lambdas}`, `mk_{meta,local}_{pis,lambdas}n`,
  `mk_{meta,local}_{pis,lambdas}_whnf`, `mk_{meta,local}_{pis,lambdas}n_whnf`.
  These can all be used to 'open' a pi or lambda binder. The binder is
  instantiated with a fresh local for the `local` variants and a fresh
  metavariable for the `meta` variants. The `whnf` variants normalise
  the input expression before checking for leading binders. The
  `{pis,lambdas}n` variants match a given number of leading binders.
  Some of these functions were already defined, but we now implement
  them in terms of a new function, `mk_binders`, which abstracts over
  the common functionality.
- We rename `get_pi_binders_dep` to `get_pi_binders_nondep`. This function returns
  the nondependent binders, so the old name was misleading.
- We add `expr.match_<C>` for every constructor `C` of `expr`. `match_pi`
  and `match_lam` are needed to implement the `mk_*` functions; the
  other functions are added for completeness.
- (Bonus) We add `get_app_fn_args_whnf` and `get_app_fn_whnf`. These are variants
  of `get_app_fn_args` and `get_app_fn`, respectively, which normalise the input
  expression as necessary.
The refactoring might be a slight performance regression because the new
implementation adds some indirection. But the affected functions aren't
widely used anyway and I suspect that the performance loss is very
minor, so having clearer and more concise code is probably worth it.
#### Estimated changes
Modified src/control/traversable/derive.lean


Modified src/meta/coinductive_predicates.lean


Modified src/meta/expr.lean


Created src/tactic/binder_matching.lean


Modified src/tactic/choose.lean


Modified src/tactic/core.lean


Modified src/tactic/ext.lean


Modified src/tactic/lift.lean


Modified src/tactic/lint/simp.lean


Modified src/tactic/lint/type_classes.lean


Modified src/tactic/mk_iff_of_inductive_prop.lean


Modified src/tactic/monotonicity/basic.lean


Modified src/tactic/norm_cast.lean


Modified src/tactic/reassoc_axiom.lean


Modified src/tactic/simps.lean




## [2020-08-23 12:27:41](https://github.com/leanprover-community/mathlib/commit/ffd8626)
refactor(linear_algebra/affine_space/basic): make more arguments of smul_vsub_vadd_mem implicit ([#3917](https://github.com/leanprover-community/mathlib/pull/3917))
Came up in [#3872](https://github.com/leanprover-community/mathlib/pull/3872).
#### Estimated changes
Modified src/linear_algebra/affine_space/basic.lean




## [2020-08-23 06:36:27](https://github.com/leanprover-community/mathlib/commit/7d88a30)
fix(data/sigma/basic): rename `ext` to `sigma.ext` ([#3916](https://github.com/leanprover-community/mathlib/pull/3916))
#### Estimated changes
Modified src/data/sigma/basic.lean
- \+ *lemma* sigma.ext
- \- *lemma* ext



## [2020-08-23 05:18:43](https://github.com/leanprover-community/mathlib/commit/ff97055)
feat(data/finset/basic): insert_singleton_comm ([#3914](https://github.com/leanprover-community/mathlib/pull/3914))
Add the result that `({a, b} : finset α) = {b, a}`.  This came up in
[#3872](https://github.com/leanprover-community/mathlib/pull/3872), and `library_search` does not show it as already present.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* insert_singleton_comm



## [2020-08-23 02:34:47](https://github.com/leanprover-community/mathlib/commit/7ac7246)
feat(linear_algebra/finite_dimensional): Add `linear_equiv.of_inj_endo` and related lemmas ([#3878](https://github.com/leanprover-community/mathlib/pull/3878))
This PR prepares [#3864](https://github.com/leanprover-community/mathlib/pull/3864).
* Move the section `zero_dim` up.
* Add several lemmas about finite dimensional vector spaces. The only new definition is `linear_equiv.of_injective_endo`, which produces a linear equivalence from an injective endomorphism.
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *lemma* linear_independent_le_dim

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* lt_omega_of_linear_independent
- \+/\- *lemma* finite_dimensional_of_dim_eq_zero
- \+/\- *lemma* findim_eq_zero_of_dim_eq_zero
- \+/\- *lemma* finite_dimensional_bot
- \+/\- *lemma* findim_bot
- \+/\- *lemma* bot_eq_top_of_dim_eq_zero
- \+ *lemma* eq_top_of_disjoint
- \+ *lemma* of_injective_endo_to_fun
- \+ *lemma* of_injective_endo_right_inv
- \+ *lemma* of_injective_endo_left_inv
- \+ *lemma* is_unit_iff
- \+/\- *theorem* dim_eq_zero
- \+/\- *theorem* findim_eq_zero



## [2020-08-22 18:09:38](https://github.com/leanprover-community/mathlib/commit/abe4459)
feat(analysis/convex): define concavity of functions ([#3849](https://github.com/leanprover-community/mathlib/pull/3849))
#### Estimated changes
Modified src/algebra/module/ordered.lean


Modified src/algebra/ordered_group.lean


Modified src/analysis/convex/basic.lean
- \+ *lemma* neg_convex_on_iff
- \+ *lemma* neg_concave_on_iff
- \+ *lemma* concave_on_id
- \+ *lemma* concave_on_const
- \+ *lemma* concave_on_iff_div
- \+ *lemma* linear_order.concave_on_of_lt
- \+ *lemma* concave_on_real_of_slope_mono_adjacent
- \+ *lemma* concave_on.subset
- \+ *lemma* concave_on.add
- \+ *lemma* concave_on.smul
- \+/\- *lemma* convex_on.le_on_segment'
- \+ *lemma* concave_on.le_on_segment'
- \+/\- *lemma* convex_on.le_on_segment
- \+ *lemma* concave_on.le_on_segment
- \+ *lemma* concave_on.concave_le
- \+ *lemma* concave_on.convex_lt
- \+ *lemma* concave_on.convex_hypograph
- \+ *lemma* concave_on_iff_convex_hypograph
- \+ *lemma* concave_on.comp_affine_map
- \+ *lemma* concave_on.comp_linear_map
- \+ *lemma* concave_on.translate_right
- \+ *lemma* concave_on.translate_left
- \+ *def* concave_on

Modified src/analysis/convex/extrema.lean
- \+/\- *lemma* is_min_on.of_is_local_min_on_of_convex_on_Icc
- \+/\- *lemma* is_min_on.of_is_local_min_on_of_convex_on
- \+ *lemma* is_max_on.of_is_local_max_on_of_concave_on
- \+/\- *lemma* is_min_on.of_is_local_min_of_convex_univ
- \+ *lemma* is_max_on.of_is_local_max_of_convex_univ



## [2020-08-22 15:14:00](https://github.com/leanprover-community/mathlib/commit/9e9b380)
doc(algebra/linear_recurrence): fix a mistake in module docstring ([#3911](https://github.com/leanprover-community/mathlib/pull/3911))
#### Estimated changes
Modified src/algebra/linear_recurrence.lean




## [2020-08-22 15:13:58](https://github.com/leanprover-community/mathlib/commit/65ceb00)
fix(topology): simplify proof of Heine-Cantor ([#3910](https://github.com/leanprover-community/mathlib/pull/3910))
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+ *theorem* bsupr_le_supr
- \+ *theorem* infi_le_binfi

Modified src/topology/uniform_space/compact_separated.lean




## [2020-08-22 14:33:36](https://github.com/leanprover-community/mathlib/commit/6a85278)
feat(data/polynomial/eval): eval_finset.prod ([#3903](https://github.com/leanprover-community/mathlib/pull/3903))
Evaluating commutes with finset.prod; useful in a variety of situations in numerical analysis.
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* eval_prod



## [2020-08-22 13:26:57](https://github.com/leanprover-community/mathlib/commit/aca785a)
feat(linear_algebra): linear_equiv_matrix lemmas ([#3898](https://github.com/leanprover-community/mathlib/pull/3898))
From the sphere eversion project, with help by Anne for the crucial `linear_equiv_matrix_apply`.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+/\- *lemma* id_apply
- \+ *lemma* id_coe
- \+ *lemma* comp_coe

Modified src/linear_algebra/matrix.lean
- \+ *lemma* linear_equiv_matrix_apply
- \+ *lemma* linear_equiv_matrix_apply'
- \+ *lemma* linear_equiv_matrix_id
- \+ *lemma* linear_equiv_matrix_symm_one
- \+/\- *lemma* linear_equiv_matrix_comp
- \+/\- *lemma* linear_equiv_matrix_mul
- \+ *lemma* linear_equiv_matrix_symm_mul
- \+ *lemma* linear_equiv.is_unit_det
- \+/\- *theorem* linear_equiv_matrix_range
- \+/\- *def* linear_equiv_matrix
- \+ *def* linear_equiv.of_is_unit_det



## [2020-08-22 12:32:20](https://github.com/leanprover-community/mathlib/commit/e9d1067)
feat(category_theory/opposites): isomorphism of opposite functor ([#3901](https://github.com/leanprover-community/mathlib/pull/3901))
Get some lemmas generated by `simps` and add two isomorphisms for opposite functors.
#### Estimated changes
Modified src/category_theory/opposites.lean
- \- *lemma* op_obj
- \- *lemma* op_map
- \- *lemma* unop_obj
- \- *lemma* unop_map
- \- *lemma* op_hom.obj
- \- *lemma* op_hom.map_app
- \- *lemma* op_inv.obj
- \- *lemma* op_inv.map_app
- \- *lemma* left_op_obj
- \- *lemma* left_op_map
- \- *lemma* right_op_obj
- \- *lemma* right_op_map
- \+ *def* op_unop_iso
- \+ *def* unop_op_iso



## [2020-08-22 10:07:23](https://github.com/leanprover-community/mathlib/commit/011a262)
feat(set_theory/game): impartial games and the Sprague-Grundy theorem ([#3855](https://github.com/leanprover-community/mathlib/pull/3855))
#### Estimated changes
Created src/set_theory/game/impartial.lean
- \+ *lemma* zero_impartial
- \+ *lemma* impartial_def
- \+ *lemma* impartial_neg_equiv_self
- \+ *lemma* impartial_move_left_impartial
- \+ *lemma* impartial_move_right_impartial
- \+ *lemma* impartial_add
- \+ *lemma* impartial_neg
- \+ *lemma* impartial_winner_cases
- \+ *lemma* impartial_add_self
- \+ *lemma* equiv_iff_sum_first_loses
- \+ *lemma* impartial_first_loses_symm
- \+ *lemma* impartial_first_wins_symm
- \+ *lemma* impartial_first_loses_symm'
- \+ *lemma* impartial_first_wins_symm'
- \+ *lemma* no_good_left_moves_iff_first_loses
- \+ *lemma* no_good_right_moves_iff_first_loses
- \+ *lemma* good_left_move_iff_first_wins
- \+ *lemma* good_right_move_iff_first_wins
- \+ *def* impartial

Created src/set_theory/game/nim.lean
- \+ *lemma* nim_def
- \+ *lemma* nim_wf_lemma
- \+ *lemma* nim_impartial
- \+ *lemma* nim_zero_first_loses
- \+ *lemma* nim_non_zero_first_wins
- \+ *lemma* nim_sum_first_loses_iff_eq
- \+ *lemma* nim_sum_first_wins_iff_neq
- \+ *lemma* nonmoves_nonempty
- \+ *lemma* Grundy_value_def
- \+ *theorem* ordinal.type_out'
- \+ *theorem* Sprague_Grundy
- \+ *def* ordinal.out
- \+ *def* nim
- \+ *def* nonmoves

Created src/set_theory/game/winner.lean
- \+ *lemma* winner_cases
- \+ *lemma* first_loses_is_zero
- \+ *lemma* first_loses_of_equiv
- \+ *lemma* first_wins_of_equiv
- \+ *lemma* left_wins_of_equiv
- \+ *lemma* right_wins_of_equiv
- \+ *lemma* first_loses_of_equiv_iff
- \+ *lemma* first_wins_of_equiv_iff
- \+ *lemma* left_wins_of_equiv_iff
- \+ *lemma* right_wins_of_equiv_iff
- \+ *theorem* zero_first_loses
- \+ *theorem* one_left_wins
- \+ *theorem* star_first_wins
- \+ *theorem* omega_left_wins
- \+ *def* first_loses
- \+ *def* first_wins
- \+ *def* left_wins
- \+ *def* right_wins

Modified src/set_theory/pgame.lean




## [2020-08-22 09:35:08](https://github.com/leanprover-community/mathlib/commit/e546e94)
fix(data/equiv/transfer_instance): remove stray #lint ([#3908](https://github.com/leanprover-community/mathlib/pull/3908))
#### Estimated changes
Modified src/data/equiv/transfer_instance.lean




## [2020-08-22 06:31:00](https://github.com/leanprover-community/mathlib/commit/13881d7)
feat(tactic/dec_trivial): make dec_trivial easier to use ([#3875](https://github.com/leanprover-community/mathlib/pull/3875))
#### Estimated changes
Modified src/tactic/basic.lean


Modified src/tactic/core.lean


Created src/tactic/dec_trivial.lean


Modified src/tactic/interactive.lean


Created test/dec_trivial_tactic.lean


Created test/revert_target_deps.lean




## [2020-08-22 04:56:48](https://github.com/leanprover-community/mathlib/commit/83db96b)
feat(algebra/group/with_one): make with_one and with_zero irreducible. ([#3883](https://github.com/leanprover-community/mathlib/pull/3883))
#### Estimated changes
Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/algebra/continued_fractions/computation/translations.lean


Modified src/algebra/continued_fractions/convergents_equiv.lean


Modified src/algebra/group/with_one.lean
- \+ *lemma* coe_mul
- \+ *lemma* zero_mul
- \+ *lemma* mul_zero
- \+ *lemma* coe_inv
- \+ *lemma* mul_inv_cancel
- \- *lemma* mul_coe
- \- *lemma* inv_coe
- \+ *theorem* mul_comm

Modified src/algebra/ordered_group.lean


Modified src/data/polynomial/ring_division.lean


Modified src/data/seq/seq.lean




## [2020-08-22 01:22:48](https://github.com/leanprover-community/mathlib/commit/4b24166)
chore(scripts): update nolints.txt ([#3905](https://github.com/leanprover-community/mathlib/pull/3905))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-22 00:21:09](https://github.com/leanprover-community/mathlib/commit/278f512)
feat(data/real): define the golden ratio and its conjugate, prove irrationality of both and Binet's formula ([#3885](https://github.com/leanprover-community/mathlib/pull/3885))
Co-authored by @alreadydone and @monadius through their solutions to the corresponding Codewars Kata.
#### Estimated changes
Modified src/data/fintype/card.lean
- \+ *lemma* finset.prod_range_eq_prod_fin
- \+ *lemma* finset.prod_fin_eq_prod_range
- \- *lemma* finset.range_prod_eq_univ_prod

Created src/data/real/golden_ratio.lean
- \+ *lemma* inv_gold
- \+ *lemma* inv_gold_conj
- \+ *lemma* gold_mul_gold_conj
- \+ *lemma* gold_conj_mul_gold
- \+ *lemma* gold_add_gold_conj
- \+ *lemma* one_sub_gold_conj
- \+ *lemma* one_sub_gold
- \+ *lemma* gold_sub_gold_conj
- \+ *lemma* gold_sq
- \+ *lemma* gold_conj_sq
- \+ *lemma* gold_pos
- \+ *lemma* gold_ne_zero
- \+ *lemma* one_lt_gold
- \+ *lemma* gold_conj_neg
- \+ *lemma* gold_conj_ne_zero
- \+ *lemma* neg_one_lt_gold_conj
- \+ *lemma* fib_rec_char_poly_eq
- \+ *lemma* fib_is_sol_fib_rec
- \+ *lemma* geom_gold_is_sol_fib_rec
- \+ *lemma* geom_gold_conj_is_sol_fib_rec
- \+ *theorem* gold_irrational
- \+ *theorem* gold_conj_irrational
- \+ *theorem* real.coe_fib_eq'
- \+ *theorem* real.coe_fib_eq
- \+ *def* golden_ratio
- \+ *def* golden_conj
- \+ *def* fib_rec

Modified src/number_theory/bernoulli.lean




## [2020-08-21 22:13:24](https://github.com/leanprover-community/mathlib/commit/9998bee)
chore(measure_theory/*): remove some `measurable f` arguments ([#3902](https://github.com/leanprover-community/mathlib/pull/3902))
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* integral_add_measure

Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* integral_add_adjacent_intervals_cancel
- \+/\- *lemma* integral_add_adjacent_intervals
- \+/\- *lemma* integral_interval_sub_left
- \+/\- *lemma* integral_interval_add_interval_comm
- \+/\- *lemma* integral_interval_sub_interval_comm
- \+/\- *lemma* integral_interval_sub_interval_comm'
- \+/\- *lemma* integral_Iic_sub_Iic

Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* integral_add_compl



## [2020-08-21 20:49:40](https://github.com/leanprover-community/mathlib/commit/4c04f0b)
feat(topology/algebra/ordered): sum of functions with limits at_top and cst ([#3833](https://github.com/leanprover-community/mathlib/pull/3833))
Two functions which tend to `at_top` have sum tending to `at_top`.  Likewise if one tends to `at_top` and one tends to a constant.
Also made a couple of edits relating to [this conversation](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Ordered.20groups.20have.20no.20top.20element) about `no_top` for algebraic structures:
#### Estimated changes
Modified src/algebra/ordered_field.lean


Modified src/algebra/ordered_ring.lean


Modified src/order/filter/at_top_bot.lean
- \+ *lemma* tendsto_at_top_add
- \+ *lemma* tendsto_at_bot_add

Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_at_top_add_tendsto_left
- \+ *lemma* tendsto_at_bot_add_tendsto_left
- \+ *lemma* tendsto_at_top_add_tendsto_right
- \+ *lemma* tendsto_at_bot_add_tendsto_right



## [2020-08-21 19:07:51](https://github.com/leanprover-community/mathlib/commit/1db32c5)
feat(set/basic): some results about `set.pi` ([#3894](https://github.com/leanprover-community/mathlib/pull/3894))
New definition: `function.eval`
Also some changes in `set.basic`
Name changes:
```
pi_empty_index -> empty_pi
pi_insert_index -> insert_pi
pi_singleton_index -> singleton_pi
set.push_pull -> image_inter_preimage
set.push_pull' -> image_preimage_inter
```
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* image_inter_preimage
- \+ *lemma* image_preimage_inter
- \+ *lemma* image_compl_preimage
- \+ *lemma* mem_pi
- \+ *lemma* mem_univ_pi
- \+ *lemma* empty_pi
- \+ *lemma* pi_eq_empty
- \+ *lemma* univ_pi_eq_empty
- \+ *lemma* pi_nonempty_iff
- \+ *lemma* univ_pi_nonempty_iff
- \+ *lemma* pi_eq_empty_iff
- \+ *lemma* univ_pi_eq_empty_iff
- \+ *lemma* insert_pi
- \+ *lemma* singleton_pi
- \+/\- *lemma* pi_if
- \+ *lemma* eval_image_pi
- \+ *lemma* eval_image_univ_pi
- \+ *lemma* update_preimage_pi
- \+ *lemma* update_preimage_univ_pi
- \+ *lemma* subset_pi_eval_image
- \- *lemma* pi_empty_index
- \- *lemma* pi_insert_index
- \- *lemma* pi_singleton_index
- \+/\- *def* pi

Modified src/field_theory/chevalley_warning.lean


Modified src/logic/function/basic.lean
- \+ *lemma* eval_apply
- \+ *def* eval

Modified src/order/filter/basic.lean




## [2020-08-21 18:31:42](https://github.com/leanprover-community/mathlib/commit/0c7ac83)
feat(measure_theory/bochner_integration): add `integral_smul_measure` ([#3900](https://github.com/leanprover-community/mathlib/pull/3900))
Also add `integral_dirac`
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* integral_eq_zero_of_ae
- \+/\- *lemma* integral_add_measure
- \+ *lemma* integral_smul_measure
- \+ *lemma* integral_dirac

Modified src/measure_theory/measure_space.lean
- \+ *lemma* ae_smul_measure
- \+ *lemma* ae_add_measure_iff
- \+ *theorem* smul_apply



## [2020-08-21 16:04:55](https://github.com/leanprover-community/mathlib/commit/ac56790)
feat(order/rel_iso): a new definition of order_iso, using preorder instances ([#3838](https://github.com/leanprover-community/mathlib/pull/3838))
defines (new) `order_embedding` and `order_iso`, which map both < and <=
replaces existing `rel_embedding` and `rel_iso` instances preserving < or <= with the new abbreviations
#### Estimated changes
Modified src/data/finsupp/lattice.lean
- \+ *lemma* order_iso_multiset_apply
- \+ *lemma* order_iso_multiset_symm_apply
- \+ *lemma* order_embedding_to_fun_apply
- \- *lemma* rel_iso_multiset_apply
- \- *lemma* rel_iso_multiset_symm_apply
- \- *lemma* rel_embedding_to_fun_apply
- \+ *def* order_iso_multiset
- \+ *def* order_embedding_to_fun
- \- *def* rel_iso_multiset
- \- *def* rel_embedding_to_fun

Modified src/data/setoid/basic.lean
- \+/\- *def* correspondence

Modified src/data/setoid/partition.lean


Modified src/group_theory/congruence.lean
- \+/\- *def* correspondence

Modified src/linear_algebra/basic.lean
- \+ *def* map_subtype.order_embedding
- \+ *def* comap_mkq.order_embedding
- \- *def* map_subtype.le_rel_embedding
- \- *def* map_subtype.lt_rel_embedding
- \- *def* comap_mkq.le_rel_embedding
- \- *def* comap_mkq.lt_rel_embedding

Modified src/order/basic.lean


Modified src/order/galois_connection.lean
- \+ *theorem* order_iso.to_galois_connection
- \- *theorem* rel_iso.to_galois_connection

Modified src/order/ord_continuous.lean
- \+ *lemma* coe_to_order_embedding
- \- *lemma* coe_to_le_rel_embedding
- \- *lemma* coe_to_lt_rel_embedding
- \+ *def* to_order_embedding
- \- *def* to_le_rel_embedding
- \- *def* to_lt_rel_embedding

Modified src/order/rel_iso.lean
- \+ *lemma* lt_embedding_apply
- \+ *lemma* order_iso.map_bot
- \- *lemma* rel_iso.map_bot
- \+ *theorem* map_le_iff
- \+ *theorem* map_lt_iff
- \+ *def* order_embedding_of_lt_embedding
- \+ *def* lt_embedding
- \+ *def* osymm
- \+/\- *def* fin.val.rel_embedding
- \+/\- *def* fin_fin.rel_embedding
- \+ *def* order_iso.osymm
- \- *def* lt_embedding_of_le_embedding

Modified src/order/semiconj_Sup.lean


Modified src/ring_theory/ideal/operations.lean
- \+ *def* order_embedding_of_surjective
- \+/\- *def* rel_iso_of_bijective
- \- *def* le_rel_embedding_of_surjective
- \- *def* lt_rel_embedding_of_surjective

Modified src/ring_theory/localization.lean
- \+ *def* order_embedding
- \- *def* le_rel_embedding

Modified src/ring_theory/noetherian.lean


Modified src/set_theory/cardinal_ordinal.lean


Modified src/set_theory/ordinal.lean
- \+ *theorem* ord.order_embedding_coe
- \- *theorem* ord.rel_embedding_coe
- \+ *def* ord.order_embedding
- \- *def* ord.rel_embedding



## [2020-08-21 13:01:05](https://github.com/leanprover-community/mathlib/commit/e3409c6)
feat(data/zmod/basic): morphisms to zmod are surjective (deps: [#3888](https://github.com/leanprover-community/mathlib/pull/3888)) ([#3889](https://github.com/leanprover-community/mathlib/pull/3889))
... and determined by their kernel
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.ring_hom_surjective
- \+ *lemma* zmod.ring_hom_eq_of_ker_eq

Modified src/group_theory/sylow.lean




## [2020-08-21 11:41:54](https://github.com/leanprover-community/mathlib/commit/4921be9)
feat(analysis/special_functions/arsinh): inverse hyperbolic sine function ([#3801](https://github.com/leanprover-community/mathlib/pull/3801))
Added the following lemmas and definitions:
`cosh_def`
`sinh_def`
`cosh_pos`
`sinh_strict_mono`
`sinh_injective`
`sinh_surjective`
`sinh_bijective`
`real.cosh_sq_sub_sinh_sq`
`sqrt_one_add_sinh_sq`
`sinh_arsinh`
`arsinh_sin`
This is from the list of UG not in lean. `cosh` coming soon.
#### Estimated changes
Created src/analysis/special_functions/arsinh.lean
- \+ *lemma* sinh_injective
- \+ *lemma* sinh_arsinh
- \+ *lemma* sinh_surjective
- \+ *lemma* sinh_bijective
- \+ *lemma* sqrt_one_add_sinh_sq
- \+ *lemma* arsinh_sinh
- \+ *def* arsinh

Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* sinh_strict_mono

Modified src/data/complex/exponential.lean
- \+ *lemma* sinh_eq
- \+ *lemma* cosh_eq
- \+ *lemma* cosh_sq_sub_sinh_sq
- \+ *lemma* cosh_pos



## [2020-08-21 10:07:49](https://github.com/leanprover-community/mathlib/commit/7a48761)
feat(logic/function): left/right inverse iff ([#3897](https://github.com/leanprover-community/mathlib/pull/3897))
From the sphere eversion project.
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *theorem* left_inverse_iff_comp
- \+ *theorem* right_inverse_iff_comp



## [2020-08-21 10:07:47](https://github.com/leanprover-community/mathlib/commit/de20a39)
feat(group_theory/subroup,ring_theory/ideal/operations): lift_of_surjective ([#3888](https://github.com/leanprover-community/mathlib/pull/3888))
Surjective homomorphisms behave like quotient maps
#### Estimated changes
Modified src/group_theory/abelianization.lean


Modified src/group_theory/presented_group.lean


Modified src/group_theory/quotient_group.lean


Modified src/group_theory/subgroup.lean
- \+/\- *lemma* mem_ker
- \+ *lemma* lift_of_surjective_comp_apply
- \+ *lemma* lift_of_surjective_comp
- \+ *lemma* eq_lift_of_surjective

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* lift_of_surjective_comp_apply
- \+ *lemma* lift_of_surjective_comp
- \+ *lemma* eq_lift_of_surjective



## [2020-08-21 10:07:46](https://github.com/leanprover-community/mathlib/commit/045b6c7)
chore(topology/basic): use dot notation ([#3861](https://github.com/leanprover-community/mathlib/pull/3861))
## API changes
* add `set.range_sigma_mk`, `finset.sigma_preimage_mk`, `finset.sigma_preimage_mk_of_subset`,
  `finset.sigma_image_fst_preimage_mk`, `finset.prod_preimage'`;
* rename `filter.monotone.tendsto_at_top_finset` to `filter.tendsto_at_top_finset_of_monotone`,
  add alias `monotone.tendsto_at_top_finset`;
* add `filter.tendsto_finset_preimage_at_top_at_top`;
* add `filter.tendsto.frequently`;
* add `cluster_pt_principal_iff_frequently`, `mem_closure_iff_frequently`, `filter.frequently.mem_closure`,
  `filter.frequently.mem_of_closed`, `is_closed.mem_of_frequently_of_tendsto`;
* rename `mem_of_closed_of_tendsto` to `is_closed.mem_of_tendsto`;
* delete `mem_of_closed_of_tendsto'`; use new `is_closed.mem_of_frequently_of_tendsto` instead;
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* range_sigma_mk

Modified src/data/set/finite.lean
- \+ *lemma* sigma_preimage_mk
- \+ *lemma* sigma_preimage_mk_of_subset
- \+ *lemma* sigma_image_fst_preimage_mk
- \+ *lemma* prod_preimage'
- \+/\- *lemma* prod_preimage

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* tendsto_at_top_finset_of_monotone
- \+ *lemma* tendsto_finset_preimage_at_top_at_top
- \- *lemma* monotone.tendsto_at_top_finset

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/basic.lean
- \+ *lemma* cluster_pt_principal_iff_frequently
- \+ *lemma* mem_closure_iff_frequently
- \+/\- *lemma* closure_eq_cluster_pts
- \+ *lemma* filter.frequently.mem_of_closed
- \+ *lemma* is_closed.mem_of_frequently_of_tendsto
- \+ *lemma* is_closed.mem_of_tendsto
- \- *lemma* mem_of_closed_of_tendsto
- \- *lemma* mem_of_closed_of_tendsto'

Modified src/topology/dense_embedding.lean


Modified src/topology/extend_from_subset.lean


Modified src/topology/metric_space/baire.lean




## [2020-08-21 10:07:44](https://github.com/leanprover-community/mathlib/commit/d8cde2a)
feat(measure_theory/interval_integral): more versions of FTC-1 ([#3709](https://github.com/leanprover-community/mathlib/pull/3709))
Left/right derivative, strict derivative, differentiability in both endpoints.
Other changes:
* rename `filter.tendsto_le_left` and `filter.tendsto_le_right` to `filter.tendsto.mono_left` and `filter.tendsto.mono_right`, swap arguments;
* rename `order_top.tendsto_at_top` to `order_top.tendsto_at_top_nhds`;
* introduce `tendsto_Ixx_class` instead of `is_interval_generated`.
#### Estimated changes
Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/tangent_cone.lean
- \+ *lemma* unique_diff_on.unique_diff_within_at

Modified src/analysis/specific_limits.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/interval_integral.lean
- \+ *lemma* filter.tendsto.eventually_interval_integrable_ae
- \+ *lemma* filter.tendsto.eventually_interval_integrable
- \+ *lemma* integral_sub
- \+ *lemma* integral_smul
- \+ *lemma* integral_const'
- \+ *lemma* integral_const
- \+ *lemma* integral_interval_sub_left
- \+ *lemma* integral_interval_add_interval_comm
- \+ *lemma* integral_interval_sub_interval_comm
- \+ *lemma* integral_interval_sub_interval_comm'
- \+ *lemma* integral_Iic_sub_Iic
- \+ *lemma* integral_const_of_cdf
- \+ *lemma* finite_at_inner
- \+ *lemma* measure_integral_sub_linear_is_o_of_tendsto_ae'
- \+ *lemma* measure_integral_sub_linear_is_o_of_tendsto_ae_of_le'
- \+ *lemma* measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge'
- \+ *lemma* measure_integral_sub_linear_is_o_of_tendsto_ae
- \+ *lemma* measure_integral_sub_linear_is_o_of_tendsto_ae_of_le
- \+ *lemma* measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge
- \+ *lemma* measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae
- \+ *lemma* measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right
- \+ *lemma* measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left
- \+/\- *lemma* integral_sub_linear_is_o_of_tendsto_ae
- \+ *lemma* integral_sub_integral_sub_linear_is_o_of_tendsto_ae
- \+ *lemma* integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right
- \+ *lemma* integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left
- \+ *lemma* integral_has_strict_fderiv_at_of_tendsto_ae
- \+ *lemma* integral_has_strict_fderiv_at
- \+ *lemma* integral_has_strict_deriv_at_of_tendsto_ae_right
- \+ *lemma* integral_has_strict_deriv_at_right
- \+ *lemma* integral_has_strict_deriv_at_of_tendsto_ae_left
- \+ *lemma* integral_has_strict_deriv_at_left
- \+ *lemma* integral_has_fderiv_at_of_tendsto_ae
- \+ *lemma* integral_has_fderiv_at
- \+ *lemma* fderiv_integral_of_tendsto_ae
- \+ *lemma* fderiv_integral
- \+ *lemma* integral_has_deriv_at_of_tendsto_ae_right
- \+ *lemma* integral_has_deriv_at_right
- \+ *lemma* deriv_integral_of_tendsto_ae_right
- \+ *lemma* deriv_integral_right
- \+ *lemma* integral_has_deriv_at_of_tendsto_ae_left
- \+ *lemma* integral_has_deriv_at_left
- \+ *lemma* deriv_integral_of_tendsto_ae_left
- \+ *lemma* deriv_integral_left
- \+ *lemma* integral_has_fderiv_within_at_of_tendsto_ae
- \+ *lemma* integral_has_fderiv_within_at
- \+ *lemma* fderiv_within_integral_of_tendsto_ae
- \+ *lemma* integral_has_deriv_within_at_of_tendsto_ae_right
- \+ *lemma* integral_has_deriv_within_at_right
- \+ *lemma* deriv_within_integral_of_tendsto_ae_right
- \+ *lemma* deriv_within_integral_right
- \+ *lemma* integral_has_deriv_within_at_of_tendsto_ae_left
- \+ *lemma* integral_has_deriv_within_at_left
- \+ *lemma* deriv_within_integral_of_tendsto_ae_left
- \+ *lemma* deriv_within_integral_left
- \- *lemma* integral_same_has_deriv_at_of_tendsto_ae
- \- *lemma* integral_has_deriv_at_of_tendsto_ae

Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_lt_top
- \+ *lemma* measure_ne_top
- \+ *lemma* measure.finite_at_bot

Modified src/measure_theory/set_integral.lean


Modified src/order/filter/basic.lean
- \+ *lemma* tendsto.frequently
- \+ *lemma* tendsto.mono_left
- \+ *lemma* tendsto.mono_right
- \+/\- *lemma* tendsto_infi'
- \- *lemma* tendsto_le_left
- \- *lemma* tendsto_le_right

Modified src/order/filter/interval.lean
- \+/\- *lemma* tendsto.Icc
- \+/\- *lemma* tendsto.Ioc
- \+/\- *lemma* tendsto.Ico
- \+/\- *lemma* tendsto.Ioo
- \+ *lemma* tendsto_Ixx_class_principal
- \+ *lemma* tendsto_Ixx_class_inf
- \+ *lemma* tendsto_Ixx_class_of_subset
- \+ *lemma* has_basis.tendsto_Ixx_class
- \- *lemma* has_basis.is_interval_generated
- \- *lemma* has_ord_connected_basis
- \- *lemma* is_interval_generated_principal_iff
- \- *lemma* tendsto_Ixx_same_filter
- \- *lemma* tendsto.Ixx
- \- *lemma* set.ord_connected.is_interval_generated_inf_principal

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/basic.lean
- \+ *lemma* order_top.tendsto_at_top_nhds
- \- *lemma* order_top.tendsto_at_top

Modified src/topology/continuous_on.lean
- \+ *lemma* tendsto_const_nhds_within



## [2020-08-21 08:35:09](https://github.com/leanprover-community/mathlib/commit/bc3e835)
feat(tactic/rcases): clear pattern `-` in rcases ([#3868](https://github.com/leanprover-community/mathlib/pull/3868))
This allows you to write:
```lean
example (h : ∃ x : ℕ, true) : true :=
begin
  rcases h with ⟨x, -⟩,
  -- x : ℕ |- true
end
```
to clear unwanted hypotheses. Note that dependents are also cleared,
meaning that you can get into trouble if you try to keep matching when a
variable later in the pattern is deleted. The `_` pattern will match
a hypothesis even if it has been deleted, so this is the recommended way
to match on variables dependent on a deleted hypothesis.
You can use `-` if you prefer, but watch out for unintended variables
getting deleted if there are duplicate names!
#### Estimated changes
Modified src/tactic/rcases.lean


Modified test/rcases.lean




## [2020-08-21 07:33:42](https://github.com/leanprover-community/mathlib/commit/da6cd55)
feat(determinant): towards multilinearity ([#3887](https://github.com/leanprover-community/mathlib/pull/3887))
From the sphere eversion project. In a PR coming soon, this will be used to prove that the determinant of a family of vectors in a given basis is multi-linear (see [here](https://github.com/leanprover-community/sphere-eversion/blob/2c776f6a92c0f9babb521a02ab0cc341a06d3f3c/src/vec_det.lean) for a preview if needed).
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* det_update_column_add
- \+ *lemma* det_update_row_add
- \+ *lemma* det_update_column_smul
- \+ *lemma* det_update_row_smul



## [2020-08-21 05:29:48](https://github.com/leanprover-community/mathlib/commit/23749aa)
chore(measure_theory/*): use `_measure` instead of `_meas` ([#3892](https://github.com/leanprover-community/mathlib/pull/3892))
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* integral_add_measure
- \+ *lemma* integral_zero_measure
- \+ *lemma* integral_map_measure
- \- *lemma* integral_add_meas
- \- *lemma* integral_zero_meas
- \- *lemma* integral_map_meas

Modified src/measure_theory/integration.lean
- \+ *lemma* lintegral_smul_measure
- \+ *lemma* lintegral_sum_measure
- \+ *lemma* lintegral_add_measure
- \+ *lemma* lintegral_zero_measure
- \- *lemma* lintegral_smul_meas
- \- *lemma* lintegral_sum_meas
- \- *lemma* lintegral_add_meas
- \- *lemma* lintegral_zero_meas

Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable.mono_measure
- \+ *lemma* integrable.add_measure
- \+ *lemma* integrable.left_of_add_measure
- \+ *lemma* integrable.right_of_add_measure
- \+ *lemma* integrable_add_measure
- \+ *lemma* integrable.smul_measure
- \+ *lemma* integrable_zero_measure
- \+ *lemma* integrable_map_measure
- \- *lemma* integrable.mono_meas
- \- *lemma* integrable.add_meas
- \- *lemma* integrable.left_of_add_meas
- \- *lemma* integrable.right_of_add_meas
- \- *lemma* integrable_add_meas
- \- *lemma* integrable.smul_meas
- \- *lemma* integrable_zero_meas
- \- *lemma* integrable_map_meas

Modified src/measure_theory/set_integral.lean
- \+ *lemma* integrable_on.mono_measure
- \+ *lemma* integrable_on.add_measure
- \+ *lemma* integrable_on_add_measure
- \+/\- *lemma* integral_empty
- \- *lemma* integrable_on.mono_meas
- \- *lemma* integrable_on.add_meas
- \- *lemma* integrable_on_add_meas



## [2020-08-21 03:53:31](https://github.com/leanprover-community/mathlib/commit/31cd6dd)
chore(order/bounded_lattice): use `⦃⦄` in `disjoint.symm` ([#3893](https://github.com/leanprover-community/mathlib/pull/3893))
#### Estimated changes
Modified src/data/set/disjointed.lean


Modified src/order/bounded_lattice.lean
- \+/\- *theorem* disjoint.symm



## [2020-08-21 02:24:33](https://github.com/leanprover-community/mathlib/commit/1719035)
feat(category_theory/monad/*): Add category of bundled (co)monads; prove equivalence of monads with monoid objects ([#3762](https://github.com/leanprover-community/mathlib/pull/3762))
This PR constructs bundled monads, and proves the "usual" equivalence between the category of monads and the category of monoid objects in the endomorphism category.
It also includes a definition of morphisms of unbundled monads, and proves some necessary small lemmas in the following two files:
1. `category_theory.functor_category`
2. `category_theory.monoidal.internal`
Given any isomorphism in `Cat`, we construct a corresponding equivalence of categories in `Cat.equiv_of_iso`.
#### Estimated changes
Modified src/category_theory/category/Cat.lean
- \+ *def* equiv_of_iso

Modified src/category_theory/functor_category.lean
- \+ *lemma* hcomp_id_app
- \+ *lemma* id_hcomp_app

Modified src/category_theory/monad/basic.lean
- \+ *lemma* id_comp
- \+ *lemma* comp_id
- \+ *lemma* assoc
- \+ *theorem* ext
- \+ *def* id
- \+ *def* comp

Created src/category_theory/monad/bundled.lean
- \+ *lemma* comp_to_nat_trans
- \+ *lemma* assoc_func_app
- \+ *lemma* coassoc_func_app
- \+ *def* initial
- \+ *def* hom
- \+ *def* forget
- \+ *def* terminal

Created src/category_theory/monad/equiv_mon.lean
- \+ *def* to_Mon
- \+ *def* Monad_to_Mon
- \+ *def* of_Mon
- \+ *def* Mon_to_Monad
- \+ *def* of_to_mon_end_iso
- \+ *def* to_of_mon_end_iso
- \+ *def* Monad_Mon_equiv



## [2020-08-21 01:44:02](https://github.com/leanprover-community/mathlib/commit/7271f74)
chore(scripts): update nolints.txt ([#3891](https://github.com/leanprover-community/mathlib/pull/3891))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-21 00:08:35](https://github.com/leanprover-community/mathlib/commit/0a48f0a)
feat(system/random): a monad for (pseudo-)randomized computations ([#3742](https://github.com/leanprover-community/mathlib/pull/3742))
#### Estimated changes
Modified src/control/monad/basic.lean
- \+ *def* state_t.eval
- \+ *def* state_t.equiv
- \+ *def* reader_t.equiv

Modified src/control/monad/cont.lean
- \+ *def* cont_t.equiv

Modified src/control/monad/writer.lean
- \+ *def* writer_t.equiv

Created src/control/uliftable.lean
- \+ *lemma* up_down
- \+ *lemma* down_up
- \+ *def* up
- \+ *def* down
- \+ *def* adapt_up
- \+ *def* adapt_down
- \+ *def* up_map
- \+ *def* down_map
- \+ *def* state_t.uliftable'
- \+ *def* reader_t.uliftable'
- \+ *def* cont_t.uliftable'
- \+ *def* writer_t.uliftable'

Created src/data/bitvec/basic.lean
- \+ *lemma* of_fin_val
- \+ *lemma* add_lsb_eq_twice_add_one
- \+ *lemma* to_nat_eq_foldr_reverse
- \+ *lemma* to_nat_lt
- \+ *lemma* add_lsb_div_two
- \+ *lemma* to_bool_add_lsb_mod_two
- \+ *lemma* of_nat_to_nat
- \+ *lemma* to_fin_val
- \+ *lemma* to_fin_le_to_fin_of_le
- \+ *lemma* of_fin_le_of_fin_of_le
- \+ *lemma* to_fin_of_fin
- \+ *lemma* of_fin_to_fin
- \+ *def* of_fin
- \+ *def* to_fin

Modified src/data/bool.lean
- \+ *lemma* of_nat_le_of_nat
- \+ *lemma* to_nat_le_to_nat
- \+ *lemma* of_nat_to_nat
- \+ *def* to_nat
- \+ *def* of_nat

Modified src/data/fin.lean
- \+ *lemma* fact.succ.pos
- \+ *lemma* fact.bit0.pos
- \+ *lemma* fact.bit1.pos
- \+ *lemma* fact.pow.pos
- \+/\- *lemma* add_nat_val
- \+ *lemma* val_of_nat_eq_mod
- \+ *lemma* val_of_nat_eq_mod'
- \+ *def* of_nat'

Modified src/data/nat/basic.lean
- \+ *lemma* pow_le_iff_le_log
- \+ *lemma* log_pow
- \+ *lemma* pow_succ_log_gt_self
- \+ *lemma* pow_log_le_self
- \+ *def* log

Modified src/data/stream/basic.lean
- \+ *lemma* length_take
- \+ *def* take
- \+ *def* corec_state

Modified src/set_theory/lists.lean


Created src/system/random/basic.lean
- \+ *lemma* bool_of_nat_mem_Icc_of_mem_Icc_to_nat
- \+ *def* rand_g
- \+ *def* rand
- \+ *def* rand_g.next
- \+ *def* shift_31_left
- \+ *def* split
- \+ *def* random
- \+ *def* random_series
- \+ *def* random_r
- \+ *def* random_series_r
- \+ *def* mk_generator
- \+ *def* run_rand
- \+ *def* random_fin_of_pos
- \+ *def* bitvec.random
- \+ *def* bitvec.random_r

Created test/slim_check.lean
- \+ *def* primality_test
- \+ *def* iterated_primality_test_aux
- \+ *def* iterated_primality_test
- \+ *def* find_prime_aux
- \+ *def* find_prime



## [2020-08-20 23:05:44](https://github.com/leanprover-community/mathlib/commit/36386fc)
feat(linear_algebra): some easy linear map/equiv lemmas ([#3890](https://github.com/leanprover-community/mathlib/pull/3890))
From the sphere eversion project.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* eq_of_linear_map_eq
- \+ *lemma* trans_symm
- \+ *lemma* symm_trans
- \+ *lemma* refl_to_linear_map
- \+ *lemma* comp_coe

Modified src/linear_algebra/basis.lean
- \+ *lemma* equiv_of_is_basis_comp
- \+ *lemma* equiv_of_is_basis_refl
- \+ *lemma* equiv_of_is_basis_trans_symm
- \+ *lemma* equiv_of_is_basis_symm_trans



## [2020-08-20 21:33:51](https://github.com/leanprover-community/mathlib/commit/c9704ff)
chore(data/matrix, linear_algebra): generalize universe parameters ([#3879](https://github.com/leanprover-community/mathlib/pull/3879))
@PatrickMassot was complaining that `matrix m n R` often doesn't work when the parameters are declared as `m n : Type*` because the universe parameters were equal. This PR makes the universe parameters of `m` and `n` distinct where possible, also generalizing some other linear algebra definitions.
The types of `col` and `row` used to be `matrix n punit` but are now `matrix n unit`, otherwise the elaborator can't figure out the universe. This doesn't seem to break anything except for the cases where `punit.{n}` was explicitly written down.
There were some breakages, but the total amount of changes is not too big.
#### Estimated changes
Modified src/algebra/classical_lie_algebras.lean
- \+/\- *def* JB
- \+/\- *def* PB

Modified src/data/matrix/basic.lean
- \+/\- *lemma* from_blocks_multiply
- \+/\- *def* matrix
- \+/\- *def* col
- \+/\- *def* row

Modified src/data/matrix/notation.lean
- \+/\- *lemma* empty_val'
- \+/\- *lemma* smul_mat_empty

Modified src/data/matrix/pequiv.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_range_le
- \+/\- *lemma* dim_map_le
- \+/\- *lemma* dim_range_of_surjective
- \+/\- *lemma* dim_eq_of_surjective
- \+/\- *lemma* dim_le_of_surjective
- \+/\- *lemma* dim_eq_of_injective
- \+/\- *lemma* dim_le_of_injective
- \+/\- *lemma* rank_le_domain
- \+/\- *lemma* rank_le_range
- \+/\- *lemma* rank_add_le
- \+/\- *lemma* rank_zero
- \+/\- *lemma* rank_finset_sum_le
- \+/\- *lemma* rank_comp_le1
- \+/\- *lemma* rank_comp_le2
- \+/\- *theorem* linear_equiv.dim_eq
- \+/\- *theorem* dim_prod
- \+/\- *theorem* dim_range_add_dim_ker
- \+/\- *def* rank

Modified src/linear_algebra/matrix.lean
- \+/\- *lemma* rank_vec_mul_vec



## [2020-08-20 21:33:49](https://github.com/leanprover-community/mathlib/commit/901c5bc)
feat(ring_theory/separable): a separable polynomial splits into a product of unique `X - C a` ([#3877](https://github.com/leanprover-community/mathlib/pull/3877))
Bonus result: the degree of a separable polynomial is the number of roots
in the field where it splits.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* bind_singleton_eq_self

Modified src/data/multiset/nodup.lean
- \+ *lemma* nodup_iff_ne_cons_cons

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* roots_prod
- \+ *lemma* roots_prod_X_sub_C

Modified src/field_theory/separable.lean
- \+ *lemma* separable.of_dvd
- \+ *lemma* is_unit_of_self_mul_dvd_separable
- \+ *lemma* not_unit_X_sub_C
- \+ *lemma* nodup_of_separable_prod
- \+ *lemma* eq_prod_roots_of_separable
- \+ *lemma* nat_degree_separable_eq_card_roots
- \+ *lemma* degree_separable_eq_card_roots



## [2020-08-20 21:33:47](https://github.com/leanprover-community/mathlib/commit/9f525c7)
chore(category_theory/limits/types): cleanup ([#3871](https://github.com/leanprover-community/mathlib/pull/3871))
Backporting some cleaning up work from `prop_limits`, while it rumbles onwards.
#### Estimated changes
Modified src/algebra/category/Module/limits.lean


Modified src/algebra/category/Mon/limits.lean


Modified src/category_theory/limits/limits.lean


Modified src/category_theory/limits/preserves/basic.lean
- \+ *def* preserves_limit_of_reflects_of_preserves
- \+ *def* preserves_colimit_of_reflects_of_preserves

Modified src/category_theory/limits/shapes/types.lean


Modified src/category_theory/limits/types.lean
- \+ *lemma* limit_equiv_sections_apply
- \+ *lemma* limit_equiv_sections_symm_apply
- \+ *lemma* limit_ext
- \+ *lemma* lift_π_apply
- \+ *lemma* colimit_equiv_quot_symm_apply
- \- *lemma* types_limit
- \- *lemma* types_limit_π
- \- *lemma* types_limit_pre
- \- *lemma* types_limit_map
- \- *lemma* types_limit_lift
- \- *lemma* types_colimit
- \- *lemma* types_colimit_ι
- \- *lemma* types_colimit_pre
- \- *lemma* types_colimit_map
- \- *lemma* types_colimit_desc
- \+ *def* limit_cone
- \+ *def* limit_cone_is_limit
- \+ *def* limit_equiv_sections
- \+ *def* quot
- \+ *def* colimit_cocone
- \+ *def* colimit_cocone_is_colimit
- \+ *def* colimit_equiv_quot
- \- *def* limit_
- \- *def* limit_is_limit_
- \- *def* colimit_
- \- *def* colimit_is_colimit_



## [2020-08-20 16:50:10](https://github.com/leanprover-community/mathlib/commit/7a93d87)
doc(src/ring_theory/integral_domain.lean): add module docstring ([#3881](https://github.com/leanprover-community/mathlib/pull/3881))
#### Estimated changes
Modified src/ring_theory/integral_domain.lean




## [2020-08-20 11:47:20](https://github.com/leanprover-community/mathlib/commit/4631018)
feat(data/polynomial): Add polynomial/eval lemmas ([#3876](https://github.com/leanprover-community/mathlib/pull/3876))
Add some lemmas about `polynomial`. In particular, add lemmas about
`eval2` for the case that the ring `S` that we evaluate into is
non-commutative.
#### Estimated changes
Modified src/data/polynomial/degree/basic.lean
- \+ *lemma* leading_coeff_X_add_C

Modified src/data/polynomial/eval.lean
- \+ *lemma* eval₂_mul_noncomm
- \+ *lemma* eval₂_list_prod_noncomm
- \+ *lemma* eval₂_endomorphism_algebra_map
- \+ *def* eval₂_ring_hom_noncomm

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* units_coeff_zero_smul



## [2020-08-20 08:43:40](https://github.com/leanprover-community/mathlib/commit/e174f42)
feat(equiv/transfer_instances): other algebraic structures ([#3870](https://github.com/leanprover-community/mathlib/pull/3870))
Some updates to `data.equiv.transfer_instances`.
1. Use `@[to_additive]`
2. Add algebraic equivalences between the original and transferred instances.
3. Transfer modules and algebras.
#### Estimated changes
Modified src/data/equiv/transfer_instance.lean
- \+ *lemma* smul_def
- \+ *lemma* mul_equiv_apply
- \+ *lemma* mul_equiv_symm_apply
- \+ *lemma* ring_equiv_apply
- \+ *lemma* ring_equiv_symm_apply
- \- *lemma* zero_def
- \- *lemma* add_def
- \- *lemma* neg_def
- \+ *def* mul_equiv
- \+ *def* ring_equiv
- \+ *def* linear_equiv
- \+ *def* alg_equiv



## [2020-08-20 08:43:38](https://github.com/leanprover-community/mathlib/commit/d7621b9)
feat(data/list/basic): lemmas about foldr/foldl ([#3865](https://github.com/leanprover-community/mathlib/pull/3865))
This PR prepares [#3864](https://github.com/leanprover-community/mathlib/pull/3864).
* Move lemmas about `foldr`/`foldl` into the appropriate section.
* Add variants of the `foldl_map`/`foldr_map` lemmas.
* Add lemmas stating that a fold over a list of injective functions is injective.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* injective_foldl_comp
- \+/\- *theorem* foldl_map
- \+/\- *theorem* foldr_map
- \+ *theorem* foldl_map'
- \+ *theorem* foldr_map'
- \+/\- *theorem* foldl_hom
- \+/\- *theorem* foldr_hom



## [2020-08-20 08:00:59](https://github.com/leanprover-community/mathlib/commit/ba06edc)
chore(data/complex/module): move `linear_map.{re,im,of_real}` from `analysis` ([#3874](https://github.com/leanprover-community/mathlib/pull/3874))
I'm going to use these `def`s in `analysis/convex/basic`, and I don't
want to `import analysis.normed_space.basic` there.
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \- *lemma* linear_map.re_apply
- \- *lemma* linear_map.im_apply
- \- *lemma* linear_map.of_real_apply
- \- *def* linear_map.re
- \- *def* linear_map.im
- \- *def* linear_map.of_real

Modified src/data/complex/module.lean
- \+ *lemma* linear_map.coe_re
- \+ *lemma* linear_map.coe_im
- \+ *lemma* linear_map.coe_of_real
- \+ *def* linear_map.re
- \+ *def* linear_map.im
- \+ *def* linear_map.of_real



## [2020-08-20 06:10:17](https://github.com/leanprover-community/mathlib/commit/34db3c3)
feat(order/category): various categories of ordered types ([#3841](https://github.com/leanprover-community/mathlib/pull/3841))
This is a first step towards the category of simplicial sets (which are presheaves on the category of nonempty finite linear orders).
#### Estimated changes
Created src/order/category/LinearOrder.lean
- \+ *def* LinearOrder
- \+ *def* of

Created src/order/category/NonemptyFinLinOrd.lean
- \+ *def* NonemptyFinLinOrd
- \+ *def* of

Created src/order/category/PartialOrder.lean
- \+ *def* PartialOrder
- \+ *def* of

Created src/order/category/Preorder.lean
- \+ *lemma* ext
- \+ *lemma* coe_inj
- \+ *lemma* coe_id
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *def* Preorder
- \+ *def* id
- \+ *def* comp
- \+ *def* of



## [2020-08-20 03:32:46](https://github.com/leanprover-community/mathlib/commit/4364798)
fix(data/fin): better defeqs in fin.has_le instance ([#3869](https://github.com/leanprover-community/mathlib/pull/3869))
This ensures that the instances from `fin.decidable_linear_order` match
the direct instances. They were defeq before but not at instance reducibility.
#### Estimated changes
Modified src/data/fin.lean




## [2020-08-19 22:20:42](https://github.com/leanprover-community/mathlib/commit/9a8e504)
feat(linear_algebra/affine_space/basic): more direction lemmas ([#3867](https://github.com/leanprover-community/mathlib/pull/3867))
Add a few more lemmas about the directions of affine subspaces.
#### Estimated changes
Modified src/linear_algebra/affine_space/basic.lean
- \+ *lemma* vadd_mem_iff_mem_direction
- \+ *lemma* direction_inf_of_mem
- \+ *lemma* direction_inf_of_mem_inf



## [2020-08-19 21:38:08](https://github.com/leanprover-community/mathlib/commit/7e6b8a9)
feat(linear_algebra/affine_space/basic): more vector_span lemmas ([#3866](https://github.com/leanprover-community/mathlib/pull/3866))
Add more lemmas relating `vector_span` to the `submodule.span` of
particular subtractions of points.  The new lemmas fix one of the
points in the subtraction and exclude that point, or its index in the
case of an indexed family of points rather than a set, from being on
the other side of the subtraction (whereas the previous lemmas don't
exclude the trivial subtraction of a point from itself).
#### Estimated changes
Modified src/linear_algebra/affine_space/basic.lean
- \+ *lemma* vector_span_eq_span_vsub_set_left_ne
- \+ *lemma* vector_span_eq_span_vsub_set_right_ne
- \+ *lemma* vector_span_image_eq_span_vsub_set_left_ne
- \+ *lemma* vector_span_image_eq_span_vsub_set_right_ne



## [2020-08-19 17:44:57](https://github.com/leanprover-community/mathlib/commit/bd5552a)
feat(ring_theory/polynomial/basic): Isomorphism between polynomials over a quotient and quotient over polynomials ([#3847](https://github.com/leanprover-community/mathlib/pull/3847))
The main statement is `polynomial_quotient_equiv_quotient_polynomial`, which gives that If `I` is an ideal of `R`, then the ring polynomials over the quotient ring `I.quotient` is isomorphic to the quotient of `polynomial R` by the ideal `map C I`.
Also, `mem_map_C_iff` shows that `map C I` contains exactly the polynomials whose coefficients all lie in `I`
#### Estimated changes
Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* quotient_map_C_eq_zero
- \+ *lemma* eval₂_C_mk_eq_zero
- \+ *theorem* mem_map_C_iff
- \+ *def* polynomial_quotient_equiv_quotient_polynomial



## [2020-08-19 13:32:50](https://github.com/leanprover-community/mathlib/commit/15cacf0)
feat(analysis/normed_space/real_inner_product): orthogonal subspace order ([#3863](https://github.com/leanprover-community/mathlib/pull/3863))
Define the Galois connection between `submodule ℝ α` and its
`order_dual` given by `submodule.orthogonal`.  Thus, deduce that the
inf of orthogonal subspaces is the subspace orthogonal to the sup (for
three different forms of inf), as well as replacing the proof of
`submodule.le_orthogonal_orthogonal` by a use of
`galois_connection.le_u_l`.
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean
- \+ *lemma* submodule.orthogonal_gc
- \+ *lemma* submodule.inf_orthogonal
- \+ *lemma* submodule.infi_orthogonal
- \+ *lemma* submodule.Inf_orthogonal



## [2020-08-19 13:32:45](https://github.com/leanprover-community/mathlib/commit/d963213)
refactor(algebra/add_torsor,linear_algebra/affine_space/basic): vsub_set ([#3858](https://github.com/leanprover-community/mathlib/pull/3858))
The definition of `vsub_set` in `algebra/add_torsor` does something
similar to `set.image2`, but expressed directly with `∃` inside
`{...}`.  Various lemmas in `linear_algebra/affine_space/basic`
likewise express such sets of subtractions with a given point on one
side directly rather than using `set.image`.  These direct forms can
be inconvenient to use with lemmas about `set.image2`, `set.image` and
`set.range`; in particular, they have the equality inside the binders
expressed the other way round, leading to constructs such as `conv_lhs
{ congr, congr, funext, conv { congr, funext, rw eq_comm } }` when
it's necessary to convert one form to the other.
The form of `vsub_set` was suggested in review of [#2720](https://github.com/leanprover-community/mathlib/pull/2720), the original
`add_torsor` addition, based on what was then used in
`algebra/pointwise`.  Since then, `image2` has been added to mathlib
and `algebra/pointwise` now uses `image2`.
Thus, convert these definitions to using `image2` or `''` as
appropriate, so simplifying various proofs.
This PR deliberately only addresses `vsub_set` and related definitions
for such sets of subtractions; it does not attempt to change any other
definitions in `linear_algebra/affine_space/basic` that might also be
able to use `image2` or `''` but are not such sets of subtractions,
and does not change the formulations of lemmas not involving such sets
even if a rearrangement of equalities and existential quantifiers in
some such lemmas might bring them closer to the formulations about
images of sets.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+/\- *def* vsub_set

Modified src/linear_algebra/affine_space/basic.lean




## [2020-08-19 11:58:06](https://github.com/leanprover-community/mathlib/commit/1e677e6)
chore(data/finset/basic): use `finset.map` in `sigma_eq_bind` ([#3857](https://github.com/leanprover-community/mathlib/pull/3857))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean


Modified src/data/finset/basic.lean
- \+/\- *theorem* sigma_eq_bind

Modified src/logic/embedding.lean
- \+ *lemma* coe_sigma_mk
- \+ *def* sigma_mk



## [2020-08-19 11:22:59](https://github.com/leanprover-community/mathlib/commit/a100396)
doc(linear_algebra/sesquilinear_form): add missing backtick ([#3862](https://github.com/leanprover-community/mathlib/pull/3862))
#### Estimated changes
Modified src/linear_algebra/sesquilinear_form.lean




## [2020-08-19 03:25:09](https://github.com/leanprover-community/mathlib/commit/8579a5f)
fix(test/norm_cast): fix(?) test ([#3859](https://github.com/leanprover-community/mathlib/pull/3859))
#### Estimated changes
Modified test/norm_cast.lean




## [2020-08-18 21:50:05](https://github.com/leanprover-community/mathlib/commit/425aee9)
feat(analysis/calculus) : L'Hôpital's rule, 0/0 case ([#3740](https://github.com/leanprover-community/mathlib/pull/3740))
This proves several forms of L'Hôpital's rule for computing 0/0 indeterminate forms, based on the proof given here : [Wikibooks](https://en.wikibooks.org/wiki/Calculus/L%27H%C3%B4pital%27s_Rule). See module docstring for more details.
#### Estimated changes
Created src/analysis/calculus/lhopital.lean
- \+ *theorem* lhopital_zero_right_on_Ioo
- \+ *theorem* lhopital_zero_right_on_Ico
- \+ *theorem* lhopital_zero_left_on_Ioo
- \+ *theorem* lhopital_zero_left_on_Ioc
- \+ *theorem* lhopital_zero_at_top_on_Ioi
- \+ *theorem* lhopital_zero_at_bot_on_Iio
- \+ *theorem* lhopital_zero_nhds_right
- \+ *theorem* lhopital_zero_nhds_left
- \+ *theorem* lhopital_zero_nhds'
- \+ *theorem* lhopital_zero_nhds
- \+ *theorem* lhopital_zero_at_top
- \+ *theorem* lhopital_zero_at_bot

Modified src/topology/continuous_on.lean
- \+ *lemma* eventually_nhds_within_of_eventually_nhds



## [2020-08-18 20:22:26](https://github.com/leanprover-community/mathlib/commit/5d2256d)
feat(miu_language): a formalisation of the MIU language described by D. Hofstadter in "Gödel, Escher, Bach". ([#3739](https://github.com/leanprover-community/mathlib/pull/3739))
We define an inductive type `derivable` so that `derivable x`  represents the notion that the MIU string `x` is derivable in the MIU language. We show `derivable x` is equivalent to `decstr x`, viz. the condition that `x` begins with an `M`, has no `M` in its tail, and for which `count I` is congruent to 1 or 2 modulo 3.
By showing `decidable_pred decstr`, we deduce that `derivable` is decidable.
#### Estimated changes
Created archive/miu_language/basic.lean
- \+ *def* miu_atom.repr
- \+ *def* miustr
- \+ *def* miustr.mrepr
- \+ *def* lchar_to_miustr

Created archive/miu_language/decision_nec.lean
- \+ *lemma* mod3_eq_1_or_mod3_eq_2
- \+ *lemma* goodmi
- \+ *lemma* goodm_of_rule1
- \+ *lemma* goodm_of_rule2
- \+ *lemma* goodm_of_rule3
- \+ *lemma* goodm_of_rule4
- \+ *theorem* count_equiv_one_or_two_mod3_of_derivable
- \+ *theorem* not_derivable_mu
- \+ *theorem* goodm_of_derivable
- \+ *theorem* decstr_of_der
- \+ *def* count_equiv_or_equiv_two_mul_mod3
- \+ *def* goodm
- \+ *def* decstr

Created archive/miu_language/decision_suf.lean
- \+ *lemma* der_of_der_append_repeat_U_even
- \+ *lemma* der_cons_repeat_I_repeat_U_append_of_der_cons_repeat_I_append
- \+ *lemma* add_mod2
- \+ *lemma* le_pow2_and_pow2_eq_mod3
- \+ *lemma* repeat_pow_minus_append
- \+ *lemma* der_repeat_I_of_mod3
- \+ *lemma* count_I_eq_length_of_count_U_zero_and_neg_mem
- \+ *lemma* base_case_suf
- \+ *lemma* mem_of_count_U_eq_succ
- \+ *lemma* eq_append_cons_U_of_count_U_pos
- \+ *lemma* ind_hyp_suf
- \+ *theorem* der_of_decstr

Modified docs/references.bib


Modified src/data/list/basic.lean
- \+ *theorem* exists_cons_of_ne_nil
- \+ *theorem* tail_append_singleton_of_ne_nil
- \+ *theorem* repeat_count_eq_of_count_eq_length



## [2020-08-18 17:14:51](https://github.com/leanprover-community/mathlib/commit/0854e83)
chore(algebra/euclidean_domain): docstrings ([#3816](https://github.com/leanprover-community/mathlib/pull/3816))
#### Estimated changes
Modified src/algebra/euclidean_domain.lean
- \+/\- *lemma* mod_eq_sub_mul_div
- \+/\- *lemma* mul_div_cancel_left
- \+/\- *lemma* mul_div_cancel
- \+/\- *lemma* mod_zero
- \+/\- *lemma* mod_eq_zero
- \+/\- *lemma* mod_self
- \+/\- *lemma* dvd_mod_iff
- \+/\- *lemma* lt_one
- \+/\- *lemma* val_dvd_le
- \+/\- *lemma* mod_one
- \+/\- *lemma* zero_mod
- \+/\- *lemma* div_zero
- \+/\- *lemma* zero_div
- \+/\- *lemma* div_self
- \+/\- *lemma* eq_div_of_mul_eq_left
- \+/\- *lemma* eq_div_of_mul_eq_right
- \+/\- *lemma* lcm_dvd_iff
- \+/\- *lemma* lcm_zero_left
- \+/\- *lemma* lcm_zero_right
- \+/\- *lemma* lcm_eq_zero_iff
- \+/\- *lemma* gcd_mul_lcm
- \+/\- *theorem* div_add_mod
- \+/\- *theorem* mod_lt
- \+/\- *theorem* mul_right_not_lt
- \+/\- *theorem* mul_div_assoc
- \+/\- *theorem* gcd.induction
- \+/\- *theorem* gcd_zero_left
- \+/\- *theorem* gcd_zero_right
- \+/\- *theorem* gcd_val
- \+/\- *theorem* gcd_dvd
- \+/\- *theorem* gcd_dvd_left
- \+/\- *theorem* gcd_dvd_right
- \+/\- *theorem* dvd_gcd
- \+/\- *theorem* gcd_eq_left
- \+/\- *theorem* gcd_one_left
- \+/\- *theorem* gcd_self
- \+/\- *theorem* xgcd_zero_left
- \+/\- *theorem* xgcd_aux_rec
- \+/\- *theorem* xgcd_aux_fst
- \+/\- *theorem* xgcd_aux_val
- \+/\- *theorem* xgcd_val
- \+/\- *theorem* xgcd_aux_P
- \+/\- *theorem* gcd_eq_gcd_ab
- \+/\- *theorem* dvd_lcm_left
- \+/\- *theorem* dvd_lcm_right
- \+/\- *theorem* lcm_dvd
- \+/\- *def* gcd
- \+/\- *def* xgcd_aux
- \+/\- *def* xgcd
- \+/\- *def* gcd_a
- \+/\- *def* gcd_b
- \+/\- *def* lcm



## [2020-08-18 15:37:53](https://github.com/leanprover-community/mathlib/commit/7877033)
chore(logic/basic): `and_iff_left/right_iff_imp`, `or.right_comm` ([#3854](https://github.com/leanprover-community/mathlib/pull/3854))
Also add `@[simp]` to `forall_bool` and `exists_bool`
#### Estimated changes
Modified src/data/bool.lean
- \+/\- *theorem* forall_bool
- \+/\- *theorem* exists_bool

Modified src/data/finmap.lean


Modified src/data/set/disjointed.lean


Modified src/logic/basic.lean
- \+ *theorem* and_iff_left_iff_imp
- \+ *theorem* and_iff_right_iff_imp
- \+ *theorem* or.right_comm

Modified src/set_theory/zfc.lean


Modified test/qpf.lean




## [2020-08-18 15:37:47](https://github.com/leanprover-community/mathlib/commit/cb4a5a2)
doc(field_theory/tower): correct docstring ([#3853](https://github.com/leanprover-community/mathlib/pull/3853))
#### Estimated changes
Modified src/field_theory/tower.lean
- \+/\- *theorem* dim_mul_dim



## [2020-08-18 14:01:34](https://github.com/leanprover-community/mathlib/commit/9a70533)
feat(data/option/basic): add ne_none_iff_exists ([#3856](https://github.com/leanprover-community/mathlib/pull/3856))
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* ne_none_iff_exists
- \+ *lemma* ne_none_iff_exists'



## [2020-08-18 10:28:42](https://github.com/leanprover-community/mathlib/commit/67549d9)
feat(order/filter/at_top_bot): add `at_bot` versions for (almost) all `at_top` lemmas ([#3845](https://github.com/leanprover-community/mathlib/pull/3845))
There are a few lemmas I ignored, either because I thought a `at_bot` version wouldn't be useful (e.g subsequence lemmas), because there is no "order inversing" equivalent of `monotone` (I think ?), or because I just didn't understand the statement so I was unable to tell if it was useful or not.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* at_bot_basis
- \+ *lemma* at_bot_basis'
- \+ *lemma* at_bot_ne_bot
- \+ *lemma* mem_at_bot_sets
- \+ *lemma* eventually_at_bot
- \+ *lemma* eventually_le_at_bot
- \+ *lemma* at_bot_countable_basis
- \+ *lemma* is_countably_generated_at_bot
- \+ *lemma* order_bot.at_bot_eq
- \+ *lemma* tendsto_at_bot_pure
- \+ *lemma* eventually.exists_forall_of_at_bot
- \+ *lemma* frequently_at_bot
- \+ *lemma* frequently_at_bot'
- \+ *lemma* frequently.forall_exists_of_at_bot
- \+ *lemma* map_at_bot_eq
- \+ *lemma* tendsto_at_bot_mono'
- \+ *lemma* tendsto_at_bot_mono
- \+ *lemma* inf_map_at_bot_ne_bot_iff
- \+ *lemma* exists_le_of_tendsto_at_bot
- \+ *lemma* exists_lt_of_tendsto_at_bot
- \+ *lemma* low_scores
- \+ *lemma* frequently_low_scores
- \+ *lemma* tendsto_at_bot_add_nonpos_left'
- \+ *lemma* tendsto_at_bot_add_nonpos_left
- \+ *lemma* tendsto_at_bot_add_nonpos_right'
- \+ *lemma* tendsto_at_bot_add_nonpos_right
- \+ *lemma* tendsto_at_bot_of_add_const_left
- \+ *lemma* tendsto_at_bot_of_add_const_right
- \+ *lemma* tendsto_at_bot_of_add_bdd_below_left'
- \+ *lemma* tendsto_at_bot_of_add_bdd_below_left
- \+ *lemma* tendsto_at_bot_of_add_bdd_below_right'
- \+ *lemma* tendsto_at_bot_of_add_bdd_below_right
- \+ *lemma* tendsto_at_bot_add_left_of_ge'
- \+ *lemma* tendsto_at_bot_add_left_of_ge
- \+ *lemma* tendsto_at_bot_add_right_of_ge'
- \+ *lemma* tendsto_at_bot_add_right_of_ge
- \+ *lemma* tendsto_at_bot_add_const_left
- \+ *lemma* tendsto_at_bot_add_const_right
- \+ *lemma* tendsto_at_bot_embedding
- \+ *lemma* tendsto_at_bot_at_bot_of_monotone
- \+ *lemma* tendsto_at_bot_at_bot_iff_of_monotone
- \+ *lemma* prod_at_bot_at_bot_eq
- \+ *lemma* prod_map_at_bot_eq
- \+ *lemma* map_at_bot_eq_of_gc
- \+ *lemma* tendsto_at_bot_at_bot_of_monotone'
- \+ *lemma* unbounded_of_tendsto_at_bot
- \+ *lemma* unbounded_of_tendsto_at_top'
- \+ *lemma* unbounded_of_tendsto_at_bot'
- \+ *lemma* tendsto_at_bot_of_monotone_of_filter
- \+ *lemma* tendsto_at_bot_of_monotone_of_subseq
- \+ *theorem* tendsto_at_bot_principal



## [2020-08-18 08:45:02](https://github.com/leanprover-community/mathlib/commit/67e0019)
refactor(topology/metric_space/baire): use choose! in Baire theorem ([#3852](https://github.com/leanprover-community/mathlib/pull/3852))
Use `choose!` in the proof of Baire theorem.
#### Estimated changes
Modified src/tactic/choose.lean


Modified src/topology/metric_space/baire.lean




## [2020-08-18 08:45:00](https://github.com/leanprover-community/mathlib/commit/6538274)
chore(data/set/finite): explicit `f` in `finset.preimage s f hf` ([#3851](https://github.com/leanprover-community/mathlib/pull/3851))
Otherwise pretty printer shows just `finset.preimage s _`.
#### Estimated changes
Modified src/data/finsupp/basic.lean


Modified src/data/set/finite.lean
- \+ *lemma* monotone_preimage

Modified src/field_theory/separable.lean


Modified src/linear_algebra/finsupp.lean


Modified src/order/filter/at_top_bot.lean




## [2020-08-18 08:44:58](https://github.com/leanprover-community/mathlib/commit/c356148)
feat(category_theory/abelian): pseudoelements and a four lemma ([#3803](https://github.com/leanprover-community/mathlib/pull/3803))
#### Estimated changes
Modified src/category_theory/abelian/basic.lean
- \+ *lemma* image_ι_eq_image_ι
- \+ *lemma* kernel_cokernel_eq_image_ι

Created src/category_theory/abelian/diagram_lemmas/four.lean
- \+ *lemma* mono_of_epi_of_mono_of_mono

Modified src/category_theory/abelian/exact.lean
- \+ *def* is_limit_image

Created src/category_theory/abelian/pseudoelements.lean
- \+ *lemma* app_hom
- \+ *lemma* pseudo_equal_refl
- \+ *lemma* pseudo_equal_symm
- \+ *lemma* pseudo_equal_trans
- \+ *lemma* over_coe_def
- \+ *lemma* pseudo_apply_aux
- \+ *lemma* pseudo_apply_mk
- \+ *lemma* pseudo_zero_aux
- \+ *lemma* zero_eq_zero'
- \+ *lemma* pseudo_zero_def
- \+ *lemma* zero_eq_zero
- \+ *lemma* pseudo_zero_iff
- \+ *lemma* zero_of_map_zero
- \+ *lemma* apply_eq_zero_of_comp_eq_zero
- \+ *theorem* comp_apply
- \+ *theorem* comp_comp
- \+ *theorem* apply_zero
- \+ *theorem* zero_apply
- \+ *theorem* zero_morphism_ext
- \+ *theorem* zero_morphism_ext'
- \+ *theorem* eq_zero_iff
- \+ *theorem* pseudo_injective_of_mono
- \+ *theorem* mono_of_zero_of_map_zero
- \+ *theorem* pseudo_surjective_of_epi
- \+ *theorem* epi_of_pseudo_surjective
- \+ *theorem* pseudo_exact_of_exact
- \+ *theorem* exact_of_pseudo_exact
- \+ *theorem* sub_of_eq_image
- \+ *theorem* pseudo_pullback
- \+ *def* app
- \+ *def* pseudo_equal
- \+ *def* pseudoelement.setoid
- \+ *def* pseudoelement
- \+ *def* object_to_sort
- \+ *def* over_to_sort
- \+ *def* pseudo_apply
- \+ *def* hom_to_fun
- \+ *def* pseudo_zero

Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* image_ι_comp_eq_zero

Modified src/category_theory/over.lean
- \+ *lemma* coe_hom
- \+ *def* coe_from_hom



## [2020-08-18 07:06:45](https://github.com/leanprover-community/mathlib/commit/0494807)
feat(algebra/ordered_*): cleanup and projection notation ([#3850](https://github.com/leanprover-community/mathlib/pull/3850))
Also add a few new projection notations.
#### Estimated changes
Modified src/algebra/order.lean


Modified src/algebra/ordered_field.lean


Modified src/algebra/ordered_group.lean
- \+/\- *lemma* mul_le_mul_three
- \+/\- *lemma* zero_lt_coe

Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* mul_le_mul_of_nonneg_left
- \+/\- *lemma* mul_le_mul_of_nonneg_right
- \+/\- *lemma* mul_lt_mul
- \+/\- *lemma* one_le_two
- \+/\- *lemma* mul_le_mul
- \+/\- *lemma* zero_lt_one
- \- *lemma* ordered_semiring.mul_le_mul_of_nonneg_left
- \- *lemma* ordered_semiring.mul_le_mul_of_nonneg_right



## [2020-08-18 00:46:41](https://github.com/leanprover-community/mathlib/commit/cd7c228)
chore(scripts): update nolints.txt ([#3848](https://github.com/leanprover-community/mathlib/pull/3848))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-17 21:27:17](https://github.com/leanprover-community/mathlib/commit/b68702e)
chore(field_theory/tower): generalize tower law to modules ([#3844](https://github.com/leanprover-community/mathlib/pull/3844))
#### Estimated changes
Modified src/field_theory/tower.lean


Modified src/ring_theory/algebra_tower.lean
- \+/\- *theorem* algebra_map_smul
- \+/\- *theorem* smul_left_comm



## [2020-08-17 21:27:15](https://github.com/leanprover-community/mathlib/commit/3ea8e28)
feat(tactic/choose): derive local nonempty instances ([#3842](https://github.com/leanprover-community/mathlib/pull/3842))
This allows `choose!` to work even in cases like `{A : Type} (p : A -> Prop) (h : ∀ x : A, p x → ∃ y : A, p y)`, where we don't know that `A` is nonempty because it is generic, but it can be derived from the inhabitance of other variables in the context of the `∃ y : A` statement. As requested on zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/non.20dependent.20chooser/near/207126587
#### Estimated changes
Modified src/tactic/choose.lean


Modified src/tactic/core.lean


Modified test/choose.lean




## [2020-08-17 21:27:14](https://github.com/leanprover-community/mathlib/commit/f77530e)
feat(ring_theory/localization): Generalize theorems about localization over an integral domain ([#3780](https://github.com/leanprover-community/mathlib/pull/3780))
A number of theorems about the `fraction_map` from an integral domain to its field of fractions can be generalized to apply to any `localization_map` that were the localization set doesn't contain any zero divisors. The main use for this is to show that localizing an integral domain at any set of non-zero elements is an integral domain, were previously this was only proven for the field of fractions.
I made `le_non_zero_divisors` a class so that the integral domain instance can be synthesized automatically once you show that zero isn't in the localization set, but it could be left as just a proposition instead if that seems unnecessary.
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/localization.lean
- \+ *lemma* le_non_zero_divisors_of_domain
- \+ *lemma* to_map_eq_zero_iff
- \+ *lemma* injective
- \+/\- *lemma* is_unit_map_of_injective
- \+ *def* integral_domain_of_le_non_zero_divisors
- \+ *def* integral_domain_localization



## [2020-08-17 20:43:24](https://github.com/leanprover-community/mathlib/commit/f818acb)
feat(analysis/normed_space): generalize corollaries of Hahn-Banach ([#3658](https://github.com/leanprover-community/mathlib/pull/3658))
#### Estimated changes
Modified src/analysis/normed_space/dual.lean
- \+/\- *lemma* norm_le_dual_bound
- \+/\- *lemma* inclusion_in_double_dual_isometry

Modified src/analysis/normed_space/hahn_banach.lean
- \+ *lemma* norm'_def
- \+ *lemma* norm_norm'
- \+/\- *lemma* coord_norm'
- \- *lemma* coord_self'
- \+/\- *theorem* exists_dual_vector
- \+/\- *theorem* exists_dual_vector'

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* coord_self



## [2020-08-17 17:33:37](https://github.com/leanprover-community/mathlib/commit/f8bf001)
fix(ring_theory/localization): remove coe_submodule instance ([#3832](https://github.com/leanprover-community/mathlib/pull/3832))
This coe can loop. See zulip discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Unknown.20error.20while.20type-checking.20with.20.60use.60/near/207089095
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+/\- *lemma* coe_coe_ideal
- \+/\- *lemma* mem_coe
- \+/\- *lemma* mem_zero_iff
- \+/\- *lemma* coe_one

Modified src/ring_theory/localization.lean
- \+ *lemma* mem_coe_submodule
- \- *lemma* mem_coe
- \+ *def* coe_submodule



## [2020-08-17 16:59:15](https://github.com/leanprover-community/mathlib/commit/472251b)
feat(algebra): define linear recurrences and prove basic lemmas about them ([#3829](https://github.com/leanprover-community/mathlib/pull/3829))
We define "linear recurrences", i.e assertions of the form `∀ n : ℕ, u (n + d) = a 0 * u n + a 1 * u (n+1) + ... + a (d-1) * u (n+d-1)`, and we introduce basic related lemmas and definitions (solution space, auxiliary polynomial). Currently, the most advanced theorem is : `q ^ n` is a solution iff `q` is a root of the auxiliary polynomial.
#### Estimated changes
Created src/algebra/linear_recurrence.lean
- \+ *lemma* is_sol_mk_sol
- \+ *lemma* mk_sol_eq_init
- \+ *lemma* eq_mk_of_is_sol_of_eq_init
- \+ *lemma* eq_mk_of_is_sol_of_eq_init'
- \+ *lemma* is_sol_iff_mem_sol_space
- \+ *lemma* sol_eq_of_eq_init
- \+ *lemma* sol_space_dim
- \+ *lemma* geom_sol_iff_root_char_poly
- \+ *def* is_solution
- \+ *def* mk_sol
- \+ *def* sol_space
- \+ *def* to_init
- \+ *def* tuple_succ
- \+ *def* char_poly



## [2020-08-17 15:28:54](https://github.com/leanprover-community/mathlib/commit/3edf2b2)
feat(ring_theory/DVR,padics/padic_integers): characterize ideals of DVRs, apply to `Z_p` ([#3827](https://github.com/leanprover-community/mathlib/pull/3827))
Also introduce the p-adic valuation on `Z_p`, stolen from the perfectoid project.
Coauthored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *lemma* dvd_pow

Modified src/data/padics/padic_integers.lean
- \+ *lemma* norm_p
- \+ *lemma* norm_p_pow
- \+ *lemma* norm_eq_pow_val
- \+ *lemma* valuation_zero
- \+ *lemma* valuation_one
- \+ *lemma* valuation_p
- \+ *lemma* valuation_nonneg
- \+ *lemma* mk_units_eq
- \+ *lemma* norm_units
- \+ *lemma* unit_coeff_coe
- \+ *lemma* unit_coeff_spec
- \+ *lemma* p_dvd_of_norm_lt_one
- \+ *lemma* p_nonnunit
- \+ *lemma* maximal_ideal_eq_span_p
- \+ *lemma* prime_p
- \+ *lemma* irreducible_p
- \+ *lemma* ideal_eq_span_pow_p
- \+ *def* valuation
- \+ *def* mk_units
- \+ *def* unit_coeff

Modified src/ring_theory/discrete_valuation_ring.lean
- \+ *lemma* unique_irreducible
- \+ *lemma* of_ufd_of_unique_irreducible
- \+ *lemma* aux_pid_of_ufd_of_unique_irreducible
- \+ *lemma* of_has_unit_mul_pow_irreducible_factorization
- \+ *lemma* associated_pow_irreducible
- \+ *lemma* ideal_eq_span_pow_irreducible
- \+ *theorem* irreducible_iff_uniformizer
- \+ *theorem* iff_pid_with_one_nonzero_prime
- \- *theorem* irreducible_iff_uniformiser
- \- *theorem* iff_PID_with_one_nonzero_prime
- \+ *def* has_unit_mul_pow_irreducible_factorization



## [2020-08-17 15:28:52](https://github.com/leanprover-community/mathlib/commit/d4cb237)
feat(algebra/module): define ordered semimodules and generalize convexity of functions ([#3728](https://github.com/leanprover-community/mathlib/pull/3728))
#### Estimated changes
Created src/algebra/module/ordered.lean
- \+ *lemma* smul_lt_smul_of_pos
- \+ *lemma* smul_le_smul_of_nonneg

Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex_on_const
- \+ *lemma* convex_on_iff_div
- \+/\- *lemma* linear_order.convex_on_of_lt
- \+/\- *lemma* convex_on.subset
- \+/\- *lemma* convex_on.add
- \+/\- *lemma* convex_on.smul
- \+/\- *lemma* convex_on.le_on_segment'
- \+/\- *lemma* convex_on.le_on_segment
- \+/\- *lemma* convex_on.convex_le
- \+/\- *lemma* convex_on.convex_lt
- \+/\- *lemma* convex_on.convex_epigraph
- \+/\- *lemma* convex_on_iff_convex_epigraph
- \+/\- *lemma* convex_on.comp_affine_map
- \+/\- *lemma* convex_on.comp_linear_map
- \+/\- *lemma* convex_on.translate_right
- \+/\- *lemma* convex_on.translate_left
- \- *lemma* convex_on_iff_div:
- \+/\- *def* convex_on

Modified src/analysis/convex/specific_functions.lean
- \+/\- *lemma* convex_on_pow_of_even
- \+/\- *lemma* convex_on_pow
- \+/\- *lemma* convex_on_fpow
- \+/\- *lemma* convex_on_rpow



## [2020-08-17 13:59:04](https://github.com/leanprover-community/mathlib/commit/bc72d90)
refactor(logic/basic): classical -> root, root -> decidable ([#3812](https://github.com/leanprover-community/mathlib/pull/3812))
This moves all logic lemmas with `decidable` instances into the `decidable` namespace, and moves or adds classical versions of these to the root namespace. This change hits a lot of files, mostly to remove the `classical.` prefix on explicit references to classical lemmas.
#### Estimated changes
Modified src/algebra/char_p.lean


Modified src/algebra/module/basic.lean


Modified src/algebra/order.lean


Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/category_theory/preadditive/biproducts.lean


Modified src/combinatorics/composition.lean


Modified src/data/complex/exponential.lean


Modified src/data/dfinsupp.lean


Modified src/data/equiv/basic.lean


Modified src/data/finset/basic.lean


Modified src/data/finsupp/basic.lean


Modified src/data/fintype/basic.lean
- \+/\- *lemma* mem_perms_of_list_of_mem

Modified src/data/matrix/pequiv.lean


Modified src/data/nat/prime.lean


Modified src/data/pequiv.lean


Modified src/data/polynomial/degree/basic.lean


Modified src/data/set/basic.lean


Modified src/data/set/lattice.lean


Modified src/data/support.lean


Modified src/data/zsqrtd/gaussian_int.lean


Modified src/dynamics/periodic_pts.lean


Modified src/field_theory/chevalley_warning.lean


Modified src/field_theory/separable.lean


Modified src/field_theory/splitting_field.lean


Modified src/group_theory/order_of_element.lean


Modified src/linear_algebra/basis.lean


Modified src/logic/basic.lean
- \+/\- *lemma* imp_imp_imp
- \+ *lemma* decidable.iff_iff_not_or_and_or_not
- \+/\- *lemma* iff_iff_not_or_and_or_not
- \+ *theorem* em
- \+/\- *theorem* or_not
- \+/\- *theorem* by_contradiction
- \+ *theorem* by_contra
- \+/\- *theorem* not_not
- \+/\- *theorem* of_not_not
- \+/\- *theorem* of_not_imp
- \+ *theorem* not.decidable_imp_symm
- \+/\- *theorem* not.imp_symm
- \+/\- *theorem* not_imp_comm
- \+/\- *theorem* or_iff_not_imp_left
- \+/\- *theorem* or_iff_not_imp_right
- \+/\- *theorem* not_imp_not
- \+/\- *theorem* not_or_of_imp
- \+/\- *theorem* imp_iff_not_or
- \+/\- *theorem* imp_or_distrib
- \+/\- *theorem* imp_or_distrib'
- \+/\- *theorem* not_imp
- \+/\- *theorem* peirce
- \+/\- *theorem* not_iff_not
- \+/\- *theorem* not_iff_comm
- \+/\- *theorem* not_iff
- \+/\- *theorem* iff_not_comm
- \+/\- *theorem* iff_iff_and_or_not_and_not
- \+/\- *theorem* not_and_not_right
- \+/\- *theorem* not_and_distrib
- \+/\- *theorem* or_iff_not_and_not
- \+/\- *theorem* and_iff_not_or_not
- \+/\- *theorem* not_forall
- \+/\- *theorem* not_forall_not
- \+/\- *theorem* not_exists_not
- \+/\- *theorem* forall_or_distrib_left
- \+/\- *theorem* forall_or_distrib_right
- \+/\- *theorem* not_ball
- \- *theorem* not_and_distrib'

Modified src/order/basic.lean


Modified src/order/bounded_lattice.lean


Modified src/order/filter/ultrafilter.lean


Modified src/order/lattice.lean


Modified src/order/pilex.lean


Modified src/order/rel_classes.lean


Modified src/order/zorn.lean


Modified src/ring_theory/ideal/basic.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/power_series.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/schroeder_bernstein.lean


Modified src/tactic/lint/default.lean


Modified src/tactic/lint/type_classes.lean


Modified src/tactic/omega/int/dnf.lean


Modified src/tactic/omega/int/form.lean


Modified src/tactic/omega/int/main.lean


Modified src/tactic/omega/nat/form.lean


Modified src/tactic/omega/nat/main.lean


Modified src/tactic/omega/nat/neg_elim.lean


Modified src/tactic/omega/nat/sub_elim.lean


Modified src/tactic/tauto.lean


Modified src/topology/continuous_on.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/separation.lean


Modified test/qpf.lean




## [2020-08-17 12:15:00](https://github.com/leanprover-community/mathlib/commit/1a8f6bf)
feat(lint): improved ge_or_gt linter ([#3810](https://github.com/leanprover-community/mathlib/pull/3810))
The linter will now correctly accepts occurrences of `f (≥)` and `∃ x ≥ t, b`
The linter will still raise a false positive on `∃ x y ≥ t, b` (with 2+ bound variables in a single binder that involves `>/≥`)
In contrast to the previous version of the linter, this one *does* check hypotheses.
This should reduce the `@[nolint ge_or_gt]` attributes from ~160 to ~10.
#### Estimated changes
Modified src/algebra/order.lean


Modified src/algebra/ordered_group.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/hofer.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/list/basic.lean
- \+/\- *lemma* insert_nth_remove_nth_of_ge

Modified src/data/real/cau_seq.lean


Modified src/dynamics/periodic_pts.lean


Modified src/group_theory/order_of_element.lean


Modified src/order/basic.lean


Modified src/order/complete_lattice.lean


Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean


Modified src/order/liminf_limsup.lean


Modified src/order/rel_classes.lean


Modified src/ring_theory/noetherian.lean


Modified src/tactic/lint/misc.lean


Modified src/tactic/monotonicity/lemmas.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/algebra/polynomial.lean


Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* Icc_mem_nhds

Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/sequences.lean


Modified src/topology/uniform_space/absolute_value.lean


Modified src/topology/uniform_space/cauchy.lean




## [2020-08-17 10:46:14](https://github.com/leanprover-community/mathlib/commit/2a8d7f3)
chore(analysis/normed_space/banach): correct typo ([#3840](https://github.com/leanprover-community/mathlib/pull/3840))
Correct a typo from an old global replace.
#### Estimated changes
Modified src/analysis/normed_space/banach.lean




## [2020-08-17 09:54:31](https://github.com/leanprover-community/mathlib/commit/41cbfdc)
chore(analysis/hofer): use  the new choose! ([#3839](https://github.com/leanprover-community/mathlib/pull/3839))
#### Estimated changes
Modified src/analysis/hofer.lean




## [2020-08-17 09:11:02](https://github.com/leanprover-community/mathlib/commit/626de47)
feat(linear_algebra/affine_space/combination): centroid ([#3825](https://github.com/leanprover-community/mathlib/pull/3825))
Define the centroid of points in an affine space (given by an indexed
family with a `finset` of the index type), when the underlying ring
`k` is a division ring, and prove a few lemmas about cases where this
does not involve division by zero.  For example, the centroid of a
triangle or simplex, although none of the definitions and lemmas here
require affine independence so they are all stated more generally.
(The sort of things that would be appropriate to state specifically
for the case of a simplex would be e.g. defining medians and showing
that the centroid is the intersection of any two medians.)
#### Estimated changes
Modified src/linear_algebra/affine_space/basic.lean


Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* centroid_weights_apply
- \+ *lemma* centroid_weights_eq_const
- \+ *lemma* sum_centroid_weights_eq_one_of_cast_card_ne_zero
- \+ *lemma* sum_centroid_weights_eq_one_of_card_ne_zero
- \+ *lemma* sum_centroid_weights_eq_one_of_nonempty
- \+ *lemma* sum_centroid_weights_eq_one_of_card_eq_add_one
- \+ *lemma* centroid_def
- \+ *lemma* centroid_singleton
- \+ *lemma* centroid_mem_affine_span_of_cast_card_ne_zero
- \+ *lemma* centroid_mem_affine_span_of_card_ne_zero
- \+ *lemma* centroid_mem_affine_span_of_nonempty
- \+ *lemma* centroid_mem_affine_span_of_card_eq_add_one
- \+ *def* centroid_weights
- \+ *def* centroid



## [2020-08-17 04:44:59](https://github.com/leanprover-community/mathlib/commit/6773f52)
feat(category_theory): limits in the category of indexed families ([#3737](https://github.com/leanprover-community/mathlib/pull/3737))
A continuation of [#3735](https://github.com/leanprover-community/mathlib/pull/3735), hopefully useful in [#3638](https://github.com/leanprover-community/mathlib/pull/3638).
#### Estimated changes
Created src/category_theory/limits/pi.lean
- \+ *def* cone_comp_eval
- \+ *def* cone_of_cone_comp_eval
- \+ *def* cone_of_cone_eval_is_limit
- \+ *def* has_limit_of_has_limit_comp_eval

Modified src/category_theory/pi/basic.lean




## [2020-08-17 04:10:13](https://github.com/leanprover-community/mathlib/commit/b0b5cd4)
feat(geometry/euclidean): circumradius simp lemmas ([#3834](https://github.com/leanprover-community/mathlib/pull/3834))
Mark `dist_circumcenter_eq_circumradius` as a `simp` lemma.  Also add
a variant of that lemma where the distance is the other way round so
`simp` can work with both forms.
#### Estimated changes
Modified src/geometry/euclidean.lean
- \+/\- *lemma* dist_circumcenter_eq_circumradius
- \+ *lemma* dist_circumcenter_eq_circumradius'



## [2020-08-17 03:03:18](https://github.com/leanprover-community/mathlib/commit/43337f7)
chore(data/nat/digits): refactor proof of `last_digit_ne_zero` ([#3836](https://github.com/leanprover-community/mathlib/pull/3836))
I thoroughly misunderstood why my prior attempts for [#3544](https://github.com/leanprover-community/mathlib/pull/3544) weren't working. I've refactored the proof so the `private` lemma is no longer necessary.
#### Estimated changes
Modified src/data/nat/digits.lean
- \+/\- *lemma* last_digit_ne_zero



## [2020-08-17 01:29:28](https://github.com/leanprover-community/mathlib/commit/c1fece3)
fix(tactic/refine_struct): accept synonyms for `structure` types ([#3828](https://github.com/leanprover-community/mathlib/pull/3828))
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Modified test/refine_struct.lean
- \+ *def* my_semigroup



## [2020-08-17 00:44:50](https://github.com/leanprover-community/mathlib/commit/56ed455)
chore(scripts): update nolints.txt ([#3835](https://github.com/leanprover-community/mathlib/pull/3835))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-16 20:46:14](https://github.com/leanprover-community/mathlib/commit/40214fc)
feat(ring_theory/derivations): stab on derivations ([#3688](https://github.com/leanprover-community/mathlib/pull/3688))
#### Estimated changes
Modified src/algebra/classical_lie_algebras.lean


Modified src/algebra/group/basic.lean
- \+ *lemma* eq_one_of_mul_self_left_cancel
- \+ *lemma* eq_one_of_left_cancel_mul_self
- \+ *lemma* eq_one_of_mul_self_right_cancel
- \+ *lemma* eq_one_of_right_cancel_mul_self

Modified src/algebra/group/defs.lean


Modified src/algebra/lie_algebra.lean
- \+ *lemma* commutator
- \- *lemma* add_left
- \- *lemma* add_right
- \- *lemma* alternate
- \- *lemma* jacobi
- \- *def* commutator
- \- *def* lie_ring.of_associative_ring
- \- *def* of_associative_algebra
- \- *def* matrix.lie_ring
- \- *def* matrix.lie_algebra

Modified src/algebra/module/basic.lean
- \+/\- *lemma* is_linear_map_smul

Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/hahn_banach.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *def* smul_algebra_right

Modified src/data/complex/module.lean


Modified src/data/monoid_algebra.lean


Modified src/group_theory/group_action.lean
- \+/\- *lemma* smul_assoc

Modified src/representation_theory/maschke.lean


Modified src/ring_theory/algebra.lean
- \+ *lemma* algebra_compatible_smul
- \+/\- *lemma* smul_algebra_smul_comm
- \+ *lemma* map_smul_eq_smul_map
- \+ *lemma* semimodule.restrict_scalars_smul_def
- \- *lemma* module.restrict_scalars_smul_def
- \- *lemma* smul_algebra_smul
- \+ *def* semimodule.restrict_scalars'
- \+ *def* semimodule.restrict_scalars
- \+/\- *def* subspace.restrict_scalars
- \+/\- *def* smul_algebra_right
- \+/\- *def* linear_map_algebra_module
- \- *def* module.restrict_scalars'
- \- *def* module.restrict_scalars

Created src/ring_theory/derivation.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_fn_coe
- \+ *lemma* coe_injective
- \+ *lemma* map_add
- \+ *lemma* map_zero
- \+ *lemma* map_smul
- \+ *lemma* leibniz
- \+ *lemma* map_one_eq_zero
- \+ *lemma* map_algebra_map
- \+ *lemma* add_apply
- \+ *lemma* smul_to_linear_map_coe
- \+ *lemma* Rsmul_apply
- \+ *lemma* smul_apply
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* commutator_coe_linear_map
- \+ *lemma* commutator_apply
- \+ *lemma* comp_der_apply
- \+ *theorem* ext
- \+ *def* commutator
- \+ *def* comp_der



## [2020-08-16 18:48:55](https://github.com/leanprover-community/mathlib/commit/4f2c958)
feat(tactic/interactive/choose): nondependent choose ([#3806](https://github.com/leanprover-community/mathlib/pull/3806))
Now you can write `choose!` to eliminate propositional arguments from the chosen functions.
```
example (h : ∀n m : ℕ, n < m → ∃i j, m = n + i ∨ m + j = n) : true :=
begin
  choose! i j h using h,
  guard_hyp i := ℕ → ℕ → ℕ,
  guard_hyp j := ℕ → ℕ → ℕ,
  guard_hyp h := ∀ (n m : ℕ), n < m → m = n + i n m ∨ m + j n m = n,
  trivial
end
```
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *theorem* sometimes_eq
- \+ *theorem* sometimes_spec

Modified src/tactic/basic.lean


Created src/tactic/choose.lean


Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Modified test/choose.lean




## [2020-08-16 17:15:55](https://github.com/leanprover-community/mathlib/commit/3d4f085)
chore(ring_theory/ideal): docstring for Krull's theorem and a special case ([#3831](https://github.com/leanprover-community/mathlib/pull/3831))
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+ *theorem* exists_maximal



## [2020-08-16 13:39:50](https://github.com/leanprover-community/mathlib/commit/ee74e7f)
feat(analysis/special_functions/exp_log): `tendsto real.log at_top at_top` ([#3826](https://github.com/leanprover-community/mathlib/pull/3826))
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* tendsto_log_at_top



## [2020-08-16 12:41:57](https://github.com/leanprover-community/mathlib/commit/863bf79)
feat(data/padics): more valuations, facts about norms ([#3790](https://github.com/leanprover-community/mathlib/pull/3790))
Assorted lemmas about the `p`-adics. @jcommelin and I are adding algebraic structure here as part of the Witt vector development.
Some of these declarations are stolen shamelessly from the perfectoid project.
Coauthored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/padics/padic_norm.lean
- \+ *lemma* padic_norm_p
- \+ *lemma* padic_norm_p_of_prime
- \+ *lemma* padic_norm_p_lt_one
- \+ *lemma* padic_norm_p_lt_one_of_prime

Modified src/data/padics/padic_numbers.lean
- \+ *lemma* norm_eq_pow_val
- \+ *lemma* val_eq_iff_norm_eq
- \+ *lemma* norm_values_discrete
- \+/\- *lemma* cast_eq_of_rat_of_nat
- \+/\- *lemma* cast_eq_of_rat_of_int
- \+ *lemma* norm_p
- \+ *lemma* norm_p_lt_one
- \+ *lemma* norm_p_pow
- \+ *lemma* valuation_zero
- \+ *lemma* valuation_one
- \+ *lemma* valuation_p
- \- *lemma* norm_image
- \+ *def* valuation



## [2020-08-16 11:27:24](https://github.com/leanprover-community/mathlib/commit/a6f6434)
feat(data/fin): bundled embedding ([#3822](https://github.com/leanprover-community/mathlib/pull/3822))
Add the coercion from `fin n` to `ℕ` as a bundled embedding, an
equivalent of `function.embedding.subtype`.  Once leanprover-community/lean[#359](https://github.com/leanprover-community/mathlib/pull/359) is fixed
(making `fin n` a subtype), this can go away as a duplicate, but until
then it is useful.
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* function.embedding.coe_fin
- \+ *def* function.embedding.fin



## [2020-08-16 10:08:53](https://github.com/leanprover-community/mathlib/commit/dda2dcd)
chore(data/*): doc strings on some definitions ([#3791](https://github.com/leanprover-community/mathlib/pull/3791))
Doc strings on definitions in `data.` which I could figure out what it does.
#### Estimated changes
Modified src/data/equiv/nat.lean


Modified src/data/int/parity.lean


Modified src/data/nat/enat.lean


Modified src/data/nat/totient.lean


Modified src/data/real/basic.lean




## [2020-08-16 08:37:23](https://github.com/leanprover-community/mathlib/commit/8f03035)
chore(algebra/with_one): docstrings ([#3817](https://github.com/leanprover-community/mathlib/pull/3817))
#### Estimated changes
Modified src/algebra/group/with_one.lean




## [2020-08-16 07:20:48](https://github.com/leanprover-community/mathlib/commit/20fe4a1)
feat(algebra/euclidean_domain): some cleanup ([#3752](https://github.com/leanprover-community/mathlib/pull/3752))
Lower the priority of simp-lemmas which have an equivalent version in `group_with_zero`, so that the version of `group_with_zero` is found by `squeeze_simp` for types that have both structures.
Add docstrings
Remove outdated comment
#### Estimated changes
Modified src/algebra/euclidean_domain.lean
- \+/\- *lemma* div_zero
- \+/\- *lemma* zero_div
- \+/\- *lemma* div_self

Modified src/analysis/special_functions/trigonometric.lean


Modified src/analysis/specific_limits.lean




## [2020-08-16 06:05:27](https://github.com/leanprover-community/mathlib/commit/490d3ce)
refactor(data/list/palindrome): use decidable_of_iff' ([#3823](https://github.com/leanprover-community/mathlib/pull/3823))
Follow-up to [#3729](https://github.com/leanprover-community/mathlib/pull/3729).
`decidable_of_iff'` allows for omitting the `eq.symm`.
#### Estimated changes
Modified src/data/list/palindrome.lean




## [2020-08-16 06:05:25](https://github.com/leanprover-community/mathlib/commit/62374f7)
doc(data/real/card): docs and cleanup ([#3815](https://github.com/leanprover-community/mathlib/pull/3815))
#### Estimated changes
Modified src/data/real/cardinality.lean
- \+/\- *lemma* mk_real
- \+/\- *lemma* mk_univ_real
- \+/\- *lemma* mk_Ioi_real
- \+/\- *lemma* mk_Ici_real
- \+/\- *lemma* mk_Iio_real
- \+/\- *lemma* mk_Iic_real
- \+/\- *lemma* mk_Ioo_real
- \+/\- *lemma* mk_Ico_real
- \+/\- *lemma* mk_Icc_real
- \+/\- *lemma* mk_Ioc_real



## [2020-08-16 06:05:24](https://github.com/leanprover-community/mathlib/commit/8325cf6)
feat(*): reorder implicit arguments in tsum, supr, infi ([#3809](https://github.com/leanprover-community/mathlib/pull/3809))
This is helpful for a future version of the `ge_or_gt` linter to recognize binders: the binding type is the (implicit) argument directly before the binding body.
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+/\- *def* supr
- \+/\- *def* infi

Modified src/tactic/converter/binders.lean


Modified src/topology/algebra/infinite_sum.lean
- \+/\- *def* tsum



## [2020-08-16 06:05:21](https://github.com/leanprover-community/mathlib/commit/dba3018)
feat(category_theory): the category of indexed families of objects ([#3735](https://github.com/leanprover-community/mathlib/pull/3735))
Pulling out a definition from [#3638](https://github.com/leanprover-community/mathlib/pull/3638), and add some associated basic material.
#### Estimated changes
Modified src/category_theory/graded_object.lean
- \- *lemma* id_apply
- \- *lemma* comp_apply
- \+/\- *def* comap_eq
- \- *def* comap
- \- *def* comap_id
- \- *def* comap_comp

Created src/category_theory/pi/basic.lean
- \+ *lemma* id_apply
- \+ *lemma* comp_apply
- \+ *def* eval
- \+ *def* comap
- \+ *def* comap_id
- \+ *def* comap_comp
- \+ *def* comap_eval_iso_eval
- \+ *def* sum
- \+ *def* pi

Modified src/category_theory/products/associator.lean


Modified src/category_theory/products/basic.lean




## [2020-08-16 06:05:19](https://github.com/leanprover-community/mathlib/commit/3c2ed2a)
feat(topology/sheaves): construct sheaves of functions ([#3608](https://github.com/leanprover-community/mathlib/pull/3608))
# Sheaf conditions for presheaves of (continuous) functions.
We show that
* `Top.sheaf_condition.to_Type`: not-necessarily-continuous functions into a type form a sheaf
* `Top.sheaf_condition.to_Types`: in fact, these may be dependent functions into a type family
* `Top.sheaf_condition.to_Top`: continuous functions into a topological space form a sheaf
#### Estimated changes
Modified src/topology/sheaves/presheaf_of_functions.lean
- \+ *lemma* presheaf_to_Type_obj
- \+ *lemma* presheaf_to_Type_map
- \+ *def* presheaf_to_Types
- \+ *def* presheaf_to_Type

Created src/topology/sheaves/sheaf_of_functions.lean
- \+ *def* to_Types
- \+ *def* to_Type
- \+ *def* forget_continuity
- \+ *def* to_Top



## [2020-08-16 06:05:17](https://github.com/leanprover-community/mathlib/commit/765e460)
feat(ring_theory/polynomial/homogeneous): definition and basic props ([#3223](https://github.com/leanprover-community/mathlib/pull/3223))
This PR also move ring_theory/polynomial.lean to
ring_theory/polynomial/basic.lean
This PR is part of bringing symmetric polynomials to mathlib,
and besided that, I also expect to add binomial polynomials
and Chebyshev polynomials in the future.
Altogether, this motivates the starting of a ring_theory/polynomial
directory.
The file basic.lean may need cleaning or splitting at some point.
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *lemma* eq_zero_iff
- \+ *lemma* ne_zero_iff
- \+ *lemma* exists_coeff_ne_zero
- \+ *lemma* coeff_eq_zero_of_total_degree_lt

Created src/ring_theory/polynomial/homogeneous.lean
- \+ *lemma* is_homogeneous_monomial
- \+ *lemma* is_homogeneous_C
- \+ *lemma* is_homogeneous_zero
- \+ *lemma* is_homogeneous_one
- \+ *lemma* is_homogeneous_X
- \+ *lemma* coeff_eq_zero
- \+ *lemma* inj_right
- \+ *lemma* add
- \+ *lemma* sum
- \+ *lemma* mul
- \+ *lemma* prod
- \+ *lemma* total_degree
- \+ *lemma* homogeneous_component_apply
- \+ *lemma* homogeneous_component_is_homogeneous
- \+ *lemma* homogeneous_component_zero
- \+ *lemma* homogeneous_component_eq_zero'
- \+ *lemma* homogeneous_component_eq_zero
- \+ *lemma* sum_homogeneous_component
- \+ *def* is_homogeneous
- \+ *def* homogeneous_component



## [2020-08-16 04:46:02](https://github.com/leanprover-community/mathlib/commit/b1e7fb2)
feat (category_theory/over): composition of `over.map` ([#3798](https://github.com/leanprover-community/mathlib/pull/3798))
Filtering in some defs from the topos project.
~~Depends on [#3797](https://github.com/leanprover-community/mathlib/pull/3797).~~
#### Estimated changes
Modified src/category_theory/over.lean
- \+ *def* map_id
- \+ *def* map_comp



## [2020-08-16 04:46:00](https://github.com/leanprover-community/mathlib/commit/1037a3a)
feat(algebra/homology, category_theory/abelian, algebra/category/Module): exactness ([#3784](https://github.com/leanprover-community/mathlib/pull/3784))
We define what it means for two maps `f` and `g` to be exact and show that for R-modules, this is the case if and only if `range f = ker g`.
#### Estimated changes
Modified src/algebra/category/Module/abelian.lean
- \+ *theorem* exact_iff

Created src/algebra/homology/exact.lean
- \+ *lemma* kernel_comp_cokernel
- \+ *lemma* comp_eq_zero_of_exact
- \+ *lemma* fork_ι_comp_cofork_π

Modified src/algebra/homology/homology.lean


Modified src/algebra/homology/image_to_kernel_map.lean
- \- *def* image_to_kernel_map

Modified src/category_theory/abelian/basic.lean
- \+/\- *lemma* image_eq_image
- \+/\- *lemma* full_image_factorisation
- \+ *def* non_preadditive_abelian

Created src/category_theory/abelian/exact.lean
- \+ *theorem* exact_iff
- \+ *theorem* exact_iff'

Modified src/category_theory/limits/limits.lean
- \+ *lemma* cone_point_unique_up_to_iso_hom_comp
- \+ *lemma* cone_point_unique_up_to_iso_inv_comp
- \+ *lemma* comp_cocone_point_unique_up_to_iso_hom
- \+ *lemma* comp_cocone_point_unique_up_to_iso_inv
- \+ *lemma* limit.cone_point_unique_up_to_iso_hom_comp
- \+ *lemma* limit.cone_point_unique_up_to_iso_inv_comp
- \+ *lemma* colimit.comp_cocone_point_unique_up_to_iso_hom
- \+ *lemma* colimit.comp_cocone_point_unique_up_to_iso_inv

Modified src/linear_algebra/basic.lean
- \+ *lemma* ker_le_range_iff



## [2020-08-16 04:45:58](https://github.com/leanprover-community/mathlib/commit/2c930a3)
refactor(algebra/gcd_monoid, ring_theory/multiplicity): generalize normalization_domain, gcd_domain, multiplicity ([#3779](https://github.com/leanprover-community/mathlib/pull/3779))
* generalize `normalization_domain`, `gcd_domain`, `multiplicity` to not reference addition and subtraction
* make `gcd_monoid` and `normalization_monoid` into mixins
* add instances of `normalization_monoid` for `nat`, `associates`
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *theorem* units_eq_one
- \+/\- *theorem* coe_unit_eq_one

Renamed src/algebra/gcd_domain.lean to src/algebra/gcd_monoid.lean
- \+ *lemma* normalize_apply
- \+/\- *lemma* normalize_zero
- \+/\- *lemma* normalize_one
- \+/\- *lemma* normalize_coe_units
- \+/\- *lemma* dvd_normalize_iff
- \+/\- *lemma* normalize_dvd_iff
- \+/\- *lemma* coe_gcd
- \+/\- *lemma* coe_lcm
- \+/\- *lemma* nat_abs_gcd
- \+/\- *lemma* nat_abs_lcm
- \+ *lemma* units_eq_one
- \+ *lemma* norm_unit_eq_one
- \+ *lemma* normalize_eq
- \+/\- *theorem* norm_unit_one
- \+/\- *theorem* norm_unit_mul_norm_unit
- \+/\- *theorem* normalize_idem
- \+ *theorem* prime_of_irreducible
- \+ *theorem* irreducible_iff_prime
- \- *theorem* normalize_mul
- \+/\- *def* normalize

Modified src/data/nat/basic.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/polynomial/field_division.lean
- \+/\- *lemma* degree_normalize

Modified src/data/real/irrational.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/ring_theory/multiplicity.lean
- \+/\- *lemma* ne_zero_of_finite
- \+/\- *lemma* min_le_multiplicity_add
- \+/\- *def* multiplicity

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *def* unique_factorization_domain.to_gcd_monoid
- \- *def* unique_factorization_domain.to_gcd_domain



## [2020-08-16 03:16:51](https://github.com/leanprover-community/mathlib/commit/ae8abf3)
chore(order/rel_iso): rename order_iso and order_embedding to rel_iso and rel_embedding ([#3750](https://github.com/leanprover-community/mathlib/pull/3750))
renames `order_iso` and `order_embedding`, to make it clear they apply to all binary relations
makes room for a new definition of `order_embedding` that will deal with order instances
#### Estimated changes
Modified scripts/nolints.txt


Modified src/data/equiv/encodable/basic.lean


Modified src/data/equiv/list.lean


Modified src/data/finsupp/lattice.lean
- \+ *lemma* rel_iso_multiset_apply
- \+ *lemma* rel_iso_multiset_symm_apply
- \+ *lemma* rel_embedding_to_fun_apply
- \- *lemma* order_iso_multiset_apply
- \- *lemma* order_iso_multiset_symm_apply
- \- *lemma* order_embedding_to_fun_apply
- \+ *def* rel_iso_multiset
- \+ *def* rel_embedding_to_fun
- \- *def* order_iso_multiset
- \- *def* order_embedding_to_fun

Modified src/data/setoid/basic.lean
- \+/\- *def* correspondence

Modified src/data/setoid/partition.lean
- \+ *def* partition.rel_iso
- \- *def* partition.order_iso

Modified src/group_theory/congruence.lean
- \+/\- *def* correspondence

Modified src/linear_algebra/basic.lean
- \+ *def* map_subtype.rel_iso
- \+ *def* map_subtype.le_rel_embedding
- \+ *def* map_subtype.lt_rel_embedding
- \+ *def* comap_mkq.rel_iso
- \+ *def* comap_mkq.le_rel_embedding
- \+ *def* comap_mkq.lt_rel_embedding
- \- *def* map_subtype.order_iso
- \- *def* map_subtype.le_order_embedding
- \- *def* map_subtype.lt_order_embedding
- \- *def* comap_mkq.order_iso
- \- *def* comap_mkq.le_order_embedding
- \- *def* comap_mkq.lt_order_embedding

Modified src/order/galois_connection.lean
- \+ *theorem* rel_iso.to_galois_connection
- \- *theorem* order_iso.to_galois_connection

Modified src/order/ord_continuous.lean
- \+ *lemma* coe_to_le_rel_embedding
- \+ *lemma* coe_to_lt_rel_embedding
- \- *lemma* coe_to_le_order_embedding
- \- *lemma* coe_to_lt_order_embedding
- \+ *def* to_le_rel_embedding
- \+ *def* to_lt_rel_embedding
- \- *def* to_le_order_embedding
- \- *def* to_lt_order_embedding

Deleted src/order/order_iso.lean
- \- *lemma* injective_of_increasing
- \- *lemma* to_order_embedding_eq_coe
- \- *lemma* coe_coe_fn
- \- *lemma* ord''
- \- *lemma* coe_one
- \- *lemma* coe_mul
- \- *lemma* mul_apply
- \- *lemma* inv_apply_self
- \- *lemma* apply_inv_self
- \- *lemma* order_iso.map_bot
- \- *lemma* order_iso.map_top
- \- *lemma* order_embedding.map_inf_le
- \- *lemma* order_iso.map_inf
- \- *lemma* order_embedding.le_map_sup
- \- *lemma* order_iso.map_sup
- \- *theorem* preimage_equivalence
- \- *theorem* injective
- \- *theorem* ord
- \- *theorem* coe_fn_mk
- \- *theorem* coe_fn_to_embedding
- \- *theorem* coe_fn_inj
- \- *theorem* refl_apply
- \- *theorem* trans_apply
- \- *theorem* eq_preimage
- \- *theorem* of_monotone_coe
- \- *theorem* coe_fn_to_equiv
- \- *theorem* to_equiv_injective
- \- *theorem* coe_fn_injective
- \- *theorem* ext
- \- *theorem* coe_fn_symm_mk
- \- *theorem* apply_symm_apply
- \- *theorem* symm_apply_apply
- \- *theorem* rel_symm_apply
- \- *theorem* symm_apply_rel
- \- *theorem* of_surjective_coe
- \- *theorem* subrel_val
- \- *theorem* order_embedding_apply
- \- *theorem* order_embedding.cod_restrict_apply
- \- *def* rsymm
- \- *def* preimage
- \- *def* of_monotone
- \- *def* lt_embedding_of_le_embedding
- \- *def* fin.val.order_embedding
- \- *def* fin_fin.order_embedding
- \- *def* to_order_embedding
- \- *def* sum_lex_congr
- \- *def* prod_lex_congr
- \- *def* set_coe_embedding
- \- *def* subrel
- \- *def* order_embedding.cod_restrict

Modified src/order/order_iso_nat.lean


Created src/order/rel_iso.lean
- \+ *lemma* injective_of_increasing
- \+ *lemma* to_rel_embedding_eq_coe
- \+ *lemma* coe_coe_fn
- \+ *lemma* map_rel_iff''
- \+ *lemma* coe_one
- \+ *lemma* coe_mul
- \+ *lemma* mul_apply
- \+ *lemma* inv_apply_self
- \+ *lemma* apply_inv_self
- \+ *lemma* rel_iso.map_bot
- \+ *lemma* rel_iso.map_top
- \+ *lemma* rel_embedding.map_inf_le
- \+ *lemma* rel_iso.map_inf
- \+ *lemma* rel_embedding.le_map_sup
- \+ *lemma* rel_iso.map_sup
- \+ *theorem* preimage_equivalence
- \+ *theorem* injective
- \+ *theorem* map_rel_iff
- \+ *theorem* coe_fn_mk
- \+ *theorem* coe_fn_to_embedding
- \+ *theorem* coe_fn_inj
- \+ *theorem* refl_apply
- \+ *theorem* trans_apply
- \+ *theorem* eq_preimage
- \+ *theorem* of_monotone_coe
- \+ *theorem* coe_fn_to_equiv
- \+ *theorem* to_equiv_injective
- \+ *theorem* coe_fn_injective
- \+ *theorem* ext
- \+ *theorem* coe_fn_symm_mk
- \+ *theorem* apply_symm_apply
- \+ *theorem* symm_apply_apply
- \+ *theorem* rel_symm_apply
- \+ *theorem* symm_apply_rel
- \+ *theorem* of_surjective_coe
- \+ *theorem* subrel_val
- \+ *theorem* rel_embedding_apply
- \+ *theorem* rel_embedding.cod_restrict_apply
- \+ *def* rsymm
- \+ *def* preimage
- \+ *def* of_monotone
- \+ *def* lt_embedding_of_le_embedding
- \+ *def* fin.val.rel_embedding
- \+ *def* fin_fin.rel_embedding
- \+ *def* to_rel_embedding
- \+ *def* sum_lex_congr
- \+ *def* prod_lex_congr
- \+ *def* set_coe_embedding
- \+ *def* subrel
- \+ *def* rel_embedding.cod_restrict

Modified src/order/semiconj_Sup.lean


Modified src/ring_theory/ideal/operations.lean
- \+ *def* rel_iso_of_surjective
- \+ *def* le_rel_embedding_of_surjective
- \+ *def* lt_rel_embedding_of_surjective
- \+ *def* rel_iso_of_bijective
- \- *def* order_iso_of_surjective
- \- *def* le_order_embedding_of_surjective
- \- *def* lt_order_embedding_of_surjective
- \- *def* order_iso_of_bijective

Modified src/ring_theory/localization.lean
- \+ *def* le_rel_embedding
- \- *def* le_order_embedding

Modified src/ring_theory/noetherian.lean


Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* aleph_idx.rel_iso_coe
- \+ *theorem* aleph'.rel_iso_coe
- \- *theorem* aleph_idx.order_iso_coe
- \- *theorem* aleph'.order_iso_coe
- \+ *def* aleph_idx.rel_iso
- \+ *def* aleph'.rel_iso
- \+/\- *def* aleph'
- \- *def* aleph_idx.order_iso
- \- *def* aleph'.order_iso

Modified src/set_theory/cofinality.lean
- \+ *theorem* rel_iso.cof.aux
- \+ *theorem* rel_iso.cof
- \+/\- *theorem* cof_cof
- \- *theorem* order_iso.cof.aux
- \- *theorem* order_iso.cof

Modified src/set_theory/ordinal.lean
- \+ *lemma* rel_iso_enum'
- \+ *lemma* rel_iso_enum
- \- *lemma* order_iso_enum'
- \- *lemma* order_iso_enum
- \+/\- *theorem* coe_fn_mk
- \+ *theorem* coe_fn_to_rel_embedding
- \+/\- *theorem* coe_coe_fn
- \+/\- *theorem* equiv_lt_apply
- \+/\- *theorem* equiv_lt_top
- \+/\- *theorem* collapse_F.lt
- \+/\- *theorem* collapse_F.not_lt
- \+/\- *theorem* collapse_apply
- \+ *theorem* ord.rel_embedding_coe
- \- *theorem* coe_fn_to_order_embedding
- \- *theorem* ord.order_embedding_coe
- \+/\- *def* of_iso
- \+/\- *def* antisymm
- \+/\- *def* equiv_lt
- \+/\- *def* collapse_F
- \+/\- *def* collapse
- \+ *def* rel_iso_out
- \+/\- *def* typein_iso
- \+ *def* ord.rel_embedding
- \- *def* order_iso_out
- \- *def* ord.order_embedding

Modified src/set_theory/ordinal_arithmetic.lean




## [2020-08-16 01:06:39](https://github.com/leanprover-community/mathlib/commit/55d06a9)
chore(scripts): update nolints.txt ([#3820](https://github.com/leanprover-community/mathlib/pull/3820))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-16 01:06:37](https://github.com/leanprover-community/mathlib/commit/bf51f82)
feat(ring_theory/integral_closure): Rings lying within an integral extension are integral extensions ([#3781](https://github.com/leanprover-community/mathlib/pull/3781))
Proofs that if an algebra tower is integral then so are the two extensions making up the tower. I needed these for another proof I'm working on, but it seemed reasonable to create a smaller PR now since they are basically self contained.
#### Estimated changes
Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_integral_of_surjective
- \+ *lemma* is_integral_tower_bot_of_is_integral
- \+ *lemma* is_integral_tower_top_of_is_integral



## [2020-08-16 01:06:35](https://github.com/leanprover-community/mathlib/commit/a991854)
feat(category_theory/limits): a Fubini theorem ([#3732](https://github.com/leanprover-community/mathlib/pull/3732))
#### Estimated changes
Modified src/category_theory/currying.lean


Created src/category_theory/limits/fubini.lean
- \+ *lemma* diagram_of_cones.mk_of_has_limits_cone_points
- \+ *lemma* limit_uncurry_iso_limit_comp_lim_hom_π_π
- \+ *lemma* limit_uncurry_iso_limit_comp_lim_inv_π
- \+ *lemma* limit_iso_limit_curry_comp_lim_hom_π_π
- \+ *lemma* limit_iso_limit_curry_comp_lim_inv_π
- \+ *def* diagram_of_cones.cone_points
- \+ *def* cone_of_cone_uncurry
- \+ *def* cone_of_cone_uncurry_is_limit
- \+ *def* diagram_of_cones.mk_of_has_limits
- \+ *def* limit_uncurry_iso_limit_comp_lim
- \+ *def* limit_iso_limit_curry_comp_lim

Modified src/category_theory/limits/limits.lean




## [2020-08-15 23:34:47](https://github.com/leanprover-community/mathlib/commit/ad8c7e5)
chore(algebra/group/defs): docstrings ([#3819](https://github.com/leanprover-community/mathlib/pull/3819))
#### Estimated changes
Modified src/algebra/group/defs.lean




## [2020-08-15 23:34:45](https://github.com/leanprover-community/mathlib/commit/ad8dcaf)
chore(algebra/field): docstrings ([#3814](https://github.com/leanprover-community/mathlib/pull/3814))
#### Estimated changes
Modified src/algebra/field.lean




## [2020-08-15 23:34:43](https://github.com/leanprover-community/mathlib/commit/598c091)
chore(tactic/squeeze): format `simp only []` as `simp only` ([#3811](https://github.com/leanprover-community/mathlib/pull/3811))
fixes [#3150](https://github.com/leanprover-community/mathlib/pull/3150)
#### Estimated changes
Modified src/tactic/squeeze.lean




## [2020-08-15 23:34:42](https://github.com/leanprover-community/mathlib/commit/e75ada7)
docs(category_theory/limits/cones): cones documentation and equivalence fixup ([#3795](https://github.com/leanprover-community/mathlib/pull/3795))
Mostly adding documentation in `ct.limits.cones`, but also shortened a couple of proofs. I also adjusted a couple of statements for `is_equivalence` to match the `is_equivalence` projections which are meant to be used (these statements were only used for cones anyway).
#### Estimated changes
Modified src/category_theory/equivalence.lean
- \+ *lemma* inv_fun_id_inv_comp
- \- *lemma* counit_inv_functor_comp

Modified src/category_theory/limits/cones.lean
- \+ *def* map_cone_inv_map_cone



## [2020-08-15 23:34:40](https://github.com/leanprover-community/mathlib/commit/db99f67)
docs(category_theory/adjunction): document convenience constructors for adjunctions ([#3788](https://github.com/leanprover-community/mathlib/pull/3788))
As mentioned here: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/monoid.20object/near/204930460
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean




## [2020-08-15 22:44:14](https://github.com/leanprover-community/mathlib/commit/cd1c00d)
chore(algebra/associated): docstrings ([#3813](https://github.com/leanprover-community/mathlib/pull/3813))
#### Estimated changes
Modified src/algebra/associated.lean




## [2020-08-15 22:09:09](https://github.com/leanprover-community/mathlib/commit/8f75f96)
feat(geometry/euclidean): circumcenter and circumradius ([#3693](https://github.com/leanprover-community/mathlib/pull/3693))
Show that every simplex in a Euclidean affine space has a unique
circumcenter (in the affine subspace spanned by that simplex) and
circumradius.  There are four main pieces, which all seem closely
enough related to put them all together in the same PR.  Both (b) and
(c) have quite long proofs, but I don't see obvious pieces to extract
from them.
(a) Various lemmas about `orthogonal_projection` in relation to points
equidistant from families of points.
(b) The induction step for the existence and uniqueness of the
(circumcenter, circumradius) pair, `exists_unique_dist_eq_of_insert`
(this is actually slightly more general than is needed for the
induction; it includes going from a set of points that has a unique
circumcenter and circumradius despite being infinite or not affine
independent, to such a unique circumcenter and circumradius when
another point is added outside their affine subspace).  This is
essentially just a calculation using an explicit expression for the
distance of the circumcenter of the new set of points from its
orthogonal projection, but still involves quite a lot of manipulation
to get things down to a form `field_simp, ring` can handle.
(c) The actual induction
`exists_unique_dist_eq_of_affine_independent`, giving a unique
(circumcenter, circumradius) pair for for any affine independent
family indexed by a `fintype`, by induction on the cardinality of that
`fintype` and using the result from (b).  Given (b), this is
essentially a lot of manipulation of trivialities.
(d) Extracting definitions and basic properties of `circumcenter` and
`circumradius` from the previous result.
#### Estimated changes
Modified src/geometry/euclidean.lean
- \+ *lemma* dist_eq_iff_dist_orthogonal_projection_eq
- \+ *lemma* dist_set_eq_iff_dist_orthogonal_projection_eq
- \+ *lemma* exists_dist_eq_iff_exists_dist_orthogonal_projection_eq
- \+ *lemma* exists_unique_dist_eq_of_insert
- \+ *lemma* exists_unique_dist_eq_of_affine_independent
- \+ *lemma* circumcenter_circumradius_unique_dist_eq
- \+ *lemma* circumcenter_mem_affine_span
- \+ *lemma* dist_circumcenter_eq_circumradius
- \+ *lemma* eq_circumcenter_of_dist_eq
- \+ *lemma* eq_circumradius_of_dist_eq
- \+ *def* circumcenter_circumradius
- \+ *def* circumcenter
- \+ *def* circumradius



## [2020-08-15 20:42:02](https://github.com/leanprover-community/mathlib/commit/b97b08b)
fix(*): remove usages of ge/gt ([#3808](https://github.com/leanprover-community/mathlib/pull/3808))
These were not caught by the old `ge_or_gt` linter, but they will be caught by the new (upcoming) `ge_or_gt` linter.
The `nolint` flags are not yet removed, this will happen in a later PR.
Renamings:
```
char_is_prime_of_ge_two -> char_is_prime_of_two_le
dist_eq_sub_of_ge -> dist_eq_sub_of_le_right
gt_of_mul_lt_mul_neg_right -> lt_of_mul_lt_mul_neg_right
```
#### Estimated changes
Modified scripts/nolints.txt


Modified src/algebra/char_p.lean
- \+ *theorem* char_is_prime_of_two_le
- \- *theorem* char_is_prime_of_ge_two

Modified src/algebra/order_functions.lean
- \+/\- *lemma* min_le_add_of_nonneg_right
- \+/\- *lemma* min_le_add_of_nonneg_left
- \+/\- *lemma* max_le_add_of_nonneg

Modified src/data/nat/basic.lean
- \+/\- *theorem* eq_of_mul_eq_mul_right

Modified src/data/nat/dist.lean
- \+ *theorem* dist_eq_sub_of_le_right
- \- *theorem* dist_eq_sub_of_ge

Modified src/data/num/lemmas.lean
- \+/\- *theorem* cmp_to_nat
- \+/\- *theorem* pred_to_nat
- \+/\- *theorem* cmp_to_int

Modified src/data/padics/padic_numbers.lean
- \+/\- *lemma* norm_nonneg
- \+/\- *lemma* defn
- \+/\- *lemma* padic_norm_e_lim_le
- \+/\- *theorem* rat_dense'
- \+/\- *theorem* rat_dense

Modified src/data/polynomial/degree/basic.lean
- \+/\- *lemma* degree_eq_iff_nat_degree_eq_of_pos

Modified src/data/real/basic.lean
- \+/\- *lemma* le_of_forall_epsilon_le

Modified src/data/real/cau_seq.lean
- \+/\- *theorem* cauchy₂
- \+/\- *theorem* cauchy₃

Modified src/data/real/hyperreal.lean
- \+/\- *lemma* infinite_pos_def
- \+/\- *lemma* pos_of_infinite_pos
- \+/\- *lemma* infinite_pos_iff_infinite_and_pos
- \+/\- *lemma* infinite_pos_iff_infinite_of_pos
- \+/\- *lemma* infinite_pos_iff_infinite_of_nonneg
- \+/\- *theorem* lt_of_pos_of_infinitesimal
- \+/\- *theorem* lt_neg_of_pos_of_infinitesimal
- \+/\- *theorem* gt_of_neg_of_infinitesimal
- \+/\- *def* infinite_pos

Modified src/data/real/nnreal.lean
- \+/\- *lemma* le_of_forall_epsilon_le
- \+/\- *lemma* le_of_real_iff_coe_le
- \+/\- *lemma* of_real_lt_iff_lt_coe

Modified src/order/basic.lean


Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* map_div_at_top_eq_nat

Modified src/order/galois_connection.lean
- \+/\- *lemma* galois_connection_mul_div

Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* add_absorp_iff

Modified src/tactic/linarith/lemmas.lean
- \+/\- *lemma* mul_neg
- \+/\- *lemma* mul_nonpos
- \+/\- *lemma* mul_eq

Modified src/tactic/monotonicity/lemmas.lean
- \+ *lemma* lt_of_mul_lt_mul_neg_right
- \- *lemma* gt_of_mul_lt_mul_neg_right

Modified src/topology/algebra/ordered.lean
- \+/\- *theorem* gt_mem_sets_of_Liminf_gt

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/metric_space/hausdorff_distance.lean
- \+/\- *lemma* Hausdorff_dist_le_of_inf_dist



## [2020-08-15 20:42:00](https://github.com/leanprover-community/mathlib/commit/36ced83)
chore(linear_algebra/matrix): format doc using markdown ([#3807](https://github.com/leanprover-community/mathlib/pull/3807))
#### Estimated changes
Modified src/linear_algebra/matrix.lean




## [2020-08-15 20:41:57](https://github.com/leanprover-community/mathlib/commit/26f2d4e)
docs(data/sum): fix typo in sum.is_right docs ([#3805](https://github.com/leanprover-community/mathlib/pull/3805))
#### Estimated changes
Modified src/data/sum.lean




## [2020-08-15 20:41:56](https://github.com/leanprover-community/mathlib/commit/9339a34)
chore(data/list/defs): docstring ([#3804](https://github.com/leanprover-community/mathlib/pull/3804))
#### Estimated changes
Modified src/data/list/defs.lean
- \- *def* find_indexes_aux



## [2020-08-15 20:41:54](https://github.com/leanprover-community/mathlib/commit/7f1a489)
fix(algebra/order): restore choiceless theorems ([#3799](https://github.com/leanprover-community/mathlib/pull/3799))
The classical_decidable linter commit made these choiceless proofs use choice
again, making them duplicates of other theorems not in the `decidable.`
namespace.
#### Estimated changes
Modified src/algebra/order.lean
- \+/\- *lemma* lt_or_eq_of_le
- \+/\- *lemma* eq_or_lt_of_le
- \+/\- *lemma* le_iff_lt_or_eq
- \+/\- *lemma* le_of_not_lt
- \+/\- *lemma* not_lt
- \+/\- *lemma* lt_or_le
- \+/\- *lemma* le_or_lt
- \+/\- *lemma* lt_trichotomy
- \+/\- *lemma* lt_or_gt_of_ne
- \+/\- *lemma* ne_iff_lt_or_gt
- \+/\- *lemma* le_imp_le_of_lt_imp_lt
- \+/\- *lemma* le_imp_le_iff_lt_imp_lt
- \+/\- *lemma* le_iff_le_iff_lt_iff_lt



## [2020-08-15 20:41:52](https://github.com/leanprover-community/mathlib/commit/2e890e6)
feat(category_theory/comma): constructing isos in the comma,over,under cats ([#3797](https://github.com/leanprover-community/mathlib/pull/3797))
Constructors to give isomorphisms in comma, over and under categories - essentially these just let you omit checking one of the commuting squares using the fact that the components are iso and the other square works.
#### Estimated changes
Modified src/category_theory/comma.lean
- \+ *def* iso_mk

Modified src/category_theory/over.lean
- \+ *lemma* iso_mk_hom_left
- \+ *lemma* iso_mk_inv_left
- \+ *lemma* iso_mk_hom_right
- \+ *lemma* iso_mk_inv_right
- \- *lemma* mk_left
- \- *lemma* mk_hom
- \+ *def* iso_mk
- \+/\- *def* forget



## [2020-08-15 20:41:50](https://github.com/leanprover-community/mathlib/commit/c9bf6f2)
feat(linear_algebra/affine_space/independent): affinely independent sets ([#3794](https://github.com/leanprover-community/mathlib/pull/3794))
Prove variants of `affine_independent_iff_linear_independent_vsub`
that relate affine independence for a set of points (as opposed to an
indexed family of points) to linear independence for a set of vectors,
so facilitating linking to results such as `exists_subset_is_basis`
expressed in terms of linearly independent sets of vectors.  There are
two variants, depending on which of the set of points or the set of
vectors is given as a hypothesis.
Thus, applying `exists_subset_is_basis`, deduce that if `k` is a
field, any affinely independent set of points can be extended to such
a set that spans the whole space.
Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/linear.20suffering
#### Estimated changes
Modified src/linear_algebra/affine_space/basic.lean
- \+ *lemma* affine_span_singleton_union_vadd_eq_top_of_span_eq_top

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_independent_set_iff_linear_independent_vsub
- \+ *lemma* linear_independent_set_iff_affine_independent_vadd_union_singleton
- \+ *lemma* exists_subset_affine_independent_affine_span_eq_top



## [2020-08-15 20:41:48](https://github.com/leanprover-community/mathlib/commit/ef3ba8b)
docs(category_theory/adjunction): lint some adjunction defs ([#3793](https://github.com/leanprover-community/mathlib/pull/3793))
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean




## [2020-08-15 20:41:45](https://github.com/leanprover-community/mathlib/commit/d40c06f)
feat(algebra/ordered_field): rewrite and cleanup ([#3751](https://github.com/leanprover-community/mathlib/pull/3751))
Group similar lemmas in a more intuitive way
Add docstrings, module doc and section headers
Simplify some proofs
Remove some implications if they had a corresponding `iff` lemma.
Add some more variants of some lemmas
Rename some lemmas for consistency
List of name changes (the lemma on the right might be a bi-implication, if the original version was an implication):
`add_midpoint` -> `add_sub_div_two_lt`
`le_div_of_mul_le`, `mul_le_of_le_div` -> `le_div_iff`
`lt_div_of_mul_lt`, `mul_lt_of_lt_div` -> `lt_div_iff`
`div_le_of_le_mul` -> `div_le_iff'`
`le_mul_of_div_le` -> `div_le_iff`
`div_lt_of_pos_of_lt_mul` -> `div_lt_iff'`
`mul_le_of_neg_of_div_le`, `div_le_of_neg_of_mul_le` -> `div_le_iff_of_neg`
`mul_lt_of_neg_of_div_lt`, `div_lt_of_neg_of_mul_lt` -> `div_lt_iff_of_neg`
`div_le_div_of_pos_of_le` -> `div_le_div_of_le`
`div_le_div_of_neg_of_le` -> `div_le_div_of_nonpos_of_le`
`div_lt_div_of_pos_of_lt` -> `div_lt_div_of_lt`
`div_mul_le_div_mul_of_div_le_div_nonneg` -> `div_mul_le_div_mul_of_div_le_div`
`one_le_div_of_le`, `le_of_one_le_div`, `one_le_div_iff_le` -> `one_le_div`
`one_lt_div_of_lt`, `lt_of_one_lt_div`, `one_lt_div_iff_lt` -> `one_lt_div`
`div_le_one_iff_le` -> `div_le_one`
`div_lt_one_iff_lt` -> `div_lt_one`
`one_div_le_of_pos_of_one_div_le` -> `one_div_le`
`one_div_le_of_neg_of_one_div_le` -> `one_div_le_of_neg`
`div_lt_div_of_pos_of_lt_of_pos` -> `div_lt_div_of_lt_left`
One regression I noticed in some other files: when using `div_le_iff`, and the argument is proven by some lemma about `linear_ordered_semiring` then Lean gives a type mismatch. Presumably this happens because the instance chain `ordered_field -> has_le` doesn't go via `ordered_semiring`. The fix is to give the type explicitly, for example using `div_le_iff (t : (0 : ℝ) < _)`
#### Estimated changes
Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/algebra/ordered_field.lean
- \+/\- *lemma* le_div_iff
- \+/\- *lemma* le_div_iff'
- \+/\- *lemma* div_le_iff
- \+/\- *lemma* div_le_iff'
- \+/\- *lemma* lt_div_iff
- \+/\- *lemma* lt_div_iff'
- \+/\- *lemma* div_lt_iff
- \+/\- *lemma* div_lt_iff'
- \+/\- *lemma* div_le_iff_of_neg
- \+ *lemma* div_le_iff_of_neg'
- \+/\- *lemma* le_div_iff_of_neg
- \+ *lemma* le_div_iff_of_neg'
- \+/\- *lemma* div_lt_iff_of_neg
- \+ *lemma* div_lt_iff_of_neg'
- \+/\- *lemma* lt_div_iff_of_neg
- \+ *lemma* lt_div_iff_of_neg'
- \+ *lemma* div_le_iff_of_nonneg_of_le
- \+/\- *lemma* inv_le_inv_of_le
- \+/\- *lemma* inv_le_inv
- \+/\- *lemma* inv_le
- \+/\- *lemma* le_inv
- \+/\- *lemma* inv_lt_inv
- \+/\- *lemma* inv_lt
- \+/\- *lemma* lt_inv
- \+ *lemma* inv_le_inv_of_neg
- \+ *lemma* inv_le_of_neg
- \+ *lemma* le_inv_of_neg
- \+ *lemma* inv_lt_inv_of_neg
- \+ *lemma* inv_lt_of_neg
- \+ *lemma* lt_inv_of_neg
- \+/\- *lemma* inv_lt_one
- \+/\- *lemma* one_lt_inv
- \+/\- *lemma* inv_le_one
- \+/\- *lemma* one_le_inv
- \+ *lemma* div_le_div_of_le
- \+/\- *lemma* div_le_div_of_le_left
- \+/\- *lemma* div_le_div_of_le_of_nonneg
- \+ *lemma* div_le_div_of_nonpos_of_le
- \+ *lemma* div_lt_div_of_lt
- \+/\- *lemma* div_lt_div_of_neg_of_lt
- \+/\- *lemma* div_le_div_right
- \+/\- *lemma* div_le_div_right_of_neg
- \+/\- *lemma* div_lt_div_right
- \+/\- *lemma* div_lt_div_right_of_neg
- \+/\- *lemma* div_lt_div_left
- \+/\- *lemma* div_le_div_left
- \+/\- *lemma* div_lt_div_iff
- \+/\- *lemma* div_le_div_iff
- \+/\- *lemma* div_le_div
- \+/\- *lemma* div_lt_div
- \+/\- *lemma* div_lt_div'
- \+ *lemma* div_lt_div_of_lt_left
- \+ *lemma* one_le_div
- \+ *lemma* div_le_one
- \+ *lemma* one_lt_div
- \+ *lemma* div_lt_one
- \+ *lemma* one_le_div_of_neg
- \+ *lemma* div_le_one_of_neg
- \+ *lemma* one_lt_div_of_neg
- \+ *lemma* div_lt_one_of_neg
- \+/\- *lemma* one_div_le
- \+/\- *lemma* one_div_lt
- \+ *lemma* le_one_div
- \+ *lemma* lt_one_div
- \+ *lemma* one_div_le_of_neg
- \+ *lemma* one_div_lt_of_neg
- \+ *lemma* le_one_div_of_neg
- \+ *lemma* lt_one_div_of_neg
- \+/\- *lemma* one_div_le_one_div_of_le
- \+/\- *lemma* one_div_lt_one_div_of_lt
- \+/\- *lemma* one_div_le_one_div_of_neg_of_le
- \+/\- *lemma* one_div_lt_one_div_of_neg_of_lt
- \+/\- *lemma* le_of_one_div_le_one_div
- \+/\- *lemma* lt_of_one_div_lt_one_div
- \+/\- *lemma* le_of_neg_of_one_div_le_one_div
- \+/\- *lemma* lt_of_neg_of_one_div_lt_one_div
- \+/\- *lemma* one_div_le_one_div
- \+/\- *lemma* one_div_lt_one_div
- \+ *lemma* one_div_le_one_div_of_neg
- \+ *lemma* one_div_lt_one_div_of_neg
- \+/\- *lemma* one_lt_one_div
- \+/\- *lemma* one_le_one_div
- \+/\- *lemma* one_div_lt_neg_one
- \+/\- *lemma* one_div_le_neg_one
- \+/\- *lemma* add_halves
- \+/\- *lemma* sub_self_div_two
- \+/\- *lemma* div_two_sub_self
- \+/\- *lemma* add_self_div_two
- \+/\- *lemma* half_pos
- \+/\- *lemma* one_half_pos
- \+/\- *lemma* div_two_lt_of_pos
- \+/\- *lemma* half_lt_self
- \+/\- *lemma* one_half_lt_one
- \+ *lemma* add_sub_div_two_lt
- \+/\- *lemma* mul_sub_mul_div_mul_neg_iff
- \+/\- *lemma* mul_sub_mul_div_mul_nonpos_iff
- \+/\- *lemma* mul_le_mul_of_mul_div_le
- \+ *lemma* div_mul_le_div_mul_of_div_le_div
- \+/\- *lemma* exists_add_lt_and_pos_of_lt
- \+/\- *lemma* le_of_forall_sub_le
- \- *lemma* one_le_div_of_le
- \- *lemma* le_of_one_le_div
- \- *lemma* one_lt_div_of_lt
- \- *lemma* lt_of_one_lt_div
- \- *lemma* mul_le_of_le_div
- \- *lemma* le_div_of_mul_le
- \- *lemma* mul_lt_of_lt_div
- \- *lemma* lt_div_of_mul_lt
- \- *lemma* mul_le_of_neg_of_div_le
- \- *lemma* div_le_of_neg_of_mul_le
- \- *lemma* mul_lt_of_neg_of_div_lt
- \- *lemma* div_lt_of_pos_of_lt_mul
- \- *lemma* div_lt_of_neg_of_mul_lt
- \- *lemma* div_le_of_le_mul
- \- *lemma* le_mul_of_div_le
- \- *lemma* div_lt_div_of_pos_of_lt
- \- *lemma* div_le_div_of_pos_of_le
- \- *lemma* div_le_div_of_neg_of_le
- \- *lemma* add_midpoint
- \- *lemma* div_mul_le_div_mul_of_div_le_div_nonneg
- \- *lemma* one_div_le_of_pos_of_one_div_le
- \- *lemma* one_div_le_of_neg_of_one_div_le
- \- *lemma* div_lt_div_of_pos_of_lt_of_pos
- \- *lemma* one_le_div_iff_le
- \- *lemma* one_lt_div_iff_lt
- \- *lemma* div_le_one_iff_le
- \- *lemma* div_lt_one_iff_lt

Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/analysis/normed_space/riesz_lemma.lean


Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/special_functions/pow.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/real/basic.lean


Modified src/data/real/cardinality.lean


Modified src/data/real/conjugate_exponents.lean


Modified src/data/real/hyperreal.lean


Modified src/data/real/pi.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/topology/metric_space/antilipschitz.lean




## [2020-08-15 20:41:42](https://github.com/leanprover-community/mathlib/commit/f953a9d)
feat(category_theory/limits/shapes/types): duals ([#3738](https://github.com/leanprover-community/mathlib/pull/3738))
Just dualising some existing material.
#### Estimated changes
Modified src/category_theory/limits/shapes/types.lean
- \+ *lemma* initial
- \+ *lemma* coprod
- \+ *lemma* coprod_inl
- \+ *lemma* coprod_inr
- \+ *lemma* coprod_desc
- \+ *lemma* coprod_map
- \+ *lemma* sigma
- \+ *lemma* sigma_ι
- \+ *lemma* sigma_desc
- \+ *lemma* sigma_map
- \+ *def* types_has_initial
- \+ *def* types_has_binary_coproducts
- \+ *def* types_has_coproducts



## [2020-08-15 19:14:07](https://github.com/leanprover-community/mathlib/commit/8ce00af)
feat(data/set/basic): pairwise_on for equality ([#3802](https://github.com/leanprover-community/mathlib/pull/3802))
Add another lemma about `pairwise_on`: if and only if `f` takes
pairwise equal values on `s`, there is some value it takes everywhere
on `s`.  This arose from discussion in [#3693](https://github.com/leanprover-community/mathlib/pull/3693).
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* pairwise_on_eq_iff_exists_eq



## [2020-08-15 19:14:05](https://github.com/leanprover-community/mathlib/commit/78354e1)
feat(tactic/linarith): support case splits in preprocessing (including `ne` hypotheses) ([#3786](https://github.com/leanprover-community/mathlib/pull/3786))
This adds an API for `linarith` preprocessors to branch. Each branch results in a separate call to `linarith`, so this can be exponentially bad. Use responsibly.
Given that the functionality is there, and I needed a way to test it, I've added a feature that people have been begging for that I've resisted: you can now call `linarith {split_ne := tt}` to handle `a ≠ b` hypotheses. Again: 2^n `linarith` calls for `n` disequalities in your context.
#### Estimated changes
Modified src/tactic/linarith/datatypes.lean


Modified src/tactic/linarith/frontend.lean


Modified src/tactic/linarith/preprocessing.lean


Modified test/linarith.lean




## [2020-08-15 17:58:55](https://github.com/leanprover-community/mathlib/commit/050728b)
feat(data/fintype/basic): card lemma and finset bool alg ([#3796](https://github.com/leanprover-community/mathlib/pull/3796))
Adds the card lemma
```
finset.card_le_univ [fintype α] (s : finset α) : s.card ≤ fintype.card α
```
which I expected to see in mathlib, and upgrade the bounded_distrib_lattice instance on finset in the presence of fintype to a boolean algebra instance.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* compl_eq_univ_sdiff
- \+ *lemma* finset.card_le_univ
- \+ *lemma* finset.card_compl



## [2020-08-15 17:58:53](https://github.com/leanprover-community/mathlib/commit/44010bc)
refactor(linear_algebra/affine_space/combination): bundled affine_combination ([#3789](https://github.com/leanprover-community/mathlib/pull/3789))
When `weighted_vsub_of_point` and `weighted_vsub` became bundled
`linear_map`s on the weights, `affine_combination` was left as an
unbundled function with different argument order from the other two
related operations.  Make it into a bundled `affine_map` on the
weights, so making it more consistent with the other two operations
and allowing general results on `affine_map`s to be used on
`affine_combination` (as illustrated by the changed proofs of
`weighted_vsub_vadd_affine_combination` and
`affine_combination_vsub`).
#### Estimated changes
Modified src/geometry/euclidean.lean


Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* affine_combination_linear
- \+/\- *def* affine_combination

Modified src/linear_algebra/affine_space/independent.lean




## [2020-08-15 17:58:51](https://github.com/leanprover-community/mathlib/commit/9216dd7)
chore(ring_theory): delete `is_algebra_tower` ([#3785](https://github.com/leanprover-community/mathlib/pull/3785))
Delete the abbreviation `is_algebra_tower` for `is_scalar_tower`, and replace all references (including the usages of the `is_algebra_tower` namespace) with `is_scalar_tower`. Documentation should also have been updated accordingly.
This change was requested in a comment on [#3717](https://github.com/leanprover-community/mathlib/pull/3717).
#### Estimated changes
Modified src/field_theory/algebraic_closure.lean


Modified src/field_theory/splitting_field.lean


Modified src/field_theory/tower.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/algebra_tower.lean
- \+ *theorem* algebra_comap_eq
- \- *theorem* comap_eq

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/integral_closure.lean
- \+ *theorem* is_integral_of_is_scalar_tower
- \- *theorem* is_integral_of_is_algebra_tower

Modified src/ring_theory/localization.lean
- \+/\- *lemma* comap_is_algebraic_iff



## [2020-08-15 16:25:49](https://github.com/leanprover-community/mathlib/commit/9451f8d)
feat(data/sum): add sum.{get_left, get_right, is_left, is_right} ([#3792](https://github.com/leanprover-community/mathlib/pull/3792))
#### Estimated changes
Modified src/data/sum.lean
- \+ *def* sum.get_left
- \+ *def* sum.get_right
- \+ *def* sum.is_left
- \+ *def* sum.is_right



## [2020-08-15 14:12:32](https://github.com/leanprover-community/mathlib/commit/daafd6f)
chore(number_theory/pythagorean_triples): added doc-strings ([#3787](https://github.com/leanprover-community/mathlib/pull/3787))
Added docstrings to:
`pythagorean_triple_comm`
`pythagorean_triple.zero`
`mul`
`mul_iff`
#### Estimated changes
Modified src/number_theory/pythagorean_triples.lean




## [2020-08-15 14:12:30](https://github.com/leanprover-community/mathlib/commit/10d4811)
feat(algebra/add_torsor): injectivity lemmas ([#3767](https://github.com/leanprover-community/mathlib/pull/3767))
Add variants of the `add_action` and `add_torsor` cancellation lemmas
whose conclusion is stated in terms of `function.injective`.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* vadd_left_injective
- \+ *lemma* vadd_right_injective
- \+ *lemma* vsub_left_injective
- \+ *lemma* vsub_right_injective



## [2020-08-15 12:43:48](https://github.com/leanprover-community/mathlib/commit/5c13693)
chore(algebra/classical_lie_algebras): fix some doc strings ([#3776](https://github.com/leanprover-community/mathlib/pull/3776))
#### Estimated changes
Modified src/algebra/classical_lie_algebras.lean


Modified src/linear_algebra/basic.lean




## [2020-08-15 12:43:45](https://github.com/leanprover-community/mathlib/commit/9ac6e8a)
refactor(set_theory/pgame): rename pgame lemma ([#3775](https://github.com/leanprover-community/mathlib/pull/3775))
Renamed `move_left_right_moves_neg_symm` to `move_left_left_moves_neg_symm` to make it consistent with the other 3 related lemmas
#### Estimated changes
Modified src/set_theory/pgame.lean
- \+ *lemma* move_left_left_moves_neg_symm
- \- *lemma* move_left_right_moves_neg_symm



## [2020-08-15 12:43:43](https://github.com/leanprover-community/mathlib/commit/658cd38)
feat(tactic/derive_fintype): derive fintype instances ([#3772](https://github.com/leanprover-community/mathlib/pull/3772))
This adds a `@[derive fintype]` implementation, like so:
```
@[derive fintype]
inductive foo (α : Type)
| A : α → foo
| B : α → α → foo
| C : α × α → foo
| D : foo
```
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* mem_cons
- \+ *theorem* cons_val
- \+ *theorem* mem_disj_union
- \+ *theorem* cons_eq_insert
- \+ *theorem* disj_union_eq_union
- \+ *def* cons
- \+ *def* disj_union

Modified src/data/finset/pi.lean


Modified src/data/multiset/nodup.lean
- \+ *lemma* nodup_iff_pairwise

Modified src/data/sigma/basic.lean
- \+ *theorem* psigma.elim_val
- \+ *def* psigma.elim

Modified src/tactic/default.lean


Created src/tactic/derive_fintype.lean
- \+ *theorem* finset_above.mem_cons_self
- \+ *theorem* finset_above.mem_cons_of_mem
- \+ *theorem* finset_in.mem_mk
- \+ *theorem* finset_above.mem_union_left
- \+ *theorem* finset_above.mem_union_right
- \+ *def* foo.enum
- \+ *def* finset_above
- \+ *def* mk_fintype
- \+ *def* finset_above.cons
- \+ *def* finset_above.nil
- \+ *def* finset_in
- \+ *def* finset_in.mk
- \+ *def* finset_above.union

Modified src/tactic/derive_inhabited.lean


Created test/derive_fintype.lean




## [2020-08-15 12:43:41](https://github.com/leanprover-community/mathlib/commit/18746ef)
feat(analysis/special_functions/pow): Added lemmas for rpow of neg exponent ([#3715](https://github.com/leanprover-community/mathlib/pull/3715))
I noticed that the library was missing some lemmas regarding the bounds of rpow of a negative exponent so I added them. I cleaned up the other similar preexisting lemmas for consistency. I then repeated the process for nnreal lemmas.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* rpow_lt_one
- \+/\- *lemma* rpow_le_one
- \+ *lemma* rpow_lt_one_of_one_lt_of_neg
- \+ *lemma* rpow_le_one_of_one_le_of_nonpos
- \+/\- *lemma* one_lt_rpow
- \+/\- *lemma* one_le_rpow
- \+ *lemma* one_lt_rpow_of_pos_of_lt_one_of_neg
- \+ *lemma* one_le_rpow_of_pos_of_le_one_of_nonpos



## [2020-08-15 12:43:39](https://github.com/leanprover-community/mathlib/commit/099f070)
feat(topology/sheaves): the sheaf condition ([#3605](https://github.com/leanprover-community/mathlib/pull/3605))
Johan and I have been working with this, and it's at least minimally viable.
In follow-up PRs we have finished:
* constructing the sheaf of dependent functions to a type family
* constructing the sheaf of continuous functions to a fixed topological space
* checking the sheaf condition under forgetful functors that reflect isos and preserve limits (https://stacks.math.columbia.edu/tag/0073)
Obviously there's more we'd like to see before being confident that a design for sheaves is workable, but we'd like to get started!
#### Estimated changes
Created src/category_theory/limits/punit.lean
- \+ *def* punit_cone_is_limit
- \+ *def* punit_cocone_is_colimit

Modified src/topology/order.lean


Created src/topology/sheaves/sheaf.lean
- \+ *lemma* w
- \+ *lemma* fork_X
- \+ *lemma* fork_ι
- \+ *lemma* fork_π_app_walking_parallel_pair_zero
- \+ *lemma* fork_π_app_walking_parallel_pair_one
- \+ *def* pi_opens
- \+ *def* pi_inters
- \+ *def* left_res
- \+ *def* right_res
- \+ *def* res
- \+ *def* diagram
- \+ *def* fork
- \+ *def* sheaf_condition
- \+ *def* sheaf_condition_punit
- \+ *def* forget



## [2020-08-15 12:06:09](https://github.com/leanprover-community/mathlib/commit/36b4a1e)
refactor(algebra/add_torsor): use `out_param` ([#3727](https://github.com/leanprover-community/mathlib/pull/3727))
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+/\- *lemma* vadd_eq_add
- \+/\- *lemma* vsub_eq_sub
- \+/\- *lemma* vsub_vadd
- \+/\- *lemma* vsub_add_vsub_cancel
- \+/\- *lemma* neg_vsub_eq_vsub_rev
- \+/\- *lemma* vsub_set_empty
- \+/\- *lemma* vsub_set_singleton
- \+/\- *lemma* vsub_set_finite_of_finite
- \+/\- *lemma* vsub_set_mono
- \+/\- *lemma* vsub_left_cancel
- \+/\- *lemma* vsub_left_cancel_iff
- \+/\- *lemma* vsub_right_cancel
- \+/\- *lemma* vsub_right_cancel_iff

Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex.combo_affine_apply
- \+/\- *lemma* convex.affine_preimage
- \+/\- *lemma* convex.affine_image
- \+/\- *lemma* convex_on.comp_affine_map

Modified src/analysis/convex/extrema.lean


Modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* dist_eq_norm_vsub
- \+/\- *lemma* dist_vadd_cancel_left
- \+/\- *lemma* dist_vadd_cancel_right
- \+/\- *lemma* coe_vadd_const
- \+/\- *lemma* coe_vadd_const_symm
- \+/\- *lemma* vadd_const_to_equiv
- \+ *lemma* isometry.vadd_vsub
- \- *lemma* add_torsor.dist_eq_norm
- \- *lemma* isometry_vadd_vsub_of_isometry

Modified src/analysis/normed_space/mazur_ulam.lean
- \+/\- *lemma* coe_to_affine_map
- \+/\- *def* to_affine_map

Modified src/geometry/euclidean.lean
- \+/\- *lemma* angle_comm
- \+/\- *lemma* angle_nonneg
- \+/\- *lemma* angle_le_pi
- \+/\- *lemma* angle_eq_left
- \+/\- *lemma* angle_eq_right
- \+/\- *lemma* angle_eq_of_ne
- \+/\- *lemma* angle_eq_zero_of_angle_eq_pi_left
- \+/\- *lemma* angle_eq_zero_of_angle_eq_pi_right
- \+/\- *lemma* angle_eq_angle_of_angle_eq_pi
- \+/\- *lemma* angle_add_angle_eq_pi_of_angle_eq_pi
- \+/\- *lemma* dist_eq_of_angle_eq_angle_of_angle_ne_pi
- \+/\- *lemma* inter_eq_singleton_orthogonal_projection_fn
- \+/\- *lemma* orthogonal_projection_fn_mem
- \+/\- *lemma* orthogonal_projection_fn_mem_orthogonal
- \+/\- *lemma* orthogonal_projection_fn_vsub_mem_direction_orthogonal
- \+/\- *lemma* orthogonal_projection_fn_eq
- \+/\- *lemma* inter_eq_singleton_orthogonal_projection
- \+/\- *lemma* orthogonal_projection_mem
- \+/\- *lemma* orthogonal_projection_mem_orthogonal
- \+/\- *lemma* orthogonal_projection_vsub_mem_direction
- \+/\- *lemma* vsub_orthogonal_projection_mem_direction
- \+/\- *lemma* orthogonal_projection_eq_self_iff
- \+/\- *lemma* dist_orthogonal_projection_eq_zero_iff
- \+/\- *lemma* dist_orthogonal_projection_ne_zero_of_not_mem
- \+/\- *lemma* orthogonal_projection_vsub_mem_direction_orthogonal
- \+/\- *lemma* vsub_orthogonal_projection_mem_direction_orthogonal
- \+/\- *lemma* orthogonal_projection_vadd_eq_self
- \+/\- *lemma* orthogonal_projection_vadd_smul_vsub_orthogonal_projection
- \+/\- *lemma* dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd
- \+/\- *def* orthogonal_projection_fn
- \+/\- *def* orthogonal_projection

Modified src/linear_algebra/affine_space/basic.lean
- \+/\- *lemma* vector_span_def
- \+/\- *lemma* vector_span_empty
- \+/\- *lemma* vector_span_singleton
- \+/\- *lemma* vsub_set_subset_vector_span
- \+/\- *lemma* mem_span_points
- \+/\- *lemma* subset_span_points
- \+/\- *lemma* mem_coe
- \+/\- *lemma* direction_eq_vector_span
- \+/\- *lemma* direction_of_nonempty_eq_direction
- \+/\- *lemma* coe_direction_eq_vsub_set
- \+/\- *lemma* mem_direction_iff_eq_vsub
- \+/\- *lemma* vadd_mem_of_mem_direction
- \+/\- *lemma* vsub_mem_direction
- \+/\- *lemma* coe_direction_eq_vsub_set_right
- \+/\- *lemma* coe_direction_eq_vsub_set_left
- \+/\- *lemma* mem_direction_iff_eq_vsub_right
- \+/\- *lemma* mem_direction_iff_eq_vsub_left
- \+/\- *lemma* vsub_right_mem_direction_iff_mem
- \+/\- *lemma* vsub_left_mem_direction_iff_mem
- \+/\- *lemma* ext
- \+/\- *lemma* ext_of_direction_eq
- \+/\- *lemma* mk'_eq
- \+/\- *lemma* span_points_subset_coe_of_subset_coe
- \+/\- *lemma* direction_affine_span
- \+/\- *lemma* mem_affine_span
- \+/\- *lemma* le_def
- \+/\- *lemma* le_def'
- \+/\- *lemma* lt_def
- \+/\- *lemma* not_le_iff_exists
- \+/\- *lemma* exists_of_lt
- \+/\- *lemma* lt_iff_le_and_exists
- \+/\- *lemma* affine_span_eq_Inf
- \+/\- *lemma* span_empty
- \+/\- *lemma* span_univ
- \+/\- *lemma* coe_affine_span_singleton
- \+/\- *lemma* span_union
- \+/\- *lemma* top_coe
- \+/\- *lemma* mem_top
- \+/\- *lemma* direction_top
- \+/\- *lemma* bot_coe
- \+/\- *lemma* not_mem_bot
- \+/\- *lemma* direction_bot
- \+/\- *lemma* inf_coe
- \+/\- *lemma* mem_inf_iff
- \+/\- *lemma* direction_inf
- \+/\- *lemma* direction_le
- \+/\- *lemma* direction_lt_of_nonempty
- \+/\- *lemma* sup_direction_le
- \+/\- *lemma* sup_direction_lt_of_nonempty_of_inter_empty
- \+/\- *lemma* inter_nonempty_of_nonempty_of_sup_direction_eq_top
- \+/\- *lemma* inter_eq_singleton_of_nonempty_of_is_compl
- \+/\- *lemma* affine_span_coe
- \+/\- *lemma* direction_sup
- \+/\- *lemma* direction_affine_span_insert
- \+/\- *lemma* mem_affine_span_insert_iff
- \+/\- *lemma* to_fun_eq_coe
- \+/\- *lemma* map_vadd
- \+/\- *lemma* linear_map_vsub
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coe_const
- \+/\- *lemma* const_linear
- \+/\- *lemma* coe_zero
- \+/\- *lemma* zero_linear
- \+/\- *lemma* coe_add
- \+/\- *lemma* add_linear
- \+/\- *lemma* vadd_apply
- \+/\- *lemma* vsub_apply
- \+/\- *lemma* coe_id
- \+/\- *lemma* id_linear
- \+/\- *lemma* id_apply
- \+/\- *lemma* coe_comp
- \+/\- *lemma* comp_apply
- \+/\- *lemma* comp_id
- \+/\- *lemma* id_comp
- \+/\- *lemma* comp_assoc
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_one
- \+/\- *lemma* line_map_zero
- \+/\- *lemma* affine_apply_line_map
- \+/\- *lemma* affine_comp_line_map
- \+/\- *lemma* decomp
- \+/\- *lemma* decomp'
- \+/\- *lemma* coe_smul
- \+/\- *lemma* homothety_apply
- \+/\- *lemma* homothety_one
- \+/\- *lemma* homothety_zero
- \+/\- *lemma* coe_homothety_hom
- \+/\- *def* vector_span
- \+/\- *def* direction
- \+/\- *def* direction_of_nonempty
- \+/\- *def* mk'
- \+/\- *def* affine_span
- \+/\- *def* const
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* line_map
- \+/\- *def* homothety
- \+/\- *def* homothety_hom
- \+/\- *def* homothety_affine
- \+/\- *def* to_affine_map

Modified src/linear_algebra/affine_space/combination.lean
- \+/\- *def* weighted_vsub_of_point

Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/affine_space/independent.lean
- \+/\- *lemma* mk_of_point_points
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* face_points
- \+/\- *lemma* face_eq_mk_of_point
- \+/\- *def* mk_of_point
- \+/\- *def* face

Modified src/topology/algebra/affine.lean
- \+/\- *lemma* continuous_iff



## [2020-08-15 10:36:54](https://github.com/leanprover-community/mathlib/commit/2b8ece6)
feat(data/nat/basic): one mod two or higher is one ([#3763](https://github.com/leanprover-community/mathlib/pull/3763))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* one_mod



## [2020-08-15 10:09:19](https://github.com/leanprover-community/mathlib/commit/c444a00)
Revert "chore(ring_theory): delete `is_algebra_tower`"
This reverts commit c956ce1516ccfb3139ae3ebde7ede9c678d81968.
#### Estimated changes
Modified src/field_theory/algebraic_closure.lean


Modified src/field_theory/splitting_field.lean


Modified src/field_theory/tower.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/algebra_tower.lean
- \+ *theorem* comap_eq
- \- *theorem* algebra_comap_eq

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/integral_closure.lean
- \+ *theorem* is_integral_of_is_algebra_tower
- \- *theorem* is_integral_of_is_scalar_tower

Modified src/ring_theory/localization.lean
- \+/\- *lemma* comap_is_algebraic_iff



## [2020-08-15 10:05:13](https://github.com/leanprover-community/mathlib/commit/c956ce1)
chore(ring_theory): delete `is_algebra_tower`
Delete the abbreviation `is_algebra_tower` for `is_scalar_tower`,
and replace all references (including the usages of the `is_algebra_tower`
namespace) with `is_scalar_tower`. Documentation should also have been
updated accordingly.
This change was requested in a comment on [#3717](https://github.com/leanprover-community/mathlib/pull/3717).
#### Estimated changes
Modified src/field_theory/algebraic_closure.lean


Modified src/field_theory/splitting_field.lean


Modified src/field_theory/tower.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/algebra_tower.lean
- \+ *theorem* algebra_comap_eq
- \- *theorem* comap_eq

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/integral_closure.lean
- \+ *theorem* is_integral_of_is_scalar_tower
- \- *theorem* is_integral_of_is_algebra_tower

Modified src/ring_theory/localization.lean
- \+/\- *lemma* comap_is_algebraic_iff



## [2020-08-15 08:45:27](https://github.com/leanprover-community/mathlib/commit/67dad7f)
feat(control/equiv_functor): fintype instance ([#3783](https://github.com/leanprover-community/mathlib/pull/3783))
Requested at https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/fintype.2Eequiv_congr/near/206773279
#### Estimated changes
Modified src/control/equiv_functor/instances.lean




## [2020-08-15 07:22:35](https://github.com/leanprover-community/mathlib/commit/b670212)
fix(tactic/apply): fix ordering of goals produced by `apply` ([#3777](https://github.com/leanprover-community/mathlib/pull/3777))
#### Estimated changes
Modified src/tactic/apply.lean


Modified test/apply.lean




## [2020-08-15 07:22:33](https://github.com/leanprover-community/mathlib/commit/c1a5283)
refactor(data/list/tfae): tfae.out ([#3774](https://github.com/leanprover-community/mathlib/pull/3774))
This version of `tfae.out` has slightly better automatic reduction behavior: if `h : [a, b, c].tfae` then the original of `h.out 1 2` proves `[a, b, c].nth_le 1 _ <-> [a, b, c].nth_le 2 _` while the new version of `h.out 1 2` proves `b <-> c`. These are the same, of course, and you can mostly use them interchangeably, but the second one is a bit nicer to look at (and possibly works better with e.g. subsequent rewrites).
#### Estimated changes
Modified src/data/list/tfae.lean
- \+/\- *theorem* tfae.out



## [2020-08-15 06:35:10](https://github.com/leanprover-community/mathlib/commit/55f4926)
fix(algebra/archimedean): switch to a more natural and general condition in exists_nat_pow_near ([#3782](https://github.com/leanprover-community/mathlib/pull/3782))
per discussion at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Starting.20to.20contribute.20to.20mathlib/near/206945824
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+/\- *lemma* exists_nat_pow_near



## [2020-08-14 17:00:08](https://github.com/leanprover-community/mathlib/commit/3ae44bd)
fix(tactic/equiv_rw): fix problem with stuck universe metavariables ([#3773](https://github.com/leanprover-community/mathlib/pull/3773))
#### Estimated changes
Modified src/tactic/equiv_rw.lean


Modified test/equiv_rw.lean




## [2020-08-14 15:47:08](https://github.com/leanprover-community/mathlib/commit/c252800)
chore(*): use notation for `filter.prod` ([#3768](https://github.com/leanprover-community/mathlib/pull/3768))
Also change from `∀ v w ∈ V` to `∀ (v ∈ V) (w ∈ V)` in `exists_nhds_split_inv`, `exists_nhds_half_neg`, `add_group_with_zero_nhd.exists_Z_half`.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean


Modified src/order/filter/bases.lean
- \+ *lemma* mem_prod_self_iff

Modified src/order/filter/basic.lean
- \+/\- *lemma* prod_eq

Modified src/order/filter/lift.lean
- \+/\- *lemma* prod_def
- \+/\- *lemma* prod_same_eq

Modified src/topology/algebra/group.lean
- \+/\- *lemma* add_Z
- \+/\- *lemma* exists_Z_half

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/constructions.lean
- \+/\- *lemma* nhds_prod_eq

Modified src/topology/continuous_on.lean


Modified src/topology/list.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean
- \+/\- *def* cauchy

Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-08-14 12:28:48](https://github.com/leanprover-community/mathlib/commit/0e5f44b)
chore(*): assorted lemmas for FTC-1 ([#3755](https://github.com/leanprover-community/mathlib/pull/3755))
Lemmas from FTC-1 (`has_strict_deriv` version) [#3709](https://github.com/leanprover-community/mathlib/pull/3709)
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *theorem* is_o.add_add

Modified src/data/set/basic.lean
- \+ *lemma* forall_prod_set
- \+/\- *theorem* mem_powerset_iff
- \+ *theorem* powerset_inter
- \+/\- *theorem* powerset_mono
- \+ *theorem* monotone_powerset
- \+/\- *theorem* powerset_nonempty
- \+ *theorem* powerset_empty

Modified src/data/set/intervals/disjoint.lean
- \+ *lemma* Iic_disjoint_Ioi
- \+ *lemma* Iic_disjoint_Ioc
- \+/\- *lemma* Ioc_disjoint_Ioc_same
- \+/\- *lemma* Ico_disjoint_Ico_same
- \+/\- *lemma* Ico_disjoint_Ico
- \+/\- *lemma* Ioc_disjoint_Ioc

Modified src/data/set/intervals/ord_connected.lean
- \+ *lemma* ord_connected_singleton

Modified src/order/filter/basic.lean
- \+ *lemma* eventually_pure
- \+ *lemma* principal_singleton
- \+ *lemma* tendsto_iff_eventually
- \+/\- *lemma* tendsto_infi
- \+/\- *lemma* tendsto_principal
- \+/\- *lemma* tendsto_principal_principal
- \+/\- *lemma* tendsto_pure
- \+ *lemma* pure_le_iff
- \+ *lemma* tendsto_pure_left
- \- *lemma* pure_eq_principal
- \+ *theorem* comap_pure

Modified src/order/filter/lift.lean
- \+ *lemma* lift'_pure
- \+ *lemma* lift'_bot
- \+ *lemma* lift'_inf
- \+ *lemma* lift'_inf_powerset
- \+ *lemma* tendsto_lift'_powerset_mono

Modified src/topology/continuous_on.lean
- \+ *lemma* pure_le_nhds_within



## [2020-08-14 00:40:06](https://github.com/leanprover-community/mathlib/commit/b611c5f)
chore(scripts): update nolints.txt ([#3771](https://github.com/leanprover-community/mathlib/pull/3771))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-13 19:36:34](https://github.com/leanprover-community/mathlib/commit/32c6a73)
feat(ci): auto label merge conflicts, try 2 ([#3766](https://github.com/leanprover-community/mathlib/pull/3766))
#### Estimated changes
Modified .github/workflows/merge_conflicts.yml




## [2020-08-13 19:36:32](https://github.com/leanprover-community/mathlib/commit/627b431)
feat(tactic/find_unused): find the dead code in a module ([#3701](https://github.com/leanprover-community/mathlib/pull/3701))
#### Estimated changes
Modified src/tactic/core.lean


Created src/tactic/find_unused.lean


Created test/find_unused_decl1.lean
- \+ *def* this_is_unused
- \+ *def* main_thing

Created test/find_unused_decl2.lean
- \+ *def* unused1
- \+ *def* my_list
- \+ *def* some_val
- \+ *def* other_val
- \+ *def* used_somewhere_else



## [2020-08-13 19:36:30](https://github.com/leanprover-community/mathlib/commit/28dfad8)
feat(ideals,submonoids,subgroups): mem_sup(r) and mem_inf(i) lemmas ([#3697](https://github.com/leanprover-community/mathlib/pull/3697))
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* mem_sup_left
- \+ *lemma* mem_sup_right
- \+ *lemma* mem_supr_of_mem
- \+ *lemma* mem_Sup_of_mem

Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* mem_sup_left
- \+ *lemma* mem_sup_right
- \+ *lemma* mem_supr_of_mem
- \+ *lemma* mem_Sup_of_mem

Modified src/linear_algebra/basic.lean
- \+ *lemma* mem_sup_left
- \+ *lemma* mem_sup_right
- \+/\- *lemma* mem_supr_of_mem
- \+ *lemma* mem_Sup_of_mem

Modified src/linear_algebra/finsupp.lean


Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* mem_sup_left
- \+ *lemma* mem_sup_right
- \+ *lemma* mem_supr_of_mem
- \+ *lemma* mem_Sup_of_mem
- \+ *lemma* mem_inf
- \+ *lemma* mem_infi



## [2020-08-13 18:09:00](https://github.com/leanprover-community/mathlib/commit/4cc094b)
chore(data/int/basic): norm_cast attribute on int.coe_nat_mod ([#3765](https://github.com/leanprover-community/mathlib/pull/3765))
#### Estimated changes
Modified src/data/int/basic.lean
- \+/\- *theorem* coe_nat_mod



## [2020-08-13 14:29:54](https://github.com/leanprover-community/mathlib/commit/c66ecd3)
feat(intervals/image_preimage): preimage under multiplication ([#3757](https://github.com/leanprover-community/mathlib/pull/3757))
Add lemmas `preimage_mul_const_Ixx` and `preimage_const_mul_Ixx`.
Also generalize `equiv.mul_left` and `equiv.mul_right` to `units`.
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *lemma* lt_div_iff_of_neg

Modified src/data/equiv/mul_add.lean
- \+ *lemma* coe_mul_left
- \+ *lemma* mul_left_symm
- \+ *lemma* coe_mul_right
- \+ *lemma* mul_right_symm
- \+/\- *def* to_units
- \+ *def* mul_left
- \+ *def* mul_right

Modified src/data/set/intervals/image_preimage.lean
- \+ *lemma* preimage_mul_const_Iio
- \+ *lemma* preimage_mul_const_Ioi
- \+ *lemma* preimage_mul_const_Iic
- \+ *lemma* preimage_mul_const_Ici
- \+ *lemma* preimage_mul_const_Ioo
- \+ *lemma* preimage_mul_const_Ioc
- \+ *lemma* preimage_mul_const_Ico
- \+ *lemma* preimage_mul_const_Icc
- \+ *lemma* preimage_mul_const_Iio_of_neg
- \+ *lemma* preimage_mul_const_Ioi_of_neg
- \+ *lemma* preimage_mul_const_Iic_of_neg
- \+ *lemma* preimage_mul_const_Ici_of_neg
- \+ *lemma* preimage_mul_const_Ioo_of_neg
- \+ *lemma* preimage_mul_const_Ioc_of_neg
- \+ *lemma* preimage_mul_const_Ico_of_neg
- \+ *lemma* preimage_mul_const_Icc_of_neg
- \+ *lemma* preimage_const_mul_Iio
- \+ *lemma* preimage_const_mul_Ioi
- \+ *lemma* preimage_const_mul_Iic
- \+ *lemma* preimage_const_mul_Ici
- \+ *lemma* preimage_const_mul_Ioo
- \+ *lemma* preimage_const_mul_Ioc
- \+ *lemma* preimage_const_mul_Ico
- \+ *lemma* preimage_const_mul_Icc
- \+ *lemma* preimage_const_mul_Iio_of_neg
- \+ *lemma* preimage_const_mul_Ioi_of_neg
- \+ *lemma* preimage_const_mul_Iic_of_neg
- \+ *lemma* preimage_const_mul_Ici_of_neg
- \+ *lemma* preimage_const_mul_Ioo_of_neg
- \+ *lemma* preimage_const_mul_Ioc_of_neg
- \+ *lemma* preimage_const_mul_Ico_of_neg
- \+ *lemma* preimage_const_mul_Icc_of_neg

Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/group_theory/group_action.lean




## [2020-08-13 12:59:37](https://github.com/leanprover-community/mathlib/commit/f912f18)
feat(ci): auto label merge conflicts ([#3761](https://github.com/leanprover-community/mathlib/pull/3761))
#### Estimated changes
Created .github/workflows/merge_conflicts.yml




## [2020-08-13 12:59:35](https://github.com/leanprover-community/mathlib/commit/34352c2)
refactor(algebra/associated): change several instances from [integral_domain] to [comm_cancel_monoid_with_zero] ([#3744](https://github.com/leanprover-community/mathlib/pull/3744))
defines `comm_cancel_monoid_with_zero`
replaces some `integral_domain` instances with `comm_cancel_monoid_with_zero`
prepares the API for refactoring `normalization_domain`, `gcd_domain`, and `unique_factorization_domain` to monoids
#### Estimated changes
Modified src/algebra/associated.lean
- \+/\- *lemma* dvd_and_not_dvd_iff
- \+/\- *lemma* pow_dvd_pow_iff
- \+/\- *lemma* irreducible_of_prime
- \+/\- *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \+/\- *lemma* exists_associated_mem_of_dvd_prod
- \+/\- *lemma* associated_mul_left_cancel
- \+/\- *lemma* associated_mul_right_cancel
- \+/\- *theorem* prod_eq_zero_iff

Modified src/algebra/divisibility.lean
- \+ *theorem* mul_dvd_mul_iff_right

Modified src/algebra/group_with_zero.lean


Modified src/algebra/ring/basic.lean
- \- *theorem* mul_dvd_mul_iff_right



## [2020-08-13 12:59:33](https://github.com/leanprover-community/mathlib/commit/2c4300b)
feat(data/polynomial): adds map_comp ([#3736](https://github.com/leanprover-community/mathlib/pull/3736))
Adds lemma saying that the map of the composition of two polynomials is the composition of the maps, as mentioned [here](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Polynomial.20composition.20and.20map.20commute).
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_subset_one_on_sdiff

Modified src/data/polynomial/eval.lean
- \+ *lemma* map_sum
- \+ *lemma* support_map_subset
- \+ *lemma* map_comp



## [2020-08-13 11:32:00](https://github.com/leanprover-community/mathlib/commit/ac2f011)
feat(data/*): Add sizeof lemmas. ([#3745](https://github.com/leanprover-community/mathlib/pull/3745))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* sizeof_lt_sizeof_of_mem

Modified src/data/list/basic.lean
- \+ *theorem* sizeof_lt_sizeof_of_mem

Modified src/data/list/perm.lean
- \+ *theorem* perm.sizeof_eq_sizeof

Modified src/data/multiset/basic.lean
- \+ *theorem* sizeof_lt_sizeof_of_mem



## [2020-08-13 11:01:00](https://github.com/leanprover-community/mathlib/commit/b1e56a2)
feat(analysis/special_functions/trigonometric): Added lemma cos_ne_zero_iff ([#3743](https://github.com/leanprover-community/mathlib/pull/3743))
I added the theorem `cos_ne_zero_iff`, a corollary to the preexisting theorem `cos_eq_zero_iff`
<!-- put comments you want to keep out of the PR commit here -->
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *theorem* cos_ne_zero_iff



## [2020-08-13 09:23:02](https://github.com/leanprover-community/mathlib/commit/ced7469)
chore(data/finset/order): use `[nonempty]` in `directed.finset_le` ([#3759](https://github.com/leanprover-community/mathlib/pull/3759))
#### Estimated changes
Modified src/data/finset/order.lean


Modified src/linear_algebra/basis.lean


Modified src/topology/subset_properties.lean




## [2020-08-13 09:23:00](https://github.com/leanprover-community/mathlib/commit/4c24a09)
chore(data/fintype/card): add `prod_bool` ([#3758](https://github.com/leanprover-community/mathlib/pull/3758))
#### Estimated changes
Modified src/data/fintype/card.lean
- \+ *lemma* prod_bool

Modified src/topology/algebra/infinite_sum.lean




## [2020-08-13 09:22:58](https://github.com/leanprover-community/mathlib/commit/31a0258)
chore(data/fintype/card): DRY using `@... (multiplicative _)` ([#3756](https://github.com/leanprover-community/mathlib/pull/3756))
#### Estimated changes
Modified src/data/fintype/card.lean




## [2020-08-13 09:22:56](https://github.com/leanprover-community/mathlib/commit/cc6528e)
feat(analysis/calculus/fderiv): multiplication by a complex respects real differentiability ([#3731](https://github.com/leanprover-community/mathlib/pull/3731))
If `f` takes values in a complex vector space and is real-differentiable, then `c f` is also real-differentiable when `c` is a complex number. This PR proves this fact and the obvious variations, in the general case of two fields where one is a normed algebra over the other one.
Along the way, some material on `module.restrict_scalars` is added, notably in a normed space context.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable_within_at.smul_algebra
- \+ *lemma* differentiable_at.smul_algebra
- \+ *lemma* differentiable_on.smul_algebra
- \+ *lemma* differentiable.smul_algebra
- \+ *lemma* fderiv_within_smul_algebra
- \+ *lemma* fderiv_smul_algebra
- \+ *lemma* differentiable_within_at.smul_algebra_const
- \+ *lemma* differentiable_at.smul_algebra_const
- \+ *lemma* differentiable_on.smul_algebra_const
- \+ *lemma* differentiable.smul_algebra_const
- \+ *lemma* fderiv_within_smul_algebra_const
- \+ *lemma* fderiv_smul_algebra_const
- \+ *lemma* differentiable_within_at.const_smul_algebra
- \+ *lemma* differentiable_at.const_smul_algebra
- \+ *lemma* differentiable_on.const_smul_algebra
- \+ *lemma* differentiable.const_smul_algebra
- \+ *lemma* fderiv_within_const_smul_algebra
- \+ *lemma* fderiv_const_smul_algebra
- \+ *theorem* has_strict_fderiv_at.smul_algebra
- \+ *theorem* has_fderiv_within_at.smul_algebra
- \+ *theorem* has_fderiv_at.smul_algebra
- \+ *theorem* has_strict_fderiv_at.smul_algebra_const
- \+ *theorem* has_fderiv_within_at.smul_algebra_const
- \+ *theorem* has_fderiv_at.smul_algebra_const
- \+ *theorem* has_strict_fderiv_at.const_smul_algebra
- \+ *theorem* has_fderiv_at_filter.const_smul_algebra
- \+ *theorem* has_fderiv_within_at.const_smul_algebra
- \+ *theorem* has_fderiv_at.const_smul_algebra

Modified src/analysis/complex/basic.lean


Modified src/analysis/normed_space/basic.lean
- \+ *def* normed_space.restrict_scalars'
- \- *def* normed_space.restrict_scalars

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* is_bounded_bilinear_map_smul_algebra

Modified src/analysis/normed_space/hahn_banach.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* linear_map.mk_continuous_norm_le
- \+ *lemma* has_sum_of_summable
- \- *lemma* continuous_linear_map.has_sum
- \- *lemma* continuous_linear_map.has_sum_of_summable
- \+ *theorem* smul_algebra_right_apply
- \+/\- *def* restrict_scalars
- \+ *def* smul_algebra_right

Modified src/data/complex/module.lean


Modified src/ring_theory/algebra.lean
- \+ *lemma* smul_algebra_smul
- \+ *lemma* smul_algebra_smul_comm
- \+ *theorem* smul_algebra_right_apply
- \+ *def* smul_algebra_right



## [2020-08-13 09:22:52](https://github.com/leanprover-community/mathlib/commit/cfcbea6)
feat(data/list/palindrome): define palindromes ([#3729](https://github.com/leanprover-community/mathlib/pull/3729))
This introduces an inductive type `palindrome`, with conversions to and from the proposition `reverse l = l`.
Review of this PR indicates two things: (1) maybe the name `is_palindrome` is better, especially if we define the subtype of palindromic lists; (2) maybe defining palindrome by `reverse l = l` is simpler. We note these for future development.
#### Estimated changes
Created src/data/list/palindrome.lean
- \+ *lemma* reverse_eq
- \+ *lemma* of_reverse_eq
- \+ *lemma* iff_reverse_eq
- \+ *lemma* append_reverse



## [2020-08-13 07:52:35](https://github.com/leanprover-community/mathlib/commit/c503b7a)
feat(algebra/order): more lemmas for projection notation ([#3753](https://github.com/leanprover-community/mathlib/pull/3753))
Also import `tactic.lint` and ensure that the linter passes
Move `ge_of_eq` to this file
#### Estimated changes
Modified src/algebra/order.lean
- \+ *lemma* le_rfl
- \+ *lemma* trans_le
- \+ *lemma* trans_eq
- \+/\- *lemma* ge_iff_le
- \+/\- *lemma* gt_iff_lt
- \+/\- *lemma* le_implies_le_of_le_of_le
- \+ *theorem* ge_of_eq

Modified src/order/basic.lean
- \- *theorem* ge_of_eq

Modified src/order/filter/germ.lean




## [2020-08-13 06:22:20](https://github.com/leanprover-community/mathlib/commit/6c8b2cd)
fix(algebra/field) remove `one_div_eq_inv` ([#3749](https://github.com/leanprover-community/mathlib/pull/3749))
It already existed as `one_div` for `group_with_zero`
Also make `one_div` a `simp` lemma and renamed `nnreal.one_div_eq_inv` to `nnreal.one_div`.
#### Estimated changes
Modified src/algebra/archimedean.lean


Modified src/algebra/field.lean
- \- *lemma* one_div_eq_inv

Modified src/algebra/field_power.lean


Modified src/algebra/group_with_zero.lean
- \+/\- *lemma* one_div
- \+/\- *lemma* one_div_one_div

Modified src/algebra/ordered_field.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/asymptotics.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/analysis/specific_limits.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/nat/cast.lean


Modified src/data/real/conjugate_exponents.lean


Modified src/data/real/hyperreal.lean


Modified src/data/real/nnreal.lean
- \+ *lemma* one_div
- \- *lemma* one_div_eq_inv

Modified src/measure_theory/simple_func_dense.lean


Modified src/tactic/interactive.lean


Modified src/tactic/norm_num.lean


Modified src/topology/metric_space/pi_Lp.lean




## [2020-08-13 01:10:43](https://github.com/leanprover-community/mathlib/commit/d6ffc1a)
feat(tactic/clear_value): preserve order and naming ([#3700](https://github.com/leanprover-community/mathlib/pull/3700))
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Modified test/tactics.lean




## [2020-08-13 00:42:53](https://github.com/leanprover-community/mathlib/commit/cacb54e)
chore(scripts): update nolints.txt ([#3754](https://github.com/leanprover-community/mathlib/pull/3754))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-12 23:09:20](https://github.com/leanprover-community/mathlib/commit/486830b)
feat(tactic/choose): `choose` can now decompose conjunctions ([#3699](https://github.com/leanprover-community/mathlib/pull/3699))
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Modified test/choose.lean




## [2020-08-12 20:04:21](https://github.com/leanprover-community/mathlib/commit/f8c8135)
feat(tactic/rcases): type ascriptions in rcases ([#3730](https://github.com/leanprover-community/mathlib/pull/3730))
This is a general rewrite of the `rcases` tactic, with the primary intent of adding support for type ascriptions in `rcases` patterns but it also includes a bunch more documentation, as well as making the grammar simpler, avoiding the strict tuple/alts alternations required by the previous `many` constructor (and the need for `rcases_patt_inverted` for whether the constructor means `tuple` of `alts` or `alts` of `tuple`).
From a user perspective, it should not be noticeably different, except:
* You can now use parentheses freely in patterns, so things like `a | (b | c)` work
* You can use type ascriptions
The new `rcases` is backward compatible with the old one, except that `rcases e with a` (where `a` is a name) no longer does any cases and is basically just another way to write `have a := e`; to get the same effect as `cases e with a` you have to write `rcases e with ⟨a⟩` instead.
#### Estimated changes
Modified src/analysis/specific_limits.lean


Modified src/data/nat/digits.lean


Modified src/data/pnat/factors.lean


Modified src/tactic/ext.lean


Modified src/tactic/lift.lean


Modified src/tactic/rcases.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/isometry.lean


Modified test/rcases.lean




## [2020-08-12 16:33:24](https://github.com/leanprover-community/mathlib/commit/4324778)
feat(.): add code of conduct ([#3747](https://github.com/leanprover-community/mathlib/pull/3747))
#### Estimated changes
Created CODE_OF_CONDUCT.md




## [2020-08-12 15:04:27](https://github.com/leanprover-community/mathlib/commit/eb4b2a0)
feat(field_theory/algebraic_closure): algebraic closure ([#3733](https://github.com/leanprover-community/mathlib/pull/3733))
```lean
instance : is_alg_closed (algebraic_closure k) :=
```
TODO: Show that any algebraic extension embeds into any algebraically closed extension (via Zorn's lemma).
#### Estimated changes
Modified src/algebra/direct_limit.lean
- \+ *theorem* polynomial.exists_of

Modified src/data/mv_polynomial.lean
- \+ *theorem* algebra_map_eq

Modified src/data/polynomial/field_division.lean
- \+ *theorem* monic_map_iff
- \+ *theorem* not_irreducible_C
- \+ *theorem* degree_pos_of_irreducible

Modified src/data/real/ennreal.lean


Created src/field_theory/algebraic_closure.lean
- \+ *lemma* coe_to_step_of_le
- \+ *theorem* polynomial.splits'
- \+ *theorem* of_exists_root
- \+ *theorem* to_splitting_field_eval_X_self
- \+ *theorem* span_eval_ne_top
- \+ *theorem* le_max_ideal
- \+ *theorem* adjoin_monic.algebra_map
- \+ *theorem* adjoin_monic.is_integral
- \+ *theorem* adjoin_monic.exists_root
- \+ *theorem* to_step_succ.exists_root
- \+ *theorem* step.is_integral
- \+ *theorem* of_step_succ
- \+ *theorem* exists_of_step
- \+ *theorem* exists_root
- \+ *theorem* is_algebraic
- \+ *def* is_alg_closure
- \+ *def* monic_irreducible
- \+ *def* eval_X_self
- \+ *def* span_eval
- \+ *def* to_splitting_field
- \+ *def* max_ideal
- \+ *def* adjoin_monic
- \+ *def* to_adjoin_monic
- \+ *def* step_aux
- \+ *def* step
- \+ *def* to_step_zero
- \+ *def* to_step_succ
- \+ *def* to_step_of_le
- \+ *def* algebraic_closure
- \+ *def* of_step
- \+ *def* of_step_hom

Modified src/field_theory/splitting_field.lean
- \+ *theorem* splits_of_is_unit
- \+ *theorem* map_root_of_splits
- \+ *def* root_of_splits

Modified src/order/directed.lean


Modified src/ring_theory/algebra.lean
- \+/\- *theorem* comp_algebra_map

Modified src/ring_theory/valuation/basic.lean




## [2020-08-12 10:41:14](https://github.com/leanprover-community/mathlib/commit/bfcf640)
feat(topology/opens): open_embedding_of_le ([#3597](https://github.com/leanprover-community/mathlib/pull/3597))
Add `lemma open_embedding_of_le {U V : opens α} (i : U ≤ V) : open_embedding (set.inclusion i)`.
Also, I was finding it quite inconvenient to have `x ∈ U` for `U : opens X` being unrelated to `x ∈ (U : set X)`. I propose we just add the simp lemmas in this PR that unfold to the set-level membership operation.
(I'd be happy to go the other way if someone has a strong opinion here; just that we pick a simp normal form for talking about membership and inclusion of opens.)
#### Estimated changes
Modified src/topology/opens.lean
- \+ *lemma* subset_coe
- \+ *lemma* mem_coe
- \+ *lemma* supr_s
- \+ *lemma* open_embedding_of_le
- \+ *theorem* mem_supr



## [2020-08-11 15:31:36](https://github.com/leanprover-community/mathlib/commit/06e1405)
docs(category/default): Fix typo for monomorphism ([#3741](https://github.com/leanprover-community/mathlib/pull/3741))
#### Estimated changes
Modified src/category_theory/category/default.lean




## [2020-08-11 09:57:43](https://github.com/leanprover-community/mathlib/commit/f92fd0d)
refactor(algebra/divisibility, associated): generalize instances in divisibility, associated ([#3714](https://github.com/leanprover-community/mathlib/pull/3714))
generalizes the divisibility relation to noncommutative monoids
adds missing headers to algebra/divisibility
generalizes the instances in many of the lemmas in algebra/associated
reunites (some of the) divisibility API for ordinals with general monoids
#### Estimated changes
Modified src/algebra/associated.lean
- \+/\- *lemma* is_unit_of_dvd_one
- \+/\- *lemma* ne_zero
- \+/\- *lemma* not_unit
- \+/\- *lemma* div_or_div
- \+/\- *lemma* dvd_of_dvd_pow
- \+/\- *lemma* not_prime_zero
- \+/\- *lemma* not_prime_one
- \+/\- *lemma* exists_mem_multiset_dvd_of_prime
- \+/\- *lemma* dvd_symm_of_irreducible
- \+/\- *lemma* dvd_symm_iff_of_irreducible
- \+/\- *lemma* dvd_of_associated
- \+/\- *lemma* dvd_dvd_of_associated
- \+/\- *lemma* dvd_iff_dvd_of_rel_left
- \- *lemma* unit_mul_dvd_iff
- \- *lemma* mul_unit_dvd_iff
- \- *lemma* dvd_mul_unit_iff
- \+/\- *theorem* is_unit_iff_dvd_one
- \+/\- *theorem* is_unit_iff_forall_dvd
- \+/\- *theorem* is_unit_of_dvd_unit
- \+/\- *theorem* not_irreducible_zero
- \+/\- *theorem* irreducible.ne_zero
- \+/\- *theorem* associated_of_dvd_dvd
- \+/\- *theorem* dvd_dvd_iff_associated
- \- *theorem* mul_dvd_of_is_unit_left
- \- *theorem* mul_dvd_of_is_unit_right
- \+/\- *def* prime

Modified src/algebra/divisibility.lean
- \+ *lemma* coe_dvd
- \+ *lemma* dvd_mul_right
- \+ *lemma* mul_right_dvd
- \+ *lemma* dvd_mul_left
- \+ *lemma* mul_left_dvd
- \+ *lemma* dvd
- \+/\- *theorem* one_dvd
- \+/\- *theorem* dvd_of_mul_right_dvd
- \+/\- *theorem* dvd.intro_left
- \+/\- *theorem* exists_eq_mul_left_of_dvd
- \+/\- *theorem* dvd.elim_left
- \+/\- *theorem* dvd_mul_left
- \+ *theorem* mul_dvd_mul_iff_left

Modified src/algebra/gcd_domain.lean


Modified src/algebra/group_power.lean
- \+/\- *lemma* zero_pow
- \+/\- *lemma* pow_dvd_pow
- \+/\- *theorem* pow_dvd_pow_of_dvd
- \+/\- *theorem* pow_eq_zero
- \+/\- *theorem* pow_ne_zero

Modified src/algebra/group_with_zero.lean


Modified src/algebra/ring/basic.lean
- \- *lemma* units.coe_ne_zero
- \- *lemma* coe_dvd
- \- *lemma* dvd_coe_mul
- \- *lemma* dvd_coe
- \- *lemma* coe_mul_dvd
- \- *lemma* mul_right_dvd_of_dvd
- \- *lemma* mul_left_dvd_of_dvd
- \+/\- *theorem* two_dvd_bit1
- \- *theorem* mul_dvd_mul_iff_left

Modified src/analysis/normed_space/basic.lean


Modified src/data/equiv/ring.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/ring_division.lean


Modified src/field_theory/separable.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/ring_theory/ideal/basic.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/polynomial/rational_root.lean


Modified src/ring_theory/power_series.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* dvd_def
- \- *theorem* dvd_mul
- \- *theorem* dvd_trans
- \- *theorem* dvd_mul_of_dvd

Modified src/set_theory/ordinal_notation.lean




## [2020-08-11 07:24:07](https://github.com/leanprover-community/mathlib/commit/57df7f5)
feat(haar_measure): define the Haar measure ([#3542](https://github.com/leanprover-community/mathlib/pull/3542))
Define the Haar measure on a locally compact Hausdorff group.
Some additions and simplifications to outer_measure and content.
#### Estimated changes
Modified docs/references.bib


Modified src/measure_theory/content.lean
- \+ *lemma* inner_content_comap
- \+/\- *lemma* is_left_invariant_inner_content
- \+ *lemma* of_content_eq_infi
- \+ *lemma* of_content_preimage
- \+ *lemma* is_left_invariant_of_content
- \+ *lemma* of_content_caratheodory

Created src/measure_theory/haar_measure.lean
- \+ *lemma* index_empty
- \+ *lemma* prehaar_empty
- \+ *lemma* prehaar_nonneg
- \+ *lemma* mem_prehaar_empty
- \+ *lemma* index_defined
- \+ *lemma* index_elim
- \+ *lemma* le_index_mul
- \+ *lemma* index_pos
- \+ *lemma* index_mono
- \+ *lemma* index_union_le
- \+ *lemma* index_union_eq
- \+ *lemma* mul_left_index_le
- \+ *lemma* is_left_invariant_index
- \+ *lemma* prehaar_le_index
- \+ *lemma* prehaar_pos
- \+ *lemma* prehaar_mono
- \+ *lemma* prehaar_self
- \+ *lemma* prehaar_sup_le
- \+ *lemma* prehaar_sup_eq
- \+ *lemma* is_left_invariant_prehaar
- \+ *lemma* prehaar_mem_haar_product
- \+ *lemma* nonempty_Inter_cl_prehaar
- \+ *lemma* chaar_mem_haar_product
- \+ *lemma* chaar_mem_cl_prehaar
- \+ *lemma* chaar_nonneg
- \+ *lemma* chaar_empty
- \+ *lemma* chaar_self
- \+ *lemma* chaar_mono
- \+ *lemma* chaar_sup_le
- \+ *lemma* chaar_sup_eq
- \+ *lemma* is_left_invariant_chaar
- \+ *lemma* echaar_sup_le
- \+ *lemma* echaar_mono
- \+ *lemma* haar_outer_measure_eq_infi
- \+ *lemma* chaar_le_haar_outer_measure
- \+ *lemma* haar_outer_measure_of_is_open
- \+ *lemma* haar_outer_measure_le_chaar
- \+ *lemma* haar_outer_measure_exists_open
- \+ *lemma* haar_outer_measure_exists_compact
- \+ *lemma* haar_outer_measure_caratheodory
- \+ *lemma* one_le_haar_outer_measure_self
- \+ *lemma* haar_outer_measure_pos_of_is_open
- \+ *lemma* haar_outer_measure_self_pos
- \+ *lemma* haar_outer_measure_lt_top_of_is_compact
- \+ *lemma* haar_caratheodory_measurable
- \+ *lemma* haar_measure_apply
- \+ *lemma* is_left_invariant_haar_measure
- \+ *lemma* haar_measure_self
- \+ *lemma* haar_measure_pos_of_is_open
- \+ *lemma* regular_haar_measure
- \+ *def* index
- \+ *def* prehaar
- \+ *def* haar_product
- \+ *def* cl_prehaar
- \+ *def* chaar
- \+ *def* echaar
- \+ *def* haar_outer_measure
- \+ *def* haar_measure

Modified src/measure_theory/outer_measure.lean
- \+ *lemma* induced_outer_measure_preimage
- \+/\- *theorem* le_trim_iff

Modified src/topology/subset_properties.lean
- \+ *lemma* is_compact.inter_Inter_nonempty



## [2020-08-11 00:42:24](https://github.com/leanprover-community/mathlib/commit/43ceb3e)
chore(scripts): update nolints.txt ([#3734](https://github.com/leanprover-community/mathlib/pull/3734))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-10 19:28:55](https://github.com/leanprover-community/mathlib/commit/9e03995)
chore(algebra/ordered_field): cleanup ([#3723](https://github.com/leanprover-community/mathlib/pull/3723))
* drop `mul_zero_lt_mul_inv_of_pos` and `mul_zero_lt_mul_inv_of_neg`;
* add `iff` lemmas `one_div_pos/neg/nonneg/nonpos` replacing old
  implications;
* some lemmas now assume `≤` instead of `<`;
* rename `mul_lt_of_gt_div_of_neg` to `mul_lt_of_neg_of_div_lt`
  replacing `>` by `<`.
* add `mul_sub_mul_div_mul_neg_iff` and `mul_sub_mul_div_mul_nonpos_iff`,
  generate implications using `alias`;
* drop `div_pos_of_pos_of_pos` (use `div_pos`) and
  `div_nonneg_of_nonneg_of_pos` (use `div_nonneg`);
* replace `div_nonpos_of_nonpos_of_pos` with
  `div_nonpos_of_nonpos_of_nonneg`;
* replace `div_nonpos_of_nonneg_of_neg` with
  `div_nonpos_of_nonneg_of_nonpos`;
* replace `div_mul_le_div_mul_of_div_le_div_pos` and
  `div_mul_le_div_mul_of_div_le_div_pos'` with
  `div_mul_le_div_mul_of_div_le_div_nonneg`; I failed to find
  in the history why we had two equivalent lemmas.
* merge `le_mul_of_ge_one_right` and `le_mul_of_one_le_right'` into
  `le_mul_of_one_le_right`, rename old `le_mul_of_one_le_right` to
  `le_mul_of_one_le_right'`;
* ditto with `le_mul_of_ge_one_left`, `le_mul_of_one_le_left`, and
  `le_mul_of_one_le_left'`;
* ditto with `lt_mul_of_gt_one_right`, `lt_mul_of_one_lt_right`, and
  `lt_mul_of_one_lt_right'`;
* rename `div_lt_of_mul_lt_of_pos` to `div_lt_of_pos_of_lt_mul`;
* rename `div_lt_of_mul_gt_of_neg` to `div_lt_of_neg_of_mul_lt`;
* rename `mul_le_of_div_le_of_neg` to `mul_le_of_neg_of_div_le`;
* rename `div_le_of_mul_le_of_neg` to `div_le_of_neg_of_mul_le`;
* rename `div_lt_div_of_lt_of_pos` to `div_lt_div_of_pos_of_lt`, swap
  arguments;
* rename `div_le_div_of_le_of_pos` to `div_le_div_of_pos_of_le`, swap
  arguments;
* rename `div_lt_div_of_lt_of_neg` to `div_lt_div_of_neg_of_lt`, swap
  arguments;
* rename `div_le_div_of_le_of_neg` to `div_le_div_of_neg_of_le`, swap
  arguments;
* rename `one_div_lt_one_div_of_lt_of_neg` to
  `one_div_lt_one_div_of_neg_of_lt`;
* rename `one_div_le_one_div_of_le_of_neg` to
  `one_div_le_one_div_of_neg_of_le`;
* rename `le_of_one_div_le_one_div_of_neg` to
  `le_of_neg_of_one_div_le_one_div`;
* rename `lt_of_one_div_lt_one_div_of_neg` to
  `lt_of_neg_of_one_div_lt_one_div`;
* rename `one_div_le_of_one_div_le_of_pos` to
  `one_div_le_of_pos_of_one_div_le`;
* rename `one_div_le_of_one_div_le_of_neg` to
  `one_div_le_of_neg_of_one_div_le`.
#### Estimated changes
Modified src/algebra/archimedean.lean


Modified src/algebra/group_with_zero.lean
- \+ *lemma* zero_eq_inv

Modified src/algebra/ordered_field.lean
- \+/\- *lemma* inv_pos
- \+/\- *lemma* inv_nonneg
- \+/\- *lemma* inv_lt_zero
- \+/\- *lemma* inv_nonpos
- \+ *lemma* one_div_pos
- \+ *lemma* one_div_neg
- \+ *lemma* one_div_nonneg
- \+ *lemma* one_div_nonpos
- \+/\- *lemma* div_pos
- \+/\- *lemma* div_pos_of_neg_of_neg
- \+/\- *lemma* div_neg_of_neg_of_pos
- \+/\- *lemma* div_neg_of_pos_of_neg
- \+/\- *lemma* div_nonneg
- \+ *lemma* div_nonneg_of_nonpos
- \+ *lemma* div_nonpos_of_nonpos_of_nonneg
- \+ *lemma* div_nonpos_of_nonneg_of_nonpos
- \+/\- *lemma* one_le_div_of_le
- \+/\- *lemma* le_of_one_le_div
- \+/\- *lemma* one_lt_div_of_lt
- \+/\- *lemma* lt_of_one_lt_div
- \+ *lemma* mul_le_of_neg_of_div_le
- \+ *lemma* div_le_of_neg_of_mul_le
- \+ *lemma* mul_lt_of_neg_of_div_lt
- \+ *lemma* div_lt_of_pos_of_lt_mul
- \+ *lemma* div_lt_of_neg_of_mul_lt
- \+/\- *lemma* div_le_of_le_mul
- \+/\- *lemma* le_mul_of_div_le
- \+ *lemma* mul_sub_mul_div_mul_neg_iff
- \+ *lemma* mul_sub_mul_div_mul_nonpos_iff
- \+ *lemma* div_lt_div_of_pos_of_lt
- \+ *lemma* div_le_div_of_pos_of_le
- \+ *lemma* div_lt_div_of_neg_of_lt
- \+ *lemma* div_le_div_of_neg_of_le
- \+/\- *lemma* mul_le_mul_of_mul_div_le
- \+/\- *lemma* div_two_lt_of_pos
- \+ *lemma* div_mul_le_div_mul_of_div_le_div_nonneg
- \+ *lemma* one_div_lt_one_div_of_neg_of_lt
- \+ *lemma* one_div_le_one_div_of_neg_of_le
- \+ *lemma* le_of_neg_of_one_div_le_one_div
- \+ *lemma* lt_of_neg_of_one_div_lt_one_div
- \+ *lemma* one_div_le_of_pos_of_one_div_le
- \+ *lemma* one_div_le_of_neg_of_one_div_le
- \- *lemma* mul_zero_lt_mul_inv_of_pos
- \- *lemma* mul_zero_lt_mul_inv_of_neg
- \- *lemma* one_div_pos_of_pos
- \- *lemma* pos_of_one_div_pos
- \- *lemma* one_div_neg_of_neg
- \- *lemma* neg_of_one_div_neg
- \- *lemma* le_mul_of_ge_one_right
- \- *lemma* le_mul_of_ge_one_left
- \- *lemma* lt_mul_of_gt_one_right
- \- *lemma* mul_le_of_div_le_of_neg
- \- *lemma* div_le_of_mul_le_of_neg
- \- *lemma* mul_lt_of_gt_div_of_neg
- \- *lemma* div_lt_of_mul_lt_of_pos
- \- *lemma* div_lt_of_mul_gt_of_neg
- \- *lemma* mul_sub_mul_div_mul_neg
- \- *lemma* mul_sub_mul_div_mul_nonpos
- \- *lemma* div_lt_div_of_mul_sub_mul_div_neg
- \- *lemma* div_le_div_of_mul_sub_mul_div_nonpos
- \- *lemma* div_pos_of_pos_of_pos
- \- *lemma* div_nonneg_of_nonneg_of_pos
- \- *lemma* div_nonpos_of_nonpos_of_pos
- \- *lemma* div_nonpos_of_nonneg_of_neg
- \- *lemma* div_nonneg_of_nonpos_of_neg
- \- *lemma* div_lt_div_of_lt_of_pos
- \- *lemma* div_le_div_of_le_of_pos
- \- *lemma* div_lt_div_of_lt_of_neg
- \- *lemma* div_le_div_of_le_of_neg
- \- *lemma* div_mul_le_div_mul_of_div_le_div_pos
- \- *lemma* one_div_lt_one_div_of_lt_of_neg
- \- *lemma* one_div_le_one_div_of_le_of_neg
- \- *lemma* le_of_one_div_le_one_div_of_neg
- \- *lemma* lt_of_one_div_lt_one_div_of_neg
- \- *lemma* one_div_le_of_one_div_le_of_pos
- \- *lemma* one_div_le_of_one_div_le_of_neg
- \- *lemma* div_mul_le_div_mul_of_div_le_div_pos'
- \- *lemma* div_nonneg'

Modified src/algebra/ordered_group.lean
- \+ *lemma* le_mul_of_one_le_right'
- \+ *lemma* le_mul_of_one_le_left'
- \+ *lemma* lt_mul_of_one_lt_right'
- \+ *lemma* lt_mul_of_one_lt_left'
- \- *lemma* le_mul_of_one_le_right
- \- *lemma* le_mul_of_one_le_left
- \- *lemma* lt_mul_of_one_lt_right
- \- *lemma* lt_mul_of_one_lt_left

Modified src/algebra/ordered_ring.lean
- \+ *lemma* lt_mul_of_one_lt_right
- \+ *lemma* le_mul_of_one_le_right
- \+ *lemma* le_mul_of_one_le_left
- \- *lemma* lt_mul_of_one_lt_right'
- \- *lemma* le_mul_of_one_le_right'
- \- *lemma* le_mul_of_one_le_left'

Modified src/algebra/quadratic_discriminant.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/caratheodory.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/data/complex/exponential.lean


Modified src/data/nat/modeq.lean


Modified src/data/padics/hensel.lean


Modified src/data/polynomial/div.lean


Modified src/data/real/basic.lean


Modified src/data/real/conjugate_exponents.lean


Modified src/data/real/pi.lean


Modified src/data/zsqrtd/gaussian_int.lean


Modified src/tactic/cancel_denoms.lean


Modified src/tactic/norm_num.lean


Modified src/topology/algebra/polynomial.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/pi_Lp.lean


Modified src/topology/uniform_space/absolute_value.lean




## [2020-08-10 19:28:53](https://github.com/leanprover-community/mathlib/commit/4a75df9)
feat(group_theory/group_action): generalize `is_algebra_tower` ([#3717](https://github.com/leanprover-community/mathlib/pull/3717))
This PR introduces a new typeclass `is_scalar_tower R M N` stating that scalar multiplications between the three types are compatible: `smul_assoc : ((x : R) • (y : M)) • (z : N) = x • (y • z)`.
This typeclass is the general form of `is_algebra_tower`. It also generalizes some of the existing instances of `is_algebra_tower`. I didn't try very hard though, so I might have missed some instances.
Related Zulip discussions:
 * https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Effect.20of.20changing.20the.20base.20field.20on.20span
 * https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/pull.20back.20an.20R.20module.20along.20.60S.20-.3E.2B*.20R.60
#### Estimated changes
Modified src/algebra/module/pi.lean


Modified src/algebra/module/ulift.lean


Modified src/group_theory/group_action.lean
- \+ *lemma* smul_assoc

Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/ideal/operations.lean
- \- *theorem* smul_assoc



## [2020-08-10 17:55:47](https://github.com/leanprover-community/mathlib/commit/37e97b5)
feat(tactic): fix two bugs with generalize' ([#3710](https://github.com/leanprover-community/mathlib/pull/3710))
The name generated by `generalize'` will be exactly the given name, even if the name already occurs in the context.
There was a bug with `generalize' h : e = x` if `e` occurred in the goal.
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Modified test/tactics.lean




## [2020-08-10 15:19:08](https://github.com/leanprover-community/mathlib/commit/4786136)
feat(category_theory/limits): explicit isomorphisms between preserved limits ([#3602](https://github.com/leanprover-community/mathlib/pull/3602))
When `G` preserves limits, it's nice to be able to quickly obtain the iso `G.obj (pi_obj f) ≅ pi_obj (λ j, G.obj (f j))`.
#### Estimated changes
Modified src/algebra/category/Group/limits.lean


Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/creates.lean


Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/over.lean


Renamed src/category_theory/limits/preserves.lean to src/category_theory/limits/preserves/basic.lean


Created src/category_theory/limits/preserves/shapes.lean
- \+ *lemma* preserves_limits_iso_hom_π
- \+ *lemma* preserves_products_iso_hom_π
- \+ *lemma* map_lift_comp_preserves_products_iso_hom
- \+ *def* preserves_limits_iso
- \+ *def* preserves_products_iso

Modified src/category_theory/limits/shapes/constructions/preserve_binary_products.lean


Modified src/category_theory/limits/shapes/regular_mono.lean


Modified src/topology/category/Top/limits.lean




## [2020-08-10 12:46:02](https://github.com/leanprover-community/mathlib/commit/5680428)
chore(category_theory/limits): minor changes in equalizers and products ([#3603](https://github.com/leanprover-community/mathlib/pull/3603))
#### Estimated changes
Modified src/algebra/category/Group/abelian.lean


Modified src/algebra/category/Module/abelian.lean


Modified src/category_theory/abelian/non_preadditive.lean


Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/limits/opposites.lean
- \+ *def* has_limit_of_has_colimit_left_op
- \+ *def* has_limits_of_shape_op_of_has_colimits_of_shape
- \+ *def* has_limits_op_of_has_colimits
- \+ *def* has_colimit_of_has_limit_left_op
- \+ *def* has_colimits_of_shape_op_of_has_limits_of_shape
- \+ *def* has_colimits_op_of_has_limits
- \+ *def* has_coproducts_opposite
- \+ *def* has_products_opposite

Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/constructions/binary_products.lean


Modified src/category_theory/limits/shapes/constructions/equalizers.lean


Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/shapes/constructions/over/default.lean


Modified src/category_theory/limits/shapes/constructions/over/products.lean


Modified src/category_theory/limits/shapes/constructions/pullbacks.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* equalizer.fork_ι
- \+ *lemma* equalizer.fork_π_app_zero
- \+/\- *lemma* equalizer.iso_source_of_self_hom
- \+/\- *lemma* equalizer.iso_source_of_self_inv
- \+ *lemma* coequalizer.cofork_π
- \+ *lemma* coequalizer.cofork_ι_app_one
- \+/\- *lemma* coequalizer.iso_target_of_self_hom
- \+/\- *lemma* coequalizer.iso_target_of_self_inv
- \- *lemma* equalizer.ι.fork
- \- *lemma* equalizer.ι.eq_app_zero
- \- *lemma* coequalizer.π.cofork
- \- *lemma* coequalizer.π.eq_app_one
- \+ *def* fork.mk_hom
- \+/\- *def* equalizer.ι_of_eq
- \+/\- *def* equalizer.iso_source_of_self
- \+ *def* cofork.mk_hom
- \+/\- *def* coequalizer.π_of_eq
- \+/\- *def* coequalizer.iso_target_of_self

Modified src/category_theory/limits/shapes/finite_limits.lean
- \+ *def* has_finite_limits
- \+ *def* has_finite_colimits
- \+ *def* has_finite_wide_pullbacks
- \+ *def* has_finite_wide_pushouts
- \- *def* has_equalizers_of_has_finite_limits
- \- *def* has_coequalizers_of_has_finite_colimits
- \- *def* has_pullbacks_of_has_finite_limits
- \- *def* has_pushouts_of_has_finite_colimits

Modified src/category_theory/limits/shapes/finite_products.lean
- \+ *def* has_finite_products
- \+ *def* has_finite_products_of_has_products
- \+ *def* has_finite_coproducts
- \+ *def* has_finite_coproducts_of_has_coproducts

Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean
- \+/\- *lemma* pullback.lift_fst
- \+/\- *lemma* pullback.lift_snd
- \+/\- *lemma* pushout.inl_desc
- \+/\- *lemma* pushout.inr_desc
- \+/\- *lemma* pullback.condition
- \+/\- *lemma* pushout.condition
- \+/\- *lemma* pullback.hom_ext
- \+/\- *lemma* pushout.hom_ext
- \+/\- *def* pullback.lift'
- \+/\- *def* pullback.desc'

Modified src/category_theory/limits/shapes/terminal.lean


Modified src/category_theory/limits/shapes/types.lean
- \+ *lemma* pi
- \+ *lemma* pi_π
- \+ *lemma* pi_lift
- \+ *lemma* pi_map
- \+/\- *def* types_has_products

Modified src/category_theory/limits/shapes/wide_pullbacks.lean




## [2020-08-09 01:11:07](https://github.com/leanprover-community/mathlib/commit/17ef529)
refactor(linear_algebra/affine_space): split up file ([#3726](https://github.com/leanprover-community/mathlib/pull/3726))
`linear_algebra/affine_space.lean` was the 10th largest `.lean` file
in mathlib.  Move it to `linear_algebra/affine_space/basic.lean` and
split out some pieces into separate files, so reducing its size to
41st largest as well as reducing dependencies for users not needing
all those files.
More pieces could also be split out (for example, splitting out
`homothety` would eliminate the dependence of
`linear_algebra.affine_space.basic` on
`linear_algebra.tensor_product`), but this split seems a reasonable
starting point.
This split is intended to preserve the exact set of definitions
present and their namespaces, just moving some of them to different
files, even if the existing namespaces aren't very consistent
(e.g. some definitions relating to affine combinations are in the
`finset` namespace, so allowing dot notation to be used for such
combinations, but others are in the `affine_space` namespace, and
there may not be a consistent rule for the division between the two).
#### Estimated changes
Modified src/analysis/convex/basic.lean


Modified src/analysis/normed_space/mazur_ulam.lean


Modified src/geometry/euclidean.lean


Renamed src/linear_algebra/affine_space.lean to src/linear_algebra/affine_space/basic.lean
- \- *lemma* weighted_vsub_of_point_apply
- \- *lemma* weighted_vsub_of_point_eq_of_sum_eq_zero
- \- *lemma* weighted_vsub_of_point_vadd_eq_of_sum_eq_one
- \- *lemma* weighted_vsub_of_point_erase
- \- *lemma* weighted_vsub_of_point_insert
- \- *lemma* weighted_vsub_of_point_indicator_subset
- \- *lemma* weighted_vsub_apply
- \- *lemma* weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero
- \- *lemma* weighted_vsub_empty
- \- *lemma* weighted_vsub_indicator_subset
- \- *lemma* affine_combination_apply
- \- *lemma* affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one
- \- *lemma* weighted_vsub_vadd_affine_combination
- \- *lemma* affine_combination_vsub
- \- *lemma* affine_combination_of_eq_one_of_eq_zero
- \- *lemma* affine_combination_indicator_subset
- \- *lemma* eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype
- \- *lemma* eq_weighted_vsub_subset_iff_eq_weighted_vsub_subtype
- \- *lemma* eq_affine_combination_subset_iff_eq_affine_combination_subtype
- \- *lemma* affine_independent_of_subsingleton
- \- *lemma* affine_independent_iff_linear_independent_vsub
- \- *lemma* affine_independent_iff_indicator_eq_of_affine_combination_eq
- \- *lemma* affine_independent_embedding_of_affine_independent
- \- *lemma* affine_independent_subtype_of_affine_independent
- \- *lemma* mk_of_point_points
- \- *lemma* ext
- \- *lemma* ext_iff
- \- *lemma* face_points
- \- *lemma* face_eq_mk_of_point
- \- *lemma* finite_dimensional_vector_span_of_finite
- \- *lemma* finite_dimensional_direction_affine_span_of_finite
- \- *lemma* weighted_vsub_mem_vector_span
- \- *lemma* affine_combination_mem_affine_span
- \- *lemma* mem_vector_span_iff_eq_weighted_vsub
- \- *lemma* eq_affine_combination_of_mem_affine_span
- \- *lemma* mem_affine_span_iff_eq_affine_combination
- \- *lemma* exists_mem_inter_of_exists_mem_inter_affine_span_of_affine_independent
- \- *lemma* affine_span_disjoint_of_disjoint_of_affine_independent
- \- *lemma* mem_affine_span_iff_mem_of_affine_independent
- \- *lemma* not_mem_affine_span_diff_of_affine_independent
- \- *def* weighted_vsub_of_point
- \- *def* weighted_vsub
- \- *def* affine_combination
- \- *def* affine_independent
- \- *def* mk_of_point
- \- *def* face

Created src/linear_algebra/affine_space/combination.lean
- \+ *lemma* weighted_vsub_of_point_apply
- \+ *lemma* weighted_vsub_of_point_eq_of_sum_eq_zero
- \+ *lemma* weighted_vsub_of_point_vadd_eq_of_sum_eq_one
- \+ *lemma* weighted_vsub_of_point_erase
- \+ *lemma* weighted_vsub_of_point_insert
- \+ *lemma* weighted_vsub_of_point_indicator_subset
- \+ *lemma* weighted_vsub_apply
- \+ *lemma* weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero
- \+ *lemma* weighted_vsub_empty
- \+ *lemma* weighted_vsub_indicator_subset
- \+ *lemma* affine_combination_apply
- \+ *lemma* affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one
- \+ *lemma* weighted_vsub_vadd_affine_combination
- \+ *lemma* affine_combination_vsub
- \+ *lemma* affine_combination_of_eq_one_of_eq_zero
- \+ *lemma* affine_combination_indicator_subset
- \+ *lemma* eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype
- \+ *lemma* eq_weighted_vsub_subset_iff_eq_weighted_vsub_subtype
- \+ *lemma* eq_affine_combination_subset_iff_eq_affine_combination_subtype
- \+ *lemma* weighted_vsub_mem_vector_span
- \+ *lemma* affine_combination_mem_affine_span
- \+ *lemma* mem_vector_span_iff_eq_weighted_vsub
- \+ *lemma* eq_affine_combination_of_mem_affine_span
- \+ *lemma* mem_affine_span_iff_eq_affine_combination
- \+ *def* weighted_vsub_of_point
- \+ *def* weighted_vsub
- \+ *def* affine_combination

Created src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* finite_dimensional_vector_span_of_finite
- \+ *lemma* finite_dimensional_direction_affine_span_of_finite

Created src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_independent_of_subsingleton
- \+ *lemma* affine_independent_iff_linear_independent_vsub
- \+ *lemma* affine_independent_iff_indicator_eq_of_affine_combination_eq
- \+ *lemma* affine_independent_embedding_of_affine_independent
- \+ *lemma* affine_independent_subtype_of_affine_independent
- \+ *lemma* exists_mem_inter_of_exists_mem_inter_affine_span_of_affine_independent
- \+ *lemma* affine_span_disjoint_of_disjoint_of_affine_independent
- \+ *lemma* mem_affine_span_iff_mem_of_affine_independent
- \+ *lemma* not_mem_affine_span_diff_of_affine_independent
- \+ *lemma* mk_of_point_points
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* face_points
- \+ *lemma* face_eq_mk_of_point
- \+ *def* affine_independent
- \+ *def* mk_of_point
- \+ *def* face

Modified src/topology/algebra/affine.lean




## [2020-08-08 14:34:18](https://github.com/leanprover-community/mathlib/commit/f23fe9a)
doc(tactic/lean_core_docs): by_cases is classical ([#3718](https://github.com/leanprover-community/mathlib/pull/3718))
`by_cases` was changed to use classical reasoning (leanprover-community/mathlib[#3354](https://github.com/leanprover-community/mathlib/pull/3354), leanprover-community/lean[#409](https://github.com/leanprover-community/mathlib/pull/409)), but the documentation hasn't been updated yet.
I leave `by_contra` alone as it still uses `decidable`.
#### Estimated changes
Modified src/tactic/lean_core_docs.lean




## [2020-08-08 13:01:43](https://github.com/leanprover-community/mathlib/commit/d27ddb4)
chore(linear_algebra/basic): rewrite `p.comap q.subtype` to `comap q.subtype p` ([#3725](https://github.com/leanprover-community/mathlib/pull/3725))
@PatrickMassot requested this change in the review of [#3720](https://github.com/leanprover-community/mathlib/pull/3720):
> I find this statement very difficult to read. I think this is a bad use of dot notation, it really feels like `p` is pulling back `q.subtype` instead of the other way around (and even the docstring is suggesting that!). The same problem happens with filter.(co)map and always try to avoid it.
> I would open submodule and then write `comap q.subtype p ≃ₗ[R] p`.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+/\- *lemma* comap_subtype_self



## [2020-08-08 10:16:01](https://github.com/leanprover-community/mathlib/commit/1675dc4)
chore(order/complete_lattice): use `order_dual` ([#3724](https://github.com/leanprover-community/mathlib/pull/3724))
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+/\- *theorem* infi_infi_eq_left
- \+/\- *theorem* infi_infi_eq_right
- \+/\- *theorem* supr_supr_eq_left
- \+/\- *theorem* supr_supr_eq_right
- \+/\- *theorem* infi_exists
- \+/\- *theorem* supr_exists
- \+/\- *theorem* infi_insert
- \+/\- *theorem* supr_insert
- \- *theorem* infi_le₂'



## [2020-08-08 09:22:19](https://github.com/leanprover-community/mathlib/commit/bf1c7b7)
feat(linear_algebra/finite_dimensional): finite dimensional `is_basis` helpers ([#3720](https://github.com/leanprover-community/mathlib/pull/3720))
If we have a family of vectors in `V` with cardinality equal to the (finite) dimension of `V` over a field `K`, they span the whole space iff they are linearly independent.
This PR proves those two facts (in the form that either of the conditions of `is_basis K b` suffices to prove `is_basis K b` if `b` has the right cardinality).
We don't need to assume that `V` is finite dimensional, because the case that `findim K V = 0` will generally lead to a contradiction. We do sometimes need to assume that the family is nonempty, which seems like a much nicer condition.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* nontrivial_of_lt_top
- \+ *def* comap_subtype_equiv_of_le

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* findim_pos_iff_exists_ne_zero
- \+ *lemma* findim_pos_iff
- \+ *lemma* findim_pos
- \+ *lemma* findim_lt
- \+ *lemma* findim_mono
- \+ *lemma* lt_of_le_of_findim_lt_findim
- \+ *lemma* lt_top_of_findim_lt_findim
- \+ *lemma* findim_span_le_card
- \+ *lemma* findim_span_eq_card
- \+ *lemma* findim_span_set_eq_card
- \+ *lemma* span_lt_of_subset_of_card_lt_findim
- \+ *lemma* span_lt_top_of_card_lt_findim
- \+ *lemma* linear_independent_of_span_eq_top_of_card_eq_findim
- \+ *lemma* is_basis_of_span_eq_top_of_card_eq_findim
- \+ *lemma* finset_is_basis_of_span_eq_top_of_card_eq_findim
- \+ *lemma* set_is_basis_of_span_eq_top_of_card_eq_findim
- \+ *lemma* span_eq_top_of_linear_independent_of_card_eq_findim
- \+ *lemma* is_basis_of_linear_independent_of_card_eq_findim
- \+ *lemma* finset_is_basis_of_linear_independent_of_card_eq_findim
- \+ *lemma* set_is_basis_of_linear_independent_of_card_eq_findim



## [2020-08-07 21:33:16](https://github.com/leanprover-community/mathlib/commit/d61bd4a)
feat(algebra/classical_lie_algebras): add lie_algebra.orthogonal.mem_so ([#3711](https://github.com/leanprover-community/mathlib/pull/3711))
Also unrelated change to use new notation for direct_sum
#### Estimated changes
Modified src/algebra/classical_lie_algebras.lean
- \+ *lemma* mem_so

Modified src/algebra/lie_algebra.lean
- \+/\- *lemma* bracket_apply



## [2020-08-07 19:53:30](https://github.com/leanprover-community/mathlib/commit/1cd74b1)
fix(linear_algebra/finite_dimensional): universe generalize cardinal_mk_le_findim_of_linear_independent ([#3721](https://github.com/leanprover-community/mathlib/pull/3721))
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *lemma* {m}
- \+/\- *lemma* cardinal_le_dim_of_linear_independent
- \+ *theorem* {m}

Modified src/linear_algebra/finite_dimensional.lean




## [2020-08-07 18:26:21](https://github.com/leanprover-community/mathlib/commit/00e4c04)
doc(linear_algebra/affine_space): expand module doc string ([#3719](https://github.com/leanprover-community/mathlib/pull/3719))
Make module doc string discuss the main definitions relating to affine
spaces.
#### Estimated changes
Modified src/linear_algebra/affine_space.lean




## [2020-08-07 18:26:19](https://github.com/leanprover-community/mathlib/commit/4e24f4c)
feat(data/list/*): add indexed versions of some list functions ([#2191](https://github.com/leanprover-community/mathlib/pull/2191))
Add `foldr_with_index`, `foldl_with_index`, `mfoldr_with_index`, `mfoldl_with_index`, `mmap_with_index` and `mmap_with_index'`. The new functions are proven correct by relating them to their non-indexed counterparts.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* map_eq_foldr
- \+ *theorem* map_filter_eq_foldr
- \+ *theorem* mfoldr_eq_foldr
- \+ *theorem* mfoldl_eq_foldl
- \+ *theorem* filter_eq_foldr

Modified src/data/list/default.lean


Modified src/data/list/defs.lean
- \+ *def* foldl_with_index_aux
- \+ *def* foldl_with_index
- \+ *def* foldr_with_index_aux
- \+ *def* foldr_with_index
- \+/\- *def* indexes_values
- \+/\- *def* indexes_of
- \+ *def* mfoldl_with_index
- \+ *def* mfoldr_with_index
- \+ *def* mmap_with_index_aux
- \+ *def* mmap_with_index
- \+ *def* mmap_with_index'_aux
- \+ *def* mmap_with_index'
- \- *def* indexes_values_aux

Created src/data/list/indexes.lean
- \+ *theorem* foldr_with_index_aux_spec_cons
- \+ *theorem* foldr_with_index_aux_eq_foldr_with_index_aux_spec
- \+ *theorem* foldr_with_index_eq_foldr_enum
- \+ *theorem* indexes_values_eq_filter_enum
- \+ *theorem* find_indexes_eq_map_indexes_values
- \+ *theorem* foldl_with_index_aux_spec_cons
- \+ *theorem* foldl_with_index_aux_eq_foldl_with_index_aux_spec
- \+ *theorem* foldl_with_index_eq_foldl_enum
- \+ *theorem* mfoldr_with_index_eq_mfoldr_enum
- \+ *theorem* mfoldl_with_index_eq_mfoldl_enum
- \+ *theorem* mmap_with_index_aux_spec_cons
- \+ *theorem* mmap_with_index_aux_eq_mmap_with_index_aux_spec
- \+ *theorem* mmap_with_index_eq_mmap_enum
- \+ *theorem* mmap_with_index'_aux_eq_mmap_with_index_aux
- \+ *theorem* mmap_with_index'_eq_mmap_with_index
- \+ *def* foldr_with_index_aux_spec
- \+ *def* foldl_with_index_aux_spec
- \+ *def* mmap_with_index_aux_spec

Modified src/data/list/zip.lean
- \+ *theorem* map_fst_zip
- \+ *theorem* map_snd_zip



## [2020-08-07 16:49:27](https://github.com/leanprover-community/mathlib/commit/aacd757)
feat(measurable_space): more properties of measurable sets in a product ([#3703](https://github.com/leanprover-community/mathlib/pull/3703))
Add multiple lemmas about `prod` to `set.basic`
Some cleanup in `set.basic`
Fix the name of the instance `measure_space ℝ`
Cleanup and a couple of additions to the `prod` section of `measurable_space`.
Rename: `prod_singleton_singleton` -> `singleton_prod_singleton`
Use `prod.swap` in the statement of `image_swap_prod`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *lemma* set_of_eq_eq_singleton
- \+/\- *lemma* diff_self
- \+/\- *lemma* image_id'
- \+/\- *lemma* prod_eq
- \+/\- *lemma* mk_mem_prod
- \+ *lemma* mk_preimage_prod_left
- \+ *lemma* mk_preimage_prod_right
- \+/\- *theorem* image_empty
- \+/\- *theorem* mem_prod_eq
- \+/\- *theorem* mem_prod
- \+/\- *theorem* prod_mk_mem_set_prod_eq
- \+/\- *theorem* prod_mono
- \+/\- *theorem* prod_empty
- \+/\- *theorem* univ_prod_univ
- \+ *theorem* singleton_prod
- \+ *theorem* prod_singleton
- \+ *theorem* singleton_prod_singleton
- \+ *theorem* union_prod
- \+ *theorem* prod_union
- \+/\- *theorem* prod_inter_prod
- \+/\- *theorem* image_swap_prod
- \- *theorem* prod_singleton_singleton

Modified src/data/set/lattice.lean
- \+/\- *lemma* prod_eq_seq

Modified src/measure_theory/integration.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable_fst
- \+/\- *lemma* measurable.fst
- \+/\- *lemma* measurable_snd
- \+/\- *lemma* measurable.snd
- \+/\- *lemma* measurable.prod
- \+/\- *lemma* measurable.prod_mk
- \+/\- *lemma* is_measurable.prod
- \+ *lemma* is_measurable_prod_of_nonempty
- \+ *lemma* is_measurable_prod

Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/subset_properties.lean




## [2020-08-07 00:44:48](https://github.com/leanprover-community/mathlib/commit/49ba4c4)
chore(scripts): update nolints.txt ([#3712](https://github.com/leanprover-community/mathlib/pull/3712))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-06 16:42:35](https://github.com/leanprover-community/mathlib/commit/1930601)
feat(algebra/group_power): lemmas relating pow in `multiplicative int` with multiplication in `int` ([#3706](https://github.com/leanprover-community/mathlib/pull/3706))
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *lemma* nat.to_add_pow
- \+ *lemma* nat.of_add_mul
- \+ *lemma* int.to_add_pow
- \+ *lemma* int.to_add_gpow
- \+ *lemma* int.of_add_mul



## [2020-08-06 16:42:33](https://github.com/leanprover-community/mathlib/commit/35ecc7b)
feat(analysis/calculus): Rolle's and Cauchy's mean value theorems with weaker assumptions (deps : 3590) ([#3681](https://github.com/leanprover-community/mathlib/pull/3681))
This introduces stronger versions of Rolle's theorem and Cauchy's mean value theorem, essentially by encapsulating an extension by continuity using the newly introduced `extend_from` of [#3590](https://github.com/leanprover-community/mathlib/pull/3590)
#### Estimated changes
Modified src/analysis/calculus/local_extr.lean
- \+ *lemma* exists_has_deriv_at_eq_zero'
- \+ *lemma* exists_deriv_eq_zero'

Modified src/analysis/calculus/mean_value.lean
- \+ *lemma* exists_ratio_has_deriv_at_eq_ratio_slope'
- \+ *lemma* exists_ratio_deriv_eq_ratio_slope'



## [2020-08-06 16:42:31](https://github.com/leanprover-community/mathlib/commit/e57fc3d)
feat(field_theory/splitting_field): splitting field unique ([#3654](https://github.com/leanprover-community/mathlib/pull/3654))
Main theorem:
```lean
polynomial.is_splitting_field.alg_equiv {α} (β) [field α] [field β] [algebra α β]
  (f : polynomial α) [is_splitting_field α β f] : β ≃ₐ[α] splitting_field f
````
#### Estimated changes
Modified src/algebra/group/hom.lean


Modified src/data/equiv/ring.lean
- \+/\- *lemma* to_ring_hom_apply_symm_to_ring_hom_apply
- \+/\- *lemma* symm_to_ring_hom_apply_to_ring_hom_apply
- \+ *lemma* to_ring_hom_trans
- \+/\- *lemma* ext
- \+ *theorem* trans_symm
- \+ *theorem* symm_trans

Modified src/data/finset/basic.lean
- \+ *theorem* multiset.to_finset_map

Modified src/data/list/basic.lean
- \+ *theorem* prod_ne_zero

Modified src/data/multiset/basic.lean
- \+ *theorem* forall_mem_cons
- \+ *theorem* forall_mem_map_iff
- \+ *theorem* prod_ne_zero

Modified src/data/polynomial/eval.lean
- \+ *lemma* map_list_prod
- \+ *lemma* map_multiset_prod
- \+ *lemma* map_prod

Modified src/data/polynomial/field_division.lean
- \+ *lemma* map_ne_zero

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* roots_zero
- \+ *lemma* roots_C
- \+ *lemma* roots_one
- \+ *lemma* roots_list_prod
- \+ *lemma* roots_multiset_prod

Modified src/field_theory/minimal_polynomial.lean
- \+/\- *lemma* prime
- \+/\- *lemma* irreducible

Modified src/field_theory/splitting_field.lean
- \+ *theorem* roots_map
- \+ *theorem* lift_of_splits
- \+ *theorem* splits_iff
- \+ *theorem* mul
- \+ *theorem* finite_dimensional
- \+ *def* alg_equiv.adjoin_singleton_equiv_adjoin_root_minimal_polynomial
- \+ *def* lift
- \+ *def* alg_equiv

Modified src/linear_algebra/finite_dimensional.lean
- \+ *theorem* dim_eq_zero
- \+ *theorem* findim_eq_zero
- \+ *theorem* findim_top
- \+ *theorem* injective_iff_surjective_of_findim_eq_findim
- \+ *theorem* findim_le_findim_of_injective

Modified src/ring_theory/adjoin_root.lean
- \+ *lemma* coe_alg_hom
- \+ *def* alg_hom

Modified src/ring_theory/algebra.lean
- \+ *theorem* injective_iff
- \+ *theorem* injective_cod_restrict
- \+ *theorem* surjective_algbera_map_iff
- \+ *theorem* bijective_algbera_map_iff
- \+ *def* of_bijective
- \+ *def* cod_restrict
- \+ *def* bot_equiv_of_injective
- \+ *def* bot_equiv

Modified src/ring_theory/algebra_tower.lean
- \+ *lemma* res_top
- \+ *lemma* mem_res
- \+ *lemma* res_inj
- \+/\- *theorem* range_under_adjoin
- \- *theorem* subalgebra_comap_top
- \+ *def* res
- \+ *def* of_under
- \- *def* subalgebra_comap

Modified src/ring_theory/subsemiring.lean




## [2020-08-06 15:42:26](https://github.com/leanprover-community/mathlib/commit/bc2bcac)
chore(algebra/module): Move submodule to its own file ([#3696](https://github.com/leanprover-community/mathlib/pull/3696))
#### Estimated changes
Modified src/algebra/module/basic.lean
- \- *lemma* zero_mem
- \- *lemma* add_mem
- \- *lemma* smul_mem
- \- *lemma* sum_mem
- \- *lemma* sum_smul_mem
- \- *lemma* smul_mem_iff'
- \- *lemma* mk_eq_zero
- \- *lemma* coe_eq_coe
- \- *lemma* coe_eq_zero
- \- *lemma* coe_add
- \- *lemma* coe_zero
- \- *lemma* coe_smul
- \- *lemma* coe_mk
- \- *lemma* coe_mem
- \- *lemma* subtype_eq_val
- \- *lemma* neg_mem
- \- *lemma* coe_to_add_subgroup
- \- *lemma* sub_mem
- \- *lemma* neg_mem_iff
- \- *lemma* add_mem_iff_left
- \- *lemma* add_mem_iff_right
- \- *lemma* coe_neg
- \- *lemma* coe_sub
- \- *theorem* coe_sort_coe
- \- *theorem* coe_injective
- \- *theorem* coe_set_eq
- \- *theorem* ext'_iff
- \- *theorem* ext
- \- *theorem* to_add_submonoid_injective
- \- *theorem* to_add_submonoid_eq
- \- *theorem* mem_coe
- \- *theorem* subtype_apply
- \- *theorem* smul_mem_iff
- \- *def* to_add_subgroup

Modified src/algebra/module/default.lean


Created src/algebra/module/submodule.lean
- \+ *lemma* zero_mem
- \+ *lemma* add_mem
- \+ *lemma* smul_mem
- \+ *lemma* sum_mem
- \+ *lemma* sum_smul_mem
- \+ *lemma* smul_mem_iff'
- \+ *lemma* mk_eq_zero
- \+ *lemma* coe_eq_coe
- \+ *lemma* coe_eq_zero
- \+ *lemma* coe_add
- \+ *lemma* coe_zero
- \+ *lemma* coe_smul
- \+ *lemma* coe_mk
- \+ *lemma* coe_mem
- \+ *lemma* subtype_eq_val
- \+ *lemma* neg_mem
- \+ *lemma* coe_to_add_subgroup
- \+ *lemma* sub_mem
- \+ *lemma* neg_mem_iff
- \+ *lemma* add_mem_iff_left
- \+ *lemma* add_mem_iff_right
- \+ *lemma* coe_neg
- \+ *lemma* coe_sub
- \+ *theorem* coe_sort_coe
- \+ *theorem* coe_injective
- \+ *theorem* coe_set_eq
- \+ *theorem* ext'_iff
- \+ *theorem* ext
- \+ *theorem* to_add_submonoid_injective
- \+ *theorem* to_add_submonoid_eq
- \+ *theorem* mem_coe
- \+ *theorem* subtype_apply
- \+ *theorem* smul_mem_iff
- \+ *def* to_add_subgroup

Modified src/linear_algebra/basic.lean




## [2020-08-06 14:19:33](https://github.com/leanprover-community/mathlib/commit/224e0f8)
docs(tactic/interactive): Add tag `debugging` and doc `mwe` for `extract_goal` ([#3708](https://github.com/leanprover-community/mathlib/pull/3708))
Requested by @kbuzzard on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Being.20stuck.20-.3E.20MWE/near/206124861).
x-ref: leanprover-community/leanprover-community.github.io[#105](https://github.com/leanprover-community/mathlib/pull/105)
#### Estimated changes
Modified src/tactic/interactive.lean




## [2020-08-06 09:35:08](https://github.com/leanprover-community/mathlib/commit/ee7bb12)
chore(ring_theory/ideal): Move ideal modules into a single folder ([#3707](https://github.com/leanprover-community/mathlib/pull/3707))
The main motivation is to fix the odd inconsistency of `ideals` being plural, while most other files have singular names.
Besides that, there seems to be precedent for grouping together such files
#### Estimated changes
Modified scripts/nolints.txt


Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/linear_algebra/adic_completion.lean


Modified src/linear_algebra/invariant_basis_number.lean


Modified src/number_theory/basic.lean


Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/free_comm_ring.lean


Renamed src/ring_theory/ideals.lean to src/ring_theory/ideal/basic.lean


Renamed src/ring_theory/ideal_operations.lean to src/ring_theory/ideal/operations.lean


Renamed src/ring_theory/ideal_over.lean to src/ring_theory/ideal/over.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/jacobson_ideal.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/power_series.lean


Modified src/ring_theory/valuation/basic.lean


Modified src/topology/algebra/ring.lean




## [2020-08-06 06:58:32](https://github.com/leanprover-community/mathlib/commit/3eea109)
feat(measure_theory/interval_integral): introduce `∫ x in a..b, f x`, prove FTC-1 ([#3640](https://github.com/leanprover-community/mathlib/pull/3640))
Define `∫ x in a..b, f x ∂μ` as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. With this definition for a probability measure `μ` we have `F_μ(b)-F_μ(a)=∫ x in a..b, f x ∂μ`, where `F_μ` is the cumulative distribution function.
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* integral_mono_of_nonneg
- \+ *lemma* norm_integral_le_of_norm_le
- \+ *lemma* norm_integral_le_of_norm_le_const
- \+/\- *lemma* integral_add_meas
- \+ *lemma* integral_map_meas

Created src/measure_theory/interval_integral.lean
- \+ *lemma* symm
- \+ *lemma* refl
- \+ *lemma* trans
- \+ *lemma* neg
- \+ *lemma* smul
- \+ *lemma* add
- \+ *lemma* sub
- \+ *lemma* integral_of_le
- \+ *lemma* integral_same
- \+ *lemma* integral_symm
- \+ *lemma* integral_of_ge
- \+ *lemma* integral_cases
- \+ *lemma* norm_integral_eq_norm_integral_Ioc
- \+ *lemma* norm_integral_le_integral_norm_Ioc
- \+ *lemma* norm_integral_le_abs_integral_norm
- \+ *lemma* norm_integral_le_of_norm_le_const_ae
- \+ *lemma* norm_integral_le_of_norm_le_const
- \+ *lemma* integral_add
- \+ *lemma* integral_neg
- \+ *lemma* integral_add_adjacent_intervals_cancel
- \+ *lemma* integral_add_adjacent_intervals
- \+ *lemma* integral_sub_linear_is_o_of_tendsto_ae
- \+ *lemma* integral_same_has_deriv_at_of_tendsto_ae
- \+ *lemma* integral_has_deriv_at_of_tendsto_ae
- \+ *def* interval_integrable
- \+ *def* interval_integral

Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable.mono'
- \+ *lemma* integrable.congr'
- \+ *lemma* integrable_congr'
- \+ *lemma* integrable_const_iff
- \+/\- *lemma* integrable_const
- \+ *lemma* integrable_of_bounded
- \+ *lemma* integrable_add_meas
- \+ *lemma* integrable_zero_meas
- \+ *lemma* integrable_map_meas
- \- *lemma* integrable.mono_set
- \- *lemma* integrable.union
- \- *lemma* integrable_of_integrable_bound

Modified src/measure_theory/set_integral.lean
- \+ *lemma* piecewise_ae_eq_restrict
- \+ *lemma* piecewise_ae_eq_restrict_compl
- \+ *lemma* indicator_ae_eq_restrict
- \+ *lemma* indicator_ae_eq_restrict_compl
- \+ *lemma* integrable_on.integrable
- \+ *lemma* integrable_on_empty
- \+ *lemma* integrable_on_univ
- \+ *lemma* integrable_on_zero
- \+ *lemma* integrable_on_const
- \+ *lemma* integrable_on.mono
- \+ *lemma* integrable_on.mono_set
- \+ *lemma* integrable_on.mono_meas
- \+ *lemma* integrable_on.mono_set_ae
- \+ *lemma* integrable.integrable_on
- \+ *lemma* integrable.integrable_on'
- \+ *lemma* integrable_on.left_of_union
- \+ *lemma* integrable_on.right_of_union
- \+ *lemma* integrable_on.union
- \+ *lemma* integrable_on_union
- \+ *lemma* integrable_on_finite_union
- \+ *lemma* integrable_on_finset_union
- \+ *lemma* integrable_on.add_meas
- \+ *lemma* integrable_on_add_meas
- \+ *lemma* integrable_indicator_iff
- \+ *lemma* integrable_on.indicator
- \+ *lemma* integrable_on_of_bounded
- \+ *lemma* integrable_at_filter.filter_mono
- \+ *lemma* integrable_at_filter.inf_of_left
- \+ *lemma* integrable_at_filter.inf_of_right
- \+ *lemma* integrable_at_filter.inf_ae_iff
- \+ *lemma* measure.finite_at_filter.integrable_at_filter
- \+ *lemma* measure.finite_at_filter.integrable_at_filter_of_tendsto_ae
- \+ *lemma* measure.finite_at_filter.integrable_at_filter_of_tendsto
- \+ *lemma* integral_union
- \+ *lemma* integral_empty
- \+ *lemma* integral_univ
- \+ *lemma* integral_add_compl
- \+ *lemma* integral_indicator
- \+ *lemma* set_integral_const
- \+ *lemma* norm_set_integral_le_of_norm_le_const_ae
- \+ *lemma* norm_set_integral_le_of_norm_le_const_ae'
- \+ *lemma* norm_set_integral_le_of_norm_le_const_ae''
- \+ *lemma* norm_set_integral_le_of_norm_le_const
- \+ *lemma* norm_set_integral_le_of_norm_le_const'
- \+ *lemma* filter.tendsto.integral_sub_linear_is_o_ae
- \+ *lemma* is_compact.integrable_on_of_nhds_within
- \+ *lemma* continuous_on.integrable_on_compact
- \+ *lemma* continuous.integrable_on_compact
- \+ *lemma* continuous_at.integral_sub_linear_is_o_ae
- \- *lemma* integral_on_smul
- \- *lemma* integral_on_mul_left
- \- *lemma* integral_on_mul_right
- \- *lemma* integral_on_div
- \- *lemma* integral_on_neg
- \+ *theorem* for
- \+ *def* integrable_on
- \+ *def* integrable_at_filter



## [2020-08-06 03:47:24](https://github.com/leanprover-community/mathlib/commit/5cba21d)
chore(*): swap order of [fintype A] [decidable_eq A] ([#3705](https://github.com/leanprover-community/mathlib/pull/3705))
@fpvandoorn  suggested in [#3603](https://github.com/leanprover-community/mathlib/pull/3603) swapping the order of some `[fintype A] [decidable_eq A]` arguments to solve a linter problem with slow typeclass lookup.
The reasoning is that Lean solves typeclass search problems from right to left, and 
* it's "less likely" that a type is a `fintype` than it has `decidable_eq`, so we can fail earlier if `fintype` comes second
* typeclass search for `[decidable_eq]` can already be slow, so it's better to avoid it.
This PR applies this suggestion across the library.
#### Estimated changes
Modified src/algebra/lie_algebra.lean
- \+/\- *lemma* matrix.reindex_lie_equiv_apply
- \+/\- *lemma* matrix.reindex_lie_equiv_symm_apply
- \+/\- *def* matrix.reindex_lie_equiv
- \+/\- *def* skew_adjoint_matrices_lie_subalgebra_equiv_transpose

Modified src/data/equiv/list.lean
- \+/\- *def* fintype_arrow
- \+/\- *def* fintype_pi

Modified src/data/fintype/basic.lean
- \+/\- *lemma* finset.card_univ_diff
- \+/\- *theorem* quotient.fin_choice_eq
- \+/\- *def* equiv_fin
- \+/\- *def* of_surjective
- \+/\- *def* quotient.fin_choice

Modified src/data/fintype/card.lean
- \+/\- *lemma* fintype.card_pi
- \+/\- *lemma* fintype.card_fun
- \+/\- *lemma* finset.prod_fiberwise
- \+/\- *lemma* fintype.prod_fiberwise

Modified src/data/matrix/basic.lean
- \+/\- *def* scalar

Modified src/field_theory/finite.lean
- \+/\- *lemma* card_image_polynomial_eval

Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* is_cyclic_of_order_of_eq_card
- \+/\- *lemma* order_of_eq_card_of_forall_mem_gpowers
- \+/\- *lemma* is_cyclic.card_pow_eq_one_le
- \+/\- *lemma* is_cyclic.card_order_of_eq_totient

Modified src/linear_algebra/char_poly.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/matrix.lean
- \+/\- *theorem* to_matrix_of_equiv

Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/linear_algebra/quadratic_form.lean


Modified src/linear_algebra/special_linear_group.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/integral_domain.lean
- \+/\- *def* field_of_integral_domain

Modified src/ring_theory/polynomial_algebra.lean




## [2020-08-06 00:42:41](https://github.com/leanprover-community/mathlib/commit/f8fd0c3)
chore(scripts): update nolints.txt ([#3704](https://github.com/leanprover-community/mathlib/pull/3704))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-05 22:44:03](https://github.com/leanprover-community/mathlib/commit/9d3c709)
chore(algebra/module): Reuse proofs from subgroup ([#3631](https://github.com/leanprover-community/mathlib/pull/3631))
Confusingly these have opposite names - someone can always fix the names later though.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+/\- *lemma* sub_mem
- \+/\- *lemma* add_mem_iff_left
- \+/\- *lemma* add_mem_iff_right



## [2020-08-05 22:44:01](https://github.com/leanprover-community/mathlib/commit/2918b00)
feat(topology): define `extend_from`, add lemmas about extension by continuity on sets and intervals and continuity gluing ([#3590](https://github.com/leanprover-community/mathlib/pull/3590))
#### Add a new file `topology/extend_from_subset` (mostly by @PatrickMassot )
Define `extend_from A f` (where `f : X → Y` and `A : set X`) to be a function `g : X → Y` which maps any
`x₀ : X` to the limit of `f` as `x` tends to `x₀`, if such a limit exists. Although this is not really an extension, it maps with the classical meaning of extending a function *defined on a set*, hence the name. In some way it is analogous to `dense_inducing.extend`, but in `set` world.
The main theorem about this is `continuous_on_extend_from` about extension by continuity
#### Corollaries for extending functions defined on intervals
A few lemmas of the form : if `f` is continuous on `Ioo a b`, then `extend_from (Ioo a b) f` is continuous on `I[cc/co/oc] a b`, provided some assumptions about limits on the boundary (and has some other properties, e.g it is equal to `f` on `Ioo a b`)
#### More general continuity gluing
Lemmas `continuous_on_if'` and its corollaries `continuous_on_if` and `continuous_if'`, and a few other continuity lemmas
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* mem_Ioo_or_eq_endpoints_of_mem_Icc
- \+ *lemma* mem_Ioo_or_eq_left_of_mem_Ico
- \+ *lemma* mem_Ioo_or_eq_right_of_mem_Ioc

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* tendsto_inv_nhds_within_Ioi
- \+/\- *lemma* tendsto_inv_nhds_within_Iio
- \+/\- *lemma* tendsto_inv_nhds_within_Ioi_inv
- \+/\- *lemma* tendsto_inv_nhds_within_Iio_inv
- \+ *lemma* nhds_left_sup_nhds_right
- \+ *lemma* nhds_left'_sup_nhds_right
- \+ *lemma* nhds_left_sup_nhds_right'
- \+ *lemma* continuous_at_iff_continuous_left_right
- \+ *lemma* continuous_on_Icc_extend_from_Ioo
- \+ *lemma* eq_lim_at_left_extend_from_Ioo
- \+ *lemma* eq_lim_at_right_extend_from_Ioo
- \+ *lemma* continuous_on_Ico_extend_from_Ioo
- \+ *lemma* continuous_on_Ioc_extend_from_Ioo
- \+ *lemma* continuous_within_at_Ioi_iff_Ici
- \+ *lemma* continuous_within_at_Iio_iff_Iic
- \+ *lemma* continuous_at_iff_continuous_left'_right'

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_within_at_of_not_mem_closure
- \+ *lemma* continuous_on_if'
- \+ *lemma* continuous_on_if
- \+ *lemma* continuous_if'

Created src/topology/extend_from_subset.lean
- \+ *lemma* tendsto_extend_from
- \+ *lemma* extend_from_eq
- \+ *lemma* extend_from_extends
- \+ *lemma* continuous_on_extend_from
- \+ *lemma* continuous_extend_from
- \+ *def* extend_from



## [2020-08-05 21:26:53](https://github.com/leanprover-community/mathlib/commit/89ada87)
chore(algebra, data/pnat): refactoring comm_semiring_has_dvd into comm_monoid_has_dvd ([#3702](https://github.com/leanprover-community/mathlib/pull/3702))
changes the instance comm_semiring_has_dvd to apply to any comm_monoid
cleans up the pnat API to use this new definition
#### Estimated changes
Created src/algebra/divisibility.lean
- \+ *lemma* zero_dvd_iff
- \+ *theorem* dvd.intro
- \+ *theorem* dvd.intro_left
- \+ *theorem* exists_eq_mul_right_of_dvd
- \+ *theorem* dvd.elim
- \+ *theorem* exists_eq_mul_left_of_dvd
- \+ *theorem* dvd.elim_left
- \+ *theorem* dvd_refl
- \+ *theorem* dvd_trans
- \+ *theorem* one_dvd
- \+ *theorem* dvd_mul_right
- \+ *theorem* dvd_mul_left
- \+ *theorem* dvd_mul_of_dvd_left
- \+ *theorem* dvd_mul_of_dvd_right
- \+ *theorem* mul_dvd_mul
- \+ *theorem* mul_dvd_mul_left
- \+ *theorem* mul_dvd_mul_right
- \+ *theorem* dvd_of_mul_right_dvd
- \+ *theorem* dvd_of_mul_left_dvd
- \+ *theorem* eq_zero_of_zero_dvd
- \+ *theorem* dvd_zero

Modified src/algebra/ring/basic.lean
- \- *lemma* zero_dvd_iff
- \- *theorem* dvd.intro
- \- *theorem* dvd.intro_left
- \- *theorem* exists_eq_mul_right_of_dvd
- \- *theorem* dvd.elim
- \- *theorem* exists_eq_mul_left_of_dvd
- \- *theorem* dvd.elim_left
- \- *theorem* dvd_refl
- \- *theorem* dvd_trans
- \- *theorem* eq_zero_of_zero_dvd
- \- *theorem* dvd_zero
- \- *theorem* one_dvd
- \- *theorem* dvd_mul_right
- \- *theorem* dvd_mul_left
- \- *theorem* dvd_mul_of_dvd_left
- \- *theorem* dvd_mul_of_dvd_right
- \- *theorem* mul_dvd_mul
- \- *theorem* mul_dvd_mul_left
- \- *theorem* mul_dvd_mul_right
- \- *theorem* dvd_of_mul_right_dvd
- \- *theorem* dvd_of_mul_left_dvd

Modified src/data/pnat/basic.lean
- \+/\- *theorem* dvd_iff
- \+/\- *theorem* gcd_dvd_left
- \+/\- *theorem* gcd_dvd_right
- \+/\- *theorem* dvd_lcm_left
- \+/\- *theorem* dvd_lcm_right
- \- *theorem* dvd_iff''
- \- *theorem* dvd_intro
- \- *theorem* dvd_refl
- \- *theorem* one_dvd

Modified src/data/pnat/factors.lean


Modified src/data/pnat/xgcd.lean




## [2020-08-05 19:30:40](https://github.com/leanprover-community/mathlib/commit/13d4fbe)
feat(tactic/interactive_attr): `@[interactive]` attribute to export interactive tactics ([#3698](https://github.com/leanprover-community/mathlib/pull/3698))
Allows one to write 
```lean
@[interactive]
meta def my_tactic := ...
```
instead of
```lean
meta def my_tactic := ...
run_cmd add_interactive [``my_tactic]
```
#### Estimated changes
Modified src/tactic/core.lean




## [2020-08-05 16:34:55](https://github.com/leanprover-community/mathlib/commit/5fc6281)
chore(data/matrix/basic): rename _val lemmas to _apply ([#3297](https://github.com/leanprover-community/mathlib/pull/3297))
We use `_apply` for lemmas about applications of functions to arguments. Arguably "picking out the entries of a matrix" could warrant a different name, but as we treat matrices just as functions all over, I think it's better to use the usual names.
#### Estimated changes
Modified src/algebra/classical_lie_algebras.lean


Modified src/data/matrix/basic.lean
- \+ *lemma* bit0_apply
- \+ *lemma* bit1_apply
- \+ *lemma* bit1_apply_eq
- \+ *lemma* bit1_apply_ne
- \+ *lemma* row_mul_col_apply
- \+ *lemma* smul_apply
- \+ *lemma* transpose_apply
- \+ *lemma* col_apply
- \+ *lemma* row_apply
- \+ *lemma* update_row_apply
- \+ *lemma* update_column_apply
- \- *lemma* bit0_val
- \- *lemma* bit1_val
- \- *lemma* bit1_val_eq
- \- *lemma* bit1_val_ne
- \- *lemma* row_mul_col_val
- \- *lemma* smul_val
- \- *lemma* transpose_val
- \- *lemma* col_val
- \- *lemma* row_val
- \- *lemma* update_row_val
- \- *lemma* update_column_val
- \+ *theorem* zero_apply
- \+ *theorem* neg_apply
- \+ *theorem* add_apply
- \+ *theorem* diagonal_apply_eq
- \+ *theorem* diagonal_apply_ne
- \+ *theorem* diagonal_apply_ne'
- \+ *theorem* one_apply
- \+ *theorem* one_apply_eq
- \+ *theorem* one_apply_ne
- \+ *theorem* one_apply_ne'
- \+ *theorem* mul_apply
- \+ *theorem* mul_apply'
- \- *theorem* zero_val
- \- *theorem* neg_val
- \- *theorem* add_val
- \- *theorem* diagonal_val_eq
- \- *theorem* diagonal_val_ne
- \- *theorem* diagonal_val_ne'
- \- *theorem* one_val
- \- *theorem* one_val_eq
- \- *theorem* one_val_ne
- \- *theorem* one_val_ne'
- \- *theorem* mul_val
- \- *theorem* mul_val'

Modified src/data/matrix/pequiv.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/matrix.lean


Modified src/linear_algebra/nonsingular_inverse.lean
- \+ *lemma* adjugate_apply
- \+ *lemma* mul_adjugate_apply
- \- *lemma* adjugate_val
- \- *lemma* mul_adjugate_val

Modified src/ring_theory/matrix_algebra.lean
- \+ *lemma* algebra_map_matrix_apply
- \- *lemma* algebra_map_matrix_val

Modified src/ring_theory/polynomial_algebra.lean




## [2020-08-05 15:41:26](https://github.com/leanprover-community/mathlib/commit/d952e8b)
chore(topology/category/Top/opens): module-doc, cleanup, and construct some morphisms ([#3601](https://github.com/leanprover-community/mathlib/pull/3601))
#### Estimated changes
Modified src/category_theory/category/default.lean
- \+ *lemma* le_of_hom
- \+ *def* hom_of_le

Modified src/category_theory/limits/lattice.lean


Modified src/topology/category/Top/opens.lean
- \+ *lemma* to_Top_map
- \+/\- *lemma* map_obj
- \- *lemma* map_id_hom_app
- \- *lemma* map_id_inv_app
- \- *lemma* map_comp_hom_app
- \- *lemma* map_comp_inv_app
- \+ *def* inf_le_left
- \+ *def* inf_le_right
- \+ *def* le_supr



## [2020-08-05 11:37:40](https://github.com/leanprover-community/mathlib/commit/c63dad1)
chore(ring_theory/ideals): Move the definition of ideals out of algebra/module ([#3692](https://github.com/leanprover-community/mathlib/pull/3692))
Neatness was the main motivation - it makes it easier to reason about what would need doing in [#3635](https://github.com/leanprover-community/mathlib/pull/3635).
It also results in somewhere sensible for the docs about ideals. Also adds a very minimal docstring to `ring_theory/ideals.lean`.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \- *lemma* neg_mem_iff
- \- *lemma* add_mem_iff_left
- \- *lemma* add_mem_iff_right
- \- *lemma* mul_mem_left
- \- *lemma* mul_mem_right
- \- *def* ideal

Modified src/ring_theory/ideals.lean
- \+ *lemma* neg_mem_iff
- \+ *lemma* add_mem_iff_left
- \+ *lemma* add_mem_iff_right
- \+ *lemma* mul_mem_left
- \+ *lemma* mul_mem_right
- \+ *def* ideal



## [2020-08-05 11:37:36](https://github.com/leanprover-community/mathlib/commit/4a82e84)
feat(algebra/*/ulift): algebraic instances for ulift ([#3675](https://github.com/leanprover-community/mathlib/pull/3675))
#### Estimated changes
Created src/algebra/group/ulift.lean
- \+ *lemma* one_down
- \+ *lemma* mul_down
- \+ *lemma* inv_down
- \+ *lemma* sub_down
- \+ *def* mul_equiv

Modified src/algebra/module/pi.lean


Created src/algebra/module/ulift.lean
- \+ *lemma* smul_down
- \+ *lemma* smul_down'
- \+ *def* semimodule_equiv

Created src/algebra/ring/ulift.lean
- \+ *def* ring_equiv



## [2020-08-05 10:42:04](https://github.com/leanprover-community/mathlib/commit/2b9ac69)
feat(linear_algebra/affine_space): faces of simplices ([#3691](https://github.com/leanprover-community/mathlib/pull/3691))
Define a `face` of an `affine_space.simplex` with any given nonempty
subset of the vertices, using `finset.mono_of_fin`.
#### Estimated changes
Modified src/linear_algebra/affine_space.lean
- \+ *lemma* face_points
- \+ *lemma* face_eq_mk_of_point
- \+ *def* face



## [2020-08-05 10:42:02](https://github.com/leanprover-community/mathlib/commit/ecb5c5f)
docs(algebra/module): Remove completed TODO ([#3690](https://github.com/leanprover-community/mathlib/pull/3690))
Today, submodule _does_ extend `add_submonoid`, which is I assume what this TODO was about
#### Estimated changes
Modified src/algebra/module/basic.lean




## [2020-08-05 10:42:00](https://github.com/leanprover-community/mathlib/commit/0531cb0)
feat(algebra/classical_lie_algebras): add definitions of missing classical Lie algebras ([#3661](https://github.com/leanprover-community/mathlib/pull/3661))
Copying from the comments I have added at the top of `classical_lie_algebras.lean`:
## Main definitions
  * `lie_algebra.symplectic.sp`
  * `lie_algebra.orthogonal.so`
  * `lie_algebra.orthogonal.so'`
  * `lie_algebra.orthogonal.so_indefinite_equiv`
  * `lie_algebra.orthogonal.type_D`
  * `lie_algebra.orthogonal.type_B`
  * `lie_algebra.orthogonal.type_D_equiv_so'`
  * `lie_algebra.orthogonal.type_B_equiv_so'`
#### Estimated changes
Modified src/algebra/classical_lie_algebras.lean
- \+ *lemma* Pso_inv
- \+ *lemma* is_unit_Pso
- \+ *lemma* indefinite_diagonal_transform
- \+ *lemma* so_indefinite_equiv_apply
- \+ *lemma* S_as_blocks
- \+ *lemma* JD_transform
- \+ *lemma* PD_inv
- \+ *lemma* is_unit_PD
- \+ *lemma* PB_inv
- \+ *lemma* is_unit_PB
- \+ *lemma* JB_transform
- \+ *lemma* indefinite_diagonal_assoc
- \+ *def* J
- \+ *def* sp
- \+ *def* so
- \+ *def* indefinite_diagonal
- \+ *def* so'
- \+ *def* Pso
- \+ *def* JD
- \+ *def* type_D
- \+ *def* PD
- \+ *def* S
- \+ *def* JB
- \+ *def* type_B
- \+ *def* PB

Modified src/algebra/lie_algebra.lean
- \+ *lemma* to_lie_equiv_apply
- \+ *lemma* to_lie_equiv_symm_apply
- \+ *lemma* mem_skew_adjoint_matrices_lie_subalgebra
- \+ *lemma* skew_adjoint_matrices_lie_subalgebra_equiv_transpose_apply
- \+ *lemma* mem_skew_adjoint_matrices_lie_subalgebra_unit_smul
- \+ *def* to_lie_equiv
- \+ *def* skew_adjoint_matrices_lie_subalgebra_equiv_transpose

Modified src/data/matrix/basic.lean
- \+ *lemma* from_blocks_apply₁₁
- \+ *lemma* from_blocks_apply₁₂
- \+ *lemma* from_blocks_apply₂₁
- \+ *lemma* from_blocks_apply₂₂
- \+ *lemma* from_blocks_to_blocks
- \+ *lemma* to_blocks_from_blocks₁₁
- \+ *lemma* to_blocks_from_blocks₁₂
- \+ *lemma* to_blocks_from_blocks₂₁
- \+ *lemma* to_blocks_from_blocks₂₂
- \+ *lemma* from_blocks_transpose
- \+ *lemma* from_blocks_smul
- \+ *lemma* from_blocks_add
- \+ *lemma* from_blocks_multiply
- \+ *lemma* from_blocks_diagonal
- \+ *lemma* from_blocks_one
- \+ *def* from_blocks
- \+ *def* to_blocks₁₁
- \+ *def* to_blocks₁₂
- \+ *def* to_blocks₂₁
- \+ *def* to_blocks₂₂

Modified src/linear_algebra/matrix.lean
- \+ *lemma* reindex_transpose

Modified src/linear_algebra/nonsingular_inverse.lean
- \+ *lemma* is_unit_det_of_left_inverse
- \+ *lemma* is_unit_det_of_right_inverse
- \+ *lemma* nonsing_inv_left_right
- \+ *lemma* nonsing_inv_right_left

Modified src/ring_theory/algebra.lean
- \+ *lemma* to_linear_equiv_apply
- \+ *def* to_linear_equiv



## [2020-08-05 09:56:01](https://github.com/leanprover-community/mathlib/commit/37119b4)
feat(topology): normed spaces are (locally) path connected ([#3689](https://github.com/leanprover-community/mathlib/pull/3689))
#### Estimated changes
Modified src/analysis/convex/topology.lean
- \+ *lemma* convex.is_path_connected

Modified src/topology/algebra/module.lean


Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on.comp_continuous

Modified src/topology/metric_space/basic.lean
- \+ *lemma* nonempty_ball
- \+ *lemma* nonempty_closed_ball

Modified src/topology/path_connected.lean
- \+ *lemma* of_line_mem
- \+ *lemma* joined_in.of_line
- \+ *def* of_line



## [2020-08-05 09:09:06](https://github.com/leanprover-community/mathlib/commit/545186c)
refactor(*): add a notation for `nhds_within` ([#3683](https://github.com/leanprover-community/mathlib/pull/3683))
The definition is still there and can be used too.
#### Estimated changes
Modified src/analysis/ODE/gronwall.lean


Modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* has_deriv_within_at_inter'

Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* has_fderiv_within_at_inter'
- \+/\- *lemma* differentiable_within_at_inter'

Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/calculus/tangent_cone.lean
- \+/\- *lemma* tangent_cone_mono_nhds
- \+/\- *lemma* tangent_cone_congr
- \+/\- *lemma* unique_diff_within_at_congr
- \+/\- *lemma* unique_diff_within_at_inter'
- \+/\- *lemma* unique_diff_within_at.inter'

Modified src/analysis/calculus/times_cont_diff.lean
- \+/\- *lemma* times_cont_diff_within_at_inter'

Modified src/analysis/normed_space/basic.lean


Modified src/analysis/specific_limits.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/local_invariant_properties.lean
- \+/\- *lemma* lift_prop_within_at_inter'

Modified src/geometry/manifold/mfderiv.lean
- \+/\- *lemma* unique_mdiff_within_at.inter'
- \+/\- *lemma* has_mfderiv_within_at_inter'
- \+/\- *lemma* mdifferentiable_within_at_inter'

Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+/\- *lemma* ext_chart_preimage_mem_nhds_within

Modified src/geometry/manifold/times_cont_mdiff.lean
- \+/\- *lemma* times_cont_mdiff_within_at_inter'

Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/order/filter/basic.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/basic.lean


Modified src/topology/continuous_on.lean
- \+/\- *lemma* mem_of_mem_nhds_within
- \+/\- *lemma* mem_nhds_within_insert
- \+/\- *lemma* continuous_within_at_inter'
- \+/\- *theorem* nhds_within_univ
- \+/\- *theorem* self_mem_nhds_within
- \+/\- *theorem* nhds_within_mono
- \+/\- *theorem* nhds_within_restrict''
- \+/\- *theorem* nhds_within_le_of_mem
- \+/\- *theorem* nhds_within_empty
- \+/\- *theorem* mem_nhds_within_subtype

Modified src/topology/dense_embedding.lean


Modified src/topology/local_extr.lean
- \+/\- *lemma* filter.eventually_le.is_local_max_on
- \+/\- *lemma* filter.eventually_eq.is_local_max_on_iff
- \+/\- *lemma* filter.eventually_le.is_local_min_on
- \+/\- *lemma* filter.eventually_eq.is_local_min_on_iff
- \+/\- *lemma* filter.eventually_eq.is_local_extr_on_iff
- \+/\- *def* is_local_min_on
- \+/\- *def* is_local_max_on
- \+/\- *def* is_local_extr_on

Modified src/topology/local_homeomorph.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* mem_nhds_within_iff

Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/complete_separated.lean


Modified src/topology/uniform_space/uniform_convergence.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-08-05 08:29:26](https://github.com/leanprover-community/mathlib/commit/3b26878)
feat(linear_algebra/affine_space): more lemmas ([#3615](https://github.com/leanprover-community/mathlib/pull/3615))
Add further lemmas on affine spaces.  This is the last piece of
preparation needed on the affine space side for my definitions of
`circumcenter` and `circumradius` for a simplex in a Euclidean affine
space.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* eq_vadd_iff_vsub_eq
- \+ *lemma* vsub_set_finite_of_finite

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype
- \+ *lemma* eq_weighted_vsub_subset_iff_eq_weighted_vsub_subtype
- \+ *lemma* eq_affine_combination_subset_iff_eq_affine_combination_subtype
- \+ *lemma* affine_independent_iff_indicator_eq_of_affine_combination_eq
- \+ *lemma* affine_independent_embedding_of_affine_independent
- \+ *lemma* affine_independent_subtype_of_affine_independent
- \+ *lemma* finite_dimensional_vector_span_of_finite
- \+ *lemma* finite_dimensional_direction_affine_span_of_finite
- \+ *lemma* mem_affine_span_singleton
- \+ *lemma* affine_span_coe
- \+ *lemma* exists_mem_inter_of_exists_mem_inter_affine_span_of_affine_independent
- \+ *lemma* affine_span_disjoint_of_disjoint_of_affine_independent
- \+ *lemma* mem_affine_span_iff_mem_of_affine_independent
- \+ *lemma* not_mem_affine_span_diff_of_affine_independent



## [2020-08-04 18:21:00](https://github.com/leanprover-community/mathlib/commit/84b450d)
feat(topology): path connected spaces ([#3627](https://github.com/leanprover-community/mathlib/pull/3627))
From the sphere eversion project.
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* Ioo_def
- \+ *lemma* Ico_def
- \+ *lemma* Iio_def
- \+ *lemma* Icc_def
- \+ *lemma* Iic_def
- \+ *lemma* Ioc_def
- \+ *lemma* Ici_def
- \+ *lemma* Ioi_def

Modified src/geometry/manifold/real_instances.lean


Modified src/order/filter/bases.lean
- \+ *lemma* has_basis.to_has_basis

Created src/topology/path_connected.lean
- \+ *lemma* Icc_zero_one_symm
- \+ *lemma* coe_I_zero
- \+ *lemma* coe_I_one
- \+ *lemma* I_symm_zero
- \+ *lemma* I_symm_one
- \+ *lemma* continuous_I_symm
- \+ *lemma* proj_I_I
- \+ *lemma* surjective_proj_I
- \+ *lemma* range_proj_I
- \+ *lemma* continuous_proj_I
- \+ *lemma* continuous.I_extend
- \+ *lemma* I_extend_extends
- \+ *lemma* I_extend_zero
- \+ *lemma* I_extend_one
- \+ *lemma* I_extend_range
- \+ *lemma* continuous_extend
- \+ *lemma* extend_zero
- \+ *lemma* extend_one
- \+ *lemma* map_coe
- \+ *lemma* cast_coe
- \+ *lemma* joined.refl
- \+ *lemma* joined.symm
- \+ *lemma* joined.trans
- \+ *lemma* joined_in.mem
- \+ *lemma* joined_in.source_mem
- \+ *lemma* joined_in.target_mem
- \+ *lemma* joined_in.some_path_mem
- \+ *lemma* joined_in.joined_subtype
- \+ *lemma* joined_in.joined
- \+ *lemma* joined_in_iff_joined
- \+ *lemma* joined_in_univ
- \+ *lemma* joined_in.mono
- \+ *lemma* joined_in.refl
- \+ *lemma* joined_in.symm
- \+ *lemma* joined_in.trans
- \+ *lemma* mem_path_component_self
- \+ *lemma* path_component.nonempty
- \+ *lemma* mem_path_component_of_mem
- \+ *lemma* path_component_symm
- \+ *lemma* path_component_congr
- \+ *lemma* path_component_subset_component
- \+ *lemma* path_component_in_univ
- \+ *lemma* joined.mem_path_component
- \+ *lemma* is_path_connected_iff_eq
- \+ *lemma* is_path_connected.joined_in
- \+ *lemma* is_path_connected_iff
- \+ *lemma* is_path_connected.image
- \+ *lemma* is_path_connected.mem_path_component
- \+ *lemma* is_path_connected.subset_path_component
- \+ *lemma* is_path_connected.union
- \+ *lemma* is_path_connected.preimage_coe
- \+ *lemma* path_connected_space_iff_zeroth_homotopy
- \+ *lemma* is_path_connected_iff_path_connected_space
- \+ *lemma* path_connected_space_iff_univ
- \+ *lemma* path_connected_space_iff_eq
- \+ *lemma* loc_path_connected_of_bases
- \+ *lemma* path_connected_space_iff_connected_space
- \+ *lemma* path_connected_subset_basis
- \+ *lemma* loc_path_connected_of_is_open
- \+ *lemma* is_open.is_connected_iff_is_path_connected
- \+ *def* I_symm
- \+ *def* proj_I
- \+ *def* I_extend
- \+ *def* refl
- \+ *def* symm
- \+ *def* extend
- \+ *def* trans
- \+ *def* map
- \+ *def* cast
- \+ *def* joined
- \+ *def* joined.some_path
- \+ *def* path_setoid
- \+ *def* zeroth_homotopy
- \+ *def* joined_in
- \+ *def* joined_in.some_path
- \+ *def* path_component
- \+ *def* path_component_in
- \+ *def* is_path_connected
- \+ *def* some_path



## [2020-08-04 16:33:38](https://github.com/leanprover-community/mathlib/commit/f4b2790)
feat(data/list/defs): add monadic versions of list.{find,any,all,bor,band} ([#3679](https://github.com/leanprover-community/mathlib/pull/3679))
Also universe-generalise `mfind` while I'm at it.
#### Estimated changes
Modified src/data/list/defs.lean
- \+/\- *def* mfind
- \+ *def* mbfind'
- \+ *def* mbfind
- \+ *def* many
- \+ *def* mall
- \+ *def* mbor
- \+ *def* mband



## [2020-08-04 13:40:24](https://github.com/leanprover-community/mathlib/commit/3ae6cea)
feat(group_theory/submonoid/operations): transfer galois connection/insertion lemmas ([#3657](https://github.com/leanprover-community/mathlib/pull/3657))
#### Estimated changes
Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* comap_id
- \+ *lemma* map_le_of_le_comap
- \+ *lemma* le_comap_of_map_le
- \+ *lemma* le_comap_map
- \+ *lemma* map_comap_le
- \+ *lemma* monotone_map
- \+ *lemma* monotone_comap
- \+ *lemma* map_comap_map
- \+ *lemma* comap_map_comap
- \+ *lemma* comap_map_eq_of_injective
- \+ *lemma* comap_surjective_of_injective
- \+ *lemma* map_injective_of_injective
- \+ *lemma* comap_inf_map_of_injective
- \+ *lemma* comap_infi_map_of_injective
- \+ *lemma* comap_sup_map_of_injective
- \+ *lemma* comap_supr_map_of_injective
- \+ *lemma* map_le_map_iff_of_injective
- \+ *lemma* map_strict_mono_of_injective
- \+ *lemma* map_comap_eq_of_surjective
- \+ *lemma* map_surjective_of_surjective
- \+ *lemma* comap_injective_of_surjective
- \+ *lemma* map_inf_comap_of_surjective
- \+ *lemma* map_infi_comap_of_surjective
- \+ *lemma* map_sup_comap_of_surjective
- \+ *lemma* map_supr_comap_of_surjective
- \+ *lemma* comap_le_comap_iff_of_surjective
- \+ *lemma* comap_strict_mono_of_surjective
- \+ *def* gci_map_comap
- \+ *def* gi_map_comap



## [2020-08-04 10:47:06](https://github.com/leanprover-community/mathlib/commit/78fe862)
chore(measure_theory/lebesgue_measure): review ([#3686](https://github.com/leanprover-community/mathlib/pull/3686))
* use `ennreal.of_real` instead of `coe ∘ nnreal.of_real`;
* avoid some non-finishing `simp`s;
* simplify proofs of `lebesgue_outer_Ico/Ioc/Ioo`;
* add `instance : locally_finite_measure (volume : measure ℝ)`
  instead of `real.volume_lt_top_of_bounded` and
  `real.volume_lt_top_of_compact`.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+/\- *lemma* to_real_of_real
- \+ *lemma* to_real_of_real'
- \+/\- *lemma* of_real_eq_coe_nnreal
- \+ *lemma* of_real_coe_nnreal
- \+ *lemma* of_real_add_le

Modified src/measure_theory/lebesgue_measure.lean
- \+/\- *lemma* lebesgue_length_mono
- \+/\- *lemma* lebesgue_length_eq_infi_Ioo
- \+/\- *lemma* lebesgue_length_eq_infi_Icc
- \+ *lemma* lebesgue_outer_Ioc
- \+ *lemma* borel_le_lebesgue_measurable
- \+/\- *lemma* real.volume_Ico
- \+/\- *lemma* real.volume_Icc
- \+/\- *lemma* real.volume_Ioo
- \+ *lemma* real.volume_Ioc
- \+/\- *lemma* real.volume_singleton
- \- *lemma* real.volume_lt_top_of_bounded
- \- *lemma* real.volume_lt_top_of_compact

Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean
- \+ *lemma* diff_null



## [2020-08-04 10:47:04](https://github.com/leanprover-community/mathlib/commit/8f02ad2)
feat(geometry/euclidean): orthogonal projection ([#3662](https://github.com/leanprover-community/mathlib/pull/3662))
Define orthogonal projection onto an affine subspace of a Euclidean
affine space, and prove some basic lemmas about it.
#### Estimated changes
Modified src/geometry/euclidean.lean
- \+ *lemma* inter_eq_singleton_orthogonal_projection_fn
- \+ *lemma* is
- \+ *lemma* orthogonal_projection_fn_mem
- \+ *lemma* orthogonal_projection_fn_mem_orthogonal
- \+ *lemma* orthogonal_projection_fn_vsub_mem_direction_orthogonal
- \+ *lemma* orthogonal_projection_fn_eq
- \+ *lemma* inter_eq_singleton_orthogonal_projection
- \+ *lemma* orthogonal_projection_mem
- \+ *lemma* orthogonal_projection_mem_orthogonal
- \+ *lemma* orthogonal_projection_vsub_mem_direction
- \+ *lemma* vsub_orthogonal_projection_mem_direction
- \+ *lemma* orthogonal_projection_eq_self_iff
- \+ *lemma* dist_orthogonal_projection_eq_zero_iff
- \+ *lemma* dist_orthogonal_projection_ne_zero_of_not_mem
- \+ *lemma* orthogonal_projection_vsub_mem_direction_orthogonal
- \+ *lemma* vsub_orthogonal_projection_mem_direction_orthogonal
- \+ *lemma* orthogonal_projection_vadd_eq_self
- \+ *lemma* orthogonal_projection_vadd_smul_vsub_orthogonal_projection
- \+ *lemma* dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
- \+ *lemma* dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd
- \+ *def* orthogonal_projection_fn
- \+ *def* orthogonal_projection



## [2020-08-04 09:49:04](https://github.com/leanprover-community/mathlib/commit/14d206b)
feat(order/filter/interval): define class `filter.is_interval_generated` ([#3663](https://github.com/leanprover-community/mathlib/pull/3663))
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *theorem* exists_finite_iff_finset

Modified src/order/filter/bases.lean
- \+ *lemma* has_basis_infi_principal_finite

Created src/order/filter/interval.lean
- \+ *lemma* has_basis.is_interval_generated
- \+ *lemma* has_ord_connected_basis
- \+ *lemma* is_interval_generated_principal_iff
- \+ *lemma* tendsto_Ixx_same_filter
- \+ *lemma* tendsto.Ixx
- \+ *lemma* tendsto.Icc
- \+ *lemma* tendsto.Ico
- \+ *lemma* tendsto.Ioc
- \+ *lemma* tendsto.Ioo
- \+ *lemma* set.ord_connected.is_interval_generated_inf_principal

Modified src/topology/algebra/ordered.lean




## [2020-08-04 09:49:02](https://github.com/leanprover-community/mathlib/commit/ed377e1)
feat(analysis/convex): a local minimum of a convex function is a global minimum ([#3613](https://github.com/leanprover-community/mathlib/pull/3613))
#### Estimated changes
Created src/analysis/convex/extrema.lean
- \+ *lemma* is_min_on.of_is_local_min_on_of_convex_on_Icc
- \+ *lemma* is_min_on.of_is_local_min_on_of_convex_on
- \+ *lemma* is_min_on.of_is_local_min_of_convex_univ

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* decomp
- \+ *lemma* decomp'

Created src/topology/algebra/affine.lean
- \+ *lemma* continuous_iff
- \+ *lemma* line_map_continuous



## [2020-08-04 09:09:02](https://github.com/leanprover-community/mathlib/commit/b4a6651)
chore(order/filter/at_top_bot): golf three proofs ([#3684](https://github.com/leanprover-community/mathlib/pull/3684))
Also add `is_countably_generated_at_top`.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* is_countably_generated_at_top
- \+ *lemma* at_top_finset_eq_infi
- \+/\- *lemma* monotone.tendsto_at_top_finset



## [2020-08-04 07:11:52](https://github.com/leanprover-community/mathlib/commit/b0de811)
chore(measure_theory/borel_space): DRY by using `order_dual` ([#3685](https://github.com/leanprover-community/mathlib/pull/3685))
#### Estimated changes
Modified src/measure_theory/borel_space.lean




## [2020-08-04 02:05:22](https://github.com/leanprover-community/mathlib/commit/d9a6e47)
feat(measure_theory/group): regular, invariant, and conjugate measures ([#3650](https://github.com/leanprover-community/mathlib/pull/3650))
Define the notion of a regular measure. I did this in Borel space, which required me to add an import measure_space -> borel_space.
Define left invariant and right invariant measures for groups
Define the conjugate measure, and show it is left invariant iff the original is right invariant
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+ *lemma* outer_regular_eq
- \+ *lemma* inner_regular_eq

Created src/measure_theory/group.lean
- \+ *lemma* map_mul_left_eq_self
- \+ *lemma* map_mul_right_eq_self
- \+ *lemma* conj_apply
- \+ *lemma* conj_conj
- \+ *lemma* regular.conj
- \+ *lemma* regular_conj_iff
- \+ *lemma* is_right_invariant_conj'
- \+ *lemma* is_left_invariant_conj'
- \+ *lemma* is_right_invariant_conj
- \+ *lemma* is_left_invariant_conj
- \+ *def* is_left_invariant
- \+ *def* is_right_invariant

Modified src/measure_theory/measure_space.lean
- \+ *lemma* ext_iff



## [2020-08-04 00:36:52](https://github.com/leanprover-community/mathlib/commit/acedda0)
chore(scripts): update nolints.txt ([#3682](https://github.com/leanprover-community/mathlib/pull/3682))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-03 20:53:03](https://github.com/leanprover-community/mathlib/commit/b215e95)
fix(data/set/intervals/basic): fix a typo ([#3680](https://github.com/leanprover-community/mathlib/pull/3680))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* Ioo_subset_Ioo_union_Ico
- \- *lemma* Ioo_subset_Ioo_union_Ici



## [2020-08-03 20:53:01](https://github.com/leanprover-community/mathlib/commit/234011d)
chore(order/filter/lift): prove `has_basis.lift` and `has_basis.lift'` ([#3618](https://github.com/leanprover-community/mathlib/pull/3618))
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* has_basis_principal

Modified src/order/filter/lift.lean
- \+ *lemma* has_basis.mem_lift_iff
- \+ *lemma* has_basis.lift
- \+ *lemma* has_basis.lift'



## [2020-08-03 19:22:21](https://github.com/leanprover-community/mathlib/commit/50d1c48)
feat(order/galois_connection): galois_coinsertions ([#3656](https://github.com/leanprover-community/mathlib/pull/3656))
#### Estimated changes
Modified src/order/basic.lean
- \+/\- *lemma* strict_mono_of_monotone_of_injective
- \+ *lemma* strict_mono_of_le_iff_le

Modified src/order/galois_connection.lean
- \+ *lemma* l_supr_of_ul_eq_self
- \+ *lemma* l_infi_of_ul_eq_self
- \+ *lemma* u_le_u_iff
- \+ *lemma* strict_mono_u
- \+ *lemma* u_l_eq
- \+ *lemma* u_surjective
- \+ *lemma* l_injective
- \+ *lemma* u_inf_l
- \+ *lemma* u_infi_l
- \+ *lemma* u_infi_of_lu_eq_self
- \+ *lemma* u_sup_l
- \+ *lemma* u_supr_l
- \+ *lemma* u_supr_of_lu_eq_self
- \+ *lemma* l_le_l_iff
- \+ *lemma* strict_mono_l
- \- *lemma* l_supr_of_ul
- \- *lemma* l_infi_of_ul
- \+ *def* galois_connection.to_galois_insertion
- \+ *def* galois_coinsertion.dual
- \+ *def* galois_insertion.dual
- \+ *def* galois_coinsertion.of_dual
- \+ *def* galois_insertion.of_dual
- \+ *def* galois_coinsertion.monotone_intro
- \+ *def* galois_connection.to_galois_coinsertion
- \+ *def* galois_connection.lift_order_top
- \+ *def* lift_semilattice_inf
- \+ *def* lift_semilattice_sup
- \+ *def* lift_lattice
- \+ *def* lift_order_bot
- \+ *def* lift_bounded_lattice
- \+ *def* lift_complete_lattice



## [2020-08-03 19:22:19](https://github.com/leanprover-community/mathlib/commit/40c6a29)
feat(measure_theory/content): define outer measure from content ([#3649](https://github.com/leanprover-community/mathlib/pull/3649))
Part of the development for the Haar measure: define an outer measure from a content.
#### Estimated changes
Created src/measure_theory/content.lean
- \+ *lemma* le_inner_content
- \+ *lemma* inner_content_le
- \+ *lemma* inner_content_of_is_compact
- \+ *lemma* inner_content_empty
- \+ *lemma* inner_content_mono
- \+ *lemma* inner_content_exists_compact
- \+ *lemma* inner_content_Sup_nat
- \+ *lemma* inner_content_Union_nat
- \+ *lemma* is_left_invariant_inner_content
- \+ *lemma* inner_content_pos
- \+ *lemma* inner_content_mono'
- \+ *lemma* of_content_opens
- \+ *lemma* le_of_content_compacts
- \+ *lemma* of_content_interior_compacts
- \+ *lemma* of_content_exists_compact
- \+ *lemma* of_content_exists_open
- \+ *lemma* of_content_pos_of_is_open
- \+ *def* inner_content
- \+ *def* of_content



## [2020-08-03 17:57:40](https://github.com/leanprover-community/mathlib/commit/018309f)
chore(linear_algebra/basis): replace explicit arguments for 0 ≠ 1 with nontrivial R ([#3678](https://github.com/leanprover-community/mathlib/pull/3678))
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/linear_algebra/basis.lean
- \+/\- *lemma* linear_independent.ne_zero
- \+/\- *lemma* linear_independent.injective
- \+/\- *lemma* surjective_of_linear_independent_of_span
- \+/\- *lemma* eq_of_linear_independent_of_span_subtype
- \+/\- *lemma* le_of_span_le_span
- \+/\- *lemma* span_le_span_iff
- \+/\- *lemma* is_basis.injective

Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/matrix.lean


Modified src/ring_theory/noetherian.lean




## [2020-08-03 17:57:38](https://github.com/leanprover-community/mathlib/commit/6186c69)
feat(group_theory/subgroup): range_gpowers_hom ([#3677](https://github.com/leanprover-community/mathlib/pull/3677))
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* range_gpowers_hom
- \+ *lemma* range_gmultiples_hom



## [2020-08-03 17:57:36](https://github.com/leanprover-community/mathlib/commit/b8df8aa)
feat(algebra/ring): the codomain of a ring hom is trivial iff ... ([#3676](https://github.com/leanprover-community/mathlib/pull/3676))
In the discussion of [#3488](https://github.com/leanprover-community/mathlib/pull/3488), Johan (currently on vacation, so I'm not pinging him) noted that we were missing the lemma "if `f` is a ring homomorphism, `∀ x, f x = 0` implies that the codomain is trivial". This PR adds a couple of ways to derive from homomorphisms that rings are trivial.
I used `0 = 1` to express that the ring is trivial because that seems to be the one that is used in practice.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* codomain_trivial_iff_map_one_eq_zero
- \+ *lemma* codomain_trivial_iff_range_trivial
- \+ *lemma* codomain_trivial_iff_range_eq_singleton_zero
- \+ *lemma* map_one_ne_zero
- \+ *lemma* domain_nontrivial

Modified src/data/polynomial/eval.lean
- \+ *lemma* map_monic_ne_zero

Modified src/ring_theory/ideal_over.lean
- \+/\- *lemma* comap_lt_comap_of_integral_mem_sdiff



## [2020-08-03 17:57:34](https://github.com/leanprover-community/mathlib/commit/5f9e427)
feat(analysis/normed_space/add_torsor): isometries of normed_add_torsors ([#3666](https://github.com/leanprover-community/mathlib/pull/3666))
Add the lemma that an isometry of `normed_add_torsor`s induces an
isometry of the corresponding `normed_group`s at any base point.
Previously discussed on Zulip, see
<https://leanprover-community.github.io/archive/stream/113488-general/topic/Undergraduate.20math.20list.html[#199450039](https://github.com/leanprover-community/mathlib/pull/199450039)>;
both statement and proof have been revised along the lines indicated
in that discussion.
#### Estimated changes
Modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* isometry_vadd_vsub_of_isometry



## [2020-08-03 17:57:32](https://github.com/leanprover-community/mathlib/commit/aef7ade)
feat(data/set/intervals): a few lemmas needed by FTC-1 ([#3653](https://github.com/leanprover-community/mathlib/pull/3653))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* Ico_diff_Iio
- \+/\- *lemma* Ico_inter_Iio
- \+ *lemma* Ioc_union_Ioc
- \+ *lemma* Ioc_union_Ioc_right
- \+ *lemma* Ioc_union_Ioc_left
- \+ *lemma* Ioc_union_Ioc_symm
- \+ *lemma* Ioc_union_Ioc_union_Ioc_cycle

Modified src/data/set/intervals/disjoint.lean
- \+ *lemma* Ico_disjoint_Ico_same
- \+ *lemma* Ioc_disjoint_Ioc
- \+ *lemma* Ioc_disjoint_Ioc_same



## [2020-08-03 16:25:13](https://github.com/leanprover-community/mathlib/commit/c6381aa)
chore(algebra/group_ring_action): docstring, move monoid.End to algebra/group/hom ([#3671](https://github.com/leanprover-community/mathlib/pull/3671))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* coe_one
- \+ *lemma* coe_mul

Modified src/algebra/group_ring_action.lean
- \- *def* monoid.End
- \- *def* add_monoid.End



## [2020-08-03 14:09:09](https://github.com/leanprover-community/mathlib/commit/b2be1ee)
feat(measure_theory/measure_space): add 3 typeclasses ([#3664](https://github.com/leanprover-community/mathlib/pull/3664))
Define `probability_measure`, `finite_measure`, and `locally_finite_measure`.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean


Modified src/data/real/ennreal.lean
- \+ *lemma* one_lt_top

Modified src/measure_theory/integration.lean
- \+/\- *lemma* lintegral_congr

Modified src/measure_theory/measure_space.lean
- \+ *lemma* le_sum
- \+ *lemma* ae_mono
- \+ *lemma* ae_restrict_iff
- \+ *lemma* measure_diff_of_ae_le
- \+ *lemma* measure_mono_ae
- \+/\- *lemma* measure_congr
- \+ *lemma* restrict_mono_ae
- \+ *lemma* restrict_congr
- \+ *lemma* finite_at_filter_of_finite
- \+ *lemma* measure.finite_at_nhds
- \+ *lemma* filter_mono
- \+ *lemma* inf_of_left
- \+ *lemma* inf_of_right
- \+ *lemma* inf_ae_iff
- \+ *lemma* filter_mono_ae
- \+ *lemma* filter_sup
- \+ *lemma* finite_at_nhds_within
- \+ *lemma* finite_at_principal
- \+ *lemma* finite_measure
- \+ *lemma* metric.bounded.finite_measure
- \- *lemma* measure_diff_of_ae_imp
- \- *lemma* measure_le_of_ae_imp
- \+ *def* measure.finite_at_filter

Modified src/order/filter/basic.lean
- \+ *lemma* eventually_eq_set
- \+ *lemma* eventually_eq.filter_mono
- \- *lemma* eventually_set_ext
- \- *lemma* eventually_eq.mem_iff



## [2020-08-03 11:29:40](https://github.com/leanprover-community/mathlib/commit/3781435)
feat(algebra/category/Group): the category of abelian groups is abelian ([#3621](https://github.com/leanprover-community/mathlib/pull/3621))
#### Estimated changes
Created src/algebra/category/Group/abelian.lean
- \+ *def* normal_mono
- \+ *def* normal_epi

Modified src/algebra/category/Module/abelian.lean
- \+/\- *def* normal_mono
- \+/\- *def* normal_epi

Modified src/category_theory/limits/shapes/equalizers.lean
- \+/\- *def* parallel_pair

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* iso_of_ι
- \+ *def* of_ι_congr
- \+ *def* comp_nat_iso
- \+ *def* iso_of_π
- \+ *def* of_π_congr

Modified src/category_theory/limits/shapes/regular_mono.lean
- \+ *def* equivalence_reflects_normal_mono
- \+ *def* equivalence_reflects_normal_epi

Modified src/category_theory/limits/shapes/zero.lean
- \+/\- *lemma* equivalence_preserves_zero_morphisms
- \+ *lemma* is_equivalence_preserves_zero_morphisms



## [2020-08-03 11:29:38](https://github.com/leanprover-community/mathlib/commit/6079ef9)
feat(analysis/normed_space/real_inner_product): orthogonal projection ([#3563](https://github.com/leanprover-community/mathlib/pull/3563))
`analysis.normed_space.real_inner_product` proves the existence of
orthogonal projections onto complete subspaces, but only in the form
of an existence theorem without a corresponding `def` for the function
that is proved to exist.  Add the corresponding `def` of
`orthogonal_projection` as a `linear_map` and lemmas with the basic
properties, extracted from the existing results with `some` and
`some_spec`.
For convenience in constructing the `linear_map`, some lemmas are
first proved for a version of the orthogonal projection as an
unbundled function, then used in the definition of the bundled
`linear_map` version, then restarted for the bundled version (the two
versions of each lemma being definitionally equal; the bundled version
is considered the main version that should be used in all subsequent
code).
This is preparation for defining the corresponding operation for
Euclidean affine spaces as an `affine_map`.
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean
- \+ *lemma* orthogonal_projection_fn_mem
- \+ *lemma* is
- \+ *lemma* orthogonal_projection_fn_inner_eq_zero
- \+ *lemma* eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
- \+ *lemma* orthogonal_projection_fn_eq
- \+ *lemma* orthogonal_projection_mem
- \+ *lemma* orthogonal_projection_inner_eq_zero
- \+ *lemma* eq_orthogonal_projection_of_mem_of_inner_eq_zero
- \+ *def* orthogonal_projection_fn
- \+ *def* orthogonal_projection



## [2020-08-03 10:04:53](https://github.com/leanprover-community/mathlib/commit/8e0d111)
feat(data/finset/lattice,data/finset/sort): singleton lemmas ([#3668](https://github.com/leanprover-community/mathlib/pull/3668))
Add lemmas about `min'`, `max'` and `mono_of_fin` for a singleton
`finset`.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* min'_singleton
- \+ *lemma* max'_singleton

Modified src/data/finset/sort.lean
- \+ *lemma* mono_of_fin_singleton



## [2020-08-03 10:04:51](https://github.com/leanprover-community/mathlib/commit/61db67d)
chore(measure_theory/integration): define composition of a `simple_func` and a measurable function ([#3667](https://github.com/leanprover-community/mathlib/pull/3667))
#### Estimated changes
Modified src/measure_theory/integration.lean
- \+ *lemma* coe_comp
- \+ *lemma* range_comp_subset_range
- \+ *def* comp



## [2020-08-03 10:04:49](https://github.com/leanprover-community/mathlib/commit/292c921)
doc(category_theory): add library note about 'dsimp, simp' pattern ([#3659](https://github.com/leanprover-community/mathlib/pull/3659))
#### Estimated changes
Modified src/algebra/category/Group/biproducts.lean


Modified src/algebraic_geometry/presheafed_space.lean


Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/category/default.lean


Modified src/category_theory/currying.lean


Modified src/category_theory/graded_object.lean


Modified src/category_theory/limits/creates.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/constructions/over/connected.lean


Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/monad/algebra.lean


Modified src/category_theory/over.lean


Modified src/category_theory/punit.lean


Modified src/category_theory/whiskering.lean


Modified src/data/matrix/basic.lean




## [2020-08-03 09:08:57](https://github.com/leanprover-community/mathlib/commit/3d41e33)
feat(group_theory/submonoid/operations): mrange_eq_map ([#3673](https://github.com/leanprover-community/mathlib/pull/3673))
#### Estimated changes
Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* mrange_eq_map



## [2020-08-03 08:41:40](https://github.com/leanprover-community/mathlib/commit/d3e1f5f)
feat(README): add @Vierkantor to maintainer list ([#3674](https://github.com/leanprover-community/mathlib/pull/3674))
#### Estimated changes
Modified README.md




## [2020-08-03 07:29:19](https://github.com/leanprover-community/mathlib/commit/d6c17c9)
feat(linear_algebra/affine_space): simplex ext lemmas ([#3669](https://github.com/leanprover-community/mathlib/pull/3669))
Add `ext` lemmas for `affine_space.simplex`.
#### Estimated changes
Modified src/linear_algebra/affine_space.lean
- \+ *lemma* ext
- \+ *lemma* ext_iff



## [2020-08-03 05:29:42](https://github.com/leanprover-community/mathlib/commit/60ba478)
feat(algebra/category/Module): the category of R-modules is abelian ([#3606](https://github.com/leanprover-community/mathlib/pull/3606))
#### Estimated changes
Created src/algebra/category/Module/abelian.lean
- \+ *def* normal_mono
- \+ *def* normal_epi

Modified src/algebra/category/Module/basic.lean
- \+ *lemma* ker_eq_bot_of_mono
- \+ *lemma* range_eq_top_of_epi
- \+ *lemma* mono_of_ker_eq_bot
- \+ *lemma* epi_of_range_eq_top
- \+ *def* Module.as_hom
- \+ *def* linear_equiv.to_Module_iso'
- \- *def* kernel_cone
- \- *def* kernel_is_limit

Created src/algebra/category/Module/kernels.lean
- \+ *def* kernel_cone
- \+ *def* kernel_is_limit
- \+ *def* cokernel_cocone
- \+ *def* cokernel_is_colimit
- \+ *def* has_kernels_Module
- \+ *def* has_cokernels_Module

Modified src/linear_algebra/basic.lean
- \+ *lemma* comp_ker_subtype
- \+ *lemma* range_mkq_comp
- \+ *lemma* ker_eq_bot_of_cancel
- \+ *lemma* range_eq_top_of_cancel
- \+ *def* quot_equiv_of_eq



## [2020-08-03 00:42:24](https://github.com/leanprover-community/mathlib/commit/fb883ea)
chore(scripts): update nolints.txt ([#3670](https://github.com/leanprover-community/mathlib/pull/3670))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-02 22:03:03](https://github.com/leanprover-community/mathlib/commit/06df503)
chore(analysis/calculus/times_cont_diff): transpose lemmas ([#3665](https://github.com/leanprover-community/mathlib/pull/3665))
In [#3639](https://github.com/leanprover-community/mathlib/pull/3639) , I accidentally placed the new lemma `times_cont_diff_at_inverse` between `times_cont_diff_at.prod_map'` and `times_cont_diff.prod_map`.  This fixes that.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+/\- *lemma* times_cont_diff.prod_map



## [2020-08-02 16:01:03](https://github.com/leanprover-community/mathlib/commit/4588400)
chore(group_theory/*): refactor quotient groups to use bundled subgroups ([#3321](https://github.com/leanprover-community/mathlib/pull/3321))
#### Estimated changes
Modified src/algebra/category/Group/adjunctions.lean


Modified src/algebra/category/Group/colimits.lean


Modified src/algebra/category/Group/images.lean
- \+/\- *def* image
- \+/\- *def* image.ι
- \+/\- *def* factor_thru_image

Modified src/algebra/group/type_tags.lean
- \+ *def* add_monoid_hom.to_multiplicative'
- \+ *def* monoid_hom.to_additive'

Modified src/algebra/group_action_hom.lean


Modified src/algebra/group_ring_action.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/category_theory/action.lean
- \+/\- *lemma* stabilizer_iso_End_apply
- \+/\- *def* stabilizer_iso_End

Modified src/data/equiv/mul_add.lean


Modified src/deprecated/subgroup.lean


Modified src/deprecated/submonoid.lean


Modified src/field_theory/finite.lean


Modified src/group_theory/abelianization.lean
- \+/\- *lemma* commutator_subset_ker
- \+/\- *lemma* lift.of
- \+ *theorem* hom_ext
- \+/\- *def* commutator
- \+/\- *def* of
- \+/\- *def* lift

Modified src/group_theory/coset.lean
- \+/\- *lemma* right_coset_mem_right_coset
- \+/\- *lemma* eq_class_eq_left_coset
- \+/\- *theorem* normal_of_eq_cosets
- \+/\- *theorem* eq_cosets_of_normal
- \+/\- *theorem* normal_iff_eq_cosets
- \+/\- *def* left_rel
- \+/\- *def* quotient

Modified src/group_theory/free_abelian_group.lean
- \+ *lemma* of_mul_of
- \+ *lemma* of_mul
- \+ *lemma* one_def
- \+ *lemma* of_one
- \+/\- *def* lift
- \+ *def* map

Modified src/group_theory/free_group.lean
- \+/\- *lemma* prod.unique
- \+/\- *theorem* to_group.unique
- \+/\- *theorem* to_group.range_subset
- \+ *theorem* closure_subset
- \+ *def* to_group.to_fun
- \+/\- *def* to_group
- \+ *def* map.to_fun
- \+/\- *def* map
- \+/\- *def* prod

Modified src/group_theory/group_action.lean
- \+ *lemma* inv_smul_eq_iff
- \+ *lemma* eq_inv_smul_iff
- \+ *def* stabilizer_carrier
- \+/\- *def* comp_hom
- \+ *def* stabilizer.submonoid
- \+/\- *def* stabilizer
- \+ *def* stabilizer.subgroup
- \+/\- *def* mul_left_cosets

Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* card_trivial
- \+/\- *lemma* card_eq_card_quotient_mul_card_subgroup
- \+/\- *lemma* card_subgroup_dvd_card
- \+/\- *lemma* card_quotient_dvd_card
- \+/\- *lemma* order_eq_card_gpowers
- \+ *lemma* mem_powers_iff_mem_gpowers
- \+/\- *lemma* powers_eq_gpowers

Modified src/group_theory/presented_group.lean
- \+/\- *lemma* closure_rels_subset_ker
- \+/\- *lemma* to_group_eq_one_of_mem_closure
- \+/\- *theorem* to_group.unique
- \+/\- *def* to_group

Modified src/group_theory/quotient_group.lean
- \+/\- *lemma* lift_mk
- \+/\- *lemma* lift_mk'
- \+ *lemma* range_ker_lift_injective
- \+ *lemma* range_ker_lift_surjective
- \+ *def* mk'
- \+/\- *def* lift
- \+/\- *def* map
- \+/\- *def* ker_lift
- \+ *def* range_ker_lift

Modified src/group_theory/subgroup.lean
- \+/\- *lemma* mem_bot
- \+/\- *lemma* mem_ker
- \+ *lemma* to_range_ker
- \+ *lemma* gpowers_subset
- \+ *lemma* gmultiples_subset
- \+ *def* set_normalizer
- \+ *def* to_range

Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* mem_powers
- \+ *lemma* powers_eq_closure
- \+ *lemma* powers_subset
- \+ *lemma* mem_multiples
- \+ *lemma* multiples_eq_closure
- \+ *lemma* multiples_subset
- \+ *def* powers
- \+ *def* multiples

Modified src/group_theory/sylow.lean
- \+/\- *lemma* quotient_group.card_preimage_mk
- \+/\- *lemma* mem_fixed_points_mul_left_cosets_iff_mem_normalizer
- \+/\- *def* fixed_points_mul_left_cosets_equiv_quotient

Modified src/number_theory/quadratic_reciprocity.lean


Modified src/ring_theory/free_comm_ring.lean
- \+/\- *lemma* lift_comp_of
- \+ *lemma* lift_hom_comp_of
- \+/\- *def* lift
- \+/\- *def* restriction
- \+/\- *def* to_free_comm_ring

Modified src/ring_theory/free_ring.lean
- \+ *def* lift_hom
- \+ *def* map_hom

Modified src/topology/algebra/group.lean
- \+/\- *lemma* quotient_group_saturate

Modified src/topology/algebra/monoid.lean
- \+ *lemma* submonoid.mem_nhds_one
- \- *lemma* is_submonoid.mem_nhds_one



## [2020-08-02 11:46:51](https://github.com/leanprover-community/mathlib/commit/6559832)
feat(order/filter/lift): a few lemmas about `filter.lift' _ powerset` ([#3652](https://github.com/leanprover-community/mathlib/pull/3652))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* powerset_mono
- \+ *theorem* powerset_nonempty

Modified src/order/filter/lift.lean
- \+ *lemma* eventually_lift'_iff
- \+ *lemma* eventually_lift'_powerset
- \+ *lemma* eventually_lift'_powerset'
- \+ *lemma* eventually_lift'_powerset_forall
- \+ *lemma* eventually_lift'_powerset_eventually



## [2020-08-02 11:46:49](https://github.com/leanprover-community/mathlib/commit/fe4da7b)
feat(category_theory/limits): transporting is_limit ([#3598](https://github.com/leanprover-community/mathlib/pull/3598))
Some lemmas about moving `is_limit` terms around over equivalences, or (post|pre)composing.
#### Estimated changes
Modified src/category_theory/limits/limits.lean
- \+ *def* hom_is_iso
- \+ *def* of_right_adjoint
- \+/\- *def* of_cone_equiv
- \+ *def* postcompose_hom_equiv
- \+ *def* postcompose_inv_equiv
- \+ *def* of_left_adjoint
- \+/\- *def* of_cocone_equiv
- \+ *def* precompose_hom_equiv
- \+ *def* precompose_inv_equiv

Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/limits/shapes/constructions/over/products.lean




## [2020-08-02 11:46:47](https://github.com/leanprover-community/mathlib/commit/52c0b42)
feat(category_theory): Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D ([#3576](https://github.com/leanprover-community/mathlib/pull/3576))
When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing as functors from `C` into the monoid objects of `D`.
This is formalised as:
* `Mon_functor_category_equivalence : Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`
The intended application is that as `Ring ≌ Mon_ Ab` (not yet constructed!),
we have `presheaf Ring X ≌ presheaf (Mon_ Ab) X ≌ Mon_ (presheaf Ab X)`,
and we can model a module over a presheaf of rings as a module object in `presheaf Ab X`.
#### Estimated changes
Created src/category_theory/monoidal/internal/functor_category.lean
- \+ *def* functor
- \+ *def* inverse
- \+ *def* unit_iso
- \+ *def* counit_iso
- \+ *def* Mon_functor_category_equivalence

Modified src/category_theory/natural_transformation.lean
- \+ *lemma* congr_app



## [2020-08-02 11:46:45](https://github.com/leanprover-community/mathlib/commit/e99518b)
feat(category_theory): braided and symmetric categories ([#3550](https://github.com/leanprover-community/mathlib/pull/3550))
Just the very basics:
* the definition of braided and symmetric categories
* braided functors, and compositions thereof
* the symmetric monoidal structure coming from products
* upgrading `Type u` to a symmetric monoidal structure
This is prompted by the desire to explore modelling sheaves of modules as the monoidal category of module objects for an internal commutative monoid in sheaves of `Ab`.
#### Estimated changes
Created src/category_theory/monoidal/braided.lean
- \+ *def* id
- \+ *def* comp

Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/monoidal/of_has_finite_products.lean
- \+ *def* symmetric_of_has_finite_products
- \+ *def* symmetric_of_has_finite_coproducts

Modified src/category_theory/monoidal/types.lean




## [2020-08-02 11:46:43](https://github.com/leanprover-community/mathlib/commit/8c1e2da)
feat(linear_algebra/tensor_algebra): Tensor algebras ([#3531](https://github.com/leanprover-community/mathlib/pull/3531))
This PR constructs the tensor algebra of a module over a commutative ring.
The main components are:
1. The construction of the tensor algebra: `tensor_algebra R M` for a module `M` over a commutative ring `R`.
2. The linear map `univ R M` from `M` to `tensor_algebra R M`.
3. Given a linear map `f`from `M`to an `R`-algebra `A`, the lift of `f` to `tensor_algebra R M` is denoted `lift R M f`.
4. A theorem `univ_comp_lift` asserting that the composition of `univ R M` with `lift R M f`is `f`.
5. A theorem `lift_unique` asserting the uniqueness of `lift R M f`with respect to property 4.
#### Estimated changes
Modified src/data/quot.lean
- \+ *lemma* lift₂_mk
- \+ *lemma* lift_on₂_mk
- \+ *lemma* map₂_mk

Created src/linear_algebra/tensor_algebra.lean
- \+ *theorem* ι_comp_lift
- \+ *theorem* lift_unique
- \+ *theorem* lift_comp_ι
- \+ *theorem* hom_ext
- \+ *def* has_coe_module
- \+ *def* has_coe_semiring
- \+ *def* has_mul
- \+ *def* has_add
- \+ *def* has_zero
- \+ *def* has_one
- \+ *def* has_scalar
- \+ *def* lift_fun
- \+ *def* tensor_algebra
- \+ *def* ι
- \+ *def* lift



## [2020-08-02 10:18:28](https://github.com/leanprover-community/mathlib/commit/58f2c36)
feat(dynamics/periodic_pts): definition and basic properties ([#3660](https://github.com/leanprover-community/mathlib/pull/3660))
Also add more lemmas about `inj/surj/bij_on` and `maps_to`.
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* bij_on.inter
- \+ *lemma* bij_on.union
- \+ *theorem* maps_to.union_union
- \+ *theorem* maps_to.union
- \+ *theorem* maps_to.inter
- \+ *theorem* maps_to.inter_inter
- \+ *theorem* surj_on.union
- \+ *theorem* surj_on.union_union
- \+ *theorem* surj_on.inter_inter
- \+ *theorem* surj_on.inter

Modified src/data/set/lattice.lean
- \+ *lemma* maps_to_sUnion
- \+ *lemma* maps_to_Union
- \+ *lemma* maps_to_bUnion
- \+ *lemma* maps_to_Union_Union
- \+ *lemma* maps_to_bUnion_bUnion
- \+ *lemma* maps_to_sInter
- \+ *lemma* maps_to_Inter
- \+ *lemma* maps_to_bInter
- \+ *lemma* maps_to_Inter_Inter
- \+ *lemma* maps_to_bInter_bInter
- \+ *lemma* image_Inter_subset
- \+ *lemma* image_bInter_subset
- \+ *lemma* image_sInter_subset
- \+ *lemma* inj_on.image_Inter_eq
- \+ *lemma* inj_on.image_bInter_eq
- \+ *lemma* inj_on_Union_of_directed
- \+ *lemma* surj_on_sUnion
- \+ *lemma* surj_on_Union
- \+ *lemma* surj_on_Union_Union
- \+ *lemma* surj_on_bUnion
- \+ *lemma* surj_on_bUnion_bUnion
- \+ *lemma* surj_on_Inter
- \+ *lemma* surj_on_Inter_Inter
- \+ *lemma* bij_on_Union
- \+ *lemma* bij_on_Inter
- \+ *lemma* bij_on_Union_of_directed
- \+ *lemma* bij_on_Inter_of_directed

Created src/dynamics/periodic_pts.lean
- \+ *lemma* is_fixed_pt.is_periodic_pt
- \+ *lemma* is_periodic_id
- \+ *lemma* is_periodic_pt_zero
- \+ *lemma* apply_iterate
- \+ *lemma* left_of_add
- \+ *lemma* right_of_add
- \+ *lemma* trans_dvd
- \+ *lemma* eq_of_apply_eq_same
- \+ *lemma* eq_of_apply_eq
- \+ *lemma* mem_pts_of_period
- \+ *lemma* semiconj.maps_to_pts_of_period
- \+ *lemma* bij_on_pts_of_period
- \+ *lemma* directed_pts_of_period_pnat
- \+ *lemma* mk_mem_periodic_pts
- \+ *lemma* mem_periodic_pts
- \+ *lemma* bUnion_pts_of_period
- \+ *lemma* Union_pnat_pts_of_period
- \+ *lemma* bij_on_periodic_pts
- \+ *lemma* semiconj.maps_to_periodic_pts
- \+ *lemma* is_periodic_pt_minimal_period
- \+ *lemma* minimal_period_pos_of_mem_periodic_pts
- \+ *lemma* is_periodic_pt.minimal_period_pos
- \+ *lemma* minimal_period_pos_iff_mem_periodic_pts
- \+ *lemma* is_periodic_pt.minimal_period_le
- \+ *lemma* is_periodic_pt.eq_zero_of_lt_minimal_period
- \+ *lemma* is_periodic_pt.minimal_period_dvd
- \+ *lemma* is_periodic_pt_iff_minimal_period_dvd
- \+ *def* is_periodic_pt
- \+ *def* pts_of_period
- \+ *def* periodic_pts
- \+ *def* minimal_period



## [2020-08-02 08:31:21](https://github.com/leanprover-community/mathlib/commit/78655b6)
feat(data/set/intervals): define `set.ord_connected` ([#3647](https://github.com/leanprover-community/mathlib/pull/3647))
A set `s : set α`, `[preorder α]` is `ord_connected` if for
any `x y ∈ s` we have `[x, y] ⊆ s`. For real numbers this property
is equivalent to each of the properties `convex s`
and `is_preconnected s`. We define it for any `preorder`, prove some
basic properties, and migrate lemmas like `convex_I??` and
`is_preconnected_I??` to this API.
#### Estimated changes
Modified src/analysis/calculus/darboux.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/convex/basic.lean
- \+ *lemma* real.convex_iff_ord_connected
- \+/\- *lemma* convex_Iio
- \+/\- *lemma* convex_Ioi
- \+/\- *lemma* convex_Iic
- \+/\- *lemma* convex_Ici
- \+/\- *lemma* convex_Ioo
- \+/\- *lemma* convex_Ico
- \+/\- *lemma* convex_Ioc
- \+/\- *lemma* convex_Icc
- \+ *lemma* convex_interval
- \- *lemma* convex_real_iff

Modified src/analysis/convex/topology.lean
- \+ *lemma* real.convex_iff_is_preconnected

Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* Icc_diff_left
- \+/\- *lemma* Icc_diff_right
- \+/\- *lemma* Ico_diff_left
- \+/\- *lemma* Ioc_diff_right
- \+/\- *lemma* Icc_diff_both
- \+/\- *lemma* Ici_diff_left
- \+/\- *lemma* Iic_diff_right
- \+/\- *lemma* Ico_diff_Ioo_same
- \+/\- *lemma* Ioc_diff_Ioo_same
- \+/\- *lemma* Icc_diff_Ico_same
- \+/\- *lemma* Icc_diff_Ioc_same
- \+/\- *lemma* Icc_diff_Ioo_same
- \+/\- *lemma* Ici_diff_Ioi_same
- \+/\- *lemma* Iic_diff_Iio_same
- \+/\- *lemma* Ioi_union_left
- \+/\- *lemma* Iio_union_right

Created src/data/set/intervals/ord_connected.lean
- \+ *lemma* ord_connected_iff
- \+ *lemma* ord_connected_of_Ioo
- \+ *lemma* ord_connected.inter
- \+ *lemma* ord_connected.dual
- \+ *lemma* ord_connected_dual
- \+ *lemma* ord_connected_sInter
- \+ *lemma* ord_connected_Inter
- \+ *lemma* ord_connected_bInter
- \+ *lemma* ord_connected_Ici
- \+ *lemma* ord_connected_Iic
- \+ *lemma* ord_connected_Ioi
- \+ *lemma* ord_connected_Iio
- \+ *lemma* ord_connected_Icc
- \+ *lemma* ord_connected_Ico
- \+ *lemma* ord_connected_Ioc
- \+ *lemma* ord_connected_Ioo
- \+ *lemma* ord_connected_empty
- \+ *lemma* ord_connected_univ
- \+ *lemma* ord_connected_interval
- \+ *lemma* ord_connected.interval_subset
- \+ *lemma* ord_connected_iff_interval_subset
- \+ *def* ord_connected

Modified src/topology/algebra/ordered.lean
- \+ *lemma* is_preconnected_interval
- \+ *lemma* is_preconnected_iff_ord_connected
- \+/\- *lemma* is_preconnected_Ici
- \+/\- *lemma* is_preconnected_Iic
- \+/\- *lemma* is_preconnected_Iio
- \+/\- *lemma* is_preconnected_Ioi
- \+/\- *lemma* is_preconnected_Ioo
- \+/\- *lemma* is_preconnected_Ioc
- \+/\- *lemma* is_preconnected_Ico
- \- *lemma* is_preconnected_iff_forall_Icc_subset



## [2020-08-02 08:31:19](https://github.com/leanprover-community/mathlib/commit/f2db6a8)
chore(algebra/order): enable dot syntax ([#3643](https://github.com/leanprover-community/mathlib/pull/3643))
Add dot syntax aliases to some lemmas about order (e.g.,
`has_le.le.trans`). Also remove `lt_of_le_of_ne'` (was equivalent
to `lt_of_le_of_ne`).
#### Estimated changes
Modified src/algebra/order.lean
- \+ *lemma* has_le.le.lt_or_le
- \+ *lemma* has_le.le.le_or_lt
- \- *lemma* lt_of_le_of_ne'

Modified src/analysis/normed_space/real_inner_product.lean




## [2020-08-02 06:44:24](https://github.com/leanprover-community/mathlib/commit/6394e4d)
feat(algebra/category/*): forget reflects isos ([#3600](https://github.com/leanprover-community/mathlib/pull/3600))
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean


Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/Group/adjunctions.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Group/images.lean


Modified src/algebra/category/Mon/basic.lean


Created src/category_theory/concrete_category/reflects_isomorphisms.lean


Modified src/category_theory/limits/cones.lean
- \+ *def* cone_iso_of_hom_iso
- \+ *def* cocone_iso_of_hom_iso

Modified src/category_theory/limits/limits.lean


Modified src/category_theory/monad/algebra.lean


Modified src/category_theory/over.lean


Deleted src/category_theory/reflect_isomorphisms.lean
- \- *def* is_iso_of_reflects_iso
- \- *def* cone_iso_of_hom_iso
- \- *def* cocone_iso_of_hom_iso

Created src/category_theory/reflects_isomorphisms.lean
- \+ *def* is_iso_of_reflects_iso

Modified src/topology/category/TopCommRing.lean


Modified src/topology/sheaves/presheaf_of_functions.lean




## [2020-08-02 04:10:31](https://github.com/leanprover-community/mathlib/commit/d76c75e)
feat(measure_theory): cleanup and generalize measure' ([#3648](https://github.com/leanprover-community/mathlib/pull/3648))
There were two functions `measure'` and `outer_measure'` with undescriptive names, and which were not very general
rename `measure'` -> `extend`
rename `outer_measure'` -> `induced_outer_measure`
generalize both `extend` and `induced_outer_measure` to an arbitrary subset of `set α` (instead of just the measurable sets). Most lemmas still hold in full generality, sometimes with a couple more assumptions. For the lemmas that need more assumptions, we have also kept the version that is just for `is_measurable`.
Move functions `extend`, `induced_outer_measure` and `trim` to `outer_measure.lean`.
rename `caratheodory_is_measurable` -> `of_function_caratheodory`
rename `trim_ge` -> `le_trim`
Make the section on caratheodory sets not private (and give a more descriptive name to lemmas).
Style in `measurable_space` and `outer_measure`
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* image_symm_preimage

Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* is_measurable.Union
- \+/\- *lemma* ext
- \+/\- *def* measurable

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_eq_induced_outer_measure
- \+ *lemma* to_outer_measure_eq_induced_outer_measure
- \+ *lemma* measure_eq_extend
- \- *lemma* measure'_eq
- \- *lemma* measure'_empty
- \- *lemma* measure'_Union_nat
- \- *lemma* measure'_Union_le_tsum_nat'
- \- *lemma* measure'_Union
- \- *lemma* measure'_union
- \- *lemma* measure'_mono
- \- *lemma* measure'_Union_le_tsum_nat
- \- *lemma* outer_measure'_eq
- \- *lemma* outer_measure'_eq_measure'
- \- *lemma* exists_is_measurable_superset_of_trim_eq_zero
- \- *lemma* measure_eq_outer_measure'
- \- *lemma* to_outer_measure_eq_outer_measure'
- \- *lemma* measure_eq_measure'
- \- *theorem* trim_ge
- \- *theorem* trim_eq
- \- *theorem* trim_congr
- \- *theorem* trim_le_trim
- \- *theorem* le_trim_iff
- \- *theorem* trim_eq_infi
- \- *theorem* trim_eq_infi'
- \- *theorem* trim_trim
- \- *theorem* trim_zero
- \- *theorem* trim_add
- \- *theorem* trim_sum_ge
- \- *theorem* trim_smul
- \- *def* measure'
- \- *def* outer_measure'
- \- *def* trim

Modified src/measure_theory/outer_measure.lean
- \+ *lemma* is_caratheodory_iff_le'
- \+ *lemma* is_caratheodory_empty
- \+ *lemma* is_caratheodory_compl
- \+ *lemma* is_caratheodory_compl_iff
- \+ *lemma* is_caratheodory_union
- \+ *lemma* measure_inter_union
- \+ *lemma* is_caratheodory_Union_lt
- \+ *lemma* is_caratheodory_inter
- \+ *lemma* is_caratheodory_sum
- \+ *lemma* is_caratheodory_Union_nat
- \+ *lemma* f_Union
- \+ *lemma* is_caratheodory_iff
- \+ *lemma* is_caratheodory_iff_le
- \+ *lemma* of_function_caratheodory
- \+ *lemma* extend_eq
- \+ *lemma* le_extend
- \+ *lemma* extend_empty
- \+ *lemma* extend_Union_nat
- \+ *lemma* extend_Union_le_tsum_nat'
- \+ *lemma* extend_mono'
- \+ *lemma* extend_Union
- \+ *lemma* extend_union
- \+ *lemma* induced_outer_measure_eq_extend'
- \+ *lemma* induced_outer_measure_eq'
- \+ *lemma* induced_outer_measure_eq_infi
- \+ *lemma* induced_outer_measure_exists_set
- \+ *lemma* induced_outer_measure_caratheodory
- \+ *lemma* extend_mono
- \+ *lemma* extend_Union_le_tsum_nat
- \+ *lemma* induced_outer_measure_eq_extend
- \+ *lemma* induced_outer_measure_eq
- \+ *lemma* exists_is_measurable_superset_of_trim_eq_zero
- \- *lemma* is_caratheodory
- \- *lemma* is_caratheodory_le
- \- *lemma* caratheodory_is_measurable
- \+/\- *theorem* of_function_le
- \+ *theorem* of_function_eq
- \+/\- *theorem* le_of_function
- \+ *theorem* le_trim
- \+ *theorem* trim_eq
- \+ *theorem* trim_congr
- \+ *theorem* trim_le_trim
- \+ *theorem* le_trim_iff
- \+ *theorem* trim_eq_infi
- \+ *theorem* trim_eq_infi'
- \+ *theorem* trim_trim
- \+ *theorem* trim_zero
- \+ *theorem* trim_add
- \+ *theorem* trim_sum_ge
- \+ *theorem* trim_smul
- \+ *def* is_caratheodory
- \+ *def* caratheodory_dynkin
- \+ *def* extend
- \+ *def* induced_outer_measure
- \+ *def* trim



## [2020-08-02 03:20:12](https://github.com/leanprover-community/mathlib/commit/fc65ba0)
feat(analysis/calculus/times_cont_diff): inversion is smooth ([#3639](https://github.com/leanprover-community/mathlib/pull/3639))
At an invertible element of a complete normed algebra, the inversion operation is smooth.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_at.comp
- \+ *lemma* times_cont_diff.comp_times_cont_diff_at
- \+ *lemma* times_cont_diff_at_inverse
- \+ *theorem* times_cont_diff_at_succ_iff_has_fderiv_at

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* continuous_linear_map.lmul_left_right_is_bounded_bilinear

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* lmul_left_apply
- \+/\- *lemma* lmul_right_apply
- \+ *lemma* lmul_left_right_apply
- \+ *lemma* lmul_left_norm
- \+ *lemma* lmul_right_norm
- \+ *lemma* lmul_left_right_norm_le
- \+/\- *def* lmul_left
- \+/\- *def* lmul_right
- \+ *def* lmul_left_right

Modified src/analysis/normed_space/units.lean
- \+ *lemma* nhds

Modified src/ring_theory/algebra.lean
- \+ *lemma* lmul_left_right_apply
- \+ *def* lmul_left_right



## [2020-08-02 02:10:22](https://github.com/leanprover-community/mathlib/commit/d3de289)
feat(topology/local_homeomorph): open_embedding.continuous_at_iff ([#3599](https://github.com/leanprover-community/mathlib/pull/3599))
```
lemma continuous_at_iff
  {f : α → β} {g : β → γ} (hf : open_embedding f) {x : α} :
  continuous_at (g ∘ f) x ↔ continuous_at g (f x) :=
```
#### Estimated changes
Modified src/topology/local_homeomorph.lean
- \+ *lemma* continuous_at_iff



## [2020-08-01 21:07:07](https://github.com/leanprover-community/mathlib/commit/4274ddd)
chore(*): bump to Lean 3.18.4 ([#3610](https://github.com/leanprover-community/mathlib/pull/3610))
* Remove `pi_arity` and the `vm_override` for `by_cases`, which have moved to core
* Fix fallout from the change to the definition of `max`
* Fix a small number of errors caused by changes to instance caching
* Remove `min_add`, which is generalized by `min_add_add_right`  and make `to_additive` generate some lemmas
#### Estimated changes
Modified leanpkg.toml


Modified src/algebra/order_functions.lean
- \- *lemma* min_add
- \- *lemma* fn_min_add_fn_max
- \- *lemma* min_add_max

Modified src/algebra/ordered_group.lean


Modified src/computability/primrec.lean
- \+/\- *theorem* nat_max

Modified src/control/traversable/equiv.lean


Modified src/data/int/cast.lean


Modified src/data/list/min_max.lean


Modified src/data/polynomial/monic.lean


Modified src/data/rat/cast.lean


Modified src/measure_theory/borel_space.lean


Modified src/meta/expr.lean


Modified src/order/filter/filter_product.lean


Modified src/ring_theory/algebra_tower.lean


Modified src/set_theory/ordinal.lean


Modified src/tactic/core.lean


Deleted src/tactic/fix_by_cases.lean


Modified src/tactic/interval_cases.lean


Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* continuous.max



## [2020-08-01 15:55:33](https://github.com/leanprover-community/mathlib/commit/92a20e6)
feat(order/filter/extr, topology/local_extr): links between extremas of two eventually le/eq functions ([#3624](https://github.com/leanprover-community/mathlib/pull/3624))
Add many lemmas that look similar to e.g : if f and g are equal at `a`, and `f ≤ᶠ[l] g` for some filter `l`, then `is_min_filter l f a`implies `is_min_filter l g a`
#### Estimated changes
Modified src/order/filter/extr.lean
- \+ *lemma* filter.eventually_le.is_max_filter
- \+ *lemma* is_max_filter.congr
- \+ *lemma* filter.eventually_eq.is_max_filter_iff
- \+ *lemma* filter.eventually_le.is_min_filter
- \+ *lemma* is_min_filter.congr
- \+ *lemma* filter.eventually_eq.is_min_filter_iff
- \+ *lemma* is_extr_filter.congr
- \+ *lemma* filter.eventually_eq.is_extr_filter_iff

Modified src/topology/continuous_on.lean
- \+ *lemma* filter.eventually_eq.eq_of_nhds_within

Modified src/topology/local_extr.lean
- \+ *lemma* filter.eventually_le.is_local_max_on
- \+ *lemma* is_local_max_on.congr
- \+ *lemma* filter.eventually_eq.is_local_max_on_iff
- \+ *lemma* filter.eventually_le.is_local_min_on
- \+ *lemma* is_local_min_on.congr
- \+ *lemma* filter.eventually_eq.is_local_min_on_iff
- \+ *lemma* is_local_extr_on.congr
- \+ *lemma* filter.eventually_eq.is_local_extr_on_iff
- \+ *lemma* filter.eventually_le.is_local_max
- \+ *lemma* is_local_max.congr
- \+ *lemma* filter.eventually_eq.is_local_max_iff
- \+ *lemma* filter.eventually_le.is_local_min
- \+ *lemma* is_local_min.congr
- \+ *lemma* filter.eventually_eq.is_local_min_iff
- \+ *lemma* is_local_extr.congr
- \+ *lemma* filter.eventually_eq.is_local_extr_iff



## [2020-08-01 12:08:21](https://github.com/leanprover-community/mathlib/commit/aa67315)
chore(order/filter/bases): generalize `has_basis.restrict` ([#3645](https://github.com/leanprover-community/mathlib/pull/3645))
The old lemma is renamed to `filter.has_basis.restrict_subset`
#### Estimated changes
Modified src/order/filter/bases.lean
- \+/\- *lemma* has_basis.restrict
- \+ *lemma* has_basis.restrict_subset



## [2020-08-01 09:06:29](https://github.com/leanprover-community/mathlib/commit/c6f3399)
feat(topology/subset_properties): add `is_compact.induction_on` ([#3642](https://github.com/leanprover-community/mathlib/pull/3642))
#### Estimated changes
Modified src/topology/subset_properties.lean
- \+ *lemma* is_compact.induction_on

