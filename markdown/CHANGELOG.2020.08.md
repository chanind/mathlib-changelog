## [2020-08-31 22:41:43](https://github.com/leanprover-community/mathlib/commit/036527a)
feat(linear_algebra/finite_dimensional): eq_of_le_of_findim_eq ([#4005](https://github.com/leanprover-community/mathlib/pull/4005))
Add a variant of `eq_top_of_findim_eq`, where instead of proving a
submodule equal to `⊤`, it's shown equal to another finite-dimensional
submodule with the same dimension that contains it.  The two lemmas
are related by the `comap_subtype` lemmas, so the proof is short, but
it still seems useful to have this form.
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.eq_of_le_of_findim_eq



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
- \+ *lemma* real.exists_cos_eq
- \+ *lemma* real.range_cos
- \+ *lemma* real.range_sin



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
- \+ *structure* is_field
- \+ *lemma* uniq_inv_of_is_field

Modified src/ring_theory/ideal/basic.lean
- \+ *theorem* ideal.quotient.maximal_ideal_iff_is_field_quotient
- \+ *theorem* ideal.quotient.maximal_of_is_field



## [2020-08-31 14:45:05](https://github.com/leanprover-community/mathlib/commit/8089f50)
chore(category_theory/limits): some simp lemmas ([#3993](https://github.com/leanprover-community/mathlib/pull/3993))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* category_theory.limits.binary_cofan.ι_app_left
- \+ *lemma* category_theory.limits.binary_cofan.ι_app_right
- \+ *lemma* category_theory.limits.binary_fan.π_app_left
- \+ *lemma* category_theory.limits.binary_fan.π_app_right



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
- \+ *lemma* fin.mk_eq_subtype_mk



## [2020-08-31 08:47:27](https://github.com/leanprover-community/mathlib/commit/10ebb71)
feat(measure_theory): induction principles in measure theory ([#3978](https://github.com/leanprover-community/mathlib/pull/3978))
This commit adds three induction principles for measure theory
* To prove something for arbitrary simple functions
* To prove something for arbitrary measurable functions into `ennreal`
* To prove something for arbitrary measurable + integrable functions.
This also adds some basic lemmas to various files. Not all of them are used in this PR, some will be used by near-future PRs.
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+ *lemma* pi.comp_one
- \+ *lemma* pi.const_one
- \+ *lemma* pi.one_comp

Modified src/data/indicator_function.lean
- \+ *lemma* set.comp_indicator
- \+ *lemma* set.indicator_add_eq_left
- \+ *lemma* set.indicator_add_eq_right
- \+/\- *lemma* set.indicator_comp_of_zero
- \+ *lemma* set.indicator_zero'
- \+ *lemma* set.piecewise_eq_indicator

Modified src/data/list/indexes.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.div_pos_iff
- \+/\- *lemma* ennreal.div_zero_iff
- \+ *lemma* ennreal.lt_top_of_mul_lt_top_left
- \+ *lemma* ennreal.lt_top_of_mul_lt_top_right
- \+/\- *lemma* ennreal.mul_eq_top
- \+/\- *lemma* ennreal.mul_lt_top
- \+/\- *lemma* ennreal.mul_ne_top
- \+/\- *lemma* ennreal.mul_pos
- \+ *lemma* ennreal.ne_top_of_mul_ne_top_left
- \+ *lemma* ennreal.ne_top_of_mul_ne_top_right
- \+ *lemma* ennreal.not_lt_top
- \+/\- *lemma* ennreal.to_real_eq_to_real
- \+/\- *lemma* ennreal.to_real_mul_to_real

Modified src/data/set/basic.lean
- \+ *lemma* eq.subset
- \+ *lemma* set.diff_diff_comm
- \+/\- *lemma* set.image_compl_preimage
- \+ *lemma* set.image_diff_preimage
- \+ *lemma* set.image_preimage_eq_iff
- \+ *lemma* set.range_subset_singleton

Modified src/data/set/function.lean
- \+ *lemma* set.comp_piecewise
- \+ *lemma* set.piecewise_same
- \+ *lemma* set.range_piecewise

Modified src/logic/function/basic.lean
- \+ *lemma* function.comp_const
- \+ *lemma* function.const_apply
- \+ *lemma* function.const_comp
- \+/\- *lemma* function.injective.of_comp
- \+/\- *theorem* function.left_inverse.comp
- \+/\- *theorem* function.right_inverse.comp
- \+/\- *lemma* function.surjective.of_comp

Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/integration.lean
- \+ *theorem* measurable.ennreal_induction

Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/set_integral.lean
- \+ *lemma* measure_theory.integrable.induction
- \+ *lemma* measure_theory.integrable_add



## [2020-08-31 08:11:24](https://github.com/leanprover-community/mathlib/commit/bf7487b)
fix(algebraic_geometry/Spec): inline TeX in heading ([#3992](https://github.com/leanprover-community/mathlib/pull/3992))
#### Estimated changes
Modified src/algebraic_geometry/Spec.lean




## [2020-08-31 05:09:37](https://github.com/leanprover-community/mathlib/commit/b79fc03)
feature(algebraic_geometry/Scheme): the category of schemes ([#3961](https://github.com/leanprover-community/mathlib/pull/3961))
The definition of a `Scheme`, and the category of schemes as the full subcategory of locally ringed spaces.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* ring_hom.is_unit_map

Added src/algebraic_geometry/Scheme.lean
- \+ *def* algebraic_geometry.Scheme.empty
- \+ *def* algebraic_geometry.Scheme.to_LocallyRingedSpace
- \+ *structure* algebraic_geometry.Scheme

Added src/algebraic_geometry/Spec.lean
- \+ *def* algebraic_geometry.Spec.PresheafedSpace
- \+ *def* algebraic_geometry.Spec.SheafedSpace

Added src/algebraic_geometry/locally_ringed_space.lean
- \+ *def* algebraic_geometry.LocallyRingedSpace.comp
- \+ *def* algebraic_geometry.LocallyRingedSpace.forget_to_SheafedSpace
- \+ *def* algebraic_geometry.LocallyRingedSpace.hom
- \+ *lemma* algebraic_geometry.LocallyRingedSpace.hom_ext
- \+ *def* algebraic_geometry.LocallyRingedSpace.id
- \+ *def* algebraic_geometry.LocallyRingedSpace.stalk
- \+ *def* algebraic_geometry.LocallyRingedSpace.stalk_map
- \+ *def* algebraic_geometry.LocallyRingedSpace.to_Top
- \+ *def* algebraic_geometry.LocallyRingedSpace.𝒪
- \+ *structure* algebraic_geometry.LocallyRingedSpace

Modified src/algebraic_geometry/presheafed_space.lean
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.as_coe
- \+ *def* algebraic_geometry.PresheafedSpace.const
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.mk_coe
- \+ *def* algebraic_geometry.PresheafedSpace.restrict
- \+ *lemma* category_theory.functor.map_presheaf_obj_presheaf
- \- *lemma* category_theory.functor.map_presheaf_obj_𝒪

Modified src/algebraic_geometry/prime_spectrum.lean
- \+ *def* prime_spectrum.basic_open
- \+ *lemma* prime_spectrum.basic_open_open
- \+ *lemma* prime_spectrum.punit

Added src/algebraic_geometry/sheafed_space.lean
- \+ *lemma* algebraic_geometry.SheafedSpace.as_coe
- \+ *lemma* algebraic_geometry.SheafedSpace.comp_base
- \+ *lemma* algebraic_geometry.SheafedSpace.comp_c_app
- \+ *def* algebraic_geometry.SheafedSpace.forget
- \+ *def* algebraic_geometry.SheafedSpace.forget_to_PresheafedSpace
- \+ *lemma* algebraic_geometry.SheafedSpace.id_base
- \+ *lemma* algebraic_geometry.SheafedSpace.id_c
- \+ *lemma* algebraic_geometry.SheafedSpace.id_c_app
- \+ *lemma* algebraic_geometry.SheafedSpace.mk_coe
- \+ *def* algebraic_geometry.SheafedSpace.punit
- \+ *def* algebraic_geometry.SheafedSpace.restrict
- \+ *def* algebraic_geometry.SheafedSpace.sheaf
- \+ *structure* algebraic_geometry.SheafedSpace

Modified src/algebraic_geometry/stalks.lean
- \+/\- *def* algebraic_geometry.PresheafedSpace.stalk

Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *def* algebraic_geometry.stalk_iso
- \+ *def* algebraic_geometry.stalk_iso_Type
- \+ *def* algebraic_geometry.stalk_to_fiber_ring_hom
- \+ *lemma* algebraic_geometry.structure_sheaf_stalk_to_fiber_injective
- \+ *lemma* algebraic_geometry.structure_sheaf_stalk_to_fiber_surjective

Modified src/category_theory/limits/types.lean
- \+ *lemma* category_theory.limits.types.jointly_surjective'

Modified src/data/equiv/transfer_instance.lean


Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* is_unit_map_iff
- \+ *lemma* local_of_surjective

Modified src/ring_theory/localization.lean


Modified src/topology/category/Top/opens.lean
- \+ *def* is_open_map.functor
- \+ *def* topological_space.opens.inclusion
- \+ *lemma* topological_space.opens.inclusion_open_embedding

Modified src/topology/opens.lean
- \+ *lemma* topological_space.opens.coe_inf
- \+ *lemma* topological_space.opens.le_def
- \+ *lemma* topological_space.opens.mk_inf_mk
- \+ *lemma* topological_space.opens.supr_mk

Modified src/topology/sheaves/local_predicate.lean
- \+ *lemma* Top.prelocal_predicate.sheafify_of

Modified src/topology/sheaves/sheaf.lean
- \+ *def* Top.sheaf_condition.cover.of_open_embedding
- \+ *def* Top.sheaf_condition.diagram.iso_of_open_embedding
- \+ *def* Top.sheaf_condition.fork.iso_of_open_embedding
- \+ *def* Top.sheaf_condition.pi_inters.iso_of_open_embedding
- \+ *def* Top.sheaf_condition.pi_opens.iso_of_open_embedding

Modified src/topology/sheaves/stalks.lean
- \+ *lemma* Top.presheaf.germ_exist



## [2020-08-30 23:20:13](https://github.com/leanprover-community/mathlib/commit/e88843c)
feat(data/finset/sort): range_mono_of_fin ([#3987](https://github.com/leanprover-community/mathlib/pull/3987))
Add a `simp` lemma giving the range of `mono_of_fin`.
#### Estimated changes
Modified src/data/finset/sort.lean
- \+ *lemma* finset.range_mono_of_fin



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
Added src/data/complex/is_R_or_C.lean
- \+ *lemma* is_R_or_C.I_im
- \+ *lemma* is_R_or_C.I_mul_I
- \+ *lemma* is_R_or_C.I_mul_I_of_nonzero
- \+ *lemma* is_R_or_C.I_re
- \+ *lemma* is_R_or_C.I_to_complex
- \+ *lemma* is_R_or_C.I_to_real
- \+ *lemma* is_R_or_C.abs_abs
- \+ *lemma* is_R_or_C.abs_abs_sub_le_abs_sub
- \+ *lemma* is_R_or_C.abs_add
- \+ *lemma* is_R_or_C.abs_cast_nat
- \+ *lemma* is_R_or_C.abs_conj
- \+ *theorem* is_R_or_C.abs_div
- \+ *lemma* is_R_or_C.abs_eq_zero
- \+ *lemma* is_R_or_C.abs_im_div_abs_le_one
- \+ *lemma* is_R_or_C.abs_im_le_abs
- \+ *theorem* is_R_or_C.abs_inv
- \+ *lemma* is_R_or_C.abs_mul
- \+ *lemma* is_R_or_C.abs_ne_zero
- \+ *lemma* is_R_or_C.abs_neg
- \+ *lemma* is_R_or_C.abs_nonneg
- \+ *lemma* is_R_or_C.abs_of_nat
- \+ *lemma* is_R_or_C.abs_of_nonneg
- \+ *lemma* is_R_or_C.abs_of_real
- \+ *lemma* is_R_or_C.abs_one
- \+ *lemma* is_R_or_C.abs_pos
- \+ *lemma* is_R_or_C.abs_re_div_abs_le_one
- \+ *lemma* is_R_or_C.abs_re_le_abs
- \+ *lemma* is_R_or_C.abs_sub
- \+ *lemma* is_R_or_C.abs_sub_le
- \+ *lemma* is_R_or_C.abs_to_complex
- \+ *lemma* is_R_or_C.abs_to_real
- \+ *lemma* is_R_or_C.abs_two
- \+ *lemma* is_R_or_C.abs_zero
- \+ *theorem* is_R_or_C.add_conj
- \+ *lemma* is_R_or_C.bit0_im
- \+ *lemma* is_R_or_C.bit0_re
- \+ *lemma* is_R_or_C.bit1_im
- \+ *lemma* is_R_or_C.bit1_re
- \+ *lemma* is_R_or_C.char_zero_R_or_C
- \+ *lemma* is_R_or_C.conj_bijective
- \+ *lemma* is_R_or_C.conj_bit0
- \+ *lemma* is_R_or_C.conj_bit1
- \+ *lemma* is_R_or_C.conj_conj
- \+ *lemma* is_R_or_C.conj_eq_zero
- \+ *lemma* is_R_or_C.conj_im
- \+ *lemma* is_R_or_C.conj_inj
- \+ *lemma* is_R_or_C.conj_involutive
- \+ *lemma* is_R_or_C.conj_neg_I
- \+ *lemma* is_R_or_C.conj_of_real
- \+ *lemma* is_R_or_C.conj_re
- \+ *lemma* is_R_or_C.conj_to_complex
- \+ *lemma* is_R_or_C.conj_to_real
- \+ *lemma* is_R_or_C.div_I
- \+ *lemma* is_R_or_C.div_im
- \+ *lemma* is_R_or_C.div_re
- \+ *lemma* is_R_or_C.eq_conj_iff_re
- \+ *lemma* is_R_or_C.eq_conj_iff_real
- \+ *theorem* is_R_or_C.ext
- \+ *theorem* is_R_or_C.ext_iff
- \+ *lemma* is_R_or_C.im_le_abs
- \+ *lemma* is_R_or_C.im_sq_le_norm_sq
- \+ *lemma* is_R_or_C.im_to_complex
- \+ *lemma* is_R_or_C.im_to_real
- \+ *lemma* is_R_or_C.int_cast_im
- \+ *lemma* is_R_or_C.int_cast_re
- \+ *lemma* is_R_or_C.inv_I
- \+ *lemma* is_R_or_C.inv_def
- \+ *lemma* is_R_or_C.inv_im
- \+ *lemma* is_R_or_C.inv_re
- \+ *lemma* is_R_or_C.is_cau_seq_abs
- \+ *theorem* is_R_or_C.is_cau_seq_im
- \+ *theorem* is_R_or_C.is_cau_seq_re
- \+ *theorem* is_R_or_C.mul_conj
- \+ *lemma* is_R_or_C.mul_im
- \+ *lemma* is_R_or_C.mul_re
- \+ *lemma* is_R_or_C.mul_self_abs
- \+ *lemma* is_R_or_C.nat_cast_im
- \+ *lemma* is_R_or_C.nat_cast_re
- \+ *def* is_R_or_C.norm_sq
- \+ *lemma* is_R_or_C.norm_sq_add
- \+ *lemma* is_R_or_C.norm_sq_conj
- \+ *lemma* is_R_or_C.norm_sq_div
- \+ *lemma* is_R_or_C.norm_sq_eq_abs
- \+ *lemma* is_R_or_C.norm_sq_eq_def'
- \+ *lemma* is_R_or_C.norm_sq_eq_def
- \+ *lemma* is_R_or_C.norm_sq_eq_zero
- \+ *lemma* is_R_or_C.norm_sq_inv
- \+ *lemma* is_R_or_C.norm_sq_mul
- \+ *lemma* is_R_or_C.norm_sq_neg
- \+ *lemma* is_R_or_C.norm_sq_nonneg
- \+ *lemma* is_R_or_C.norm_sq_of_real
- \+ *lemma* is_R_or_C.norm_sq_one
- \+ *lemma* is_R_or_C.norm_sq_pos
- \+ *lemma* is_R_or_C.norm_sq_sub
- \+ *lemma* is_R_or_C.norm_sq_to_complex
- \+ *lemma* is_R_or_C.norm_sq_to_real
- \+ *lemma* is_R_or_C.norm_sq_zero
- \+ *lemma* is_R_or_C.of_real_add
- \+ *lemma* is_R_or_C.of_real_alg
- \+ *lemma* is_R_or_C.of_real_bit0
- \+ *lemma* is_R_or_C.of_real_bit1
- \+ *lemma* is_R_or_C.of_real_div
- \+ *theorem* is_R_or_C.of_real_eq_zero
- \+ *lemma* is_R_or_C.of_real_fpow
- \+ *def* is_R_or_C.of_real_hom
- \+ *lemma* is_R_or_C.of_real_im
- \+ *theorem* is_R_or_C.of_real_inj
- \+ *theorem* is_R_or_C.of_real_int_cast
- \+ *lemma* is_R_or_C.of_real_inv
- \+ *lemma* is_R_or_C.of_real_mul
- \+ *theorem* is_R_or_C.of_real_nat_cast
- \+ *lemma* is_R_or_C.of_real_neg
- \+ *lemma* is_R_or_C.of_real_one
- \+ *lemma* is_R_or_C.of_real_pow
- \+ *theorem* is_R_or_C.of_real_rat_cast
- \+ *lemma* is_R_or_C.of_real_re
- \+ *lemma* is_R_or_C.of_real_sub
- \+ *lemma* is_R_or_C.of_real_to_complex
- \+ *lemma* is_R_or_C.of_real_to_real
- \+ *lemma* is_R_or_C.of_real_zero
- \+ *lemma* is_R_or_C.one_im
- \+ *lemma* is_R_or_C.one_re
- \+ *lemma* is_R_or_C.rat_cast_im
- \+ *lemma* is_R_or_C.rat_cast_re
- \+ *lemma* is_R_or_C.re_add_im
- \+ *theorem* is_R_or_C.re_eq_add_conj
- \+ *lemma* is_R_or_C.re_le_abs
- \+ *lemma* is_R_or_C.re_sq_le_norm_sq
- \+ *lemma* is_R_or_C.re_to_complex
- \+ *lemma* is_R_or_C.re_to_real
- \+ *lemma* is_R_or_C.smul_im'
- \+ *lemma* is_R_or_C.smul_im
- \+ *lemma* is_R_or_C.smul_re'
- \+ *lemma* is_R_or_C.smul_re
- \+ *theorem* is_R_or_C.sub_conj
- \+ *lemma* is_R_or_C.two_ne_zero
- \+ *lemma* is_R_or_C.zero_im
- \+ *lemma* is_R_or_C.zero_re



## [2020-08-30 04:53:26](https://github.com/leanprover-community/mathlib/commit/a18f142)
feat(set_theory/game): computation of grundy_value (nim n + nim m) ([#3977](https://github.com/leanprover-community/mathlib/pull/3977))
#### Estimated changes
Modified src/data/nat/bitwise.lean
- \+ *lemma* nat.lxor_trichotomy

Modified src/set_theory/game/nim.lean
- \+ *lemma* pgame.equiv_iff_grundy_value_eq
- \+/\- *lemma* pgame.equiv_nim_iff_grundy_value_eq
- \+ *lemma* pgame.equiv_zero_iff_grundy_value
- \+ *lemma* pgame.grundy_value_add
- \+ *lemma* pgame.grundy_value_nim_add_nim
- \+ *lemma* pgame.grundy_value_zero
- \+ *lemma* pgame.nim.exists_move_left_eq
- \+ *lemma* pgame.nim.exists_ordinal_move_left_eq
- \+ *lemma* pgame.nim_add_nim_equiv

Modified src/set_theory/pgame.lean
- \+ *theorem* pgame.equiv_congr_left
- \+ *theorem* pgame.equiv_congr_right



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
- \+/\- *theorem* add_pow_char
- \+ *theorem* add_pow_char_pow
- \+ *theorem* add_pow_char_pow_of_commute
- \+ *theorem* iterate_frobenius
- \+ *theorem* sub_pow_char
- \+ *theorem* sub_pow_char_of_commute
- \+ *theorem* sub_pow_char_pow
- \+ *theorem* sub_pow_char_pow_of_commute

Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.map_sub
- \+ *lemma* matrix.scalar_inj
- \+ *lemma* matrix.subsingleton_of_empty_left
- \+ *lemma* matrix.subsingleton_of_empty_right

Added src/data/matrix/char_p.lean


Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.commute_X

Modified src/field_theory/finite.lean
- \+ *lemma* finite_field.expand_card
- \+ *theorem* finite_field.frobenius_pow
- \+ *lemma* finite_field.pow_card
- \+/\- *lemma* finite_field.pow_card_sub_one_eq_one
- \+ *lemma* zmod.card_units
- \+ *lemma* zmod.expand_card
- \+ *lemma* zmod.pow_card
- \+ *theorem* zmod.pow_card_sub_one_eq_one
- \+ *theorem* zmod.units_pow_card_sub_one_eq_one

Modified src/field_theory/separable.lean
- \+ *theorem* polynomial.expand_char
- \+ *theorem* polynomial.map_expand
- \+ *theorem* polynomial.map_expand_pow_char

Modified src/linear_algebra/char_poly/coeff.lean
- \+ *lemma* finite_field.char_poly_pow_card
- \+ *lemma* finite_field.trace_pow_card
- \+ *lemma* zmod.char_poly_pow_card
- \+ *lemma* zmod.trace_pow_card

Modified src/number_theory/quadratic_reciprocity.lean
- \- *lemma* zmod.card_units
- \- *theorem* zmod.fermat_little
- \- *theorem* zmod.fermat_little_units



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
- \+ *lemma* linear_equiv.map_sum

Modified src/linear_algebra/basis.lean
- \- *def* equiv_fun_basis
- \- *lemma* equiv_fun_basis_symm_apply
- \+ *def* is_basis.equiv_fun
- \+ *lemma* is_basis.equiv_fun_apply
- \+ *lemma* is_basis.equiv_fun_self
- \+ *lemma* is_basis.equiv_fun_symm_apply
- \+ *lemma* is_basis.equiv_fun_total
- \+ *lemma* is_basis.repr_self_apply

Modified src/linear_algebra/matrix.lean
- \+ *def* is_basis.det
- \+ *lemma* is_basis.det_apply
- \+ *lemma* is_basis.det_self
- \+ *lemma* is_basis.iff_det
- \+ *def* is_basis.to_matrix
- \+ *lemma* is_basis.to_matrix_apply
- \+ *def* is_basis.to_matrix_equiv
- \+ *lemma* is_basis.to_matrix_self
- \+ *lemma* is_basis.to_matrix_update
- \+ *lemma* linear_equiv.is_unit_det
- \+ *def* linear_equiv.of_is_unit_det
- \- *lemma* matrix.linear_equiv.is_unit_det
- \- *def* matrix.linear_equiv.of_is_unit_det



## [2020-08-29 15:59:15](https://github.com/leanprover-community/mathlib/commit/94b1292)
doc(topology/sheaves): update module docs ([#3971](https://github.com/leanprover-community/mathlib/pull/3971))
#### Estimated changes
Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/sheaf_of_functions.lean




## [2020-08-29 15:59:13](https://github.com/leanprover-community/mathlib/commit/ba41f0a)
feat(data/nat): API for test_bit and bitwise operations ([#3964](https://github.com/leanprover-community/mathlib/pull/3964))
#### Estimated changes
Modified src/data/bool.lean
- \+ *theorem* bool.bxor_ff_left
- \+ *theorem* bool.bxor_ff_right

Modified src/data/nat/basic.lean
- \- *lemma* nat.bitwise_comm
- \- *lemma* nat.land_comm
- \- *lemma* nat.lor_comm
- \- *lemma* nat.lxor_comm

Added src/data/nat/bitwise.lean
- \+ *lemma* nat.bit_ff
- \+ *lemma* nat.bit_tt
- \+ *lemma* nat.bitwise_comm
- \+ *lemma* nat.eq_of_test_bit_eq
- \+ *lemma* nat.exists_most_significant_bit
- \+ *lemma* nat.land_assoc
- \+ *lemma* nat.land_comm
- \+ *lemma* nat.land_zero
- \+ *lemma* nat.lor_assoc
- \+ *lemma* nat.lor_comm
- \+ *lemma* nat.lor_zero
- \+ *lemma* nat.lt_of_test_bit
- \+ *lemma* nat.lxor_assoc
- \+ *lemma* nat.lxor_comm
- \+ *lemma* nat.lxor_eq_zero
- \+ *lemma* nat.lxor_left_inj
- \+ *lemma* nat.lxor_right_inj
- \+ *lemma* nat.lxor_self
- \+ *lemma* nat.lxor_zero
- \+ *lemma* nat.zero_land
- \+ *lemma* nat.zero_lor
- \+ *lemma* nat.zero_lxor
- \+ *lemma* nat.zero_of_test_bit_eq_ff
- \+ *lemma* nat.zero_test_bit



## [2020-08-29 14:16:16](https://github.com/leanprover-community/mathlib/commit/faf1df4)
chore(topology/sheaves/sheaf_of_functions): rely less on defeq ([#3972](https://github.com/leanprover-community/mathlib/pull/3972))
This backports some changes from the `prop_limits` branch.
#### Estimated changes
Modified src/category_theory/limits/shapes/types.lean
- \+ *lemma* category_theory.limits.types.lift_π_apply'

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
- \- *lemma* decidable.eq_or_lt_of_le
- \- *lemma* decidable.le_iff_lt_or_eq
- \- *lemma* decidable.le_imp_le_of_lt_imp_lt
- \- *lemma* decidable.le_of_not_lt
- \- *lemma* decidable.le_or_lt
- \- *def* decidable.lt_by_cases
- \- *lemma* decidable.lt_or_eq_of_le
- \- *lemma* decidable.lt_or_gt_of_ne
- \- *lemma* decidable.lt_or_le
- \- *lemma* decidable.lt_trichotomy
- \- *lemma* decidable.ne_iff_lt_or_gt
- \- *lemma* decidable.not_lt
- \- *lemma* not_le
- \- *lemma* not_lt

Modified src/analysis/analytic/composition.lean


Modified src/combinatorics/composition.lean
- \+/\- *lemma* composition.lt_size_up_to_index_succ
- \+/\- *lemma* composition_as_set.lt_length'
- \+/\- *lemma* composition_as_set.lt_length

Modified src/computability/primrec.lean
- \+/\- *theorem* primrec.fin_val

Modified src/data/array/lemmas.lean
- \+/\- *theorem* array.write_to_list

Modified src/data/bitvec/basic.lean
- \+/\- *lemma* bitvec.to_fin_val

Modified src/data/equiv/fin.lean


Modified src/data/fin.lean
- \- *lemma* fin.add_nat_val
- \- *lemma* fin.cast_add_val
- \- *lemma* fin.cast_le_val
- \+/\- *lemma* fin.cast_lt_cast_succ
- \- *lemma* fin.cast_lt_val
- \+/\- *lemma* fin.cast_succ_cast_lt
- \+/\- *lemma* fin.cast_succ_lt_last
- \- *lemma* fin.cast_succ_val
- \- *lemma* fin.cast_val
- \+/\- *def* fin.clamp
- \- *lemma* fin.clamp_val
- \+ *lemma* fin.coe_add
- \+ *lemma* fin.coe_add_nat
- \+ *lemma* fin.coe_cast
- \+ *lemma* fin.coe_cast_add
- \+ *lemma* fin.coe_cast_le
- \+ *lemma* fin.coe_cast_lt
- \+ *lemma* fin.coe_cast_succ
- \+ *lemma* fin.coe_clamp
- \+ *lemma* fin.coe_injective
- \+ *lemma* fin.coe_mul
- \+ *lemma* fin.coe_of_nat_eq_mod'
- \+ *lemma* fin.coe_of_nat_eq_mod
- \+ *lemma* fin.coe_one'
- \+ *lemma* fin.coe_pred
- \+ *lemma* fin.coe_sub_nat
- \+ *lemma* fin.coe_succ
- \+/\- *lemma* fin.coe_val_eq_self
- \+/\- *lemma* fin.eq_last_of_not_lt
- \+ *lemma* fin.ext
- \+ *lemma* fin.ext_iff
- \+ *lemma* fin.is_lt
- \+/\- *lemma* fin.last_val
- \+ *lemma* fin.le_iff_coe_le_coe
- \- *lemma* fin.le_iff_val_le_val
- \+ *lemma* fin.lt_iff_coe_lt_coe
- \- *lemma* fin.lt_iff_val_lt_val
- \+ *lemma* fin.mk_coe
- \+/\- *lemma* fin.mk_one
- \+/\- *lemma* fin.mk_zero
- \- *lemma* fin.pred_val
- \+/\- *def* fin.sub_nat
- \- *lemma* fin.sub_nat_val
- \+/\- *lemma* fin.succ_pos
- \- *lemma* fin.succ_val
- \+ *lemma* fin.val_eq_coe
- \- *lemma* fin.val_injective
- \- *lemma* fin.val_of_nat_eq_mod'
- \- *lemma* fin.val_of_nat_eq_mod
- \- *lemma* function.embedding.coe_fin
- \- *def* function.embedding.fin

Modified src/data/finset/basic.lean


Modified src/data/finset/sort.lean


Modified src/data/finsupp/basic.lean


Modified src/data/fintype/card.lean


Modified src/data/hash_map.lean


Modified src/data/list/of_fn.lean
- \+/\- *theorem* list.of_fn_nth_le

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


Added src/algebraic_geometry/structure_sheaf.lean
- \+ *def* algebraic_geometry.Spec.Top
- \+ *def* algebraic_geometry.structure_presheaf_comp_forget
- \+ *def* algebraic_geometry.structure_presheaf_in_CommRing
- \+ *def* algebraic_geometry.structure_sheaf.is_fraction
- \+ *def* algebraic_geometry.structure_sheaf.is_fraction_prelocal
- \+ *def* algebraic_geometry.structure_sheaf.is_locally_fraction
- \+ *lemma* algebraic_geometry.structure_sheaf.is_locally_fraction_pred
- \+ *def* algebraic_geometry.structure_sheaf.localizations
- \+ *def* algebraic_geometry.structure_sheaf.sections_subring
- \+ *def* algebraic_geometry.structure_sheaf
- \+ *def* algebraic_geometry.structure_sheaf_in_Type



## [2020-08-29 11:21:31](https://github.com/leanprover-community/mathlib/commit/84d47a0)
refactor(set_theory/game): make impartial a class ([#3974](https://github.com/leanprover-community/mathlib/pull/3974))
* Misc. style cleanups and code golf
* Changed naming and namespace to adhere more closely to the naming convention
* Changed `impartial` to be a `class`. I am aware that @semorrison explicitly requested not to make `impartial` a class in the [#3855](https://github.com/leanprover-community/mathlib/pull/3855), but after working with the definition a bit I concluded that making it a class is worth it, simply because writing `impartial_add (nim_impartial _) (nim_impartial _)` gets annoying quite quickly, but also because you tend to get goal states of the form `Grundy_value _ = Grundy_value _`. By making `impartial` a class and making the game argument explicit, these goal states look like `grundy_value G = grundy_value H`, which is much nicer to work with.
#### Estimated changes
Modified src/set_theory/game/impartial.lean
- \- *lemma* pgame.equiv_iff_sum_first_loses
- \- *lemma* pgame.good_left_move_iff_first_wins
- \- *lemma* pgame.good_right_move_iff_first_wins
- \+ *lemma* pgame.impartial.add_self
- \+ *lemma* pgame.impartial.equiv_iff_sum_first_loses
- \+ *lemma* pgame.impartial.first_loses_symm'
- \+ *lemma* pgame.impartial.first_loses_symm
- \+ *lemma* pgame.impartial.first_wins_symm'
- \+ *lemma* pgame.impartial.first_wins_symm
- \+ *lemma* pgame.impartial.good_left_move_iff_first_wins
- \+ *lemma* pgame.impartial.good_right_move_iff_first_wins
- \+ *lemma* pgame.impartial.le_zero_iff
- \+ *lemma* pgame.impartial.lt_zero_iff
- \+ *lemma* pgame.impartial.neg_equiv_self
- \+ *lemma* pgame.impartial.no_good_left_moves_iff_first_loses
- \+ *lemma* pgame.impartial.no_good_right_moves_iff_first_loses
- \+ *lemma* pgame.impartial.not_first_loses
- \+ *lemma* pgame.impartial.not_first_wins
- \+ *lemma* pgame.impartial.winner_cases
- \+/\- *def* pgame.impartial
- \- *lemma* pgame.impartial_add
- \- *lemma* pgame.impartial_add_self
- \- *lemma* pgame.impartial_first_loses_symm'
- \- *lemma* pgame.impartial_first_loses_symm
- \- *lemma* pgame.impartial_first_wins_symm'
- \- *lemma* pgame.impartial_first_wins_symm
- \- *lemma* pgame.impartial_move_left_impartial
- \- *lemma* pgame.impartial_move_right_impartial
- \- *lemma* pgame.impartial_neg
- \- *lemma* pgame.impartial_neg_equiv_self
- \- *lemma* pgame.impartial_not_first_loses
- \- *lemma* pgame.impartial_not_first_wins
- \- *lemma* pgame.impartial_winner_cases
- \- *lemma* pgame.no_good_left_moves_iff_first_loses
- \- *lemma* pgame.no_good_right_moves_iff_first_loses
- \- *lemma* pgame.zero_impartial

Modified src/set_theory/game/nim.lean
- \- *lemma* nim.Grundy_value_def
- \- *lemma* nim.Grundy_value_nim
- \- *theorem* nim.Sprague_Grundy
- \- *lemma* nim.equiv_nim_iff_Grundy_value_eq
- \- *lemma* nim.nim_def
- \- *lemma* nim.nim_equiv_iff_eq
- \- *lemma* nim.nim_impartial
- \- *lemma* nim.nim_non_zero_first_wins
- \- *lemma* nim.nim_sum_first_loses_iff_eq
- \- *lemma* nim.nim_sum_first_wins_iff_neq
- \- *lemma* nim.nim_wf_lemma
- \- *lemma* nim.nim_zero_first_loses
- \- *def* nim.nonmoves
- \- *lemma* nim.nonmoves_nonempty
- \+ *theorem* pgame.equiv_nim_grundy_value
- \+ *lemma* pgame.equiv_nim_iff_grundy_value_eq
- \+ *lemma* pgame.grundy_value_def
- \+ *lemma* pgame.nim.equiv_iff_eq
- \+ *lemma* pgame.nim.grundy_value
- \+ *lemma* pgame.nim.nim_def
- \+ *lemma* pgame.nim.nim_wf_lemma
- \+ *lemma* pgame.nim.non_zero_first_wins
- \+ *lemma* pgame.nim.sum_first_loses_iff_eq
- \+ *lemma* pgame.nim.sum_first_wins_iff_neq
- \+ *lemma* pgame.nim.zero_first_loses
- \+ *def* pgame.nonmoves
- \+ *lemma* pgame.nonmoves_nonempty

Modified src/set_theory/game/winner.lean
- \+/\- *theorem* pgame.star_first_wins



## [2020-08-29 04:30:09](https://github.com/leanprover-community/mathlib/commit/ea177c2)
feat(analysis/convex): add correspondence between convex cones and ordered semimodules ([#3931](https://github.com/leanprover-community/mathlib/pull/3931))
This shows that a convex cone defines an ordered semimodule and vice-versa.
#### Estimated changes
Modified src/algebra/module/ordered.lean


Modified src/analysis/convex/cone.lean
- \+ *def* convex_cone.blunt
- \+ *def* convex_cone.flat
- \+ *def* convex_cone.pointed
- \+ *lemma* convex_cone.pointed_iff_not_blunt
- \+ *lemma* convex_cone.pointed_of_positive_cone
- \+ *def* convex_cone.positive_cone
- \+ *def* convex_cone.salient
- \+ *lemma* convex_cone.salient_iff_not_flat
- \+ *lemma* convex_cone.salient_of_blunt
- \+ *lemma* convex_cone.salient_of_positive_cone
- \+ *def* convex_cone.to_ordered_add_comm_group
- \+ *def* convex_cone.to_ordered_semimodule
- \+ *def* convex_cone.to_partial_order
- \+ *def* convex_cone.to_preorder



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
- \+ *lemma* finsupp.mem_support_on_finset
- \+ *lemma* finsupp.support_on_finset

Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.coe_to_list
- \+ *lemma* multiset.mem_to_list
- \+ *lemma* multiset.prod_eq_zero
- \+ *lemma* multiset.to_list_zero

Modified src/field_theory/algebraic_closure.lean
- \+ *lemma* is_alg_closed.degree_eq_one_of_irreducible

Modified src/field_theory/splitting_field.lean
- \+ *lemma* polynomial.degree_eq_one_of_irreducible_of_splits

Modified src/group_theory/submonoid/basic.lean
- \+ *lemma* is_unit.mem_submonoid_iff
- \+ *def* is_unit.submonoid

Added src/linear_algebra/eigenspace.lean
- \+ *def* module.End.eigenspace
- \+ *lemma* module.End.eigenspace_div
- \+ *lemma* module.End.eigenspace_eval₂_polynomial_degree_1
- \+ *lemma* module.End.eigenvectors_linear_independent
- \+ *lemma* module.End.exists_eigenvalue
- \+ *def* module.End.has_eigenvalue
- \+ *def* module.End.has_eigenvector
- \+ *lemma* module.End.ker_eval₂_ring_hom_noncomm_unit_polynomial
- \+ *lemma* module.End.mem_eigenspace_iff

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.not_linear_independent_of_infinite

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp.total_on_finset

Modified src/ring_theory/algebra.lean
- \+ *lemma* module.algebra_map_End_apply
- \+ *lemma* module.algebra_map_End_eq_smul_id
- \+ *lemma* module.ker_algebra_map_End

Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* polynomial.linear_independent_powers_iff_eval₂

Modified src/ring_theory/principal_ideal_domain.lean
- \+ *lemma* principal_ideal_ring.mem_submonoid_of_factors_subset_of_units_subset
- \+ *lemma* principal_ideal_ring.ne_zero_of_mem_factors
- \+ *lemma* principal_ideal_ring.ring_hom_mem_submonoid_of_factors_subset_of_units_subset



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
Added src/category_theory/limits/shapes/kernel_pair.lean
- \+ *def* category_theory.is_kernel_pair.cancel_right
- \+ *def* category_theory.is_kernel_pair.cancel_right_of_mono
- \+ *def* category_theory.is_kernel_pair.comp_of_mono
- \+ *def* category_theory.is_kernel_pair.id_of_mono
- \+ *def* category_theory.is_kernel_pair.lift'
- \+ *def* category_theory.is_kernel_pair.to_coequalizer
- \+ *structure* category_theory.is_kernel_pair



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
- \+/\- *lemma* pfunctor.M.ext'

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


Added src/tactic/congr.lean


Modified src/tactic/ext.lean


Modified src/tactic/interactive.lean


Modified src/topology/algebra/multilinear.lean


Modified src/topology/bases.lean


Modified src/topology/opens.lean


Modified src/topology/uniform_space/compact_separated.lean


Added test/congr.lean


Modified test/tactics.lean


Modified test/trunc_cases.lean




## [2020-08-28 07:24:16](https://github.com/leanprover-community/mathlib/commit/ceacf54)
feat(category_theory/filtered): filtered categories, and filtered colimits in `Type` ([#3960](https://github.com/leanprover-community/mathlib/pull/3960))
This is some work @rwbarton did last year. I've merged master, written some comments, and satisfied the linter.
#### Estimated changes
Added src/category_theory/filtered.lean


Modified src/category_theory/limits/types.lean
- \+ *lemma* category_theory.limits.types.filtered_colimit.colimit_eq_iff
- \+ *lemma* category_theory.limits.types.filtered_colimit.is_colimit_eq_iff
- \+ *lemma* category_theory.limits.types.jointly_surjective
- \+ *lemma* category_theory.limits.types.ι_desc_apply

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
Added src/topology/sheaves/forget.lean
- \+ *def* Top.sheaf_condition.diagram_comp_preserves_limits
- \+ *def* Top.sheaf_condition.map_cone_fork
- \+ *def* Top.sheaf_condition_equiv_sheaf_condition_comp



## [2020-08-28 03:16:37](https://github.com/leanprover-community/mathlib/commit/7e6393f)
feat(topology/sheaves): the sheaf condition for functions satisfying a local predicate ([#3906](https://github.com/leanprover-community/mathlib/pull/3906))
Functions satisfying a local predicate form a sheaf.
This sheaf has a natural map from the stalk to the original fiber, and we give conditions for this map to be injective or surjective.
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* category_theory.limits.cofork.ext
- \+ *def* category_theory.limits.fork.ext

Modified src/category_theory/limits/shapes/products.lean
- \+ *abbreviation* category_theory.limits.pi.map_iso
- \+ *abbreviation* category_theory.limits.sigma.map_iso

Modified src/data/set/basic.lean
- \+ *lemma* set.inclusion_right

Modified src/topology/category/Top/open_nhds.lean
- \+/\- *def* topological_space.open_nhds.inclusion
- \+/\- *lemma* topological_space.open_nhds.inclusion_obj
- \+/\- *def* topological_space.open_nhds

Added src/topology/sheaves/local_predicate.lean
- \+ *def* Top.continuous_local
- \+ *def* Top.continuous_prelocal
- \+ *structure* Top.local_predicate
- \+ *def* Top.prelocal_predicate.sheafify
- \+ *structure* Top.prelocal_predicate
- \+ *def* Top.sheaf_to_Top
- \+ *def* Top.stalk_to_fiber
- \+ *lemma* Top.stalk_to_fiber_germ
- \+ *lemma* Top.stalk_to_fiber_injective
- \+ *lemma* Top.stalk_to_fiber_surjective
- \+ *def* Top.subpresheaf_continuous_prelocal_iso_presheaf_to_Top
- \+ *def* Top.subpresheaf_to_Types.diagram_subtype
- \+ *def* Top.subpresheaf_to_Types.sheaf_condition
- \+ *def* Top.subpresheaf_to_Types.subtype
- \+ *def* Top.subpresheaf_to_Types
- \+ *def* Top.subsheaf_to_Types

Modified src/topology/sheaves/presheaf_of_functions.lean
- \+ *lemma* Top.presheaf_to_Top_obj
- \+/\- *def* Top.presheaf_to_Types
- \+ *lemma* Top.presheaf_to_Types_map
- \+ *lemma* Top.presheaf_to_Types_obj

Modified src/topology/sheaves/sheaf.lean
- \+ *def* Top.sheaf_condition.diagram.iso_of_iso
- \+ *def* Top.sheaf_condition.fork.iso_of_iso
- \+ *def* Top.sheaf_condition.pi_inters.iso_of_iso
- \+ *def* Top.sheaf_condition.pi_opens.iso_of_iso
- \+ *def* Top.sheaf_condition_equiv_of_iso

Modified src/topology/sheaves/sheaf_of_functions.lean
- \- *def* Top.sheaf_condition.forget_continuity
- \- *def* Top.sheaf_condition.to_Top
- \+ *def* Top.sheaf_to_Type
- \+ *def* Top.sheaf_to_Types

Modified src/topology/sheaves/stalks.lean
- \+ *def* Top.presheaf.germ
- \+ *lemma* Top.presheaf.germ_res
- \+ *lemma* Top.presheaf.germ_res_apply
- \+/\- *lemma* Top.presheaf.stalk_functor_obj



## [2020-08-27 20:30:40](https://github.com/leanprover-community/mathlib/commit/eaaac99)
feat(geometry/euclidean/basic): reflection ([#3932](https://github.com/leanprover-community/mathlib/pull/3932))
Define the reflection of a point in an affine subspace, as a bundled
isometry, in terms of the orthogonal projection onto that subspace,
and prove some basic lemmas about it.
#### Estimated changes
Modified src/geometry/euclidean/basic.lean
- \+ *lemma* euclidean_geometry.dist_reflection
- \+ *lemma* euclidean_geometry.dist_reflection_eq_of_mem
- \+ *lemma* euclidean_geometry.orthogonal_projection_linear
- \+ *lemma* euclidean_geometry.orthogonal_projection_orthogonal_projection
- \+ *def* euclidean_geometry.reflection
- \+ *lemma* euclidean_geometry.reflection_apply
- \+ *lemma* euclidean_geometry.reflection_eq_iff_orthogonal_projection_eq
- \+ *lemma* euclidean_geometry.reflection_eq_self_iff
- \+ *lemma* euclidean_geometry.reflection_involutive
- \+ *lemma* euclidean_geometry.reflection_reflection
- \+ *lemma* euclidean_geometry.reflection_symm



## [2020-08-27 18:31:26](https://github.com/leanprover-community/mathlib/commit/359261e)
feat(data/nat): commutativity of bitwise operations ([#3956](https://github.com/leanprover-community/mathlib/pull/3956))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.bitwise_comm
- \+ *lemma* nat.land_comm
- \+ *lemma* nat.lor_comm
- \+ *lemma* nat.lxor_comm



## [2020-08-27 14:44:42](https://github.com/leanprover-community/mathlib/commit/6b556cf)
feat(combinatorics/adjacency_matrix): defines adjacency matrices of simple graphs ([#3672](https://github.com/leanprover-community/mathlib/pull/3672))
defines the adjacency matrix of a simple graph
proves lemmas about adjacency matrix that will form the bulk of the proof of the friendship theorem (freek 83)
#### Estimated changes
Added src/combinatorics/adj_matrix.lean
- \+ *def* simple_graph.adj_matrix
- \+ *lemma* simple_graph.adj_matrix_apply
- \+ *lemma* simple_graph.adj_matrix_dot_product
- \+ *lemma* simple_graph.adj_matrix_mul_apply
- \+ *theorem* simple_graph.adj_matrix_mul_self_apply_self
- \+ *lemma* simple_graph.adj_matrix_mul_vec_apply
- \+ *lemma* simple_graph.adj_matrix_mul_vec_const_apply
- \+ *lemma* simple_graph.adj_matrix_mul_vec_const_apply_of_regular
- \+ *lemma* simple_graph.adj_matrix_vec_mul_apply
- \+ *lemma* simple_graph.dot_product_adj_matrix
- \+ *lemma* simple_graph.mul_adj_matrix_apply
- \+ *theorem* simple_graph.trace_adj_matrix
- \+ *theorem* simple_graph.transpose_adj_matrix



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
- \+/\- *def* orthogonal_projection
- \+ *lemma* orthogonal_projection_def
- \+/\- *lemma* orthogonal_projection_inner_eq_zero
- \+ *def* orthogonal_projection_of_complete

Modified src/geometry/euclidean/basic.lean
- \+/\- *def* euclidean_geometry.orthogonal_projection
- \+ *lemma* euclidean_geometry.orthogonal_projection_def
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_mem_orthogonal
- \+ *def* euclidean_geometry.orthogonal_projection_of_nonempty_of_complete
- \+ *lemma* euclidean_geometry.orthogonal_projection_of_nonempty_of_complete_eq
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_vsub_mem_direction_orthogonal
- \+/\- *lemma* euclidean_geometry.vsub_orthogonal_projection_mem_direction_orthogonal

Modified src/geometry/euclidean/circumcenter.lean
- \+/\- *lemma* euclidean_geometry.dist_eq_iff_dist_orthogonal_projection_eq
- \+/\- *lemma* euclidean_geometry.dist_set_eq_iff_dist_orthogonal_projection_eq
- \+/\- *lemma* euclidean_geometry.exists_unique_dist_eq_of_insert



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
- \+ *lemma* fin.add_one_pos
- \+ *lemma* fin.cast_succ_lt_last
- \+ *lemma* fin.cast_succ_lt_succ
- \- *lemma* fin.cast_succ_ne_last
- \+ *lemma* fin.cast_succ_zero
- \+ *lemma* fin.coe_eq_cast_succ
- \+ *lemma* fin.coe_nat_eq_last
- \+ *lemma* fin.coe_succ_eq_succ
- \+ *lemma* fin.eq_mk_iff_coe_eq
- \+ *lemma* fin.last_pos
- \+ *lemma* fin.le_coe_last
- \+ *lemma* fin.lt_succ
- \+ *lemma* fin.mk_bit0
- \+ *lemma* fin.mk_bit1
- \+ *lemma* fin.mk_one
- \+ *lemma* fin.mk_succ_pos
- \+ *lemma* fin.mk_zero
- \+ *lemma* fin.ne_iff_vne
- \+ *lemma* fin.one_lt_succ_succ
- \+ *lemma* fin.one_pos
- \+ *lemma* fin.pred_add_one
- \+ *lemma* fin.pred_mk_succ
- \+ *lemma* fin.pred_one
- \+ *lemma* fin.succ_above_above
- \+ *lemma* fin.succ_above_below
- \+ *lemma* fin.succ_above_last
- \+ *lemma* fin.succ_above_pos
- \+ *lemma* fin.succ_above_zero
- \+ *lemma* fin.succ_le_succ_iff
- \+ *lemma* fin.succ_lt_succ_iff
- \+ *lemma* fin.succ_pos
- \+ *lemma* fin.succ_succ_ne_one
- \+ *lemma* fin.succ_zero_eq_one
- \+ *lemma* fin.val_zero'
- \+ *lemma* fin.zero_ne_one
- \- *lemma* fin.zero_val

Modified src/data/fintype/card.lean


Modified src/data/matrix/notation.lean
- \+/\- *lemma* matrix.cons_val_zero'

Modified src/linear_algebra/multilinear.lean




## [2020-08-26 18:55:44](https://github.com/leanprover-community/mathlib/commit/26dfea5)
feat(algebra/big_operators): sum of two products ([#3944](https://github.com/leanprover-community/mathlib/pull/3944))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.mul_prod_diff_singleton
- \+ *lemma* finset.prod_add_prod_eq
- \+ *lemma* finset.prod_inter_mul_prod_diff

Modified src/algebra/big_operators/order.lean
- \+ *lemma* finset.prod_add_prod_le'
- \+ *lemma* finset.prod_add_prod_le

Modified src/algebra/group_with_zero_power.lean
- \+ *lemma* zero_pow_eq_zero

Modified src/algebra/ordered_ring.lean
- \+ *lemma* canonically_ordered_semiring.mul_le_mul_left'
- \+ *lemma* canonically_ordered_semiring.mul_le_mul_right'



## [2020-08-26 18:55:42](https://github.com/leanprover-community/mathlib/commit/64aad5b)
feat(category_theory/adjunction): uniqueness of adjunctions ([#3940](https://github.com/leanprover-community/mathlib/pull/3940))
Co-authored by @thjread
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/opposites.lean
- \+ *def* adjunction.left_adjoint_uniq
- \+ *def* adjunction.left_adjoints_coyoneda_equiv
- \+ *def* adjunction.right_adjoint_uniq



## [2020-08-26 18:55:40](https://github.com/leanprover-community/mathlib/commit/080746f)
feat(algebra/category/*/limits): don't rely on definitions ([#3873](https://github.com/leanprover-community/mathlib/pull/3873))
This is a second attempt (which works **much** better) at [#3860](https://github.com/leanprover-community/mathlib/pull/3860), after @TwoFX explained how to do it properly.
This PR takes the constructions of limits in the concrete categories `(Add)(Comm)[Mon|Group]`, `(Comm)(Semi)Ring`, `Module R`, and `Algebra R`, and makes sure that they never rely on the actual definitions of limits in "prior" categories.
Of course, at this stage the `has_limit` typeclasses still contain data, so it's hard to judge whether we're really not relying on the definitions. I've marked all the `has_limits` instances in these files as irreducible, but the real proof is just that this same code is working over on the `prop_limits` branch.
#### Estimated changes
Modified src/algebra/category/Algebra/limits.lean
- \+ *def* Algebra.forget₂_Module_preserves_limits_aux
- \+ *def* Algebra.forget₂_Ring_preserves_limits_aux
- \- *def* Algebra.has_limits.limit
- \+ *def* Algebra.has_limits.limit_cone
- \+ *def* Algebra.has_limits.limit_cone_is_limit
- \- *def* Algebra.has_limits.limit_is_limit

Modified src/algebra/category/CommRing/limits.lean
- \+ *def* CommRing.forget₂_CommSemiRing_preserves_limits_aux
- \+ *def* CommRing.limit_cone
- \+ *def* CommRing.limit_cone_is_limit
- \+ *def* CommSemiRing.limit_cone
- \+ *def* CommSemiRing.limit_cone_is_limit
- \+ *def* Ring.limit_cone
- \+ *def* Ring.limit_cone_is_limit
- \- *def* SemiRing.has_limits.limit
- \+ *def* SemiRing.has_limits.limit_cone
- \+ *def* SemiRing.has_limits.limit_cone_is_limit
- \- *def* SemiRing.has_limits.limit_is_limit

Modified src/algebra/category/Group/limits.lean
- \+ *lemma* AddCommGroup.lift_π_apply
- \+ *def* CommGroup.limit_cone
- \+ *def* CommGroup.limit_cone_is_limit
- \+ *def* Group.limit_cone
- \+ *def* Group.limit_cone_is_limit

Modified src/algebra/category/Module/limits.lean
- \+ *def* Module.forget₂_AddCommGroup_preserves_limits_aux
- \- *def* Module.has_limits.limit
- \+ *def* Module.has_limits.limit_cone
- \+ *def* Module.has_limits.limit_cone_is_limit
- \- *def* Module.has_limits.limit_is_limit

Modified src/algebra/category/Mon/limits.lean
- \+ *def* CommMon.limit_cone
- \+ *def* CommMon.limit_cone_is_limit
- \- *def* Mon.has_limits.limit
- \+ *def* Mon.has_limits.limit_cone
- \+ *def* Mon.has_limits.limit_cone_is_limit
- \- *def* Mon.has_limits.limit_is_limit

Modified src/topology/category/Top/limits.lean
- \- *def* Top.colimit
- \+ *def* Top.colimit_cocone
- \+ *def* Top.colimit_cocone_is_colimit
- \- *def* Top.colimit_is_colimit
- \- *def* Top.limit
- \+ *def* Top.limit_cone
- \+ *def* Top.limit_cone_is_limit
- \- *def* Top.limit_is_limit



## [2020-08-26 17:53:30](https://github.com/leanprover-community/mathlib/commit/2d9ab61)
feat(ring_theory/ideal/basic): R/I is an ID iff I is prime ([#3951](https://github.com/leanprover-community/mathlib/pull/3951))
`is_integral_domain_iff_prime (I : ideal α) : is_integral_domain I.quotient ↔ I.is_prime`
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* ideal.quotient.is_integral_domain_iff_prime



## [2020-08-26 16:20:07](https://github.com/leanprover-community/mathlib/commit/2b6924d)
feat(topology/algebra/ordered): conditions for a strictly monotone function to be a homeomorphism ([#3843](https://github.com/leanprover-community/mathlib/pull/3843))
If a strictly monotone function between linear orders is surjective, it is a homeomorphism.
If a strictly monotone function between conditionally complete linear orders is continuous, and tends to `+∞` at `+∞` and to `-∞` at `-∞`, then it is a homeomorphism.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Order.20topology)
Co-authored by: Yury Kudryashov <urkud@ya.ru>
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Ici_bot
- \+ *lemma* set.Ici_singleton_of_top
- \+ *lemma* set.Ici_top
- \+ *lemma* set.Iic_singleton_of_bot

Added src/data/set/intervals/surj_on.lean
- \+ *lemma* surj_on_Icc_of_monotone_surjective
- \+ *lemma* surj_on_Ici_of_monotone_surjective
- \+ *lemma* surj_on_Ico_of_monotone_surjective
- \+ *lemma* surj_on_Iic_of_monotone_surjective
- \+ *lemma* surj_on_Iio_of_monotone_surjective
- \+ *lemma* surj_on_Ioc_of_monotone_surjective
- \+ *lemma* surj_on_Ioi_of_monotone_surjective
- \+ *lemma* surj_on_Ioo_of_monotone_surjective

Modified src/order/basic.lean
- \+ *lemma* strict_mono.bot_preimage_bot
- \+ *lemma* strict_mono.top_preimage_top

Modified src/order/bounded_lattice.lean
- \+ *lemma* strict_mono.bot_preimage_bot'
- \+ *lemma* strict_mono.top_preimage_top'

Modified src/topology/algebra/ordered.lean
- \+ *lemma* coe_homeomorph_of_strict_mono_continuous
- \+ *lemma* coe_homeomorph_of_strict_mono_surjective
- \+ *lemma* continuous_at_of_strict_mono_surjective
- \+ *lemma* continuous_inv_of_strict_mono_equiv
- \+ *lemma* continuous_left_of_strict_mono_surjective
- \+ *lemma* continuous_of_strict_mono_surjective
- \+ *lemma* continuous_right_of_strict_mono_surjective
- \+ *lemma* surjective_of_continuous'
- \+ *lemma* surjective_of_continuous



## [2020-08-26 14:45:52](https://github.com/leanprover-community/mathlib/commit/f4f0854)
feat(ring_theory/bundled_subring): add bundled subrings ([#3886](https://github.com/leanprover-community/mathlib/pull/3886))
#### Estimated changes
Modified src/algebra/category/CommRing/limits.lean


Added src/deprecated/subring.lean
- \+ *lemma* is_subring.coe_subtype
- \+ *def* is_subring.subtype
- \+ *lemma* is_subring_Union_of_directed
- \+ *def* ring.closure
- \+ *theorem* ring.closure_mono
- \+ *theorem* ring.closure_subset
- \+ *theorem* ring.closure_subset_iff
- \+ *theorem* ring.exists_list_of_mem_closure
- \+ *lemma* ring.image_closure
- \+ *theorem* ring.mem_closure
- \+ *theorem* ring.subset_closure
- \+ *def* ring_hom.cod_restrict

Modified src/field_theory/subfield.lean


Modified src/group_theory/subgroup.lean
- \+ *def* monoid_hom.cod_restrict
- \+ *lemma* subgroup.coe_supr_of_directed

Modified src/linear_algebra/basic.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/subring.lean
- \- *lemma* is_subring.coe_subtype
- \- *def* is_subring.subtype
- \- *lemma* is_subring_Union_of_directed
- \- *def* ring.closure
- \- *theorem* ring.closure_mono
- \- *theorem* ring.closure_subset
- \- *theorem* ring.closure_subset_iff
- \- *theorem* ring.exists_list_of_mem_closure
- \- *lemma* ring.image_closure
- \- *theorem* ring.mem_closure
- \- *theorem* ring.subset_closure
- \+ *def* ring_equiv.subring_congr
- \+ *lemma* ring_hom.closure_preimage_le
- \+ *def* ring_hom.cod_restrict'
- \- *def* ring_hom.cod_restrict
- \+ *lemma* ring_hom.coe_range
- \+ *lemma* ring_hom.coe_range_restrict
- \+ *def* ring_hom.eq_locus
- \+ *lemma* ring_hom.eq_of_eq_on_set_dense
- \+ *lemma* ring_hom.eq_of_eq_on_set_top
- \+ *lemma* ring_hom.eq_on_set_closure
- \+ *lemma* ring_hom.map_closure
- \+ *lemma* ring_hom.map_range
- \+ *lemma* ring_hom.mem_range
- \+ *def* ring_hom.range
- \+ *def* ring_hom.range_restrict
- \+ *lemma* ring_hom.range_top_iff_surjective
- \+ *lemma* ring_hom.range_top_of_surjective
- \+ *def* ring_hom.restrict
- \+ *lemma* ring_hom.restrict_apply
- \+ *lemma* subring.Inf_to_add_subgroup
- \+ *lemma* subring.Inf_to_submonoid
- \+ *theorem* subring.add_mem
- \+ *def* subring.closure
- \+ *lemma* subring.closure_Union
- \+ *lemma* subring.closure_empty
- \+ *lemma* subring.closure_eq
- \+ *lemma* subring.closure_eq_of_le
- \+ *lemma* subring.closure_induction
- \+ *lemma* subring.closure_le
- \+ *lemma* subring.closure_mono
- \+ *lemma* subring.closure_preimage_le
- \+ *lemma* subring.closure_sUnion
- \+ *lemma* subring.closure_union
- \+ *lemma* subring.closure_univ
- \+ *lemma* subring.coe_Inf
- \+ *lemma* subring.coe_Sup_of_directed_on
- \+ *lemma* subring.coe_add
- \+ *lemma* subring.coe_bot
- \+ *lemma* subring.coe_coe
- \+ *lemma* subring.coe_comap
- \+ *lemma* subring.coe_inf
- \+ *lemma* subring.coe_int_mem
- \+ *lemma* subring.coe_map
- \+ *lemma* subring.coe_mk'
- \+ *lemma* subring.coe_mul
- \+ *lemma* subring.coe_neg
- \+ *lemma* subring.coe_one
- \+ *lemma* subring.coe_prod
- \+ *lemma* subring.coe_ssubset_coe
- \+ *lemma* subring.coe_subset_coe
- \+ *theorem* subring.coe_subtype
- \+ *lemma* subring.coe_supr_of_directed
- \+ *lemma* subring.coe_to_add_subgroup
- \+ *lemma* subring.coe_to_submonoid
- \+ *lemma* subring.coe_top
- \+ *lemma* subring.coe_zero
- \+ *def* subring.comap
- \+ *lemma* subring.comap_comap
- \+ *lemma* subring.comap_inf
- \+ *lemma* subring.comap_infi
- \+ *lemma* subring.comap_top
- \+ *theorem* subring.exists_list_of_mem_closure
- \+ *theorem* subring.ext'
- \+ *theorem* subring.ext
- \+ *lemma* subring.gc_map_comap
- \+ *lemma* subring.gsmul_mem
- \+ *def* subring.inclusion
- \+ *lemma* subring.le_def
- \+ *lemma* subring.list_prod_mem
- \+ *lemma* subring.list_sum_mem
- \+ *def* subring.map
- \+ *lemma* subring.map_bot
- \+ *lemma* subring.map_le_iff_le_comap
- \+ *lemma* subring.map_map
- \+ *lemma* subring.map_sup
- \+ *lemma* subring.map_supr
- \+ *lemma* subring.mem_Inf
- \+ *lemma* subring.mem_Sup_of_directed_on
- \+ *lemma* subring.mem_bot
- \+ *lemma* subring.mem_closure
- \+ *lemma* subring.mem_closure_iff
- \+ *lemma* subring.mem_coe
- \+ *lemma* subring.mem_comap
- \+ *lemma* subring.mem_inf
- \+ *lemma* subring.mem_map
- \+ *lemma* subring.mem_mk'
- \+ *lemma* subring.mem_prod
- \+ *lemma* subring.mem_supr_of_directed
- \+ *lemma* subring.mem_to_add_subgroup
- \+ *lemma* subring.mem_to_submonoid
- \+ *lemma* subring.mem_top
- \+ *lemma* subring.mk'_to_add_subgroup
- \+ *lemma* subring.mk'_to_submonoid
- \+ *theorem* subring.mul_mem
- \+ *lemma* subring.multiset_prod_mem
- \+ *lemma* subring.multiset_sum_mem
- \+ *theorem* subring.neg_mem
- \+ *theorem* subring.one_mem
- \+ *lemma* subring.pow_mem
- \+ *def* subring.prod
- \+ *lemma* subring.prod_bot_sup_bot_prod
- \+ *def* subring.prod_equiv
- \+ *lemma* subring.prod_mem
- \+ *lemma* subring.prod_mono
- \+ *lemma* subring.prod_mono_left
- \+ *lemma* subring.prod_mono_right
- \+ *lemma* subring.prod_top
- \+ *lemma* subring.range_fst
- \+ *lemma* subring.range_snd
- \+ *lemma* subring.range_subtype
- \+ *lemma* subring.subset_closure
- \+ *def* subring.subset_comm_ring
- \+ *def* subring.subtype
- \+ *lemma* subring.sum_mem
- \+ *def* subring.to_comm_ring
- \+ *def* subring.to_submonoid
- \+ *lemma* subring.top_prod
- \+ *lemma* subring.top_prod_top
- \+ *theorem* subring.zero_mem
- \+ *structure* subring
- \+ *def* subsemiring.to_subring

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
- \+ *lemma* submodule.lt_add_iff_not_mem
- \+ *lemma* submodule.nonzero_mem_of_bot_lt

Modified src/order/rel_classes.lean
- \+ *lemma* well_founded.eq_iff_not_lt_of_le
- \+ *theorem* well_founded.well_founded_iff_has_max'
- \+ *theorem* well_founded.well_founded_iff_has_min'
- \+ *theorem* well_founded.well_founded_iff_has_min

Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* ideal.bot_prime

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.mul_eq_bot

Modified src/ring_theory/localization.lean


Modified src/ring_theory/noetherian.lean
- \+ *theorem* set_has_maximal_iff_noetherian



## [2020-08-26 13:12:40](https://github.com/leanprover-community/mathlib/commit/187bfa5)
feat(set/basic): additions to prod ([#3943](https://github.com/leanprover-community/mathlib/pull/3943))
Also add one lemma about `Inter`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *theorem* set.insert_prod
- \+ *lemma* set.mk_preimage_prod_left_eq_empty
- \+ *lemma* set.mk_preimage_prod_left_eq_if
- \+ *lemma* set.mk_preimage_prod_right_eq_empty
- \+ *lemma* set.mk_preimage_prod_right_eq_if
- \+/\- *theorem* set.prod_eq_empty_iff
- \+/\- *theorem* set.prod_insert
- \+ *lemma* set.prod_univ
- \+ *lemma* set.univ_prod

Modified src/data/set/lattice.lean
- \+ *lemma* set.Inter_set_of



## [2020-08-26 13:12:38](https://github.com/leanprover-community/mathlib/commit/fb6046e)
feat(*/category/*): add coe_of simp lemmas ([#3938](https://github.com/leanprover-community/mathlib/pull/3938))
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean
- \+ *lemma* Algebra.coe_of
- \- *lemma* Algebra.of_apply

Modified src/algebra/category/CommRing/basic.lean
- \+ *lemma* CommRing.coe_of
- \+ *lemma* CommSemiRing.coe_of
- \+ *lemma* Ring.coe_of
- \+ *lemma* SemiRing.coe_of

Modified src/algebra/category/Group/basic.lean
- \+ *lemma* CommGroup.coe_of
- \+ *lemma* Group.coe_of

Modified src/algebra/category/Module/basic.lean
- \+ *lemma* Module.coe_of
- \- *lemma* Module.of_apply

Modified src/algebra/category/Mon/basic.lean
- \+ *lemma* CommMon.coe_of
- \+ *lemma* Mon.coe_of

Modified src/measure_theory/category/Meas.lean
- \+ *lemma* Meas.coe_of

Modified src/topology/category/Top/basic.lean
- \+ *lemma* Top.coe_of

Modified src/topology/category/TopCommRing.lean
- \+ *lemma* TopCommRing.coe_of

Modified src/topology/category/UniformSpace.lean
- \+ *lemma* CpltSepUniformSpace.coe_of
- \+ *lemma* UniformSpace.coe_of



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
- \+ *lemma* finsupp.hom_ext
- \+ *lemma* finsupp.smul_single_one



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
- \+ *lemma* with_one.some_eq_coe

Modified src/algebra/ordered_group.lean
- \+ *lemma* with_zero.coe_le_coe
- \+ *lemma* with_zero.coe_lt_coe
- \+ *lemma* with_zero.lt_of_mul_lt_mul_left
- \+ *lemma* with_zero.mul_le_mul_left
- \+ *lemma* with_zero.zero_le
- \+ *lemma* with_zero.zero_lt_coe

Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/mean_inequalities.lean


Modified src/topology/instances/ennreal.lean




## [2020-08-25 16:55:18](https://github.com/leanprover-community/mathlib/commit/4478719)
feat(data/padic/padic_integers): homs to zmod(p ^ n) ([#3882](https://github.com/leanprover-community/mathlib/pull/3882))
This is the next PR in a series of PRs on the padic numbers/integers that should culminate in a proof that Z_p is isomorphic to the ring of Witt vectors of zmod p.
In this PR we build ring homs from Z_p to zmod (p ^ n).
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.to_nat_zero_of_neg

Modified src/data/padics/padic_integers.lean
- \+ *lemma* padic_int.appr_lt
- \+ *lemma* padic_int.appr_spec
- \+ *lemma* padic_int.coe_coe_int
- \+ *lemma* padic_int.coe_int_eq
- \+ *lemma* padic_int.exists_mem_range
- \+ *lemma* padic_int.is_unit_denom
- \+ *lemma* padic_int.ker_to_zmod
- \+ *lemma* padic_int.ker_to_zmod_pow
- \+/\- *lemma* padic_int.maximal_ideal_eq_span_p
- \+ *def* padic_int.mod_part
- \+ *lemma* padic_int.mod_part_lt_p
- \+ *lemma* padic_int.mod_part_nonneg
- \+ *lemma* padic_int.norm_int_lt_one_iff_dvd
- \+ *lemma* padic_int.norm_lt_one_iff_dvd
- \+ *lemma* padic_int.norm_sub_mod_part
- \+ *lemma* padic_int.norm_sub_mod_part_aux
- \+ *lemma* padic_int.pow_p_dvd_int_iff
- \+ *lemma* padic_int.sub_zmod_repr_mem
- \+ *def* padic_int.to_zmod
- \+ *def* padic_int.to_zmod_hom
- \+ *def* padic_int.to_zmod_pow
- \+ *lemma* padic_int.to_zmod_spec
- \+ *lemma* padic_int.valuation_p_pow_mul
- \+ *lemma* padic_int.zmod_congr_of_sub_mem_max_ideal
- \+ *lemma* padic_int.zmod_congr_of_sub_mem_span
- \+ *lemma* padic_int.zmod_congr_of_sub_mem_span_aux
- \+ *def* padic_int.zmod_repr
- \+ *lemma* padic_int.zmod_repr_lt_p
- \+ *lemma* padic_int.zmod_repr_spec
- \+ *lemma* padic_norm_z.padic_norm_z_of_int

Modified src/data/padics/padic_norm.lean
- \+ *lemma* padic_norm.dvd_iff_norm_le
- \- *lemma* padic_norm.le_of_dvd

Modified src/data/padics/padic_numbers.lean
- \+ *theorem* padic_norm_e.norm_int_le_one
- \+ *lemma* padic_norm_e.norm_int_lt_one_iff_dvd
- \+ *lemma* padic_norm_e.norm_int_lt_pow_iff_dvd

Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.coe_to_nat

Modified src/ring_theory/discrete_valuation_ring.lean
- \+ *lemma* discrete_valuation_ring.unit_mul_pow_congr_pow
- \+ *lemma* discrete_valuation_ring.unit_mul_pow_congr_unit



## [2020-08-25 14:36:42](https://github.com/leanprover-community/mathlib/commit/b03ce61)
chore(set_theory/game): various cleanup and code golf ([#3939](https://github.com/leanprover-community/mathlib/pull/3939))
#### Estimated changes
Modified src/set_theory/game/impartial.lean
- \+ *lemma* pgame.impartial_not_first_loses
- \+ *lemma* pgame.impartial_not_first_wins

Modified src/set_theory/game/nim.lean
- \+/\- *lemma* nim.nim_def
- \+/\- *lemma* nim.nim_zero_first_loses

Modified src/set_theory/game/winner.lean
- \+ *lemma* pgame.not_first_loses_of_first_wins
- \+ *lemma* pgame.not_first_wins_of_first_loses



## [2020-08-25 14:36:40](https://github.com/leanprover-community/mathlib/commit/878c44f)
feat(category_theory/adjunction): restrict adjunction to full subcategory ([#3924](https://github.com/leanprover-community/mathlib/pull/3924))
Blocked by [#3923](https://github.com/leanprover-community/mathlib/pull/3923).
#### Estimated changes
Modified src/category_theory/adjunction/fully_faithful.lean
- \+ *def* category_theory.adjunction.restrict_fully_faithful



## [2020-08-25 13:04:30](https://github.com/leanprover-community/mathlib/commit/a5a9858)
feat(data/sigma/basic): cleanup ([#3933](https://github.com/leanprover-community/mathlib/pull/3933))
Use namespaces
Add `sigma.ext_iff`, `psigma.ext` and `sigma.ext_iff`
#### Estimated changes
Modified src/data/pfunctor/multivariate/basic.lean


Modified src/data/sigma/basic.lean
- \+/\- *def* psigma.elim
- \+/\- *theorem* psigma.elim_val
- \+ *lemma* psigma.ext
- \+ *lemma* psigma.ext_iff
- \+/\- *def* psigma.map
- \+/\- *theorem* psigma.mk.inj_iff
- \+/\- *theorem* sigma.eta
- \- *theorem* sigma.exists
- \+/\- *lemma* sigma.ext
- \+ *lemma* sigma.ext_iff
- \- *theorem* sigma.forall
- \+/\- *def* sigma.map
- \+/\- *theorem* sigma.mk.inj_iff
- \+ *theorem* sigma.«exists»
- \+ *theorem* sigma.«forall»



## [2020-08-25 12:10:39](https://github.com/leanprover-community/mathlib/commit/3409388)
doc(ring_theory/*): add some module docstrings ([#3880](https://github.com/leanprover-community/mathlib/pull/3880))
#### Estimated changes
Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/algebra_operations.lean


Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/free_comm_ring.lean
- \+/\- *lemma* free_comm_ring.coe_lift_hom
- \+/\- *def* free_comm_ring.lift
- \+/\- *lemma* free_comm_ring.lift_comp_of
- \+/\- *def* free_comm_ring.lift_hom
- \+/\- *lemma* free_comm_ring.lift_hom_comp_of

Modified src/ring_theory/free_ring.lean
- \+/\- *def* free_ring.lift
- \+/\- *lemma* free_ring.lift_comp_of
- \+/\- *def* free_ring.lift_hom

Modified src/ring_theory/integral_closure.lean




## [2020-08-24 23:25:19](https://github.com/leanprover-community/mathlib/commit/d4d33de)
feat(combinatorics): define simple graphs ([#3458](https://github.com/leanprover-community/mathlib/pull/3458))
adds basic definition of `simple_graph`s
#### Estimated changes
Added src/combinatorics/simple_graph.lean
- \+ *def* complete_graph
- \+ *lemma* simple_graph.adj_iff_exists_edge
- \+ *lemma* simple_graph.card_neighbor_set_eq_degree
- \+ *lemma* simple_graph.complete_graph_degree
- \+ *lemma* simple_graph.complete_graph_is_regular
- \+ *def* simple_graph.degree
- \+ *def* simple_graph.edge_finset
- \+ *lemma* simple_graph.edge_other_ne
- \+ *def* simple_graph.edge_set
- \+ *lemma* simple_graph.edge_symm
- \+ *lemma* simple_graph.irrefl
- \+ *def* simple_graph.is_regular_of_degree
- \+ *def* simple_graph.locally_finite
- \+ *lemma* simple_graph.mem_edge_finset
- \+ *lemma* simple_graph.mem_edge_set
- \+ *lemma* simple_graph.mem_neighbor_finset
- \+ *lemma* simple_graph.mem_neighbor_set
- \+ *lemma* simple_graph.ne_of_adj
- \+ *def* simple_graph.neighbor_finset
- \+ *lemma* simple_graph.neighbor_finset_eq_filter
- \+ *def* simple_graph.neighbor_set
- \+ *structure* simple_graph

Modified src/data/sym2.lean
- \+ *lemma* sym2.elems_iff_eq
- \+/\- *lemma* sym2.mem_iff
- \+ *lemma* sym2.mk_has_mem_right
- \+/\- *inductive* sym2.rel
- \+ *def* sym2.rel_bool
- \+ *lemma* sym2.rel_bool_spec
- \+/\- *def* sym2



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
- \- *def* affine.simplex.altitude
- \- *lemma* affine.simplex.altitude_def
- \- *lemma* affine.simplex.centroid_eq_affine_combination_of_points_with_circumcenter
- \- *def* affine.simplex.centroid_weights_with_circumcenter
- \- *def* affine.simplex.circumcenter
- \- *def* affine.simplex.circumcenter_circumradius
- \- *lemma* affine.simplex.circumcenter_circumradius_unique_dist_eq
- \- *lemma* affine.simplex.circumcenter_eq_affine_combination_of_points_with_circumcenter
- \- *lemma* affine.simplex.circumcenter_mem_affine_span
- \- *def* affine.simplex.circumcenter_weights_with_circumcenter
- \- *def* affine.simplex.circumradius
- \- *lemma* affine.simplex.direction_monge_plane
- \- *lemma* affine.simplex.dist_circumcenter_eq_circumradius'
- \- *lemma* affine.simplex.dist_circumcenter_eq_circumradius
- \- *lemma* affine.simplex.eq_circumcenter_of_dist_eq
- \- *lemma* affine.simplex.eq_circumradius_of_dist_eq
- \- *lemma* affine.simplex.eq_monge_point_of_forall_mem_monge_plane
- \- *lemma* affine.simplex.inner_monge_point_vsub_face_centroid_vsub
- \- *def* affine.simplex.monge_plane
- \- *lemma* affine.simplex.monge_plane_comm
- \- *lemma* affine.simplex.monge_plane_def
- \- *def* affine.simplex.monge_point
- \- *lemma* affine.simplex.monge_point_eq_affine_combination_of_points_with_circumcenter
- \- *lemma* affine.simplex.monge_point_eq_smul_vsub_vadd_circumcenter
- \- *lemma* affine.simplex.monge_point_mem_affine_span
- \- *lemma* affine.simplex.monge_point_mem_monge_plane
- \- *lemma* affine.simplex.monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter
- \- *def* affine.simplex.monge_point_vsub_face_centroid_weights_with_circumcenter
- \- *lemma* affine.simplex.monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub
- \- *def* affine.simplex.monge_point_weights_with_circumcenter
- \- *lemma* affine.simplex.point_eq_affine_combination_of_points_with_circumcenter
- \- *def* affine.simplex.point_index_embedding
- \- *def* affine.simplex.point_weights_with_circumcenter
- \- *def* affine.simplex.points_with_circumcenter
- \- *lemma* affine.simplex.points_with_circumcenter_eq_circumcenter
- \- *inductive* affine.simplex.points_with_circumcenter_index
- \- *lemma* affine.simplex.points_with_circumcenter_point
- \- *lemma* affine.simplex.sum_centroid_weights_with_circumcenter
- \- *lemma* affine.simplex.sum_circumcenter_weights_with_circumcenter
- \- *lemma* affine.simplex.sum_monge_point_vsub_face_centroid_weights_with_circumcenter
- \- *lemma* affine.simplex.sum_monge_point_weights_with_circumcenter
- \- *lemma* affine.simplex.sum_point_weights_with_circumcenter
- \- *lemma* affine.simplex.sum_points_with_circumcenter
- \- *lemma* affine.triangle.altitude_eq_monge_plane
- \- *lemma* affine.triangle.eq_orthocenter_of_forall_mem_altitude
- \- *def* affine.triangle.orthocenter
- \- *lemma* affine.triangle.orthocenter_eq_monge_point
- \- *lemma* affine.triangle.orthocenter_eq_smul_vsub_vadd_circumcenter
- \- *lemma* affine.triangle.orthocenter_mem_affine_span
- \- *lemma* affine.triangle.orthocenter_mem_altitude
- \- *def* euclidean_geometry.angle
- \- *lemma* euclidean_geometry.angle_add_angle_add_angle_eq_pi
- \- *lemma* euclidean_geometry.angle_add_angle_eq_pi_of_angle_eq_pi
- \- *lemma* euclidean_geometry.angle_comm
- \- *lemma* euclidean_geometry.angle_eq_angle_of_angle_eq_pi
- \- *lemma* euclidean_geometry.angle_eq_angle_of_dist_eq
- \- *lemma* euclidean_geometry.angle_eq_left
- \- *lemma* euclidean_geometry.angle_eq_of_ne
- \- *lemma* euclidean_geometry.angle_eq_right
- \- *lemma* euclidean_geometry.angle_eq_zero_of_angle_eq_pi_left
- \- *lemma* euclidean_geometry.angle_eq_zero_of_angle_eq_pi_right
- \- *lemma* euclidean_geometry.angle_le_pi
- \- *lemma* euclidean_geometry.angle_nonneg
- \- *lemma* euclidean_geometry.dist_affine_combination
- \- *lemma* euclidean_geometry.dist_eq_iff_dist_orthogonal_projection_eq
- \- *lemma* euclidean_geometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi
- \- *lemma* euclidean_geometry.dist_orthogonal_projection_eq_zero_iff
- \- *lemma* euclidean_geometry.dist_orthogonal_projection_ne_zero_of_not_mem
- \- *lemma* euclidean_geometry.dist_set_eq_iff_dist_orthogonal_projection_eq
- \- *lemma* euclidean_geometry.dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
- \- *lemma* euclidean_geometry.dist_square_eq_dist_square_add_dist_square_iff_angle_eq_pi_div_two
- \- *lemma* euclidean_geometry.dist_square_eq_dist_square_add_dist_square_sub_two_mul_dist_mul_dist_mul_cos_angle
- \- *lemma* euclidean_geometry.dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd
- \- *lemma* euclidean_geometry.exists_dist_eq_iff_exists_dist_orthogonal_projection_eq
- \- *lemma* euclidean_geometry.exists_unique_dist_eq_of_affine_independent
- \- *lemma* euclidean_geometry.exists_unique_dist_eq_of_insert
- \- *lemma* euclidean_geometry.inner_weighted_vsub
- \- *lemma* euclidean_geometry.inter_eq_singleton_orthogonal_projection
- \- *lemma* euclidean_geometry.inter_eq_singleton_orthogonal_projection_fn
- \- *def* euclidean_geometry.orthogonal_projection
- \- *lemma* euclidean_geometry.orthogonal_projection_eq_self_iff
- \- *def* euclidean_geometry.orthogonal_projection_fn
- \- *lemma* euclidean_geometry.orthogonal_projection_fn_eq
- \- *lemma* euclidean_geometry.orthogonal_projection_fn_mem
- \- *lemma* euclidean_geometry.orthogonal_projection_fn_mem_orthogonal
- \- *lemma* euclidean_geometry.orthogonal_projection_fn_vsub_mem_direction_orthogonal
- \- *lemma* euclidean_geometry.orthogonal_projection_mem
- \- *lemma* euclidean_geometry.orthogonal_projection_mem_orthogonal
- \- *lemma* euclidean_geometry.orthogonal_projection_vadd_eq_self
- \- *lemma* euclidean_geometry.orthogonal_projection_vadd_smul_vsub_orthogonal_projection
- \- *lemma* euclidean_geometry.orthogonal_projection_vsub_mem_direction
- \- *lemma* euclidean_geometry.orthogonal_projection_vsub_mem_direction_orthogonal
- \- *lemma* euclidean_geometry.vsub_orthogonal_projection_mem_direction
- \- *lemma* euclidean_geometry.vsub_orthogonal_projection_mem_direction_orthogonal
- \- *def* inner_product_geometry.angle
- \- *lemma* inner_product_geometry.angle_add_angle_eq_pi_of_angle_eq_pi
- \- *lemma* inner_product_geometry.angle_add_angle_sub_add_angle_sub_eq_pi
- \- *lemma* inner_product_geometry.angle_comm
- \- *lemma* inner_product_geometry.angle_eq_pi_iff
- \- *lemma* inner_product_geometry.angle_eq_zero_iff
- \- *lemma* inner_product_geometry.angle_le_pi
- \- *lemma* inner_product_geometry.angle_neg_left
- \- *lemma* inner_product_geometry.angle_neg_neg
- \- *lemma* inner_product_geometry.angle_neg_right
- \- *lemma* inner_product_geometry.angle_neg_self_of_nonzero
- \- *lemma* inner_product_geometry.angle_nonneg
- \- *lemma* inner_product_geometry.angle_self
- \- *lemma* inner_product_geometry.angle_self_neg_of_nonzero
- \- *lemma* inner_product_geometry.angle_smul_left_of_neg
- \- *lemma* inner_product_geometry.angle_smul_left_of_pos
- \- *lemma* inner_product_geometry.angle_smul_right_of_neg
- \- *lemma* inner_product_geometry.angle_smul_right_of_pos
- \- *lemma* inner_product_geometry.angle_sub_eq_angle_sub_rev_of_norm_eq
- \- *lemma* inner_product_geometry.angle_zero_left
- \- *lemma* inner_product_geometry.angle_zero_right
- \- *lemma* inner_product_geometry.cos_angle
- \- *lemma* inner_product_geometry.cos_angle_add_angle_sub_add_angle_sub_eq_neg_one
- \- *lemma* inner_product_geometry.cos_angle_mul_norm_mul_norm
- \- *lemma* inner_product_geometry.cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle
- \- *lemma* inner_product_geometry.inner_eq_zero_iff_angle_eq_pi_div_two
- \- *lemma* inner_product_geometry.norm_add_square_eq_norm_square_add_norm_square'
- \- *lemma* inner_product_geometry.norm_add_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two
- \- *lemma* inner_product_geometry.norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi
- \- *lemma* inner_product_geometry.norm_sub_square_eq_norm_square_add_norm_square'
- \- *lemma* inner_product_geometry.norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two
- \- *lemma* inner_product_geometry.norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_cos_angle
- \- *lemma* inner_product_geometry.sin_angle_add_angle_sub_add_angle_sub_eq_zero
- \- *lemma* inner_product_geometry.sin_angle_mul_norm_mul_norm
- \- *lemma* inner_product_geometry.sin_angle_sub_add_angle_sub_rev_eq_sin_angle

Added src/geometry/euclidean/basic.lean
- \+ *def* euclidean_geometry.angle
- \+ *lemma* euclidean_geometry.angle_add_angle_eq_pi_of_angle_eq_pi
- \+ *lemma* euclidean_geometry.angle_comm
- \+ *lemma* euclidean_geometry.angle_eq_angle_of_angle_eq_pi
- \+ *lemma* euclidean_geometry.angle_eq_left
- \+ *lemma* euclidean_geometry.angle_eq_of_ne
- \+ *lemma* euclidean_geometry.angle_eq_right
- \+ *lemma* euclidean_geometry.angle_eq_zero_of_angle_eq_pi_left
- \+ *lemma* euclidean_geometry.angle_eq_zero_of_angle_eq_pi_right
- \+ *lemma* euclidean_geometry.angle_le_pi
- \+ *lemma* euclidean_geometry.angle_nonneg
- \+ *lemma* euclidean_geometry.dist_affine_combination
- \+ *lemma* euclidean_geometry.dist_orthogonal_projection_eq_zero_iff
- \+ *lemma* euclidean_geometry.dist_orthogonal_projection_ne_zero_of_not_mem
- \+ *lemma* euclidean_geometry.dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
- \+ *lemma* euclidean_geometry.dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd
- \+ *lemma* euclidean_geometry.inner_weighted_vsub
- \+ *lemma* euclidean_geometry.inter_eq_singleton_orthogonal_projection
- \+ *lemma* euclidean_geometry.inter_eq_singleton_orthogonal_projection_fn
- \+ *def* euclidean_geometry.orthogonal_projection
- \+ *lemma* euclidean_geometry.orthogonal_projection_eq_self_iff
- \+ *def* euclidean_geometry.orthogonal_projection_fn
- \+ *lemma* euclidean_geometry.orthogonal_projection_fn_eq
- \+ *lemma* euclidean_geometry.orthogonal_projection_fn_mem
- \+ *lemma* euclidean_geometry.orthogonal_projection_fn_mem_orthogonal
- \+ *lemma* euclidean_geometry.orthogonal_projection_fn_vsub_mem_direction_orthogonal
- \+ *lemma* euclidean_geometry.orthogonal_projection_mem
- \+ *lemma* euclidean_geometry.orthogonal_projection_mem_orthogonal
- \+ *lemma* euclidean_geometry.orthogonal_projection_vadd_eq_self
- \+ *lemma* euclidean_geometry.orthogonal_projection_vadd_smul_vsub_orthogonal_projection
- \+ *lemma* euclidean_geometry.orthogonal_projection_vsub_mem_direction
- \+ *lemma* euclidean_geometry.orthogonal_projection_vsub_mem_direction_orthogonal
- \+ *lemma* euclidean_geometry.vsub_orthogonal_projection_mem_direction
- \+ *lemma* euclidean_geometry.vsub_orthogonal_projection_mem_direction_orthogonal
- \+ *def* inner_product_geometry.angle
- \+ *lemma* inner_product_geometry.angle_add_angle_eq_pi_of_angle_eq_pi
- \+ *lemma* inner_product_geometry.angle_comm
- \+ *lemma* inner_product_geometry.angle_eq_pi_iff
- \+ *lemma* inner_product_geometry.angle_eq_zero_iff
- \+ *lemma* inner_product_geometry.angle_le_pi
- \+ *lemma* inner_product_geometry.angle_neg_left
- \+ *lemma* inner_product_geometry.angle_neg_neg
- \+ *lemma* inner_product_geometry.angle_neg_right
- \+ *lemma* inner_product_geometry.angle_neg_self_of_nonzero
- \+ *lemma* inner_product_geometry.angle_nonneg
- \+ *lemma* inner_product_geometry.angle_self
- \+ *lemma* inner_product_geometry.angle_self_neg_of_nonzero
- \+ *lemma* inner_product_geometry.angle_smul_left_of_neg
- \+ *lemma* inner_product_geometry.angle_smul_left_of_pos
- \+ *lemma* inner_product_geometry.angle_smul_right_of_neg
- \+ *lemma* inner_product_geometry.angle_smul_right_of_pos
- \+ *lemma* inner_product_geometry.angle_zero_left
- \+ *lemma* inner_product_geometry.angle_zero_right
- \+ *lemma* inner_product_geometry.cos_angle
- \+ *lemma* inner_product_geometry.cos_angle_mul_norm_mul_norm
- \+ *lemma* inner_product_geometry.inner_eq_zero_iff_angle_eq_pi_div_two
- \+ *lemma* inner_product_geometry.sin_angle_mul_norm_mul_norm

Added src/geometry/euclidean/circumcenter.lean
- \+ *lemma* affine.simplex.centroid_eq_affine_combination_of_points_with_circumcenter
- \+ *def* affine.simplex.centroid_weights_with_circumcenter
- \+ *def* affine.simplex.circumcenter
- \+ *def* affine.simplex.circumcenter_circumradius
- \+ *lemma* affine.simplex.circumcenter_circumradius_unique_dist_eq
- \+ *lemma* affine.simplex.circumcenter_eq_affine_combination_of_points_with_circumcenter
- \+ *lemma* affine.simplex.circumcenter_mem_affine_span
- \+ *def* affine.simplex.circumcenter_weights_with_circumcenter
- \+ *def* affine.simplex.circumradius
- \+ *lemma* affine.simplex.dist_circumcenter_eq_circumradius'
- \+ *lemma* affine.simplex.dist_circumcenter_eq_circumradius
- \+ *lemma* affine.simplex.eq_circumcenter_of_dist_eq
- \+ *lemma* affine.simplex.eq_circumradius_of_dist_eq
- \+ *lemma* affine.simplex.point_eq_affine_combination_of_points_with_circumcenter
- \+ *def* affine.simplex.point_index_embedding
- \+ *def* affine.simplex.point_weights_with_circumcenter
- \+ *def* affine.simplex.points_with_circumcenter
- \+ *lemma* affine.simplex.points_with_circumcenter_eq_circumcenter
- \+ *inductive* affine.simplex.points_with_circumcenter_index
- \+ *lemma* affine.simplex.points_with_circumcenter_point
- \+ *lemma* affine.simplex.sum_centroid_weights_with_circumcenter
- \+ *lemma* affine.simplex.sum_circumcenter_weights_with_circumcenter
- \+ *lemma* affine.simplex.sum_point_weights_with_circumcenter
- \+ *lemma* affine.simplex.sum_points_with_circumcenter
- \+ *lemma* euclidean_geometry.dist_eq_iff_dist_orthogonal_projection_eq
- \+ *lemma* euclidean_geometry.dist_set_eq_iff_dist_orthogonal_projection_eq
- \+ *lemma* euclidean_geometry.exists_dist_eq_iff_exists_dist_orthogonal_projection_eq
- \+ *lemma* euclidean_geometry.exists_unique_dist_eq_of_affine_independent
- \+ *lemma* euclidean_geometry.exists_unique_dist_eq_of_insert

Added src/geometry/euclidean/default.lean


Added src/geometry/euclidean/monge_point.lean
- \+ *def* affine.simplex.altitude
- \+ *lemma* affine.simplex.altitude_def
- \+ *lemma* affine.simplex.direction_monge_plane
- \+ *lemma* affine.simplex.eq_monge_point_of_forall_mem_monge_plane
- \+ *lemma* affine.simplex.inner_monge_point_vsub_face_centroid_vsub
- \+ *def* affine.simplex.monge_plane
- \+ *lemma* affine.simplex.monge_plane_comm
- \+ *lemma* affine.simplex.monge_plane_def
- \+ *def* affine.simplex.monge_point
- \+ *lemma* affine.simplex.monge_point_eq_affine_combination_of_points_with_circumcenter
- \+ *lemma* affine.simplex.monge_point_eq_smul_vsub_vadd_circumcenter
- \+ *lemma* affine.simplex.monge_point_mem_affine_span
- \+ *lemma* affine.simplex.monge_point_mem_monge_plane
- \+ *lemma* affine.simplex.monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter
- \+ *def* affine.simplex.monge_point_vsub_face_centroid_weights_with_circumcenter
- \+ *lemma* affine.simplex.monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub
- \+ *def* affine.simplex.monge_point_weights_with_circumcenter
- \+ *lemma* affine.simplex.sum_monge_point_vsub_face_centroid_weights_with_circumcenter
- \+ *lemma* affine.simplex.sum_monge_point_weights_with_circumcenter
- \+ *lemma* affine.triangle.altitude_eq_monge_plane
- \+ *lemma* affine.triangle.eq_orthocenter_of_forall_mem_altitude
- \+ *def* affine.triangle.orthocenter
- \+ *lemma* affine.triangle.orthocenter_eq_monge_point
- \+ *lemma* affine.triangle.orthocenter_eq_smul_vsub_vadd_circumcenter
- \+ *lemma* affine.triangle.orthocenter_mem_affine_span
- \+ *lemma* affine.triangle.orthocenter_mem_altitude

Added src/geometry/euclidean/triangle.lean
- \+ *lemma* euclidean_geometry.angle_add_angle_add_angle_eq_pi
- \+ *lemma* euclidean_geometry.angle_eq_angle_of_dist_eq
- \+ *lemma* euclidean_geometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi
- \+ *lemma* euclidean_geometry.dist_square_eq_dist_square_add_dist_square_iff_angle_eq_pi_div_two
- \+ *lemma* euclidean_geometry.dist_square_eq_dist_square_add_dist_square_sub_two_mul_dist_mul_dist_mul_cos_angle
- \+ *lemma* inner_product_geometry.angle_add_angle_sub_add_angle_sub_eq_pi
- \+ *lemma* inner_product_geometry.angle_sub_eq_angle_sub_rev_of_norm_eq
- \+ *lemma* inner_product_geometry.cos_angle_add_angle_sub_add_angle_sub_eq_neg_one
- \+ *lemma* inner_product_geometry.cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle
- \+ *lemma* inner_product_geometry.norm_add_square_eq_norm_square_add_norm_square'
- \+ *lemma* inner_product_geometry.norm_add_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two
- \+ *lemma* inner_product_geometry.norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi
- \+ *lemma* inner_product_geometry.norm_sub_square_eq_norm_square_add_norm_square'
- \+ *lemma* inner_product_geometry.norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two
- \+ *lemma* inner_product_geometry.norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_cos_angle
- \+ *lemma* inner_product_geometry.sin_angle_add_angle_sub_add_angle_sub_eq_zero
- \+ *lemma* inner_product_geometry.sin_angle_sub_add_angle_sub_rev_eq_sin_angle



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
- \+ *lemma* nim.Grundy_value_nim
- \+ *lemma* nim.equiv_nim_iff_Grundy_value_eq
- \+ *lemma* nim.nim_equiv_iff_eq



## [2020-08-24 01:55:42](https://github.com/leanprover-community/mathlib/commit/1ccdbb9)
feat(category_theory/images): unique image ([#3921](https://github.com/leanprover-community/mathlib/pull/3921))
Show that the strong-epi mono factorisation of a morphism is unique.
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean
- \+ *def* category_theory.limits.image.iso_strong_epi_mono
- \+ *lemma* category_theory.limits.image.iso_strong_epi_mono_hom_comp_ι
- \+ *lemma* category_theory.limits.image.iso_strong_epi_mono_inv_comp_mono



## [2020-08-24 01:55:40](https://github.com/leanprover-community/mathlib/commit/685d9dd)
feat(category_theory): cancel fully faithful functor ([#3920](https://github.com/leanprover-community/mathlib/pull/3920))
Construct the natural isomorphism between `F` and `G` given a natural iso between `F ⋙ H` and `G ⋙ H` for a fully faithful `H`.
#### Estimated changes
Modified src/category_theory/fully_faithful.lean
- \+ *def* category_theory.fully_faithful_cancel_right
- \+ *lemma* category_theory.fully_faithful_cancel_right_hom_app
- \+ *lemma* category_theory.fully_faithful_cancel_right_inv_app



## [2020-08-24 01:00:11](https://github.com/leanprover-community/mathlib/commit/ebd3351)
chore(category_theory/conj): add a new simp lemma ([#3922](https://github.com/leanprover-community/mathlib/pull/3922))
Mark a new simp lemma which I think is helpful and simplify some proofs using it.
#### Estimated changes
Modified src/category_theory/conj.lean




## [2020-08-24 01:00:09](https://github.com/leanprover-community/mathlib/commit/f230409)
feat(category_theory/adjunction): opposite adjunctions ([#3899](https://github.com/leanprover-community/mathlib/pull/3899))
Add two constructions for adjoints for opposite functors.
#### Estimated changes
Added src/category_theory/adjunction/opposites.lean
- \+ *def* adjunction.adjoint_of_op_adjoint_op
- \+ *def* adjunction.adjoint_of_unop_adjoint_unop
- \+ *def* adjunction.adjoint_op_of_adjoint_unop
- \+ *def* adjunction.adjoint_unop_of_adjoint_op
- \+ *def* adjunction.op_adjoint_of_unop_adjoint
- \+ *def* adjunction.op_adjoint_op_of_adjoint
- \+ *def* adjunction.unop_adjoint_of_op_adjoint
- \+ *def* adjunction.unop_adjoint_unop_of_adjoint

Modified src/category_theory/opposites.lean
- \+ *def* category_theory.op_equiv
- \+ *lemma* category_theory.op_equiv_apply
- \+ *lemma* category_theory.op_equiv_symm_apply



## [2020-08-24 01:00:07](https://github.com/leanprover-community/mathlib/commit/bfc8c66)
feat(category_theory/limits/shapes/finite*): finite limits from limits ([#3800](https://github.com/leanprover-community/mathlib/pull/3800))
Add some missing derivations in the new has_limits hierarchy
#### Estimated changes
Modified src/category_theory/limits/shapes/finite_limits.lean
- \+ *def* category_theory.limits.has_finite_colimits_of_has_colimits
- \+ *def* category_theory.limits.has_finite_limits_of_has_limits

Modified src/category_theory/limits/shapes/finite_products.lean
- \+ *def* category_theory.limits.has_finite_coproducts_of_has_finite_colimits
- \+ *def* category_theory.limits.has_finite_products_of_has_finite_limits



## [2020-08-23 23:56:34](https://github.com/leanprover-community/mathlib/commit/bf6cd28)
feat(category_theory/fully_faithful): equivalence of homsets ([#3923](https://github.com/leanprover-community/mathlib/pull/3923))
I was *so sure* I'd already made this PR but I can't find it nor this construction, so here it is.
#### Estimated changes
Modified src/category_theory/fully_faithful.lean
- \+ *def* category_theory.equiv_of_fully_faithful
- \+ *lemma* category_theory.equiv_of_fully_faithful_apply
- \+ *lemma* category_theory.equiv_of_fully_faithful_symm_apply



## [2020-08-23 16:22:06](https://github.com/leanprover-community/mathlib/commit/7d4f773)
feat(ring_theory/jacobson): Proof that if a ring is a Jacobson Ring then so is its localization at a single element ([#3651](https://github.com/leanprover-community/mathlib/pull/3651))
The main result here is that the localization of a Jacobson ring to a single element is also a Jacobson ring, which is one of the things needed for the proof that `R` is Jacobson if and only if `R[x]` is Jacobson.
Two characterization of Jacobson rings in terms of their quotient rings are also included, again needed to prove `R[x]` is Jacobson.
#### Estimated changes
Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* submonoid.mem_closure_singleton_self

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.quotient.mk_surjective

Modified src/order/complete_lattice.lean
- \+ *theorem* Inf_le_Inf_of_subset_insert_top
- \+ *theorem* Sup_le_Sup_of_subset_instert_bot

Modified src/ring_theory/ideal/basic.lean
- \+ *theorem* ideal.mul_unit_mem_iff_mem
- \+ *theorem* ideal.unit_mul_mem_iff_mem

Modified src/ring_theory/ideal/operations.lean
- \- *theorem* ideal.comap.is_maximal
- \+ *lemma* ideal.comap_Inf'
- \+ *theorem* ideal.comap_is_maximal_of_surjective
- \+ *theorem* ideal.comap_is_prime
- \+ *theorem* ideal.map_is_prime_of_surjective
- \+ *theorem* ideal.map_radical_of_surjective
- \+ *lemma* ideal.mk_ker
- \+ *lemma* ring_hom.ker_eq_comap_bot

Modified src/ring_theory/jacobson.lean
- \+ *lemma* ideal.disjoint_closure_singleton_iff_not_mem
- \+ *lemma* ideal.is_jacobson_iff_Inf_maximal'
- \+ *lemma* ideal.is_jacobson_localization
- \+ *lemma* ideal.is_maximal_iff_is_maximal_disjoint
- \+ *lemma* ideal.is_maximal_of_is_maximal_disjoint
- \+ *def* ideal.order_iso_of_maximal

Modified src/ring_theory/jacobson_ideal.lean
- \+ *theorem* ideal.comap_jacobson_of_surjective
- \+ *theorem* ideal.eq_jacobson_iff_Inf_maximal'
- \+ *theorem* ideal.eq_jacobson_iff_Inf_maximal
- \+ *lemma* ideal.eq_jacobson_iff_not_mem
- \+ *lemma* ideal.eq_radical_of_eq_jacobson
- \- *lemma* ideal.jacobson.is_maximal
- \+ *theorem* ideal.jacobson_eq_iff_jacobson_quotient_eq_bot
- \+ *lemma* ideal.jacobson_eq_self_of_is_maximal
- \+ *theorem* ideal.map_jacobson_of_surjective
- \+ *theorem* ideal.radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot
- \+ *lemma* ideal.radical_le_jacobson

Modified src/ring_theory/localization.lean
- \+ *theorem* localization_map.comap_map_of_is_prime_disjoint
- \+ *lemma* localization_map.is_prime_iff_is_prime_disjoint
- \+ *lemma* localization_map.is_prime_of_is_prime_disjoint
- \+ *theorem* localization_map.mem_map_to_map_iff
- \+ *lemma* localization_map.mk'_mem_iff
- \+ *def* localization_map.order_iso_of_prime



## [2020-08-23 15:35:50](https://github.com/leanprover-community/mathlib/commit/e216755)
feat(linear_algebra/affine_space): more lemmas ([#3918](https://github.com/leanprover-community/mathlib/pull/3918))
Add some more affine space lemmas.  In particular, this includes
lemmas about the dimension of the span of a finite affinely
independent family.
#### Estimated changes
Modified src/linear_algebra/affine_space/basic.lean
- \+ *lemma* affine_subspace.direction_eq_top_iff_of_nonempty

Modified src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one
- \+ *lemma* findim_vector_span_of_affine_independent
- \+ *lemma* vector_span_eq_top_of_affine_independent_of_card_eq_findim_add_one

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_independent_set_of_affine_independent
- \+ *lemma* injective_of_affine_independent



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
- \+ *def* affine.simplex.altitude
- \+ *lemma* affine.simplex.altitude_def
- \+ *lemma* affine.simplex.centroid_eq_affine_combination_of_points_with_circumcenter
- \+ *def* affine.simplex.centroid_weights_with_circumcenter
- \+ *lemma* affine.simplex.circumcenter_eq_affine_combination_of_points_with_circumcenter
- \+ *def* affine.simplex.circumcenter_weights_with_circumcenter
- \+ *lemma* affine.simplex.direction_monge_plane
- \+ *lemma* affine.simplex.eq_monge_point_of_forall_mem_monge_plane
- \+ *lemma* affine.simplex.inner_monge_point_vsub_face_centroid_vsub
- \+ *def* affine.simplex.monge_plane
- \+ *lemma* affine.simplex.monge_plane_comm
- \+ *lemma* affine.simplex.monge_plane_def
- \+ *def* affine.simplex.monge_point
- \+ *lemma* affine.simplex.monge_point_eq_affine_combination_of_points_with_circumcenter
- \+ *lemma* affine.simplex.monge_point_eq_smul_vsub_vadd_circumcenter
- \+ *lemma* affine.simplex.monge_point_mem_affine_span
- \+ *lemma* affine.simplex.monge_point_mem_monge_plane
- \+ *lemma* affine.simplex.monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter
- \+ *def* affine.simplex.monge_point_vsub_face_centroid_weights_with_circumcenter
- \+ *lemma* affine.simplex.monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub
- \+ *def* affine.simplex.monge_point_weights_with_circumcenter
- \+ *lemma* affine.simplex.point_eq_affine_combination_of_points_with_circumcenter
- \+ *def* affine.simplex.point_index_embedding
- \+ *def* affine.simplex.point_weights_with_circumcenter
- \+ *def* affine.simplex.points_with_circumcenter
- \+ *lemma* affine.simplex.points_with_circumcenter_eq_circumcenter
- \+ *inductive* affine.simplex.points_with_circumcenter_index
- \+ *lemma* affine.simplex.points_with_circumcenter_point
- \+ *lemma* affine.simplex.sum_centroid_weights_with_circumcenter
- \+ *lemma* affine.simplex.sum_circumcenter_weights_with_circumcenter
- \+ *lemma* affine.simplex.sum_monge_point_vsub_face_centroid_weights_with_circumcenter
- \+ *lemma* affine.simplex.sum_monge_point_weights_with_circumcenter
- \+ *lemma* affine.simplex.sum_point_weights_with_circumcenter
- \+ *lemma* affine.simplex.sum_points_with_circumcenter
- \+ *lemma* affine.triangle.altitude_eq_monge_plane
- \+ *lemma* affine.triangle.eq_orthocenter_of_forall_mem_altitude
- \+ *def* affine.triangle.orthocenter
- \+ *lemma* affine.triangle.orthocenter_eq_monge_point
- \+ *lemma* affine.triangle.orthocenter_eq_smul_vsub_vadd_circumcenter
- \+ *lemma* affine.triangle.orthocenter_mem_affine_span
- \+ *lemma* affine.triangle.orthocenter_mem_altitude



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


Added src/tactic/binder_matching.lean


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
- \- *lemma* ext
- \+ *lemma* sigma.ext



## [2020-08-23 05:18:43](https://github.com/leanprover-community/mathlib/commit/ff97055)
feat(data/finset/basic): insert_singleton_comm ([#3914](https://github.com/leanprover-community/mathlib/pull/3914))
Add the result that `({a, b} : finset α) = {b, a}`.  This came up in
[#3872](https://github.com/leanprover-community/mathlib/pull/3872), and `library_search` does not show it as already present.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* finset.insert_singleton_comm



## [2020-08-23 02:34:47](https://github.com/leanprover-community/mathlib/commit/7ac7246)
feat(linear_algebra/finite_dimensional): Add `linear_equiv.of_inj_endo` and related lemmas ([#3878](https://github.com/leanprover-community/mathlib/pull/3878))
This PR prepares [#3864](https://github.com/leanprover-community/mathlib/pull/3864).
* Move the section `zero_dim` up.
* Add several lemmas about finite dimensional vector spaces. The only new definition is `linear_equiv.of_injective_endo`, which produces a linear equivalence from an injective endomorphism.
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *lemma* linear_independent_le_dim

Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* findim_bot
- \+ *lemma* finite_dimensional.lt_omega_of_linear_independent
- \+ *lemma* linear_equiv.of_injective_endo_left_inv
- \+ *lemma* linear_equiv.of_injective_endo_right_inv
- \+ *lemma* linear_equiv.of_injective_endo_to_fun
- \+ *lemma* linear_map.is_unit_iff
- \+ *lemma* submodule.eq_top_of_disjoint



## [2020-08-22 18:09:38](https://github.com/leanprover-community/mathlib/commit/abe4459)
feat(analysis/convex): define concavity of functions ([#3849](https://github.com/leanprover-community/mathlib/pull/3849))
#### Estimated changes
Modified src/algebra/module/ordered.lean


Modified src/algebra/ordered_group.lean


Modified src/analysis/convex/basic.lean
- \+ *lemma* concave_on.add
- \+ *lemma* concave_on.comp_affine_map
- \+ *lemma* concave_on.comp_linear_map
- \+ *lemma* concave_on.concave_le
- \+ *lemma* concave_on.convex_hypograph
- \+ *lemma* concave_on.convex_lt
- \+ *lemma* concave_on.le_on_segment'
- \+ *lemma* concave_on.le_on_segment
- \+ *lemma* concave_on.smul
- \+ *lemma* concave_on.subset
- \+ *lemma* concave_on.translate_left
- \+ *lemma* concave_on.translate_right
- \+ *def* concave_on
- \+ *lemma* concave_on_const
- \+ *lemma* concave_on_id
- \+ *lemma* concave_on_iff_convex_hypograph
- \+ *lemma* concave_on_iff_div
- \+ *lemma* concave_on_real_of_slope_mono_adjacent
- \+/\- *lemma* convex_on.le_on_segment'
- \+/\- *lemma* convex_on.le_on_segment
- \+ *lemma* linear_order.concave_on_of_lt
- \+ *lemma* neg_concave_on_iff
- \+ *lemma* neg_convex_on_iff

Modified src/analysis/convex/extrema.lean
- \+ *lemma* is_max_on.of_is_local_max_of_convex_univ
- \+ *lemma* is_max_on.of_is_local_max_on_of_concave_on
- \+/\- *lemma* is_min_on.of_is_local_min_of_convex_univ
- \+/\- *lemma* is_min_on.of_is_local_min_on_of_convex_on
- \+/\- *lemma* is_min_on.of_is_local_min_on_of_convex_on_Icc



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
- \+ *lemma* polynomial.eval_prod



## [2020-08-22 13:26:57](https://github.com/leanprover-community/mathlib/commit/aca785a)
feat(linear_algebra): linear_equiv_matrix lemmas ([#3898](https://github.com/leanprover-community/mathlib/pull/3898))
From the sphere eversion project, with help by Anne for the crucial `linear_equiv_matrix_apply`.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *lemma* linear_map.comp_coe
- \+/\- *lemma* linear_map.id_apply
- \+ *lemma* linear_map.id_coe

Modified src/linear_algebra/matrix.lean
- \+/\- *def* linear_equiv_matrix
- \+ *lemma* linear_equiv_matrix_apply'
- \+ *lemma* linear_equiv_matrix_apply
- \+ *lemma* linear_equiv_matrix_id
- \+/\- *theorem* linear_equiv_matrix_range
- \+ *lemma* linear_equiv_matrix_symm_one
- \+ *lemma* matrix.linear_equiv.is_unit_det
- \+ *def* matrix.linear_equiv.of_is_unit_det
- \+/\- *lemma* matrix.linear_equiv_matrix_comp
- \+/\- *lemma* matrix.linear_equiv_matrix_mul
- \+ *lemma* matrix.linear_equiv_matrix_symm_mul



## [2020-08-22 12:32:20](https://github.com/leanprover-community/mathlib/commit/e9d1067)
feat(category_theory/opposites): isomorphism of opposite functor ([#3901](https://github.com/leanprover-community/mathlib/pull/3901))
Get some lemmas generated by `simps` and add two isomorphisms for opposite functors.
#### Estimated changes
Modified src/category_theory/opposites.lean
- \- *lemma* category_theory.functor.left_op_map
- \- *lemma* category_theory.functor.left_op_obj
- \- *lemma* category_theory.functor.op_hom.map_app
- \- *lemma* category_theory.functor.op_hom.obj
- \- *lemma* category_theory.functor.op_inv.map_app
- \- *lemma* category_theory.functor.op_inv.obj
- \- *lemma* category_theory.functor.op_map
- \- *lemma* category_theory.functor.op_obj
- \+ *def* category_theory.functor.op_unop_iso
- \- *lemma* category_theory.functor.right_op_map
- \- *lemma* category_theory.functor.right_op_obj
- \- *lemma* category_theory.functor.unop_map
- \- *lemma* category_theory.functor.unop_obj
- \+ *def* category_theory.functor.unop_op_iso



## [2020-08-22 10:07:23](https://github.com/leanprover-community/mathlib/commit/011a262)
feat(set_theory/game): impartial games and the Sprague-Grundy theorem ([#3855](https://github.com/leanprover-community/mathlib/pull/3855))
#### Estimated changes
Added src/set_theory/game/impartial.lean
- \+ *lemma* pgame.equiv_iff_sum_first_loses
- \+ *lemma* pgame.good_left_move_iff_first_wins
- \+ *lemma* pgame.good_right_move_iff_first_wins
- \+ *def* pgame.impartial
- \+ *lemma* pgame.impartial_add
- \+ *lemma* pgame.impartial_add_self
- \+ *lemma* pgame.impartial_def
- \+ *lemma* pgame.impartial_first_loses_symm'
- \+ *lemma* pgame.impartial_first_loses_symm
- \+ *lemma* pgame.impartial_first_wins_symm'
- \+ *lemma* pgame.impartial_first_wins_symm
- \+ *lemma* pgame.impartial_move_left_impartial
- \+ *lemma* pgame.impartial_move_right_impartial
- \+ *lemma* pgame.impartial_neg
- \+ *lemma* pgame.impartial_neg_equiv_self
- \+ *lemma* pgame.impartial_winner_cases
- \+ *lemma* pgame.no_good_left_moves_iff_first_loses
- \+ *lemma* pgame.no_good_right_moves_iff_first_loses
- \+ *lemma* pgame.zero_impartial

Added src/set_theory/game/nim.lean
- \+ *lemma* nim.Grundy_value_def
- \+ *theorem* nim.Sprague_Grundy
- \+ *lemma* nim.nim_def
- \+ *lemma* nim.nim_impartial
- \+ *lemma* nim.nim_non_zero_first_wins
- \+ *lemma* nim.nim_sum_first_loses_iff_eq
- \+ *lemma* nim.nim_sum_first_wins_iff_neq
- \+ *lemma* nim.nim_wf_lemma
- \+ *lemma* nim.nim_zero_first_loses
- \+ *def* nim.nonmoves
- \+ *lemma* nim.nonmoves_nonempty
- \+ *def* nim
- \+ *def* ordinal.out
- \+ *theorem* ordinal.type_out'

Added src/set_theory/game/winner.lean
- \+ *def* pgame.first_loses
- \+ *lemma* pgame.first_loses_is_zero
- \+ *lemma* pgame.first_loses_of_equiv
- \+ *lemma* pgame.first_loses_of_equiv_iff
- \+ *def* pgame.first_wins
- \+ *lemma* pgame.first_wins_of_equiv
- \+ *lemma* pgame.first_wins_of_equiv_iff
- \+ *def* pgame.left_wins
- \+ *lemma* pgame.left_wins_of_equiv
- \+ *lemma* pgame.left_wins_of_equiv_iff
- \+ *theorem* pgame.omega_left_wins
- \+ *theorem* pgame.one_left_wins
- \+ *def* pgame.right_wins
- \+ *lemma* pgame.right_wins_of_equiv
- \+ *lemma* pgame.right_wins_of_equiv_iff
- \+ *theorem* pgame.star_first_wins
- \+ *lemma* pgame.winner_cases
- \+ *theorem* pgame.zero_first_loses

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


Added src/tactic/dec_trivial.lean


Modified src/tactic/interactive.lean


Added test/dec_trivial_tactic.lean


Added test/revert_target_deps.lean




## [2020-08-22 04:56:48](https://github.com/leanprover-community/mathlib/commit/83db96b)
feat(algebra/group/with_one): make with_one and with_zero irreducible. ([#3883](https://github.com/leanprover-community/mathlib/pull/3883))
#### Estimated changes
Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/algebra/continued_fractions/computation/translations.lean


Modified src/algebra/continued_fractions/convergents_equiv.lean


Modified src/algebra/group/with_one.lean
- \+ *lemma* with_one.coe_mul
- \- *lemma* with_one.mul_coe
- \+ *lemma* with_zero.coe_inv
- \+ *lemma* with_zero.coe_mul
- \- *lemma* with_zero.inv_coe
- \- *lemma* with_zero.mul_coe
- \+ *theorem* with_zero.mul_comm
- \+ *lemma* with_zero.mul_inv_cancel
- \+ *lemma* with_zero.mul_zero
- \+ *lemma* with_zero.zero_mul

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
- \+ *lemma* finset.prod_fin_eq_prod_range
- \+ *lemma* finset.prod_range_eq_prod_fin
- \- *lemma* finset.range_prod_eq_univ_prod

Added src/data/real/golden_ratio.lean
- \+ *lemma* fib_is_sol_fib_rec
- \+ *def* fib_rec
- \+ *lemma* fib_rec_char_poly_eq
- \+ *lemma* geom_gold_conj_is_sol_fib_rec
- \+ *lemma* geom_gold_is_sol_fib_rec
- \+ *lemma* gold_add_gold_conj
- \+ *theorem* gold_conj_irrational
- \+ *lemma* gold_conj_mul_gold
- \+ *lemma* gold_conj_ne_zero
- \+ *lemma* gold_conj_neg
- \+ *lemma* gold_conj_sq
- \+ *theorem* gold_irrational
- \+ *lemma* gold_mul_gold_conj
- \+ *lemma* gold_ne_zero
- \+ *lemma* gold_pos
- \+ *lemma* gold_sq
- \+ *lemma* gold_sub_gold_conj
- \+ *def* golden_conj
- \+ *def* golden_ratio
- \+ *lemma* inv_gold
- \+ *lemma* inv_gold_conj
- \+ *lemma* neg_one_lt_gold_conj
- \+ *lemma* one_lt_gold
- \+ *lemma* one_sub_gold
- \+ *lemma* one_sub_gold_conj
- \+ *theorem* real.coe_fib_eq'
- \+ *theorem* real.coe_fib_eq

Modified src/number_theory/bernoulli.lean




## [2020-08-21 22:13:24](https://github.com/leanprover-community/mathlib/commit/9998bee)
chore(measure_theory/*): remove some `measurable f` arguments ([#3902](https://github.com/leanprover-community/mathlib/pull/3902))
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* measure_theory.integral_add_measure

Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* interval_integral.integral_Iic_sub_Iic
- \+/\- *lemma* interval_integral.integral_add_adjacent_intervals
- \+/\- *lemma* interval_integral.integral_add_adjacent_intervals_cancel
- \+/\- *lemma* interval_integral.integral_interval_add_interval_comm
- \+/\- *lemma* interval_integral.integral_interval_sub_interval_comm'
- \+/\- *lemma* interval_integral.integral_interval_sub_interval_comm
- \+/\- *lemma* interval_integral.integral_interval_sub_left

Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* measure_theory.integral_add_compl



## [2020-08-21 20:49:40](https://github.com/leanprover-community/mathlib/commit/4c04f0b)
feat(topology/algebra/ordered): sum of functions with limits at_top and cst ([#3833](https://github.com/leanprover-community/mathlib/pull/3833))
Two functions which tend to `at_top` have sum tending to `at_top`.  Likewise if one tends to `at_top` and one tends to a constant.
Also made a couple of edits relating to [this conversation](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Ordered.20groups.20have.20no.20top.20element) about `no_top` for algebraic structures:
#### Estimated changes
Modified src/algebra/ordered_field.lean


Modified src/algebra/ordered_ring.lean


Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.tendsto_at_bot_add
- \+ *lemma* filter.tendsto_at_top_add

Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_at_bot_add_tendsto_left
- \+ *lemma* tendsto_at_bot_add_tendsto_right
- \+ *lemma* tendsto_at_top_add_tendsto_left
- \+ *lemma* tendsto_at_top_add_tendsto_right



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
- \+ *lemma* set.empty_pi
- \+ *lemma* set.eval_image_pi
- \+ *lemma* set.eval_image_univ_pi
- \+ *lemma* set.image_compl_preimage
- \+ *lemma* set.image_inter_preimage
- \+ *lemma* set.image_preimage_inter
- \+ *lemma* set.insert_pi
- \+ *lemma* set.mem_pi
- \+ *lemma* set.mem_univ_pi
- \+/\- *def* set.pi
- \- *lemma* set.pi_empty_index
- \+ *lemma* set.pi_eq_empty
- \+ *lemma* set.pi_eq_empty_iff
- \+/\- *lemma* set.pi_if
- \- *lemma* set.pi_insert_index
- \+ *lemma* set.pi_nonempty_iff
- \- *lemma* set.pi_singleton_index
- \+ *lemma* set.singleton_pi
- \+ *lemma* set.subset_pi_eval_image
- \+ *lemma* set.univ_pi_eq_empty
- \+ *lemma* set.univ_pi_eq_empty_iff
- \+ *lemma* set.univ_pi_nonempty_iff
- \+ *lemma* set.update_preimage_pi
- \+ *lemma* set.update_preimage_univ_pi

Modified src/field_theory/chevalley_warning.lean


Modified src/logic/function/basic.lean
- \+ *def* function.eval
- \+ *lemma* function.eval_apply

Modified src/order/filter/basic.lean




## [2020-08-21 18:31:42](https://github.com/leanprover-community/mathlib/commit/0c7ac83)
feat(measure_theory/bochner_integration): add `integral_smul_measure` ([#3900](https://github.com/leanprover-community/mathlib/pull/3900))
Also add `integral_dirac`
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* measure_theory.integral_add_measure
- \+ *lemma* measure_theory.integral_dirac
- \+ *lemma* measure_theory.integral_eq_zero_of_ae
- \+ *lemma* measure_theory.integral_smul_measure

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.ae_add_measure_iff
- \+ *lemma* measure_theory.ae_smul_measure
- \+ *theorem* measure_theory.measure.smul_apply



## [2020-08-21 16:04:55](https://github.com/leanprover-community/mathlib/commit/ac56790)
feat(order/rel_iso): a new definition of order_iso, using preorder instances ([#3838](https://github.com/leanprover-community/mathlib/pull/3838))
defines (new) `order_embedding` and `order_iso`, which map both < and <=
replaces existing `rel_embedding` and `rel_iso` instances preserving < or <= with the new abbreviations
#### Estimated changes
Modified src/data/finsupp/lattice.lean
- \+ *def* finsupp.order_embedding_to_fun
- \+ *lemma* finsupp.order_embedding_to_fun_apply
- \+ *def* finsupp.order_iso_multiset
- \+ *lemma* finsupp.order_iso_multiset_apply
- \+ *lemma* finsupp.order_iso_multiset_symm_apply
- \- *def* finsupp.rel_embedding_to_fun
- \- *lemma* finsupp.rel_embedding_to_fun_apply
- \- *def* finsupp.rel_iso_multiset
- \- *lemma* finsupp.rel_iso_multiset_apply
- \- *lemma* finsupp.rel_iso_multiset_symm_apply

Modified src/data/setoid/basic.lean
- \+/\- *def* setoid.correspondence

Modified src/data/setoid/partition.lean


Modified src/group_theory/congruence.lean
- \+/\- *def* con.correspondence

Modified src/linear_algebra/basic.lean
- \- *def* submodule.comap_mkq.le_rel_embedding
- \- *def* submodule.comap_mkq.lt_rel_embedding
- \+ *def* submodule.comap_mkq.order_embedding
- \- *def* submodule.map_subtype.le_rel_embedding
- \- *def* submodule.map_subtype.lt_rel_embedding
- \+ *def* submodule.map_subtype.order_embedding

Modified src/order/basic.lean


Modified src/order/galois_connection.lean
- \+ *theorem* order_iso.to_galois_connection
- \- *theorem* rel_iso.to_galois_connection

Modified src/order/ord_continuous.lean
- \- *lemma* left_ord_continuous.coe_to_le_rel_embedding
- \- *lemma* left_ord_continuous.coe_to_lt_rel_embedding
- \+ *lemma* left_ord_continuous.coe_to_order_embedding
- \- *def* left_ord_continuous.to_le_rel_embedding
- \- *def* left_ord_continuous.to_lt_rel_embedding
- \+ *def* left_ord_continuous.to_order_embedding
- \- *lemma* right_ord_continuous.coe_to_le_rel_embedding
- \- *lemma* right_ord_continuous.coe_to_lt_rel_embedding
- \+ *lemma* right_ord_continuous.coe_to_order_embedding
- \- *def* right_ord_continuous.to_le_rel_embedding
- \- *def* right_ord_continuous.to_lt_rel_embedding
- \+ *def* right_ord_continuous.to_order_embedding

Modified src/order/rel_iso.lean
- \+/\- *def* fin.val.rel_embedding
- \+/\- *def* fin_fin.rel_embedding
- \+ *def* order_embedding.lt_embedding
- \+ *lemma* order_embedding.lt_embedding_apply
- \+ *theorem* order_embedding.map_le_iff
- \+ *theorem* order_embedding.map_lt_iff
- \+ *def* order_embedding.osymm
- \+ *abbreviation* order_embedding
- \+ *lemma* order_iso.map_bot
- \+ *def* order_iso.osymm
- \+ *abbreviation* order_iso
- \- *def* rel_embedding.lt_embedding_of_le_embedding
- \+ *def* rel_embedding.order_embedding_of_lt_embedding
- \- *lemma* rel_iso.map_bot

Modified src/order/semiconj_Sup.lean


Modified src/ring_theory/ideal/operations.lean
- \- *def* ideal.le_rel_embedding_of_surjective
- \- *def* ideal.lt_rel_embedding_of_surjective
- \+ *def* ideal.order_embedding_of_surjective
- \+/\- *def* ideal.rel_iso_of_bijective

Modified src/ring_theory/localization.lean
- \- *def* localization_map.le_rel_embedding
- \+ *def* localization_map.order_embedding

Modified src/ring_theory/noetherian.lean


Modified src/set_theory/cardinal_ordinal.lean


Modified src/set_theory/ordinal.lean
- \+ *def* cardinal.ord.order_embedding
- \+ *theorem* cardinal.ord.order_embedding_coe
- \- *def* cardinal.ord.rel_embedding
- \- *theorem* cardinal.ord.rel_embedding_coe



## [2020-08-21 13:01:05](https://github.com/leanprover-community/mathlib/commit/e3409c6)
feat(data/zmod/basic): morphisms to zmod are surjective (deps: [#3888](https://github.com/leanprover-community/mathlib/pull/3888)) ([#3889](https://github.com/leanprover-community/mathlib/pull/3889))
... and determined by their kernel
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.ring_hom_eq_of_ker_eq
- \+ *lemma* zmod.ring_hom_surjective

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
Added src/analysis/special_functions/arsinh.lean
- \+ *def* real.arsinh
- \+ *lemma* real.arsinh_sinh
- \+ *lemma* real.sinh_arsinh
- \+ *lemma* real.sinh_bijective
- \+ *lemma* real.sinh_injective
- \+ *lemma* real.sinh_surjective
- \+ *lemma* real.sqrt_one_add_sinh_sq

Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* real.sinh_strict_mono

Modified src/data/complex/exponential.lean
- \+ *lemma* real.cosh_eq
- \+ *lemma* real.cosh_pos
- \+ *lemma* real.cosh_sq_sub_sinh_sq
- \+ *lemma* real.sinh_eq



## [2020-08-21 10:07:49](https://github.com/leanprover-community/mathlib/commit/7a48761)
feat(logic/function): left/right inverse iff ([#3897](https://github.com/leanprover-community/mathlib/pull/3897))
From the sphere eversion project.
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *theorem* function.left_inverse_iff_comp
- \+ *theorem* function.right_inverse_iff_comp



## [2020-08-21 10:07:47](https://github.com/leanprover-community/mathlib/commit/de20a39)
feat(group_theory/subroup,ring_theory/ideal/operations): lift_of_surjective ([#3888](https://github.com/leanprover-community/mathlib/pull/3888))
Surjective homomorphisms behave like quotient maps
#### Estimated changes
Modified src/group_theory/abelianization.lean


Modified src/group_theory/presented_group.lean


Modified src/group_theory/quotient_group.lean


Modified src/group_theory/subgroup.lean
- \+ *lemma* monoid_hom.eq_lift_of_surjective
- \+ *lemma* monoid_hom.lift_of_surjective_comp
- \+ *lemma* monoid_hom.lift_of_surjective_comp_apply
- \+/\- *lemma* monoid_hom.mem_ker

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ring_hom.eq_lift_of_surjective
- \+ *lemma* ring_hom.lift_of_surjective_comp
- \+ *lemma* ring_hom.lift_of_surjective_comp_apply



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
- \+ *theorem* set.range_sigma_mk

Modified src/data/set/finite.lean
- \+ *lemma* finset.prod_preimage'
- \+ *lemma* finset.sigma_image_fst_preimage_mk
- \+ *lemma* finset.sigma_preimage_mk
- \+ *lemma* finset.sigma_preimage_mk_of_subset

Modified src/order/filter/at_top_bot.lean
- \- *lemma* filter.monotone.tendsto_at_top_finset
- \+ *lemma* filter.tendsto_at_top_finset_of_monotone
- \+ *lemma* filter.tendsto_finset_preimage_at_top_at_top

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/basic.lean
- \+ *lemma* cluster_pt_principal_iff_frequently
- \+ *lemma* filter.frequently.mem_of_closed
- \+ *lemma* is_closed.mem_of_frequently_of_tendsto
- \+ *lemma* is_closed.mem_of_tendsto
- \+ *lemma* mem_closure_iff_frequently
- \- *lemma* mem_of_closed_of_tendsto'
- \- *lemma* mem_of_closed_of_tendsto

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
- \+ *lemma* filter.tendsto.eventually_interval_integrable
- \+ *lemma* filter.tendsto.eventually_interval_integrable_ae
- \+ *lemma* interval_integral.FTC_filter.finite_at_inner
- \+ *lemma* interval_integral.deriv_integral_left
- \+ *lemma* interval_integral.deriv_integral_of_tendsto_ae_left
- \+ *lemma* interval_integral.deriv_integral_of_tendsto_ae_right
- \+ *lemma* interval_integral.deriv_integral_right
- \+ *lemma* interval_integral.deriv_within_integral_left
- \+ *lemma* interval_integral.deriv_within_integral_of_tendsto_ae_left
- \+ *lemma* interval_integral.deriv_within_integral_of_tendsto_ae_right
- \+ *lemma* interval_integral.deriv_within_integral_right
- \+ *lemma* interval_integral.fderiv_integral
- \+ *lemma* interval_integral.fderiv_integral_of_tendsto_ae
- \+ *lemma* interval_integral.fderiv_within_integral_of_tendsto_ae
- \+ *lemma* interval_integral.integral_Iic_sub_Iic
- \+ *lemma* interval_integral.integral_const'
- \+ *lemma* interval_integral.integral_const
- \+ *lemma* interval_integral.integral_const_of_cdf
- \+ *lemma* interval_integral.integral_has_deriv_at_left
- \- *lemma* interval_integral.integral_has_deriv_at_of_tendsto_ae
- \+ *lemma* interval_integral.integral_has_deriv_at_of_tendsto_ae_left
- \+ *lemma* interval_integral.integral_has_deriv_at_of_tendsto_ae_right
- \+ *lemma* interval_integral.integral_has_deriv_at_right
- \+ *lemma* interval_integral.integral_has_deriv_within_at_left
- \+ *lemma* interval_integral.integral_has_deriv_within_at_of_tendsto_ae_left
- \+ *lemma* interval_integral.integral_has_deriv_within_at_of_tendsto_ae_right
- \+ *lemma* interval_integral.integral_has_deriv_within_at_right
- \+ *lemma* interval_integral.integral_has_fderiv_at
- \+ *lemma* interval_integral.integral_has_fderiv_at_of_tendsto_ae
- \+ *lemma* interval_integral.integral_has_fderiv_within_at
- \+ *lemma* interval_integral.integral_has_fderiv_within_at_of_tendsto_ae
- \+ *lemma* interval_integral.integral_has_strict_deriv_at_left
- \+ *lemma* interval_integral.integral_has_strict_deriv_at_of_tendsto_ae_left
- \+ *lemma* interval_integral.integral_has_strict_deriv_at_of_tendsto_ae_right
- \+ *lemma* interval_integral.integral_has_strict_deriv_at_right
- \+ *lemma* interval_integral.integral_has_strict_fderiv_at
- \+ *lemma* interval_integral.integral_has_strict_fderiv_at_of_tendsto_ae
- \+ *lemma* interval_integral.integral_interval_add_interval_comm
- \+ *lemma* interval_integral.integral_interval_sub_interval_comm'
- \+ *lemma* interval_integral.integral_interval_sub_interval_comm
- \+ *lemma* interval_integral.integral_interval_sub_left
- \- *lemma* interval_integral.integral_same_has_deriv_at_of_tendsto_ae
- \+ *lemma* interval_integral.integral_smul
- \+ *lemma* interval_integral.integral_sub
- \+ *lemma* interval_integral.integral_sub_integral_sub_linear_is_o_of_tendsto_ae
- \+ *lemma* interval_integral.integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left
- \+ *lemma* interval_integral.integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right
- \+/\- *lemma* interval_integral.integral_sub_linear_is_o_of_tendsto_ae
- \+ *lemma* interval_integral.measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae
- \+ *lemma* interval_integral.measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left
- \+ *lemma* interval_integral.measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right
- \+ *lemma* interval_integral.measure_integral_sub_linear_is_o_of_tendsto_ae'
- \+ *lemma* interval_integral.measure_integral_sub_linear_is_o_of_tendsto_ae
- \+ *lemma* interval_integral.measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge'
- \+ *lemma* interval_integral.measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge
- \+ *lemma* interval_integral.measure_integral_sub_linear_is_o_of_tendsto_ae_of_le'
- \+ *lemma* interval_integral.measure_integral_sub_linear_is_o_of_tendsto_ae_of_le

Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure.finite_at_bot
- \+ *lemma* measure_theory.measure_lt_top
- \+ *lemma* measure_theory.measure_ne_top

Modified src/measure_theory/set_integral.lean


Modified src/order/filter/basic.lean
- \+ *lemma* filter.tendsto.frequently
- \+ *lemma* filter.tendsto.mono_left
- \+ *lemma* filter.tendsto.mono_right
- \+/\- *lemma* filter.tendsto_infi'
- \- *lemma* filter.tendsto_le_left
- \- *lemma* filter.tendsto_le_right

Modified src/order/filter/interval.lean
- \- *lemma* filter.has_basis.is_interval_generated
- \+ *lemma* filter.has_basis.tendsto_Ixx_class
- \- *lemma* filter.has_ord_connected_basis
- \- *lemma* filter.is_interval_generated_principal_iff
- \+/\- *lemma* filter.tendsto.Icc
- \+/\- *lemma* filter.tendsto.Ico
- \+/\- *lemma* filter.tendsto.Ioc
- \+/\- *lemma* filter.tendsto.Ioo
- \- *lemma* filter.tendsto.Ixx
- \+ *lemma* filter.tendsto_Ixx_class_inf
- \+ *lemma* filter.tendsto_Ixx_class_of_subset
- \+ *lemma* filter.tendsto_Ixx_class_principal
- \- *lemma* filter.tendsto_Ixx_same_filter
- \- *lemma* set.ord_connected.is_interval_generated_inf_principal

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/basic.lean
- \- *lemma* order_top.tendsto_at_top
- \+ *lemma* order_top.tendsto_at_top_nhds

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
- \+ *lemma* matrix.det_update_column_add
- \+ *lemma* matrix.det_update_column_smul
- \+ *lemma* matrix.det_update_row_add
- \+ *lemma* matrix.det_update_row_smul



## [2020-08-21 05:29:48](https://github.com/leanprover-community/mathlib/commit/23749aa)
chore(measure_theory/*): use `_measure` instead of `_meas` ([#3892](https://github.com/leanprover-community/mathlib/pull/3892))
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \- *lemma* measure_theory.integral_add_meas
- \+ *lemma* measure_theory.integral_add_measure
- \- *lemma* measure_theory.integral_map_meas
- \+ *lemma* measure_theory.integral_map_measure
- \- *lemma* measure_theory.integral_zero_meas
- \+ *lemma* measure_theory.integral_zero_measure
- \- *lemma* measure_theory.simple_func.integral_add_meas
- \+ *lemma* measure_theory.simple_func.integral_add_measure

Modified src/measure_theory/integration.lean
- \- *lemma* measure_theory.lintegral_add_meas
- \+ *lemma* measure_theory.lintegral_add_measure
- \- *lemma* measure_theory.lintegral_smul_meas
- \+ *lemma* measure_theory.lintegral_smul_measure
- \- *lemma* measure_theory.lintegral_sum_meas
- \+ *lemma* measure_theory.lintegral_sum_measure
- \- *lemma* measure_theory.lintegral_zero_meas
- \+ *lemma* measure_theory.lintegral_zero_measure

Modified src/measure_theory/l1_space.lean
- \- *lemma* measure_theory.integrable.add_meas
- \+ *lemma* measure_theory.integrable.add_measure
- \- *lemma* measure_theory.integrable.left_of_add_meas
- \+ *lemma* measure_theory.integrable.left_of_add_measure
- \- *lemma* measure_theory.integrable.mono_meas
- \+ *lemma* measure_theory.integrable.mono_measure
- \- *lemma* measure_theory.integrable.right_of_add_meas
- \+ *lemma* measure_theory.integrable.right_of_add_measure
- \- *lemma* measure_theory.integrable.smul_meas
- \+ *lemma* measure_theory.integrable.smul_measure
- \- *lemma* measure_theory.integrable_add_meas
- \+ *lemma* measure_theory.integrable_add_measure
- \- *lemma* measure_theory.integrable_map_meas
- \+ *lemma* measure_theory.integrable_map_measure
- \- *lemma* measure_theory.integrable_zero_meas
- \+ *lemma* measure_theory.integrable_zero_measure

Modified src/measure_theory/set_integral.lean
- \- *lemma* measure_theory.integrable_on.add_meas
- \+ *lemma* measure_theory.integrable_on.add_measure
- \- *lemma* measure_theory.integrable_on.mono_meas
- \+ *lemma* measure_theory.integrable_on.mono_measure
- \- *lemma* measure_theory.integrable_on_add_meas
- \+ *lemma* measure_theory.integrable_on_add_measure
- \+/\- *lemma* measure_theory.integral_empty



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
- \+ *def* category_theory.Cat.equiv_of_iso

Modified src/category_theory/functor_category.lean
- \+ *lemma* category_theory.nat_trans.hcomp_id_app
- \+ *lemma* category_theory.nat_trans.id_hcomp_app

Modified src/category_theory/monad/basic.lean
- \+ *lemma* category_theory.comonad_hom.assoc
- \+ *def* category_theory.comonad_hom.comp
- \+ *lemma* category_theory.comonad_hom.comp_id
- \+ *theorem* category_theory.comonad_hom.ext
- \+ *def* category_theory.comonad_hom.id
- \+ *lemma* category_theory.comonad_hom.id_comp
- \+ *structure* category_theory.comonad_hom
- \+ *lemma* category_theory.monad_hom.assoc
- \+ *def* category_theory.monad_hom.comp
- \+ *lemma* category_theory.monad_hom.comp_id
- \+ *theorem* category_theory.monad_hom.ext
- \+ *def* category_theory.monad_hom.id
- \+ *lemma* category_theory.monad_hom.id_comp
- \+ *structure* category_theory.monad_hom

Added src/category_theory/monad/bundled.lean
- \+ *lemma* category_theory.Comonad.coassoc_func_app
- \+ *lemma* category_theory.Comonad.comp_to_nat_trans
- \+ *def* category_theory.Comonad.forget
- \+ *def* category_theory.Comonad.hom
- \+ *def* category_theory.Comonad.terminal
- \+ *structure* category_theory.Comonad
- \+ *lemma* category_theory.Monad.assoc_func_app
- \+ *lemma* category_theory.Monad.comp_to_nat_trans
- \+ *def* category_theory.Monad.forget
- \+ *def* category_theory.Monad.hom
- \+ *def* category_theory.Monad.initial
- \+ *structure* category_theory.Monad

Added src/category_theory/monad/equiv_mon.lean
- \+ *def* category_theory.Monad.Mon_to_Monad
- \+ *def* category_theory.Monad.Monad_Mon_equiv
- \+ *def* category_theory.Monad.Monad_to_Mon
- \+ *def* category_theory.Monad.of_Mon
- \+ *def* category_theory.Monad.of_to_mon_end_iso
- \+ *def* category_theory.Monad.to_Mon
- \+ *def* category_theory.Monad.to_of_mon_end_iso



## [2020-08-21 01:44:02](https://github.com/leanprover-community/mathlib/commit/7271f74)
chore(scripts): update nolints.txt ([#3891](https://github.com/leanprover-community/mathlib/pull/3891))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-21 00:08:35](https://github.com/leanprover-community/mathlib/commit/0a48f0a)
feat(system/random): a monad for (pseudo-)randomized computations ([#3742](https://github.com/leanprover-community/mathlib/pull/3742))
#### Estimated changes
Modified src/control/monad/basic.lean
- \+ *def* reader_t.equiv
- \+ *def* state_t.equiv
- \+ *def* state_t.eval

Modified src/control/monad/cont.lean
- \+ *def* cont_t.equiv

Modified src/control/monad/writer.lean
- \+ *def* writer_t.equiv

Added src/control/uliftable.lean
- \+ *def* cont_t.uliftable'
- \+ *def* reader_t.uliftable'
- \+ *def* state_t.uliftable'
- \+ *def* uliftable.adapt_down
- \+ *def* uliftable.adapt_up
- \+ *def* uliftable.down
- \+ *def* uliftable.down_map
- \+ *lemma* uliftable.down_up
- \+ *def* uliftable.up
- \+ *lemma* uliftable.up_down
- \+ *def* uliftable.up_map
- \+ *def* writer_t.uliftable'

Added src/data/bitvec/basic.lean
- \+ *lemma* bitvec.add_lsb_div_two
- \+ *lemma* bitvec.add_lsb_eq_twice_add_one
- \+ *def* bitvec.of_fin
- \+ *lemma* bitvec.of_fin_le_of_fin_of_le
- \+ *lemma* bitvec.of_fin_to_fin
- \+ *lemma* bitvec.of_fin_val
- \+ *lemma* bitvec.of_nat_to_nat
- \+ *lemma* bitvec.to_bool_add_lsb_mod_two
- \+ *def* bitvec.to_fin
- \+ *lemma* bitvec.to_fin_le_to_fin_of_le
- \+ *lemma* bitvec.to_fin_of_fin
- \+ *lemma* bitvec.to_fin_val
- \+ *lemma* bitvec.to_nat_eq_foldr_reverse
- \+ *lemma* bitvec.to_nat_lt

Modified src/data/bool.lean
- \+ *def* bool.of_nat
- \+ *lemma* bool.of_nat_le_of_nat
- \+ *lemma* bool.of_nat_to_nat
- \+ *def* bool.to_nat
- \+ *lemma* bool.to_nat_le_to_nat

Modified src/data/fin.lean
- \+ *lemma* fact.bit0.pos
- \+ *lemma* fact.bit1.pos
- \+ *lemma* fact.pow.pos
- \+ *lemma* fact.succ.pos
- \+/\- *lemma* fin.add_nat_val
- \+ *def* fin.of_nat'
- \+ *lemma* fin.val_of_nat_eq_mod'
- \+ *lemma* fin.val_of_nat_eq_mod

Modified src/data/nat/basic.lean
- \+ *def* nat.log
- \+ *lemma* nat.log_pow
- \+ *lemma* nat.pow_le_iff_le_log
- \+ *lemma* nat.pow_log_le_self
- \+ *lemma* nat.pow_succ_log_gt_self

Modified src/data/stream/basic.lean
- \+ *def* stream.corec_state
- \+ *lemma* stream.length_take
- \+ *def* stream.take

Modified src/set_theory/lists.lean


Added src/system/random/basic.lean
- \+ *def* bitvec.random
- \+ *def* bitvec.random_r
- \+ *lemma* bool_of_nat_mem_Icc_of_mem_Icc_to_nat
- \+ *def* io.mk_generator
- \+ *def* io.random
- \+ *def* io.random_r
- \+ *def* io.random_series
- \+ *def* io.random_series_r
- \+ *def* io.run_rand
- \+ *def* rand.random
- \+ *def* rand.random_r
- \+ *def* rand.random_series
- \+ *def* rand.random_series_r
- \+ *def* rand.split
- \+ *def* rand
- \+ *def* rand_g.next
- \+ *def* rand_g
- \+ *def* random_fin_of_pos
- \+ *def* shift_31_left

Added test/slim_check.lean
- \+ *def* find_prime
- \+ *def* find_prime_aux
- \+ *def* iterated_primality_test
- \+ *def* iterated_primality_test_aux
- \+ *def* primality_test



## [2020-08-20 23:05:44](https://github.com/leanprover-community/mathlib/commit/36386fc)
feat(linear_algebra): some easy linear map/equiv lemmas ([#3890](https://github.com/leanprover-community/mathlib/pull/3890))
From the sphere eversion project.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv.comp_coe
- \+ *lemma* linear_equiv.eq_of_linear_map_eq
- \+ *lemma* linear_equiv.refl_to_linear_map
- \+ *lemma* linear_equiv.symm_trans
- \+ *lemma* linear_equiv.trans_symm

Modified src/linear_algebra/basis.lean
- \+ *lemma* equiv_of_is_basis_comp
- \+ *lemma* equiv_of_is_basis_refl
- \+ *lemma* equiv_of_is_basis_symm_trans
- \+ *lemma* equiv_of_is_basis_trans_symm



## [2020-08-20 21:33:51](https://github.com/leanprover-community/mathlib/commit/c9704ff)
chore(data/matrix, linear_algebra): generalize universe parameters ([#3879](https://github.com/leanprover-community/mathlib/pull/3879))
@PatrickMassot was complaining that `matrix m n R` often doesn't work when the parameters are declared as `m n : Type*` because the universe parameters were equal. This PR makes the universe parameters of `m` and `n` distinct where possible, also generalizing some other linear algebra definitions.
The types of `col` and `row` used to be `matrix n punit` but are now `matrix n unit`, otherwise the elaborator can't figure out the universe. This doesn't seem to break anything except for the cases where `punit.{n}` was explicitly written down.
There were some breakages, but the total amount of changes is not too big.
#### Estimated changes
Modified src/algebra/classical_lie_algebras.lean
- \+/\- *def* lie_algebra.orthogonal.JB
- \+/\- *def* lie_algebra.orthogonal.PB

Modified src/data/matrix/basic.lean
- \+/\- *def* matrix.col
- \+/\- *lemma* matrix.from_blocks_multiply
- \+/\- *def* matrix.row
- \+/\- *def* matrix

Modified src/data/matrix/notation.lean
- \+/\- *lemma* matrix.empty_val'
- \+/\- *lemma* matrix.smul_mat_empty

Modified src/data/matrix/pequiv.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_eq_of_injective
- \+/\- *lemma* dim_eq_of_surjective
- \+/\- *lemma* dim_le_of_injective
- \+/\- *lemma* dim_le_of_surjective
- \+/\- *lemma* dim_map_le
- \+/\- *theorem* dim_prod
- \+/\- *theorem* dim_range_add_dim_ker
- \+/\- *lemma* dim_range_le
- \+/\- *lemma* dim_range_of_surjective
- \+/\- *theorem* linear_equiv.dim_eq
- \+/\- *def* rank
- \+/\- *lemma* rank_add_le
- \+/\- *lemma* rank_comp_le1
- \+/\- *lemma* rank_comp_le2
- \+/\- *lemma* rank_finset_sum_le
- \+/\- *lemma* rank_le_domain
- \+/\- *lemma* rank_le_range
- \+/\- *lemma* rank_zero

Modified src/linear_algebra/matrix.lean
- \+/\- *lemma* matrix.rank_vec_mul_vec



## [2020-08-20 21:33:49](https://github.com/leanprover-community/mathlib/commit/901c5bc)
feat(ring_theory/separable): a separable polynomial splits into a product of unique `X - C a` ([#3877](https://github.com/leanprover-community/mathlib/pull/3877))
Bonus result: the degree of a separable polynomial is the number of roots
in the field where it splits.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.bind_singleton_eq_self

Modified src/data/multiset/nodup.lean
- \+ *lemma* multiset.nodup_iff_ne_cons_cons

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.roots_prod
- \+ *lemma* polynomial.roots_prod_X_sub_C

Modified src/field_theory/separable.lean
- \+ *lemma* polynomial.degree_separable_eq_card_roots
- \+ *lemma* polynomial.eq_prod_roots_of_separable
- \+ *lemma* polynomial.is_unit_of_self_mul_dvd_separable
- \+ *lemma* polynomial.nat_degree_separable_eq_card_roots
- \+ *lemma* polynomial.nodup_of_separable_prod
- \+ *lemma* polynomial.not_unit_X_sub_C
- \+ *lemma* polynomial.separable.of_dvd



## [2020-08-20 21:33:47](https://github.com/leanprover-community/mathlib/commit/9f525c7)
chore(category_theory/limits/types): cleanup ([#3871](https://github.com/leanprover-community/mathlib/pull/3871))
Backporting some cleaning up work from `prop_limits`, while it rumbles onwards.
#### Estimated changes
Modified src/algebra/category/Module/limits.lean


Modified src/algebra/category/Mon/limits.lean


Modified src/category_theory/limits/limits.lean


Modified src/category_theory/limits/preserves/basic.lean
- \+ *def* category_theory.limits.preserves_colimit_of_reflects_of_preserves
- \+ *def* category_theory.limits.preserves_limit_of_reflects_of_preserves

Modified src/category_theory/limits/shapes/types.lean


Modified src/category_theory/limits/types.lean
- \- *def* category_theory.limits.types.colimit_
- \+ *def* category_theory.limits.types.colimit_cocone
- \+ *def* category_theory.limits.types.colimit_cocone_is_colimit
- \+ *def* category_theory.limits.types.colimit_equiv_quot
- \+ *lemma* category_theory.limits.types.colimit_equiv_quot_symm_apply
- \- *def* category_theory.limits.types.colimit_is_colimit_
- \+ *lemma* category_theory.limits.types.lift_π_apply
- \- *def* category_theory.limits.types.limit_
- \+ *def* category_theory.limits.types.limit_cone
- \+ *def* category_theory.limits.types.limit_cone_is_limit
- \+ *def* category_theory.limits.types.limit_equiv_sections
- \+ *lemma* category_theory.limits.types.limit_equiv_sections_apply
- \+ *lemma* category_theory.limits.types.limit_equiv_sections_symm_apply
- \+ *lemma* category_theory.limits.types.limit_ext
- \- *def* category_theory.limits.types.limit_is_limit_
- \+ *def* category_theory.limits.types.quot
- \- *lemma* category_theory.limits.types.types_colimit
- \- *lemma* category_theory.limits.types.types_colimit_desc
- \- *lemma* category_theory.limits.types.types_colimit_map
- \- *lemma* category_theory.limits.types.types_colimit_pre
- \- *lemma* category_theory.limits.types.types_colimit_ι
- \- *lemma* category_theory.limits.types.types_limit
- \- *lemma* category_theory.limits.types.types_limit_lift
- \- *lemma* category_theory.limits.types.types_limit_map
- \- *lemma* category_theory.limits.types.types_limit_pre
- \- *lemma* category_theory.limits.types.types_limit_π



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
- \+ *lemma* polynomial.leading_coeff_X_add_C

Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.eval₂_endomorphism_algebra_map
- \+ *lemma* polynomial.eval₂_list_prod_noncomm
- \+ *lemma* polynomial.eval₂_mul_noncomm
- \+ *def* polynomial.eval₂_ring_hom_noncomm

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.units_coeff_zero_smul



## [2020-08-20 08:43:40](https://github.com/leanprover-community/mathlib/commit/e174f42)
feat(equiv/transfer_instances): other algebraic structures ([#3870](https://github.com/leanprover-community/mathlib/pull/3870))
Some updates to `data.equiv.transfer_instances`.
1. Use `@[to_additive]`
2. Add algebraic equivalences between the original and transferred instances.
3. Transfer modules and algebras.
#### Estimated changes
Modified src/data/equiv/transfer_instance.lean
- \- *lemma* equiv.add_def
- \+ *def* equiv.alg_equiv
- \+ *def* equiv.linear_equiv
- \+ *def* equiv.mul_equiv
- \+ *lemma* equiv.mul_equiv_apply
- \+ *lemma* equiv.mul_equiv_symm_apply
- \- *lemma* equiv.neg_def
- \+ *def* equiv.ring_equiv
- \+ *lemma* equiv.ring_equiv_apply
- \+ *lemma* equiv.ring_equiv_symm_apply
- \+ *lemma* equiv.smul_def
- \- *lemma* equiv.zero_def



## [2020-08-20 08:43:38](https://github.com/leanprover-community/mathlib/commit/d7621b9)
feat(data/list/basic): lemmas about foldr/foldl ([#3865](https://github.com/leanprover-community/mathlib/pull/3865))
This PR prepares [#3864](https://github.com/leanprover-community/mathlib/pull/3864).
* Move lemmas about `foldr`/`foldl` into the appropriate section.
* Add variants of the `foldl_map`/`foldr_map` lemmas.
* Add lemmas stating that a fold over a list of injective functions is injective.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.foldl_map'
- \+ *theorem* list.foldr_map'
- \+ *lemma* list.injective_foldl_comp



## [2020-08-20 08:00:59](https://github.com/leanprover-community/mathlib/commit/ba06edc)
chore(data/complex/module): move `linear_map.{re,im,of_real}` from `analysis` ([#3874](https://github.com/leanprover-community/mathlib/pull/3874))
I'm going to use these `def`s in `analysis/convex/basic`, and I don't
want to `import analysis.normed_space.basic` there.
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \- *def* complex.linear_map.im
- \- *lemma* complex.linear_map.im_apply
- \- *def* complex.linear_map.of_real
- \- *lemma* complex.linear_map.of_real_apply
- \- *def* complex.linear_map.re
- \- *lemma* complex.linear_map.re_apply

Modified src/data/complex/module.lean
- \+ *lemma* complex.linear_map.coe_im
- \+ *lemma* complex.linear_map.coe_of_real
- \+ *lemma* complex.linear_map.coe_re
- \+ *def* complex.linear_map.im
- \+ *def* complex.linear_map.of_real
- \+ *def* complex.linear_map.re



## [2020-08-20 06:10:17](https://github.com/leanprover-community/mathlib/commit/34db3c3)
feat(order/category): various categories of ordered types ([#3841](https://github.com/leanprover-community/mathlib/pull/3841))
This is a first step towards the category of simplicial sets (which are presheaves on the category of nonempty finite linear orders).
#### Estimated changes
Added src/order/category/LinearOrder.lean
- \+ *def* LinearOrder.of
- \+ *def* LinearOrder

Added src/order/category/NonemptyFinLinOrd.lean
- \+ *def* NonemptyFinLinOrd.of
- \+ *def* NonemptyFinLinOrd

Added src/order/category/PartialOrder.lean
- \+ *def* PartialOrder.of
- \+ *def* PartialOrder

Added src/order/category/Preorder.lean
- \+ *def* Preorder.of
- \+ *def* Preorder
- \+ *lemma* preorder_hom.coe_id
- \+ *lemma* preorder_hom.coe_inj
- \+ *def* preorder_hom.comp
- \+ *lemma* preorder_hom.comp_id
- \+ *lemma* preorder_hom.ext
- \+ *def* preorder_hom.id
- \+ *lemma* preorder_hom.id_comp
- \+ *structure* preorder_hom



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
- \+ *lemma* affine_subspace.direction_inf_of_mem
- \+ *lemma* affine_subspace.direction_inf_of_mem_inf
- \+ *lemma* affine_subspace.vadd_mem_iff_mem_direction



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
- \+ *lemma* ideal.eval₂_C_mk_eq_zero
- \+ *theorem* ideal.mem_map_C_iff
- \+ *def* ideal.polynomial_quotient_equiv_quotient_polynomial
- \+ *lemma* ideal.quotient_map_C_eq_zero



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
- \+ *lemma* submodule.Inf_orthogonal
- \+ *lemma* submodule.inf_orthogonal
- \+ *lemma* submodule.infi_orthogonal
- \+ *lemma* submodule.orthogonal_gc



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
- \+/\- *theorem* finset.sigma_eq_bind

Modified src/logic/embedding.lean
- \+ *lemma* function.embedding.coe_sigma_mk
- \+ *def* function.embedding.sigma_mk



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
Added src/analysis/calculus/lhopital.lean
- \+ *theorem* deriv.lhopital_zero_at_bot
- \+ *theorem* deriv.lhopital_zero_at_bot_on_Iio
- \+ *theorem* deriv.lhopital_zero_at_top
- \+ *theorem* deriv.lhopital_zero_at_top_on_Ioi
- \+ *theorem* deriv.lhopital_zero_left_on_Ioo
- \+ *theorem* deriv.lhopital_zero_nhds'
- \+ *theorem* deriv.lhopital_zero_nhds
- \+ *theorem* deriv.lhopital_zero_nhds_left
- \+ *theorem* deriv.lhopital_zero_nhds_right
- \+ *theorem* deriv.lhopital_zero_right_on_Ico
- \+ *theorem* deriv.lhopital_zero_right_on_Ioo
- \+ *theorem* has_deriv_at.lhopital_zero_at_bot
- \+ *theorem* has_deriv_at.lhopital_zero_at_bot_on_Iio
- \+ *theorem* has_deriv_at.lhopital_zero_at_top
- \+ *theorem* has_deriv_at.lhopital_zero_at_top_on_Ioi
- \+ *theorem* has_deriv_at.lhopital_zero_left_on_Ioc
- \+ *theorem* has_deriv_at.lhopital_zero_left_on_Ioo
- \+ *theorem* has_deriv_at.lhopital_zero_nhds'
- \+ *theorem* has_deriv_at.lhopital_zero_nhds
- \+ *theorem* has_deriv_at.lhopital_zero_nhds_left
- \+ *theorem* has_deriv_at.lhopital_zero_nhds_right
- \+ *theorem* has_deriv_at.lhopital_zero_right_on_Ico
- \+ *theorem* has_deriv_at.lhopital_zero_right_on_Ioo

Modified src/topology/continuous_on.lean
- \+ *lemma* eventually_nhds_within_of_eventually_nhds



## [2020-08-18 20:22:26](https://github.com/leanprover-community/mathlib/commit/5d2256d)
feat(miu_language): a formalisation of the MIU language described by D. Hofstadter in "Gödel, Escher, Bach". ([#3739](https://github.com/leanprover-community/mathlib/pull/3739))
We define an inductive type `derivable` so that `derivable x`  represents the notion that the MIU string `x` is derivable in the MIU language. We show `derivable x` is equivalent to `decstr x`, viz. the condition that `x` begins with an `M`, has no `M` in its tail, and for which `count I` is congruent to 1 or 2 modulo 3.
By showing `decidable_pred decstr`, we deduce that `derivable` is decidable.
#### Estimated changes
Added archive/miu_language/basic.lean
- \+ *inductive* miu.derivable
- \+ *def* miu.lchar_to_miustr
- \+ *def* miu.miu_atom.repr
- \+ *inductive* miu.miu_atom
- \+ *def* miu.miustr.mrepr
- \+ *def* miu.miustr

Added archive/miu_language/decision_nec.lean
- \+ *theorem* miu.count_equiv_one_or_two_mod3_of_derivable
- \+ *def* miu.count_equiv_or_equiv_two_mul_mod3
- \+ *def* miu.decstr
- \+ *theorem* miu.decstr_of_der
- \+ *def* miu.goodm
- \+ *theorem* miu.goodm_of_derivable
- \+ *lemma* miu.goodm_of_rule1
- \+ *lemma* miu.goodm_of_rule2
- \+ *lemma* miu.goodm_of_rule3
- \+ *lemma* miu.goodm_of_rule4
- \+ *lemma* miu.goodmi
- \+ *lemma* miu.mod3_eq_1_or_mod3_eq_2
- \+ *theorem* miu.not_derivable_mu

Added archive/miu_language/decision_suf.lean
- \+ *lemma* miu.add_mod2
- \+ *lemma* miu.base_case_suf
- \+ *lemma* miu.count_I_eq_length_of_count_U_zero_and_neg_mem
- \+ *lemma* miu.der_cons_repeat_I_repeat_U_append_of_der_cons_repeat_I_append
- \+ *theorem* miu.der_of_decstr
- \+ *lemma* miu.der_of_der_append_repeat_U_even
- \+ *lemma* miu.der_repeat_I_of_mod3
- \+ *lemma* miu.eq_append_cons_U_of_count_U_pos
- \+ *lemma* miu.ind_hyp_suf
- \+ *lemma* miu.le_pow2_and_pow2_eq_mod3
- \+ *lemma* miu.mem_of_count_U_eq_succ
- \+ *lemma* miu.repeat_pow_minus_append

Modified docs/references.bib


Modified src/data/list/basic.lean
- \+ *theorem* list.exists_cons_of_ne_nil
- \+ *theorem* list.repeat_count_eq_of_count_eq_length
- \+ *theorem* list.tail_append_singleton_of_ne_nil



## [2020-08-18 17:14:51](https://github.com/leanprover-community/mathlib/commit/0854e83)
chore(algebra/euclidean_domain): docstrings ([#3816](https://github.com/leanprover-community/mathlib/pull/3816))
#### Estimated changes
Modified src/algebra/euclidean_domain.lean
- \+/\- *theorem* euclidean_domain.div_add_mod
- \+/\- *lemma* euclidean_domain.div_self
- \+/\- *lemma* euclidean_domain.div_zero
- \+/\- *theorem* euclidean_domain.dvd_gcd
- \+/\- *theorem* euclidean_domain.dvd_lcm_left
- \+/\- *theorem* euclidean_domain.dvd_lcm_right
- \+/\- *lemma* euclidean_domain.dvd_mod_iff
- \+/\- *lemma* euclidean_domain.eq_div_of_mul_eq_left
- \+/\- *lemma* euclidean_domain.eq_div_of_mul_eq_right
- \+/\- *theorem* euclidean_domain.gcd.induction
- \+/\- *def* euclidean_domain.gcd
- \+/\- *def* euclidean_domain.gcd_a
- \+/\- *def* euclidean_domain.gcd_b
- \+/\- *theorem* euclidean_domain.gcd_dvd
- \+/\- *theorem* euclidean_domain.gcd_dvd_left
- \+/\- *theorem* euclidean_domain.gcd_dvd_right
- \+/\- *theorem* euclidean_domain.gcd_eq_gcd_ab
- \+/\- *theorem* euclidean_domain.gcd_eq_left
- \+/\- *lemma* euclidean_domain.gcd_mul_lcm
- \+/\- *theorem* euclidean_domain.gcd_one_left
- \+/\- *theorem* euclidean_domain.gcd_self
- \+/\- *theorem* euclidean_domain.gcd_val
- \+/\- *theorem* euclidean_domain.gcd_zero_left
- \+/\- *theorem* euclidean_domain.gcd_zero_right
- \+/\- *def* euclidean_domain.lcm
- \+/\- *theorem* euclidean_domain.lcm_dvd
- \+/\- *lemma* euclidean_domain.lcm_dvd_iff
- \+/\- *lemma* euclidean_domain.lcm_eq_zero_iff
- \+/\- *lemma* euclidean_domain.lcm_zero_left
- \+/\- *lemma* euclidean_domain.lcm_zero_right
- \+/\- *lemma* euclidean_domain.lt_one
- \+/\- *lemma* euclidean_domain.mod_eq_sub_mul_div
- \+/\- *lemma* euclidean_domain.mod_eq_zero
- \+/\- *theorem* euclidean_domain.mod_lt
- \+/\- *lemma* euclidean_domain.mod_one
- \+/\- *lemma* euclidean_domain.mod_self
- \+/\- *lemma* euclidean_domain.mod_zero
- \+/\- *theorem* euclidean_domain.mul_div_assoc
- \+/\- *lemma* euclidean_domain.mul_div_cancel
- \+/\- *lemma* euclidean_domain.mul_div_cancel_left
- \+/\- *theorem* euclidean_domain.mul_right_not_lt
- \+/\- *lemma* euclidean_domain.val_dvd_le
- \+/\- *def* euclidean_domain.xgcd
- \+/\- *def* euclidean_domain.xgcd_aux
- \+/\- *theorem* euclidean_domain.xgcd_aux_P
- \+/\- *theorem* euclidean_domain.xgcd_aux_fst
- \+/\- *theorem* euclidean_domain.xgcd_aux_rec
- \+/\- *theorem* euclidean_domain.xgcd_aux_val
- \+/\- *theorem* euclidean_domain.xgcd_val
- \+/\- *theorem* euclidean_domain.xgcd_zero_left
- \+/\- *lemma* euclidean_domain.zero_div
- \+/\- *lemma* euclidean_domain.zero_mod



## [2020-08-18 15:37:53](https://github.com/leanprover-community/mathlib/commit/7877033)
chore(logic/basic): `and_iff_left/right_iff_imp`, `or.right_comm` ([#3854](https://github.com/leanprover-community/mathlib/pull/3854))
Also add `@[simp]` to `forall_bool` and `exists_bool`
#### Estimated changes
Modified src/data/bool.lean
- \+/\- *theorem* bool.exists_bool
- \+/\- *theorem* bool.forall_bool

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
- \+ *lemma* option.ne_none_iff_exists'
- \+ *lemma* option.ne_none_iff_exists



## [2020-08-18 10:28:42](https://github.com/leanprover-community/mathlib/commit/67549d9)
feat(order/filter/at_top_bot): add `at_bot` versions for (almost) all `at_top` lemmas ([#3845](https://github.com/leanprover-community/mathlib/pull/3845))
There are a few lemmas I ignored, either because I thought a `at_bot` version wouldn't be useful (e.g subsequence lemmas), because there is no "order inversing" equivalent of `monotone` (I think ?), or because I just didn't understand the statement so I was unable to tell if it was useful or not.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.at_bot_basis'
- \+ *lemma* filter.at_bot_basis
- \+ *lemma* filter.at_bot_countable_basis
- \+ *lemma* filter.at_bot_ne_bot
- \+ *lemma* filter.eventually.exists_forall_of_at_bot
- \+ *lemma* filter.eventually_at_bot
- \+ *lemma* filter.eventually_le_at_bot
- \+ *lemma* filter.exists_le_of_tendsto_at_bot
- \+ *lemma* filter.exists_lt_of_tendsto_at_bot
- \+ *lemma* filter.frequently.forall_exists_of_at_bot
- \+ *lemma* filter.frequently_at_bot'
- \+ *lemma* filter.frequently_at_bot
- \+ *lemma* filter.frequently_low_scores
- \+ *lemma* filter.inf_map_at_bot_ne_bot_iff
- \+ *lemma* filter.is_countably_generated_at_bot
- \+ *lemma* filter.low_scores
- \+ *lemma* filter.map_at_bot_eq
- \+ *lemma* filter.map_at_bot_eq_of_gc
- \+ *lemma* filter.mem_at_bot_sets
- \+ *lemma* filter.order_bot.at_bot_eq
- \+ *lemma* filter.prod_at_bot_at_bot_eq
- \+ *lemma* filter.prod_map_at_bot_eq
- \+ *lemma* filter.tendsto_at_bot_add_const_left
- \+ *lemma* filter.tendsto_at_bot_add_const_right
- \+ *lemma* filter.tendsto_at_bot_add_left_of_ge'
- \+ *lemma* filter.tendsto_at_bot_add_left_of_ge
- \+ *lemma* filter.tendsto_at_bot_add_nonpos_left'
- \+ *lemma* filter.tendsto_at_bot_add_nonpos_left
- \+ *lemma* filter.tendsto_at_bot_add_nonpos_right'
- \+ *lemma* filter.tendsto_at_bot_add_nonpos_right
- \+ *lemma* filter.tendsto_at_bot_add_right_of_ge'
- \+ *lemma* filter.tendsto_at_bot_add_right_of_ge
- \+ *lemma* filter.tendsto_at_bot_at_bot_iff_of_monotone
- \+ *lemma* filter.tendsto_at_bot_at_bot_of_monotone'
- \+ *lemma* filter.tendsto_at_bot_at_bot_of_monotone
- \+ *lemma* filter.tendsto_at_bot_embedding
- \+ *lemma* filter.tendsto_at_bot_mono'
- \+ *lemma* filter.tendsto_at_bot_mono
- \+ *lemma* filter.tendsto_at_bot_of_add_bdd_below_left'
- \+ *lemma* filter.tendsto_at_bot_of_add_bdd_below_left
- \+ *lemma* filter.tendsto_at_bot_of_add_bdd_below_right'
- \+ *lemma* filter.tendsto_at_bot_of_add_bdd_below_right
- \+ *lemma* filter.tendsto_at_bot_of_add_const_left
- \+ *lemma* filter.tendsto_at_bot_of_add_const_right
- \+ *lemma* filter.tendsto_at_bot_of_monotone_of_filter
- \+ *lemma* filter.tendsto_at_bot_of_monotone_of_subseq
- \+ *theorem* filter.tendsto_at_bot_principal
- \+ *lemma* filter.tendsto_at_bot_pure
- \+ *lemma* filter.unbounded_of_tendsto_at_bot'
- \+ *lemma* filter.unbounded_of_tendsto_at_bot
- \+ *lemma* filter.unbounded_of_tendsto_at_top'



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
- \+ *lemma* finset.monotone_preimage

Modified src/field_theory/separable.lean


Modified src/linear_algebra/finsupp.lean


Modified src/order/filter/at_top_bot.lean




## [2020-08-18 08:44:58](https://github.com/leanprover-community/mathlib/commit/c356148)
feat(category_theory/abelian): pseudoelements and a four lemma ([#3803](https://github.com/leanprover-community/mathlib/pull/3803))
#### Estimated changes
Modified src/category_theory/abelian/basic.lean
- \+ *lemma* category_theory.abelian.image_ι_eq_image_ι
- \+ *lemma* category_theory.abelian.kernel_cokernel_eq_image_ι

Added src/category_theory/abelian/diagram_lemmas/four.lean
- \+ *lemma* category_theory.abelian.mono_of_epi_of_mono_of_mono

Modified src/category_theory/abelian/exact.lean
- \+ *def* category_theory.abelian.is_limit_image

Added src/category_theory/abelian/pseudoelements.lean
- \+ *def* category_theory.abelian.app
- \+ *lemma* category_theory.abelian.app_hom
- \+ *def* category_theory.abelian.pseudo_equal
- \+ *lemma* category_theory.abelian.pseudo_equal_refl
- \+ *lemma* category_theory.abelian.pseudo_equal_symm
- \+ *lemma* category_theory.abelian.pseudo_equal_trans
- \+ *lemma* category_theory.abelian.pseudoelement.apply_eq_zero_of_comp_eq_zero
- \+ *theorem* category_theory.abelian.pseudoelement.apply_zero
- \+ *theorem* category_theory.abelian.pseudoelement.comp_apply
- \+ *theorem* category_theory.abelian.pseudoelement.comp_comp
- \+ *theorem* category_theory.abelian.pseudoelement.epi_of_pseudo_surjective
- \+ *theorem* category_theory.abelian.pseudoelement.eq_zero_iff
- \+ *theorem* category_theory.abelian.pseudoelement.exact_of_pseudo_exact
- \+ *def* category_theory.abelian.pseudoelement.hom_to_fun
- \+ *theorem* category_theory.abelian.pseudoelement.mono_of_zero_of_map_zero
- \+ *def* category_theory.abelian.pseudoelement.object_to_sort
- \+ *lemma* category_theory.abelian.pseudoelement.over_coe_def
- \+ *def* category_theory.abelian.pseudoelement.over_to_sort
- \+ *def* category_theory.abelian.pseudoelement.pseudo_apply
- \+ *lemma* category_theory.abelian.pseudoelement.pseudo_apply_aux
- \+ *lemma* category_theory.abelian.pseudoelement.pseudo_apply_mk
- \+ *theorem* category_theory.abelian.pseudoelement.pseudo_exact_of_exact
- \+ *theorem* category_theory.abelian.pseudoelement.pseudo_injective_of_mono
- \+ *theorem* category_theory.abelian.pseudoelement.pseudo_pullback
- \+ *theorem* category_theory.abelian.pseudoelement.pseudo_surjective_of_epi
- \+ *def* category_theory.abelian.pseudoelement.pseudo_zero
- \+ *lemma* category_theory.abelian.pseudoelement.pseudo_zero_aux
- \+ *lemma* category_theory.abelian.pseudoelement.pseudo_zero_def
- \+ *lemma* category_theory.abelian.pseudoelement.pseudo_zero_iff
- \+ *def* category_theory.abelian.pseudoelement.setoid
- \+ *theorem* category_theory.abelian.pseudoelement.sub_of_eq_image
- \+ *theorem* category_theory.abelian.pseudoelement.zero_apply
- \+ *lemma* category_theory.abelian.pseudoelement.zero_eq_zero'
- \+ *lemma* category_theory.abelian.pseudoelement.zero_eq_zero
- \+ *theorem* category_theory.abelian.pseudoelement.zero_morphism_ext'
- \+ *theorem* category_theory.abelian.pseudoelement.zero_morphism_ext
- \+ *lemma* category_theory.abelian.pseudoelement.zero_of_map_zero
- \+ *def* category_theory.abelian.pseudoelement

Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* category_theory.limits.image_ι_comp_eq_zero

Modified src/category_theory/over.lean
- \+ *def* category_theory.over.coe_from_hom
- \+ *lemma* category_theory.over.coe_hom



## [2020-08-18 07:06:45](https://github.com/leanprover-community/mathlib/commit/0494807)
feat(algebra/ordered_*): cleanup and projection notation ([#3850](https://github.com/leanprover-community/mathlib/pull/3850))
Also add a few new projection notations.
#### Estimated changes
Modified src/algebra/order.lean


Modified src/algebra/ordered_field.lean


Modified src/algebra/ordered_group.lean
- \+/\- *lemma* mul_le_mul_three
- \+/\- *lemma* with_top.zero_lt_coe

Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* canonically_ordered_semiring.mul_le_mul
- \+/\- *lemma* canonically_ordered_semiring.zero_lt_one
- \+/\- *lemma* mul_lt_mul
- \+/\- *lemma* one_le_two
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
- \+/\- *lemma* fraction_map.is_unit_map_of_injective
- \+ *lemma* le_non_zero_divisors_of_domain
- \+ *lemma* localization_map.injective
- \+ *def* localization_map.integral_domain_localization
- \+ *def* localization_map.integral_domain_of_le_non_zero_divisors
- \+ *lemma* localization_map.to_map_eq_zero_iff



## [2020-08-17 20:43:24](https://github.com/leanprover-community/mathlib/commit/f818acb)
feat(analysis/normed_space): generalize corollaries of Hahn-Banach ([#3658](https://github.com/leanprover-community/mathlib/pull/3658))
#### Estimated changes
Modified src/analysis/normed_space/dual.lean
- \+/\- *lemma* normed_space.inclusion_in_double_dual_isometry
- \+/\- *lemma* normed_space.norm_le_dual_bound

Modified src/analysis/normed_space/hahn_banach.lean
- \+/\- *lemma* coord_norm'
- \- *lemma* coord_self'
- \+/\- *theorem* exists_dual_vector'
- \+/\- *theorem* exists_dual_vector
- \+ *lemma* norm'_def
- \+ *lemma* norm_norm'

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_equiv.coord_self



## [2020-08-17 17:33:37](https://github.com/leanprover-community/mathlib/commit/f8bf001)
fix(ring_theory/localization): remove coe_submodule instance ([#3832](https://github.com/leanprover-community/mathlib/pull/3832))
This coe can loop. See zulip discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Unknown.20error.20while.20type-checking.20with.20.60use.60/near/207089095
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+/\- *lemma* ring.fractional_ideal.coe_coe_ideal
- \+/\- *lemma* ring.fractional_ideal.coe_one
- \+/\- *lemma* ring.fractional_ideal.mem_coe
- \+/\- *lemma* ring.fractional_ideal.mem_zero_iff

Modified src/ring_theory/localization.lean
- \+ *def* localization_map.coe_submodule
- \- *lemma* localization_map.mem_coe
- \+ *lemma* localization_map.mem_coe_submodule



## [2020-08-17 16:59:15](https://github.com/leanprover-community/mathlib/commit/472251b)
feat(algebra): define linear recurrences and prove basic lemmas about them ([#3829](https://github.com/leanprover-community/mathlib/pull/3829))
We define "linear recurrences", i.e assertions of the form `∀ n : ℕ, u (n + d) = a 0 * u n + a 1 * u (n+1) + ... + a (d-1) * u (n+d-1)`, and we introduce basic related lemmas and definitions (solution space, auxiliary polynomial). Currently, the most advanced theorem is : `q ^ n` is a solution iff `q` is a root of the auxiliary polynomial.
#### Estimated changes
Added src/algebra/linear_recurrence.lean
- \+ *def* linear_recurrence.char_poly
- \+ *lemma* linear_recurrence.eq_mk_of_is_sol_of_eq_init'
- \+ *lemma* linear_recurrence.eq_mk_of_is_sol_of_eq_init
- \+ *lemma* linear_recurrence.geom_sol_iff_root_char_poly
- \+ *lemma* linear_recurrence.is_sol_iff_mem_sol_space
- \+ *lemma* linear_recurrence.is_sol_mk_sol
- \+ *def* linear_recurrence.is_solution
- \+ *def* linear_recurrence.mk_sol
- \+ *lemma* linear_recurrence.mk_sol_eq_init
- \+ *lemma* linear_recurrence.sol_eq_of_eq_init
- \+ *def* linear_recurrence.sol_space
- \+ *lemma* linear_recurrence.sol_space_dim
- \+ *def* linear_recurrence.to_init
- \+ *def* linear_recurrence.tuple_succ
- \+ *structure* linear_recurrence



## [2020-08-17 15:28:54](https://github.com/leanprover-community/mathlib/commit/3edf2b2)
feat(ring_theory/DVR,padics/padic_integers): characterize ideals of DVRs, apply to `Z_p` ([#3827](https://github.com/leanprover-community/mathlib/pull/3827))
Also introduce the p-adic valuation on `Z_p`, stolen from the perfectoid project.
Coauthored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *lemma* dvd_pow

Modified src/data/padics/padic_integers.lean
- \+ *lemma* padic_int.ideal_eq_span_pow_p
- \+ *lemma* padic_int.irreducible_p
- \+ *lemma* padic_int.maximal_ideal_eq_span_p
- \+ *def* padic_int.mk_units
- \+ *lemma* padic_int.mk_units_eq
- \+ *lemma* padic_int.norm_eq_pow_val
- \+ *lemma* padic_int.norm_units
- \+ *lemma* padic_int.p_dvd_of_norm_lt_one
- \+ *lemma* padic_int.p_nonnunit
- \+ *lemma* padic_int.prime_p
- \+ *def* padic_int.unit_coeff
- \+ *lemma* padic_int.unit_coeff_coe
- \+ *lemma* padic_int.unit_coeff_spec
- \+ *def* padic_int.valuation
- \+ *lemma* padic_int.valuation_nonneg
- \+ *lemma* padic_int.valuation_one
- \+ *lemma* padic_int.valuation_p
- \+ *lemma* padic_int.valuation_zero
- \+ *lemma* padic_norm_z.norm_p
- \+ *lemma* padic_norm_z.norm_p_pow

Modified src/ring_theory/discrete_valuation_ring.lean
- \+ *lemma* discrete_valuation_ring.associated_pow_irreducible
- \+ *lemma* discrete_valuation_ring.aux_pid_of_ufd_of_unique_irreducible
- \+ *lemma* discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization.of_ufd_of_unique_irreducible
- \+ *lemma* discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization.unique_irreducible
- \+ *def* discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization
- \+ *lemma* discrete_valuation_ring.ideal_eq_span_pow_irreducible
- \- *theorem* discrete_valuation_ring.iff_PID_with_one_nonzero_prime
- \+ *theorem* discrete_valuation_ring.iff_pid_with_one_nonzero_prime
- \- *theorem* discrete_valuation_ring.irreducible_iff_uniformiser
- \+ *theorem* discrete_valuation_ring.irreducible_iff_uniformizer
- \+ *lemma* discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization
- \+ *lemma* discrete_valuation_ring.of_ufd_of_unique_irreducible



## [2020-08-17 15:28:52](https://github.com/leanprover-community/mathlib/commit/d4cb237)
feat(algebra/module): define ordered semimodules and generalize convexity of functions ([#3728](https://github.com/leanprover-community/mathlib/pull/3728))
#### Estimated changes
Added src/algebra/module/ordered.lean
- \+ *lemma* smul_le_smul_of_nonneg
- \+ *lemma* smul_lt_smul_of_pos

Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex_on.add
- \+/\- *lemma* convex_on.comp_affine_map
- \+/\- *lemma* convex_on.comp_linear_map
- \+/\- *lemma* convex_on.convex_epigraph
- \+/\- *lemma* convex_on.convex_le
- \+/\- *lemma* convex_on.convex_lt
- \+/\- *lemma* convex_on.le_on_segment'
- \+/\- *lemma* convex_on.le_on_segment
- \+/\- *lemma* convex_on.smul
- \+/\- *lemma* convex_on.subset
- \+/\- *lemma* convex_on.translate_left
- \+/\- *lemma* convex_on.translate_right
- \+/\- *def* convex_on
- \+/\- *lemma* convex_on_const
- \+/\- *lemma* convex_on_iff_convex_epigraph
- \- *lemma* convex_on_iff_div:
- \+ *lemma* convex_on_iff_div
- \+/\- *lemma* linear_order.convex_on_of_lt

Modified src/analysis/convex/specific_functions.lean
- \+/\- *lemma* convex_on_fpow
- \+/\- *lemma* convex_on_pow
- \+/\- *lemma* convex_on_pow_of_even
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
- \+/\- *theorem* and_iff_not_or_not
- \+ *theorem* by_contra
- \+/\- *theorem* by_contradiction
- \- *lemma* classical.iff_iff_not_or_and_or_not
- \- *theorem* classical.or_not
- \+ *lemma* decidable.iff_iff_not_or_and_or_not
- \+ *theorem* em
- \+/\- *theorem* forall_or_distrib_left
- \+/\- *theorem* forall_or_distrib_right
- \+/\- *theorem* iff_iff_and_or_not_and_not
- \+ *lemma* iff_iff_not_or_and_or_not
- \+/\- *theorem* iff_not_comm
- \+/\- *theorem* imp_iff_not_or
- \+/\- *lemma* imp_imp_imp
- \+/\- *theorem* imp_or_distrib'
- \+/\- *theorem* imp_or_distrib
- \+ *theorem* not.decidable_imp_symm
- \+/\- *theorem* not.imp_symm
- \- *theorem* not_and_distrib'
- \+/\- *theorem* not_and_distrib
- \+/\- *theorem* not_and_not_right
- \+/\- *theorem* not_ball
- \+/\- *theorem* not_exists_not
- \+/\- *theorem* not_forall
- \+/\- *theorem* not_forall_not
- \+/\- *theorem* not_iff
- \+/\- *theorem* not_iff_comm
- \+/\- *theorem* not_iff_not
- \+/\- *theorem* not_imp
- \+/\- *theorem* not_imp_comm
- \+/\- *theorem* not_imp_not
- \+/\- *theorem* not_not
- \+/\- *theorem* not_or_of_imp
- \+/\- *theorem* of_not_imp
- \+/\- *theorem* of_not_not
- \+/\- *theorem* or_iff_not_and_not
- \+/\- *theorem* or_iff_not_imp_left
- \+/\- *theorem* or_iff_not_imp_right
- \+ *theorem* or_not
- \+/\- *theorem* peirce

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
- \+/\- *lemma* list.insert_nth_remove_nth_of_ge

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
- \+/\- *lemma* ennreal.Icc_mem_nhds

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
- \+ *lemma* centroid_mem_affine_span_of_card_eq_add_one
- \+ *lemma* centroid_mem_affine_span_of_card_ne_zero
- \+ *lemma* centroid_mem_affine_span_of_cast_card_ne_zero
- \+ *lemma* centroid_mem_affine_span_of_nonempty
- \+ *def* finset.centroid
- \+ *lemma* finset.centroid_def
- \+ *lemma* finset.centroid_singleton
- \+ *def* finset.centroid_weights
- \+ *lemma* finset.centroid_weights_apply
- \+ *lemma* finset.centroid_weights_eq_const
- \+ *lemma* finset.sum_centroid_weights_eq_one_of_card_eq_add_one
- \+ *lemma* finset.sum_centroid_weights_eq_one_of_card_ne_zero
- \+ *lemma* finset.sum_centroid_weights_eq_one_of_cast_card_ne_zero
- \+ *lemma* finset.sum_centroid_weights_eq_one_of_nonempty



## [2020-08-17 04:44:59](https://github.com/leanprover-community/mathlib/commit/6773f52)
feat(category_theory): limits in the category of indexed families ([#3737](https://github.com/leanprover-community/mathlib/pull/3737))
A continuation of [#3735](https://github.com/leanprover-community/mathlib/pull/3735), hopefully useful in [#3638](https://github.com/leanprover-community/mathlib/pull/3638).
#### Estimated changes
Added src/category_theory/limits/pi.lean
- \+ *def* category_theory.pi.cone_comp_eval
- \+ *def* category_theory.pi.cone_of_cone_comp_eval
- \+ *def* category_theory.pi.cone_of_cone_eval_is_limit
- \+ *def* category_theory.pi.has_limit_of_has_limit_comp_eval

Modified src/category_theory/pi/basic.lean
- \+ *abbreviation* category_theory.pi'



## [2020-08-17 04:10:13](https://github.com/leanprover-community/mathlib/commit/b0b5cd4)
feat(geometry/euclidean): circumradius simp lemmas ([#3834](https://github.com/leanprover-community/mathlib/pull/3834))
Mark `dist_circumcenter_eq_circumradius` as a `simp` lemma.  Also add
a variant of that lemma where the distance is the other way round so
`simp` can work with both forms.
#### Estimated changes
Modified src/geometry/euclidean.lean
- \+ *lemma* affine.simplex.dist_circumcenter_eq_circumradius'
- \+/\- *lemma* affine.simplex.dist_circumcenter_eq_circumradius



## [2020-08-17 03:03:18](https://github.com/leanprover-community/mathlib/commit/43337f7)
chore(data/nat/digits): refactor proof of `last_digit_ne_zero` ([#3836](https://github.com/leanprover-community/mathlib/pull/3836))
I thoroughly misunderstood why my prior attempts for [#3544](https://github.com/leanprover-community/mathlib/pull/3544) weren't working. I've refactored the proof so the `private` lemma is no longer necessary.
#### Estimated changes
Modified src/data/nat/digits.lean




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
- \+ *lemma* eq_one_of_left_cancel_mul_self
- \+ *lemma* eq_one_of_mul_self_left_cancel
- \+ *lemma* eq_one_of_mul_self_right_cancel
- \+ *lemma* eq_one_of_right_cancel_mul_self

Modified src/algebra/group/defs.lean


Modified src/algebra/lie_algebra.lean
- \- *def* lie_algebra.of_associative_algebra
- \- *def* lie_ring.of_associative_ring
- \- *def* matrix.lie_algebra
- \- *def* matrix.lie_ring
- \- *lemma* ring_commutator.add_left
- \- *lemma* ring_commutator.add_right
- \- *lemma* ring_commutator.alternate
- \+ *lemma* ring_commutator.commutator
- \- *def* ring_commutator.commutator
- \- *lemma* ring_commutator.jacobi

Modified src/algebra/module/basic.lean
- \+/\- *lemma* is_linear_map.is_linear_map_smul

Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/hahn_banach.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *def* continuous_linear_map.smul_algebra_right

Modified src/data/complex/module.lean


Modified src/data/monoid_algebra.lean


Modified src/group_theory/group_action.lean
- \+/\- *lemma* smul_assoc

Modified src/representation_theory/maschke.lean


Modified src/ring_theory/algebra.lean
- \+ *lemma* algebra_compatible_smul
- \+/\- *def* linear_map_algebra_module
- \+ *lemma* map_smul_eq_smul_map
- \- *def* module.restrict_scalars'
- \- *def* module.restrict_scalars
- \- *lemma* module.restrict_scalars_smul_def
- \+ *def* semimodule.restrict_scalars'
- \+ *def* semimodule.restrict_scalars
- \+ *lemma* semimodule.restrict_scalars_smul_def
- \+/\- *def* smul_algebra_right
- \- *lemma* smul_algebra_smul
- \+/\- *lemma* smul_algebra_smul_comm
- \+/\- *def* subspace.restrict_scalars

Added src/ring_theory/derivation.lean
- \+ *lemma* derivation.Rsmul_apply
- \+ *lemma* derivation.add_apply
- \+ *lemma* derivation.coe_fn_coe
- \+ *lemma* derivation.coe_injective
- \+ *def* derivation.commutator
- \+ *lemma* derivation.commutator_apply
- \+ *lemma* derivation.commutator_coe_linear_map
- \+ *theorem* derivation.ext
- \+ *lemma* derivation.leibniz
- \+ *lemma* derivation.map_add
- \+ *lemma* derivation.map_algebra_map
- \+ *lemma* derivation.map_neg
- \+ *lemma* derivation.map_one_eq_zero
- \+ *lemma* derivation.map_smul
- \+ *lemma* derivation.map_sub
- \+ *lemma* derivation.map_zero
- \+ *lemma* derivation.smul_apply
- \+ *lemma* derivation.smul_to_linear_map_coe
- \+ *lemma* derivation.to_fun_eq_coe
- \+ *structure* derivation
- \+ *def* linear_map.comp_der
- \+ *lemma* linear_map.comp_der_apply



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
- \+ *theorem* function.sometimes_eq
- \+ *theorem* function.sometimes_spec

Modified src/tactic/basic.lean


Added src/tactic/choose.lean


Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Modified test/choose.lean




## [2020-08-16 17:15:55](https://github.com/leanprover-community/mathlib/commit/3d4f085)
chore(ring_theory/ideal): docstring for Krull's theorem and a special case ([#3831](https://github.com/leanprover-community/mathlib/pull/3831))
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+ *theorem* ideal.exists_maximal



## [2020-08-16 13:39:50](https://github.com/leanprover-community/mathlib/commit/ee74e7f)
feat(analysis/special_functions/exp_log): `tendsto real.log at_top at_top` ([#3826](https://github.com/leanprover-community/mathlib/pull/3826))
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* real.tendsto_log_at_top



## [2020-08-16 12:41:57](https://github.com/leanprover-community/mathlib/commit/863bf79)
feat(data/padics): more valuations, facts about norms ([#3790](https://github.com/leanprover-community/mathlib/pull/3790))
Assorted lemmas about the `p`-adics. @jcommelin and I are adding algebraic structure here as part of the Witt vector development.
Some of these declarations are stolen shamelessly from the perfectoid project.
Coauthored by: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/padics/padic_norm.lean
- \+ *lemma* padic_norm.padic_norm_p
- \+ *lemma* padic_norm.padic_norm_p_lt_one
- \+ *lemma* padic_norm.padic_norm_p_lt_one_of_prime
- \+ *lemma* padic_norm.padic_norm_p_of_prime

Modified src/data/padics/padic_numbers.lean
- \+/\- *lemma* padic.cast_eq_of_rat_of_int
- \+/\- *lemma* padic.cast_eq_of_rat_of_nat
- \+ *lemma* padic.norm_eq_pow_val
- \+ *def* padic.valuation
- \+ *lemma* padic.valuation_one
- \+ *lemma* padic.valuation_p
- \+ *lemma* padic.valuation_zero
- \+ *lemma* padic_norm_e.norm_p
- \+ *lemma* padic_norm_e.norm_p_lt_one
- \+ *lemma* padic_norm_e.norm_p_pow
- \+ *lemma* padic_seq.norm_eq_pow_val
- \- *lemma* padic_seq.norm_image
- \+ *lemma* padic_seq.norm_values_discrete
- \+ *lemma* padic_seq.val_eq_iff_norm_eq
- \+ *def* padic_seq.valuation



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
- \+/\- *lemma* euclidean_domain.div_self
- \+/\- *lemma* euclidean_domain.div_zero
- \+/\- *lemma* euclidean_domain.zero_div

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
- \+/\- *lemma* cardinal.mk_Icc_real
- \+/\- *lemma* cardinal.mk_Ici_real
- \+/\- *lemma* cardinal.mk_Ico_real
- \+/\- *lemma* cardinal.mk_Iic_real
- \+/\- *lemma* cardinal.mk_Iio_real
- \+/\- *lemma* cardinal.mk_Ioc_real
- \+/\- *lemma* cardinal.mk_Ioi_real
- \+/\- *lemma* cardinal.mk_Ioo_real
- \+/\- *lemma* cardinal.mk_real
- \+/\- *lemma* cardinal.mk_univ_real



## [2020-08-16 06:05:24](https://github.com/leanprover-community/mathlib/commit/8325cf6)
feat(*): reorder implicit arguments in tsum, supr, infi ([#3809](https://github.com/leanprover-community/mathlib/pull/3809))
This is helpful for a future version of the `ge_or_gt` linter to recognize binders: the binding type is the (implicit) argument directly before the binding body.
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+/\- *def* infi
- \+/\- *def* supr

Modified src/tactic/converter/binders.lean


Modified src/topology/algebra/infinite_sum.lean
- \+/\- *def* tsum



## [2020-08-16 06:05:21](https://github.com/leanprover-community/mathlib/commit/dba3018)
feat(category_theory): the category of indexed families of objects ([#3735](https://github.com/leanprover-community/mathlib/pull/3735))
Pulling out a definition from [#3638](https://github.com/leanprover-community/mathlib/pull/3638), and add some associated basic material.
#### Estimated changes
Modified src/category_theory/graded_object.lean
- \- *def* category_theory.graded_object.comap
- \- *def* category_theory.graded_object.comap_comp
- \+/\- *def* category_theory.graded_object.comap_eq
- \- *def* category_theory.graded_object.comap_id
- \- *lemma* category_theory.graded_object.comp_apply
- \- *lemma* category_theory.graded_object.id_apply

Added src/category_theory/pi/basic.lean
- \+ *def* category_theory.functor.pi
- \+ *def* category_theory.nat_trans.pi
- \+ *def* category_theory.pi.comap
- \+ *def* category_theory.pi.comap_comp
- \+ *def* category_theory.pi.comap_eval_iso_eval
- \+ *def* category_theory.pi.comap_id
- \+ *lemma* category_theory.pi.comp_apply
- \+ *def* category_theory.pi.eval
- \+ *lemma* category_theory.pi.id_apply
- \+ *def* category_theory.pi.sum

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
- \+ *def* Top.presheaf_to_Type
- \+ *lemma* Top.presheaf_to_Type_map
- \+ *lemma* Top.presheaf_to_Type_obj
- \+ *def* Top.presheaf_to_Types

Added src/topology/sheaves/sheaf_of_functions.lean
- \+ *def* Top.sheaf_condition.forget_continuity
- \+ *def* Top.sheaf_condition.to_Top
- \+ *def* Top.sheaf_condition.to_Type
- \+ *def* Top.sheaf_condition.to_Types



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
- \+ *lemma* mv_polynomial.coeff_eq_zero_of_total_degree_lt
- \+ *lemma* mv_polynomial.eq_zero_iff
- \+ *lemma* mv_polynomial.exists_coeff_ne_zero
- \+ *lemma* mv_polynomial.ne_zero_iff

Added src/ring_theory/polynomial/homogeneous.lean
- \+ *def* mv_polynomial.homogeneous_component
- \+ *lemma* mv_polynomial.homogeneous_component_apply
- \+ *lemma* mv_polynomial.homogeneous_component_eq_zero'
- \+ *lemma* mv_polynomial.homogeneous_component_eq_zero
- \+ *lemma* mv_polynomial.homogeneous_component_is_homogeneous
- \+ *lemma* mv_polynomial.homogeneous_component_zero
- \+ *lemma* mv_polynomial.is_homogeneous.add
- \+ *lemma* mv_polynomial.is_homogeneous.coeff_eq_zero
- \+ *lemma* mv_polynomial.is_homogeneous.inj_right
- \+ *lemma* mv_polynomial.is_homogeneous.mul
- \+ *lemma* mv_polynomial.is_homogeneous.prod
- \+ *lemma* mv_polynomial.is_homogeneous.sum
- \+ *lemma* mv_polynomial.is_homogeneous.total_degree
- \+ *def* mv_polynomial.is_homogeneous
- \+ *lemma* mv_polynomial.is_homogeneous_C
- \+ *lemma* mv_polynomial.is_homogeneous_X
- \+ *lemma* mv_polynomial.is_homogeneous_monomial
- \+ *lemma* mv_polynomial.is_homogeneous_one
- \+ *lemma* mv_polynomial.is_homogeneous_zero
- \+ *lemma* mv_polynomial.sum_homogeneous_component



## [2020-08-16 04:46:02](https://github.com/leanprover-community/mathlib/commit/b1e7fb2)
feat (category_theory/over): composition of `over.map` ([#3798](https://github.com/leanprover-community/mathlib/pull/3798))
Filtering in some defs from the topos project.
~~Depends on [#3797](https://github.com/leanprover-community/mathlib/pull/3797).~~
#### Estimated changes
Modified src/category_theory/over.lean
- \+ *def* category_theory.over.map_comp
- \+ *def* category_theory.over.map_id
- \+ *def* category_theory.under.map_comp
- \+ *def* category_theory.under.map_id



## [2020-08-16 04:46:00](https://github.com/leanprover-community/mathlib/commit/1037a3a)
feat(algebra/homology, category_theory/abelian, algebra/category/Module): exactness ([#3784](https://github.com/leanprover-community/mathlib/pull/3784))
We define what it means for two maps `f` and `g` to be exact and show that for R-modules, this is the case if and only if `range f = ker g`.
#### Estimated changes
Modified src/algebra/category/Module/abelian.lean
- \+ *theorem* Module.exact_iff

Added src/algebra/homology/exact.lean
- \+ *lemma* category_theory.comp_eq_zero_of_exact
- \+ *lemma* category_theory.fork_ι_comp_cofork_π
- \+ *lemma* category_theory.kernel_comp_cokernel

Modified src/algebra/homology/homology.lean


Modified src/algebra/homology/image_to_kernel_map.lean
- \+ *abbreviation* category_theory.image_to_kernel_map
- \- *def* category_theory.image_to_kernel_map

Modified src/category_theory/abelian/basic.lean
- \+/\- *abbreviation* category_theory.abelian.coimage_iso_image
- \- *def* category_theory.abelian.coimage_strong_epi_mono_factorisation
- \+ *def* category_theory.abelian.coimages.coimage_strong_epi_mono_factorisation
- \+/\- *lemma* category_theory.abelian.full_image_factorisation
- \+/\- *lemma* category_theory.abelian.image_eq_image
- \- *def* category_theory.abelian.image_strong_epi_mono_factorisation
- \+ *def* category_theory.abelian.images.image_strong_epi_mono_factorisation
- \+ *def* category_theory.abelian.non_preadditive_abelian

Added src/category_theory/abelian/exact.lean
- \+ *theorem* category_theory.abelian.exact_iff'
- \+ *theorem* category_theory.abelian.exact_iff

Modified src/category_theory/limits/limits.lean
- \+ *lemma* category_theory.limits.colimit.comp_cocone_point_unique_up_to_iso_hom
- \+ *lemma* category_theory.limits.colimit.comp_cocone_point_unique_up_to_iso_inv
- \+ *lemma* category_theory.limits.is_colimit.comp_cocone_point_unique_up_to_iso_hom
- \+ *lemma* category_theory.limits.is_colimit.comp_cocone_point_unique_up_to_iso_inv
- \+ *lemma* category_theory.limits.is_limit.cone_point_unique_up_to_iso_hom_comp
- \+ *lemma* category_theory.limits.is_limit.cone_point_unique_up_to_iso_inv_comp
- \+ *lemma* category_theory.limits.limit.cone_point_unique_up_to_iso_hom_comp
- \+ *lemma* category_theory.limits.limit.cone_point_unique_up_to_iso_inv_comp

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.ker_le_range_iff



## [2020-08-16 04:45:58](https://github.com/leanprover-community/mathlib/commit/2c930a3)
refactor(algebra/gcd_monoid, ring_theory/multiplicity): generalize normalization_domain, gcd_domain, multiplicity ([#3779](https://github.com/leanprover-community/mathlib/pull/3779))
* generalize `normalization_domain`, `gcd_domain`, `multiplicity` to not reference addition and subtraction
* make `gcd_monoid` and `normalization_monoid` into mixins
* add instances of `normalization_monoid` for `nat`, `associates`
#### Estimated changes
Modified src/algebra/associated.lean
- \+/\- *theorem* associates.coe_unit_eq_one
- \+ *theorem* associates.units_eq_one

Renamed src/algebra/gcd_domain.lean to src/algebra/gcd_monoid.lean
- \+/\- *lemma* dvd_normalize_iff
- \+ *theorem* gcd_monoid.irreducible_iff_prime
- \+ *theorem* gcd_monoid.prime_of_irreducible
- \+/\- *lemma* int.coe_gcd
- \+/\- *lemma* int.coe_lcm
- \+/\- *lemma* int.nat_abs_gcd
- \+/\- *lemma* int.nat_abs_lcm
- \+ *lemma* norm_unit_eq_one
- \+/\- *theorem* norm_unit_mul_norm_unit
- \+/\- *def* normalize
- \+ *lemma* normalize_apply
- \+/\- *lemma* normalize_coe_units
- \+/\- *lemma* normalize_dvd_iff
- \+ *lemma* normalize_eq
- \+/\- *theorem* normalize_idem
- \- *theorem* normalize_mul
- \+/\- *lemma* normalize_one
- \+/\- *lemma* normalize_zero
- \+ *lemma* units_eq_one

Modified src/data/nat/basic.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/polynomial/field_division.lean
- \+/\- *lemma* polynomial.degree_normalize

Modified src/data/real/irrational.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/ring_theory/multiplicity.lean
- \+/\- *def* multiplicity

Modified src/ring_theory/unique_factorization_domain.lean
- \- *def* unique_factorization_domain.to_gcd_domain
- \+ *def* unique_factorization_domain.to_gcd_monoid



## [2020-08-16 03:16:51](https://github.com/leanprover-community/mathlib/commit/ae8abf3)
chore(order/rel_iso): rename order_iso and order_embedding to rel_iso and rel_embedding ([#3750](https://github.com/leanprover-community/mathlib/pull/3750))
renames `order_iso` and `order_embedding`, to make it clear they apply to all binary relations
makes room for a new definition of `order_embedding` that will deal with order instances
#### Estimated changes
Modified scripts/nolints.txt


Modified src/data/equiv/encodable/basic.lean


Modified src/data/equiv/list.lean


Modified src/data/finsupp/lattice.lean
- \- *def* finsupp.order_embedding_to_fun
- \- *lemma* finsupp.order_embedding_to_fun_apply
- \- *def* finsupp.order_iso_multiset
- \- *lemma* finsupp.order_iso_multiset_apply
- \- *lemma* finsupp.order_iso_multiset_symm_apply
- \+ *def* finsupp.rel_embedding_to_fun
- \+ *lemma* finsupp.rel_embedding_to_fun_apply
- \+ *def* finsupp.rel_iso_multiset
- \+ *lemma* finsupp.rel_iso_multiset_apply
- \+ *lemma* finsupp.rel_iso_multiset_symm_apply

Modified src/data/setoid/basic.lean
- \+/\- *def* setoid.correspondence

Modified src/data/setoid/partition.lean
- \- *def* setoid.partition.order_iso
- \+ *def* setoid.partition.rel_iso

Modified src/group_theory/congruence.lean
- \+/\- *def* con.correspondence

Modified src/linear_algebra/basic.lean
- \- *def* submodule.comap_mkq.le_order_embedding
- \+ *def* submodule.comap_mkq.le_rel_embedding
- \- *def* submodule.comap_mkq.lt_order_embedding
- \+ *def* submodule.comap_mkq.lt_rel_embedding
- \- *def* submodule.comap_mkq.order_iso
- \+ *def* submodule.comap_mkq.rel_iso
- \- *def* submodule.map_subtype.le_order_embedding
- \+ *def* submodule.map_subtype.le_rel_embedding
- \- *def* submodule.map_subtype.lt_order_embedding
- \+ *def* submodule.map_subtype.lt_rel_embedding
- \- *def* submodule.map_subtype.order_iso
- \+ *def* submodule.map_subtype.rel_iso

Modified src/order/galois_connection.lean
- \- *theorem* order_iso.to_galois_connection
- \+ *theorem* rel_iso.to_galois_connection

Modified src/order/ord_continuous.lean
- \- *lemma* left_ord_continuous.coe_to_le_order_embedding
- \+ *lemma* left_ord_continuous.coe_to_le_rel_embedding
- \- *lemma* left_ord_continuous.coe_to_lt_order_embedding
- \+ *lemma* left_ord_continuous.coe_to_lt_rel_embedding
- \- *def* left_ord_continuous.to_le_order_embedding
- \+ *def* left_ord_continuous.to_le_rel_embedding
- \- *def* left_ord_continuous.to_lt_order_embedding
- \+ *def* left_ord_continuous.to_lt_rel_embedding
- \- *lemma* right_ord_continuous.coe_to_le_order_embedding
- \+ *lemma* right_ord_continuous.coe_to_le_rel_embedding
- \- *lemma* right_ord_continuous.coe_to_lt_order_embedding
- \+ *lemma* right_ord_continuous.coe_to_lt_rel_embedding
- \- *def* right_ord_continuous.to_le_order_embedding
- \+ *def* right_ord_continuous.to_le_rel_embedding
- \- *def* right_ord_continuous.to_lt_order_embedding
- \+ *def* right_ord_continuous.to_lt_rel_embedding

Deleted src/order/order_iso.lean
- \- *def* fin.val.order_embedding
- \- *def* fin_fin.order_embedding
- \- *lemma* injective_of_increasing
- \- *def* order_embedding.cod_restrict
- \- *theorem* order_embedding.cod_restrict_apply
- \- *theorem* order_embedding.coe_fn_inj
- \- *theorem* order_embedding.coe_fn_mk
- \- *theorem* order_embedding.coe_fn_to_embedding
- \- *theorem* order_embedding.eq_preimage
- \- *theorem* order_embedding.injective
- \- *lemma* order_embedding.le_map_sup
- \- *def* order_embedding.lt_embedding_of_le_embedding
- \- *lemma* order_embedding.map_inf_le
- \- *def* order_embedding.of_monotone
- \- *theorem* order_embedding.of_monotone_coe
- \- *theorem* order_embedding.ord
- \- *def* order_embedding.preimage
- \- *theorem* order_embedding.refl_apply
- \- *def* order_embedding.rsymm
- \- *theorem* order_embedding.trans_apply
- \- *structure* order_embedding
- \- *lemma* order_iso.apply_inv_self
- \- *theorem* order_iso.apply_symm_apply
- \- *lemma* order_iso.coe_coe_fn
- \- *theorem* order_iso.coe_fn_injective
- \- *theorem* order_iso.coe_fn_mk
- \- *theorem* order_iso.coe_fn_symm_mk
- \- *theorem* order_iso.coe_fn_to_equiv
- \- *lemma* order_iso.coe_mul
- \- *lemma* order_iso.coe_one
- \- *theorem* order_iso.ext
- \- *lemma* order_iso.inv_apply_self
- \- *lemma* order_iso.map_bot
- \- *lemma* order_iso.map_inf
- \- *lemma* order_iso.map_sup
- \- *lemma* order_iso.map_top
- \- *lemma* order_iso.mul_apply
- \- *theorem* order_iso.of_surjective_coe
- \- *lemma* order_iso.ord''
- \- *theorem* order_iso.ord
- \- *def* order_iso.prod_lex_congr
- \- *theorem* order_iso.refl_apply
- \- *theorem* order_iso.rel_symm_apply
- \- *def* order_iso.rsymm
- \- *def* order_iso.sum_lex_congr
- \- *theorem* order_iso.symm_apply_apply
- \- *theorem* order_iso.symm_apply_rel
- \- *theorem* order_iso.to_equiv_injective
- \- *def* order_iso.to_order_embedding
- \- *lemma* order_iso.to_order_embedding_eq_coe
- \- *theorem* order_iso.trans_apply
- \- *structure* order_iso
- \- *theorem* preimage_equivalence
- \- *def* set_coe_embedding
- \- *theorem* subrel.order_embedding_apply
- \- *def* subrel
- \- *theorem* subrel_val

Modified src/order/order_iso_nat.lean
- \- *def* order_embedding.nat_gt
- \- *def* order_embedding.nat_lt
- \- *theorem* order_embedding.well_founded_iff_no_descending_seq
- \+ *def* rel_embedding.nat_gt
- \+ *def* rel_embedding.nat_lt
- \+ *theorem* rel_embedding.well_founded_iff_no_descending_seq

Added src/order/rel_iso.lean
- \+ *def* fin.val.rel_embedding
- \+ *def* fin_fin.rel_embedding
- \+ *lemma* injective_of_increasing
- \+ *theorem* preimage_equivalence
- \+ *def* rel_embedding.cod_restrict
- \+ *theorem* rel_embedding.cod_restrict_apply
- \+ *theorem* rel_embedding.coe_fn_inj
- \+ *theorem* rel_embedding.coe_fn_mk
- \+ *theorem* rel_embedding.coe_fn_to_embedding
- \+ *theorem* rel_embedding.eq_preimage
- \+ *theorem* rel_embedding.injective
- \+ *lemma* rel_embedding.le_map_sup
- \+ *def* rel_embedding.lt_embedding_of_le_embedding
- \+ *lemma* rel_embedding.map_inf_le
- \+ *theorem* rel_embedding.map_rel_iff
- \+ *def* rel_embedding.of_monotone
- \+ *theorem* rel_embedding.of_monotone_coe
- \+ *def* rel_embedding.preimage
- \+ *theorem* rel_embedding.refl_apply
- \+ *def* rel_embedding.rsymm
- \+ *theorem* rel_embedding.trans_apply
- \+ *structure* rel_embedding
- \+ *lemma* rel_iso.apply_inv_self
- \+ *theorem* rel_iso.apply_symm_apply
- \+ *lemma* rel_iso.coe_coe_fn
- \+ *theorem* rel_iso.coe_fn_injective
- \+ *theorem* rel_iso.coe_fn_mk
- \+ *theorem* rel_iso.coe_fn_symm_mk
- \+ *theorem* rel_iso.coe_fn_to_equiv
- \+ *lemma* rel_iso.coe_mul
- \+ *lemma* rel_iso.coe_one
- \+ *theorem* rel_iso.ext
- \+ *lemma* rel_iso.inv_apply_self
- \+ *lemma* rel_iso.map_bot
- \+ *lemma* rel_iso.map_inf
- \+ *lemma* rel_iso.map_rel_iff''
- \+ *theorem* rel_iso.map_rel_iff
- \+ *lemma* rel_iso.map_sup
- \+ *lemma* rel_iso.map_top
- \+ *lemma* rel_iso.mul_apply
- \+ *theorem* rel_iso.of_surjective_coe
- \+ *def* rel_iso.prod_lex_congr
- \+ *theorem* rel_iso.refl_apply
- \+ *theorem* rel_iso.rel_symm_apply
- \+ *def* rel_iso.rsymm
- \+ *def* rel_iso.sum_lex_congr
- \+ *theorem* rel_iso.symm_apply_apply
- \+ *theorem* rel_iso.symm_apply_rel
- \+ *theorem* rel_iso.to_equiv_injective
- \+ *def* rel_iso.to_rel_embedding
- \+ *lemma* rel_iso.to_rel_embedding_eq_coe
- \+ *theorem* rel_iso.trans_apply
- \+ *structure* rel_iso
- \+ *def* set_coe_embedding
- \+ *theorem* subrel.rel_embedding_apply
- \+ *def* subrel
- \+ *theorem* subrel_val

Modified src/order/semiconj_Sup.lean


Modified src/ring_theory/ideal/operations.lean
- \- *def* ideal.le_order_embedding_of_surjective
- \+ *def* ideal.le_rel_embedding_of_surjective
- \- *def* ideal.lt_order_embedding_of_surjective
- \+ *def* ideal.lt_rel_embedding_of_surjective
- \- *def* ideal.order_iso_of_bijective
- \- *def* ideal.order_iso_of_surjective
- \+ *def* ideal.rel_iso_of_bijective
- \+ *def* ideal.rel_iso_of_surjective

Modified src/ring_theory/localization.lean
- \- *def* localization_map.le_order_embedding
- \+ *def* localization_map.le_rel_embedding

Modified src/ring_theory/noetherian.lean


Modified src/set_theory/cardinal_ordinal.lean
- \- *def* cardinal.aleph'.order_iso
- \- *theorem* cardinal.aleph'.order_iso_coe
- \+ *def* cardinal.aleph'.rel_iso
- \+ *theorem* cardinal.aleph'.rel_iso_coe
- \+/\- *def* cardinal.aleph'
- \- *def* cardinal.aleph_idx.order_iso
- \- *theorem* cardinal.aleph_idx.order_iso_coe
- \+ *def* cardinal.aleph_idx.rel_iso
- \+ *theorem* cardinal.aleph_idx.rel_iso_coe

Modified src/set_theory/cofinality.lean
- \- *theorem* order_iso.cof.aux
- \- *theorem* order_iso.cof
- \+/\- *theorem* ordinal.cof_cof
- \+ *theorem* rel_iso.cof.aux
- \+ *theorem* rel_iso.cof

Modified src/set_theory/ordinal.lean
- \- *def* cardinal.ord.order_embedding
- \- *theorem* cardinal.ord.order_embedding_coe
- \+ *def* cardinal.ord.rel_embedding
- \+ *theorem* cardinal.ord.rel_embedding_coe
- \+/\- *def* initial_seg.antisymm
- \+/\- *theorem* initial_seg.coe_coe_fn
- \+/\- *theorem* initial_seg.coe_fn_mk
- \- *theorem* initial_seg.coe_fn_to_order_embedding
- \+ *theorem* initial_seg.coe_fn_to_rel_embedding
- \+/\- *def* initial_seg.of_iso
- \+/\- *structure* initial_seg
- \- *def* order_embedding.collapse
- \- *theorem* order_embedding.collapse_F.lt
- \- *theorem* order_embedding.collapse_F.not_lt
- \- *def* order_embedding.collapse_F
- \- *theorem* order_embedding.collapse_apply
- \- *lemma* ordinal.order_iso_enum'
- \- *lemma* ordinal.order_iso_enum
- \- *def* ordinal.order_iso_out
- \+ *lemma* ordinal.rel_iso_enum'
- \+ *lemma* ordinal.rel_iso_enum
- \+ *def* ordinal.rel_iso_out
- \+/\- *def* ordinal.typein_iso
- \+/\- *theorem* principal_seg.coe_coe_fn
- \+/\- *theorem* principal_seg.coe_fn_mk
- \- *theorem* principal_seg.coe_fn_to_order_embedding
- \+ *theorem* principal_seg.coe_fn_to_rel_embedding
- \+/\- *def* principal_seg.equiv_lt
- \+/\- *theorem* principal_seg.equiv_lt_apply
- \+/\- *theorem* principal_seg.equiv_lt_top
- \+/\- *structure* principal_seg
- \+ *def* rel_embedding.collapse
- \+ *theorem* rel_embedding.collapse_F.lt
- \+ *theorem* rel_embedding.collapse_F.not_lt
- \+ *def* rel_embedding.collapse_F
- \+ *theorem* rel_embedding.collapse_apply

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


Added src/category_theory/limits/fubini.lean
- \+ *def* category_theory.limits.cone_of_cone_uncurry
- \+ *def* category_theory.limits.cone_of_cone_uncurry_is_limit
- \+ *def* category_theory.limits.diagram_of_cones.cone_points
- \+ *def* category_theory.limits.diagram_of_cones.mk_of_has_limits
- \+ *lemma* category_theory.limits.diagram_of_cones.mk_of_has_limits_cone_points
- \+ *structure* category_theory.limits.diagram_of_cones
- \+ *def* category_theory.limits.limit_iso_limit_curry_comp_lim
- \+ *lemma* category_theory.limits.limit_iso_limit_curry_comp_lim_hom_π_π
- \+ *lemma* category_theory.limits.limit_iso_limit_curry_comp_lim_inv_π
- \+ *def* category_theory.limits.limit_uncurry_iso_limit_comp_lim
- \+ *lemma* category_theory.limits.limit_uncurry_iso_limit_comp_lim_hom_π_π
- \+ *lemma* category_theory.limits.limit_uncurry_iso_limit_comp_lim_inv_π

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
- \- *lemma* category_theory.is_equivalence.counit_inv_functor_comp
- \+ *lemma* category_theory.is_equivalence.inv_fun_id_inv_comp

Modified src/category_theory/limits/cones.lean
- \+ *def* category_theory.functor.map_cone_inv_map_cone



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
- \+ *def* affine.simplex.circumcenter
- \+ *def* affine.simplex.circumcenter_circumradius
- \+ *lemma* affine.simplex.circumcenter_circumradius_unique_dist_eq
- \+ *lemma* affine.simplex.circumcenter_mem_affine_span
- \+ *def* affine.simplex.circumradius
- \+ *lemma* affine.simplex.dist_circumcenter_eq_circumradius
- \+ *lemma* affine.simplex.eq_circumcenter_of_dist_eq
- \+ *lemma* affine.simplex.eq_circumradius_of_dist_eq
- \+ *lemma* euclidean_geometry.dist_eq_iff_dist_orthogonal_projection_eq
- \+ *lemma* euclidean_geometry.dist_set_eq_iff_dist_orthogonal_projection_eq
- \+ *lemma* euclidean_geometry.exists_dist_eq_iff_exists_dist_orthogonal_projection_eq
- \+ *lemma* euclidean_geometry.exists_unique_dist_eq_of_affine_independent
- \+ *lemma* euclidean_geometry.exists_unique_dist_eq_of_insert



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
- \- *theorem* char_p.char_is_prime_of_ge_two
- \+ *theorem* char_p.char_is_prime_of_two_le

Modified src/algebra/order_functions.lean
- \+/\- *lemma* max_le_add_of_nonneg
- \+/\- *lemma* min_le_add_of_nonneg_left
- \+/\- *lemma* min_le_add_of_nonneg_right

Modified src/data/nat/basic.lean
- \+/\- *theorem* nat.eq_of_mul_eq_mul_right

Modified src/data/nat/dist.lean
- \- *theorem* nat.dist_eq_sub_of_ge
- \+ *theorem* nat.dist_eq_sub_of_le_right

Modified src/data/num/lemmas.lean
- \+/\- *theorem* num.cmp_to_nat
- \+/\- *theorem* pos_num.cmp_to_nat
- \+/\- *theorem* pos_num.pred_to_nat
- \+/\- *theorem* znum.cmp_to_int

Modified src/data/padics/padic_numbers.lean
- \+/\- *lemma* padic.padic_norm_e_lim_le
- \+/\- *theorem* padic.rat_dense'
- \+/\- *theorem* padic.rat_dense
- \+/\- *lemma* padic_norm_e.defn
- \+/\- *lemma* padic_seq.norm_nonneg

Modified src/data/polynomial/degree/basic.lean
- \+/\- *lemma* polynomial.degree_eq_iff_nat_degree_eq_of_pos

Modified src/data/real/basic.lean
- \+/\- *lemma* real.le_of_forall_epsilon_le

Modified src/data/real/cau_seq.lean
- \+/\- *theorem* cau_seq.cauchy₂
- \+/\- *theorem* cau_seq.cauchy₃
- \+/\- *theorem* is_cau_seq.cauchy₂
- \+/\- *theorem* is_cau_seq.cauchy₃

Modified src/data/real/hyperreal.lean
- \+/\- *theorem* hyperreal.gt_of_neg_of_infinitesimal
- \+/\- *def* hyperreal.infinite_pos
- \+/\- *lemma* hyperreal.infinite_pos_def
- \+/\- *lemma* hyperreal.infinite_pos_iff_infinite_and_pos
- \+/\- *lemma* hyperreal.infinite_pos_iff_infinite_of_nonneg
- \+/\- *lemma* hyperreal.infinite_pos_iff_infinite_of_pos
- \+/\- *theorem* hyperreal.lt_neg_of_pos_of_infinitesimal
- \+/\- *theorem* hyperreal.lt_of_pos_of_infinitesimal
- \+/\- *lemma* hyperreal.pos_of_infinite_pos

Modified src/data/real/nnreal.lean
- \+/\- *lemma* nnreal.le_of_forall_epsilon_le
- \+/\- *lemma* nnreal.le_of_real_iff_coe_le
- \+/\- *lemma* nnreal.of_real_lt_iff_lt_coe

Modified src/order/basic.lean


Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* filter.map_div_at_top_eq_nat

Modified src/order/galois_connection.lean
- \+/\- *lemma* nat.galois_connection_mul_div

Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* ordinal.add_absorp_iff

Modified src/tactic/linarith/lemmas.lean
- \+/\- *lemma* linarith.mul_eq
- \+/\- *lemma* linarith.mul_neg
- \+/\- *lemma* linarith.mul_nonpos

Modified src/tactic/monotonicity/lemmas.lean
- \- *lemma* gt_of_mul_lt_mul_neg_right
- \+ *lemma* lt_of_mul_lt_mul_neg_right

Modified src/topology/algebra/ordered.lean
- \+/\- *theorem* gt_mem_sets_of_Liminf_gt

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/metric_space/hausdorff_distance.lean
- \+/\- *lemma* metric.Hausdorff_dist_le_of_inf_dist



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
- \- *def* list.find_indexes_aux



## [2020-08-15 20:41:54](https://github.com/leanprover-community/mathlib/commit/7f1a489)
fix(algebra/order): restore choiceless theorems ([#3799](https://github.com/leanprover-community/mathlib/pull/3799))
The classical_decidable linter commit made these choiceless proofs use choice
again, making them duplicates of other theorems not in the `decidable.`
namespace.
#### Estimated changes
Modified src/algebra/order.lean
- \+/\- *lemma* decidable.eq_or_lt_of_le
- \+/\- *lemma* decidable.le_iff_le_iff_lt_iff_lt
- \+/\- *lemma* decidable.le_iff_lt_or_eq
- \+/\- *lemma* decidable.le_imp_le_iff_lt_imp_lt
- \+/\- *lemma* decidable.le_imp_le_of_lt_imp_lt
- \+/\- *lemma* decidable.le_of_not_lt
- \+/\- *lemma* decidable.le_or_lt
- \+/\- *lemma* decidable.lt_or_eq_of_le
- \+/\- *lemma* decidable.lt_or_gt_of_ne
- \+/\- *lemma* decidable.lt_or_le
- \+/\- *lemma* decidable.lt_trichotomy
- \+/\- *lemma* decidable.ne_iff_lt_or_gt
- \+/\- *lemma* decidable.not_lt



## [2020-08-15 20:41:52](https://github.com/leanprover-community/mathlib/commit/2e890e6)
feat(category_theory/comma): constructing isos in the comma,over,under cats ([#3797](https://github.com/leanprover-community/mathlib/pull/3797))
Constructors to give isomorphisms in comma, over and under categories - essentially these just let you omit checking one of the commuting squares using the fact that the components are iso and the other square works.
#### Estimated changes
Modified src/category_theory/comma.lean
- \+ *def* category_theory.comma.iso_mk

Modified src/category_theory/over.lean
- \+/\- *def* category_theory.over.forget
- \+ *def* category_theory.over.iso_mk
- \+ *lemma* category_theory.over.iso_mk_hom_left
- \+ *lemma* category_theory.over.iso_mk_inv_left
- \- *lemma* category_theory.over.mk_hom
- \- *lemma* category_theory.over.mk_left
- \+/\- *def* category_theory.under.forget
- \+ *def* category_theory.under.iso_mk
- \+ *lemma* category_theory.under.iso_mk_hom_right
- \+ *lemma* category_theory.under.iso_mk_inv_right



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
- \+ *lemma* exists_subset_affine_independent_affine_span_eq_top
- \+ *lemma* linear_independent_set_iff_affine_independent_vadd_union_singleton



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
- \- *lemma* add_midpoint
- \+ *lemma* add_sub_div_two_lt
- \+ *lemma* div_le_div_of_le
- \+/\- *lemma* div_le_div_of_le_left
- \+/\- *lemma* div_le_div_of_le_of_nonneg
- \- *lemma* div_le_div_of_neg_of_le
- \+ *lemma* div_le_div_of_nonpos_of_le
- \- *lemma* div_le_div_of_pos_of_le
- \+ *lemma* div_le_iff_of_neg'
- \+ *lemma* div_le_iff_of_nonneg_of_le
- \- *lemma* div_le_of_le_mul
- \- *lemma* div_le_of_neg_of_mul_le
- \+ *lemma* div_le_one
- \- *lemma* div_le_one_iff_le
- \+ *lemma* div_le_one_of_neg
- \+ *lemma* div_lt_div_of_lt
- \+ *lemma* div_lt_div_of_lt_left
- \- *lemma* div_lt_div_of_pos_of_lt
- \- *lemma* div_lt_div_of_pos_of_lt_of_pos
- \+ *lemma* div_lt_iff_of_neg'
- \- *lemma* div_lt_of_neg_of_mul_lt
- \- *lemma* div_lt_of_pos_of_lt_mul
- \+ *lemma* div_lt_one
- \- *lemma* div_lt_one_iff_lt
- \+ *lemma* div_lt_one_of_neg
- \+ *lemma* div_mul_le_div_mul_of_div_le_div
- \- *lemma* div_mul_le_div_mul_of_div_le_div_nonneg
- \+/\- *lemma* div_two_lt_of_pos
- \+/\- *lemma* exists_add_lt_and_pos_of_lt
- \+/\- *lemma* half_pos
- \+/\- *lemma* inv_le_inv_of_le
- \+ *lemma* inv_le_inv_of_neg
- \+ *lemma* inv_le_of_neg
- \+ *lemma* inv_lt_inv_of_neg
- \+ *lemma* inv_lt_of_neg
- \+ *lemma* le_div_iff_of_neg'
- \- *lemma* le_div_of_mul_le
- \+ *lemma* le_inv_of_neg
- \- *lemma* le_mul_of_div_le
- \+/\- *lemma* le_of_forall_sub_le
- \+/\- *lemma* le_of_neg_of_one_div_le_one_div
- \+/\- *lemma* le_of_one_div_le_one_div
- \- *lemma* le_of_one_le_div
- \+ *lemma* le_one_div
- \+ *lemma* le_one_div_of_neg
- \+ *lemma* lt_div_iff_of_neg'
- \- *lemma* lt_div_of_mul_lt
- \+ *lemma* lt_inv_of_neg
- \+/\- *lemma* lt_of_neg_of_one_div_lt_one_div
- \+/\- *lemma* lt_of_one_div_lt_one_div
- \- *lemma* lt_of_one_lt_div
- \+ *lemma* lt_one_div
- \+ *lemma* lt_one_div_of_neg
- \+/\- *lemma* mul_le_mul_of_mul_div_le
- \- *lemma* mul_le_of_le_div
- \- *lemma* mul_le_of_neg_of_div_le
- \- *lemma* mul_lt_of_lt_div
- \- *lemma* mul_lt_of_neg_of_div_lt
- \+/\- *lemma* one_div_le_neg_one
- \+ *lemma* one_div_le_of_neg
- \- *lemma* one_div_le_of_neg_of_one_div_le
- \- *lemma* one_div_le_of_pos_of_one_div_le
- \+/\- *lemma* one_div_le_one_div_of_le
- \+ *lemma* one_div_le_one_div_of_neg
- \+/\- *lemma* one_div_le_one_div_of_neg_of_le
- \+/\- *lemma* one_div_lt_neg_one
- \+ *lemma* one_div_lt_of_neg
- \+/\- *lemma* one_div_lt_one_div_of_lt
- \+ *lemma* one_div_lt_one_div_of_neg
- \+/\- *lemma* one_div_lt_one_div_of_neg_of_lt
- \+ *lemma* one_le_div
- \- *lemma* one_le_div_iff_le
- \- *lemma* one_le_div_of_le
- \+ *lemma* one_le_div_of_neg
- \+/\- *lemma* one_le_inv
- \+/\- *lemma* one_le_one_div
- \+ *lemma* one_lt_div
- \- *lemma* one_lt_div_iff_lt
- \- *lemma* one_lt_div_of_lt
- \+ *lemma* one_lt_div_of_neg
- \+/\- *lemma* one_lt_one_div

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
- \+ *lemma* category_theory.limits.types.coprod
- \+ *lemma* category_theory.limits.types.coprod_desc
- \+ *lemma* category_theory.limits.types.coprod_inl
- \+ *lemma* category_theory.limits.types.coprod_inr
- \+ *lemma* category_theory.limits.types.coprod_map
- \+ *lemma* category_theory.limits.types.initial
- \+ *lemma* category_theory.limits.types.sigma
- \+ *lemma* category_theory.limits.types.sigma_desc
- \+ *lemma* category_theory.limits.types.sigma_map
- \+ *lemma* category_theory.limits.types.sigma_ι
- \+ *def* category_theory.limits.types.types_has_binary_coproducts
- \+ *def* category_theory.limits.types.types_has_coproducts
- \+ *def* category_theory.limits.types.types_has_initial



## [2020-08-15 19:14:07](https://github.com/leanprover-community/mathlib/commit/8ce00af)
feat(data/set/basic): pairwise_on for equality ([#3802](https://github.com/leanprover-community/mathlib/pull/3802))
Add another lemma about `pairwise_on`: if and only if `f` takes
pairwise equal values on `s`, there is some value it takes everywhere
on `s`.  This arose from discussion in [#3693](https://github.com/leanprover-community/mathlib/pull/3693).
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.pairwise_on_eq_iff_exists_eq



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
- \+ *lemma* finset.card_compl
- \+ *lemma* finset.card_le_univ
- \+ *lemma* finset.compl_eq_univ_sdiff



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
- \+/\- *def* finset.affine_combination
- \+ *lemma* finset.affine_combination_linear

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
- \- *theorem* is_algebra_tower.aeval_apply
- \- *lemma* is_algebra_tower.algebra.ext
- \- *theorem* is_algebra_tower.algebra_map_apply
- \- *theorem* is_algebra_tower.algebra_map_eq
- \- *theorem* is_algebra_tower.algebra_map_smul
- \- *theorem* is_algebra_tower.comap_eq
- \- *theorem* is_algebra_tower.of_algebra_map_eq
- \- *theorem* is_algebra_tower.range_under_adjoin
- \- *def* is_algebra_tower.restrict_base
- \- *lemma* is_algebra_tower.restrict_base_apply
- \- *theorem* is_algebra_tower.smul_left_comm
- \- *def* is_algebra_tower.to_alg_hom
- \- *lemma* is_algebra_tower.to_alg_hom_apply
- \- *abbreviation* is_algebra_tower
- \+ *theorem* is_scalar_tower.aeval_apply
- \+ *lemma* is_scalar_tower.algebra.ext
- \+ *theorem* is_scalar_tower.algebra_comap_eq
- \+ *theorem* is_scalar_tower.algebra_map_apply
- \+ *theorem* is_scalar_tower.algebra_map_eq
- \+ *theorem* is_scalar_tower.algebra_map_smul
- \+ *theorem* is_scalar_tower.of_algebra_map_eq
- \+ *theorem* is_scalar_tower.range_under_adjoin
- \+ *def* is_scalar_tower.restrict_base
- \+ *lemma* is_scalar_tower.restrict_base_apply
- \+ *theorem* is_scalar_tower.smul_left_comm
- \+ *def* is_scalar_tower.to_alg_hom
- \+ *lemma* is_scalar_tower.to_alg_hom_apply

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/integral_closure.lean
- \- *theorem* is_integral_of_is_algebra_tower
- \+ *theorem* is_integral_of_is_scalar_tower

Modified src/ring_theory/localization.lean
- \+/\- *lemma* fraction_map.comap_is_algebraic_iff



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
- \+ *lemma* pgame.move_left_left_moves_neg_symm
- \- *lemma* pgame.move_left_right_moves_neg_symm



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
- \+ *def* finset.cons
- \+ *theorem* finset.cons_eq_insert
- \+ *theorem* finset.cons_val
- \+ *def* finset.disj_union
- \+ *theorem* finset.disj_union_eq_union
- \+ *theorem* finset.mem_cons
- \+ *theorem* finset.mem_disj_union

Modified src/data/finset/pi.lean


Modified src/data/multiset/nodup.lean
- \+ *lemma* multiset.nodup_iff_pairwise

Modified src/data/sigma/basic.lean
- \+ *def* psigma.elim
- \+ *theorem* psigma.elim_val

Modified src/tactic/default.lean


Added src/tactic/derive_fintype.lean
- \+ *def* derive_fintype.finset_above.cons
- \+ *theorem* derive_fintype.finset_above.mem_cons_of_mem
- \+ *theorem* derive_fintype.finset_above.mem_cons_self
- \+ *theorem* derive_fintype.finset_above.mem_union_left
- \+ *theorem* derive_fintype.finset_above.mem_union_right
- \+ *def* derive_fintype.finset_above.nil
- \+ *def* derive_fintype.finset_above.union
- \+ *def* derive_fintype.finset_above
- \+ *theorem* derive_fintype.finset_in.mem_mk
- \+ *def* derive_fintype.finset_in.mk
- \+ *def* derive_fintype.finset_in
- \+ *def* derive_fintype.mk_fintype

Modified src/tactic/derive_inhabited.lean


Added test/derive_fintype.lean
- \+ *inductive* alphabet
- \+ *inductive* foo2
- \+ *inductive* foo3
- \+ *inductive* foo



## [2020-08-15 12:43:41](https://github.com/leanprover-community/mathlib/commit/18746ef)
feat(analysis/special_functions/pow): Added lemmas for rpow of neg exponent ([#3715](https://github.com/leanprover-community/mathlib/pull/3715))
I noticed that the library was missing some lemmas regarding the bounds of rpow of a negative exponent so I added them. I cleaned up the other similar preexisting lemmas for consistency. I then repeated the process for nnreal lemmas.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* nnreal.one_le_rpow_of_pos_of_le_one_of_nonpos
- \+ *lemma* nnreal.one_lt_rpow_of_pos_of_lt_one_of_neg
- \+ *lemma* nnreal.rpow_le_one_of_one_le_of_nonpos
- \+/\- *lemma* nnreal.rpow_lt_one
- \+ *lemma* nnreal.rpow_lt_one_of_one_lt_of_neg
- \+/\- *lemma* real.one_le_rpow
- \+ *lemma* real.one_le_rpow_of_pos_of_le_one_of_nonpos
- \+/\- *lemma* real.one_lt_rpow
- \+ *lemma* real.one_lt_rpow_of_pos_of_lt_one_of_neg
- \+/\- *lemma* real.rpow_le_one
- \+ *lemma* real.rpow_le_one_of_one_le_of_nonpos
- \+/\- *lemma* real.rpow_lt_one
- \+ *lemma* real.rpow_lt_one_of_one_lt_of_neg



## [2020-08-15 12:43:39](https://github.com/leanprover-community/mathlib/commit/099f070)
feat(topology/sheaves): the sheaf condition ([#3605](https://github.com/leanprover-community/mathlib/pull/3605))
Johan and I have been working with this, and it's at least minimally viable.
In follow-up PRs we have finished:
* constructing the sheaf of dependent functions to a type family
* constructing the sheaf of continuous functions to a fixed topological space
* checking the sheaf condition under forgetful functors that reflect isos and preserve limits (https://stacks.math.columbia.edu/tag/0073)
Obviously there's more we'd like to see before being confident that a design for sheaves is workable, but we'd like to get started!
#### Estimated changes
Added src/category_theory/limits/punit.lean
- \+ *def* category_theory.limits.punit_cocone_is_colimit
- \+ *def* category_theory.limits.punit_cone_is_limit

Modified src/topology/order.lean


Added src/topology/sheaves/sheaf.lean
- \+ *def* Top.sheaf.forget
- \+ *structure* Top.sheaf
- \+ *def* Top.sheaf_condition.diagram
- \+ *def* Top.sheaf_condition.fork
- \+ *lemma* Top.sheaf_condition.fork_X
- \+ *lemma* Top.sheaf_condition.fork_ι
- \+ *lemma* Top.sheaf_condition.fork_π_app_walking_parallel_pair_one
- \+ *lemma* Top.sheaf_condition.fork_π_app_walking_parallel_pair_zero
- \+ *def* Top.sheaf_condition.left_res
- \+ *def* Top.sheaf_condition.pi_inters
- \+ *def* Top.sheaf_condition.pi_opens
- \+ *def* Top.sheaf_condition.res
- \+ *def* Top.sheaf_condition.right_res
- \+ *lemma* Top.sheaf_condition.w
- \+ *def* Top.sheaf_condition
- \+ *def* Top.sheaf_condition_punit



## [2020-08-15 12:06:09](https://github.com/leanprover-community/mathlib/commit/36b4a1e)
refactor(algebra/add_torsor): use `out_param` ([#3727](https://github.com/leanprover-community/mathlib/pull/3727))
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \- *lemma* add_action.vadd_assoc
- \- *lemma* add_action.vadd_comm
- \- *lemma* add_action.vadd_left_cancel
- \- *lemma* add_action.vadd_left_cancel_iff
- \- *lemma* add_action.zero_vadd
- \- *lemma* add_torsor.eq_of_vsub_eq_zero
- \- *lemma* add_torsor.eq_vadd_iff_vsub_eq
- \- *lemma* add_torsor.neg_vsub_eq_vsub_rev
- \- *lemma* add_torsor.vadd_right_cancel
- \- *lemma* add_torsor.vadd_right_cancel_iff
- \- *lemma* add_torsor.vadd_vsub
- \- *lemma* add_torsor.vadd_vsub_assoc
- \- *lemma* add_torsor.vadd_vsub_vadd_cancel_left
- \- *lemma* add_torsor.vadd_vsub_vadd_cancel_right
- \- *lemma* add_torsor.vsub_add_vsub_cancel
- \- *lemma* add_torsor.vsub_eq_zero_iff_eq
- \- *lemma* add_torsor.vsub_left_cancel
- \- *lemma* add_torsor.vsub_left_cancel_iff
- \- *lemma* add_torsor.vsub_mem_vsub_set
- \- *lemma* add_torsor.vsub_right_cancel
- \- *lemma* add_torsor.vsub_right_cancel_iff
- \- *lemma* add_torsor.vsub_self
- \- *def* add_torsor.vsub_set
- \- *lemma* add_torsor.vsub_set_empty
- \- *lemma* add_torsor.vsub_set_finite_of_finite
- \- *lemma* add_torsor.vsub_set_mono
- \- *lemma* add_torsor.vsub_set_singleton
- \- *lemma* add_torsor.vsub_sub_vsub_cancel_left
- \- *lemma* add_torsor.vsub_sub_vsub_cancel_right
- \- *lemma* add_torsor.vsub_vadd
- \- *lemma* add_torsor.vsub_vadd_eq_vsub_sub
- \+ *lemma* eq_of_vsub_eq_zero
- \+ *lemma* eq_vadd_iff_vsub_eq
- \+ *lemma* neg_vsub_eq_vsub_rev
- \+ *lemma* vadd_assoc
- \+ *lemma* vadd_comm
- \+/\- *lemma* vadd_eq_add
- \+ *lemma* vadd_left_cancel
- \+ *lemma* vadd_left_cancel_iff
- \+ *lemma* vadd_right_cancel
- \+ *lemma* vadd_right_cancel_iff
- \+ *lemma* vadd_vsub
- \+ *lemma* vadd_vsub_assoc
- \+ *lemma* vadd_vsub_vadd_cancel_left
- \+ *lemma* vadd_vsub_vadd_cancel_right
- \+ *lemma* vsub_add_vsub_cancel
- \+/\- *lemma* vsub_eq_sub
- \+ *lemma* vsub_eq_zero_iff_eq
- \+ *lemma* vsub_left_cancel
- \+ *lemma* vsub_left_cancel_iff
- \+ *lemma* vsub_mem_vsub_set
- \+ *lemma* vsub_right_cancel
- \+ *lemma* vsub_right_cancel_iff
- \+ *lemma* vsub_self
- \+ *def* vsub_set
- \+ *lemma* vsub_set_empty
- \+ *lemma* vsub_set_finite_of_finite
- \+ *lemma* vsub_set_mono
- \+ *lemma* vsub_set_singleton
- \+ *lemma* vsub_sub_vsub_cancel_left
- \+ *lemma* vsub_sub_vsub_cancel_right
- \+ *lemma* vsub_vadd
- \+ *lemma* vsub_vadd_eq_vsub_sub
- \+ *lemma* zero_vadd

Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex.affine_image
- \+/\- *lemma* convex.affine_preimage
- \+/\- *lemma* convex.combo_affine_apply
- \+/\- *lemma* convex_on.comp_affine_map

Modified src/analysis/convex/extrema.lean


Modified src/analysis/normed_space/add_torsor.lean
- \- *lemma* add_torsor.dist_eq_norm
- \+ *lemma* dist_eq_norm_vsub
- \+/\- *lemma* dist_vadd_cancel_left
- \+/\- *lemma* dist_vadd_cancel_right
- \+/\- *lemma* isometric.coe_vadd_const
- \+/\- *lemma* isometric.coe_vadd_const_symm
- \- *lemma* isometric.isometry_vadd_vsub_of_isometry
- \+/\- *lemma* isometric.vadd_const_to_equiv
- \+ *lemma* isometry.vadd_vsub

Modified src/analysis/normed_space/mazur_ulam.lean
- \+/\- *lemma* isometric.coe_to_affine_map
- \+/\- *def* isometric.to_affine_map

Modified src/geometry/euclidean.lean
- \- *abbreviation* euclidean_affine_space
- \+/\- *lemma* euclidean_geometry.angle_add_angle_eq_pi_of_angle_eq_pi
- \+/\- *lemma* euclidean_geometry.angle_comm
- \+/\- *lemma* euclidean_geometry.angle_eq_angle_of_angle_eq_pi
- \+/\- *lemma* euclidean_geometry.angle_eq_left
- \+/\- *lemma* euclidean_geometry.angle_eq_of_ne
- \+/\- *lemma* euclidean_geometry.angle_eq_right
- \+/\- *lemma* euclidean_geometry.angle_eq_zero_of_angle_eq_pi_left
- \+/\- *lemma* euclidean_geometry.angle_eq_zero_of_angle_eq_pi_right
- \+/\- *lemma* euclidean_geometry.angle_le_pi
- \+/\- *lemma* euclidean_geometry.angle_nonneg
- \+/\- *lemma* euclidean_geometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi
- \+/\- *lemma* euclidean_geometry.dist_orthogonal_projection_eq_zero_iff
- \+/\- *lemma* euclidean_geometry.dist_orthogonal_projection_ne_zero_of_not_mem
- \+/\- *lemma* euclidean_geometry.dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd
- \+/\- *lemma* euclidean_geometry.inter_eq_singleton_orthogonal_projection
- \+/\- *lemma* euclidean_geometry.inter_eq_singleton_orthogonal_projection_fn
- \+/\- *def* euclidean_geometry.orthogonal_projection
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_eq_self_iff
- \+/\- *def* euclidean_geometry.orthogonal_projection_fn
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_fn_eq
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_fn_mem
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_fn_mem_orthogonal
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_fn_vsub_mem_direction_orthogonal
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_mem
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_mem_orthogonal
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_vadd_eq_self
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_vadd_smul_vsub_orthogonal_projection
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_vsub_mem_direction
- \+/\- *lemma* euclidean_geometry.orthogonal_projection_vsub_mem_direction_orthogonal
- \+/\- *lemma* euclidean_geometry.vsub_orthogonal_projection_mem_direction
- \+/\- *lemma* euclidean_geometry.vsub_orthogonal_projection_mem_direction_orthogonal

Modified src/linear_algebra/affine_space/basic.lean
- \+/\- *lemma* affine_map.add_linear
- \+/\- *lemma* affine_map.affine_apply_line_map
- \+/\- *lemma* affine_map.affine_comp_line_map
- \+/\- *lemma* affine_map.coe_add
- \+/\- *lemma* affine_map.coe_comp
- \+/\- *lemma* affine_map.coe_const
- \+/\- *lemma* affine_map.coe_homothety_hom
- \+/\- *lemma* affine_map.coe_id
- \+/\- *lemma* affine_map.coe_mul
- \+/\- *lemma* affine_map.coe_one
- \+/\- *lemma* affine_map.coe_smul
- \+/\- *lemma* affine_map.coe_zero
- \+/\- *def* affine_map.comp
- \+/\- *lemma* affine_map.comp_apply
- \+/\- *lemma* affine_map.comp_assoc
- \+/\- *lemma* affine_map.comp_id
- \+/\- *def* affine_map.const
- \+/\- *lemma* affine_map.const_linear
- \+/\- *lemma* affine_map.decomp'
- \+/\- *lemma* affine_map.decomp
- \+/\- *lemma* affine_map.ext
- \+/\- *lemma* affine_map.ext_iff
- \+/\- *def* affine_map.homothety
- \+/\- *def* affine_map.homothety_affine
- \+/\- *lemma* affine_map.homothety_apply
- \+/\- *def* affine_map.homothety_hom
- \+/\- *lemma* affine_map.homothety_one
- \+/\- *lemma* affine_map.homothety_zero
- \+/\- *def* affine_map.id
- \+/\- *lemma* affine_map.id_apply
- \+/\- *lemma* affine_map.id_comp
- \+/\- *lemma* affine_map.id_linear
- \+/\- *def* affine_map.line_map
- \+/\- *lemma* affine_map.line_map_zero
- \+/\- *lemma* affine_map.linear_map_vsub
- \+/\- *lemma* affine_map.map_vadd
- \+/\- *lemma* affine_map.to_fun_eq_coe
- \+/\- *lemma* affine_map.vadd_apply
- \+/\- *lemma* affine_map.vsub_apply
- \+/\- *lemma* affine_map.zero_linear
- \+/\- *structure* affine_map
- \- *lemma* affine_space.affine_span_nonempty
- \- *lemma* affine_space.mem_span_points
- \- *def* affine_space.span_points
- \- *lemma* affine_space.span_points_nonempty
- \- *lemma* affine_space.subset_span_points
- \- *lemma* affine_space.vadd_mem_span_points_of_mem_span_points_of_mem_vector_span
- \- *def* affine_space.vector_span
- \- *lemma* affine_space.vector_span_def
- \- *lemma* affine_space.vector_span_empty
- \- *lemma* affine_space.vector_span_eq_span_vsub_set_left
- \- *lemma* affine_space.vector_span_eq_span_vsub_set_right
- \- *lemma* affine_space.vector_span_range_eq_span_range_vsub_left
- \- *lemma* affine_space.vector_span_range_eq_span_range_vsub_right
- \- *lemma* affine_space.vector_span_singleton
- \- *lemma* affine_space.vsub_mem_vector_span
- \- *lemma* affine_space.vsub_mem_vector_span_of_mem_span_points_of_mem_span_points
- \- *lemma* affine_space.vsub_set_subset_vector_span
- \- *abbreviation* affine_space
- \+/\- *def* affine_span
- \+ *lemma* affine_span_nonempty
- \+/\- *lemma* affine_subspace.affine_span_coe
- \+/\- *lemma* affine_subspace.affine_span_eq_Inf
- \+/\- *lemma* affine_subspace.bot_coe
- \+/\- *lemma* affine_subspace.coe_affine_span_singleton
- \+/\- *lemma* affine_subspace.coe_direction_eq_vsub_set
- \+/\- *lemma* affine_subspace.coe_direction_eq_vsub_set_left
- \+/\- *lemma* affine_subspace.coe_direction_eq_vsub_set_right
- \+/\- *def* affine_subspace.direction
- \+/\- *lemma* affine_subspace.direction_affine_span_insert
- \+/\- *lemma* affine_subspace.direction_bot
- \+/\- *lemma* affine_subspace.direction_eq_vector_span
- \+/\- *lemma* affine_subspace.direction_inf
- \+/\- *lemma* affine_subspace.direction_le
- \+/\- *lemma* affine_subspace.direction_lt_of_nonempty
- \+/\- *def* affine_subspace.direction_of_nonempty
- \+/\- *lemma* affine_subspace.direction_of_nonempty_eq_direction
- \+/\- *lemma* affine_subspace.direction_sup
- \+/\- *lemma* affine_subspace.direction_top
- \+/\- *lemma* affine_subspace.exists_of_lt
- \+/\- *lemma* affine_subspace.ext
- \+/\- *lemma* affine_subspace.ext_of_direction_eq
- \+/\- *lemma* affine_subspace.inf_coe
- \+/\- *lemma* affine_subspace.inter_eq_singleton_of_nonempty_of_is_compl
- \+/\- *lemma* affine_subspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top
- \+/\- *lemma* affine_subspace.le_def'
- \+/\- *lemma* affine_subspace.le_def
- \+/\- *lemma* affine_subspace.lt_def
- \+/\- *lemma* affine_subspace.lt_iff_le_and_exists
- \+/\- *lemma* affine_subspace.mem_affine_span_insert_iff
- \+/\- *lemma* affine_subspace.mem_coe
- \+/\- *lemma* affine_subspace.mem_direction_iff_eq_vsub
- \+/\- *lemma* affine_subspace.mem_direction_iff_eq_vsub_left
- \+/\- *lemma* affine_subspace.mem_direction_iff_eq_vsub_right
- \+/\- *lemma* affine_subspace.mem_inf_iff
- \+/\- *lemma* affine_subspace.mem_top
- \+/\- *def* affine_subspace.mk'
- \+/\- *lemma* affine_subspace.mk'_eq
- \+/\- *lemma* affine_subspace.not_le_iff_exists
- \+/\- *lemma* affine_subspace.not_mem_bot
- \+/\- *lemma* affine_subspace.span_empty
- \+/\- *lemma* affine_subspace.span_points_subset_coe_of_subset_coe
- \+/\- *lemma* affine_subspace.span_union
- \+/\- *lemma* affine_subspace.span_univ
- \+/\- *lemma* affine_subspace.sup_direction_le
- \+/\- *lemma* affine_subspace.sup_direction_lt_of_nonempty_of_inter_empty
- \+/\- *lemma* affine_subspace.top_coe
- \+/\- *lemma* affine_subspace.vadd_mem_of_mem_direction
- \+/\- *lemma* affine_subspace.vsub_left_mem_direction_iff_mem
- \+/\- *lemma* affine_subspace.vsub_mem_direction
- \+/\- *lemma* affine_subspace.vsub_right_mem_direction_iff_mem
- \+/\- *structure* affine_subspace
- \+/\- *lemma* direction_affine_span
- \+/\- *def* linear_map.to_affine_map
- \+/\- *lemma* mem_affine_span
- \+ *lemma* mem_span_points
- \+ *def* span_points
- \+ *lemma* span_points_nonempty
- \+ *lemma* subset_span_points
- \+ *lemma* vadd_mem_span_points_of_mem_span_points_of_mem_vector_span
- \+ *def* vector_span
- \+ *lemma* vector_span_def
- \+ *lemma* vector_span_empty
- \+ *lemma* vector_span_eq_span_vsub_set_left
- \+ *lemma* vector_span_eq_span_vsub_set_right
- \+ *lemma* vector_span_range_eq_span_range_vsub_left
- \+ *lemma* vector_span_range_eq_span_range_vsub_right
- \+ *lemma* vector_span_singleton
- \+ *lemma* vsub_mem_vector_span
- \+ *lemma* vsub_mem_vector_span_of_mem_span_points_of_mem_span_points
- \+ *lemma* vsub_set_subset_vector_span

Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* affine_combination_mem_affine_span
- \+/\- *def* affine_map.weighted_vsub_of_point
- \- *lemma* affine_space.affine_combination_mem_affine_span
- \- *lemma* affine_space.eq_affine_combination_of_mem_affine_span
- \- *lemma* affine_space.mem_affine_span_iff_eq_affine_combination
- \- *lemma* affine_space.mem_vector_span_iff_eq_weighted_vsub
- \- *lemma* affine_space.weighted_vsub_mem_vector_span
- \+ *lemma* eq_affine_combination_of_mem_affine_span
- \+ *lemma* mem_affine_span_iff_eq_affine_combination
- \+ *lemma* mem_vector_span_iff_eq_weighted_vsub
- \+ *lemma* weighted_vsub_mem_vector_span

Modified src/linear_algebra/affine_space/finite_dimensional.lean
- \- *lemma* affine_space.finite_dimensional_direction_affine_span_of_finite
- \- *lemma* affine_space.finite_dimensional_vector_span_of_finite
- \+ *lemma* finite_dimensional_direction_affine_span_of_finite
- \+ *lemma* finite_dimensional_vector_span_of_finite

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine.simplex.ext
- \+ *lemma* affine.simplex.ext_iff
- \+ *def* affine.simplex.face
- \+ *lemma* affine.simplex.face_eq_mk_of_point
- \+ *lemma* affine.simplex.face_points
- \+ *def* affine.simplex.mk_of_point
- \+ *lemma* affine.simplex.mk_of_point_points
- \+ *structure* affine.simplex
- \+ *abbreviation* affine.triangle
- \- *lemma* affine_space.simplex.ext
- \- *lemma* affine_space.simplex.ext_iff
- \- *def* affine_space.simplex.face
- \- *lemma* affine_space.simplex.face_eq_mk_of_point
- \- *lemma* affine_space.simplex.face_points
- \- *def* affine_space.simplex.mk_of_point
- \- *lemma* affine_space.simplex.mk_of_point_points
- \- *structure* affine_space.simplex
- \- *abbreviation* affine_space.triangle

Modified src/topology/algebra/affine.lean
- \+/\- *lemma* affine_map.continuous_iff



## [2020-08-15 10:36:54](https://github.com/leanprover-community/mathlib/commit/2b8ece6)
feat(data/nat/basic): one mod two or higher is one ([#3763](https://github.com/leanprover-community/mathlib/pull/3763))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.one_mod



## [2020-08-15 10:09:19](https://github.com/leanprover-community/mathlib/commit/c444a00)
Revert "chore(ring_theory): delete `is_algebra_tower`"
This reverts commit c956ce1516ccfb3139ae3ebde7ede9c678d81968.
#### Estimated changes
Modified src/field_theory/algebraic_closure.lean


Modified src/field_theory/splitting_field.lean


Modified src/field_theory/tower.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/algebra_tower.lean
- \+ *theorem* is_algebra_tower.aeval_apply
- \+ *lemma* is_algebra_tower.algebra.ext
- \+ *theorem* is_algebra_tower.algebra_map_apply
- \+ *theorem* is_algebra_tower.algebra_map_eq
- \+ *theorem* is_algebra_tower.algebra_map_smul
- \+ *theorem* is_algebra_tower.comap_eq
- \+ *theorem* is_algebra_tower.of_algebra_map_eq
- \+ *theorem* is_algebra_tower.range_under_adjoin
- \+ *def* is_algebra_tower.restrict_base
- \+ *lemma* is_algebra_tower.restrict_base_apply
- \+ *theorem* is_algebra_tower.smul_left_comm
- \+ *def* is_algebra_tower.to_alg_hom
- \+ *lemma* is_algebra_tower.to_alg_hom_apply
- \+ *abbreviation* is_algebra_tower
- \- *theorem* is_scalar_tower.aeval_apply
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

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/integral_closure.lean
- \+ *theorem* is_integral_of_is_algebra_tower
- \- *theorem* is_integral_of_is_scalar_tower

Modified src/ring_theory/localization.lean
- \+/\- *lemma* fraction_map.comap_is_algebraic_iff



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
- \- *theorem* is_algebra_tower.aeval_apply
- \- *lemma* is_algebra_tower.algebra.ext
- \- *theorem* is_algebra_tower.algebra_map_apply
- \- *theorem* is_algebra_tower.algebra_map_eq
- \- *theorem* is_algebra_tower.algebra_map_smul
- \- *theorem* is_algebra_tower.comap_eq
- \- *theorem* is_algebra_tower.of_algebra_map_eq
- \- *theorem* is_algebra_tower.range_under_adjoin
- \- *def* is_algebra_tower.restrict_base
- \- *lemma* is_algebra_tower.restrict_base_apply
- \- *theorem* is_algebra_tower.smul_left_comm
- \- *def* is_algebra_tower.to_alg_hom
- \- *lemma* is_algebra_tower.to_alg_hom_apply
- \- *abbreviation* is_algebra_tower
- \+ *theorem* is_scalar_tower.aeval_apply
- \+ *lemma* is_scalar_tower.algebra.ext
- \+ *theorem* is_scalar_tower.algebra_comap_eq
- \+ *theorem* is_scalar_tower.algebra_map_apply
- \+ *theorem* is_scalar_tower.algebra_map_eq
- \+ *theorem* is_scalar_tower.algebra_map_smul
- \+ *theorem* is_scalar_tower.of_algebra_map_eq
- \+ *theorem* is_scalar_tower.range_under_adjoin
- \+ *def* is_scalar_tower.restrict_base
- \+ *lemma* is_scalar_tower.restrict_base_apply
- \+ *theorem* is_scalar_tower.smul_left_comm
- \+ *def* is_scalar_tower.to_alg_hom
- \+ *lemma* is_scalar_tower.to_alg_hom_apply

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/integral_closure.lean
- \- *theorem* is_integral_of_is_algebra_tower
- \+ *theorem* is_integral_of_is_scalar_tower

Modified src/ring_theory/localization.lean
- \+/\- *lemma* fraction_map.comap_is_algebraic_iff



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
- \+/\- *theorem* list.tfae.out



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
- \+ *lemma* filter.mem_prod_self_iff

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.prod_eq

Modified src/order/filter/lift.lean
- \+/\- *lemma* filter.prod_def
- \+/\- *lemma* filter.prod_same_eq

Modified src/topology/algebra/group.lean
- \+/\- *lemma* add_group_with_zero_nhd.add_Z
- \+/\- *lemma* add_group_with_zero_nhd.exists_Z_half

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
- \+ *theorem* asymptotics.is_o.add_add

Modified src/data/set/basic.lean
- \+ *lemma* set.forall_prod_set
- \+/\- *theorem* set.mem_powerset_iff
- \+ *theorem* set.monotone_powerset
- \+ *theorem* set.powerset_empty
- \+ *theorem* set.powerset_inter
- \+/\- *theorem* set.powerset_mono
- \+/\- *theorem* set.powerset_nonempty

Modified src/data/set/intervals/disjoint.lean
- \+/\- *lemma* set.Ico_disjoint_Ico
- \+/\- *lemma* set.Ico_disjoint_Ico_same
- \+ *lemma* set.Iic_disjoint_Ioc
- \+ *lemma* set.Iic_disjoint_Ioi
- \+/\- *lemma* set.Ioc_disjoint_Ioc
- \+/\- *lemma* set.Ioc_disjoint_Ioc_same

Modified src/data/set/intervals/ord_connected.lean
- \+ *lemma* set.ord_connected_singleton

Modified src/order/filter/basic.lean
- \+ *theorem* filter.comap_pure
- \+ *lemma* filter.eventually_pure
- \+ *lemma* filter.principal_singleton
- \- *lemma* filter.pure_eq_principal
- \+ *lemma* filter.pure_le_iff
- \+ *lemma* filter.tendsto_iff_eventually
- \+/\- *lemma* filter.tendsto_infi
- \+/\- *lemma* filter.tendsto_principal
- \+/\- *lemma* filter.tendsto_principal_principal
- \+/\- *lemma* filter.tendsto_pure
- \+ *lemma* filter.tendsto_pure_left

Modified src/order/filter/lift.lean
- \+ *lemma* filter.lift'_bot
- \+ *lemma* filter.lift'_inf
- \+ *lemma* filter.lift'_inf_powerset
- \+ *lemma* filter.lift'_pure
- \+ *lemma* filter.tendsto_lift'_powerset_mono

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


Added src/tactic/find_unused.lean


Added test/find_unused_decl1.lean
- \+ *def* main_thing
- \+ *def* this_is_unused

Added test/find_unused_decl2.lean
- \+ *def* my_list
- \+ *def* other_val
- \+ *def* some_val
- \+ *def* unused1
- \+ *inductive* unused_type
- \+ *def* used_somewhere_else



## [2020-08-13 19:36:30](https://github.com/leanprover-community/mathlib/commit/28dfad8)
feat(ideals,submonoids,subgroups): mem_sup(r) and mem_inf(i) lemmas ([#3697](https://github.com/leanprover-community/mathlib/pull/3697))
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.mem_Sup_of_mem
- \+ *lemma* subgroup.mem_sup_left
- \+ *lemma* subgroup.mem_sup_right
- \+ *lemma* subgroup.mem_supr_of_mem

Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* submonoid.mem_Sup_of_mem
- \+ *lemma* submonoid.mem_sup_left
- \+ *lemma* submonoid.mem_sup_right
- \+ *lemma* submonoid.mem_supr_of_mem

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.mem_Sup_of_mem
- \+ *lemma* submodule.mem_sup_left
- \+ *lemma* submodule.mem_sup_right
- \+/\- *lemma* submodule.mem_supr_of_mem

Modified src/linear_algebra/finsupp.lean


Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* ideal.mem_Sup_of_mem
- \+ *lemma* ideal.mem_inf
- \+ *lemma* ideal.mem_infi
- \+ *lemma* ideal.mem_sup_left
- \+ *lemma* ideal.mem_sup_right
- \+ *lemma* ideal.mem_supr_of_mem



## [2020-08-13 18:09:00](https://github.com/leanprover-community/mathlib/commit/4cc094b)
chore(data/int/basic): norm_cast attribute on int.coe_nat_mod ([#3765](https://github.com/leanprover-community/mathlib/pull/3765))
#### Estimated changes
Modified src/data/int/basic.lean
- \+/\- *theorem* int.coe_nat_mod



## [2020-08-13 14:29:54](https://github.com/leanprover-community/mathlib/commit/c66ecd3)
feat(intervals/image_preimage): preimage under multiplication ([#3757](https://github.com/leanprover-community/mathlib/pull/3757))
Add lemmas `preimage_mul_const_Ixx` and `preimage_const_mul_Ixx`.
Also generalize `equiv.mul_left` and `equiv.mul_right` to `units`.
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *lemma* lt_div_iff_of_neg

Modified src/data/equiv/mul_add.lean
- \+/\- *def* to_units
- \+ *lemma* units.coe_mul_left
- \+ *lemma* units.coe_mul_right
- \+ *def* units.mul_left
- \+ *lemma* units.mul_left_symm
- \+ *def* units.mul_right
- \+ *lemma* units.mul_right_symm

Modified src/data/set/intervals/image_preimage.lean
- \+ *lemma* set.preimage_const_mul_Icc
- \+ *lemma* set.preimage_const_mul_Icc_of_neg
- \+ *lemma* set.preimage_const_mul_Ici
- \+ *lemma* set.preimage_const_mul_Ici_of_neg
- \+ *lemma* set.preimage_const_mul_Ico
- \+ *lemma* set.preimage_const_mul_Ico_of_neg
- \+ *lemma* set.preimage_const_mul_Iic
- \+ *lemma* set.preimage_const_mul_Iic_of_neg
- \+ *lemma* set.preimage_const_mul_Iio
- \+ *lemma* set.preimage_const_mul_Iio_of_neg
- \+ *lemma* set.preimage_const_mul_Ioc
- \+ *lemma* set.preimage_const_mul_Ioc_of_neg
- \+ *lemma* set.preimage_const_mul_Ioi
- \+ *lemma* set.preimage_const_mul_Ioi_of_neg
- \+ *lemma* set.preimage_const_mul_Ioo
- \+ *lemma* set.preimage_const_mul_Ioo_of_neg
- \+ *lemma* set.preimage_mul_const_Icc
- \+ *lemma* set.preimage_mul_const_Icc_of_neg
- \+ *lemma* set.preimage_mul_const_Ici
- \+ *lemma* set.preimage_mul_const_Ici_of_neg
- \+ *lemma* set.preimage_mul_const_Ico
- \+ *lemma* set.preimage_mul_const_Ico_of_neg
- \+ *lemma* set.preimage_mul_const_Iic
- \+ *lemma* set.preimage_mul_const_Iic_of_neg
- \+ *lemma* set.preimage_mul_const_Iio
- \+ *lemma* set.preimage_mul_const_Iio_of_neg
- \+ *lemma* set.preimage_mul_const_Ioc
- \+ *lemma* set.preimage_mul_const_Ioc_of_neg
- \+ *lemma* set.preimage_mul_const_Ioi
- \+ *lemma* set.preimage_mul_const_Ioi_of_neg
- \+ *lemma* set.preimage_mul_const_Ioo
- \+ *lemma* set.preimage_mul_const_Ioo_of_neg

Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/group_theory/group_action.lean




## [2020-08-13 12:59:37](https://github.com/leanprover-community/mathlib/commit/f912f18)
feat(ci): auto label merge conflicts ([#3761](https://github.com/leanprover-community/mathlib/pull/3761))
#### Estimated changes
Added .github/workflows/merge_conflicts.yml




## [2020-08-13 12:59:35](https://github.com/leanprover-community/mathlib/commit/34352c2)
refactor(algebra/associated): change several instances from [integral_domain] to [comm_cancel_monoid_with_zero] ([#3744](https://github.com/leanprover-community/mathlib/pull/3744))
defines `comm_cancel_monoid_with_zero`
replaces some `integral_domain` instances with `comm_cancel_monoid_with_zero`
prepares the API for refactoring `normalization_domain`, `gcd_domain`, and `unique_factorization_domain` to monoids
#### Estimated changes
Modified src/algebra/associated.lean
- \+/\- *lemma* associated_mul_left_cancel
- \+/\- *lemma* associated_mul_right_cancel
- \+/\- *theorem* associates.prod_eq_zero_iff
- \+/\- *lemma* dvd_and_not_dvd_iff
- \+/\- *lemma* exists_associated_mem_of_dvd_prod
- \+/\- *lemma* irreducible_of_prime
- \+/\- *lemma* pow_dvd_pow_iff
- \+/\- *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul

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
- \+ *lemma* finset.prod_subset_one_on_sdiff

Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.map_comp
- \+ *lemma* polynomial.map_sum
- \+ *lemma* polynomial.support_map_subset



## [2020-08-13 11:32:00](https://github.com/leanprover-community/mathlib/commit/ac2f011)
feat(data/*): Add sizeof lemmas. ([#3745](https://github.com/leanprover-community/mathlib/pull/3745))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* finset.sizeof_lt_sizeof_of_mem

Modified src/data/list/basic.lean
- \+ *theorem* list.sizeof_lt_sizeof_of_mem

Modified src/data/list/perm.lean
- \+ *theorem* list.perm.sizeof_eq_sizeof

Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.sizeof_lt_sizeof_of_mem



## [2020-08-13 11:01:00](https://github.com/leanprover-community/mathlib/commit/b1e56a2)
feat(analysis/special_functions/trigonometric): Added lemma cos_ne_zero_iff ([#3743](https://github.com/leanprover-community/mathlib/pull/3743))
I added the theorem `cos_ne_zero_iff`, a corollary to the preexisting theorem `cos_eq_zero_iff`
<!-- put comments you want to keep out of the PR commit here -->
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *theorem* real.cos_ne_zero_iff



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
- \+ *lemma* fintype.prod_bool

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
- \+ *lemma* differentiable.const_smul_algebra
- \+ *lemma* differentiable.smul_algebra
- \+ *lemma* differentiable.smul_algebra_const
- \+ *lemma* differentiable_at.const_smul_algebra
- \+ *lemma* differentiable_at.smul_algebra
- \+ *lemma* differentiable_at.smul_algebra_const
- \+ *lemma* differentiable_on.const_smul_algebra
- \+ *lemma* differentiable_on.smul_algebra
- \+ *lemma* differentiable_on.smul_algebra_const
- \+ *lemma* differentiable_within_at.const_smul_algebra
- \+ *lemma* differentiable_within_at.smul_algebra
- \+ *lemma* differentiable_within_at.smul_algebra_const
- \+ *lemma* fderiv_const_smul_algebra
- \+ *lemma* fderiv_smul_algebra
- \+ *lemma* fderiv_smul_algebra_const
- \+ *lemma* fderiv_within_const_smul_algebra
- \+ *lemma* fderiv_within_smul_algebra
- \+ *lemma* fderiv_within_smul_algebra_const
- \+ *theorem* has_fderiv_at.const_smul_algebra
- \+ *theorem* has_fderiv_at.smul_algebra
- \+ *theorem* has_fderiv_at.smul_algebra_const
- \+ *theorem* has_fderiv_at_filter.const_smul_algebra
- \+ *theorem* has_fderiv_within_at.const_smul_algebra
- \+ *theorem* has_fderiv_within_at.smul_algebra
- \+ *theorem* has_fderiv_within_at.smul_algebra_const
- \+ *theorem* has_strict_fderiv_at.const_smul_algebra
- \+ *theorem* has_strict_fderiv_at.smul_algebra
- \+ *theorem* has_strict_fderiv_at.smul_algebra_const

Modified src/analysis/complex/basic.lean


Modified src/analysis/normed_space/basic.lean
- \+ *def* normed_space.restrict_scalars'
- \- *def* normed_space.restrict_scalars

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* is_bounded_bilinear_map_smul_algebra

Modified src/analysis/normed_space/hahn_banach.lean


Modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* continuous_linear_map.has_sum
- \+/\- *lemma* continuous_linear_map.has_sum_of_summable
- \+/\- *def* continuous_linear_map.restrict_scalars
- \+ *def* continuous_linear_map.smul_algebra_right
- \+ *theorem* continuous_linear_map.smul_algebra_right_apply

Modified src/data/complex/module.lean


Modified src/ring_theory/algebra.lean
- \+ *def* smul_algebra_right
- \+ *theorem* smul_algebra_right_apply
- \+ *lemma* smul_algebra_smul
- \+ *lemma* smul_algebra_smul_comm



## [2020-08-13 09:22:52](https://github.com/leanprover-community/mathlib/commit/cfcbea6)
feat(data/list/palindrome): define palindromes ([#3729](https://github.com/leanprover-community/mathlib/pull/3729))
This introduces an inductive type `palindrome`, with conversions to and from the proposition `reverse l = l`.
Review of this PR indicates two things: (1) maybe the name `is_palindrome` is better, especially if we define the subtype of palindromic lists; (2) maybe defining palindrome by `reverse l = l` is simpler. We note these for future development.
#### Estimated changes
Added src/data/list/palindrome.lean
- \+ *lemma* palindrome.append_reverse
- \+ *lemma* palindrome.iff_reverse_eq
- \+ *lemma* palindrome.of_reverse_eq
- \+ *lemma* palindrome.reverse_eq
- \+ *inductive* palindrome



## [2020-08-13 07:52:35](https://github.com/leanprover-community/mathlib/commit/c503b7a)
feat(algebra/order): more lemmas for projection notation ([#3753](https://github.com/leanprover-community/mathlib/pull/3753))
Also import `tactic.lint` and ensure that the linter passes
Move `ge_of_eq` to this file
#### Estimated changes
Modified src/algebra/order.lean
- \+ *lemma* eq.trans_le
- \+/\- *lemma* ge_iff_le
- \+ *theorem* ge_of_eq
- \+/\- *lemma* gt_iff_lt
- \+ *lemma* has_le.le.trans_eq
- \+/\- *lemma* le_implies_le_of_le_of_le
- \+ *lemma* le_rfl

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
- \+ *lemma* nnreal.one_div
- \- *lemma* nnreal.one_div_eq_inv

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
Added CODE_OF_CONDUCT.md




## [2020-08-12 15:04:27](https://github.com/leanprover-community/mathlib/commit/eb4b2a0)
feat(field_theory/algebraic_closure): algebraic closure ([#3733](https://github.com/leanprover-community/mathlib/pull/3733))
```lean
instance : is_alg_closed (algebraic_closure k) :=
```
TODO: Show that any algebraic extension embeds into any algebraically closed extension (via Zorn's lemma).
#### Estimated changes
Modified src/algebra/direct_limit.lean
- \+ *theorem* ring.direct_limit.polynomial.exists_of

Modified src/data/mv_polynomial.lean
- \+ *theorem* mv_polynomial.algebra_map_eq

Modified src/data/polynomial/field_division.lean
- \+ *theorem* polynomial.degree_pos_of_irreducible
- \+ *theorem* polynomial.monic_map_iff
- \+ *theorem* polynomial.not_irreducible_C

Modified src/data/real/ennreal.lean


Added src/field_theory/algebraic_closure.lean
- \+ *theorem* algebraic_closure.adjoin_monic.algebra_map
- \+ *theorem* algebraic_closure.adjoin_monic.exists_root
- \+ *theorem* algebraic_closure.adjoin_monic.is_integral
- \+ *def* algebraic_closure.adjoin_monic
- \+ *lemma* algebraic_closure.coe_to_step_of_le
- \+ *def* algebraic_closure.eval_X_self
- \+ *theorem* algebraic_closure.exists_of_step
- \+ *theorem* algebraic_closure.exists_root
- \+ *theorem* algebraic_closure.is_algebraic
- \+ *theorem* algebraic_closure.le_max_ideal
- \+ *def* algebraic_closure.max_ideal
- \+ *def* algebraic_closure.monic_irreducible
- \+ *def* algebraic_closure.of_step
- \+ *def* algebraic_closure.of_step_hom
- \+ *theorem* algebraic_closure.of_step_succ
- \+ *def* algebraic_closure.span_eval
- \+ *theorem* algebraic_closure.span_eval_ne_top
- \+ *theorem* algebraic_closure.step.is_integral
- \+ *def* algebraic_closure.step
- \+ *def* algebraic_closure.step_aux
- \+ *def* algebraic_closure.to_adjoin_monic
- \+ *def* algebraic_closure.to_splitting_field
- \+ *theorem* algebraic_closure.to_splitting_field_eval_X_self
- \+ *def* algebraic_closure.to_step_of_le
- \+ *theorem* algebraic_closure.to_step_succ.exists_root
- \+ *def* algebraic_closure.to_step_succ
- \+ *def* algebraic_closure.to_step_zero
- \+ *def* algebraic_closure
- \+ *theorem* is_alg_closed.of_exists_root
- \+ *def* is_alg_closure
- \+ *theorem* polynomial.splits'

Modified src/field_theory/splitting_field.lean
- \+ *theorem* polynomial.map_root_of_splits
- \+ *def* polynomial.root_of_splits
- \+ *theorem* polynomial.splits_of_is_unit

Modified src/order/directed.lean


Modified src/ring_theory/algebra.lean
- \+/\- *theorem* alg_hom.comp_algebra_map

Modified src/ring_theory/valuation/basic.lean




## [2020-08-12 10:41:14](https://github.com/leanprover-community/mathlib/commit/bfcf640)
feat(topology/opens): open_embedding_of_le ([#3597](https://github.com/leanprover-community/mathlib/pull/3597))
Add `lemma open_embedding_of_le {U V : opens α} (i : U ≤ V) : open_embedding (set.inclusion i)`.
Also, I was finding it quite inconvenient to have `x ∈ U` for `U : opens X` being unrelated to `x ∈ (U : set X)`. I propose we just add the simp lemmas in this PR that unfold to the set-level membership operation.
(I'd be happy to go the other way if someone has a strong opinion here; just that we pick a simp normal form for talking about membership and inclusion of opens.)
#### Estimated changes
Modified src/topology/opens.lean
- \+ *lemma* topological_space.opens.mem_coe
- \+ *theorem* topological_space.opens.mem_supr
- \+ *lemma* topological_space.opens.open_embedding_of_le
- \+ *lemma* topological_space.opens.subset_coe
- \+ *lemma* topological_space.opens.supr_s



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
- \+/\- *theorem* associated_of_dvd_dvd
- \+/\- *theorem* dvd_dvd_iff_associated
- \+/\- *lemma* dvd_dvd_of_associated
- \+/\- *lemma* dvd_iff_dvd_of_rel_left
- \- *lemma* dvd_mul_unit_iff
- \+/\- *lemma* dvd_of_associated
- \+/\- *lemma* dvd_symm_iff_of_irreducible
- \+/\- *lemma* dvd_symm_of_irreducible
- \+/\- *lemma* exists_mem_multiset_dvd_of_prime
- \+/\- *theorem* irreducible.ne_zero
- \+/\- *theorem* is_unit_iff_dvd_one
- \+/\- *theorem* is_unit_iff_forall_dvd
- \+/\- *lemma* is_unit_of_dvd_one
- \+/\- *theorem* is_unit_of_dvd_unit
- \- *theorem* mul_dvd_of_is_unit_left
- \- *theorem* mul_dvd_of_is_unit_right
- \- *lemma* mul_unit_dvd_iff
- \+/\- *theorem* not_irreducible_zero
- \+/\- *lemma* not_prime_one
- \+/\- *lemma* not_prime_zero
- \+/\- *lemma* prime.div_or_div
- \+/\- *lemma* prime.dvd_of_dvd_pow
- \+/\- *lemma* prime.ne_zero
- \+/\- *lemma* prime.not_unit
- \+/\- *def* prime
- \- *lemma* unit_mul_dvd_iff

Modified src/algebra/divisibility.lean
- \+/\- *theorem* dvd_mul_left
- \+ *lemma* is_unit.dvd
- \+ *lemma* is_unit.dvd_mul_left
- \+ *lemma* is_unit.dvd_mul_right
- \+ *lemma* is_unit.mul_left_dvd
- \+ *lemma* is_unit.mul_right_dvd
- \+ *theorem* mul_dvd_mul_iff_left
- \+/\- *theorem* one_dvd
- \+ *lemma* units.coe_dvd
- \+ *lemma* units.dvd_mul_left
- \+ *lemma* units.dvd_mul_right
- \+ *lemma* units.mul_left_dvd
- \+ *lemma* units.mul_right_dvd

Modified src/algebra/gcd_domain.lean


Modified src/algebra/group_power.lean
- \+/\- *lemma* pow_dvd_pow
- \+/\- *theorem* pow_dvd_pow_of_dvd
- \+/\- *theorem* pow_eq_zero
- \+/\- *theorem* pow_ne_zero
- \+/\- *lemma* zero_pow

Modified src/algebra/group_with_zero.lean


Modified src/algebra/ring/basic.lean
- \- *lemma* is_unit.mul_left_dvd_of_dvd
- \- *lemma* is_unit.mul_right_dvd_of_dvd
- \- *theorem* mul_dvd_mul_iff_left
- \+/\- *theorem* two_dvd_bit1
- \- *lemma* units.coe_dvd
- \- *lemma* units.coe_mul_dvd
- \- *lemma* units.coe_ne_zero
- \- *lemma* units.dvd_coe
- \- *lemma* units.dvd_coe_mul

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
- \- *theorem* ordinal.dvd_def
- \- *theorem* ordinal.dvd_mul
- \- *theorem* ordinal.dvd_mul_of_dvd
- \- *theorem* ordinal.dvd_trans

Modified src/set_theory/ordinal_notation.lean




## [2020-08-11 07:24:07](https://github.com/leanprover-community/mathlib/commit/57df7f5)
feat(haar_measure): define the Haar measure ([#3542](https://github.com/leanprover-community/mathlib/pull/3542))
Define the Haar measure on a locally compact Hausdorff group.
Some additions and simplifications to outer_measure and content.
#### Estimated changes
Modified docs/references.bib


Modified src/measure_theory/content.lean
- \+ *lemma* measure_theory.inner_content_comap
- \+ *lemma* measure_theory.outer_measure.is_left_invariant_of_content
- \+ *lemma* measure_theory.outer_measure.of_content_caratheodory
- \+ *lemma* measure_theory.outer_measure.of_content_eq_infi
- \+ *lemma* measure_theory.outer_measure.of_content_preimage

Added src/measure_theory/haar_measure.lean
- \+ *lemma* measure_theory.measure.chaar_le_haar_outer_measure
- \+ *def* measure_theory.measure.haar.chaar
- \+ *lemma* measure_theory.measure.haar.chaar_empty
- \+ *lemma* measure_theory.measure.haar.chaar_mem_cl_prehaar
- \+ *lemma* measure_theory.measure.haar.chaar_mem_haar_product
- \+ *lemma* measure_theory.measure.haar.chaar_mono
- \+ *lemma* measure_theory.measure.haar.chaar_nonneg
- \+ *lemma* measure_theory.measure.haar.chaar_self
- \+ *lemma* measure_theory.measure.haar.chaar_sup_eq
- \+ *lemma* measure_theory.measure.haar.chaar_sup_le
- \+ *def* measure_theory.measure.haar.cl_prehaar
- \+ *def* measure_theory.measure.haar.echaar
- \+ *lemma* measure_theory.measure.haar.echaar_mono
- \+ *lemma* measure_theory.measure.haar.echaar_sup_le
- \+ *def* measure_theory.measure.haar.haar_product
- \+ *def* measure_theory.measure.haar.index
- \+ *lemma* measure_theory.measure.haar.index_defined
- \+ *lemma* measure_theory.measure.haar.index_elim
- \+ *lemma* measure_theory.measure.haar.index_empty
- \+ *lemma* measure_theory.measure.haar.index_mono
- \+ *lemma* measure_theory.measure.haar.index_pos
- \+ *lemma* measure_theory.measure.haar.index_union_eq
- \+ *lemma* measure_theory.measure.haar.index_union_le
- \+ *lemma* measure_theory.measure.haar.is_left_invariant_chaar
- \+ *lemma* measure_theory.measure.haar.is_left_invariant_index
- \+ *lemma* measure_theory.measure.haar.is_left_invariant_prehaar
- \+ *lemma* measure_theory.measure.haar.le_index_mul
- \+ *lemma* measure_theory.measure.haar.mem_prehaar_empty
- \+ *lemma* measure_theory.measure.haar.mul_left_index_le
- \+ *lemma* measure_theory.measure.haar.nonempty_Inter_cl_prehaar
- \+ *def* measure_theory.measure.haar.prehaar
- \+ *lemma* measure_theory.measure.haar.prehaar_empty
- \+ *lemma* measure_theory.measure.haar.prehaar_le_index
- \+ *lemma* measure_theory.measure.haar.prehaar_mem_haar_product
- \+ *lemma* measure_theory.measure.haar.prehaar_mono
- \+ *lemma* measure_theory.measure.haar.prehaar_nonneg
- \+ *lemma* measure_theory.measure.haar.prehaar_pos
- \+ *lemma* measure_theory.measure.haar.prehaar_self
- \+ *lemma* measure_theory.measure.haar.prehaar_sup_eq
- \+ *lemma* measure_theory.measure.haar.prehaar_sup_le
- \+ *lemma* measure_theory.measure.haar_caratheodory_measurable
- \+ *def* measure_theory.measure.haar_measure
- \+ *lemma* measure_theory.measure.haar_measure_apply
- \+ *lemma* measure_theory.measure.haar_measure_pos_of_is_open
- \+ *lemma* measure_theory.measure.haar_measure_self
- \+ *def* measure_theory.measure.haar_outer_measure
- \+ *lemma* measure_theory.measure.haar_outer_measure_caratheodory
- \+ *lemma* measure_theory.measure.haar_outer_measure_eq_infi
- \+ *lemma* measure_theory.measure.haar_outer_measure_exists_compact
- \+ *lemma* measure_theory.measure.haar_outer_measure_exists_open
- \+ *lemma* measure_theory.measure.haar_outer_measure_le_chaar
- \+ *lemma* measure_theory.measure.haar_outer_measure_lt_top_of_is_compact
- \+ *lemma* measure_theory.measure.haar_outer_measure_of_is_open
- \+ *lemma* measure_theory.measure.haar_outer_measure_pos_of_is_open
- \+ *lemma* measure_theory.measure.haar_outer_measure_self_pos
- \+ *lemma* measure_theory.measure.is_left_invariant_haar_measure
- \+ *lemma* measure_theory.measure.one_le_haar_outer_measure_self
- \+ *lemma* measure_theory.measure.regular_haar_measure

Modified src/measure_theory/outer_measure.lean
- \+ *lemma* measure_theory.induced_outer_measure_preimage
- \+/\- *theorem* measure_theory.outer_measure.le_trim_iff

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
- \- *lemma* div_le_div_of_le_of_neg
- \- *lemma* div_le_div_of_le_of_pos
- \- *lemma* div_le_div_of_mul_sub_mul_div_nonpos
- \+ *lemma* div_le_div_of_neg_of_le
- \+ *lemma* div_le_div_of_pos_of_le
- \+/\- *lemma* div_le_of_le_mul
- \- *lemma* div_le_of_mul_le_of_neg
- \+ *lemma* div_le_of_neg_of_mul_le
- \- *lemma* div_lt_div_of_lt_of_neg
- \- *lemma* div_lt_div_of_lt_of_pos
- \- *lemma* div_lt_div_of_mul_sub_mul_div_neg
- \+ *lemma* div_lt_div_of_neg_of_lt
- \+ *lemma* div_lt_div_of_pos_of_lt
- \- *lemma* div_lt_of_mul_gt_of_neg
- \- *lemma* div_lt_of_mul_lt_of_pos
- \+ *lemma* div_lt_of_neg_of_mul_lt
- \+ *lemma* div_lt_of_pos_of_lt_mul
- \+ *lemma* div_mul_le_div_mul_of_div_le_div_nonneg
- \- *lemma* div_mul_le_div_mul_of_div_le_div_pos'
- \- *lemma* div_mul_le_div_mul_of_div_le_div_pos
- \+/\- *lemma* div_neg_of_neg_of_pos
- \+/\- *lemma* div_neg_of_pos_of_neg
- \- *lemma* div_nonneg'
- \+/\- *lemma* div_nonneg
- \- *lemma* div_nonneg_of_nonneg_of_pos
- \+ *lemma* div_nonneg_of_nonpos
- \- *lemma* div_nonneg_of_nonpos_of_neg
- \- *lemma* div_nonpos_of_nonneg_of_neg
- \+ *lemma* div_nonpos_of_nonneg_of_nonpos
- \+ *lemma* div_nonpos_of_nonpos_of_nonneg
- \- *lemma* div_nonpos_of_nonpos_of_pos
- \+/\- *lemma* div_pos
- \+/\- *lemma* div_pos_of_neg_of_neg
- \- *lemma* div_pos_of_pos_of_pos
- \+/\- *lemma* div_two_lt_of_pos
- \+/\- *lemma* inv_lt_zero
- \+/\- *lemma* inv_pos
- \+/\- *lemma* le_mul_of_div_le
- \- *lemma* le_mul_of_ge_one_left
- \- *lemma* le_mul_of_ge_one_right
- \+ *lemma* le_of_neg_of_one_div_le_one_div
- \- *lemma* le_of_one_div_le_one_div_of_neg
- \+/\- *lemma* le_of_one_le_div
- \- *lemma* lt_mul_of_gt_one_right
- \+ *lemma* lt_of_neg_of_one_div_lt_one_div
- \- *lemma* lt_of_one_div_lt_one_div_of_neg
- \+/\- *lemma* lt_of_one_lt_div
- \+/\- *lemma* mul_le_mul_of_mul_div_le
- \- *lemma* mul_le_of_div_le_of_neg
- \+ *lemma* mul_le_of_neg_of_div_le
- \- *lemma* mul_lt_of_gt_div_of_neg
- \+ *lemma* mul_lt_of_neg_of_div_lt
- \- *lemma* mul_sub_mul_div_mul_neg
- \+ *lemma* mul_sub_mul_div_mul_neg_iff
- \- *lemma* mul_sub_mul_div_mul_nonpos
- \+ *lemma* mul_sub_mul_div_mul_nonpos_iff
- \- *lemma* mul_zero_lt_mul_inv_of_neg
- \- *lemma* mul_zero_lt_mul_inv_of_pos
- \- *lemma* neg_of_one_div_neg
- \+ *lemma* one_div_le_of_neg_of_one_div_le
- \- *lemma* one_div_le_of_one_div_le_of_neg
- \- *lemma* one_div_le_of_one_div_le_of_pos
- \+ *lemma* one_div_le_of_pos_of_one_div_le
- \- *lemma* one_div_le_one_div_of_le_of_neg
- \+ *lemma* one_div_le_one_div_of_neg_of_le
- \- *lemma* one_div_lt_one_div_of_lt_of_neg
- \+ *lemma* one_div_lt_one_div_of_neg_of_lt
- \+ *lemma* one_div_neg
- \- *lemma* one_div_neg_of_neg
- \+ *lemma* one_div_nonneg
- \+ *lemma* one_div_nonpos
- \+ *lemma* one_div_pos
- \- *lemma* one_div_pos_of_pos
- \+/\- *lemma* one_le_div_of_le
- \+/\- *lemma* one_lt_div_of_lt
- \- *lemma* pos_of_one_div_pos

Modified src/algebra/ordered_group.lean
- \+ *lemma* le_mul_of_one_le_left'
- \- *lemma* le_mul_of_one_le_left
- \+ *lemma* le_mul_of_one_le_right'
- \- *lemma* le_mul_of_one_le_right
- \+ *lemma* lt_mul_of_one_lt_left'
- \- *lemma* lt_mul_of_one_lt_left
- \+ *lemma* lt_mul_of_one_lt_right'
- \- *lemma* lt_mul_of_one_lt_right

Modified src/algebra/ordered_ring.lean
- \- *lemma* le_mul_of_one_le_left'
- \+ *lemma* le_mul_of_one_le_left
- \- *lemma* le_mul_of_one_le_right'
- \+ *lemma* le_mul_of_one_le_right
- \- *lemma* lt_mul_of_one_lt_right'
- \+ *lemma* lt_mul_of_one_lt_right

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
- \+ *abbreviation* is_algebra_tower

Modified src/ring_theory/ideal/operations.lean
- \- *theorem* submodule.smul_assoc



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


Added src/category_theory/limits/preserves/shapes.lean
- \+ *lemma* map_lift_comp_preserves_products_iso_hom
- \+ *def* preserves_limits_iso
- \+ *lemma* preserves_limits_iso_hom_π
- \+ *def* preserves_products_iso
- \+ *lemma* preserves_products_iso_hom_π

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
- \+ *def* category_theory.limits.has_colimit_of_has_limit_left_op
- \+ *def* category_theory.limits.has_colimits_of_shape_op_of_has_limits_of_shape
- \+ *def* category_theory.limits.has_colimits_op_of_has_limits
- \+ *def* category_theory.limits.has_coproducts_opposite
- \+ *def* category_theory.limits.has_limit_of_has_colimit_left_op
- \+ *def* category_theory.limits.has_limits_of_shape_op_of_has_colimits_of_shape
- \+ *def* category_theory.limits.has_limits_op_of_has_colimits
- \+ *def* category_theory.limits.has_products_opposite

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *abbreviation* category_theory.limits.has_binary_coproducts
- \+ *abbreviation* category_theory.limits.has_binary_products

Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/constructions/binary_products.lean


Modified src/category_theory/limits/shapes/constructions/equalizers.lean


Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/shapes/constructions/over/default.lean


Modified src/category_theory/limits/shapes/constructions/over/products.lean


Modified src/category_theory/limits/shapes/constructions/pullbacks.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *abbreviation* category_theory.limits.coequalizer.cofork
- \+ *lemma* category_theory.limits.coequalizer.cofork_ι_app_one
- \+ *lemma* category_theory.limits.coequalizer.cofork_π
- \+/\- *def* category_theory.limits.coequalizer.iso_target_of_self
- \+/\- *lemma* category_theory.limits.coequalizer.iso_target_of_self_hom
- \+/\- *lemma* category_theory.limits.coequalizer.iso_target_of_self_inv
- \- *lemma* category_theory.limits.coequalizer.π.cofork
- \- *lemma* category_theory.limits.coequalizer.π.eq_app_one
- \+/\- *def* category_theory.limits.coequalizer.π_of_eq
- \+/\- *abbreviation* category_theory.limits.coequalizer
- \+ *def* category_theory.limits.cofork.mk_hom
- \+ *abbreviation* category_theory.limits.equalizer.fork
- \+ *lemma* category_theory.limits.equalizer.fork_ι
- \+ *lemma* category_theory.limits.equalizer.fork_π_app_zero
- \+/\- *def* category_theory.limits.equalizer.iso_source_of_self
- \+/\- *lemma* category_theory.limits.equalizer.iso_source_of_self_hom
- \+/\- *lemma* category_theory.limits.equalizer.iso_source_of_self_inv
- \- *lemma* category_theory.limits.equalizer.ι.eq_app_zero
- \- *lemma* category_theory.limits.equalizer.ι.fork
- \+/\- *def* category_theory.limits.equalizer.ι_of_eq
- \+/\- *abbreviation* category_theory.limits.equalizer
- \+ *def* category_theory.limits.fork.mk_hom
- \+ *abbreviation* category_theory.limits.has_coequalizer
- \+ *abbreviation* category_theory.limits.has_coequalizers
- \+ *abbreviation* category_theory.limits.has_equalizer
- \+ *abbreviation* category_theory.limits.has_equalizers

Modified src/category_theory/limits/shapes/finite_limits.lean
- \- *def* category_theory.limits.has_coequalizers_of_has_finite_colimits
- \- *def* category_theory.limits.has_equalizers_of_has_finite_limits
- \+ *def* category_theory.limits.has_finite_colimits
- \+ *def* category_theory.limits.has_finite_limits
- \+ *def* category_theory.limits.has_finite_wide_pullbacks
- \+ *def* category_theory.limits.has_finite_wide_pushouts
- \- *def* category_theory.limits.has_pullbacks_of_has_finite_limits
- \- *def* category_theory.limits.has_pushouts_of_has_finite_colimits

Modified src/category_theory/limits/shapes/finite_products.lean
- \+ *def* category_theory.limits.has_finite_coproducts
- \+ *def* category_theory.limits.has_finite_coproducts_of_has_coproducts
- \+ *def* category_theory.limits.has_finite_products
- \+ *def* category_theory.limits.has_finite_products_of_has_products

Modified src/category_theory/limits/shapes/products.lean
- \+ *abbreviation* category_theory.limits.has_coproducts
- \+ *abbreviation* category_theory.limits.has_products

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *abbreviation* category_theory.limits.has_pullback
- \+ *abbreviation* category_theory.limits.has_pullbacks
- \+ *abbreviation* category_theory.limits.has_pushout
- \+ *abbreviation* category_theory.limits.has_pushouts
- \+/\- *lemma* category_theory.limits.pullback.condition
- \+/\- *def* category_theory.limits.pullback.desc'
- \+/\- *abbreviation* category_theory.limits.pullback.fst
- \+/\- *lemma* category_theory.limits.pullback.hom_ext
- \+/\- *def* category_theory.limits.pullback.lift'
- \+/\- *abbreviation* category_theory.limits.pullback.lift
- \+/\- *lemma* category_theory.limits.pullback.lift_fst
- \+/\- *lemma* category_theory.limits.pullback.lift_snd
- \+/\- *abbreviation* category_theory.limits.pullback.snd
- \+/\- *abbreviation* category_theory.limits.pullback
- \+/\- *lemma* category_theory.limits.pushout.condition
- \+/\- *abbreviation* category_theory.limits.pushout.desc
- \+/\- *lemma* category_theory.limits.pushout.hom_ext
- \+/\- *abbreviation* category_theory.limits.pushout.inl
- \+/\- *lemma* category_theory.limits.pushout.inl_desc
- \+/\- *abbreviation* category_theory.limits.pushout.inr
- \+/\- *lemma* category_theory.limits.pushout.inr_desc
- \+/\- *abbreviation* category_theory.limits.pushout

Modified src/category_theory/limits/shapes/terminal.lean
- \+ *abbreviation* category_theory.limits.has_initial
- \+ *abbreviation* category_theory.limits.has_terminal

Modified src/category_theory/limits/shapes/types.lean
- \+ *lemma* category_theory.limits.types.pi
- \+ *lemma* category_theory.limits.types.pi_lift
- \+ *lemma* category_theory.limits.types.pi_map
- \+ *lemma* category_theory.limits.types.pi_π
- \+/\- *def* category_theory.limits.types.types_has_products

Modified src/category_theory/limits/shapes/wide_pullbacks.lean
- \+ *abbreviation* category_theory.limits.has_wide_pullbacks
- \+ *abbreviation* category_theory.limits.has_wide_pushouts



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
- \- *def* affine_independent
- \- *lemma* affine_independent_embedding_of_affine_independent
- \- *lemma* affine_independent_iff_indicator_eq_of_affine_combination_eq
- \- *lemma* affine_independent_iff_linear_independent_vsub
- \- *lemma* affine_independent_of_subsingleton
- \- *lemma* affine_independent_subtype_of_affine_independent
- \- *def* affine_map.weighted_vsub_of_point
- \- *lemma* affine_space.affine_combination_mem_affine_span
- \- *lemma* affine_space.eq_affine_combination_of_mem_affine_span
- \- *lemma* affine_space.finite_dimensional_direction_affine_span_of_finite
- \- *lemma* affine_space.finite_dimensional_vector_span_of_finite
- \- *lemma* affine_space.mem_affine_span_iff_eq_affine_combination
- \- *lemma* affine_space.mem_vector_span_iff_eq_weighted_vsub
- \- *lemma* affine_space.simplex.ext
- \- *lemma* affine_space.simplex.ext_iff
- \- *def* affine_space.simplex.face
- \- *lemma* affine_space.simplex.face_eq_mk_of_point
- \- *lemma* affine_space.simplex.face_points
- \- *def* affine_space.simplex.mk_of_point
- \- *lemma* affine_space.simplex.mk_of_point_points
- \- *structure* affine_space.simplex
- \- *abbreviation* affine_space.triangle
- \- *lemma* affine_space.weighted_vsub_mem_vector_span
- \- *lemma* affine_span_disjoint_of_disjoint_of_affine_independent
- \- *lemma* exists_mem_inter_of_exists_mem_inter_affine_span_of_affine_independent
- \- *def* finset.affine_combination
- \- *lemma* finset.affine_combination_apply
- \- *lemma* finset.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one
- \- *lemma* finset.affine_combination_indicator_subset
- \- *lemma* finset.affine_combination_of_eq_one_of_eq_zero
- \- *lemma* finset.affine_combination_vsub
- \- *lemma* finset.eq_affine_combination_subset_iff_eq_affine_combination_subtype
- \- *lemma* finset.eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype
- \- *lemma* finset.eq_weighted_vsub_subset_iff_eq_weighted_vsub_subtype
- \- *def* finset.weighted_vsub
- \- *lemma* finset.weighted_vsub_apply
- \- *lemma* finset.weighted_vsub_empty
- \- *lemma* finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero
- \- *lemma* finset.weighted_vsub_indicator_subset
- \- *def* finset.weighted_vsub_of_point
- \- *lemma* finset.weighted_vsub_of_point_apply
- \- *lemma* finset.weighted_vsub_of_point_eq_of_sum_eq_zero
- \- *lemma* finset.weighted_vsub_of_point_erase
- \- *lemma* finset.weighted_vsub_of_point_indicator_subset
- \- *lemma* finset.weighted_vsub_of_point_insert
- \- *lemma* finset.weighted_vsub_of_point_vadd_eq_of_sum_eq_one
- \- *lemma* finset.weighted_vsub_vadd_affine_combination
- \- *lemma* mem_affine_span_iff_mem_of_affine_independent
- \- *lemma* not_mem_affine_span_diff_of_affine_independent

Added src/linear_algebra/affine_space/combination.lean
- \+ *def* affine_map.weighted_vsub_of_point
- \+ *lemma* affine_space.affine_combination_mem_affine_span
- \+ *lemma* affine_space.eq_affine_combination_of_mem_affine_span
- \+ *lemma* affine_space.mem_affine_span_iff_eq_affine_combination
- \+ *lemma* affine_space.mem_vector_span_iff_eq_weighted_vsub
- \+ *lemma* affine_space.weighted_vsub_mem_vector_span
- \+ *def* finset.affine_combination
- \+ *lemma* finset.affine_combination_apply
- \+ *lemma* finset.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one
- \+ *lemma* finset.affine_combination_indicator_subset
- \+ *lemma* finset.affine_combination_of_eq_one_of_eq_zero
- \+ *lemma* finset.affine_combination_vsub
- \+ *lemma* finset.eq_affine_combination_subset_iff_eq_affine_combination_subtype
- \+ *lemma* finset.eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype
- \+ *lemma* finset.eq_weighted_vsub_subset_iff_eq_weighted_vsub_subtype
- \+ *def* finset.weighted_vsub
- \+ *lemma* finset.weighted_vsub_apply
- \+ *lemma* finset.weighted_vsub_empty
- \+ *lemma* finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero
- \+ *lemma* finset.weighted_vsub_indicator_subset
- \+ *def* finset.weighted_vsub_of_point
- \+ *lemma* finset.weighted_vsub_of_point_apply
- \+ *lemma* finset.weighted_vsub_of_point_eq_of_sum_eq_zero
- \+ *lemma* finset.weighted_vsub_of_point_erase
- \+ *lemma* finset.weighted_vsub_of_point_indicator_subset
- \+ *lemma* finset.weighted_vsub_of_point_insert
- \+ *lemma* finset.weighted_vsub_of_point_vadd_eq_of_sum_eq_one
- \+ *lemma* finset.weighted_vsub_vadd_affine_combination

Added src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* affine_space.finite_dimensional_direction_affine_span_of_finite
- \+ *lemma* affine_space.finite_dimensional_vector_span_of_finite

Added src/linear_algebra/affine_space/independent.lean
- \+ *def* affine_independent
- \+ *lemma* affine_independent_embedding_of_affine_independent
- \+ *lemma* affine_independent_iff_indicator_eq_of_affine_combination_eq
- \+ *lemma* affine_independent_iff_linear_independent_vsub
- \+ *lemma* affine_independent_of_subsingleton
- \+ *lemma* affine_independent_subtype_of_affine_independent
- \+ *lemma* affine_space.simplex.ext
- \+ *lemma* affine_space.simplex.ext_iff
- \+ *def* affine_space.simplex.face
- \+ *lemma* affine_space.simplex.face_eq_mk_of_point
- \+ *lemma* affine_space.simplex.face_points
- \+ *def* affine_space.simplex.mk_of_point
- \+ *lemma* affine_space.simplex.mk_of_point_points
- \+ *structure* affine_space.simplex
- \+ *abbreviation* affine_space.triangle
- \+ *lemma* affine_span_disjoint_of_disjoint_of_affine_independent
- \+ *lemma* exists_mem_inter_of_exists_mem_inter_affine_span_of_affine_independent
- \+ *lemma* mem_affine_span_iff_mem_of_affine_independent
- \+ *lemma* not_mem_affine_span_diff_of_affine_independent

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
- \+/\- *lemma* submodule.comap_subtype_self



## [2020-08-08 10:16:01](https://github.com/leanprover-community/mathlib/commit/1675dc4)
chore(order/complete_lattice): use `order_dual` ([#3724](https://github.com/leanprover-community/mathlib/pull/3724))
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+/\- *theorem* infi_exists
- \+/\- *theorem* infi_infi_eq_left
- \+/\- *theorem* infi_infi_eq_right
- \+/\- *theorem* infi_insert
- \+/\- *theorem* supr_exists
- \+/\- *theorem* supr_insert
- \+/\- *theorem* supr_supr_eq_left
- \+/\- *theorem* supr_supr_eq_right



## [2020-08-08 09:22:19](https://github.com/leanprover-community/mathlib/commit/bf1c7b7)
feat(linear_algebra/finite_dimensional): finite dimensional `is_basis` helpers ([#3720](https://github.com/leanprover-community/mathlib/pull/3720))
If we have a family of vectors in `V` with cardinality equal to the (finite) dimension of `V` over a field `K`, they span the whole space iff they are linearly independent.
This PR proves those two facts (in the form that either of the conditions of `is_basis K b` suffices to prove `is_basis K b` if `b` has the right cardinality).
We don't need to assume that `V` is finite dimensional, because the case that `findim K V = 0` will generally lead to a contradiction. We do sometimes need to assume that the family is nonempty, which seems like a much nicer condition.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *def* submodule.comap_subtype_equiv_of_le
- \+ *lemma* submodule.quotient.nontrivial_of_lt_top

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* findim_span_eq_card
- \+ *lemma* findim_span_le_card
- \+ *lemma* findim_span_set_eq_card
- \+ *lemma* finite_dimensional.findim_pos
- \+ *lemma* finite_dimensional.findim_pos_iff
- \+ *lemma* finite_dimensional.findim_pos_iff_exists_ne_zero
- \+ *lemma* finset_is_basis_of_linear_independent_of_card_eq_findim
- \+ *lemma* finset_is_basis_of_span_eq_top_of_card_eq_findim
- \+ *lemma* is_basis_of_linear_independent_of_card_eq_findim
- \+ *lemma* is_basis_of_span_eq_top_of_card_eq_findim
- \+ *lemma* linear_independent_of_span_eq_top_of_card_eq_findim
- \+ *lemma* set_is_basis_of_linear_independent_of_card_eq_findim
- \+ *lemma* set_is_basis_of_span_eq_top_of_card_eq_findim
- \+ *lemma* span_eq_top_of_linear_independent_of_card_eq_findim
- \+ *lemma* span_lt_of_subset_of_card_lt_findim
- \+ *lemma* span_lt_top_of_card_lt_findim
- \+ *lemma* submodule.findim_lt
- \+ *lemma* submodule.findim_mono
- \+ *lemma* submodule.lt_of_le_of_findim_lt_findim
- \+ *lemma* submodule.lt_top_of_findim_lt_findim



## [2020-08-07 21:33:16](https://github.com/leanprover-community/mathlib/commit/d61bd4a)
feat(algebra/classical_lie_algebras): add lie_algebra.orthogonal.mem_so ([#3711](https://github.com/leanprover-community/mathlib/pull/3711))
Also unrelated change to use new notation for direct_sum
#### Estimated changes
Modified src/algebra/classical_lie_algebras.lean
- \+ *lemma* lie_algebra.orthogonal.mem_so

Modified src/algebra/lie_algebra.lean
- \+/\- *lemma* lie_algebra.direct_sum.bracket_apply



## [2020-08-07 19:53:30](https://github.com/leanprover-community/mathlib/commit/1cd74b1)
fix(linear_algebra/finite_dimensional): universe generalize cardinal_mk_le_findim_of_linear_independent ([#3721](https://github.com/leanprover-community/mathlib/pull/3721))
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *theorem* {m}
- \+ *lemma* {m}

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
- \+ *theorem* list.filter_eq_foldr
- \+ *theorem* list.map_eq_foldr
- \+ *theorem* list.map_filter_eq_foldr
- \+ *theorem* list.mfoldl_eq_foldl
- \+ *theorem* list.mfoldr_eq_foldr

Modified src/data/list/default.lean


Modified src/data/list/defs.lean
- \+ *def* list.foldl_with_index
- \+ *def* list.foldl_with_index_aux
- \+ *def* list.foldr_with_index
- \+ *def* list.foldr_with_index_aux
- \+/\- *def* list.indexes_values
- \- *def* list.indexes_values_aux
- \+ *def* list.mfoldl_with_index
- \+ *def* list.mfoldr_with_index
- \+ *def* list.mmap_with_index'
- \+ *def* list.mmap_with_index'_aux
- \+ *def* list.mmap_with_index
- \+ *def* list.mmap_with_index_aux

Added src/data/list/indexes.lean
- \+ *theorem* list.find_indexes_eq_map_indexes_values
- \+ *theorem* list.foldl_with_index_aux_eq_foldl_with_index_aux_spec
- \+ *def* list.foldl_with_index_aux_spec
- \+ *theorem* list.foldl_with_index_aux_spec_cons
- \+ *theorem* list.foldl_with_index_eq_foldl_enum
- \+ *theorem* list.foldr_with_index_aux_eq_foldr_with_index_aux_spec
- \+ *def* list.foldr_with_index_aux_spec
- \+ *theorem* list.foldr_with_index_aux_spec_cons
- \+ *theorem* list.foldr_with_index_eq_foldr_enum
- \+ *theorem* list.indexes_values_eq_filter_enum
- \+ *theorem* list.mfoldl_with_index_eq_mfoldl_enum
- \+ *theorem* list.mfoldr_with_index_eq_mfoldr_enum
- \+ *theorem* list.mmap_with_index'_aux_eq_mmap_with_index_aux
- \+ *theorem* list.mmap_with_index'_eq_mmap_with_index
- \+ *theorem* list.mmap_with_index_aux_eq_mmap_with_index_aux_spec
- \+ *def* list.mmap_with_index_aux_spec
- \+ *theorem* list.mmap_with_index_aux_spec_cons
- \+ *theorem* list.mmap_with_index_eq_mmap_enum

Modified src/data/list/zip.lean
- \+ *theorem* list.map_fst_zip
- \+ *theorem* list.map_snd_zip



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
- \+/\- *lemma* set.diff_self
- \+/\- *theorem* set.image_empty
- \+/\- *lemma* set.image_id'
- \+/\- *theorem* set.image_swap_prod
- \+/\- *theorem* set.mem_prod
- \+/\- *theorem* set.mem_prod_eq
- \+/\- *lemma* set.mk_mem_prod
- \+ *lemma* set.mk_preimage_prod_left
- \+ *lemma* set.mk_preimage_prod_right
- \+/\- *theorem* set.prod_empty
- \+/\- *lemma* set.prod_eq
- \+/\- *theorem* set.prod_inter_prod
- \+/\- *theorem* set.prod_mk_mem_set_prod_eq
- \+ *theorem* set.prod_singleton
- \- *theorem* set.prod_singleton_singleton
- \+ *theorem* set.prod_union
- \+/\- *lemma* set.set_of_eq_eq_singleton
- \+ *theorem* set.singleton_prod
- \+ *theorem* set.singleton_prod_singleton
- \+ *theorem* set.union_prod
- \+/\- *theorem* set.univ_prod_univ

Modified src/data/set/lattice.lean
- \+/\- *lemma* set.prod_eq_seq

Modified src/measure_theory/integration.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* is_measurable.prod
- \+ *lemma* is_measurable_prod
- \+ *lemma* is_measurable_prod_of_nonempty
- \+/\- *lemma* measurable.fst
- \+/\- *lemma* measurable.prod
- \+/\- *lemma* measurable.prod_mk
- \+/\- *lemma* measurable.snd
- \+/\- *lemma* measurable_fst
- \+/\- *lemma* measurable_snd

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
- \+ *lemma* int.of_add_mul
- \+ *lemma* int.to_add_gpow
- \+ *lemma* int.to_add_pow
- \+ *lemma* nat.of_add_mul
- \+ *lemma* nat.to_add_pow



## [2020-08-06 16:42:33](https://github.com/leanprover-community/mathlib/commit/35ecc7b)
feat(analysis/calculus): Rolle's and Cauchy's mean value theorems with weaker assumptions (deps : 3590) ([#3681](https://github.com/leanprover-community/mathlib/pull/3681))
This introduces stronger versions of Rolle's theorem and Cauchy's mean value theorem, essentially by encapsulating an extension by continuity using the newly introduced `extend_from` of [#3590](https://github.com/leanprover-community/mathlib/pull/3590)
#### Estimated changes
Modified src/analysis/calculus/local_extr.lean
- \+ *lemma* exists_deriv_eq_zero'
- \+ *lemma* exists_has_deriv_at_eq_zero'

Modified src/analysis/calculus/mean_value.lean
- \+ *lemma* exists_ratio_deriv_eq_ratio_slope'
- \+ *lemma* exists_ratio_has_deriv_at_eq_ratio_slope'



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
- \+/\- *lemma* ring_equiv.ext
- \+/\- *lemma* ring_equiv.symm_to_ring_hom_apply_to_ring_hom_apply
- \+ *theorem* ring_equiv.symm_trans
- \+/\- *lemma* ring_equiv.to_ring_hom_apply_symm_to_ring_hom_apply
- \+ *lemma* ring_equiv.to_ring_hom_trans
- \+ *theorem* ring_equiv.trans_symm

Modified src/data/finset/basic.lean
- \+ *theorem* multiset.to_finset_map

Modified src/data/list/basic.lean
- \+ *theorem* list.prod_ne_zero

Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.forall_mem_cons
- \+ *theorem* multiset.forall_mem_map_iff
- \+ *theorem* multiset.prod_ne_zero

Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.map_list_prod
- \+ *lemma* polynomial.map_multiset_prod
- \+ *lemma* polynomial.map_prod

Modified src/data/polynomial/field_division.lean
- \+ *lemma* polynomial.map_ne_zero

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.roots_C
- \+ *lemma* polynomial.roots_list_prod
- \+ *lemma* polynomial.roots_multiset_prod
- \+ *lemma* polynomial.roots_one
- \+ *lemma* polynomial.roots_zero

Modified src/field_theory/minimal_polynomial.lean


Modified src/field_theory/splitting_field.lean
- \+ *def* alg_equiv.adjoin_singleton_equiv_adjoin_root_minimal_polynomial
- \+ *theorem* lift_of_splits
- \+ *def* polynomial.is_splitting_field.alg_equiv
- \+ *theorem* polynomial.is_splitting_field.finite_dimensional
- \+ *def* polynomial.is_splitting_field.lift
- \+ *theorem* polynomial.is_splitting_field.mul
- \+ *theorem* polynomial.is_splitting_field.splits_iff
- \+ *theorem* polynomial.roots_map

Modified src/linear_algebra/finite_dimensional.lean
- \+ *theorem* dim_eq_zero
- \+ *theorem* findim_eq_zero
- \+ *theorem* findim_top
- \+ *theorem* linear_map.findim_le_findim_of_injective
- \+ *theorem* linear_map.injective_iff_surjective_of_findim_eq_findim

Modified src/ring_theory/adjoin_root.lean
- \+ *def* adjoin_root.alg_hom
- \+ *lemma* adjoin_root.coe_alg_hom

Modified src/ring_theory/algebra.lean
- \+ *def* alg_equiv.of_bijective
- \+ *def* alg_hom.cod_restrict
- \+ *theorem* alg_hom.injective_cod_restrict
- \+ *theorem* alg_hom.injective_iff
- \+ *theorem* algebra.bijective_algbera_map_iff
- \+ *def* algebra.bot_equiv
- \+ *def* algebra.bot_equiv_of_injective
- \+ *theorem* algebra.surjective_algbera_map_iff

Modified src/ring_theory/algebra_tower.lean
- \- *def* is_algebra_tower.subalgebra_comap
- \- *theorem* is_algebra_tower.subalgebra_comap_top
- \+ *lemma* subalgebra.mem_res
- \+ *def* subalgebra.of_under
- \+ *def* subalgebra.res
- \+ *lemma* subalgebra.res_inj
- \+ *lemma* subalgebra.res_top

Modified src/ring_theory/subsemiring.lean




## [2020-08-06 15:42:26](https://github.com/leanprover-community/mathlib/commit/bc2bcac)
chore(algebra/module): Move submodule to its own file ([#3696](https://github.com/leanprover-community/mathlib/pull/3696))
#### Estimated changes
Modified src/algebra/module/basic.lean
- \- *lemma* submodule.add_mem
- \- *lemma* submodule.add_mem_iff_left
- \- *lemma* submodule.add_mem_iff_right
- \- *lemma* submodule.coe_add
- \- *lemma* submodule.coe_eq_coe
- \- *lemma* submodule.coe_eq_zero
- \- *theorem* submodule.coe_injective
- \- *lemma* submodule.coe_mem
- \- *lemma* submodule.coe_mk
- \- *lemma* submodule.coe_neg
- \- *theorem* submodule.coe_set_eq
- \- *lemma* submodule.coe_smul
- \- *theorem* submodule.coe_sort_coe
- \- *lemma* submodule.coe_sub
- \- *lemma* submodule.coe_to_add_subgroup
- \- *lemma* submodule.coe_zero
- \- *theorem* submodule.ext'_iff
- \- *theorem* submodule.ext
- \- *theorem* submodule.mem_coe
- \- *lemma* submodule.mk_eq_zero
- \- *lemma* submodule.neg_mem
- \- *lemma* submodule.neg_mem_iff
- \- *lemma* submodule.smul_mem
- \- *lemma* submodule.smul_mem_iff'
- \- *theorem* submodule.smul_mem_iff
- \- *lemma* submodule.sub_mem
- \- *theorem* submodule.subtype_apply
- \- *lemma* submodule.subtype_eq_val
- \- *lemma* submodule.sum_mem
- \- *lemma* submodule.sum_smul_mem
- \- *def* submodule.to_add_subgroup
- \- *theorem* submodule.to_add_submonoid_eq
- \- *theorem* submodule.to_add_submonoid_injective
- \- *lemma* submodule.zero_mem
- \- *structure* submodule
- \- *abbreviation* subspace

Modified src/algebra/module/default.lean


Added src/algebra/module/submodule.lean
- \+ *lemma* submodule.add_mem
- \+ *lemma* submodule.add_mem_iff_left
- \+ *lemma* submodule.add_mem_iff_right
- \+ *lemma* submodule.coe_add
- \+ *lemma* submodule.coe_eq_coe
- \+ *lemma* submodule.coe_eq_zero
- \+ *theorem* submodule.coe_injective
- \+ *lemma* submodule.coe_mem
- \+ *lemma* submodule.coe_mk
- \+ *lemma* submodule.coe_neg
- \+ *theorem* submodule.coe_set_eq
- \+ *lemma* submodule.coe_smul
- \+ *theorem* submodule.coe_sort_coe
- \+ *lemma* submodule.coe_sub
- \+ *lemma* submodule.coe_to_add_subgroup
- \+ *lemma* submodule.coe_zero
- \+ *theorem* submodule.ext'_iff
- \+ *theorem* submodule.ext
- \+ *theorem* submodule.mem_coe
- \+ *lemma* submodule.mk_eq_zero
- \+ *lemma* submodule.neg_mem
- \+ *lemma* submodule.neg_mem_iff
- \+ *lemma* submodule.smul_mem
- \+ *lemma* submodule.smul_mem_iff'
- \+ *theorem* submodule.smul_mem_iff
- \+ *lemma* submodule.sub_mem
- \+ *theorem* submodule.subtype_apply
- \+ *lemma* submodule.subtype_eq_val
- \+ *lemma* submodule.sum_mem
- \+ *lemma* submodule.sum_smul_mem
- \+ *def* submodule.to_add_subgroup
- \+ *theorem* submodule.to_add_submonoid_eq
- \+ *theorem* submodule.to_add_submonoid_injective
- \+ *lemma* submodule.zero_mem
- \+ *structure* submodule
- \+ *abbreviation* subspace

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
- \+/\- *lemma* measure_theory.integral_add_meas
- \+ *lemma* measure_theory.integral_map_meas
- \+ *lemma* measure_theory.integral_mono_of_nonneg
- \+ *lemma* measure_theory.norm_integral_le_of_norm_le
- \+ *lemma* measure_theory.norm_integral_le_of_norm_le_const

Added src/measure_theory/interval_integral.lean
- \+ *lemma* interval_integrable.add
- \+ *lemma* interval_integrable.neg
- \+ *lemma* interval_integrable.refl
- \+ *lemma* interval_integrable.smul
- \+ *lemma* interval_integrable.sub
- \+ *lemma* interval_integrable.symm
- \+ *lemma* interval_integrable.trans
- \+ *def* interval_integrable
- \+ *lemma* interval_integral.integral_add
- \+ *lemma* interval_integral.integral_add_adjacent_intervals
- \+ *lemma* interval_integral.integral_add_adjacent_intervals_cancel
- \+ *lemma* interval_integral.integral_cases
- \+ *lemma* interval_integral.integral_has_deriv_at_of_tendsto_ae
- \+ *lemma* interval_integral.integral_neg
- \+ *lemma* interval_integral.integral_of_ge
- \+ *lemma* interval_integral.integral_of_le
- \+ *lemma* interval_integral.integral_same
- \+ *lemma* interval_integral.integral_same_has_deriv_at_of_tendsto_ae
- \+ *lemma* interval_integral.integral_sub_linear_is_o_of_tendsto_ae
- \+ *lemma* interval_integral.integral_symm
- \+ *lemma* interval_integral.norm_integral_eq_norm_integral_Ioc
- \+ *lemma* interval_integral.norm_integral_le_abs_integral_norm
- \+ *lemma* interval_integral.norm_integral_le_integral_norm_Ioc
- \+ *lemma* interval_integral.norm_integral_le_of_norm_le_const
- \+ *lemma* interval_integral.norm_integral_le_of_norm_le_const_ae
- \+ *def* interval_integral

Modified src/measure_theory/l1_space.lean
- \+ *lemma* measure_theory.integrable.congr'
- \+ *lemma* measure_theory.integrable.mono'
- \- *lemma* measure_theory.integrable.mono_set
- \- *lemma* measure_theory.integrable.union
- \+ *lemma* measure_theory.integrable_add_meas
- \+ *lemma* measure_theory.integrable_congr'
- \+/\- *lemma* measure_theory.integrable_const
- \+ *lemma* measure_theory.integrable_const_iff
- \+ *lemma* measure_theory.integrable_map_meas
- \+ *lemma* measure_theory.integrable_of_bounded
- \- *lemma* measure_theory.integrable_of_integrable_bound
- \+ *lemma* measure_theory.integrable_zero_meas

Modified src/measure_theory/set_integral.lean
- \+ *lemma* continuous.integrable_on_compact
- \+ *lemma* continuous_at.integral_sub_linear_is_o_ae
- \+ *lemma* continuous_on.integrable_on_compact
- \+ *lemma* filter.tendsto.integral_sub_linear_is_o_ae
- \+ *lemma* indicator_ae_eq_restrict
- \+ *lemma* indicator_ae_eq_restrict_compl
- \+ *lemma* is_compact.integrable_on_of_nhds_within
- \+ *lemma* measure_theory.integrable.integrable_on'
- \+ *lemma* measure_theory.integrable.integrable_on
- \+ *lemma* measure_theory.integrable_at_filter.filter_mono
- \+ *lemma* measure_theory.integrable_at_filter.inf_ae_iff
- \+ *lemma* measure_theory.integrable_at_filter.inf_of_left
- \+ *lemma* measure_theory.integrable_at_filter.inf_of_right
- \+ *def* measure_theory.integrable_at_filter
- \+ *lemma* measure_theory.integrable_indicator_iff
- \+ *lemma* measure_theory.integrable_on.add_meas
- \+ *lemma* measure_theory.integrable_on.indicator
- \+ *lemma* measure_theory.integrable_on.integrable
- \+ *lemma* measure_theory.integrable_on.left_of_union
- \+ *lemma* measure_theory.integrable_on.mono
- \+ *lemma* measure_theory.integrable_on.mono_meas
- \+ *lemma* measure_theory.integrable_on.mono_set
- \+ *lemma* measure_theory.integrable_on.mono_set_ae
- \+ *lemma* measure_theory.integrable_on.right_of_union
- \+ *lemma* measure_theory.integrable_on.union
- \+ *def* measure_theory.integrable_on
- \+ *lemma* measure_theory.integrable_on_add_meas
- \+ *lemma* measure_theory.integrable_on_const
- \+ *lemma* measure_theory.integrable_on_empty
- \+ *lemma* measure_theory.integrable_on_finite_union
- \+ *lemma* measure_theory.integrable_on_finset_union
- \+ *lemma* measure_theory.integrable_on_of_bounded
- \+ *lemma* measure_theory.integrable_on_union
- \+ *lemma* measure_theory.integrable_on_univ
- \+ *lemma* measure_theory.integrable_on_zero
- \+ *lemma* measure_theory.integral_add_compl
- \+ *lemma* measure_theory.integral_empty
- \+ *lemma* measure_theory.integral_indicator
- \+ *lemma* measure_theory.integral_union
- \+ *lemma* measure_theory.integral_univ
- \+ *lemma* measure_theory.measure.finite_at_filter.integrable_at_filter
- \+ *lemma* measure_theory.measure.finite_at_filter.integrable_at_filter_of_tendsto
- \+ *lemma* measure_theory.measure.finite_at_filter.integrable_at_filter_of_tendsto_ae
- \+ *lemma* measure_theory.norm_set_integral_le_of_norm_le_const'
- \+ *lemma* measure_theory.norm_set_integral_le_of_norm_le_const
- \+ *lemma* measure_theory.norm_set_integral_le_of_norm_le_const_ae''
- \+ *lemma* measure_theory.norm_set_integral_le_of_norm_le_const_ae'
- \+ *lemma* measure_theory.norm_set_integral_le_of_norm_le_const_ae
- \+ *lemma* measure_theory.set_integral_const
- \+ *lemma* piecewise_ae_eq_restrict
- \+ *lemma* piecewise_ae_eq_restrict_compl



## [2020-08-06 03:47:24](https://github.com/leanprover-community/mathlib/commit/5cba21d)
chore(*): swap order of [fintype A] [decidable_eq A] ([#3705](https://github.com/leanprover-community/mathlib/pull/3705))
@fpvandoorn  suggested in [#3603](https://github.com/leanprover-community/mathlib/pull/3603) swapping the order of some `[fintype A] [decidable_eq A]` arguments to solve a linter problem with slow typeclass lookup.
The reasoning is that Lean solves typeclass search problems from right to left, and 
* it's "less likely" that a type is a `fintype` than it has `decidable_eq`, so we can fail earlier if `fintype` comes second
* typeclass search for `[decidable_eq]` can already be slow, so it's better to avoid it.
This PR applies this suggestion across the library.
#### Estimated changes
Modified src/algebra/lie_algebra.lean
- \+/\- *def* matrix.reindex_lie_equiv
- \+/\- *lemma* matrix.reindex_lie_equiv_apply
- \+/\- *lemma* matrix.reindex_lie_equiv_symm_apply
- \+/\- *def* skew_adjoint_matrices_lie_subalgebra_equiv_transpose

Modified src/data/equiv/list.lean
- \+/\- *def* encodable.fintype_arrow
- \+/\- *def* encodable.fintype_pi

Modified src/data/fintype/basic.lean
- \+/\- *lemma* finset.card_univ_diff
- \+/\- *def* fintype.equiv_fin
- \+/\- *def* fintype.of_surjective
- \+/\- *def* quotient.fin_choice
- \+/\- *theorem* quotient.fin_choice_eq

Modified src/data/fintype/card.lean
- \+/\- *lemma* finset.prod_fiberwise
- \+/\- *lemma* fintype.card_fun
- \+/\- *lemma* fintype.card_pi
- \+/\- *lemma* fintype.prod_fiberwise

Modified src/data/matrix/basic.lean
- \+/\- *def* matrix.scalar

Modified src/field_theory/finite.lean
- \+/\- *lemma* finite_field.card_image_polynomial_eval

Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* is_cyclic.card_order_of_eq_totient
- \+/\- *lemma* is_cyclic.card_pow_eq_one_le
- \+/\- *lemma* is_cyclic_of_order_of_eq_card
- \+/\- *lemma* order_of_eq_card_of_forall_mem_gpowers

Modified src/linear_algebra/char_poly.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/matrix.lean
- \+/\- *theorem* linear_map.to_matrix_of_equiv

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
- \+/\- *lemma* submodule.add_mem_iff_left
- \+/\- *lemma* submodule.add_mem_iff_right
- \+/\- *lemma* submodule.sub_mem



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
- \+ *lemma* set.mem_Ioo_or_eq_endpoints_of_mem_Icc
- \+ *lemma* set.mem_Ioo_or_eq_left_of_mem_Ico
- \+ *lemma* set.mem_Ioo_or_eq_right_of_mem_Ioc

Modified src/topology/algebra/ordered.lean
- \+ *lemma* continuous_at_iff_continuous_left'_right'
- \+ *lemma* continuous_at_iff_continuous_left_right
- \+ *lemma* continuous_on_Icc_extend_from_Ioo
- \+ *lemma* continuous_on_Ico_extend_from_Ioo
- \+ *lemma* continuous_on_Ioc_extend_from_Ioo
- \+ *lemma* continuous_within_at_Iio_iff_Iic
- \+ *lemma* continuous_within_at_Ioi_iff_Ici
- \+ *lemma* eq_lim_at_left_extend_from_Ioo
- \+ *lemma* eq_lim_at_right_extend_from_Ioo
- \+ *lemma* nhds_left'_sup_nhds_right
- \+ *lemma* nhds_left_sup_nhds_right'
- \+ *lemma* nhds_left_sup_nhds_right
- \+/\- *lemma* tendsto_inv_nhds_within_Iio
- \+/\- *lemma* tendsto_inv_nhds_within_Iio_inv
- \+/\- *lemma* tendsto_inv_nhds_within_Ioi
- \+/\- *lemma* tendsto_inv_nhds_within_Ioi_inv

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_if'
- \+ *lemma* continuous_on_if'
- \+ *lemma* continuous_on_if
- \+ *lemma* continuous_within_at_of_not_mem_closure

Added src/topology/extend_from_subset.lean
- \+ *lemma* continuous_extend_from
- \+ *lemma* continuous_on_extend_from
- \+ *def* extend_from
- \+ *lemma* extend_from_eq
- \+ *lemma* extend_from_extends
- \+ *lemma* tendsto_extend_from



## [2020-08-05 21:26:53](https://github.com/leanprover-community/mathlib/commit/89ada87)
chore(algebra, data/pnat): refactoring comm_semiring_has_dvd into comm_monoid_has_dvd ([#3702](https://github.com/leanprover-community/mathlib/pull/3702))
changes the instance comm_semiring_has_dvd to apply to any comm_monoid
cleans up the pnat API to use this new definition
#### Estimated changes
Added src/algebra/divisibility.lean
- \+ *theorem* dvd.elim
- \+ *theorem* dvd.elim_left
- \+ *theorem* dvd.intro
- \+ *theorem* dvd.intro_left
- \+ *theorem* dvd_mul_left
- \+ *theorem* dvd_mul_of_dvd_left
- \+ *theorem* dvd_mul_of_dvd_right
- \+ *theorem* dvd_mul_right
- \+ *theorem* dvd_of_mul_left_dvd
- \+ *theorem* dvd_of_mul_right_dvd
- \+ *theorem* dvd_refl
- \+ *theorem* dvd_trans
- \+ *theorem* dvd_zero
- \+ *theorem* eq_zero_of_zero_dvd
- \+ *theorem* exists_eq_mul_left_of_dvd
- \+ *theorem* exists_eq_mul_right_of_dvd
- \+ *theorem* mul_dvd_mul
- \+ *theorem* mul_dvd_mul_left
- \+ *theorem* mul_dvd_mul_right
- \+ *theorem* one_dvd
- \+ *lemma* zero_dvd_iff

Modified src/algebra/ring/basic.lean
- \- *theorem* dvd.elim
- \- *theorem* dvd.elim_left
- \- *theorem* dvd.intro
- \- *theorem* dvd.intro_left
- \- *theorem* dvd_mul_left
- \- *theorem* dvd_mul_of_dvd_left
- \- *theorem* dvd_mul_of_dvd_right
- \- *theorem* dvd_mul_right
- \- *theorem* dvd_of_mul_left_dvd
- \- *theorem* dvd_of_mul_right_dvd
- \- *theorem* dvd_refl
- \- *theorem* dvd_trans
- \- *theorem* dvd_zero
- \- *theorem* eq_zero_of_zero_dvd
- \- *theorem* exists_eq_mul_left_of_dvd
- \- *theorem* exists_eq_mul_right_of_dvd
- \- *theorem* mul_dvd_mul
- \- *theorem* mul_dvd_mul_left
- \- *theorem* mul_dvd_mul_right
- \- *theorem* one_dvd
- \- *lemma* zero_dvd_iff

Modified src/data/pnat/basic.lean
- \- *theorem* pnat.dvd_iff''
- \+/\- *theorem* pnat.dvd_iff
- \- *theorem* pnat.dvd_intro
- \+/\- *theorem* pnat.dvd_lcm_left
- \+/\- *theorem* pnat.dvd_lcm_right
- \- *theorem* pnat.dvd_refl
- \+/\- *theorem* pnat.gcd_dvd_left
- \+/\- *theorem* pnat.gcd_dvd_right
- \- *theorem* pnat.one_dvd

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
- \+ *theorem* matrix.add_apply
- \- *theorem* matrix.add_val
- \+ *lemma* matrix.bit0_apply
- \- *lemma* matrix.bit0_val
- \+ *lemma* matrix.bit1_apply
- \+ *lemma* matrix.bit1_apply_eq
- \+ *lemma* matrix.bit1_apply_ne
- \- *lemma* matrix.bit1_val
- \- *lemma* matrix.bit1_val_eq
- \- *lemma* matrix.bit1_val_ne
- \+ *lemma* matrix.col_apply
- \- *lemma* matrix.col_val
- \+ *theorem* matrix.diagonal_apply_eq
- \+ *theorem* matrix.diagonal_apply_ne'
- \+ *theorem* matrix.diagonal_apply_ne
- \- *theorem* matrix.diagonal_val_eq
- \- *theorem* matrix.diagonal_val_ne'
- \- *theorem* matrix.diagonal_val_ne
- \+ *theorem* matrix.mul_apply'
- \+ *theorem* matrix.mul_apply
- \- *theorem* matrix.mul_val'
- \- *theorem* matrix.mul_val
- \+ *theorem* matrix.neg_apply
- \- *theorem* matrix.neg_val
- \+ *theorem* matrix.one_apply
- \+ *theorem* matrix.one_apply_eq
- \+ *theorem* matrix.one_apply_ne'
- \+ *theorem* matrix.one_apply_ne
- \- *theorem* matrix.one_val
- \- *theorem* matrix.one_val_eq
- \- *theorem* matrix.one_val_ne'
- \- *theorem* matrix.one_val_ne
- \+ *lemma* matrix.row_apply
- \+ *lemma* matrix.row_mul_col_apply
- \- *lemma* matrix.row_mul_col_val
- \- *lemma* matrix.row_val
- \+ *lemma* matrix.smul_apply
- \- *lemma* matrix.smul_val
- \+ *lemma* matrix.transpose_apply
- \- *lemma* matrix.transpose_val
- \+ *lemma* matrix.update_column_apply
- \- *lemma* matrix.update_column_val
- \+ *lemma* matrix.update_row_apply
- \- *lemma* matrix.update_row_val
- \+ *theorem* matrix.zero_apply
- \- *theorem* matrix.zero_val

Modified src/data/matrix/pequiv.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/matrix.lean


Modified src/linear_algebra/nonsingular_inverse.lean
- \+ *lemma* matrix.adjugate_apply
- \- *lemma* matrix.adjugate_val
- \+ *lemma* matrix.mul_adjugate_apply
- \- *lemma* matrix.mul_adjugate_val

Modified src/ring_theory/matrix_algebra.lean
- \+ *lemma* algebra_map_matrix_apply
- \- *lemma* algebra_map_matrix_val

Modified src/ring_theory/polynomial_algebra.lean




## [2020-08-05 15:41:26](https://github.com/leanprover-community/mathlib/commit/d952e8b)
chore(topology/category/Top/opens): module-doc, cleanup, and construct some morphisms ([#3601](https://github.com/leanprover-community/mathlib/pull/3601))
#### Estimated changes
Modified src/category_theory/category/default.lean
- \+ *def* category_theory.hom_of_le
- \+ *lemma* category_theory.le_of_hom

Modified src/category_theory/limits/lattice.lean


Modified src/topology/category/Top/opens.lean
- \+ *def* topological_space.opens.inf_le_left
- \+ *def* topological_space.opens.inf_le_right
- \+ *def* topological_space.opens.le_supr
- \- *lemma* topological_space.opens.map_comp_hom_app
- \- *lemma* topological_space.opens.map_comp_inv_app
- \- *lemma* topological_space.opens.map_id_hom_app
- \- *lemma* topological_space.opens.map_id_inv_app
- \+/\- *lemma* topological_space.opens.map_obj
- \+ *lemma* topological_space.opens.to_Top_map



## [2020-08-05 11:37:40](https://github.com/leanprover-community/mathlib/commit/c63dad1)
chore(ring_theory/ideals): Move the definition of ideals out of algebra/module ([#3692](https://github.com/leanprover-community/mathlib/pull/3692))
Neatness was the main motivation - it makes it easier to reason about what would need doing in [#3635](https://github.com/leanprover-community/mathlib/pull/3635).
It also results in somewhere sensible for the docs about ideals. Also adds a very minimal docstring to `ring_theory/ideals.lean`.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \- *lemma* ideal.add_mem_iff_left
- \- *lemma* ideal.add_mem_iff_right
- \- *lemma* ideal.mul_mem_left
- \- *lemma* ideal.mul_mem_right
- \- *lemma* ideal.neg_mem_iff
- \- *def* ideal

Modified src/ring_theory/ideals.lean
- \+ *lemma* ideal.add_mem_iff_left
- \+ *lemma* ideal.add_mem_iff_right
- \+ *lemma* ideal.mul_mem_left
- \+ *lemma* ideal.mul_mem_right
- \+ *lemma* ideal.neg_mem_iff
- \+ *def* ideal



## [2020-08-05 11:37:36](https://github.com/leanprover-community/mathlib/commit/4a82e84)
feat(algebra/*/ulift): algebraic instances for ulift ([#3675](https://github.com/leanprover-community/mathlib/pull/3675))
#### Estimated changes
Added src/algebra/group/ulift.lean
- \+ *lemma* ulift.inv_down
- \+ *lemma* ulift.mul_down
- \+ *def* ulift.mul_equiv
- \+ *lemma* ulift.one_down
- \+ *lemma* ulift.sub_down

Modified src/algebra/module/pi.lean


Added src/algebra/module/ulift.lean
- \+ *def* ulift.semimodule_equiv
- \+ *lemma* ulift.smul_down'
- \+ *lemma* ulift.smul_down

Added src/algebra/ring/ulift.lean
- \+ *def* ulift.ring_equiv



## [2020-08-05 10:42:04](https://github.com/leanprover-community/mathlib/commit/2b9ac69)
feat(linear_algebra/affine_space): faces of simplices ([#3691](https://github.com/leanprover-community/mathlib/pull/3691))
Define a `face` of an `affine_space.simplex` with any given nonempty
subset of the vertices, using `finset.mono_of_fin`.
#### Estimated changes
Modified src/linear_algebra/affine_space.lean
- \+ *def* affine_space.simplex.face
- \+ *lemma* affine_space.simplex.face_eq_mk_of_point
- \+ *lemma* affine_space.simplex.face_points



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
- \+ *def* lie_algebra.orthogonal.JB
- \+ *lemma* lie_algebra.orthogonal.JB_transform
- \+ *def* lie_algebra.orthogonal.JD
- \+ *lemma* lie_algebra.orthogonal.JD_transform
- \+ *def* lie_algebra.orthogonal.PB
- \+ *lemma* lie_algebra.orthogonal.PB_inv
- \+ *def* lie_algebra.orthogonal.PD
- \+ *lemma* lie_algebra.orthogonal.PD_inv
- \+ *def* lie_algebra.orthogonal.Pso
- \+ *lemma* lie_algebra.orthogonal.Pso_inv
- \+ *def* lie_algebra.orthogonal.S
- \+ *lemma* lie_algebra.orthogonal.S_as_blocks
- \+ *def* lie_algebra.orthogonal.indefinite_diagonal
- \+ *lemma* lie_algebra.orthogonal.indefinite_diagonal_assoc
- \+ *lemma* lie_algebra.orthogonal.indefinite_diagonal_transform
- \+ *lemma* lie_algebra.orthogonal.is_unit_PB
- \+ *lemma* lie_algebra.orthogonal.is_unit_PD
- \+ *lemma* lie_algebra.orthogonal.is_unit_Pso
- \+ *def* lie_algebra.orthogonal.so'
- \+ *def* lie_algebra.orthogonal.so
- \+ *lemma* lie_algebra.orthogonal.so_indefinite_equiv_apply
- \+ *def* lie_algebra.orthogonal.type_B
- \+ *def* lie_algebra.orthogonal.type_D
- \+ *def* lie_algebra.symplectic.J
- \+ *def* lie_algebra.symplectic.sp

Modified src/algebra/lie_algebra.lean
- \+ *def* alg_equiv.to_lie_equiv
- \+ *lemma* alg_equiv.to_lie_equiv_apply
- \+ *lemma* alg_equiv.to_lie_equiv_symm_apply
- \+ *lemma* mem_skew_adjoint_matrices_lie_subalgebra
- \+ *lemma* mem_skew_adjoint_matrices_lie_subalgebra_unit_smul
- \+ *def* skew_adjoint_matrices_lie_subalgebra_equiv_transpose
- \+ *lemma* skew_adjoint_matrices_lie_subalgebra_equiv_transpose_apply

Modified src/data/matrix/basic.lean
- \+ *def* matrix.from_blocks
- \+ *lemma* matrix.from_blocks_add
- \+ *lemma* matrix.from_blocks_apply₁₁
- \+ *lemma* matrix.from_blocks_apply₁₂
- \+ *lemma* matrix.from_blocks_apply₂₁
- \+ *lemma* matrix.from_blocks_apply₂₂
- \+ *lemma* matrix.from_blocks_diagonal
- \+ *lemma* matrix.from_blocks_multiply
- \+ *lemma* matrix.from_blocks_one
- \+ *lemma* matrix.from_blocks_smul
- \+ *lemma* matrix.from_blocks_to_blocks
- \+ *lemma* matrix.from_blocks_transpose
- \+ *lemma* matrix.to_blocks_from_blocks₁₁
- \+ *lemma* matrix.to_blocks_from_blocks₁₂
- \+ *lemma* matrix.to_blocks_from_blocks₂₁
- \+ *lemma* matrix.to_blocks_from_blocks₂₂
- \+ *def* matrix.to_blocks₁₁
- \+ *def* matrix.to_blocks₁₂
- \+ *def* matrix.to_blocks₂₁
- \+ *def* matrix.to_blocks₂₂

Modified src/linear_algebra/matrix.lean
- \+ *lemma* matrix.reindex_transpose

Modified src/linear_algebra/nonsingular_inverse.lean
- \+ *lemma* matrix.is_unit_det_of_left_inverse
- \+ *lemma* matrix.is_unit_det_of_right_inverse
- \+ *lemma* matrix.nonsing_inv_left_right
- \+ *lemma* matrix.nonsing_inv_right_left

Modified src/ring_theory/algebra.lean
- \+ *def* alg_equiv.to_linear_equiv
- \+ *lemma* alg_equiv.to_linear_equiv_apply



## [2020-08-05 09:56:01](https://github.com/leanprover-community/mathlib/commit/37119b4)
feat(topology): normed spaces are (locally) path connected ([#3689](https://github.com/leanprover-community/mathlib/pull/3689))
#### Estimated changes
Modified src/analysis/convex/topology.lean
- \+ *lemma* convex.is_path_connected

Modified src/topology/algebra/module.lean


Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on.comp_continuous

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.nonempty_ball
- \+ *lemma* metric.nonempty_closed_ball

Modified src/topology/path_connected.lean
- \+ *lemma* joined_in.of_line
- \+ *def* path.of_line
- \+ *lemma* path.of_line_mem



## [2020-08-05 09:09:06](https://github.com/leanprover-community/mathlib/commit/545186c)
refactor(*): add a notation for `nhds_within` ([#3683](https://github.com/leanprover-community/mathlib/pull/3683))
The definition is still there and can be used too.
#### Estimated changes
Modified src/analysis/ODE/gronwall.lean


Modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* has_deriv_within_at_inter'

Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* differentiable_within_at_inter'
- \+/\- *lemma* has_fderiv_within_at_inter'

Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/calculus/tangent_cone.lean
- \+/\- *lemma* tangent_cone_congr
- \+/\- *lemma* tangent_cone_mono_nhds
- \+/\- *lemma* unique_diff_within_at.inter'
- \+/\- *lemma* unique_diff_within_at_congr
- \+/\- *lemma* unique_diff_within_at_inter'

Modified src/analysis/calculus/times_cont_diff.lean
- \+/\- *lemma* times_cont_diff_within_at_inter'

Modified src/analysis/normed_space/basic.lean


Modified src/analysis/specific_limits.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/local_invariant_properties.lean
- \+/\- *lemma* structure_groupoid.local_invariant_prop.lift_prop_within_at_inter'

Modified src/geometry/manifold/mfderiv.lean
- \+/\- *lemma* has_mfderiv_within_at_inter'
- \+/\- *lemma* mdifferentiable_within_at_inter'
- \+/\- *lemma* unique_mdiff_within_at.inter'

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
- \+/\- *lemma* continuous_within_at_inter'
- \+/\- *lemma* mem_nhds_within_insert
- \+/\- *theorem* mem_nhds_within_subtype
- \+/\- *lemma* mem_of_mem_nhds_within
- \+/\- *theorem* nhds_within_empty
- \+/\- *theorem* nhds_within_le_of_mem
- \+/\- *theorem* nhds_within_mono
- \+/\- *theorem* nhds_within_restrict''
- \+/\- *theorem* nhds_within_univ
- \+/\- *theorem* self_mem_nhds_within

Modified src/topology/dense_embedding.lean


Modified src/topology/local_extr.lean
- \+/\- *lemma* filter.eventually_eq.is_local_extr_on_iff
- \+/\- *lemma* filter.eventually_eq.is_local_max_on_iff
- \+/\- *lemma* filter.eventually_eq.is_local_min_on_iff
- \+/\- *lemma* filter.eventually_le.is_local_max_on
- \+/\- *lemma* filter.eventually_le.is_local_min_on
- \+/\- *def* is_local_extr_on
- \+/\- *def* is_local_max_on
- \+/\- *def* is_local_min_on

Modified src/topology/local_homeomorph.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* metric.mem_nhds_within_iff

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
- \+ *lemma* add_torsor.eq_vadd_iff_vsub_eq
- \+ *lemma* add_torsor.vsub_set_finite_of_finite

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* affine_independent_embedding_of_affine_independent
- \+ *lemma* affine_independent_iff_indicator_eq_of_affine_combination_eq
- \+ *lemma* affine_independent_subtype_of_affine_independent
- \+ *lemma* affine_space.finite_dimensional_direction_affine_span_of_finite
- \+ *lemma* affine_space.finite_dimensional_vector_span_of_finite
- \+ *lemma* affine_span_disjoint_of_disjoint_of_affine_independent
- \+ *lemma* affine_subspace.affine_span_coe
- \+ *lemma* affine_subspace.mem_affine_span_singleton
- \+ *lemma* exists_mem_inter_of_exists_mem_inter_affine_span_of_affine_independent
- \+ *lemma* finset.eq_affine_combination_subset_iff_eq_affine_combination_subtype
- \+ *lemma* finset.eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype
- \+ *lemma* finset.eq_weighted_vsub_subset_iff_eq_weighted_vsub_subtype
- \+ *lemma* mem_affine_span_iff_mem_of_affine_independent
- \+ *lemma* not_mem_affine_span_diff_of_affine_independent



## [2020-08-04 18:21:00](https://github.com/leanprover-community/mathlib/commit/84b450d)
feat(topology): path connected spaces ([#3627](https://github.com/leanprover-community/mathlib/pull/3627))
From the sphere eversion project.
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Icc_def
- \+ *lemma* set.Ici_def
- \+ *lemma* set.Ico_def
- \+ *lemma* set.Iic_def
- \+ *lemma* set.Iio_def
- \+ *lemma* set.Ioc_def
- \+ *lemma* set.Ioi_def
- \+ *lemma* set.Ioo_def

Modified src/geometry/manifold/real_instances.lean


Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.to_has_basis

Added src/topology/path_connected.lean
- \+ *def* I_extend
- \+ *lemma* I_extend_extends
- \+ *lemma* I_extend_one
- \+ *lemma* I_extend_range
- \+ *lemma* I_extend_zero
- \+ *def* I_symm
- \+ *lemma* I_symm_one
- \+ *lemma* I_symm_zero
- \+ *lemma* Icc_zero_one_symm
- \+ *lemma* coe_I_one
- \+ *lemma* coe_I_zero
- \+ *lemma* continuous.I_extend
- \+ *lemma* continuous_I_symm
- \+ *lemma* continuous_proj_I
- \+ *lemma* is_open.is_connected_iff_is_path_connected
- \+ *lemma* is_path_connected.image
- \+ *lemma* is_path_connected.joined_in
- \+ *lemma* is_path_connected.mem_path_component
- \+ *lemma* is_path_connected.preimage_coe
- \+ *lemma* is_path_connected.subset_path_component
- \+ *lemma* is_path_connected.union
- \+ *def* is_path_connected
- \+ *lemma* is_path_connected_iff
- \+ *lemma* is_path_connected_iff_eq
- \+ *lemma* is_path_connected_iff_path_connected_space
- \+ *lemma* joined.mem_path_component
- \+ *lemma* joined.refl
- \+ *def* joined.some_path
- \+ *lemma* joined.symm
- \+ *lemma* joined.trans
- \+ *def* joined
- \+ *lemma* joined_in.joined
- \+ *lemma* joined_in.joined_subtype
- \+ *lemma* joined_in.mem
- \+ *lemma* joined_in.mono
- \+ *lemma* joined_in.refl
- \+ *def* joined_in.some_path
- \+ *lemma* joined_in.some_path_mem
- \+ *lemma* joined_in.source_mem
- \+ *lemma* joined_in.symm
- \+ *lemma* joined_in.target_mem
- \+ *lemma* joined_in.trans
- \+ *def* joined_in
- \+ *lemma* joined_in_iff_joined
- \+ *lemma* joined_in_univ
- \+ *lemma* loc_path_connected_of_bases
- \+ *lemma* loc_path_connected_of_is_open
- \+ *lemma* mem_path_component_of_mem
- \+ *lemma* mem_path_component_self
- \+ *def* path.cast
- \+ *lemma* path.cast_coe
- \+ *lemma* path.continuous_extend
- \+ *def* path.extend
- \+ *lemma* path.extend_one
- \+ *lemma* path.extend_zero
- \+ *def* path.map
- \+ *lemma* path.map_coe
- \+ *def* path.refl
- \+ *def* path.symm
- \+ *def* path.trans
- \+ *structure* path
- \+ *lemma* path_component.nonempty
- \+ *def* path_component
- \+ *lemma* path_component_congr
- \+ *def* path_component_in
- \+ *lemma* path_component_in_univ
- \+ *lemma* path_component_subset_component
- \+ *lemma* path_component_symm
- \+ *def* path_connected_space.some_path
- \+ *lemma* path_connected_space_iff_connected_space
- \+ *lemma* path_connected_space_iff_eq
- \+ *lemma* path_connected_space_iff_univ
- \+ *lemma* path_connected_space_iff_zeroth_homotopy
- \+ *lemma* path_connected_subset_basis
- \+ *def* path_setoid
- \+ *def* proj_I
- \+ *lemma* proj_I_I
- \+ *lemma* range_proj_I
- \+ *lemma* surjective_proj_I
- \+ *def* zeroth_homotopy



## [2020-08-04 16:33:38](https://github.com/leanprover-community/mathlib/commit/f4b2790)
feat(data/list/defs): add monadic versions of list.{find,any,all,bor,band} ([#3679](https://github.com/leanprover-community/mathlib/pull/3679))
Also universe-generalise `mfind` while I'm at it.
#### Estimated changes
Modified src/data/list/defs.lean
- \+ *def* list.mall
- \+ *def* list.many
- \+ *def* list.mband
- \+ *def* list.mbfind'
- \+ *def* list.mbfind
- \+ *def* list.mbor
- \+/\- *def* list.mfind



## [2020-08-04 13:40:24](https://github.com/leanprover-community/mathlib/commit/3ae6cea)
feat(group_theory/submonoid/operations): transfer galois connection/insertion lemmas ([#3657](https://github.com/leanprover-community/mathlib/pull/3657))
#### Estimated changes
Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* submonoid.comap_id
- \+ *lemma* submonoid.comap_inf_map_of_injective
- \+ *lemma* submonoid.comap_infi_map_of_injective
- \+ *lemma* submonoid.comap_injective_of_surjective
- \+ *lemma* submonoid.comap_le_comap_iff_of_surjective
- \+ *lemma* submonoid.comap_map_comap
- \+ *lemma* submonoid.comap_map_eq_of_injective
- \+ *lemma* submonoid.comap_strict_mono_of_surjective
- \+ *lemma* submonoid.comap_sup_map_of_injective
- \+ *lemma* submonoid.comap_supr_map_of_injective
- \+ *lemma* submonoid.comap_surjective_of_injective
- \+ *def* submonoid.gci_map_comap
- \+ *def* submonoid.gi_map_comap
- \+ *lemma* submonoid.le_comap_map
- \+ *lemma* submonoid.le_comap_of_map_le
- \+ *lemma* submonoid.map_comap_eq_of_surjective
- \+ *lemma* submonoid.map_comap_le
- \+ *lemma* submonoid.map_comap_map
- \+ *lemma* submonoid.map_inf_comap_of_surjective
- \+ *lemma* submonoid.map_infi_comap_of_surjective
- \+ *lemma* submonoid.map_injective_of_injective
- \+ *lemma* submonoid.map_le_map_iff_of_injective
- \+ *lemma* submonoid.map_le_of_le_comap
- \+ *lemma* submonoid.map_strict_mono_of_injective
- \+ *lemma* submonoid.map_sup_comap_of_surjective
- \+ *lemma* submonoid.map_supr_comap_of_surjective
- \+ *lemma* submonoid.map_surjective_of_surjective
- \+ *lemma* submonoid.monotone_comap
- \+ *lemma* submonoid.monotone_map



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
- \+ *lemma* ennreal.of_real_add_le
- \+ *lemma* ennreal.of_real_coe_nnreal
- \+/\- *lemma* ennreal.of_real_eq_coe_nnreal
- \+ *lemma* ennreal.to_real_of_real'
- \+/\- *lemma* ennreal.to_real_of_real

Modified src/measure_theory/lebesgue_measure.lean
- \+ *lemma* measure_theory.borel_le_lebesgue_measurable
- \+/\- *lemma* measure_theory.lebesgue_length_eq_infi_Icc
- \+/\- *lemma* measure_theory.lebesgue_length_eq_infi_Ioo
- \+/\- *lemma* measure_theory.lebesgue_length_mono
- \+ *lemma* measure_theory.lebesgue_outer_Ioc
- \+/\- *lemma* real.volume_Icc
- \+/\- *lemma* real.volume_Ico
- \+ *lemma* real.volume_Ioc
- \+/\- *lemma* real.volume_Ioo
- \- *lemma* real.volume_lt_top_of_bounded
- \- *lemma* real.volume_lt_top_of_compact
- \+/\- *lemma* real.volume_singleton

Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean
- \+ *lemma* measure_theory.outer_measure.diff_null



## [2020-08-04 10:47:04](https://github.com/leanprover-community/mathlib/commit/8f02ad2)
feat(geometry/euclidean): orthogonal projection ([#3662](https://github.com/leanprover-community/mathlib/pull/3662))
Define orthogonal projection onto an affine subspace of a Euclidean
affine space, and prove some basic lemmas about it.
#### Estimated changes
Modified src/geometry/euclidean.lean
- \+ *lemma* euclidean_geometry.dist_orthogonal_projection_eq_zero_iff
- \+ *lemma* euclidean_geometry.dist_orthogonal_projection_ne_zero_of_not_mem
- \+ *lemma* euclidean_geometry.dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
- \+ *lemma* euclidean_geometry.dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd
- \+ *lemma* euclidean_geometry.inter_eq_singleton_orthogonal_projection
- \+ *lemma* euclidean_geometry.inter_eq_singleton_orthogonal_projection_fn
- \+ *def* euclidean_geometry.orthogonal_projection
- \+ *lemma* euclidean_geometry.orthogonal_projection_eq_self_iff
- \+ *def* euclidean_geometry.orthogonal_projection_fn
- \+ *lemma* euclidean_geometry.orthogonal_projection_fn_eq
- \+ *lemma* euclidean_geometry.orthogonal_projection_fn_mem
- \+ *lemma* euclidean_geometry.orthogonal_projection_fn_mem_orthogonal
- \+ *lemma* euclidean_geometry.orthogonal_projection_fn_vsub_mem_direction_orthogonal
- \+ *lemma* euclidean_geometry.orthogonal_projection_mem
- \+ *lemma* euclidean_geometry.orthogonal_projection_mem_orthogonal
- \+ *lemma* euclidean_geometry.orthogonal_projection_vadd_eq_self
- \+ *lemma* euclidean_geometry.orthogonal_projection_vadd_smul_vsub_orthogonal_projection
- \+ *lemma* euclidean_geometry.orthogonal_projection_vsub_mem_direction
- \+ *lemma* euclidean_geometry.orthogonal_projection_vsub_mem_direction_orthogonal
- \+ *lemma* euclidean_geometry.vsub_orthogonal_projection_mem_direction
- \+ *lemma* euclidean_geometry.vsub_orthogonal_projection_mem_direction_orthogonal



## [2020-08-04 09:49:04](https://github.com/leanprover-community/mathlib/commit/14d206b)
feat(order/filter/interval): define class `filter.is_interval_generated` ([#3663](https://github.com/leanprover-community/mathlib/pull/3663))
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *theorem* set.exists_finite_iff_finset

Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis_infi_principal_finite

Added src/order/filter/interval.lean
- \+ *lemma* filter.has_basis.is_interval_generated
- \+ *lemma* filter.has_ord_connected_basis
- \+ *lemma* filter.is_interval_generated_principal_iff
- \+ *lemma* filter.tendsto.Icc
- \+ *lemma* filter.tendsto.Ico
- \+ *lemma* filter.tendsto.Ioc
- \+ *lemma* filter.tendsto.Ioo
- \+ *lemma* filter.tendsto.Ixx
- \+ *lemma* filter.tendsto_Ixx_same_filter
- \+ *lemma* set.ord_connected.is_interval_generated_inf_principal

Modified src/topology/algebra/ordered.lean




## [2020-08-04 09:49:02](https://github.com/leanprover-community/mathlib/commit/ed377e1)
feat(analysis/convex): a local minimum of a convex function is a global minimum ([#3613](https://github.com/leanprover-community/mathlib/pull/3613))
#### Estimated changes
Added src/analysis/convex/extrema.lean
- \+ *lemma* is_min_on.of_is_local_min_of_convex_univ
- \+ *lemma* is_min_on.of_is_local_min_on_of_convex_on
- \+ *lemma* is_min_on.of_is_local_min_on_of_convex_on_Icc

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* affine_map.decomp'
- \+ *lemma* affine_map.decomp

Added src/topology/algebra/affine.lean
- \+ *lemma* affine_map.continuous_iff
- \+ *lemma* affine_map.line_map_continuous



## [2020-08-04 09:09:02](https://github.com/leanprover-community/mathlib/commit/b4a6651)
chore(order/filter/at_top_bot): golf three proofs ([#3684](https://github.com/leanprover-community/mathlib/pull/3684))
Also add `is_countably_generated_at_top`.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.at_top_finset_eq_infi
- \+ *lemma* filter.is_countably_generated_at_top
- \+/\- *lemma* filter.monotone.tendsto_at_top_finset



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
- \+ *lemma* measure_theory.measure.regular.inner_regular_eq
- \+ *lemma* measure_theory.measure.regular.outer_regular_eq
- \+ *structure* measure_theory.measure.regular

Added src/measure_theory/group.lean
- \+ *def* measure_theory.is_left_invariant
- \+ *lemma* measure_theory.is_left_invariant_conj'
- \+ *lemma* measure_theory.is_left_invariant_conj
- \+ *def* measure_theory.is_right_invariant
- \+ *lemma* measure_theory.is_right_invariant_conj'
- \+ *lemma* measure_theory.is_right_invariant_conj
- \+ *lemma* measure_theory.measure.conj_apply
- \+ *lemma* measure_theory.measure.conj_conj
- \+ *lemma* measure_theory.measure.map_mul_left_eq_self
- \+ *lemma* measure_theory.measure.map_mul_right_eq_self
- \+ *lemma* measure_theory.measure.regular.conj
- \+ *lemma* measure_theory.regular_conj_iff

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure.ext_iff



## [2020-08-04 00:36:52](https://github.com/leanprover-community/mathlib/commit/acedda0)
chore(scripts): update nolints.txt ([#3682](https://github.com/leanprover-community/mathlib/pull/3682))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-08-03 20:53:03](https://github.com/leanprover-community/mathlib/commit/b215e95)
fix(data/set/intervals/basic): fix a typo ([#3680](https://github.com/leanprover-community/mathlib/pull/3680))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \- *lemma* set.Ioo_subset_Ioo_union_Ici
- \+ *lemma* set.Ioo_subset_Ioo_union_Ico



## [2020-08-03 20:53:01](https://github.com/leanprover-community/mathlib/commit/234011d)
chore(order/filter/lift): prove `has_basis.lift` and `has_basis.lift'` ([#3618](https://github.com/leanprover-community/mathlib/pull/3618))
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis_principal

Modified src/order/filter/lift.lean
- \+ *lemma* filter.has_basis.lift'
- \+ *lemma* filter.has_basis.lift
- \+ *lemma* filter.has_basis.mem_lift_iff



## [2020-08-03 19:22:21](https://github.com/leanprover-community/mathlib/commit/50d1c48)
feat(order/galois_connection): galois_coinsertions ([#3656](https://github.com/leanprover-community/mathlib/pull/3656))
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* strict_mono_of_le_iff_le
- \+/\- *lemma* strict_mono_of_monotone_of_injective

Modified src/order/galois_connection.lean
- \+ *def* galois_coinsertion.dual
- \+ *lemma* galois_coinsertion.l_injective
- \+ *lemma* galois_coinsertion.l_le_l_iff
- \+ *def* galois_coinsertion.lift_bounded_lattice
- \+ *def* galois_coinsertion.lift_complete_lattice
- \+ *def* galois_coinsertion.lift_lattice
- \+ *def* galois_coinsertion.lift_order_bot
- \+ *def* galois_coinsertion.lift_semilattice_inf
- \+ *def* galois_coinsertion.lift_semilattice_sup
- \+ *def* galois_coinsertion.monotone_intro
- \+ *def* galois_coinsertion.of_dual
- \+ *lemma* galois_coinsertion.strict_mono_l
- \+ *lemma* galois_coinsertion.u_inf_l
- \+ *lemma* galois_coinsertion.u_infi_l
- \+ *lemma* galois_coinsertion.u_infi_of_lu_eq_self
- \+ *lemma* galois_coinsertion.u_l_eq
- \+ *lemma* galois_coinsertion.u_sup_l
- \+ *lemma* galois_coinsertion.u_supr_l
- \+ *lemma* galois_coinsertion.u_supr_of_lu_eq_self
- \+ *lemma* galois_coinsertion.u_surjective
- \+ *structure* galois_coinsertion
- \+ *def* galois_connection.lift_order_top
- \+ *def* galois_connection.to_galois_coinsertion
- \+ *def* galois_connection.to_galois_insertion
- \+ *def* galois_insertion.dual
- \- *lemma* galois_insertion.l_infi_of_ul
- \+ *lemma* galois_insertion.l_infi_of_ul_eq_self
- \- *lemma* galois_insertion.l_supr_of_ul
- \+ *lemma* galois_insertion.l_supr_of_ul_eq_self
- \+ *def* galois_insertion.of_dual
- \+ *lemma* galois_insertion.strict_mono_u
- \+ *lemma* galois_insertion.u_le_u_iff



## [2020-08-03 19:22:19](https://github.com/leanprover-community/mathlib/commit/40c6a29)
feat(measure_theory/content): define outer measure from content ([#3649](https://github.com/leanprover-community/mathlib/pull/3649))
Part of the development for the Haar measure: define an outer measure from a content.
#### Estimated changes
Added src/measure_theory/content.lean
- \+ *def* measure_theory.inner_content
- \+ *lemma* measure_theory.inner_content_Sup_nat
- \+ *lemma* measure_theory.inner_content_Union_nat
- \+ *lemma* measure_theory.inner_content_empty
- \+ *lemma* measure_theory.inner_content_exists_compact
- \+ *lemma* measure_theory.inner_content_le
- \+ *lemma* measure_theory.inner_content_mono'
- \+ *lemma* measure_theory.inner_content_mono
- \+ *lemma* measure_theory.inner_content_of_is_compact
- \+ *lemma* measure_theory.inner_content_pos
- \+ *lemma* measure_theory.is_left_invariant_inner_content
- \+ *lemma* measure_theory.le_inner_content
- \+ *lemma* measure_theory.outer_measure.le_of_content_compacts
- \+ *def* measure_theory.outer_measure.of_content
- \+ *lemma* measure_theory.outer_measure.of_content_exists_compact
- \+ *lemma* measure_theory.outer_measure.of_content_exists_open
- \+ *lemma* measure_theory.outer_measure.of_content_interior_compacts
- \+ *lemma* measure_theory.outer_measure.of_content_opens
- \+ *lemma* measure_theory.outer_measure.of_content_pos_of_is_open



## [2020-08-03 17:57:40](https://github.com/leanprover-community/mathlib/commit/018309f)
chore(linear_algebra/basis): replace explicit arguments for 0 ≠ 1 with nontrivial R ([#3678](https://github.com/leanprover-community/mathlib/pull/3678))
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/linear_algebra/basis.lean
- \+/\- *lemma* eq_of_linear_independent_of_span_subtype
- \+/\- *lemma* is_basis.injective
- \+/\- *lemma* le_of_span_le_span
- \+/\- *lemma* linear_independent.injective
- \+/\- *lemma* linear_independent.ne_zero
- \+/\- *lemma* span_le_span_iff
- \+/\- *lemma* surjective_of_linear_independent_of_span

Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/matrix.lean


Modified src/ring_theory/noetherian.lean




## [2020-08-03 17:57:38](https://github.com/leanprover-community/mathlib/commit/6186c69)
feat(group_theory/subgroup): range_gpowers_hom ([#3677](https://github.com/leanprover-community/mathlib/pull/3677))
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* add_subgroup.range_gmultiples_hom
- \+ *lemma* subgroup.range_gpowers_hom



## [2020-08-03 17:57:36](https://github.com/leanprover-community/mathlib/commit/b8df8aa)
feat(algebra/ring): the codomain of a ring hom is trivial iff ... ([#3676](https://github.com/leanprover-community/mathlib/pull/3676))
In the discussion of [#3488](https://github.com/leanprover-community/mathlib/pull/3488), Johan (currently on vacation, so I'm not pinging him) noted that we were missing the lemma "if `f` is a ring homomorphism, `∀ x, f x = 0` implies that the codomain is trivial". This PR adds a couple of ways to derive from homomorphisms that rings are trivial.
I used `0 = 1` to express that the ring is trivial because that seems to be the one that is used in practice.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* ring_hom.codomain_trivial_iff_map_one_eq_zero
- \+ *lemma* ring_hom.codomain_trivial_iff_range_eq_singleton_zero
- \+ *lemma* ring_hom.codomain_trivial_iff_range_trivial
- \+ *lemma* ring_hom.domain_nontrivial
- \+ *lemma* ring_hom.map_one_ne_zero

Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.map_monic_ne_zero

Modified src/ring_theory/ideal_over.lean
- \+/\- *lemma* ideal.comap_lt_comap_of_integral_mem_sdiff



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
- \+ *lemma* isometric.isometry_vadd_vsub_of_isometry



## [2020-08-03 17:57:32](https://github.com/leanprover-community/mathlib/commit/aef7ade)
feat(data/set/intervals): a few lemmas needed by FTC-1 ([#3653](https://github.com/leanprover-community/mathlib/pull/3653))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* set.Ico_diff_Iio
- \+/\- *lemma* set.Ico_inter_Iio
- \+ *lemma* set.Ioc_union_Ioc
- \+ *lemma* set.Ioc_union_Ioc_left
- \+ *lemma* set.Ioc_union_Ioc_right
- \+ *lemma* set.Ioc_union_Ioc_symm
- \+ *lemma* set.Ioc_union_Ioc_union_Ioc_cycle

Modified src/data/set/intervals/disjoint.lean
- \+ *lemma* set.Ico_disjoint_Ico_same
- \+ *lemma* set.Ioc_disjoint_Ioc
- \+ *lemma* set.Ioc_disjoint_Ioc_same



## [2020-08-03 16:25:13](https://github.com/leanprover-community/mathlib/commit/c6381aa)
chore(algebra/group_ring_action): docstring, move monoid.End to algebra/group/hom ([#3671](https://github.com/leanprover-community/mathlib/pull/3671))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* add_monoid.coe_mul
- \+ *lemma* add_monoid.coe_one
- \+ *lemma* monoid.coe_mul
- \+ *lemma* monoid.coe_one

Modified src/algebra/group_ring_action.lean
- \- *def* add_monoid.End
- \- *def* monoid.End



## [2020-08-03 14:09:09](https://github.com/leanprover-community/mathlib/commit/b2be1ee)
feat(measure_theory/measure_space): add 3 typeclasses ([#3664](https://github.com/leanprover-community/mathlib/pull/3664))
Define `probability_measure`, `finite_measure`, and `locally_finite_measure`.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean


Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.one_lt_top

Modified src/measure_theory/integration.lean
- \+/\- *lemma* measure_theory.simple_func.lintegral_congr

Modified src/measure_theory/measure_space.lean
- \+ *lemma* is_compact.finite_measure
- \+ *lemma* measure_theory.ae_mono
- \+ *lemma* measure_theory.ae_restrict_iff
- \+ *lemma* measure_theory.finite_at_filter_of_finite
- \+ *lemma* measure_theory.measure.finite_at_filter.filter_mono
- \+ *lemma* measure_theory.measure.finite_at_filter.filter_mono_ae
- \+ *lemma* measure_theory.measure.finite_at_filter.filter_sup
- \+ *lemma* measure_theory.measure.finite_at_filter.inf_ae_iff
- \+ *lemma* measure_theory.measure.finite_at_filter.inf_of_left
- \+ *lemma* measure_theory.measure.finite_at_filter.inf_of_right
- \+ *def* measure_theory.measure.finite_at_filter
- \+ *lemma* measure_theory.measure.finite_at_nhds
- \+ *lemma* measure_theory.measure.finite_at_nhds_within
- \+ *lemma* measure_theory.measure.finite_at_principal
- \+ *lemma* measure_theory.measure.le_sum
- \+/\- *lemma* measure_theory.measure_congr
- \- *lemma* measure_theory.measure_diff_of_ae_imp
- \+ *lemma* measure_theory.measure_diff_of_ae_le
- \- *lemma* measure_theory.measure_le_of_ae_imp
- \+ *lemma* measure_theory.measure_mono_ae
- \+ *lemma* measure_theory.restrict_congr
- \+ *lemma* measure_theory.restrict_mono_ae
- \+ *lemma* metric.bounded.finite_measure

Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_eq.filter_mono
- \- *lemma* filter.eventually_eq.mem_iff
- \+ *lemma* filter.eventually_eq_set
- \- *lemma* filter.eventually_set_ext



## [2020-08-03 11:29:40](https://github.com/leanprover-community/mathlib/commit/3781435)
feat(algebra/category/Group): the category of abelian groups is abelian ([#3621](https://github.com/leanprover-community/mathlib/pull/3621))
#### Estimated changes
Added src/algebra/category/Group/abelian.lean
- \+ *def* AddCommGroup.normal_epi
- \+ *def* AddCommGroup.normal_mono

Modified src/algebra/category/Module/abelian.lean
- \+/\- *def* Module.normal_epi
- \+/\- *def* Module.normal_mono

Modified src/category_theory/limits/shapes/equalizers.lean
- \+/\- *def* category_theory.limits.parallel_pair

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.comp_nat_iso
- \+ *def* category_theory.limits.iso_of_ι
- \+ *def* category_theory.limits.iso_of_π
- \+ *def* category_theory.limits.of_ι_congr
- \+ *def* category_theory.limits.of_π_congr

Modified src/category_theory/limits/shapes/regular_mono.lean
- \+ *def* category_theory.equivalence_reflects_normal_epi
- \+ *def* category_theory.equivalence_reflects_normal_mono

Modified src/category_theory/limits/shapes/zero.lean
- \+/\- *lemma* category_theory.limits.equivalence_preserves_zero_morphisms
- \+ *lemma* category_theory.limits.is_equivalence_preserves_zero_morphisms



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
- \+ *lemma* eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
- \+ *lemma* eq_orthogonal_projection_of_mem_of_inner_eq_zero
- \+ *def* orthogonal_projection
- \+ *def* orthogonal_projection_fn
- \+ *lemma* orthogonal_projection_fn_eq
- \+ *lemma* orthogonal_projection_fn_inner_eq_zero
- \+ *lemma* orthogonal_projection_fn_mem
- \+ *lemma* orthogonal_projection_inner_eq_zero
- \+ *lemma* orthogonal_projection_mem



## [2020-08-03 10:04:53](https://github.com/leanprover-community/mathlib/commit/8e0d111)
feat(data/finset/lattice,data/finset/sort): singleton lemmas ([#3668](https://github.com/leanprover-community/mathlib/pull/3668))
Add lemmas about `min'`, `max'` and `mono_of_fin` for a singleton
`finset`.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.max'_singleton
- \+ *lemma* finset.min'_singleton

Modified src/data/finset/sort.lean
- \+ *lemma* finset.mono_of_fin_singleton



## [2020-08-03 10:04:51](https://github.com/leanprover-community/mathlib/commit/61db67d)
chore(measure_theory/integration): define composition of a `simple_func` and a measurable function ([#3667](https://github.com/leanprover-community/mathlib/pull/3667))
#### Estimated changes
Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.simple_func.coe_comp
- \+ *def* measure_theory.simple_func.comp
- \+ *lemma* measure_theory.simple_func.range_comp_subset_range



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
- \+ *lemma* monoid_hom.mrange_eq_map



## [2020-08-03 08:41:40](https://github.com/leanprover-community/mathlib/commit/d3e1f5f)
feat(README): add @Vierkantor to maintainer list ([#3674](https://github.com/leanprover-community/mathlib/pull/3674))
#### Estimated changes
Modified README.md




## [2020-08-03 07:29:19](https://github.com/leanprover-community/mathlib/commit/d6c17c9)
feat(linear_algebra/affine_space): simplex ext lemmas ([#3669](https://github.com/leanprover-community/mathlib/pull/3669))
Add `ext` lemmas for `affine_space.simplex`.
#### Estimated changes
Modified src/linear_algebra/affine_space.lean
- \+ *lemma* affine_space.simplex.ext
- \+ *lemma* affine_space.simplex.ext_iff



## [2020-08-03 05:29:42](https://github.com/leanprover-community/mathlib/commit/60ba478)
feat(algebra/category/Module): the category of R-modules is abelian ([#3606](https://github.com/leanprover-community/mathlib/pull/3606))
#### Estimated changes
Added src/algebra/category/Module/abelian.lean
- \+ *def* Module.normal_epi
- \+ *def* Module.normal_mono

Modified src/algebra/category/Module/basic.lean
- \+ *def* Module.as_hom
- \+ *lemma* Module.epi_of_range_eq_top
- \+ *lemma* Module.ker_eq_bot_of_mono
- \- *def* Module.kernel_cone
- \- *def* Module.kernel_is_limit
- \+ *lemma* Module.mono_of_ker_eq_bot
- \+ *lemma* Module.range_eq_top_of_epi
- \+ *def* linear_equiv.to_Module_iso'

Added src/algebra/category/Module/kernels.lean
- \+ *def* Module.cokernel_cocone
- \+ *def* Module.cokernel_is_colimit
- \+ *def* Module.has_cokernels_Module
- \+ *def* Module.has_kernels_Module
- \+ *def* Module.kernel_cone
- \+ *def* Module.kernel_is_limit

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.comp_ker_subtype
- \+ *lemma* linear_map.ker_eq_bot_of_cancel
- \+ *lemma* linear_map.range_eq_top_of_cancel
- \+ *lemma* linear_map.range_mkq_comp
- \+ *def* submodule.quot_equiv_of_eq



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




## [2020-08-02 16:01:03](https://github.com/leanprover-community/mathlib/commit/4588400)
chore(group_theory/*): refactor quotient groups to use bundled subgroups ([#3321](https://github.com/leanprover-community/mathlib/pull/3321))
#### Estimated changes
Modified src/algebra/category/Group/adjunctions.lean


Modified src/algebra/category/Group/colimits.lean


Modified src/algebra/category/Group/images.lean
- \+/\- *def* AddCommGroup.factor_thru_image
- \+/\- *def* AddCommGroup.image.ι
- \+/\- *def* AddCommGroup.image

Modified src/algebra/group/type_tags.lean
- \+ *def* add_monoid_hom.to_multiplicative'
- \+ *def* monoid_hom.to_additive'

Modified src/algebra/group_action_hom.lean


Modified src/algebra/group_ring_action.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/category_theory/action.lean
- \+/\- *def* category_theory.action_category.stabilizer_iso_End
- \+/\- *lemma* category_theory.action_category.stabilizer_iso_End_apply

Modified src/data/equiv/mul_add.lean


Modified src/deprecated/subgroup.lean


Modified src/deprecated/submonoid.lean


Modified src/field_theory/finite.lean


Modified src/group_theory/abelianization.lean
- \+/\- *lemma* abelianization.commutator_subset_ker
- \+ *theorem* abelianization.hom_ext
- \+/\- *lemma* abelianization.lift.of
- \+/\- *def* abelianization.lift
- \+/\- *def* abelianization.of
- \+/\- *def* commutator

Modified src/group_theory/coset.lean
- \+/\- *theorem* eq_cosets_of_normal
- \- *def* is_subgroup.left_coset_equiv_subgroup
- \+/\- *theorem* normal_iff_eq_cosets
- \+/\- *theorem* normal_of_eq_cosets
- \+ *def* quotient_add_group.quotient
- \+/\- *lemma* quotient_group.eq_class_eq_left_coset
- \+/\- *def* quotient_group.left_rel
- \+/\- *def* quotient_group.quotient
- \+/\- *lemma* right_coset_mem_right_coset
- \+ *def* subgroup.left_coset_equiv_subgroup

Modified src/group_theory/free_abelian_group.lean
- \+/\- *def* free_abelian_group.lift
- \+ *def* free_abelian_group.map
- \+ *lemma* free_abelian_group.of_mul
- \+ *lemma* free_abelian_group.of_mul_of
- \+ *lemma* free_abelian_group.of_one
- \+ *lemma* free_abelian_group.one_def

Modified src/group_theory/free_group.lean
- \+ *theorem* free_group.closure_subset
- \+ *def* free_group.map.to_fun
- \+/\- *def* free_group.map
- \+/\- *lemma* free_group.prod.unique
- \+/\- *def* free_group.prod
- \+/\- *theorem* free_group.to_group.range_subset
- \+ *def* free_group.to_group.to_fun
- \+/\- *theorem* free_group.to_group.unique
- \+/\- *def* free_group.to_group

Modified src/group_theory/group_action.lean
- \+/\- *def* mul_action.comp_hom
- \+ *lemma* mul_action.eq_inv_smul_iff
- \+ *lemma* mul_action.inv_smul_eq_iff
- \+/\- *def* mul_action.mul_left_cosets
- \+ *def* mul_action.stabilizer.subgroup
- \+ *def* mul_action.stabilizer.submonoid
- \+/\- *def* mul_action.stabilizer
- \+ *def* mul_action.stabilizer_carrier

Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* card_eq_card_quotient_mul_card_subgroup
- \+/\- *lemma* card_quotient_dvd_card
- \+/\- *lemma* card_subgroup_dvd_card
- \+/\- *lemma* card_trivial
- \+ *lemma* mem_powers_iff_mem_gpowers
- \+/\- *lemma* order_eq_card_gpowers
- \+/\- *lemma* powers_eq_gpowers

Modified src/group_theory/presented_group.lean
- \+/\- *lemma* presented_group.closure_rels_subset_ker
- \+/\- *theorem* presented_group.to_group.unique
- \+/\- *def* presented_group.to_group
- \+/\- *lemma* presented_group.to_group_eq_one_of_mem_closure

Modified src/group_theory/quotient_group.lean
- \+/\- *def* quotient_group.ker_lift
- \+/\- *def* quotient_group.lift
- \+/\- *lemma* quotient_group.lift_mk'
- \+/\- *lemma* quotient_group.lift_mk
- \+/\- *def* quotient_group.map
- \+ *def* quotient_group.mk'
- \+ *def* quotient_group.range_ker_lift
- \+ *lemma* quotient_group.range_ker_lift_injective
- \+ *lemma* quotient_group.range_ker_lift_surjective

Modified src/group_theory/subgroup.lean
- \+ *lemma* add_subgroup.gmultiples_subset
- \+/\- *lemma* monoid_hom.mem_ker
- \+ *def* monoid_hom.to_range
- \+ *lemma* monoid_hom.to_range_ker
- \+ *lemma* subgroup.gpowers_subset
- \+/\- *lemma* subgroup.mem_bot
- \+ *def* subgroup.set_normalizer

Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* add_submonoid.mem_multiples
- \+ *def* add_submonoid.multiples
- \+ *lemma* add_submonoid.multiples_eq_closure
- \+ *lemma* add_submonoid.multiples_subset
- \+ *lemma* submonoid.mem_powers
- \+ *def* submonoid.powers
- \+ *lemma* submonoid.powers_eq_closure
- \+ *lemma* submonoid.powers_subset

Modified src/group_theory/sylow.lean
- \+/\- *lemma* quotient_group.card_preimage_mk
- \+/\- *def* sylow.fixed_points_mul_left_cosets_equiv_quotient
- \+/\- *lemma* sylow.mem_fixed_points_mul_left_cosets_iff_mem_normalizer

Modified src/number_theory/quadratic_reciprocity.lean


Modified src/ring_theory/free_comm_ring.lean
- \+/\- *def* free_comm_ring.lift
- \+/\- *lemma* free_comm_ring.lift_comp_of
- \+ *lemma* free_comm_ring.lift_hom_comp_of
- \+/\- *def* free_comm_ring.restriction
- \+/\- *def* free_ring.to_free_comm_ring

Modified src/ring_theory/free_ring.lean
- \+ *def* free_ring.lift_hom
- \+ *def* free_ring.map_hom

Modified src/topology/algebra/group.lean
- \+/\- *lemma* quotient_group_saturate

Modified src/topology/algebra/monoid.lean
- \- *lemma* is_submonoid.mem_nhds_one
- \+ *lemma* submonoid.mem_nhds_one



## [2020-08-02 11:46:51](https://github.com/leanprover-community/mathlib/commit/6559832)
feat(order/filter/lift): a few lemmas about `filter.lift' _ powerset` ([#3652](https://github.com/leanprover-community/mathlib/pull/3652))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.powerset_mono
- \+ *theorem* set.powerset_nonempty

Modified src/order/filter/lift.lean
- \+ *lemma* filter.eventually_lift'_iff
- \+ *lemma* filter.eventually_lift'_powerset'
- \+ *lemma* filter.eventually_lift'_powerset
- \+ *lemma* filter.eventually_lift'_powerset_eventually
- \+ *lemma* filter.eventually_lift'_powerset_forall



## [2020-08-02 11:46:49](https://github.com/leanprover-community/mathlib/commit/fe4da7b)
feat(category_theory/limits): transporting is_limit ([#3598](https://github.com/leanprover-community/mathlib/pull/3598))
Some lemmas about moving `is_limit` terms around over equivalences, or (post|pre)composing.
#### Estimated changes
Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.is_colimit.hom_is_iso
- \+ *def* category_theory.limits.is_colimit.of_left_adjoint
- \+ *def* category_theory.limits.is_colimit.precompose_hom_equiv
- \+ *def* category_theory.limits.is_colimit.precompose_inv_equiv
- \+ *def* category_theory.limits.is_limit.hom_is_iso
- \+ *def* category_theory.limits.is_limit.of_right_adjoint
- \+ *def* category_theory.limits.is_limit.postcompose_hom_equiv
- \+ *def* category_theory.limits.is_limit.postcompose_inv_equiv

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
Added src/category_theory/monoidal/internal/functor_category.lean
- \+ *def* category_theory.monoidal.Mon_functor_category_equivalence.counit_iso
- \+ *def* category_theory.monoidal.Mon_functor_category_equivalence.functor
- \+ *def* category_theory.monoidal.Mon_functor_category_equivalence.inverse
- \+ *def* category_theory.monoidal.Mon_functor_category_equivalence.unit_iso
- \+ *def* category_theory.monoidal.Mon_functor_category_equivalence

Modified src/category_theory/natural_transformation.lean
- \+ *lemma* category_theory.congr_app



## [2020-08-02 11:46:45](https://github.com/leanprover-community/mathlib/commit/e99518b)
feat(category_theory): braided and symmetric categories ([#3550](https://github.com/leanprover-community/mathlib/pull/3550))
Just the very basics:
* the definition of braided and symmetric categories
* braided functors, and compositions thereof
* the symmetric monoidal structure coming from products
* upgrading `Type u` to a symmetric monoidal structure
This is prompted by the desire to explore modelling sheaves of modules as the monoidal category of module objects for an internal commutative monoid in sheaves of `Ab`.
#### Estimated changes
Added src/category_theory/monoidal/braided.lean
- \+ *def* category_theory.braided_functor.comp
- \+ *def* category_theory.braided_functor.id
- \+ *structure* category_theory.braided_functor

Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/monoidal/of_has_finite_products.lean
- \+ *def* category_theory.symmetric_of_has_finite_coproducts
- \+ *def* category_theory.symmetric_of_has_finite_products

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
- \+ *lemma* quot.lift_on₂_mk
- \+ *lemma* quot.lift₂_mk
- \+ *lemma* quot.map₂_mk

Added src/linear_algebra/tensor_algebra.lean
- \+ *theorem* tensor_algebra.hom_ext
- \+ *def* tensor_algebra.lift
- \+ *theorem* tensor_algebra.lift_comp_ι
- \+ *def* tensor_algebra.lift_fun
- \+ *theorem* tensor_algebra.lift_unique
- \+ *def* tensor_algebra.pre.has_add
- \+ *def* tensor_algebra.pre.has_coe_module
- \+ *def* tensor_algebra.pre.has_coe_semiring
- \+ *def* tensor_algebra.pre.has_mul
- \+ *def* tensor_algebra.pre.has_one
- \+ *def* tensor_algebra.pre.has_scalar
- \+ *def* tensor_algebra.pre.has_zero
- \+ *inductive* tensor_algebra.pre
- \+ *inductive* tensor_algebra.rel
- \+ *def* tensor_algebra.ι
- \+ *theorem* tensor_algebra.ι_comp_lift
- \+ *def* tensor_algebra



## [2020-08-02 10:18:28](https://github.com/leanprover-community/mathlib/commit/58f2c36)
feat(dynamics/periodic_pts): definition and basic properties ([#3660](https://github.com/leanprover-community/mathlib/pull/3660))
Also add more lemmas about `inj/surj/bij_on` and `maps_to`.
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* set.bij_on.inter
- \+ *lemma* set.bij_on.union
- \+ *theorem* set.maps_to.inter
- \+ *theorem* set.maps_to.inter_inter
- \+ *theorem* set.maps_to.union
- \+ *theorem* set.maps_to.union_union
- \+ *theorem* set.surj_on.inter
- \+ *theorem* set.surj_on.inter_inter
- \+ *theorem* set.surj_on.union
- \+ *theorem* set.surj_on.union_union

Modified src/data/set/lattice.lean
- \+ *lemma* set.bij_on_Inter
- \+ *lemma* set.bij_on_Inter_of_directed
- \+ *lemma* set.bij_on_Union
- \+ *lemma* set.bij_on_Union_of_directed
- \+ *lemma* set.image_Inter_subset
- \+ *lemma* set.image_bInter_subset
- \+ *lemma* set.image_sInter_subset
- \+ *lemma* set.inj_on.image_Inter_eq
- \+ *lemma* set.inj_on.image_bInter_eq
- \+ *lemma* set.inj_on_Union_of_directed
- \+ *lemma* set.maps_to_Inter
- \+ *lemma* set.maps_to_Inter_Inter
- \+ *lemma* set.maps_to_Union
- \+ *lemma* set.maps_to_Union_Union
- \+ *lemma* set.maps_to_bInter
- \+ *lemma* set.maps_to_bInter_bInter
- \+ *lemma* set.maps_to_bUnion
- \+ *lemma* set.maps_to_bUnion_bUnion
- \+ *lemma* set.maps_to_sInter
- \+ *lemma* set.maps_to_sUnion
- \+ *lemma* set.surj_on_Inter
- \+ *lemma* set.surj_on_Inter_Inter
- \+ *lemma* set.surj_on_Union
- \+ *lemma* set.surj_on_Union_Union
- \+ *lemma* set.surj_on_bUnion
- \+ *lemma* set.surj_on_bUnion_bUnion
- \+ *lemma* set.surj_on_sUnion

Added src/dynamics/periodic_pts.lean
- \+ *lemma* function.Union_pnat_pts_of_period
- \+ *lemma* function.bUnion_pts_of_period
- \+ *lemma* function.bij_on_periodic_pts
- \+ *lemma* function.bij_on_pts_of_period
- \+ *lemma* function.directed_pts_of_period_pnat
- \+ *lemma* function.is_fixed_pt.is_periodic_pt
- \+ *lemma* function.is_periodic_id
- \+ *lemma* function.is_periodic_pt.apply_iterate
- \+ *lemma* function.is_periodic_pt.eq_of_apply_eq
- \+ *lemma* function.is_periodic_pt.eq_of_apply_eq_same
- \+ *lemma* function.is_periodic_pt.eq_zero_of_lt_minimal_period
- \+ *lemma* function.is_periodic_pt.left_of_add
- \+ *lemma* function.is_periodic_pt.minimal_period_dvd
- \+ *lemma* function.is_periodic_pt.minimal_period_le
- \+ *lemma* function.is_periodic_pt.minimal_period_pos
- \+ *lemma* function.is_periodic_pt.right_of_add
- \+ *lemma* function.is_periodic_pt.trans_dvd
- \+ *def* function.is_periodic_pt
- \+ *lemma* function.is_periodic_pt_iff_minimal_period_dvd
- \+ *lemma* function.is_periodic_pt_minimal_period
- \+ *lemma* function.is_periodic_pt_zero
- \+ *lemma* function.mem_periodic_pts
- \+ *lemma* function.mem_pts_of_period
- \+ *def* function.minimal_period
- \+ *lemma* function.minimal_period_pos_iff_mem_periodic_pts
- \+ *lemma* function.minimal_period_pos_of_mem_periodic_pts
- \+ *lemma* function.mk_mem_periodic_pts
- \+ *def* function.periodic_pts
- \+ *def* function.pts_of_period
- \+ *lemma* function.semiconj.maps_to_periodic_pts
- \+ *lemma* function.semiconj.maps_to_pts_of_period



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
- \+/\- *lemma* convex_Icc
- \+/\- *lemma* convex_Ici
- \+/\- *lemma* convex_Ico
- \+/\- *lemma* convex_Iic
- \+/\- *lemma* convex_Iio
- \+/\- *lemma* convex_Ioc
- \+/\- *lemma* convex_Ioi
- \+/\- *lemma* convex_Ioo
- \+ *lemma* convex_interval
- \- *lemma* convex_real_iff
- \+ *lemma* real.convex_iff_ord_connected

Modified src/analysis/convex/topology.lean
- \+ *lemma* real.convex_iff_is_preconnected

Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* set.Icc_diff_Ico_same
- \+/\- *lemma* set.Icc_diff_Ioc_same
- \+/\- *lemma* set.Icc_diff_Ioo_same
- \+/\- *lemma* set.Icc_diff_both
- \+/\- *lemma* set.Icc_diff_left
- \+/\- *lemma* set.Icc_diff_right
- \+/\- *lemma* set.Ici_diff_Ioi_same
- \+/\- *lemma* set.Ici_diff_left
- \+/\- *lemma* set.Ico_diff_Ioo_same
- \+/\- *lemma* set.Ico_diff_left
- \+/\- *lemma* set.Iic_diff_Iio_same
- \+/\- *lemma* set.Iic_diff_right
- \+/\- *lemma* set.Iio_union_right
- \+/\- *lemma* set.Ioc_diff_Ioo_same
- \+/\- *lemma* set.Ioc_diff_right
- \+/\- *lemma* set.Ioi_union_left

Added src/data/set/intervals/ord_connected.lean
- \+ *lemma* set.ord_connected.dual
- \+ *lemma* set.ord_connected.inter
- \+ *lemma* set.ord_connected.interval_subset
- \+ *def* set.ord_connected
- \+ *lemma* set.ord_connected_Icc
- \+ *lemma* set.ord_connected_Ici
- \+ *lemma* set.ord_connected_Ico
- \+ *lemma* set.ord_connected_Iic
- \+ *lemma* set.ord_connected_Iio
- \+ *lemma* set.ord_connected_Inter
- \+ *lemma* set.ord_connected_Ioc
- \+ *lemma* set.ord_connected_Ioi
- \+ *lemma* set.ord_connected_Ioo
- \+ *lemma* set.ord_connected_bInter
- \+ *lemma* set.ord_connected_dual
- \+ *lemma* set.ord_connected_empty
- \+ *lemma* set.ord_connected_iff
- \+ *lemma* set.ord_connected_iff_interval_subset
- \+ *lemma* set.ord_connected_interval
- \+ *lemma* set.ord_connected_of_Ioo
- \+ *lemma* set.ord_connected_sInter
- \+ *lemma* set.ord_connected_univ

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* is_preconnected_Ici
- \+/\- *lemma* is_preconnected_Ico
- \+/\- *lemma* is_preconnected_Iic
- \+/\- *lemma* is_preconnected_Iio
- \+/\- *lemma* is_preconnected_Ioc
- \+/\- *lemma* is_preconnected_Ioi
- \+/\- *lemma* is_preconnected_Ioo
- \- *lemma* is_preconnected_iff_forall_Icc_subset
- \+ *lemma* is_preconnected_iff_ord_connected
- \+ *lemma* is_preconnected_interval



## [2020-08-02 08:31:19](https://github.com/leanprover-community/mathlib/commit/f2db6a8)
chore(algebra/order): enable dot syntax ([#3643](https://github.com/leanprover-community/mathlib/pull/3643))
Add dot syntax aliases to some lemmas about order (e.g.,
`has_le.le.trans`). Also remove `lt_of_le_of_ne'` (was equivalent
to `lt_of_le_of_ne`).
#### Estimated changes
Modified src/algebra/order.lean
- \+ *lemma* has_le.le.le_or_lt
- \+ *lemma* has_le.le.lt_or_le
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


Added src/category_theory/concrete_category/reflects_isomorphisms.lean


Modified src/category_theory/limits/cones.lean
- \+ *def* category_theory.limits.cocones.cocone_iso_of_hom_iso
- \+ *def* category_theory.limits.cones.cone_iso_of_hom_iso

Modified src/category_theory/limits/limits.lean


Modified src/category_theory/monad/algebra.lean


Modified src/category_theory/over.lean


Deleted src/category_theory/reflect_isomorphisms.lean
- \- *def* category_theory.cocone_iso_of_hom_iso
- \- *def* category_theory.cone_iso_of_hom_iso
- \- *def* category_theory.is_iso_of_reflects_iso

Added src/category_theory/reflects_isomorphisms.lean
- \+ *def* category_theory.is_iso_of_reflects_iso

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
- \+ *lemma* equiv.set.image_symm_preimage

Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* is_measurable.Union
- \+/\- *def* measurable
- \+/\- *lemma* measurable_space.dynkin_system.ext

Modified src/measure_theory/measure_space.lean
- \- *def* measure_theory.measure'
- \- *lemma* measure_theory.measure'_Union
- \- *lemma* measure_theory.measure'_Union_le_tsum_nat'
- \- *lemma* measure_theory.measure'_Union_le_tsum_nat
- \- *lemma* measure_theory.measure'_Union_nat
- \- *lemma* measure_theory.measure'_empty
- \- *lemma* measure_theory.measure'_eq
- \- *lemma* measure_theory.measure'_mono
- \- *lemma* measure_theory.measure'_union
- \+ *lemma* measure_theory.measure_eq_extend
- \+ *lemma* measure_theory.measure_eq_induced_outer_measure
- \- *lemma* measure_theory.measure_eq_measure'
- \- *lemma* measure_theory.measure_eq_outer_measure'
- \- *def* measure_theory.outer_measure'
- \- *lemma* measure_theory.outer_measure'_eq
- \- *lemma* measure_theory.outer_measure'_eq_measure'
- \- *lemma* measure_theory.outer_measure.exists_is_measurable_superset_of_trim_eq_zero
- \- *theorem* measure_theory.outer_measure.le_trim_iff
- \- *def* measure_theory.outer_measure.trim
- \- *theorem* measure_theory.outer_measure.trim_add
- \- *theorem* measure_theory.outer_measure.trim_congr
- \- *theorem* measure_theory.outer_measure.trim_eq
- \- *theorem* measure_theory.outer_measure.trim_eq_infi'
- \- *theorem* measure_theory.outer_measure.trim_eq_infi
- \- *theorem* measure_theory.outer_measure.trim_ge
- \- *theorem* measure_theory.outer_measure.trim_le_trim
- \- *theorem* measure_theory.outer_measure.trim_smul
- \- *theorem* measure_theory.outer_measure.trim_sum_ge
- \- *theorem* measure_theory.outer_measure.trim_trim
- \- *theorem* measure_theory.outer_measure.trim_zero
- \+ *lemma* measure_theory.to_outer_measure_eq_induced_outer_measure
- \- *lemma* measure_theory.to_outer_measure_eq_outer_measure'

Modified src/measure_theory/outer_measure.lean
- \+ *def* measure_theory.extend
- \+ *lemma* measure_theory.extend_Union
- \+ *lemma* measure_theory.extend_Union_le_tsum_nat'
- \+ *lemma* measure_theory.extend_Union_le_tsum_nat
- \+ *lemma* measure_theory.extend_Union_nat
- \+ *lemma* measure_theory.extend_empty
- \+ *lemma* measure_theory.extend_eq
- \+ *lemma* measure_theory.extend_mono'
- \+ *lemma* measure_theory.extend_mono
- \+ *lemma* measure_theory.extend_union
- \+ *def* measure_theory.induced_outer_measure
- \+ *lemma* measure_theory.induced_outer_measure_caratheodory
- \+ *lemma* measure_theory.induced_outer_measure_eq'
- \+ *lemma* measure_theory.induced_outer_measure_eq
- \+ *lemma* measure_theory.induced_outer_measure_eq_extend'
- \+ *lemma* measure_theory.induced_outer_measure_eq_extend
- \+ *lemma* measure_theory.induced_outer_measure_eq_infi
- \+ *lemma* measure_theory.induced_outer_measure_exists_set
- \+ *lemma* measure_theory.le_extend
- \+ *def* measure_theory.outer_measure.caratheodory_dynkin
- \- *lemma* measure_theory.outer_measure.caratheodory_is_measurable
- \+ *lemma* measure_theory.outer_measure.exists_is_measurable_superset_of_trim_eq_zero
- \+ *lemma* measure_theory.outer_measure.f_Union
- \+ *def* measure_theory.outer_measure.is_caratheodory
- \- *lemma* measure_theory.outer_measure.is_caratheodory
- \+ *lemma* measure_theory.outer_measure.is_caratheodory_Union_lt
- \+ *lemma* measure_theory.outer_measure.is_caratheodory_Union_nat
- \+ *lemma* measure_theory.outer_measure.is_caratheodory_compl
- \+ *lemma* measure_theory.outer_measure.is_caratheodory_compl_iff
- \+ *lemma* measure_theory.outer_measure.is_caratheodory_empty
- \+ *lemma* measure_theory.outer_measure.is_caratheodory_iff
- \+ *lemma* measure_theory.outer_measure.is_caratheodory_iff_le'
- \+ *lemma* measure_theory.outer_measure.is_caratheodory_iff_le
- \+ *lemma* measure_theory.outer_measure.is_caratheodory_inter
- \- *lemma* measure_theory.outer_measure.is_caratheodory_le
- \+ *lemma* measure_theory.outer_measure.is_caratheodory_sum
- \+ *lemma* measure_theory.outer_measure.is_caratheodory_union
- \+/\- *theorem* measure_theory.outer_measure.le_of_function
- \+ *theorem* measure_theory.outer_measure.le_trim
- \+ *theorem* measure_theory.outer_measure.le_trim_iff
- \+ *lemma* measure_theory.outer_measure.measure_inter_union
- \+ *lemma* measure_theory.outer_measure.of_function_caratheodory
- \+ *theorem* measure_theory.outer_measure.of_function_eq
- \+/\- *theorem* measure_theory.outer_measure.of_function_le
- \+ *def* measure_theory.outer_measure.trim
- \+ *theorem* measure_theory.outer_measure.trim_add
- \+ *theorem* measure_theory.outer_measure.trim_congr
- \+ *theorem* measure_theory.outer_measure.trim_eq
- \+ *theorem* measure_theory.outer_measure.trim_eq_infi'
- \+ *theorem* measure_theory.outer_measure.trim_eq_infi
- \+ *theorem* measure_theory.outer_measure.trim_le_trim
- \+ *theorem* measure_theory.outer_measure.trim_smul
- \+ *theorem* measure_theory.outer_measure.trim_sum_ge
- \+ *theorem* measure_theory.outer_measure.trim_trim
- \+ *theorem* measure_theory.outer_measure.trim_zero



## [2020-08-02 03:20:12](https://github.com/leanprover-community/mathlib/commit/fc65ba0)
feat(analysis/calculus/times_cont_diff): inversion is smooth ([#3639](https://github.com/leanprover-community/mathlib/pull/3639))
At an invertible element of a complete normed algebra, the inversion operation is smooth.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff.comp_times_cont_diff_at
- \+ *lemma* times_cont_diff_at.comp
- \+ *lemma* times_cont_diff_at_inverse
- \+ *theorem* times_cont_diff_at_succ_iff_has_fderiv_at

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* continuous_linear_map.lmul_left_right_is_bounded_bilinear

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *def* continuous_linear_map.lmul_left
- \+/\- *lemma* continuous_linear_map.lmul_left_apply
- \+ *lemma* continuous_linear_map.lmul_left_norm
- \+ *def* continuous_linear_map.lmul_left_right
- \+ *lemma* continuous_linear_map.lmul_left_right_apply
- \+ *lemma* continuous_linear_map.lmul_left_right_norm_le
- \+/\- *def* continuous_linear_map.lmul_right
- \+/\- *lemma* continuous_linear_map.lmul_right_apply
- \+ *lemma* continuous_linear_map.lmul_right_norm

Modified src/analysis/normed_space/units.lean
- \+ *lemma* units.nhds

Modified src/ring_theory/algebra.lean
- \+ *def* algebra.lmul_left_right
- \+ *lemma* algebra.lmul_left_right_apply



## [2020-08-02 02:10:22](https://github.com/leanprover-community/mathlib/commit/d3de289)
feat(topology/local_homeomorph): open_embedding.continuous_at_iff ([#3599](https://github.com/leanprover-community/mathlib/pull/3599))
```
lemma continuous_at_iff
  {f : α → β} {g : β → γ} (hf : open_embedding f) {x : α} :
  continuous_at (g ∘ f) x ↔ continuous_at g (f x) :=
```
#### Estimated changes
Modified src/topology/local_homeomorph.lean
- \+ *lemma* open_embedding.continuous_at_iff



## [2020-08-01 21:07:07](https://github.com/leanprover-community/mathlib/commit/4274ddd)
chore(*): bump to Lean 3.18.4 ([#3610](https://github.com/leanprover-community/mathlib/pull/3610))
* Remove `pi_arity` and the `vm_override` for `by_cases`, which have moved to core
* Fix fallout from the change to the definition of `max`
* Fix a small number of errors caused by changes to instance caching
* Remove `min_add`, which is generalized by `min_add_add_right`  and make `to_additive` generate some lemmas
#### Estimated changes
Modified leanpkg.toml


Modified src/algebra/order_functions.lean
- \- *lemma* fn_min_add_fn_max
- \- *lemma* min_add
- \- *lemma* min_add_max

Modified src/algebra/ordered_group.lean


Modified src/computability/primrec.lean
- \+/\- *theorem* primrec.nat_max

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




## [2020-08-01 15:55:33](https://github.com/leanprover-community/mathlib/commit/92a20e6)
feat(order/filter/extr, topology/local_extr): links between extremas of two eventually le/eq functions ([#3624](https://github.com/leanprover-community/mathlib/pull/3624))
Add many lemmas that look similar to e.g : if f and g are equal at `a`, and `f ≤ᶠ[l] g` for some filter `l`, then `is_min_filter l f a`implies `is_min_filter l g a`
#### Estimated changes
Modified src/order/filter/extr.lean
- \+ *lemma* filter.eventually_eq.is_extr_filter_iff
- \+ *lemma* filter.eventually_eq.is_max_filter_iff
- \+ *lemma* filter.eventually_eq.is_min_filter_iff
- \+ *lemma* filter.eventually_le.is_max_filter
- \+ *lemma* filter.eventually_le.is_min_filter
- \+ *lemma* is_extr_filter.congr
- \+ *lemma* is_max_filter.congr
- \+ *lemma* is_min_filter.congr

Modified src/topology/continuous_on.lean
- \+ *lemma* filter.eventually_eq.eq_of_nhds_within

Modified src/topology/local_extr.lean
- \+ *lemma* filter.eventually_eq.is_local_extr_iff
- \+ *lemma* filter.eventually_eq.is_local_extr_on_iff
- \+ *lemma* filter.eventually_eq.is_local_max_iff
- \+ *lemma* filter.eventually_eq.is_local_max_on_iff
- \+ *lemma* filter.eventually_eq.is_local_min_iff
- \+ *lemma* filter.eventually_eq.is_local_min_on_iff
- \+ *lemma* filter.eventually_le.is_local_max
- \+ *lemma* filter.eventually_le.is_local_max_on
- \+ *lemma* filter.eventually_le.is_local_min
- \+ *lemma* filter.eventually_le.is_local_min_on
- \+ *lemma* is_local_extr.congr
- \+ *lemma* is_local_extr_on.congr
- \+ *lemma* is_local_max.congr
- \+ *lemma* is_local_max_on.congr
- \+ *lemma* is_local_min.congr
- \+ *lemma* is_local_min_on.congr



## [2020-08-01 12:08:21](https://github.com/leanprover-community/mathlib/commit/aa67315)
chore(order/filter/bases): generalize `has_basis.restrict` ([#3645](https://github.com/leanprover-community/mathlib/pull/3645))
The old lemma is renamed to `filter.has_basis.restrict_subset`
#### Estimated changes
Modified src/order/filter/bases.lean
- \+/\- *lemma* filter.has_basis.restrict
- \+ *lemma* filter.has_basis.restrict_subset



## [2020-08-01 09:06:29](https://github.com/leanprover-community/mathlib/commit/c6f3399)
feat(topology/subset_properties): add `is_compact.induction_on` ([#3642](https://github.com/leanprover-community/mathlib/pull/3642))
#### Estimated changes
Modified src/topology/subset_properties.lean
- \+ *lemma* is_compact.induction_on

