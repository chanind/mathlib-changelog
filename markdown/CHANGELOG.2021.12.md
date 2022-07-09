## [2021-12-31 22:23:24](https://github.com/leanprover-community/mathlib/commit/8db2fa0)
chore(category_theory/closed/cartesian): make exp right-associative ([#11172](https://github.com/leanprover-community/mathlib/pull/11172))
This makes `X ⟹ Y ⟹ Z` parse as `X ⟹ (Y ⟹ Z)`, like ordinary function types.
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean



## [2021-12-31 22:23:23](https://github.com/leanprover-community/mathlib/commit/559951c)
feat(data/quot): Add quotient pi induction ([#11137](https://github.com/leanprover-community/mathlib/pull/11137))
I am planning to use this later to show that the (pi) product of homotopy classes of paths is well-defined, and prove
properties about that product.
#### Estimated changes
Modified src/data/quot.lean
- \+ *lemma* quotient.induction_on_pi
- \+/\- *theorem* quotient.choice_eq
- \+/\- *theorem* quotient.choice_eq



## [2021-12-31 22:23:22](https://github.com/leanprover-community/mathlib/commit/200f47d)
feat(analysis/normed_space/banach_steinhaus): prove the standard Banach-Steinhaus theorem ([#10663](https://github.com/leanprover-community/mathlib/pull/10663))
Here we prove the Banach-Steinhaus theorem for maps from a Banach space into a (semi-)normed space. This is the standard version of the theorem and the proof proceeds via the Baire category theorem. Notably, the version from barelled spaces to locally convex spaces is not included because these spaces do not yet exist in `mathlib`. In addition, it is established that the pointwise limit of continuous linear maps from a Banach space into a normed space is itself a continuous linear map.
- [x] depends on: [#10700](https://github.com/leanprover-community/mathlib/pull/10700)
#### Estimated changes
Created src/analysis/normed_space/banach_steinhaus.lean
- \+ *theorem* banach_steinhaus
- \+ *theorem* banach_steinhaus_supr_nnnorm
- \+ *def* continuous_linear_map_of_tendsto

Modified src/topology/metric_space/baire.lean



## [2021-12-31 21:03:20](https://github.com/leanprover-community/mathlib/commit/ea710ca)
feat(data/polynomial/ring_division): golf and generalize `leading_coeff_div_by_monic_of_monic` ([#11077](https://github.com/leanprover-community/mathlib/pull/11077))
No longer require that the underlying ring is a domain.
Also added helper API lemma `leading_coeff_monic_mul`.
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+ *theorem* leading_coeff_monic_mul

Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* leading_coeff_div_by_monic_of_monic
- \+/\- *lemma* leading_coeff_div_by_monic_of_monic



## [2021-12-31 21:03:19](https://github.com/leanprover-community/mathlib/commit/8ec59f9)
feat(data/int/gcd): add theorem `gcd_least_linear` ([#10743](https://github.com/leanprover-community/mathlib/pull/10743))
For nonzero integers `a` and `b`, `gcd a b` is the smallest positive integer that can be written in the form `a * x + b * y` for some pair of integers `x` and `y`
This is an extension of Bézout's lemma (`gcd_eq_gcd_ab`), which says that `gcd a b` can be written in that form.
#### Estimated changes
Modified src/data/int/gcd.lean
- \+ *lemma* gcd_dvd_iff
- \+ *theorem* gcd_least_linear



## [2021-12-31 19:13:58](https://github.com/leanprover-community/mathlib/commit/e4607f8)
chore(data/sym/basic): golf and add missing simp lemmas ([#11160](https://github.com/leanprover-community/mathlib/pull/11160))
By changing `cons` to not use pattern matching, `(a :: s).1 = a ::ₘ s.1` is true by `rfl`, which is convenient here and there for golfing.
#### Estimated changes
Modified src/data/setoid/basic.lean

Modified src/data/sym/basic.lean
- \+ *lemma* of_vector_nil
- \+ *lemma* of_vector_cons
- \+ *lemma* cons_erase
- \+ *lemma* exists_mem
- \+ *lemma* eq_repeat
- \+/\- *def* nil
- \+/\- *def* cons
- \- *def* of_vector
- \+/\- *def* nil
- \+/\- *def* cons
- \- *def* mem



## [2021-12-31 19:13:57](https://github.com/leanprover-community/mathlib/commit/fbbbdfa)
feat(algebra/star/self_adjoint): define the self-adjoint elements of a star additive group ([#11135](https://github.com/leanprover-community/mathlib/pull/11135))
Given a type `R` with `[add_group R] [star_add_monoid R]`, we define `self_adjoint R` as the additive subgroup of self-adjoint elements, i.e. those such that `star x = x`. To avoid confusion, we move `is_self_adjoint` (which defines this to mean `⟪T x, y⟫ = ⟪x, T y⟫` in an inner product space) to the `inner_product_space` namespace.
#### Estimated changes
Modified docs/overview.yaml

Modified docs/undergrad.yaml

Created src/algebra/star/self_adjoint.lean
- \+ *lemma* mem_iff
- \+ *lemma* star_coe_eq
- \+ *lemma* coe_one
- \+ *lemma* one_mem
- \+ *lemma* bit0_mem
- \+ *lemma* bit1_mem
- \+ *lemma* conjugate
- \+ *lemma* conjugate'
- \+ *lemma* coe_mul
- \+ *lemma* coe_inv
- \+ *def* self_adjoint

Modified src/analysis/inner_product_space/basic.lean

Modified src/analysis/inner_product_space/rayleigh.lean

Modified src/analysis/inner_product_space/spectrum.lean



## [2021-12-31 19:13:55](https://github.com/leanprover-community/mathlib/commit/fdf09df)
feat(data/polynomial/degree/lemmas): (nat_)degree_sum_eq_of_disjoint ([#11121](https://github.com/leanprover-community/mathlib/pull/11121))
Also two helper lemmas on `nat_degree`.
Generalize `degree_sum_fin_lt` to semirings
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* nat_degree_add_eq_left_of_nat_degree_lt
- \+ *lemma* nat_degree_add_eq_right_of_nat_degree_lt
- \+/\- *lemma* degree_sum_fin_lt
- \+/\- *lemma* degree_sum_fin_lt

Modified src/data/polynomial/degree/lemmas.lean
- \+ *lemma* degree_sum_eq_of_disjoint
- \+ *lemma* nat_degree_sum_eq_of_disjoint



## [2021-12-31 16:13:18](https://github.com/leanprover-community/mathlib/commit/c4caf0e)
feat(linear_algebra/multilinear/basic): add dependent version of `multilinear_map.dom_dom_congr_linear_equiv` ([#10474](https://github.com/leanprover-community/mathlib/pull/10474))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* Pi_congr_left'_update
- \+ *lemma* Pi_congr_left'_symm_update

Modified src/linear_algebra/multilinear/basic.lean
- \+ *def* dom_dom_congr_linear_equiv'



## [2021-12-31 14:15:50](https://github.com/leanprover-community/mathlib/commit/9a38c19)
feat(data/list/indexes): map_with_index_eq_of_fn ([#11163](https://github.com/leanprover-community/mathlib/pull/11163))
Some `list.map_with_index` API.
#### Estimated changes
Modified src/data/list/indexes.lean
- \+ *lemma* map_with_index_nil
- \+ *lemma* map_with_index_cons
- \+ *lemma* length_map_with_index
- \+ *lemma* nth_le_map_with_index
- \+ *lemma* map_with_index_eq_of_fn



## [2021-12-31 14:15:49](https://github.com/leanprover-community/mathlib/commit/b92afc9)
chore(data/equiv/basic): missing dsimp lemmas ([#11159](https://github.com/leanprover-community/mathlib/pull/11159))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* subtype_quotient_equiv_quotient_subtype_mk
- \+ *lemma* subtype_quotient_equiv_quotient_subtype_symm_mk



## [2021-12-31 14:15:48](https://github.com/leanprover-community/mathlib/commit/bcf1d2d)
feat(category_theory/sites/plus): Adds a functorial version of `J.diagram P`, functorial in `P`. ([#11155](https://github.com/leanprover-community/mathlib/pull/11155))
#### Estimated changes
Modified src/category_theory/sites/plus.lean
- \+ *def* diagram_functor



## [2021-12-31 14:15:46](https://github.com/leanprover-community/mathlib/commit/7b38792)
feat(category_theory/limits/functor_category): Some additional isomorphisms involving (co)limits of functors. ([#11152](https://github.com/leanprover-community/mathlib/pull/11152))
#### Estimated changes
Modified src/category_theory/limits/colimit_limit.lean

Modified src/category_theory/limits/functor_category.lean
- \+ *lemma* limit_map_limit_obj_iso_limit_comp_evaluation_hom
- \+ *lemma* limit_obj_iso_limit_comp_evaluation_inv_limit_map
- \+ *lemma* colimit_obj_iso_colimit_comp_evaluation_inv_colimit_map
- \+ *lemma* colimit_map_colimit_obj_iso_colimit_comp_evaluation_hom
- \+ *def* limit_iso_flip_comp_lim
- \+ *def* limit_flip_iso_comp_lim
- \+/\- *def* limit_iso_swap_comp_lim
- \+ *def* colimit_iso_flip_comp_colim
- \+ *def* colimit_flip_iso_comp_colim
- \+/\- *def* colimit_iso_swap_comp_colim
- \+/\- *def* limit_iso_swap_comp_lim
- \+/\- *def* colimit_iso_swap_comp_colim

Modified src/category_theory/products/basic.lean
- \+ *def* flip_comp_evaluation



## [2021-12-31 14:15:45](https://github.com/leanprover-community/mathlib/commit/b142b69)
feat(data/list/count): add lemma `count_le_count_map` ([#11148](https://github.com/leanprover-community/mathlib/pull/11148))
Generalises `count_map_map`: for any `f : α → β` (not necessarily injective), `count x l ≤ count (f x) (map f l)`
#### Estimated changes
Modified src/data/list/count.lean
- \+ *lemma* count_map_of_injective
- \+ *lemma* count_le_count_map
- \- *lemma* count_map_map



## [2021-12-31 14:15:44](https://github.com/leanprover-community/mathlib/commit/dc57b54)
feat(ring_theory/localization): Transferring `is_localization` along equivs. ([#11146](https://github.com/leanprover-community/mathlib/pull/11146))
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *lemma* is_localization_of_alg_equiv
- \+ *lemma* is_localization_iff_of_alg_equiv
- \+ *lemma* is_localization_iff_of_ring_equiv
- \+ *lemma* is_localization_of_base_ring_equiv
- \+ *lemma* is_localization_iff_of_base_ring_equiv
- \+ *lemma* is_fraction_ring_iff_of_base_ring_equiv
- \- *lemma* iso_comp



## [2021-12-31 14:15:43](https://github.com/leanprover-community/mathlib/commit/bc5e008)
feat(data/dfinsupp/order): Pointwise order on finitely supported dependent functions ([#11138](https://github.com/leanprover-community/mathlib/pull/11138))
This defines the pointwise order on `Π₀ i, α i`, in very much the same way as in `data.finsupp.order`. It also moves `data.dfinsupp` to `data.dfinsupp.basic`.
#### Estimated changes
Modified src/algebra/direct_sum/basic.lean

Renamed src/data/dfinsupp.lean to src/data/dfinsupp/basic.lean

Created src/data/dfinsupp/order.lean
- \+ *lemma* not_mem_support_iff
- \+ *lemma* le_def
- \+ *lemma* order_embedding_to_fun_apply
- \+ *lemma* coe_fn_mono
- \+ *lemma* inf_apply
- \+ *lemma* sup_apply
- \+ *lemma* add_eq_zero_iff
- \+ *lemma* le_iff'
- \+ *lemma* le_iff
- \+ *lemma* single_le_iff
- \+ *lemma* tsub_apply
- \+ *lemma* coe_tsub
- \+ *lemma* single_tsub
- \+ *lemma* support_tsub
- \+ *lemma* subset_support_tsub
- \+ *lemma* support_inf
- \+ *lemma* support_sup
- \+ *lemma* disjoint_iff
- \+ *def* order_embedding_to_fun

Modified src/data/finsupp/to_dfinsupp.lean

Modified src/linear_algebra/basic.lean



## [2021-12-31 14:15:42](https://github.com/leanprover-community/mathlib/commit/2e8ebdc)
feat(algebra/homology): Construction of null homotopic chain complex … ([#11125](https://github.com/leanprover-community/mathlib/pull/11125))
…morphisms and one lemma on addivity of homotopies
#### Estimated changes
Modified src/algebra/homology/homotopy.lean
- \+ *lemma* null_homotopic_map_f
- \+ *lemma* null_homotopic_map'_f
- \+ *lemma* null_homotopic_map_f_of_not_rel_left
- \+ *lemma* null_homotopic_map'_f_of_not_rel_left
- \+ *lemma* null_homotopic_map_f_of_not_rel_right
- \+ *lemma* null_homotopic_map'_f_of_not_rel_right
- \+ *lemma* null_homotopic_map_f_eq_zero
- \+ *lemma* null_homotopic_map'_f_eq_zero
- \+ *def* add
- \+ *def* null_homotopic_map
- \+ *def* null_homotopic_map'
- \+ *def* null_homotopy
- \+ *def* null_homotopy'



## [2021-12-31 14:15:41](https://github.com/leanprover-community/mathlib/commit/ff7e837)
feat(combinatorics/configuration): Variant of `exists_injective_of_card_le` ([#11116](https://github.com/leanprover-community/mathlib/pull/11116))
Proves a variant of `exists_injective_of_card_le` that will be useful in an upcoming proof.
#### Estimated changes
Modified src/combinatorics/configuration.lean
- \+ *lemma* has_lines.exists_bijective_of_card_eq



## [2021-12-31 14:15:41](https://github.com/leanprover-community/mathlib/commit/1fd70b1)
refactor(algebra/big_operators/basic): Reorder lemmas ([#11113](https://github.com/leanprover-community/mathlib/pull/11113))
This PR does the following things:
- Move `prod_bij` and `prod_bij'` earlier in the file, so that they can be put to use.
- Move `prod_product` and `prod_product'` past `prod_sigma` and `prod_sigma'` down to `prod_product_right` and `prod_product_right'`.
- Use `prod_bij` and `prod_sigma` to give an easier proof of `prod_product`.
- The new proof introduces `prod_finset_product` and the remaining three analogs of the four `prod_product` lemmas.
`prod_finset_product` is a lemma that I found helpful in my own work.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* prod_bij
- \+/\- *lemma* prod_bij'
- \+ *lemma* prod_finset_product
- \+ *lemma* prod_finset_product'
- \+ *lemma* prod_finset_product_right
- \+ *lemma* prod_finset_product_right'
- \+/\- *lemma* prod_product
- \+/\- *lemma* prod_product'
- \+/\- *lemma* prod_product
- \+/\- *lemma* prod_product'
- \+/\- *lemma* prod_bij
- \+/\- *lemma* prod_bij'



## [2021-12-31 14:15:40](https://github.com/leanprover-community/mathlib/commit/99e3ffb)
feat(data/fin/tuple): new directory and file on sorting ([#11096](https://github.com/leanprover-community/mathlib/pull/11096))
Code written by @kmill at https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Permutation.20to.20make.20a.20function.20monotone
Co-authored by: Kyle Miller <kmill31415@gmail.com>
#### Estimated changes
Renamed src/data/fin/tuple.lean to src/data/fin/tuple/basic.lean

Created src/data/fin/tuple/default.lean

Created src/data/fin/tuple/sort.lean
- \+ *lemma* graph.card
- \+ *lemma* proj_equiv₁'
- \+ *lemma* self_comp_sort
- \+ *lemma* monotone_proj
- \+ *lemma* monotone_sort
- \+ *def* graph
- \+ *def* graph.proj
- \+ *def* graph_equiv₁
- \+ *def* graph_equiv₂
- \+ *def* sort



## [2021-12-31 14:15:39](https://github.com/leanprover-community/mathlib/commit/06a0197)
feat(category_theory/bicategory/basic): define bicategories ([#11079](https://github.com/leanprover-community/mathlib/pull/11079))
This PR defines bicategories and gives basic lemmas.
#### Estimated changes
Created src/category_theory/bicategory/basic.lean
- \+ *lemma* hom_inv_whisker_left
- \+ *lemma* hom_inv_whisker_right
- \+ *lemma* inv_hom_whisker_left
- \+ *lemma* inv_hom_whisker_right
- \+ *lemma* inv_whisker_left
- \+ *lemma* inv_whisker_right
- \+ *lemma* left_unitor_inv_naturality
- \+ *lemma* right_unitor_inv_naturality
- \+ *lemma* right_unitor_conjugation
- \+ *lemma* left_unitor_conjugation
- \+ *lemma* whisker_left_iff
- \+ *lemma* whisker_right_iff
- \+ *lemma* left_unitor_comp'
- \+ *lemma* left_unitor_comp
- \+ *lemma* left_unitor_comp_inv'
- \+ *lemma* left_unitor_comp_inv
- \+ *lemma* right_unitor_comp
- \+ *lemma* right_unitor_comp_inv
- \+ *lemma* whisker_left_right_unitor_inv
- \+ *lemma* whisker_left_right_unitor
- \+ *lemma* left_unitor_inv_whisker_right
- \+ *lemma* left_unitor_whisker_right
- \+ *lemma* associator_inv_naturality_left
- \+ *lemma* associator_conjugation_left
- \+ *lemma* associator_inv_conjugation_left
- \+ *lemma* associator_inv_naturality_middle
- \+ *lemma* associator_conjugation_middle
- \+ *lemma* associator_inv_conjugation_middle
- \+ *lemma* associator_inv_naturality_right
- \+ *lemma* associator_conjugation_right
- \+ *lemma* associator_inv_conjugation_right
- \+ *lemma* pentagon_inv
- \+ *lemma* pentagon_inv_inv_hom_hom_inv
- \+ *lemma* pentagon_inv_hom_hom_hom_inv
- \+ *lemma* pentagon_hom_inv_inv_inv_inv
- \+ *lemma* pentagon_hom_hom_inv_hom_hom
- \+ *lemma* pentagon_hom_inv_inv_inv_hom
- \+ *lemma* pentagon_hom_hom_inv_inv_hom
- \+ *lemma* pentagon_inv_hom_hom_hom_hom
- \+ *lemma* pentagon_inv_inv_hom_inv_inv
- \+ *lemma* triangle_assoc_comp_left
- \+ *lemma* triangle_assoc_comp_right
- \+ *lemma* triangle_assoc_comp_right_inv
- \+ *lemma* triangle_assoc_comp_left_inv
- \+ *lemma* unitors_equal
- \+ *lemma* unitors_inv_equal
- \+ *def* whisker_left_iso
- \+ *def* whisker_right_iso



## [2021-12-31 14:15:37](https://github.com/leanprover-community/mathlib/commit/a5573f3)
feat(data/{fin,multi}set/powerset): add some lemmas about powerset_len ([#10866](https://github.com/leanprover-community/mathlib/pull/10866))
For both multisets and finsets
From flt-regular
#### Estimated changes
Modified src/data/finset/powerset.lean
- \+ *lemma* powerset_len_card_add
- \+ *theorem* map_val_val_powerset_len

Modified src/data/multiset/powerset.lean
- \+ *lemma* powerset_len_card_add
- \+/\- *theorem* powerset_len_zero_right
- \+ *theorem* powerset_len_empty
- \+ *theorem* powerset_len_map
- \+/\- *theorem* powerset_len_zero_right



## [2021-12-31 12:26:01](https://github.com/leanprover-community/mathlib/commit/78a9900)
refactor(algebra/group/hom_instances): relax semiring to non_unital_non_assoc_semiring in add_monoid_hom.mul ([#11165](https://github.com/leanprover-community/mathlib/pull/11165))
Previously `algebra.group.hom_instances` ended with some results showing that left and right multiplication operators are additive monoid homomorphisms between (unital, associative) semirings. The assumptions of a unit and associativity are not required for these results to work, so we relax the condition to `non_unital_non_assoc_semiring`.
Required for [#11073](https://github.com/leanprover-community/mathlib/pull/11073) .
#### Estimated changes
Modified src/algebra/group/hom_instances.lean



## [2021-12-31 07:44:08](https://github.com/leanprover-community/mathlib/commit/dc1525f)
docs(data/sum/basic): Expand module docstring and cleanup ([#11158](https://github.com/leanprover-community/mathlib/pull/11158))
This moves `data.sum` to `data.sum.basic`, provides a proper docstring for it, cleans it up.
There are no new declarations, just some file rearrangement, variable grouping, unindentation, and a `protected` attribute for `sum.lex.inl`/`sum.lex.inr` to avoid them clashing with `sum.inl`/`sum.inr`.
#### Estimated changes
Modified src/control/bifunctor.lean

Modified src/data/equiv/basic.lean

Renamed src/data/sum.lean to src/data/sum/basic.lean
- \+ *lemma* «forall»
- \+ *lemma* «exists»
- \+/\- *lemma* inl_injective
- \+/\- *lemma* inr_injective
- \+/\- *lemma* update_elim_inl
- \+/\- *lemma* update_elim_inr
- \+/\- *lemma* update_inl_comp_inl
- \+/\- *lemma* update_inl_apply_inl
- \+/\- *lemma* update_inl_comp_inr
- \+/\- *lemma* update_inl_apply_inr
- \+/\- *lemma* update_inr_comp_inl
- \+/\- *lemma* update_inr_apply_inl
- \+/\- *lemma* update_inr_comp_inr
- \+/\- *lemma* update_inr_apply_inr
- \+/\- *lemma* swap_swap
- \+/\- *lemma* swap_swap_eq
- \+/\- *lemma* swap_left_inverse
- \+/\- *lemma* swap_right_inverse
- \+ *lemma* lex_inl_inl
- \+ *lemma* lex_inr_inr
- \+ *lemma* lex_inr_inl
- \+ *lemma* lex.mono
- \+ *lemma* lex.mono_left
- \+ *lemma* lex.mono_right
- \+ *lemma* lex_acc_inl
- \+ *lemma* lex_acc_inr
- \+ *lemma* lex_wf
- \+/\- *lemma* injective.sum_elim
- \+/\- *lemma* inl_injective
- \+/\- *lemma* inr_injective
- \+/\- *lemma* update_elim_inl
- \+/\- *lemma* update_elim_inr
- \+/\- *lemma* update_inl_comp_inl
- \+/\- *lemma* update_inl_apply_inl
- \+/\- *lemma* update_inl_comp_inr
- \+/\- *lemma* update_inl_apply_inr
- \+/\- *lemma* update_inr_comp_inl
- \+/\- *lemma* update_inr_apply_inl
- \+/\- *lemma* update_inr_comp_inr
- \+/\- *lemma* update_inr_apply_inr
- \+/\- *lemma* swap_swap
- \+/\- *lemma* swap_swap_eq
- \+/\- *lemma* swap_left_inverse
- \+/\- *lemma* swap_right_inverse
- \+/\- *lemma* injective.sum_elim
- \- *theorem* sum.forall
- \- *theorem* sum.exists
- \+ *def* get_left
- \+ *def* get_right
- \+ *def* is_left
- \+ *def* is_right
- \+/\- *def* swap
- \- *def* sum.get_left
- \- *def* sum.get_right
- \- *def* sum.is_left
- \- *def* sum.is_right
- \+/\- *def* swap

Modified src/order/rel_classes.lean

Modified src/tactic/fresh_names.lean

Modified test/simps.lean



## [2021-12-30 21:39:31](https://github.com/leanprover-community/mathlib/commit/e1a8b88)
feat(tactic/itauto): add support for [decidable p] assumptions ([#10744](https://github.com/leanprover-community/mathlib/pull/10744))
This allows proving theorems like the following, which use excluded middle selectively through `decidable` assumptions:
```
example (p q r : Prop) [decidable p] : (p → (q ∨ r)) → ((p → q) ∨ (p → r)) := by itauto
```
This also fixes a bug in the proof search order of the original itauto implementation causing nontermination in one of the new tests, which also makes the "big test" at the end run instantly.
Also adds a `!` option to enable decidability for all propositions using classical logic.
Because adding decidability instances can be expensive for proof search, they are disabled by default. You can specify specific decidable instances to add by `itauto [p, q]`, or use `itauto*` which adds all decidable atoms. (The `!` option is useless on its own, and should be combined with `*` or `[p]` options.)
#### Estimated changes
Modified src/tactic/itauto.lean
- \+ *def* map_proof
- \+ *def* is_ok
- \+ *def* when_ok

Modified test/itauto.lean



## [2021-12-30 20:16:32](https://github.com/leanprover-community/mathlib/commit/7f92832)
feat(category_theory/currying): `flip` is isomorphic to uncurrying, swapping, and currying. ([#11151](https://github.com/leanprover-community/mathlib/pull/11151))
#### Estimated changes
Modified src/category_theory/currying.lean
- \+ *def* flip_iso_curry_swap_uncurry



## [2021-12-30 18:41:23](https://github.com/leanprover-community/mathlib/commit/3dad7c8)
chore(algebra/ring/comp_typeclasses): fix doctrings ([#11150](https://github.com/leanprover-community/mathlib/pull/11150))
This fixes the docstrings of two typeclasses.
#### Estimated changes
Modified src/algebra/ring/comp_typeclasses.lean



## [2021-12-30 16:51:28](https://github.com/leanprover-community/mathlib/commit/682f1e6)
feat(analysis/normed_space/operator_norm): generalize linear_map.bound_of_ball_bound ([#11140](https://github.com/leanprover-community/mathlib/pull/11140))
This was proved over `is_R_or_C` but holds (in a slightly different form) over all nondiscrete normed fields.
#### Estimated changes
Modified src/analysis/normed_space/dual.lean

Modified src/analysis/normed_space/is_R_or_C.lean
- \+ *lemma* linear_map.bound_of_ball_bound'
- \- *lemma* linear_map.bound_of_ball_bound

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* linear_map.bound_of_ball_bound



## [2021-12-30 16:51:27](https://github.com/leanprover-community/mathlib/commit/c0b5ce1)
feat(data/nat/choose/basic): choose_eq_zero_iff ([#11120](https://github.com/leanprover-community/mathlib/pull/11120))
#### Estimated changes
Modified src/data/nat/choose/basic.lean
- \+ *lemma* choose_eq_zero_iff



## [2021-12-30 16:51:27](https://github.com/leanprover-community/mathlib/commit/993a470)
feat(analysis/special_functions/log): add log_div_self_antitone_on ([#10985](https://github.com/leanprover-community/mathlib/pull/10985))
Adds lemma `log_div_self_antitone_on`, which shows that `log x / x` is decreasing when `exp 1 \le x`. Needed for Bertrand's postulate ([#8002](https://github.com/leanprover-community/mathlib/pull/8002)).
#### Estimated changes
Modified src/analysis/special_functions/log.lean
- \+ *lemma* log_le_sub_one_of_pos
- \+ *lemma* log_div_self_antitone_on



## [2021-12-30 14:54:46](https://github.com/leanprover-community/mathlib/commit/ac97675)
feat(data/polynomial/degree/definition): nat_degree_monomial in ite form ([#11123](https://github.com/leanprover-community/mathlib/pull/11123))
Changed the proof usage elsewhere.
This helps deal with sums of over monomials.
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+/\- *lemma* nat_degree_monomial
- \+/\- *lemma* nat_degree_monomial

Modified src/data/polynomial/erase_lead.lean

Modified src/data/polynomial/mirror.lean



## [2021-12-30 14:54:45](https://github.com/leanprover-community/mathlib/commit/424773a)
feat(data/finset/fold): fold_const, fold_ite ([#11122](https://github.com/leanprover-community/mathlib/pull/11122))
#### Estimated changes
Modified src/data/finset/fold.lean
- \+ *lemma* fold_const
- \+ *lemma* fold_ite'
- \+ *lemma* fold_ite



## [2021-12-30 14:54:44](https://github.com/leanprover-community/mathlib/commit/c8a5762)
feat(order/galois_connection): gc magic ([#11114](https://github.com/leanprover-community/mathlib/pull/11114))
see [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.28l.E2.82.81.20S.29.2Emap.20.CF.83.20.E2.89.A4.20l.E2.82.82.20.28S.2Emap.20.E2.87.91.CF.83.29).
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean

Modified src/order/galois_connection.lean
- \+ *lemma* u_eq
- \+ *lemma* l_eq
- \+ *lemma* l_comm_of_u_comm
- \+ *lemma* u_comm_of_l_comm
- \+ *lemma* l_comm_iff_u_comm



## [2021-12-30 14:54:43](https://github.com/leanprover-community/mathlib/commit/f6d0f8d)
refactor(analysis/normed_space/operator_norm): split a proof ([#11112](https://github.com/leanprover-community/mathlib/pull/11112))
Split the proof of `continuous_linear_map.complete_space` into
reusable steps.
Motivated by [#9862](https://github.com/leanprover-community/mathlib/pull/9862)
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* tendsto_of_tendsto_pointwise_of_cauchy_seq
- \+ *theorem* lipschitz_apply
- \+ *def* of_mem_closure_image_coe_bounded
- \+ *def* of_tendsto_of_bounded_range



## [2021-12-30 14:54:42](https://github.com/leanprover-community/mathlib/commit/11de867)
feat(data/fin/interval): add lemmas ([#11102](https://github.com/leanprover-community/mathlib/pull/11102))
From flt-regular.
#### Estimated changes
Modified src/data/fin/basic.lean
- \+ *lemma* top_eq_last
- \+ *lemma* bot_eq_zero

Modified src/data/fin/interval.lean
- \+ *lemma* card_filter_lt
- \+ *lemma* card_filter_le
- \+ *lemma* card_filter_gt
- \+ *lemma* card_filter_ge
- \+ *lemma* card_filter_lt_lt
- \+ *lemma* card_filter_lt_le
- \+ *lemma* card_filter_le_lt
- \+ *lemma* card_filter_le_le

Modified src/data/finset/locally_finite.lean
- \+ *lemma* filter_lt_lt_eq_Ioo
- \+ *lemma* filter_lt_le_eq_Ioc
- \+ *lemma* filter_le_lt_eq_Ico
- \+ *lemma* filter_le_le_eq_Icc
- \+ *lemma* filter_lt_eq_Ioi
- \+ *lemma* filter_le_eq_Ici
- \+ *lemma* filter_gt_eq_Iio
- \+ *lemma* filter_ge_eq_Iic



## [2021-12-30 14:54:41](https://github.com/leanprover-community/mathlib/commit/3398efa)
feat(topology/homeomorph): homeo of continuous equivalence from compact to T2 ([#11072](https://github.com/leanprover-community/mathlib/pull/11072))
#### Estimated changes
Modified src/topology/homeomorph.lean
- \+ *lemma* continuous_symm_of_equiv_compact_to_t2
- \+ *lemma* homeo_of_equiv_compact_to_t2.t1_counterexample
- \- *lemma* compact_space
- \- *lemma* t2_space
- \+ *def* homeo_of_equiv_compact_to_t2



## [2021-12-30 14:54:40](https://github.com/leanprover-community/mathlib/commit/7b1c775)
chore(category_theory/adjunction/limits): generalize universe ([#11070](https://github.com/leanprover-community/mathlib/pull/11070))
#### Estimated changes
Modified src/category_theory/adjunction/limits.lean
- \+/\- *lemma* has_colimits_of_equivalence
- \+/\- *lemma* has_limits_of_equivalence
- \+/\- *lemma* has_colimits_of_equivalence
- \+/\- *lemma* has_limits_of_equivalence
- \+/\- *def* left_adjoint_preserves_colimits
- \+/\- *def* right_adjoint_preserves_limits
- \+/\- *def* cocones_iso_component_hom
- \+/\- *def* cocones_iso_component_inv
- \+/\- *def* cones_iso_component_hom
- \+/\- *def* cones_iso_component_inv
- \+/\- *def* cocones_iso
- \+/\- *def* cones_iso
- \+/\- *def* left_adjoint_preserves_colimits
- \+/\- *def* right_adjoint_preserves_limits
- \+/\- *def* cocones_iso_component_hom
- \+/\- *def* cocones_iso_component_inv
- \+/\- *def* cocones_iso
- \+/\- *def* cones_iso_component_hom
- \+/\- *def* cones_iso_component_inv
- \+/\- *def* cones_iso

Modified src/category_theory/closed/ideal.lean

Modified src/category_theory/limits/cone_category.lean

Modified src/category_theory/limits/has_limits.lean
- \+ *lemma* has_colimits.has_colimits_of_shape
- \- *lemma* has_colimits.has_limits_of_shape

Modified src/category_theory/limits/preserves/shapes/terminal.lean
- \+/\- *lemma* has_terminal_of_has_terminal_of_preserves_limit
- \+/\- *lemma* has_initial_of_has_initial_of_preserves_colimit
- \+/\- *lemma* has_terminal_of_has_terminal_of_preserves_limit
- \+/\- *lemma* has_initial_of_has_initial_of_preserves_colimit
- \+/\- *def* is_terminal.is_terminal_obj
- \+/\- *def* is_terminal.is_terminal_of_obj
- \+/\- *def* is_limit_of_has_terminal_of_preserves_limit
- \+/\- *def* is_initial.is_initial_obj
- \+/\- *def* is_initial.is_initial_of_obj
- \+/\- *def* is_colimit_of_has_initial_of_preserves_colimit
- \+/\- *def* is_terminal.is_terminal_obj
- \+/\- *def* is_terminal.is_terminal_of_obj
- \+/\- *def* is_limit_of_has_terminal_of_preserves_limit
- \+/\- *def* is_initial.is_initial_obj
- \+/\- *def* is_initial.is_initial_of_obj
- \+/\- *def* is_colimit_of_has_initial_of_preserves_colimit

Modified src/category_theory/limits/shapes/terminal.lean
- \+ *lemma* has_terminal_change_diagram
- \+ *lemma* has_terminal_change_universe
- \+ *lemma* has_initial_change_diagram
- \+ *lemma* has_initial_change_universe
- \+/\- *def* as_empty_cone
- \+/\- *def* as_empty_cocone
- \+ *def* is_limit_change_empty_cone
- \+ *def* is_limit_empty_cone_equiv
- \+ *def* is_colimit_change_empty_cocone
- \+ *def* is_colimit_empty_cocone_equiv
- \+/\- *def* as_empty_cone
- \+/\- *def* as_empty_cocone

Modified src/category_theory/monad/limits.lean
- \+/\- *lemma* has_limits_of_reflective
- \+/\- *lemma* has_colimits_of_reflective
- \+/\- *lemma* has_limits_of_reflective
- \+/\- *lemma* has_colimits_of_reflective

Modified src/category_theory/monoidal/of_chosen_finite_products.lean
- \+/\- *def* binary_fan.left_unitor
- \+/\- *def* binary_fan.right_unitor
- \+/\- *def* binary_fan.left_unitor
- \+/\- *def* binary_fan.right_unitor

Modified src/category_theory/pempty.lean
- \+/\- *lemma* empty_ext'
- \+/\- *lemma* empty_ext'
- \+ *def* empty_equivalence
- \+/\- *def* empty
- \+/\- *def* empty_ext
- \+/\- *def* unique_from_empty
- \+/\- *def* empty
- \+/\- *def* empty_ext
- \+/\- *def* unique_from_empty



## [2021-12-30 14:54:39](https://github.com/leanprover-community/mathlib/commit/d49ae12)
feat(topology/homotopy): Add homotopy product ([#10946](https://github.com/leanprover-community/mathlib/pull/10946))
Binary product and pi product of homotopies.
#### Estimated changes
Modified src/topology/continuous_function/basic.lean
- \+ *lemma* prod_eval
- \+ *lemma* pi_eval
- \+/\- *def* prod_mk
- \+/\- *def* prod_map
- \+ *def* pi
- \+/\- *def* prod_mk
- \+/\- *def* prod_map

Created src/topology/homotopy/product.lean
- \+ *def* homotopy.pi
- \+ *def* homotopy_rel.pi
- \+ *def* homotopy.prod
- \+ *def* homotopy_rel.prod



## [2021-12-30 14:14:55](https://github.com/leanprover-community/mathlib/commit/52841fb)
feat(ring_theory/polynomial/cyclotomic/basic): add cyclotomic_expand_eq_cyclotomic_mul ([#11005](https://github.com/leanprover-community/mathlib/pull/11005))
We prove that, if `¬p ∣ n`, then `expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R)`
- [x] depends on: [#10965](https://github.com/leanprover-community/mathlib/pull/10965)
#### Estimated changes
Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* cyclotomic.is_primitive
- \+ *lemma* cyclotomic_injective
- \+ *lemma* cyclotomic_eq_minpoly_rat
- \+ *lemma* cyclotomic.irreducible_rat
- \+ *lemma* cyclotomic.is_coprime_rat
- \+ *lemma* cyclotomic_expand_eq_cyclotomic_mul



## [2021-12-30 08:19:12](https://github.com/leanprover-community/mathlib/commit/655c2f0)
chore(topology/algebra/weak_dual_topology): review ([#11141](https://github.com/leanprover-community/mathlib/pull/11141))
* Fix universes in `pi.has_continuous_smul`.
* Add `function.injective.embedding_induced` and
  `weak_dual.coe_fn_embedding`.
* Golf some proofs.
* Review `weak_dual.module` etc instances to ensure, e.g.,
  `module ℝ (weak_dual ℂ E)`.
#### Estimated changes
Modified src/topology/algebra/mul_action.lean

Modified src/topology/algebra/weak_dual_topology.lean
- \+ *lemma* coe_fn_embedding

Modified src/topology/maps.lean
- \+ *lemma* function.injective.embedding_induced



## [2021-12-30 06:52:10](https://github.com/leanprover-community/mathlib/commit/04071ae)
feat(analysis/inner_product_space/adjoint): define the adjoint for linear maps between finite-dimensional spaces ([#11119](https://github.com/leanprover-community/mathlib/pull/11119))
This PR defines the adjoint of a linear map between finite-dimensional inner product spaces. We use the fact that such maps are always continuous and define it as the adjoint of the corresponding continuous linear map.
#### Estimated changes
Modified src/analysis/inner_product_space/adjoint.lean
- \+ *lemma* adjoint_to_continuous_linear_map
- \+ *lemma* adjoint_eq_to_clm_adjoint
- \+ *lemma* adjoint_inner_left
- \+ *lemma* adjoint_inner_right
- \+ *lemma* adjoint_adjoint
- \+ *lemma* adjoint_comp
- \+ *lemma* eq_adjoint_iff
- \+ *lemma* star_eq_adjoint
- \+ *lemma* is_adjoint_pair
- \+ *def* adjoint



## [2021-12-30 06:52:09](https://github.com/leanprover-community/mathlib/commit/9443a7b)
feat(data/nat/prime): min fac of a power ([#11115](https://github.com/leanprover-community/mathlib/pull/11115))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* prime.min_fac_eq
- \+ *lemma* pow_min_fac
- \+ *lemma* prime.pow_min_fac



## [2021-12-30 06:52:09](https://github.com/leanprover-community/mathlib/commit/0b6f9eb)
feat(logic/small): The image of a small set is small ([#11108](https://github.com/leanprover-community/mathlib/pull/11108))
A followup to [#11029](https://github.com/leanprover-community/mathlib/pull/11029). Only realized this could be easily proved once that PR was approved.
#### Estimated changes
Modified src/logic/small.lean



## [2021-12-30 06:52:08](https://github.com/leanprover-community/mathlib/commit/864a43b)
feat(combinatorics/simple_graph): lemmas describing edge set of subgraphs ([#11087](https://github.com/leanprover-community/mathlib/pull/11087))
#### Estimated changes
Modified src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* inf_adj
- \+ *lemma* sup_adj
- \+ *lemma* edge_set_top
- \+ *lemma* edge_set_bot
- \+ *lemma* edge_set_inf
- \+ *lemma* edge_set_sup
- \+ *lemma* spanning_coe_bot
- \+ *lemma* edge_set_mono
- \+ *lemma* _root_.disjoint.edge_set



## [2021-12-30 06:52:06](https://github.com/leanprover-community/mathlib/commit/8f873b7)
chore(data/nat/prime): move some results ([#11066](https://github.com/leanprover-community/mathlib/pull/11066))
I was expecting there'd be more that could be moved, but it doesn't seem like it.
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *theorem* _root_.irreducible_iff_nat_prime
- \+ *theorem* prime_iff
- \+ *theorem* irreducible_iff_prime

Modified src/ring_theory/int/basic.lean
- \- *theorem* nat.prime_iff
- \- *theorem* nat.irreducible_iff_prime
- \- *theorem* irreducible_iff_nat_prime



## [2021-12-30 06:04:19](https://github.com/leanprover-community/mathlib/commit/0c149c9)
feat(analysis/special_functions/log): sum of logs is log of product ([#11106](https://github.com/leanprover-community/mathlib/pull/11106))
#### Estimated changes
Modified src/analysis/special_functions/log.lean
- \+ *lemma* log_prod



## [2021-12-30 02:10:59](https://github.com/leanprover-community/mathlib/commit/23fdf99)
chore(measure_theory/function/lp_space): move `fact`s ([#11107](https://github.com/leanprover-community/mathlib/pull/11107))
Move from `measure_theory/function/lp_space` to `data/real/ennreal` the `fact`s
- `fact_one_le_one_ennreal`
- `fact_one_le_two_ennreal`
- `fact_one_le_top_ennreal`
so that they can be used not just in the measure theory development of `Lp` space but also in the new `lp` spaces.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* _root_.fact_one_le_one_ennreal
- \+ *lemma* _root_.fact_one_le_two_ennreal
- \+ *lemma* _root_.fact_one_le_top_ennreal

Modified src/measure_theory/function/lp_space.lean
- \- *lemma* fact_one_le_one_ennreal
- \- *lemma* fact_one_le_two_ennreal
- \- *lemma* fact_one_le_top_ennreal



## [2021-12-30 01:02:33](https://github.com/leanprover-community/mathlib/commit/4f3e99a)
feat(topology/algebra): range of `coe_fn : (M₁ →ₛₗ[σ] M₂) → (M₁ → M₂)` is closed ([#11105](https://github.com/leanprover-community/mathlib/pull/11105))
Motivated by [#9862](https://github.com/leanprover-community/mathlib/pull/9862)
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean

Modified src/topology/algebra/module.lean
- \+ *lemma* is_closed_set_of_map_smul
- \+ *lemma* linear_map.is_closed_range_coe
- \+ *def* linear_map_of_mem_closure_range_coe
- \+/\- *def* linear_map_of_tendsto
- \+/\- *def* linear_map_of_tendsto

Modified src/topology/algebra/monoid.lean
- \+ *lemma* is_closed_set_of_map_one
- \+ *lemma* is_closed_set_of_map_mul
- \+ *lemma* monoid_hom.is_closed_range_coe
- \+ *def* monoid_hom_of_mem_closure_range_coe
- \+/\- *def* monoid_hom_of_tendsto
- \+/\- *def* monoid_hom_of_tendsto



## [2021-12-30 00:20:50](https://github.com/leanprover-community/mathlib/commit/ea95523)
feat(analysis/normed_space/dual): add lemmas, golf ([#11132](https://github.com/leanprover-community/mathlib/pull/11132))
* add `polar_univ`, `is_closed_polar`, `polar_gc`, `polar_Union`,
  `polar_union`, `polar_antitone`, `polar_zero`, `polar_closure`;
* extract `polar_ball_subset_closed_ball_div` and
  `closed_ball_inv_subset_polar_closed_ball` out of the proofs of
  `polar_closed_ball` and `polar_bounded_of_nhds_zero`;
* rename `polar_bounded_of_nhds_zero` to
  `bounded_polar_of_mem_nhds_zero`, use `metric.bounded`;
* use `r⁻¹` instead of `1 / r` in `polar_closed_ball`. This is the
  simp normal form (though we might want to change this in the future).
#### Estimated changes
Modified src/analysis/normed_space/dual.lean
- \+ *lemma* polar_univ
- \+ *lemma* is_closed_polar
- \+ *lemma* polar_gc
- \+ *lemma* polar_Union
- \+ *lemma* polar_union
- \+ *lemma* polar_antitone
- \+/\- *lemma* polar_empty
- \+ *lemma* polar_zero
- \+ *lemma* polar_closure
- \+ *lemma* polar_ball_subset_closed_ball_div
- \+ *lemma* closed_ball_inv_subset_polar_closed_ball
- \+ *lemma* bounded_polar_of_mem_nhds_zero
- \+/\- *lemma* polar_empty
- \- *lemma* polar_bounded_of_nhds_zero



## [2021-12-29 21:58:43](https://github.com/leanprover-community/mathlib/commit/be17b92)
feat(topology/metric_space/lipschitz): image of a bdd set ([#11134](https://github.com/leanprover-community/mathlib/pull/11134))
Prove that `f '' s` is bounded provided that `f` is Lipschitz
continuous and `s` is bounded.
#### Estimated changes
Modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* bounded_image



## [2021-12-29 21:58:42](https://github.com/leanprover-community/mathlib/commit/5bfd924)
chore(analysis/normed_space/basic): add `normed_space.unbounded_univ` ([#11131](https://github.com/leanprover-community/mathlib/pull/11131))
Extract it from the proof of `normed_space.noncompact_space`.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean



## [2021-12-29 21:58:41](https://github.com/leanprover-community/mathlib/commit/5ac8715)
split(data/finsupp/multiset): Split off `data.finsupp.basic` ([#11110](https://github.com/leanprover-community/mathlib/pull/11110))
This moves `finsupp.to_multiset`, `multiset.to_finsupp` and `finsupp.order_iso_multiset` to a new file `data.finsupp.multiset`.
#### Estimated changes
Modified src/data/finsupp/antidiagonal.lean

Modified src/data/finsupp/basic.lean
- \- *lemma* to_multiset_zero
- \- *lemma* to_multiset_add
- \- *lemma* to_multiset_apply
- \- *lemma* to_multiset_symm_apply
- \- *lemma* to_multiset_single
- \- *lemma* to_multiset_sum
- \- *lemma* to_multiset_sum_single
- \- *lemma* card_to_multiset
- \- *lemma* to_multiset_map
- \- *lemma* prod_to_multiset
- \- *lemma* to_finset_to_multiset
- \- *lemma* count_to_multiset
- \- *lemma* mem_to_multiset
- \- *lemma* to_finsupp_support
- \- *lemma* to_finsupp_apply
- \- *lemma* to_finsupp_zero
- \- *lemma* to_finsupp_add
- \- *lemma* to_finsupp_singleton
- \- *lemma* to_finsupp_to_multiset
- \- *lemma* to_finsupp_eq_iff
- \- *lemma* finsupp.to_multiset_to_finsupp
- \- *def* to_multiset
- \- *def* to_finsupp

Created src/data/finsupp/multiset.lean
- \+ *lemma* to_multiset_zero
- \+ *lemma* to_multiset_add
- \+ *lemma* to_multiset_apply
- \+ *lemma* to_multiset_symm_apply
- \+ *lemma* to_multiset_single
- \+ *lemma* to_multiset_sum
- \+ *lemma* to_multiset_sum_single
- \+ *lemma* card_to_multiset
- \+ *lemma* to_multiset_map
- \+ *lemma* prod_to_multiset
- \+ *lemma* to_finset_to_multiset
- \+ *lemma* count_to_multiset
- \+ *lemma* mem_to_multiset
- \+ *lemma* to_finsupp_support
- \+ *lemma* to_finsupp_apply
- \+ *lemma* to_finsupp_zero
- \+ *lemma* to_finsupp_add
- \+ *lemma* to_finsupp_singleton
- \+ *lemma* to_finsupp_to_multiset
- \+ *lemma* to_finsupp_eq_iff
- \+ *lemma* finsupp.to_multiset_to_finsupp
- \+ *lemma* coe_order_iso_multiset
- \+ *lemma* coe_order_iso_multiset_symm
- \+ *lemma* to_multiset_strict_mono
- \+ *lemma* sum_id_lt_of_lt
- \+ *lemma* lt_wf
- \+ *lemma* multiset.to_finsupp_strict_mono
- \+ *def* to_multiset
- \+ *def* to_finsupp
- \+ *def* order_iso_multiset

Modified src/data/finsupp/order.lean
- \- *lemma* coe_order_iso_multiset
- \- *lemma* coe_order_iso_multiset_symm
- \- *lemma* to_multiset_strict_mono
- \- *lemma* sum_id_lt_of_lt
- \- *lemma* lt_wf
- \- *lemma* to_finsupp_strict_mono
- \- *def* order_iso_multiset

Modified src/ring_theory/unique_factorization_domain.lean



## [2021-12-29 21:58:40](https://github.com/leanprover-community/mathlib/commit/b8833e9)
chore(data/*): Eliminate `finish` ([#11099](https://github.com/leanprover-community/mathlib/pull/11099))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/data/complex/exponential.lean

Modified src/data/equiv/set.lean

Modified src/data/list/min_max.lean

Modified src/data/nat/totient.lean

Modified src/data/option/defs.lean
- \+ *lemma* mem_some_iff

Modified src/data/pequiv.lean

Modified src/data/setoid/partition.lean



## [2021-12-29 21:58:39](https://github.com/leanprover-community/mathlib/commit/2a929f2)
feat(algebra/ne_zero): typeclass for n ≠ 0 ([#11033](https://github.com/leanprover-community/mathlib/pull/11033))
#### Estimated changes
Modified src/algebra/invertible.lean
- \+/\- *lemma* nonzero_of_invertible
- \+/\- *lemma* nonzero_of_invertible

Created src/algebra/ne_zero.lean
- \+ *lemma* ne_zero.ne
- \+ *lemma* ne_zero.ne'
- \+ *lemma* ne_zero_iff
- \+ *lemma* not_ne_zero
- \+ *lemma* of_pos
- \+ *lemma* of_gt
- \+ *lemma* of_map
- \+ *lemma* of_injective'
- \+ *lemma* of_injective
- \+ *lemma* of_not_dvd
- \+ *lemma* of_no_zero_smul_divisors
- \+ *lemma* of_ne_zero_coe



## [2021-12-29 21:03:06](https://github.com/leanprover-community/mathlib/commit/dd65894)
chore(*): Eliminate some more instances of `finish` ([#11136](https://github.com/leanprover-community/mathlib/pull/11136))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
This (and the previous series of PRs) eliminates the last few instances of `finish` in the main body of mathlib, leaving only instances in the `scripts`, `test`, `tactic`, and `archive` folders.
#### Estimated changes
Modified src/category_theory/monad/equiv_mon.lean

Modified src/group_theory/perm/sign.lean

Modified src/set_theory/game/impartial.lean



## [2021-12-29 21:03:05](https://github.com/leanprover-community/mathlib/commit/d67a1dc)
chore(number_theory/quadratic_reciprocity): Eliminate `finish` ([#11133](https://github.com/leanprover-community/mathlib/pull/11133))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/number_theory/quadratic_reciprocity.lean



## [2021-12-29 21:03:04](https://github.com/leanprover-community/mathlib/commit/c03dbd1)
chore(algebra/continued_fractions/computation/translations): Eliminate `finish` ([#11130](https://github.com/leanprover-community/mathlib/pull/11130))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/algebra/continued_fractions/computation/translations.lean



## [2021-12-29 21:03:03](https://github.com/leanprover-community/mathlib/commit/90d12bb)
chore(computability/NFA): Eliminate `finish` ([#11103](https://github.com/leanprover-community/mathlib/pull/11103))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/computability/NFA.lean



## [2021-12-29 20:15:05](https://github.com/leanprover-community/mathlib/commit/6703cdd)
chore([normed/charted]_space): Eliminate `finish` ([#11126](https://github.com/leanprover-community/mathlib/pull/11126))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/analysis/normed_space/add_torsor_bases.lean

Modified src/analysis/normed_space/lattice_ordered_group.lean

Modified src/geometry/manifold/charted_space.lean



## [2021-12-29 18:18:57](https://github.com/leanprover-community/mathlib/commit/c25bd03)
feat(algebra/order/field): prove `a / a ≤ 1` ([#11118](https://github.com/leanprover-community/mathlib/pull/11118))
#### Estimated changes
Modified src/algebra/order/field.lean
- \+ *lemma* div_self_le_one

Modified src/data/real/nnreal.lean
- \+/\- *lemma* div_self_le
- \+/\- *lemma* div_self_le



## [2021-12-29 16:12:37](https://github.com/leanprover-community/mathlib/commit/395e275)
chore(topology/metric_space/basic): +1 version of Heine-Borel ([#11127](https://github.com/leanprover-community/mathlib/pull/11127))
* Mark `metric.is_compact_of_closed_bounded` as "Heine-Borel" theorem
  too.
* Add `metric.bounded.is_compact_closure`.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* bounded.is_compact_closure



## [2021-12-29 16:12:36](https://github.com/leanprover-community/mathlib/commit/cb37df3)
feat(data/list/pairwise): pairwise repeat ([#11117](https://github.com/leanprover-community/mathlib/pull/11117))
#### Estimated changes
Modified src/data/list/pairwise.lean
- \+ *lemma* pairwise_repeat



## [2021-12-29 14:53:37](https://github.com/leanprover-community/mathlib/commit/d8b4267)
chore(algebra/big_operators/finprod): Eliminate `finish` ([#10923](https://github.com/leanprover-community/mathlib/pull/10923))
Removing uses of finish, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean



## [2021-12-29 12:26:04](https://github.com/leanprover-community/mathlib/commit/e003d6e)
feat(data/polynomial): more API for roots ([#11081](https://github.com/leanprover-community/mathlib/pull/11081))
`leading_coeff_monic_mul`
`leading_coeff_X_sub_C`
`root_multiplicity_C`
`not_is_root_C`
`roots_smul_nonzero`
`leading_coeff_div_by_monic_X_sub_C`
`roots_eq_zero_iff`
also generalized various statements about `X - C a` to `X + C a` over semirings.
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+/\- *lemma* degree_X_add_C
- \+ *lemma* nat_degree_X_add_C
- \+ *lemma* next_coeff_X_add_C
- \+ *lemma* degree_X_pow_add_C
- \+ *lemma* X_pow_add_C_ne_zero
- \+ *lemma* nat_degree_X_pow_add_C
- \+ *lemma* leading_coeff_X_pow_add_C
- \+/\- *lemma* leading_coeff_X_add_C
- \+ *lemma* leading_coeff_X_pow_add_one
- \+/\- *lemma* next_coeff_X_sub_C
- \+ *lemma* leading_coeff_X_sub_C
- \+ *lemma* leading_coeff_C_mul_X_add_C
- \+/\- *lemma* degree_X_add_C
- \+/\- *lemma* next_coeff_X_sub_C
- \+/\- *lemma* leading_coeff_X_add_C
- \+ *theorem* X_add_C_ne_zero
- \+ *theorem* zero_nmem_multiset_map_X_add_C

Modified src/data/polynomial/div.lean
- \+ *lemma* root_multiplicity_C

Modified src/data/polynomial/eval.lean
- \+ *lemma* not_is_root_C

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* roots_smul_nonzero
- \+ *lemma* leading_coeff_div_by_monic_X_sub_C

Modified src/field_theory/is_alg_closed/basic.lean
- \+ *lemma* roots_eq_zero_iff



## [2021-12-29 02:26:11](https://github.com/leanprover-community/mathlib/commit/268d1a8)
chore(topology/metric_space/basic): golf, add dot notation ([#11111](https://github.com/leanprover-community/mathlib/pull/11111))
* add `cauchy_seq.bounded_range`;
* golf `metric.bounded_range_of_tendsto`.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* _root_.cauchy_seq.bounded_range



## [2021-12-28 20:56:25](https://github.com/leanprover-community/mathlib/commit/a82c481)
feat(data/polynomial/basic): `add_submonoid.closure` of monomials is `⊤` ([#11101](https://github.com/leanprover-community/mathlib/pull/11101))
Use it to golf `polynomial.add_hom_ext`.
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *lemma* add_submonoid_closure_set_of_eq_monomial

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* map_equiv_top



## [2021-12-28 20:56:24](https://github.com/leanprover-community/mathlib/commit/134ff7d)
feat(data/option/basic): add `eq_of_mem_of_mem` ([#11098](https://github.com/leanprover-community/mathlib/pull/11098))
If `a : α` belongs to both `o1 o2 : option α` then `o1 = o2`
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *theorem* eq_of_mem_of_mem



## [2021-12-28 20:56:23](https://github.com/leanprover-community/mathlib/commit/f11d3ca)
feat(analysis/special_functions/pow): `rpow` as an `order_iso` ([#10831](https://github.com/leanprover-community/mathlib/pull/10831))
Bundles `rpow` into an order isomorphism on `ennreal` when the exponent is a fixed positive real.
- [x] depends on: [#10701](https://github.com/leanprover-community/mathlib/pull/10701)
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* order_iso_rpow_symm_apply
- \+ *def* order_iso_rpow



## [2021-12-28 19:49:35](https://github.com/leanprover-community/mathlib/commit/8d41552)
feat(logic/small): The range of a function from a small type is small ([#11029](https://github.com/leanprover-community/mathlib/pull/11029))
That is, you don't actually need an equivalence to build `small α`, a mere function does the trick.
#### Estimated changes
Modified src/logic/small.lean
- \+/\- *theorem* small_of_injective
- \+ *theorem* small_of_surjective
- \+/\- *theorem* small_of_injective



## [2021-12-28 19:49:34](https://github.com/leanprover-community/mathlib/commit/8d24a1f)
refactor(category_theory/shift): make shifts more flexible ([#10573](https://github.com/leanprover-community/mathlib/pull/10573))
#### Estimated changes
Modified src/algebra/homology/differential_object.lean

Modified src/category_theory/differential_object.lean
- \+/\- *def* map_differential_object
- \+/\- *def* shift_functor
- \+ *def* shift_functor_add
- \+ *def* shift_ε
- \+/\- *def* map_differential_object
- \+/\- *def* shift_functor
- \- *def* shift_inverse_obj
- \- *def* shift_inverse
- \- *def* shift_unit
- \- *def* shift_unit_inv
- \- *def* shift_unit_iso
- \- *def* shift_counit
- \- *def* shift_counit_inv
- \- *def* shift_counit_iso

Modified src/category_theory/graded_object.lean
- \+/\- *lemma* shift_functor_obj_apply
- \+/\- *lemma* shift_functor_obj_apply

Modified src/category_theory/shift.lean
- \+ *lemma* has_shift.shift_obj_obj
- \+ *lemma* shift_add_hom_comp_eq_to_hom₁
- \+ *lemma* shift_add_hom_comp_eq_to_hom₂
- \+ *lemma* shift_add_hom_comp_eq_to_hom₁₂
- \+ *lemma* eq_to_hom_comp_shift_add_inv₁
- \+ *lemma* eq_to_hom_comp_shift_add_inv₂
- \+ *lemma* eq_to_hom_comp_shift_add_inv₁₂
- \+ *lemma* shift_shift'
- \+ *lemma* shift_zero'
- \+ *lemma* opaque_eq_to_iso_symm
- \+ *lemma* opaque_eq_to_iso_inv
- \+ *lemma* map_opaque_eq_to_iso_comp_app
- \+ *lemma* shift_shift_neg'
- \+ *lemma* shift_neg_shift'
- \+ *lemma* shift_equiv_triangle
- \+ *lemma* shift_shift_neg_hom_shift
- \+ *lemma* shift_shift_neg_inv_shift
- \+ *lemma* shift_shift_neg_shift_eq
- \+/\- *lemma* shift_zero_eq_zero
- \+ *lemma* shift_comm_symm
- \+ *lemma* shift_comm'
- \+ *lemma* shift_comm_hom_comp
- \+/\- *lemma* shift_zero_eq_zero
- \+ *def* add_neg_equiv
- \+ *def* has_shift_mk
- \+ *def* shift_monoidal_functor
- \+ *def* opaque_eq_to_iso
- \+ *def* shift_equiv
- \+ *def* shift_comm
- \- *def* shift

Modified src/category_theory/triangulated/basic.lean

Modified src/category_theory/triangulated/pretriangulated.lean

Modified src/category_theory/triangulated/rotate.lean
- \+ *def* to_inv_rotate_rotate
- \+ *def* from_inv_rotate_rotate
- \+ *def* from_rotate_inv_rotate
- \+/\- *def* inv_rot_comp_rot_hom
- \+ *def* to_rotate_inv_rotate
- \+/\- *def* inv_rot_comp_rot_hom



## [2021-12-28 18:16:58](https://github.com/leanprover-community/mathlib/commit/0b80d0c)
chore(ring_theory/*): Eliminate `finish` ([#11100](https://github.com/leanprover-community/mathlib/pull/11100))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean

Modified src/ring_theory/principal_ideal_domain.lean



## [2021-12-28 15:39:49](https://github.com/leanprover-community/mathlib/commit/143fec6)
chore(linear_algebra/*): Eliminate `finish` ([#11074](https://github.com/leanprover-community/mathlib/pull/11074))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/linear_algebra/basic.lean

Modified src/linear_algebra/direct_sum/finsupp.lean



## [2021-12-28 13:53:36](https://github.com/leanprover-community/mathlib/commit/d053d57)
feat(topology): missing lemmas for Kyle ([#11076](https://github.com/leanprover-community/mathlib/pull/11076))
Discussion [on Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Continuous.20bijective.20from.20compact.20to.20T1.20implies.20homeomorphis) revealed gaps in library. This PR fills those gaps and related ones discovered on the way. It will simplify [#11072](https://github.com/leanprover-community/mathlib/pull/11072). Note that it unprotects `topological_space.nhds_adjoint` and puts it into the root namespace. I guess this was protected because it was seen only as a technical tools to prove properties of `nhds`.
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* finite.sInter

Modified src/order/filter/ultrafilter.lean
- \+ *lemma* eq_principal_of_finite_mem

Modified src/topology/basic.lean
- \+ *lemma* is_open_singleton_iff_nhds_eq_pure

Modified src/topology/constructions.lean
- \+ *lemma* nhds_cofinite
- \+ *lemma* mem_nhds_cofinite
- \+ *def* cofinite_topology

Modified src/topology/order.lean
- \+ *lemma* le_iff_nhds
- \+ *lemma* nhds_adjoint_nhds
- \+ *lemma* nhds_adjoint_nhds_of_ne
- \+ *lemma* is_open_singleton_nhds_adjoint
- \+ *lemma* le_nhds_adjoint_iff'
- \+ *lemma* le_nhds_adjoint_iff
- \+ *def* nhds_adjoint

Modified src/topology/separation.lean
- \+/\- *lemma* finite.is_closed
- \+ *lemma* t1_space_antimono
- \+ *lemma* t1_space_iff_le_cofinite
- \+/\- *lemma* finite.is_closed



## [2021-12-28 12:15:06](https://github.com/leanprover-community/mathlib/commit/10771d7)
doc(combinatorics/configuration): Make comments into docstrings ([#11097](https://github.com/leanprover-community/mathlib/pull/11097))
These comments should have been docstrings.
#### Estimated changes
Modified src/combinatorics/configuration.lean



## [2021-12-28 12:15:05](https://github.com/leanprover-community/mathlib/commit/d3aa0a4)
feat(data/polynomial/coeff): generalize to coeff_X_add_C_pow ([#11093](https://github.com/leanprover-community/mathlib/pull/11093))
That golfs the proof for `coeff_X_add_one_pow`.
#### Estimated changes
Modified src/data/polynomial/coeff.lean
- \+ *lemma* coeff_X_add_C_pow
- \+/\- *lemma* coeff_X_add_one_pow
- \+/\- *lemma* coeff_X_add_one_pow



## [2021-12-28 12:15:03](https://github.com/leanprover-community/mathlib/commit/afff1bb)
chore(data/polynomial/eval): golf a proof, add versions ([#11092](https://github.com/leanprover-community/mathlib/pull/11092))
* golf the proof of `polynomial.eval_prod`;
* add versions `polynomial.eval_multiset_prod` and
  `polynomial.eval_list_prod`.
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* eval_list_prod
- \+ *lemma* eval_multiset_prod



## [2021-12-28 11:35:38](https://github.com/leanprover-community/mathlib/commit/c04a42f)
feat(measure_theory/integral/{interval,circle}_integral): add strict inequalities ([#11061](https://github.com/leanprover-community/mathlib/pull/11061))
#### Estimated changes
Modified src/measure_theory/integral/circle_integral.lean
- \+ *lemma* norm_two_pi_I_inv_smul_integral_le_of_norm_le_const
- \+ *lemma* norm_integral_lt_of_norm_le_const_of_lt

Modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* integral_pos_iff_support_of_nonneg_ae
- \+ *lemma* integral_lt_integral_of_ae_le_of_measure_set_of_lt_ne_zero
- \+ *lemma* integral_lt_integral_of_continuous_on_of_le_of_exists_lt
- \+/\- *lemma* integral_nonneg_of_ae_restrict
- \+/\- *lemma* integral_nonneg_of_ae
- \+/\- *lemma* integral_nonneg_of_forall
- \+/\- *lemma* abs_integral_le_integral_abs
- \+/\- *lemma* integral_pos_iff_support_of_nonneg_ae
- \+/\- *lemma* integral_nonneg_of_ae_restrict
- \+/\- *lemma* integral_nonneg_of_ae
- \+/\- *lemma* integral_nonneg_of_forall
- \+/\- *lemma* abs_integral_le_integral_abs



## [2021-12-28 09:40:04](https://github.com/leanprover-community/mathlib/commit/f452b38)
feat(data/pi): bit[01]_apply simp lemmas ([#11086](https://github.com/leanprover-community/mathlib/pull/11086))
#### Estimated changes
Modified src/data/pi.lean
- \+ *lemma* bit0_apply
- \+ *lemma* bit1_apply



## [2021-12-28 07:03:21](https://github.com/leanprover-community/mathlib/commit/94bb466)
feat(tactic/fin_cases): document `fin_cases with` and add `fin_cases using` ([#11085](https://github.com/leanprover-community/mathlib/pull/11085))
Closes [#11016](https://github.com/leanprover-community/mathlib/pull/11016)
#### Estimated changes
Modified src/linear_algebra/matrix/block.lean

Modified src/tactic/fin_cases.lean

Modified src/tactic/interval_cases.lean

Modified test/fin_cases.lean



## [2021-12-28 06:21:09](https://github.com/leanprover-community/mathlib/commit/44f22aa)
feat(ring_theory/power_series/basic): add api for coeffs of shifts ([#11082](https://github.com/leanprover-community/mathlib/pull/11082))
Based on the corresponding API for polynomials
#### Estimated changes
Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* coeff_C_mul_X
- \+ *lemma* coeff_mul_X_pow'
- \+ *lemma* coeff_X_pow_mul'
- \+ *theorem* coeff_mul_X_pow
- \+ *theorem* coeff_X_pow_mul



## [2021-12-28 03:25:46](https://github.com/leanprover-community/mathlib/commit/f0ca433)
feat(data/set/finite): finite_or_infinite ([#11084](https://github.com/leanprover-community/mathlib/pull/11084))
#### Estimated changes
Modified src/data/set/finite.lean
- \+ *lemma* finite_or_infinite



## [2021-12-28 03:25:45](https://github.com/leanprover-community/mathlib/commit/612a476)
feat(ring_theory/polynomial/cyclotomic/basic): add cyclotomic_expand_eq_cyclotomic ([#10974](https://github.com/leanprover-community/mathlib/pull/10974))
We prove that, if `p ∣ n`, then `expand R p (cyclotomic n R) = cyclotomic (p * n) R`.
- [x] depends on: [#10965](https://github.com/leanprover-community/mathlib/pull/10965)
- [x] depends on: [#10971](https://github.com/leanprover-community/mathlib/pull/10971)
#### Estimated changes
Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* cyclotomic_expand_eq_cyclotomic

Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* pow_of_dvd



## [2021-12-28 02:46:14](https://github.com/leanprover-community/mathlib/commit/10ea860)
feat(ring_theory/polynomial/cyclotomic/basic): cyclotomic_prime_mul_X_sub_one ([#11063](https://github.com/leanprover-community/mathlib/pull/11063))
From flt-regular.
#### Estimated changes
Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* cyclotomic_prime_mul_X_sub_one



## [2021-12-27 18:57:58](https://github.com/leanprover-community/mathlib/commit/294e78e)
feat(algebra/group_with_zero/power): With zero lemmas ([#11051](https://github.com/leanprover-community/mathlib/pull/11051))
This proves the `group_with_zero` variant of some lemmas and moves lemmas from `algebra.group_power.basic` to `algebra.group_with_zero.power`.
#### Estimated changes
Modified src/algebra/group_power/basic.lean

Modified src/algebra/group_with_zero/power.lean
- \+ *lemma* pow_sub_of_lt
- \+ *lemma* inv_pow_sub₀
- \+ *lemma* inv_pow_sub_of_lt
- \+ *lemma* zero_zpow_eq
- \+ *lemma* mul_zpow_neg_one₀
- \+ *lemma* zpow_neg_one₀
- \+/\- *lemma* mul_zpow₀
- \- *lemma* fzero_pow_eq
- \+/\- *lemma* mul_zpow₀
- \+ *def* zpow_group_hom₀



## [2021-12-27 18:57:57](https://github.com/leanprover-community/mathlib/commit/1332fe1)
fix(tactic/rcases): more with_desc fail ([#11004](https://github.com/leanprover-community/mathlib/pull/11004))
This causes hovers for definitions using `rcases_patt_parse` to print
weird stuff for the parser description.
#### Estimated changes
Modified src/tactic/rcases.lean



## [2021-12-27 16:46:26](https://github.com/leanprover-community/mathlib/commit/0e8cca3)
feat(algebra/big_operators/order): `prod_eq_prod_iff_of_le` ([#11068](https://github.com/leanprover-community/mathlib/pull/11068))
If `f i ≤ g i` for all `i ∈ s`, then `∏ i in s, f i = ∏ i in s, g i` if and only if `f i = g i` for all `i ∈ s`.
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+ *lemma* prod_eq_prod_iff_of_le



## [2021-12-27 16:46:25](https://github.com/leanprover-community/mathlib/commit/6ed17fc)
refactor(combinatorics/configuration): Generalize results ([#11065](https://github.com/leanprover-community/mathlib/pull/11065))
This PR slightly generalizes the results in `configuration.lean` by weakening the definitions of `has_points` and `has_lines`. The new definitions are also more natural, in my opinion.
#### Estimated changes
Modified src/combinatorics/configuration.lean



## [2021-12-27 16:46:24](https://github.com/leanprover-community/mathlib/commit/e1133cc)
chore(order/*): Eliminate `finish` ([#11064](https://github.com/leanprover-community/mathlib/pull/11064))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
Credit to Ruben Van de Velde who suggested the solution for `eventually_lift'_powerset_eventually`
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean

Modified src/order/filter/lift.lean



## [2021-12-27 16:46:23](https://github.com/leanprover-community/mathlib/commit/46566c5)
split(data/list/infix): Split off `data.list.basic` ([#11062](https://github.com/leanprover-community/mathlib/pull/11062))
This moves `list.prefix`, `list.subfix`, `list.infix`, `list.inits`, `list.tails` and `insert` lemmas from `data.list.basic` to a new file `data.list.infix`.
#### Estimated changes
Modified src/algebra/free_monoid.lean

Modified src/data/list/basic.lean
- \- *lemma* prefix_take_le_iff
- \- *lemma* cons_prefix_iff
- \- *lemma* map_prefix
- \- *lemma* is_prefix.filter_map
- \- *lemma* is_prefix.reduce_option
- \- *lemma* is_prefix.filter
- \- *lemma* is_suffix.filter
- \- *lemma* is_infix.filter
- \- *lemma* inits_cons
- \- *lemma* tails_cons
- \- *lemma* inits_append
- \- *lemma* tails_append
- \- *lemma* inits_eq_tails
- \- *lemma* tails_eq_inits
- \- *lemma* inits_reverse
- \- *lemma* tails_reverse
- \- *lemma* map_reverse_inits
- \- *lemma* map_reverse_tails
- \- *lemma* length_tails
- \- *lemma* length_inits
- \- *lemma* nth_le_tails
- \- *lemma* nth_le_inits
- \- *theorem* prefix_append
- \- *theorem* suffix_append
- \- *theorem* infix_append
- \- *theorem* infix_append'
- \- *theorem* nil_prefix
- \- *theorem* nil_suffix
- \- *theorem* prefix_refl
- \- *theorem* suffix_refl
- \- *theorem* suffix_cons
- \- *theorem* prefix_concat
- \- *theorem* is_prefix.is_infix
- \- *theorem* is_suffix.is_infix
- \- *theorem* infix_refl
- \- *theorem* nil_infix
- \- *theorem* infix_cons
- \- *theorem* is_prefix.trans
- \- *theorem* is_suffix.trans
- \- *theorem* is_infix.trans
- \- *theorem* reverse_suffix
- \- *theorem* reverse_prefix
- \- *theorem* infix.length_le
- \- *theorem* eq_nil_of_infix_nil
- \- *theorem* eq_nil_iff_infix_nil
- \- *theorem* eq_nil_of_prefix_nil
- \- *theorem* eq_nil_iff_prefix_nil
- \- *theorem* eq_nil_of_suffix_nil
- \- *theorem* eq_nil_iff_suffix_nil
- \- *theorem* infix_iff_prefix_suffix
- \- *theorem* eq_of_infix_of_length_eq
- \- *theorem* eq_of_prefix_of_length_eq
- \- *theorem* eq_of_suffix_of_length_eq
- \- *theorem* prefix_of_prefix_length_le
- \- *theorem* prefix_or_prefix_of_prefix
- \- *theorem* suffix_of_suffix_length_le
- \- *theorem* suffix_or_suffix_of_suffix
- \- *theorem* suffix_cons_iff
- \- *theorem* infix_of_mem_join
- \- *theorem* prefix_append_right_inj
- \- *theorem* prefix_cons_inj
- \- *theorem* take_prefix
- \- *theorem* take_sublist
- \- *theorem* take_subset
- \- *theorem* mem_of_mem_take
- \- *theorem* drop_suffix
- \- *theorem* drop_sublist
- \- *theorem* drop_subset
- \- *theorem* mem_of_mem_drop
- \- *theorem* init_prefix
- \- *theorem* init_sublist
- \- *theorem* init_subset
- \- *theorem* mem_of_mem_init
- \- *theorem* tail_suffix
- \- *theorem* tail_sublist
- \- *theorem* tail_subset
- \- *theorem* mem_of_mem_tail
- \- *theorem* prefix_iff_eq_append
- \- *theorem* suffix_iff_eq_append
- \- *theorem* prefix_iff_eq_take
- \- *theorem* suffix_iff_eq_drop
- \- *theorem* mem_inits
- \- *theorem* mem_tails
- \- *theorem* insert_nil
- \- *theorem* insert.def
- \- *theorem* insert_of_mem
- \- *theorem* insert_of_not_mem
- \- *theorem* mem_insert_iff
- \- *theorem* suffix_insert
- \- *theorem* infix_insert
- \- *theorem* sublist_insert
- \- *theorem* subset_insert
- \- *theorem* mem_insert_self
- \- *theorem* mem_insert_of_mem
- \- *theorem* eq_or_mem_of_mem_insert
- \- *theorem* length_insert_of_mem
- \- *theorem* length_insert_of_not_mem

Modified src/data/list/forall2.lean

Created src/data/list/infix.lean
- \+ *lemma* prefix_append
- \+ *lemma* suffix_append
- \+ *lemma* infix_append
- \+ *lemma* infix_append'
- \+ *lemma* is_prefix.is_infix
- \+ *lemma* is_suffix.is_infix
- \+ *lemma* nil_prefix
- \+ *lemma* nil_suffix
- \+ *lemma* nil_infix
- \+ *lemma* prefix_refl
- \+ *lemma* suffix_refl
- \+ *lemma* infix_refl
- \+ *lemma* prefix_rfl
- \+ *lemma* suffix_rfl
- \+ *lemma* infix_rfl
- \+ *lemma* suffix_cons
- \+ *lemma* prefix_concat
- \+ *lemma* infix_cons
- \+ *lemma* infix_concat
- \+ *lemma* is_prefix.trans
- \+ *lemma* is_suffix.trans
- \+ *lemma* is_infix.trans
- \+ *lemma* reverse_suffix
- \+ *lemma* reverse_prefix
- \+ *lemma* infix.length_le
- \+ *lemma* eq_nil_of_infix_nil
- \+ *lemma* infix_nil_iff
- \+ *lemma* prefix_nil_iff
- \+ *lemma* suffix_nil_iff
- \+ *lemma* infix_iff_prefix_suffix
- \+ *lemma* eq_of_infix_of_length_eq
- \+ *lemma* eq_of_prefix_of_length_eq
- \+ *lemma* eq_of_suffix_of_length_eq
- \+ *lemma* prefix_of_prefix_length_le
- \+ *lemma* prefix_or_prefix_of_prefix
- \+ *lemma* suffix_of_suffix_length_le
- \+ *lemma* suffix_or_suffix_of_suffix
- \+ *lemma* suffix_cons_iff
- \+ *lemma* infix_of_mem_join
- \+ *lemma* prefix_append_right_inj
- \+ *lemma* prefix_cons_inj
- \+ *lemma* take_prefix
- \+ *lemma* drop_suffix
- \+ *lemma* take_sublist
- \+ *lemma* drop_sublist
- \+ *lemma* take_subset
- \+ *lemma* drop_subset
- \+ *lemma* mem_of_mem_take
- \+ *lemma* mem_of_mem_drop
- \+ *lemma* init_prefix
- \+ *lemma* tail_suffix
- \+ *lemma* init_sublist
- \+ *lemma* tail_sublist
- \+ *lemma* init_subset
- \+ *lemma* tail_subset
- \+ *lemma* mem_of_mem_init
- \+ *lemma* mem_of_mem_tail
- \+ *lemma* prefix_iff_eq_append
- \+ *lemma* suffix_iff_eq_append
- \+ *lemma* prefix_iff_eq_take
- \+ *lemma* suffix_iff_eq_drop
- \+ *lemma* prefix_take_le_iff
- \+ *lemma* cons_prefix_iff
- \+ *lemma* is_prefix.map
- \+ *lemma* is_prefix.filter_map
- \+ *lemma* is_prefix.reduce_option
- \+ *lemma* is_prefix.filter
- \+ *lemma* is_suffix.filter
- \+ *lemma* is_infix.filter
- \+ *lemma* mem_inits
- \+ *lemma* mem_tails
- \+ *lemma* inits_cons
- \+ *lemma* tails_cons
- \+ *lemma* inits_append
- \+ *lemma* tails_append
- \+ *lemma* inits_eq_tails
- \+ *lemma* tails_eq_inits
- \+ *lemma* inits_reverse
- \+ *lemma* tails_reverse
- \+ *lemma* map_reverse_inits
- \+ *lemma* map_reverse_tails
- \+ *lemma* length_tails
- \+ *lemma* length_inits
- \+ *lemma* nth_le_tails
- \+ *lemma* nth_le_inits
- \+ *lemma* insert_nil
- \+ *lemma* insert.def
- \+ *lemma* insert_of_mem
- \+ *lemma* insert_of_not_mem
- \+ *lemma* mem_insert_iff
- \+ *lemma* suffix_insert
- \+ *lemma* infix_insert
- \+ *lemma* sublist_insert
- \+ *lemma* subset_insert
- \+ *lemma* mem_insert_self
- \+ *lemma* mem_insert_of_mem
- \+ *lemma* eq_or_mem_of_mem_insert
- \+ *lemma* length_insert_of_mem
- \+ *lemma* length_insert_of_not_mem

Modified src/data/list/lattice.lean

Modified src/data/nat/nth.lean



## [2021-12-27 16:46:22](https://github.com/leanprover-community/mathlib/commit/2ecf480)
feat(algebra/group/units): generalize `units.coe_lift` ([#11057](https://github.com/leanprover-community/mathlib/pull/11057))
* Generalize `units.coe_lift` from `group_with_zero` to `monoid`; use condition `is_unit` instead of `≠ 0`.
* Add some missing `@[to_additive]` attrs.
#### Estimated changes
Modified src/algebra/group/units.lean
- \+/\- *lemma* is_unit_of_subsingleton
- \+/\- *lemma* is_unit_of_subsingleton

Modified src/algebra/group_with_zero/basic.lean

Modified src/group_theory/submonoid/center.lean



## [2021-12-27 16:46:21](https://github.com/leanprover-community/mathlib/commit/de6f57d)
chore(ring_theory/unique_factorization_domain): Eliminate `finish` ([#11055](https://github.com/leanprover-community/mathlib/pull/11055))
Removing uses of finish, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/ring_theory/unique_factorization_domain.lean



## [2021-12-27 16:46:20](https://github.com/leanprover-community/mathlib/commit/d67c469)
feat(combinatorics/simple_graph/basic): edge deletion ([#11054](https://github.com/leanprover-community/mathlib/pull/11054))
Function to delete edges from a simple graph, and some associated lemmas.
Also defines `sym2.to_rel` as an inverse to `sym2.from_rel`.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* delete_edges_adj
- \+ *lemma* sdiff_eq_delete_edges
- \+ *lemma* compl_eq_delete_edges
- \+ *lemma* delete_edges_delete_edges
- \+ *lemma* delete_edges_empty_eq
- \+ *lemma* delete_edges_univ_eq
- \+ *lemma* delete_edges_le
- \+ *lemma* delete_edges_le_of_le
- \+ *lemma* delete_edges_eq_inter_edge_set
- \+ *def* delete_edges

Modified src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* spanning_coe_le_of_le
- \- *lemma* spanning_coe.is_subgraph_of_is_subgraph

Modified src/data/sym/sym2.lean
- \+ *lemma* to_rel_prop
- \+ *lemma* to_rel_symmetric
- \+ *lemma* to_rel_from_rel
- \+ *lemma* from_rel_to_rel
- \+ *def* to_rel



## [2021-12-27 16:46:19](https://github.com/leanprover-community/mathlib/commit/ca2c344)
split(data/finsupp/order): Split off `data.finsupp.basic` ([#11045](https://github.com/leanprover-community/mathlib/pull/11045))
This moves all order instances about `finsupp` from `data.finsupp.basic` and `data.finsupp.lattice` to a new file `data.finsupp.order`.
I'm crediting
* Johan for [#1216](https://github.com/leanprover-community/mathlib/pull/1216), [#1244](https://github.com/leanprover-community/mathlib/pull/1244)
* Aaron Anderson for [#3335](https://github.com/leanprover-community/mathlib/pull/3335)
#### Estimated changes
Modified src/data/finsupp/antidiagonal.lean

Modified src/data/finsupp/basic.lean
- \- *lemma* le_def
- \- *lemma* le_iff'
- \- *lemma* le_iff
- \- *lemma* single_le_iff
- \- *lemma* add_eq_zero_iff
- \- *lemma* coe_order_iso_multiset
- \- *lemma* coe_order_iso_multiset_symm
- \- *lemma* to_multiset_strict_mono
- \- *lemma* sum_id_lt_of_lt
- \- *lemma* lt_wf
- \- *lemma* coe_tsub
- \- *lemma* tsub_apply
- \- *lemma* single_tsub
- \- *lemma* support_tsub
- \- *lemma* subset_support_tsub
- \- *lemma* sub_single_one_add
- \- *lemma* add_sub_single_one
- \- *lemma* to_finsuppstrict_mono
- \- *def* order_iso_multiset

Deleted src/data/finsupp/lattice.lean
- \- *lemma* inf_apply
- \- *lemma* support_inf
- \- *lemma* sup_apply
- \- *lemma* support_sup
- \- *lemma* bot_eq_zero
- \- *lemma* disjoint_iff
- \- *lemma* order_embedding_to_fun_apply
- \- *lemma* monotone_to_fun
- \- *def* order_embedding_to_fun

Created src/data/finsupp/order.lean
- \+ *lemma* le_def
- \+ *lemma* order_embedding_to_fun_apply
- \+ *lemma* monotone_to_fun
- \+ *lemma* inf_apply
- \+ *lemma* sup_apply
- \+ *lemma* add_eq_zero_iff
- \+ *lemma* le_iff'
- \+ *lemma* le_iff
- \+ *lemma* single_le_iff
- \+ *lemma* coe_tsub
- \+ *lemma* tsub_apply
- \+ *lemma* single_tsub
- \+ *lemma* support_tsub
- \+ *lemma* subset_support_tsub
- \+ *lemma* support_inf
- \+ *lemma* support_sup
- \+ *lemma* disjoint_iff
- \+ *lemma* coe_order_iso_multiset
- \+ *lemma* coe_order_iso_multiset_symm
- \+ *lemma* to_multiset_strict_mono
- \+ *lemma* sum_id_lt_of_lt
- \+ *lemma* lt_wf
- \+ *lemma* sub_single_one_add
- \+ *lemma* add_sub_single_one
- \+ *lemma* to_finsupp_strict_mono
- \+ *def* order_embedding_to_fun
- \+ *def* order_iso_multiset



## [2021-12-27 16:46:18](https://github.com/leanprover-community/mathlib/commit/463be88)
feat(algebra/group_with_zero): add zero_mul_eq_const and mul_zero_eq_const ([#11021](https://github.com/leanprover-community/mathlib/pull/11021))
These are to match the corresponding lemmas about unapplied application of multiplication by 1. Like those lemmas, these are not marked simp.
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* zero_mul_eq_const
- \+ *lemma* mul_zero_eq_const



## [2021-12-27 16:46:17](https://github.com/leanprover-community/mathlib/commit/a360354)
feat(algebraic_geometry): Basic open set is empty iff section is zero in reduced schemes. ([#11012](https://github.com/leanprover-community/mathlib/pull/11012))
#### Estimated changes
Modified src/algebraic_geometry/locally_ringed_space.lean
- \+ *lemma* basic_open_zero

Modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+ *lemma* basic_open_eq_bot_iff

Modified src/algebraic_geometry/properties.lean
- \+ *lemma* is_reduced_of_open_immersion
- \+ *lemma* basic_open_eq_of_affine
- \+ *lemma* basic_open_eq_of_affine'
- \+ *lemma* reduce_to_affine_global
- \+ *lemma* eq_zero_of_basic_open_empty
- \+ *lemma* basic_open_eq_bot_iff

Modified src/algebraic_geometry/structure_sheaf.lean

Modified src/ring_theory/nilpotent.lean
- \+ *lemma* is_reduced_of_injective

Modified src/topology/opens.lean
- \+ *lemma* coe_bot



## [2021-12-27 16:46:16](https://github.com/leanprover-community/mathlib/commit/ae8f08f)
feat(combinatorics/simple_graph/connectivity): more lemmas ([#11010](https://github.com/leanprover-community/mathlib/pull/11010))
This is the second chunk of [#8737](https://github.com/leanprover-community/mathlib/pull/8737), which gives some more lemmas for manipulating the support and edge lists of walks. This also turns `is_trail` back into a structure.
#### Estimated changes
Modified src/combinatorics/simple_graph/connectivity.lean
- \+ *lemma* exists_eq_cons_of_ne
- \+ *lemma* support_append
- \+ *lemma* support_reverse
- \+ *lemma* tail_support_append
- \+ *lemma* support_eq_cons
- \+ *lemma* mem_support_iff
- \+ *lemma* mem_tail_support_append_iff
- \+ *lemma* end_mem_tail_support_of_ne
- \+ *lemma* mem_support_append_iff
- \+ *lemma* coe_support
- \+ *lemma* coe_support_append
- \+ *lemma* coe_support_append'
- \+ *lemma* edges_append
- \+ *lemma* edges_reverse
- \+/\- *lemma* mem_support_of_mem_edges
- \+ *lemma* edges_nodup_of_support_nodup
- \+ *lemma* is_trail_def
- \+ *lemma* is_path.mk'
- \+/\- *lemma* is_path_def
- \+ *lemma* is_trail.nil
- \+ *lemma* is_trail.of_cons
- \+/\- *lemma* cons_is_trail_iff
- \+ *lemma* is_trail.reverse
- \+ *lemma* reverse_is_trail_iff
- \+ *lemma* is_trail.of_append_left
- \+ *lemma* is_trail.of_append_right
- \+ *lemma* is_trail.count_edges_le_one
- \+ *lemma* is_trail.count_edges_eq_one
- \+ *lemma* is_path.nil
- \+ *lemma* is_path.of_cons
- \+ *lemma* is_path.reverse
- \+ *lemma* is_path_reverse_iff
- \+ *lemma* is_path.of_append_left
- \+ *lemma* is_path.of_append_right
- \- *lemma* support_eq
- \+/\- *lemma* mem_support_of_mem_edges
- \+/\- *lemma* is_path_def
- \- *lemma* count_edges_le_one_of_trail
- \- *lemma* count_edges_eq_one_of_trail
- \- *lemma* nil_is_trail
- \- *lemma* nil_is_path
- \- *lemma* is_trail_of_cons_is_trail
- \- *lemma* is_path_of_cons_is_path
- \+/\- *lemma* cons_is_trail_iff
- \- *def* is_trail



## [2021-12-27 16:46:14](https://github.com/leanprover-community/mathlib/commit/f525f93)
chore(*): Eliminate `finish` ([#10970](https://github.com/leanprover-community/mathlib/pull/10970))
Eliminating the use of `finish` in `data/set/basic`, `order/filter/bases`, and `topology/algebra/valued_field`.
#### Estimated changes
Modified src/data/set/basic.lean

Modified src/order/filter/bases.lean



## [2021-12-27 16:46:13](https://github.com/leanprover-community/mathlib/commit/2f3b966)
feat(number_theory/cyclotomic/basic): add is_cyclotomic_extension ([#10849](https://github.com/leanprover-community/mathlib/pull/10849))
We add a class `is_cyclotomic_extension S A B` expressing the fact that `B` is obtained by `A` by adding `n`-th
primitive roots of unity, for all `n ∈ S`, where `S : set ℕ+`, and some basic properties.
We will add more properties of cyclotomic extensions in a future work.
From flt-regular.
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* is_root.dvd

Created src/number_theory/cyclotomic/basic.lean
- \+ *lemma* iff_adjoin_eq_top
- \+ *lemma* iff_singleton
- \+ *lemma* empty
- \+ *lemma* trans
- \+ *lemma* union_right
- \+ *lemma* union_left
- \+ *lemma* finite_of_singleton
- \+ *lemma* finite
- \+ *lemma* number_field

Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* cyclotomic.dvd_X_pow_sub_one



## [2021-12-27 14:52:07](https://github.com/leanprover-community/mathlib/commit/002b8d9)
feat(algebra/group_with_zero/basic): mul_{left,right}_eq_self₀ ([#11069](https://github.com/leanprover-community/mathlib/pull/11069))
Defined on `cancel_monoid_with_zero`,
copying the name and proofs from `{left,right)_cancel_monoid`s,
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* mul_right_eq_self₀
- \+ *lemma* mul_left_eq_self₀



## [2021-12-27 12:07:40](https://github.com/leanprover-community/mathlib/commit/b28734c)
feat(data/sym): Provide API for data.sym ([#11032](https://github.com/leanprover-community/mathlib/pull/11032))
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* mem_repeat
- \+ *lemma* repeat_left_injective
- \+ *lemma* repeat_left_inj

Modified src/data/sym/basic.lean
- \+ *lemma* eq_nil_of_card_zero
- \+ *lemma* repeat_succ
- \+ *lemma* exists_eq_cons_of_succ
- \+ *lemma* eq_repeat_of_subsingleton
- \+ *lemma* repeat_left_inj
- \+ *lemma* repeat_left_injective
- \+ *lemma* mem_map
- \+ *lemma* map_id
- \+ *lemma* map_map
- \+ *lemma* map_zero
- \+ *lemma* map_cons
- \+ *def* erase
- \+ *def* repeat
- \+ *def* map
- \+ *def* equiv_congr

Modified src/data/sym/sym2.lean



## [2021-12-27 08:24:00](https://github.com/leanprover-community/mathlib/commit/7e0b994)
feat(topology/compact_convergence): define compact convergence ([#10967](https://github.com/leanprover-community/mathlib/pull/10967))
And prove that the topology it induces is the compact-open topology
#### Estimated changes
Modified src/topology/compact_open.lean

Modified src/topology/order.lean
- \+ *lemma* nhds_mk_of_nhds_filter_basis

Created src/topology/uniform_space/compact_convergence.lean
- \+ *lemma* self_mem_compact_conv_nhd
- \+ *lemma* compact_conv_nhd_mono
- \+ *lemma* compact_conv_nhd_mem_comp
- \+ *lemma* compact_conv_nhd_nhd_basis
- \+ *lemma* compact_conv_nhd_subset_inter
- \+ *lemma* compact_conv_nhd_compact_entourage_nonempty
- \+ *lemma* compact_conv_nhd_filter_is_basis
- \+ *lemma* mem_compact_convergence_nhd_filter
- \+ *lemma* nhds_compact_convergence
- \+ *lemma* has_basis_nhds_compact_convergence
- \+ *lemma* tendsto_iff_forall_compact_tendsto_uniformly_on'
- \+ *lemma* compact_conv_nhd_subset_compact_open
- \+ *lemma* Inter_compact_open_gen_subset_compact_conv_nhd
- \+ *lemma* compact_open_eq_compact_convergence
- \+ *lemma* mem_compact_convergence_uniformity
- \+ *lemma* mem_compact_convergence_entourage_iff
- \+ *lemma* has_basis_compact_convergence_uniformity
- \+ *lemma* tendsto_iff_forall_compact_tendsto_uniformly_on
- \+ *def* compact_conv_nhd
- \+ *def* compact_convergence_filter_basis
- \+ *def* compact_convergence_topology
- \+ *def* compact_convergence_uniformity



## [2021-12-26 23:49:34](https://github.com/leanprover-community/mathlib/commit/7c9ce5c)
feat(algebra/order/monoid_lemmas): `mul_eq_mul_iff_eq_and_eq` ([#11056](https://github.com/leanprover-community/mathlib/pull/11056))
If `a ≤ c` and `b ≤ d`, then `a * b = c * d` iff `a = c` and `b = d`.
#### Estimated changes
Modified src/algebra/order/monoid_lemmas.lean
- \+ *lemma* mul_eq_mul_iff_eq_and_eq



## [2021-12-26 05:05:27](https://github.com/leanprover-community/mathlib/commit/4f02336)
chore(analysis/complex/circle): minor review ([#11059](https://github.com/leanprover-community/mathlib/pull/11059))
* use implicit arg in `mem_circle_iff_abs`;
* rename `abs_eq_of_mem_circle` to `abs_coe_circle` to reflect the type of LHS;
* add `mem_circle_iff_norm_sq`.
#### Estimated changes
Modified src/analysis/complex/circle.lean
- \+/\- *lemma* mem_circle_iff_abs
- \+/\- *lemma* circle_def
- \+ *lemma* abs_coe_circle
- \+ *lemma* mem_circle_iff_norm_sq
- \+/\- *lemma* mem_circle_iff_abs
- \+/\- *lemma* circle_def
- \- *lemma* abs_eq_of_mem_circle

Modified src/analysis/special_functions/complex/circle.lean



## [2021-12-26 03:49:28](https://github.com/leanprover-community/mathlib/commit/daab3ac)
feat(data/pi/interval): Dependent functions to locally finite orders are locally finite ([#11050](https://github.com/leanprover-community/mathlib/pull/11050))
This provides the locally finite order instance for `Π i, α i` where the `α i` are locally finite.
#### Estimated changes
Created src/data/pi/interval.lean
- \+ *lemma* card_Icc
- \+ *lemma* card_Ico
- \+ *lemma* card_Ioc
- \+ *lemma* card_Ioo



## [2021-12-26 03:49:27](https://github.com/leanprover-community/mathlib/commit/2e2510e)
chore(logic/small): Some golfing ([#11030](https://github.com/leanprover-community/mathlib/pull/11030))
#### Estimated changes
Modified src/logic/small.lean
- \+ *theorem* small_map
- \+/\- *theorem* small_congr
- \+/\- *theorem* small_congr



## [2021-12-26 03:49:26](https://github.com/leanprover-community/mathlib/commit/dd6707c)
feat(measure_theory/integral): a couple of lemmas on integrals and integrability ([#10983](https://github.com/leanprover-community/mathlib/pull/10983))
Adds a couple of congruence lemmas for integrating on intervals and integrability
#### Estimated changes
Modified src/measure_theory/integral/integrable_on.lean
- \+ *lemma* integrable_on.congr_fun'
- \+ *lemma* integrable_on.congr_fun

Modified src/measure_theory/integral/interval_integral.lean
- \- *lemma* integral_Icc_eq_integral_Ioc'
- \- *lemma* integral_Icc_eq_integral_Ioc

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* integral_Icc_eq_integral_Ioc'
- \+ *lemma* integral_Ioc_eq_integral_Ioo'
- \+ *lemma* integral_Icc_eq_integral_Ioc
- \+ *lemma* integral_Ioc_eq_integral_Ioo

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* Iio_ae_eq_Iic'
- \+ *lemma* Ioi_ae_eq_Ici'
- \+ *lemma* Ioo_ae_eq_Ioc'
- \+ *lemma* Ioc_ae_eq_Icc'
- \+ *lemma* Ioo_ae_eq_Ico'
- \+ *lemma* Ioo_ae_eq_Icc'
- \+ *lemma* Ico_ae_eq_Icc'
- \+ *lemma* Ico_ae_eq_Ioc'



## [2021-12-26 02:00:29](https://github.com/leanprover-community/mathlib/commit/34e79d6)
chore(data/list/prod): remove an out of date comment ([#11058](https://github.com/leanprover-community/mathlib/pull/11058))
Due to changes in the library structure this comment is no longer relevant.
#### Estimated changes
Modified src/data/list/prod_monoid.lean



## [2021-12-26 01:20:52](https://github.com/leanprover-community/mathlib/commit/266d12b)
chore(ring_theory/polynomial/bernstein): use `∑` notation ([#11060](https://github.com/leanprover-community/mathlib/pull/11060))
Also rewrite a proof using `calc` mode
#### Estimated changes
Modified src/ring_theory/polynomial/bernstein.lean
- \+/\- *lemma* sum
- \+/\- *lemma* sum



## [2021-12-25 21:05:18](https://github.com/leanprover-community/mathlib/commit/abf9657)
feat(algebraic_geometry): Results about open immersions of schemes. ([#10977](https://github.com/leanprover-community/mathlib/pull/10977))
#### Estimated changes
Modified src/algebraic_geometry/Scheme.lean
- \- *def* to_LocallyRingedSpace

Modified src/algebraic_geometry/open_immersion.lean
- \+ *lemma* affine_basis_cover_obj
- \+ *lemma* to_Scheme_to_LocallyRingedSpace
- \+ *lemma* to_Scheme_hom_val
- \+ *lemma* Scheme_eq_of_LocallyRingedSpace_eq
- \+ *lemma* Scheme_to_Scheme
- \+ *def* iso_restrict
- \+ *def* affine_basis_cover_ring
- \+ *def* to_Scheme
- \+ *def* to_Scheme_hom



## [2021-12-25 21:05:17](https://github.com/leanprover-community/mathlib/commit/07b578e)
feat(data/int/basic): add lemma `gcd_greatest` ([#10613](https://github.com/leanprover-community/mathlib/pull/10613))
Proving a uniqueness property for `gcd`.  This is (a version of) Theorem 1.3 in Apostol (1976) Introduction to Analytic Number Theory.
#### Estimated changes
Modified src/algebra/gcd_monoid/basic.lean
- \+ *lemma* gcd_greatest
- \+ *lemma* gcd_greatest_associated

Modified src/data/int/gcd.lean
- \+ *lemma* gcd_greatest



## [2021-12-25 19:14:06](https://github.com/leanprover-community/mathlib/commit/8d426f0)
split(algebra/big_operators/multiset): Split off `data.multiset.basic` ([#11043](https://github.com/leanprover-community/mathlib/pull/11043))
This moves
* `multiset.prod`, `multiset.sum` to `algebra.big_operators.multiset`
* `multiset.join`, `multiset.bind`, `multiset.product`, `multiset.sigma` to `data.multiset.bind`. This is needed as `join` is defined
  using `sum`.
The file was quite messy, so I reorganized `algebra.big_operators.multiset` by increasing typeclass assumptions.
I'm crediting Mario for 0663945f55335e51c2b9b3a0177a84262dd87eaf (`prod`, `sum`, `join`), f9de18397dc1a43817803c2fe5d84b282287ed0d (`bind`, `product`), 16d40d7491d1fe8a733d21e90e516e0dd3f41c5b (`sigma`).
#### Estimated changes
Created src/algebra/big_operators/multiset.lean
- \+ *lemma* prod_eq_foldr
- \+ *lemma* prod_eq_foldl
- \+ *lemma* coe_prod
- \+ *lemma* prod_to_list
- \+ *lemma* prod_zero
- \+ *lemma* prod_cons
- \+ *lemma* prod_singleton
- \+ *lemma* prod_add
- \+ *lemma* prod_nsmul
- \+ *lemma* prod_repeat
- \+ *lemma* pow_count
- \+ *lemma* prod_map_one
- \+ *lemma* prod_map_mul
- \+ *lemma* prod_map_prod_map
- \+ *lemma* prod_induction
- \+ *lemma* prod_induction_nonempty
- \+ *lemma* prod_hom
- \+ *lemma* prod_hom_rel
- \+ *lemma* dvd_prod
- \+ *lemma* prod_dvd_prod
- \+ *lemma* coe_sum_add_monoid_hom
- \+ *lemma* prod_eq_zero
- \+ *lemma* prod_eq_zero_iff
- \+ *lemma* prod_ne_zero
- \+ *lemma* coe_inv_monoid_hom
- \+ *lemma* prod_map_inv
- \+ *lemma* sum_map_mul_left
- \+ *lemma* sum_map_mul_right
- \+ *lemma* dvd_sum
- \+ *lemma* one_le_prod_of_one_le
- \+ *lemma* single_le_prod
- \+ *lemma* prod_le_of_forall_le
- \+ *lemma* all_one_of_le_one_le_of_prod_eq_one
- \+ *lemma* prod_le_prod_of_rel_le
- \+ *lemma* prod_map_le_prod
- \+ *lemma* prod_le_sum_prod
- \+ *lemma* pow_card_le_prod
- \+ *lemma* prod_le_pow_card
- \+ *lemma* prod_nonneg
- \+ *lemma* sum_eq_zero_iff
- \+ *lemma* le_sum_of_mem
- \+ *lemma* le_prod_of_submultiplicative_on_pred
- \+ *lemma* le_prod_of_submultiplicative
- \+ *lemma* le_prod_nonempty_of_submultiplicative_on_pred
- \+ *lemma* le_prod_nonempty_of_submultiplicative
- \+ *lemma* sum_map_singleton
- \+ *lemma* abs_sum_le_sum_abs
- \+ *lemma* monoid_hom.map_multiset_prod
- \+ *def* prod
- \+ *def* sum_add_monoid_hom

Modified src/data/multiset/antidiagonal.lean

Modified src/data/multiset/basic.lean
- \- *lemma* coe_sum_add_monoid_hom
- \- *lemma* prod_nsmul
- \- *lemma* prod_map_one
- \- *lemma* prod_map_mul
- \- *lemma* prod_map_prod_map
- \- *lemma* sum_map_mul_left
- \- *lemma* sum_map_mul_right
- \- *lemma* prod_eq_zero
- \- *lemma* prod_eq_zero_iff
- \- *lemma* prod_hom
- \- *lemma* coe_inv_monoid_hom
- \- *lemma* prod_map_inv
- \- *lemma* dvd_prod
- \- *lemma* prod_dvd_prod
- \- *lemma* prod_nonneg
- \- *lemma* one_le_prod_of_one_le
- \- *lemma* single_le_prod
- \- *lemma* prod_le_of_forall_le
- \- *lemma* all_one_of_le_one_le_of_prod_eq_one
- \- *lemma* sum_eq_zero_iff
- \- *lemma* prod_induction
- \- *lemma* le_prod_of_submultiplicative_on_pred
- \- *lemma* le_prod_of_submultiplicative
- \- *lemma* prod_induction_nonempty
- \- *lemma* le_prod_nonempty_of_submultiplicative_on_pred
- \- *lemma* le_prod_nonempty_of_submultiplicative
- \- *lemma* bind_congr
- \- *lemma* bind_hcongr
- \- *lemma* map_bind
- \- *lemma* bind_map
- \- *lemma* bind_assoc
- \- *lemma* bind_bind
- \- *lemma* bind_map_comm
- \- *lemma* prod_bind
- \- *lemma* count_sum
- \- *lemma* count_bind
- \- *lemma* pow_count
- \- *lemma* rel_join
- \- *lemma* rel_bind
- \- *lemma* sum_le_sum_of_rel_le
- \- *lemma* le_sum_of_mem
- \- *lemma* sum_map_le_sum
- \- *lemma* sum_le_sum_map
- \- *lemma* card_nsmul_le_sum
- \- *lemma* sum_le_card_nsmul
- \- *theorem* prod_eq_foldr
- \- *theorem* prod_eq_foldl
- \- *theorem* coe_prod
- \- *theorem* prod_to_list
- \- *theorem* prod_zero
- \- *theorem* prod_cons
- \- *theorem* prod_singleton
- \- *theorem* prod_add
- \- *theorem* prod_repeat
- \- *theorem* prod_ne_zero
- \- *theorem* prod_hom_rel
- \- *theorem* dvd_sum
- \- *theorem* sum_map_singleton
- \- *theorem* abs_sum_le_sum_abs
- \- *theorem* coe_join
- \- *theorem* join_zero
- \- *theorem* join_cons
- \- *theorem* join_add
- \- *theorem* singleton_join
- \- *theorem* mem_join
- \- *theorem* card_join
- \- *theorem* coe_bind
- \- *theorem* zero_bind
- \- *theorem* cons_bind
- \- *theorem* singleton_bind
- \- *theorem* add_bind
- \- *theorem* bind_zero
- \- *theorem* bind_add
- \- *theorem* bind_cons
- \- *theorem* bind_singleton
- \- *theorem* mem_bind
- \- *theorem* card_bind
- \- *theorem* coe_product
- \- *theorem* zero_product
- \- *theorem* cons_product
- \- *theorem* product_singleton
- \- *theorem* add_product
- \- *theorem* product_add
- \- *theorem* mem_product
- \- *theorem* card_product
- \- *theorem* coe_sigma
- \- *theorem* zero_sigma
- \- *theorem* cons_sigma
- \- *theorem* sigma_singleton
- \- *theorem* add_sigma
- \- *theorem* sigma_add
- \- *theorem* mem_sigma
- \- *theorem* card_sigma
- \- *theorem* monoid_hom.map_multiset_prod
- \- *def* prod
- \- *def* sum_add_monoid_hom
- \- *def* join
- \- *def* bind
- \- *def* product

Created src/data/multiset/bind.lean
- \+ *lemma* coe_join
- \+ *lemma* join_zero
- \+ *lemma* join_cons
- \+ *lemma* join_add
- \+ *lemma* singleton_join
- \+ *lemma* mem_join
- \+ *lemma* card_join
- \+ *lemma* rel_join
- \+ *lemma* coe_bind
- \+ *lemma* zero_bind
- \+ *lemma* cons_bind
- \+ *lemma* singleton_bind
- \+ *lemma* add_bind
- \+ *lemma* bind_zero
- \+ *lemma* bind_add
- \+ *lemma* bind_cons
- \+ *lemma* bind_singleton
- \+ *lemma* mem_bind
- \+ *lemma* card_bind
- \+ *lemma* bind_congr
- \+ *lemma* bind_hcongr
- \+ *lemma* map_bind
- \+ *lemma* bind_map
- \+ *lemma* bind_assoc
- \+ *lemma* bind_bind
- \+ *lemma* bind_map_comm
- \+ *lemma* prod_bind
- \+ *lemma* rel_bind
- \+ *lemma* count_sum
- \+ *lemma* count_bind
- \+ *lemma* coe_product
- \+ *lemma* zero_product
- \+ *lemma* cons_product
- \+ *lemma* product_singleton
- \+ *lemma* add_product
- \+ *lemma* product_add
- \+ *lemma* mem_product
- \+ *lemma* card_product
- \+ *lemma* coe_sigma
- \+ *lemma* zero_sigma
- \+ *lemma* cons_sigma
- \+ *lemma* sigma_singleton
- \+ *lemma* add_sigma
- \+ *lemma* sigma_add
- \+ *lemma* mem_sigma
- \+ *lemma* card_sigma
- \+ *def* join
- \+ *def* bind
- \+ *def* product

Modified src/data/multiset/functor.lean

Modified src/data/multiset/nodup.lean

Modified src/data/multiset/sections.lean



## [2021-12-25 17:20:05](https://github.com/leanprover-community/mathlib/commit/4923cfc)
chore(set_theory/ordinal): Removed redundant argument from `enum_typein` ([#11049](https://github.com/leanprover-community/mathlib/pull/11049))
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+/\- *theorem* enum_typein
- \+/\- *theorem* enum_typein



## [2021-12-25 17:20:04](https://github.com/leanprover-community/mathlib/commit/ad99529)
feat(data/set/basic): Added `range_eq_iff` ([#11044](https://github.com/leanprover-community/mathlib/pull/11044))
This serves as a convenient theorem for proving statements of the form `range f = S`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* range_eq_iff



## [2021-12-25 16:16:30](https://github.com/leanprover-community/mathlib/commit/914250e)
chore(data/real/ennreal): adjust form of `to_real_pos_iff` ([#11047](https://github.com/leanprover-community/mathlib/pull/11047))
We have a principle (which may not have been crystallized at the time of writing of `data/real/ennreal`) that hypotheses of lemmas should contain the weak form `a ≠ ∞`, while conclusions should report the strong form `a < ∞`, and also the same for  `a ≠ 0`, `0 < a`.
In the case of the existing lemma
```lean
lemma to_real_pos_iff : 0 < a.to_real ↔ (0 < a ∧ a ≠ ∞):=
```
it's not clear whether the RHS of the iff should count as a hypothesis or a conclusion.  So I have rewritten to provide two forms,
```lean
lemma to_real_pos_iff : 0 < a.to_real ↔ (0 < a ∧ a < ∞):=
lemma to_real_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.to_real :=
```
Having both versions available shortens many proofs slightly.
#### Estimated changes
Modified src/analysis/convex/integral.lean

Modified src/data/real/ennreal.lean
- \+/\- *lemma* coe_inv_le
- \+/\- *lemma* to_nnreal_pos_iff
- \+ *lemma* to_nnreal_pos
- \+/\- *lemma* to_real_pos_iff
- \+ *lemma* to_real_pos
- \+/\- *lemma* coe_inv_le
- \+/\- *lemma* to_nnreal_pos_iff
- \+/\- *lemma* to_real_pos_iff

Modified src/measure_theory/function/lp_space.lean

Modified src/measure_theory/function/simple_func_dense.lean
- \+/\- *lemma* measure_preimage_lt_top_of_mem_ℒp
- \+/\- *lemma* mem_ℒp_iff
- \+/\- *lemma* mem_ℒp_iff_integrable
- \+/\- *lemma* mem_ℒp_iff_fin_meas_supp
- \+/\- *lemma* measure_lt_top_of_mem_ℒp_indicator
- \+/\- *lemma* measure_preimage_lt_top_of_mem_ℒp
- \+/\- *lemma* mem_ℒp_iff
- \+/\- *lemma* mem_ℒp_iff_integrable
- \+/\- *lemma* mem_ℒp_iff_fin_meas_supp
- \+/\- *lemma* measure_lt_top_of_mem_ℒp_indicator

Modified src/measure_theory/integral/set_to_l1.lean



## [2021-12-25 10:29:50](https://github.com/leanprover-community/mathlib/commit/c9f47c9)
chore(data/matrix/block): Eliminate `finish` ([#10948](https://github.com/leanprover-community/mathlib/pull/10948))
Removing uses of finish, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/data/matrix/block.lean



## [2021-12-25 10:29:49](https://github.com/leanprover-community/mathlib/commit/0aca706)
feat(measure_theory/integral): define `circle_integral` ([#10906](https://github.com/leanprover-community/mathlib/pull/10906))
#### Estimated changes
Modified src/algebra/periodic.lean
- \+ *lemma* periodic.image_Ioc

Created src/measure_theory/integral/circle_integral.lean
- \+ *lemma* periodic_circle_map
- \+ *lemma* circle_map_sub_center
- \+ *lemma* abs_circle_map_zero
- \+ *lemma* circle_map_mem_sphere'
- \+ *lemma* circle_map_mem_sphere
- \+ *lemma* circle_map_mem_closed_ball
- \+ *lemma* range_circle_map
- \+ *lemma* image_circle_map_Ioc
- \+ *lemma* circle_map_eq_center_iff
- \+ *lemma* circle_map_zero_radius
- \+ *lemma* circle_map_ne_center
- \+ *lemma* has_deriv_at_circle_map
- \+ *lemma* differentiable_circle_map
- \+ *lemma* continuous_circle_map
- \+ *lemma* measurable_circle_map
- \+ *lemma* deriv_circle_map
- \+ *lemma* deriv_circle_map_eq_zero_iff
- \+ *lemma* deriv_circle_map_ne_zero
- \+ *lemma* lipschitz_with_circle_map
- \+ *lemma* circle_integrable_const
- \+ *lemma* add
- \+ *lemma* neg
- \+ *lemma* out
- \+ *lemma* circle_integrable_zero_radius
- \+ *lemma* circle_integrable_iff
- \+ *lemma* continuous_on.circle_integrable'
- \+ *lemma* continuous_on.circle_integrable
- \+ *lemma* circle_integrable_sub_zpow_iff
- \+ *lemma* circle_integrable_sub_inv_iff
- \+ *lemma* integral_radius_zero
- \+ *lemma* integral_congr
- \+ *lemma* integral_undef
- \+ *lemma* integral_sub
- \+ *lemma* norm_integral_le_of_norm_le_const'
- \+ *lemma* norm_integral_le_of_norm_le_const
- \+ *lemma* integral_smul
- \+ *lemma* integral_smul_const
- \+ *lemma* integral_const_mul
- \+ *lemma* integral_sub_center_inv
- \+ *lemma* integral_eq_zero_of_has_deriv_within_at'
- \+ *lemma* integral_eq_zero_of_has_deriv_within_at
- \+ *lemma* integral_sub_zpow_of_undef
- \+ *lemma* integral_sub_zpow_of_ne
- \+ *lemma* cauchy_power_series_apply
- \+ *lemma* norm_cauchy_power_series_le
- \+ *lemma* le_radius_cauchy_power_series
- \+ *lemma* has_sum_two_pi_I_cauchy_power_series_integral
- \+ *lemma* has_sum_cauchy_power_series_integral
- \+ *lemma* sum_cauchy_power_series_eq_integral
- \+ *lemma* has_fpower_series_on_cauchy_integral
- \+ *lemma* integral_sub_inv_of_mem_ball
- \+ *def* circle_map
- \+ *def* circle_integrable
- \+ *def* circle_integral
- \+ *def* cauchy_power_series

Modified src/topology/metric_space/basic.lean
- \+ *theorem* closed_ball_mem_nhds_of_mem



## [2021-12-25 05:51:25](https://github.com/leanprover-community/mathlib/commit/ef8005c)
chore(category_theory/limits) : Remove instance requirement  ([#11041](https://github.com/leanprover-community/mathlib/pull/11041))
#### Estimated changes
Modified src/category_theory/limits/shapes/multiequalizer.lean



## [2021-12-25 05:51:24](https://github.com/leanprover-community/mathlib/commit/864a12e)
chore(measure_theory/function/lp_space): use notation for `nnnorm` ([#11039](https://github.com/leanprover-community/mathlib/pull/11039))
#### Estimated changes
Modified src/measure_theory/function/lp_space.lean
- \+/\- *lemma* snorm_one_eq_lintegral_nnnorm
- \+/\- *lemma* snorm_one_eq_lintegral_nnnorm



## [2021-12-25 05:51:23](https://github.com/leanprover-community/mathlib/commit/0f076d2)
chore(algebra/*): Eliminate `finish` ([#11034](https://github.com/leanprover-community/mathlib/pull/11034))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/algebra/big_operators/basic.lean

Modified src/algebra/continued_fractions/computation/approximations.lean



## [2021-12-25 05:51:22](https://github.com/leanprover-community/mathlib/commit/f9561d4)
feat(ring_theory/localization): The localization at a fg submonoid is of finite type. ([#10990](https://github.com/leanprover-community/mathlib/pull/10990))
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *lemma* submonoid_map_le_is_unit
- \+ *lemma* to_inv_submonoid_surjective
- \+ *lemma* to_inv_submonoid_mul
- \+ *lemma* mul_to_inv_submonoid
- \+ *lemma* smul_to_inv_submonoid
- \+ *lemma* surj'
- \+ *lemma* to_inv_submonoid_eq_mk'
- \+ *lemma* mem_inv_submonoid_iff_exists_mk'
- \+ *lemma* span_inv_submonoid
- \+ *lemma* finite_type_of_monoid_fg
- \+ *def* inv_submonoid
- \+ *def* to_inv_submonoid



## [2021-12-25 05:51:21](https://github.com/leanprover-community/mathlib/commit/5719a02)
feat(data/nat/totient): add totient_mul_prime_div ([#10971](https://github.com/leanprover-community/mathlib/pull/10971))
We add `(p * n).totient = p * n.totient` if `p ∣ n`.
#### Estimated changes
Modified src/data/nat/totient.lean
- \+ *lemma* totient_mul_of_prime_of_dvd

Modified src/ring_theory/multiplicity.lean
- \+ *lemma* pos_of_dvd
- \+ *lemma* exists_eq_pow_mul_and_not_dvd



## [2021-12-25 05:51:20](https://github.com/leanprover-community/mathlib/commit/d28b3bd)
feat(combinatorics/configuration): Points and lines inequality ([#10772](https://github.com/leanprover-community/mathlib/pull/10772))
If a nondegenerate configuration has a unique line through any two points, then there are at least as many lines as points.
#### Estimated changes
Modified src/combinatorics/configuration.lean
- \+ *lemma* has_lines.card_le
- \+ *lemma* has_points.card_le



## [2021-12-25 05:09:25](https://github.com/leanprover-community/mathlib/commit/0dd60ae)
feat(algebraic_geometry): Schemes are sober. ([#11040](https://github.com/leanprover-community/mathlib/pull/11040))
Also renamed things in `topology/sober.lean`.
#### Estimated changes
Modified src/algebraic_geometry/properties.lean

Modified src/topology/sober.lean
- \+ *lemma* closed_embedding.quasi_sober
- \+ *lemma* open_embedding.quasi_sober
- \+ *lemma* quasi_sober_of_open_cover
- \- *lemma* closed_embedding.sober
- \- *lemma* open_embedding.sober
- \- *lemma* sober_of_open_cover



## [2021-12-25 02:17:30](https://github.com/leanprover-community/mathlib/commit/f80c18b)
feat(measure_theory/measure/haar_lebesgue): Lebesgue measure of the image of a set under a linear map ([#11038](https://github.com/leanprover-community/mathlib/pull/11038))
The image of a set `s` under a linear map `f` has measure equal to `μ s` times the absolute value of the determinant of `f`.
#### Estimated changes
Modified src/measure_theory/measure/haar_lebesgue.lean
- \+ *lemma* add_haar_eq_zero_of_disjoint_translates_aux
- \+ *lemma* add_haar_eq_zero_of_disjoint_translates
- \+ *lemma* add_haar_submodule
- \+ *lemma* add_haar_preimage_linear_map
- \+ *lemma* add_haar_preimage_continuous_linear_map
- \+ *lemma* add_haar_preimage_linear_equiv
- \+ *lemma* add_haar_preimage_continuous_linear_equiv
- \+ *lemma* add_haar_image_linear_map
- \+ *lemma* add_haar_image_continuous_linear_map
- \+ *lemma* add_haar_image_continuous_linear_equiv
- \+/\- *lemma* add_haar_preimage_smul
- \+/\- *lemma* add_haar_smul
- \- *lemma* haar_preimage_linear_map
- \+/\- *lemma* add_haar_preimage_smul
- \+/\- *lemma* add_haar_smul



## [2021-12-24 23:10:00](https://github.com/leanprover-community/mathlib/commit/aa66909)
chore(algebraic_geometry): Remove unwanted spaces. ([#11042](https://github.com/leanprover-community/mathlib/pull/11042))
#### Estimated changes
Modified src/algebraic_geometry/sheafed_space.lean



## [2021-12-24 23:09:59](https://github.com/leanprover-community/mathlib/commit/d6ecc14)
feat(data/mv_polynomial): API for mv polynomial.rename ([#10921](https://github.com/leanprover-community/mathlib/pull/10921))
Relation between `rename` and `support`, `degrees` and `degree_of` when `f : σ → τ` is injective.
- I'm not sure if we already have something like `sup_map_multiset`.
- I've stated `sup_map_multiset`using `embedding` but I've used `injective` elsewhere because `mv_polynomial.rename` is written using `injective`.
-  I'm not sure if we should have `map_domain_embedding_of_injective`.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* map_finset_sup

Modified src/data/finsupp/basic.lean
- \+ *lemma* map_domain_support_of_injective
- \+ *def* map_domain_embedding

Modified src/data/mv_polynomial/rename.lean
- \+ *lemma* support_rename_of_injective

Modified src/data/mv_polynomial/variables.lean
- \+ *lemma* degrees_rename_of_injective
- \+ *lemma* degree_of_rename_of_injective



## [2021-12-24 23:09:58](https://github.com/leanprover-community/mathlib/commit/f7038c2)
feat(analysis/inner_product_space/adjoint): show that continuous linear maps on a Hilbert space form a C*-algebra ([#10837](https://github.com/leanprover-community/mathlib/pull/10837))
This PR puts a `cstar_ring` instance on `E →L[𝕜] E`, thereby showing that it forms a C*-algebra.
- [x] depends on: [#10825](https://github.com/leanprover-community/mathlib/pull/10825) [which defines the adjoint]
#### Estimated changes
Modified src/analysis/inner_product_space/adjoint.lean
- \+ *lemma* apply_norm_sq_eq_inner_adjoint_left
- \+ *lemma* apply_norm_eq_sqrt_inner_adjoint_left
- \+ *lemma* apply_norm_sq_eq_inner_adjoint_right
- \+ *lemma* apply_norm_eq_sqrt_inner_adjoint_right
- \+ *lemma* star_eq_adjoint

Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* re_inner_le_norm



## [2021-12-24 21:14:13](https://github.com/leanprover-community/mathlib/commit/8a997f3)
feat(combinatorics/configuration): Inequality between `point_count` and `line_count` ([#11036](https://github.com/leanprover-community/mathlib/pull/11036))
An inequality between `point_count` and `line_count`.
#### Estimated changes
Modified src/combinatorics/configuration.lean
- \+ *lemma* has_lines.point_count_le_line_count
- \+ *lemma* has_points.line_count_le_point_count



## [2021-12-24 21:14:12](https://github.com/leanprover-community/mathlib/commit/8181fe8)
feat(measure_theory/covering/besicovitch): covering a set by balls with controlled measure ([#11035](https://github.com/leanprover-community/mathlib/pull/11035))
We show that, in a real vector space, any set `s` can be covered by balls whose measures add up to at most `μ s + ε`, as a consequence of the Besicovitch covering theorem.
#### Estimated changes
Modified src/measure_theory/covering/besicovitch.lean
- \+ *theorem* exists_closed_ball_covering_tsum_measure_le

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* tsum_congr_subtype

Modified src/topology/instances/ennreal.lean
- \+ *lemma* tsum_mono_subtype
- \+ *lemma* tsum_union_le
- \+ *lemma* tsum_bUnion_le
- \+ *lemma* tsum_Union_le



## [2021-12-24 21:14:11](https://github.com/leanprover-community/mathlib/commit/a998db6)
refactor(data/nat/prime): redefine nat.prime as irreducible ([#11031](https://github.com/leanprover-community/mathlib/pull/11031))
#### Estimated changes
Modified archive/100-theorems-list/70_perfect_numbers.lean

Modified archive/imo/imo1969_q1.lean
- \+/\- *lemma* polynomial_not_prime
- \+/\- *lemma* polynomial_not_prime
- \+/\- *theorem* imo1969_q1
- \+/\- *theorem* imo1969_q1
- \+/\- *def* good_nats
- \+/\- *def* good_nats

Modified src/algebra/associated.lean
- \+ *theorem* irreducible.ne_one

Modified src/algebra/char_p/basic.lean

Modified src/data/int/nat_prime.lean

Modified src/data/nat/prime.lean
- \+ *lemma* two_le_iff
- \+ *lemma* prime.eq_one_or_self_of_dvd
- \- *lemma* prime.ne_zero
- \+/\- *theorem* not_prime_zero
- \+/\- *theorem* not_prime_one
- \+ *theorem* prime.ne_zero
- \+/\- *theorem* prime.pos
- \+/\- *theorem* prime.two_le
- \+ *theorem* prime_def_lt''
- \+/\- *theorem* prime.two_le
- \+/\- *theorem* prime.pos
- \+/\- *theorem* not_prime_zero
- \+/\- *theorem* not_prime_one
- \+/\- *def* prime
- \+/\- *def* min_fac_aux
- \+/\- *def* prime
- \+/\- *def* min_fac_aux

Modified src/data/zmod/basic.lean

Modified src/dynamics/periodic_pts.lean

Modified src/group_theory/order_of_element.lean

Modified src/group_theory/perm/cycle_type.lean

Modified src/group_theory/specific_groups/cyclic.lean

Modified src/number_theory/divisors.lean

Modified src/number_theory/primorial.lean
- \+/\- *lemma* dvd_choose_of_middling_prime
- \+/\- *lemma* prod_primes_dvd
- \+/\- *lemma* dvd_choose_of_middling_prime
- \+/\- *lemma* prod_primes_dvd
- \+/\- *def* primorial
- \+/\- *def* primorial

Modified src/number_theory/sum_four_squares.lean

Modified src/ring_theory/int/basic.lean
- \+/\- *theorem* irreducible_iff_nat_prime
- \+/\- *theorem* irreducible_iff_nat_prime

Modified test/fin_cases.lean



## [2021-12-24 21:14:10](https://github.com/leanprover-community/mathlib/commit/3588c3a)
feat(data/multiset/basic): empty_or_exists_mem ([#11023](https://github.com/leanprover-community/mathlib/pull/11023))
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* empty_or_exists_mem



## [2021-12-24 21:14:09](https://github.com/leanprover-community/mathlib/commit/404a912)
chore(ring_theory/adjoin/power_basis): add `simps` ([#11018](https://github.com/leanprover-community/mathlib/pull/11018))
#### Estimated changes
Modified src/ring_theory/adjoin/power_basis.lean

Modified src/ring_theory/norm.lean

Modified src/ring_theory/power_basis.lean



## [2021-12-24 21:14:08](https://github.com/leanprover-community/mathlib/commit/d5a3e8c)
feat(ring_theory/derivation): add 3 lemmas ([#10996](https://github.com/leanprover-community/mathlib/pull/10996))
Add `map_smul_of_tower`, `map_coe_nat`, and `map_coe_int`.
#### Estimated changes
Modified src/ring_theory/derivation.lean
- \+ *lemma* map_smul_of_tower
- \+ *lemma* map_coe_nat
- \+ *lemma* map_coe_int



## [2021-12-24 21:14:07](https://github.com/leanprover-community/mathlib/commit/c4268a8)
feat(topology,analysis): there exists `y ∈ frontier s` at distance `inf_dist x sᶜ` from `x` ([#10976](https://github.com/leanprover-community/mathlib/pull/10976))
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* exists_mem_frontier_inf_dist_compl_eq_dist

Modified src/topology/metric_space/hausdorff_distance.lean
- \+/\- *lemma* _root_.is_compact.exists_inf_edist_eq_edist
- \+ *lemma* not_mem_of_dist_lt_inf_dist
- \+ *lemma* disjoint_ball_inf_dist
- \+ *lemma* inf_dist_inter_closed_ball_of_mem
- \+ *lemma* _root_.is_compact.exists_inf_dist_eq_dist
- \+ *lemma* _root_.is_closed.exists_inf_dist_eq_dist
- \+ *lemma* exists_mem_closure_inf_dist_eq_dist
- \+ *lemma* closed_ball_inf_dist_compl_subset_closure'
- \+ *lemma* closed_ball_inf_dist_compl_subset_closure
- \+/\- *lemma* _root_.is_compact.exists_inf_edist_eq_edist



## [2021-12-24 19:23:20](https://github.com/leanprover-community/mathlib/commit/5dac1c0)
chore(topology/*): Eliminate `finish` ([#10991](https://github.com/leanprover-community/mathlib/pull/10991))
Removing uses of finish, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/data/fin/basic.lean
- \+ *lemma* fin_two_eq_of_eq_zero_iff

Modified src/topology/algebra/valued_field.lean

Modified src/topology/category/Compactum.lean

Modified src/topology/connected.lean

Modified src/topology/continuous_on.lean

Modified src/topology/locally_constant/basic.lean

Modified src/topology/uniform_space/basic.lean



## [2021-12-24 16:32:31](https://github.com/leanprover-community/mathlib/commit/35b67fd)
feat(algebra/order/field, data/real/basic): lemmas about `Sup` and `is_lub` ([#11013](https://github.com/leanprover-community/mathlib/pull/11013))
Add a lemma stating that for `f : α → ℝ` with `α` empty, `(⨆ i, f i) = 0`; a lemma stating that in an ordered field `is_lub` scales under multiplication by a nonnegative constant, and some variants.
#### Estimated changes
Modified src/algebra/order/field.lean
- \+ *lemma* is_lub.mul_left
- \+ *lemma* is_lub.mul_right
- \+ *lemma* is_glb.mul_left
- \+ *lemma* is_glb.mul_right

Modified src/data/real/basic.lean
- \+ *lemma* csupr_empty
- \+ *lemma* csupr_const_zero
- \+ *lemma* cinfi_empty
- \+ *lemma* cinfi_const_zero



## [2021-12-24 16:32:30](https://github.com/leanprover-community/mathlib/commit/3377bcc)
feat(analysis/inner_product_space/adjoint): define the adjoint of a continuous linear map between Hilbert spaces ([#10825](https://github.com/leanprover-community/mathlib/pull/10825))
This PR defines the adjoint of an operator `A : E →L[𝕜] F` as the unique operator `adjoint A : F →L[𝕜] E` such that `⟪x, A y⟫ = ⟪adjoint A x, y⟫` for all `x` and `y`. We then use this to put a star algebra structure on `E →L[𝕜] E` with the adjoint as the star operation (while leaving the C* property for a subsequent PR).
#### Estimated changes
Created src/analysis/inner_product_space/adjoint.lean
- \+ *lemma* adjoint_aux_apply
- \+ *lemma* adjoint_aux_inner_left
- \+ *lemma* adjoint_aux_inner_right
- \+ *lemma* adjoint_aux_adjoint_aux
- \+ *lemma* adjoint_aux_norm
- \+ *lemma* adjoint_inner_left
- \+ *lemma* adjoint_inner_right
- \+ *lemma* adjoint_adjoint
- \+ *lemma* adjoint_comp
- \+ *lemma* eq_adjoint_iff
- \+ *lemma* is_adjoint_pair
- \+ *def* adjoint_aux
- \+ *def* adjoint

Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* innerSL_flip_apply
- \+ *lemma* to_sesq_form_apply_coe
- \+ *lemma* to_sesq_form_apply_norm_le
- \+ *def* innerSL_flip
- \+ *def* to_sesq_form

Modified src/analysis/inner_product_space/dual.lean
- \+ *lemma* ext_inner_left
- \+ *lemma* ext_inner_right

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* op_norm_ext
- \+ *lemma* norm_to_continuous_linear_map_comp

Modified src/topology/algebra/module.lean
- \+ *lemma* comp_smulₛₗ



## [2021-12-24 15:31:49](https://github.com/leanprover-community/mathlib/commit/99c634c)
feat(analysis/normed_space/spectrum): adds easy direction of Gelfand's formula for the spectral radius ([#10847](https://github.com/leanprover-community/mathlib/pull/10847))
This adds the easy direction (i.e., an inequality) of Gelfand's formula for the spectral radius. Namely, we prove that `spectral_radius 𝕜 a ≤ ∥a ^ (n + 1)∥₊ ^ (1 / (n + 1) : ℝ)` for all `n : ℕ` using the spectral mapping theorem for polynomials.
- [x] depends on: [#10783](https://github.com/leanprover-community/mathlib/pull/10783)
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *lemma* norm_to_nnreal

Modified src/analysis/normed_space/spectrum.lean
- \+ *theorem* spectral_radius_le_pow_nnnorm_pow_one_div



## [2021-12-24 13:57:18](https://github.com/leanprover-community/mathlib/commit/ffbab0d)
chore(group_theory/quotient_group): change injective_ker_lift to ker_lift_injective for naming regularisation ([#11027](https://github.com/leanprover-community/mathlib/pull/11027))
Minor change for naming regularisation.
#### Estimated changes
Modified src/group_theory/quotient_group.lean



## [2021-12-24 13:57:17](https://github.com/leanprover-community/mathlib/commit/a0993e4)
feat(combinatorics/configuration): Sum of line counts equals sum of point counts ([#11026](https://github.com/leanprover-community/mathlib/pull/11026))
Counting the set `{(p,l) : P × L | p ∈ l}` in two different ways.
#### Estimated changes
Modified src/combinatorics/configuration.lean
- \+ *lemma* sum_line_count_eq_sum_point_count



## [2021-12-24 13:57:16](https://github.com/leanprover-community/mathlib/commit/04aeb01)
feat(data/polynomial/ring_division): roots.le_of_dvd ([#11025](https://github.com/leanprover-community/mathlib/pull/11025))
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+ *lemma* roots.le_of_dvd



## [2021-12-24 13:57:15](https://github.com/leanprover-community/mathlib/commit/c0e613a)
feat(combinatorics/configuration): `nondegenerate.exists_injective_of_card_le` ([#11019](https://github.com/leanprover-community/mathlib/pull/11019))
If a nondegenerate configuration has at least as many points as lines, then there exists an injective function `f` from lines to points, such that `f l` does not lie on `l`.
This is the key lemma for [#10772](https://github.com/leanprover-community/mathlib/pull/10772). The proof is an application of Hall's marriage theorem.
#### Estimated changes
Modified src/combinatorics/configuration.lean
- \+ *lemma* nondegenerate.exists_injective_of_card_le



## [2021-12-24 13:57:14](https://github.com/leanprover-community/mathlib/commit/2c4e6df)
feat(data/real/ennreal): trichotomy lemmas ([#11014](https://github.com/leanprover-community/mathlib/pull/11014))
If there is a case split one performs frequently, it can be useful to provide the case split and the standard data-wrangling one performs after the case split together.  I do this here for the `ennreal` case-split lemma
```lean
protected lemma trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.to_real :=
```
and a couple of variants.
#### Estimated changes
Modified src/data/real/ennreal.lean



## [2021-12-24 13:57:12](https://github.com/leanprover-community/mathlib/commit/7c7195f)
feat(field_theory/adjoin): lemmas about `inf`s of `intermediate_field`s ([#10997](https://github.com/leanprover-community/mathlib/pull/10997))
This adjusts the data in the `galois_insertion` slightly such that this new lemma is true by `rfl`, to match how we handle this in `subalgebra`. As a result, `top_to_subalgebra` is now refl, but `adjoin_univ` is no longer refl.
This also adds a handful of trivial simp lemmas.
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* coe_bot
- \+/\- *lemma* mem_bot
- \+ *lemma* coe_top
- \+/\- *lemma* mem_top
- \+ *lemma* top_to_subfield
- \+ *lemma* coe_inf
- \+ *lemma* mem_inf
- \+ *lemma* inf_to_subalgebra
- \+ *lemma* inf_to_subfield
- \+ *lemma* coe_Inf
- \+ *lemma* Inf_to_subalgebra
- \+ *lemma* Inf_to_subfield
- \+ *lemma* coe_infi
- \+ *lemma* infi_to_subalgebra
- \+ *lemma* infi_to_subfield
- \+ *lemma* adjoin_univ
- \+/\- *lemma* mem_bot
- \+/\- *lemma* mem_top

Modified src/field_theory/intermediate_field.lean
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq

Modified src/field_theory/normal.lean



## [2021-12-24 13:57:11](https://github.com/leanprover-community/mathlib/commit/d329d6b)
feat(combinatorics/simple_graph/connectivity): walks, paths, cycles ([#10981](https://github.com/leanprover-community/mathlib/pull/10981))
This is the first chunk of [#8737](https://github.com/leanprover-community/mathlib/pull/8737), which gives a type for walks in a simple graph as well as some basic operations.
It is designed to one day generalize to other types of graphs once there is a more generic framework by swapping out the `G.adj u v` argument from `walk`.
#### Estimated changes
Modified docs/references.bib

Created src/combinatorics/simple_graph/connectivity.lean
- \+ *lemma* cons_append
- \+ *lemma* cons_nil_append
- \+ *lemma* append_nil
- \+ *lemma* nil_append
- \+ *lemma* append_assoc
- \+ *lemma* reverse_nil
- \+ *lemma* reverse_singleton
- \+ *lemma* cons_reverse_aux
- \+ *lemma* reverse_cons
- \+ *lemma* reverse_append
- \+ *lemma* reverse_reverse
- \+ *lemma* length_nil
- \+ *lemma* length_cons
- \+ *lemma* length_append
- \+ *lemma* length_reverse
- \+ *lemma* support_nil
- \+ *lemma* support_cons
- \+ *lemma* support_ne_nil
- \+ *lemma* support_eq
- \+ *lemma* start_mem_support
- \+ *lemma* end_mem_support
- \+ *lemma* chain_adj_support_aux
- \+ *lemma* chain_adj_support
- \+ *lemma* edges_subset_edge_set
- \+ *lemma* edges_nil
- \+ *lemma* edges_cons
- \+ *lemma* length_support
- \+ *lemma* length_edges
- \+ *lemma* mem_support_of_mem_edges
- \+ *lemma* is_path_def
- \+ *lemma* is_cycle_def
- \+ *lemma* count_edges_le_one_of_trail
- \+ *lemma* count_edges_eq_one_of_trail
- \+ *lemma* nil_is_trail
- \+ *lemma* nil_is_path
- \+ *lemma* is_trail_of_cons_is_trail
- \+ *lemma* is_path_of_cons_is_path
- \+ *lemma* cons_is_trail_iff
- \+ *lemma* cons_is_path_iff
- \+ *def* length
- \+ *def* append
- \+ *def* reverse
- \+ *def* get_vert
- \+ *def* support
- \+ *def* edges
- \+ *def* is_trail



## [2021-12-24 13:57:10](https://github.com/leanprover-community/mathlib/commit/028c161)
feat(topology/is_locally_homeomorph): New file ([#10960](https://github.com/leanprover-community/mathlib/pull/10960))
This PR defines local homeomorphisms.
#### Estimated changes
Created src/topology/is_locally_homeomorph.lean
- \+ *lemma* mk
- \+ *lemma* map_nhds_eq
- \+ *lemma* is_open_map
- \+ *def* is_locally_homeomorph



## [2021-12-24 13:57:09](https://github.com/leanprover-community/mathlib/commit/a0f12bc)
feat(field_theory/adjoin): Supremum of finite dimensional intermediate fields ([#10938](https://github.com/leanprover-community/mathlib/pull/10938))
The supremum of finite dimensional intermediate fields is finite dimensional.
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* finite_dimensional_sup



## [2021-12-24 13:57:08](https://github.com/leanprover-community/mathlib/commit/084b1ac)
feat(group_theory/specific_groups/cyclic): |G|=expG ↔ G is cyclic ([#10692](https://github.com/leanprover-community/mathlib/pull/10692))
#### Estimated changes
Modified src/group_theory/specific_groups/cyclic.lean
- \+ *lemma* infinite.order_of_eq_zero_of_forall_mem_zpowers
- \+ *lemma* is_cyclic.exponent_eq_card
- \+ *lemma* is_cyclic.of_exponent_eq_card
- \+ *lemma* is_cyclic.iff_exponent_eq_card
- \+ *lemma* is_cyclic.exponent_eq_zero_of_infinite



## [2021-12-24 12:49:44](https://github.com/leanprover-community/mathlib/commit/6c6c7da)
feat(topology/connected): add `inducing.is_preconnected_image` ([#11011](https://github.com/leanprover-community/mathlib/pull/11011))
Generalize the proof of `subtype.preconnected_space` to any `inducing`
map. Also golf the proof of `is_preconnected.subset_right_of_subset_union`.
#### Estimated changes
Modified src/topology/connected.lean
- \+ *lemma* inducing.is_preconnected_image
- \+/\- *lemma* continuous.image_connected_component_subset
- \+ *lemma* continuous.maps_to_connected_component
- \+/\- *lemma* preimage_connected_component_connected
- \+/\- *lemma* continuous.image_connected_component_subset
- \+/\- *lemma* preimage_connected_component_connected



## [2021-12-24 03:30:38](https://github.com/leanprover-community/mathlib/commit/67cf406)
chore(scripts): update nolints.txt ([#11028](https://github.com/leanprover-community/mathlib/pull/11028))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt



## [2021-12-24 03:30:37](https://github.com/leanprover-community/mathlib/commit/f846a42)
feat(algebra/pointwise): expand API for multiplication / addition of finsets by copying the corresponding API for sets ([#10600](https://github.com/leanprover-community/mathlib/pull/10600))
From flt-regular, I wanted to be able to add finsets so we add a lot of API to show that the existing definition has good algebraic properties by copying the existing set API.
Where possible I tried to give proofs that use the existing set lemmas and cast the finsets to sets to make it clear that these are essentially the same lemmas.
It would be nice to have a better system for duplicating this API of course, some general versions for set_like or Galois insertions perhaps to unify the theories, but I don't know what that would look like.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* singleton_zero_mul
- \+ *lemma* singleton_one
- \+ *lemma* one_mem_one
- \+ *lemma* image_mul_prod
- \+ *lemma* image_mul_left
- \+ *lemma* image_mul_right
- \+ *lemma* image_mul_left'
- \+ *lemma* image_mul_right'
- \+ *lemma* preimage_mul_left_singleton
- \+ *lemma* preimage_mul_right_singleton
- \+ *lemma* preimage_mul_left_one
- \+ *lemma* preimage_mul_right_one
- \+ *lemma* preimage_mul_left_one'
- \+ *lemma* preimage_mul_right_one'
- \+ *theorem* one_nonempty
- \+ *theorem* image_one



## [2021-12-24 02:34:32](https://github.com/leanprover-community/mathlib/commit/7b641cb)
chore(number_theory/primorial): golf some proofs ([#11024](https://github.com/leanprover-community/mathlib/pull/11024))
#### Estimated changes
Modified src/number_theory/primorial.lean



## [2021-12-24 00:43:12](https://github.com/leanprover-community/mathlib/commit/1dd6080)
feat(ring_theory/derivation): drop unused `is_scalar_tower` ([#10995](https://github.com/leanprover-community/mathlib/pull/10995))
#### Estimated changes
Modified src/ring_theory/derivation.lean
- \+/\- *lemma* leibniz_inv
- \+/\- *lemma* leibniz_inv



## [2021-12-24 00:43:11](https://github.com/leanprover-community/mathlib/commit/f03447f)
feat(analysis/normed_space): a normed space over a nondiscrete normed field is noncompact ([#10994](https://github.com/leanprover-community/mathlib/pull/10994))
Register this as an instance for a nondiscrete normed field and for a real normed vector space. Also add `is_compact.ne_univ`.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* normed_space.exists_lt_norm

Modified src/topology/subset_properties.lean
- \+ *lemma* is_compact.ne_univ



## [2021-12-24 00:43:10](https://github.com/leanprover-community/mathlib/commit/0ac9f83)
feat(analysis/mean_inequalities): Minkowski inequality for infinite sums ([#10984](https://github.com/leanprover-community/mathlib/pull/10984))
A few versions of the Minkowski inequality for `tsum` and `has_sum`.
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *theorem* Lp_add_le_tsum
- \+ *theorem* Lp_add_le_has_sum
- \+ *theorem* Lp_add_le_tsum_of_nonneg
- \+ *theorem* Lp_add_le_has_sum_of_nonneg

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* rpow_inv_rpow_self
- \+ *lemma* rpow_self_rpow_inv
- \+ *lemma* rpow_one_div_le_iff
- \+ *lemma* rpow_left_injective
- \+ *lemma* rpow_eq_rpow_iff
- \+ *lemma* rpow_left_surjective
- \+ *lemma* rpow_left_bijective
- \+ *lemma* eq_rpow_one_div_iff
- \+ *lemma* rpow_one_div_eq_iff



## [2021-12-24 00:43:09](https://github.com/leanprover-community/mathlib/commit/1a780f6)
chore(topology/metric_space): export `is_compact_closed_ball` ([#10973](https://github.com/leanprover-community/mathlib/pull/10973))
#### Estimated changes
Modified src/analysis/inner_product_space/euclidean_dist.lean

Modified src/geometry/manifold/bump_function.lean

Modified src/measure_theory/covering/besicovitch_vector_space.lean

Modified src/topology/metric_space/basic.lean



## [2021-12-24 00:43:08](https://github.com/leanprover-community/mathlib/commit/36ba1ac)
feat(algebraic_geometry): Define `open_cover`s of Schemes. ([#10931](https://github.com/leanprover-community/mathlib/pull/10931))
#### Estimated changes
Created src/algebra/category/CommRing/instances.lean

Modified src/algebraic_geometry/Scheme.lean
- \+ *def* forget_to_LocallyRingedSpace
- \+ *def* forget_to_Top

Modified src/algebraic_geometry/locally_ringed_space.lean
- \+/\- *def* forget_to_SheafedSpace
- \+ *def* forget_to_Top
- \+/\- *def* forget_to_SheafedSpace

Modified src/algebraic_geometry/open_immersion.lean
- \+ *lemma* is_open_immersion.open_range
- \+ *lemma* affine_basis_cover_map_range
- \+ *lemma* affine_basis_cover_is_basis
- \+ *def* affine_cover
- \+ *def* open_cover.bind
- \+ *def* affine_basis_cover_of_affine
- \+ *def* affine_basis_cover



## [2021-12-24 00:43:07](https://github.com/leanprover-community/mathlib/commit/c374a3b)
feat(data/nat/nth): add nth function ([#10707](https://github.com/leanprover-community/mathlib/pull/10707))
Split off from [#9457](https://github.com/leanprover-community/mathlib/pull/9457), introduces `nth` and proves theorems about it.
#### Estimated changes
Modified src/data/nat/count.lean
- \+/\- *lemma* count_monotone
- \+ *lemma* count_lt_count_succ_iff
- \+ *lemma* count_strict_mono
- \+ *lemma* count_injective
- \+ *lemma* count_le_card
- \+ *lemma* count_lt_card
- \+/\- *lemma* count_monotone

Created src/data/nat/nth.lean
- \+ *lemma* nth_zero
- \+ *lemma* nth_zero_of_zero
- \+ *lemma* nth_zero_of_exists
- \+ *lemma* nth_set_card_aux
- \+ *lemma* nth_set_card
- \+ *lemma* nth_set_nonempty_of_lt_card
- \+ *lemma* nth_mem_of_lt_card_finite_aux
- \+ *lemma* nth_mem_of_lt_card_finite
- \+ *lemma* nth_strict_mono_of_finite
- \+ *lemma* nth_mem_of_infinite_aux
- \+ *lemma* nth_mem_of_infinite
- \+ *lemma* nth_strict_mono
- \+ *lemma* nth_monotone
- \+ *lemma* nth_mono_of_finite
- \+ *lemma* le_nth_of_lt_nth_succ_finite
- \+ *lemma* le_nth_of_lt_nth_succ_infinite
- \+ *lemma* count_nth_zero
- \+ *lemma* filter_range_nth_eq_insert_of_finite
- \+ *lemma* count_nth_of_lt_card_finite
- \+ *lemma* filter_range_nth_eq_insert_of_infinite
- \+ *lemma* count_nth_of_infinite
- \+ *lemma* nth_count
- \+ *lemma* nth_count_eq_Inf
- \+ *lemma* nth_count_le
- \+ *lemma* count_nth_gc
- \+ *lemma* count_le_iff_le_nth
- \+ *lemma* lt_nth_iff_count_lt
- \+ *lemma* nth_lt_of_lt_count
- \+ *lemma* le_nth_of_count_le
- \+ *lemma* nth_zero_of_nth_zero
- \+ *lemma* nth_eq_order_iso_of_nat

Modified src/order/order_iso_nat.lean



## [2021-12-23 22:35:58](https://github.com/leanprover-community/mathlib/commit/421b9bb)
feat(algebraic_topology): alternating face map complex of a simplicial object ([#10927](https://github.com/leanprover-community/mathlib/pull/10927))
added the alternating face map complex of a simplicial object in a preadditive category and the natural inclusion of the normalized_Moore_complex
#### Estimated changes
Created src/algebraic_topology/alternating_face_map_complex.lean
- \+ *lemma* d_squared
- \+ *lemma* inclusion_of_Moore_complex_map_f
- \+ *def* obj_d
- \+ *def* obj
- \+ *def* map
- \+ *def* alternating_face_map_complex
- \+ *def* inclusion_of_Moore_complex_map
- \+ *def* inclusion_of_Moore_complex



## [2021-12-23 22:35:57](https://github.com/leanprover-community/mathlib/commit/dc57de2)
feat(logic/basic): When a dependent If-Then-Else is not one of its arguments ([#10924](https://github.com/leanprover-community/mathlib/pull/10924))
This is the dependent version of [#10800](https://github.com/leanprover-community/mathlib/pull/10800).
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* not_ne_iff
- \+ *lemma* exists_iff_of_forall
- \+ *lemma* dite_eq_iff
- \+/\- *lemma* ite_eq_iff
- \+ *lemma* dite_eq_left_iff
- \+ *lemma* dite_eq_right_iff
- \+/\- *lemma* ite_eq_left_iff
- \+/\- *lemma* ite_eq_right_iff
- \+ *lemma* dite_ne_left_iff
- \+ *lemma* dite_ne_right_iff
- \+/\- *lemma* ite_ne_left_iff
- \+/\- *lemma* ite_ne_right_iff
- \+ *lemma* dite_eq_or_eq
- \+/\- *lemma* ite_eq_or_eq
- \+/\- *lemma* ite_eq_iff
- \+/\- *lemma* ite_eq_left_iff
- \+/\- *lemma* ite_eq_right_iff
- \+/\- *lemma* ite_ne_left_iff
- \+/\- *lemma* ite_ne_right_iff
- \+/\- *lemma* ite_eq_or_eq



## [2021-12-23 22:35:56](https://github.com/leanprover-community/mathlib/commit/1db0052)
feat(group_theory/submonoid/membership): upgrade definition of pow from a set morphism to a monoid morphism ([#10898](https://github.com/leanprover-community/mathlib/pull/10898))
This comes at no extra cost. All the prerequisite definitions and lemmas were already in mathlib.
#### Estimated changes
Modified src/group_theory/submonoid/membership.lean
- \+/\- *def* pow
- \+ *def* pow_log_equiv
- \+/\- *def* pow



## [2021-12-23 22:35:55](https://github.com/leanprover-community/mathlib/commit/68aada0)
feat(algebra/algebra/spectrum): prove the spectral mapping theorem for polynomials ([#10783](https://github.com/leanprover-community/mathlib/pull/10783))
Prove the spectral mapping theorem for polynomials. That is, if `p` is a polynomial and `a : A` where `A` is an algebra over a field `𝕜`, then `p (σ a) ⊆ σ (p a)`. Moreover, if `𝕜` is algebraically closed, then this inclusion is an equality.
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean
- \+ *lemma* exists_mem_of_not_is_unit_aeval_prod
- \+ *theorem* subset_polynomial_aeval
- \+ *theorem* map_polynomial_aeval_of_degree_pos
- \+ *theorem* map_polynomial_aeval_of_nonempty

Modified src/algebra/ring/basic.lean
- \+ *lemma* is_unit.sub_iff



## [2021-12-23 22:35:54](https://github.com/leanprover-community/mathlib/commit/720fa8f)
feat(data/rat/basic): API around rat.mk ([#10782](https://github.com/leanprover-community/mathlib/pull/10782))
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *lemma* ext_iff
- \+ *lemma* ext
- \+ *lemma* mk_neg_denom
- \+ *lemma* num_mk
- \+ *lemma* denom_mk

Modified src/number_theory/bernoulli.lean

Modified src/number_theory/number_field.lean



## [2021-12-23 19:11:42](https://github.com/leanprover-community/mathlib/commit/4ce0d04)
feat(data/real/sqrt): add a few lemmas ([#11003](https://github.com/leanprover-community/mathlib/pull/11003))
#### Estimated changes
Modified src/data/real/sqrt.lean
- \+ *lemma* sqrt_eq_one
- \+ *theorem* sqrt_eq_cases
- \+ *theorem* sqrt_eq_iff_mul_self_eq_of_pos



## [2021-12-23 19:11:41](https://github.com/leanprover-community/mathlib/commit/694b3f8)
chore(measure_theory): golf a proof ([#11002](https://github.com/leanprover-community/mathlib/pull/11002))
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean



## [2021-12-23 19:11:40](https://github.com/leanprover-community/mathlib/commit/3362b1e)
refactor(analysis/seminorm): Weaken typeclasses ([#10999](https://github.com/leanprover-community/mathlib/pull/10999))
This weakens `normed_field` to the appropriate `normed_whatever`.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+/\- *lemma* balanced.univ
- \+/\- *lemma* balanced.union
- \+/\- *lemma* balanced.inter
- \+/\- *lemma* balanced.add
- \+/\- *lemma* balanced.smul
- \+/\- *lemma* balanced.absorbs_self
- \+/\- *lemma* balanced.subset_smul
- \+/\- *lemma* balanced.smul_eq
- \+/\- *lemma* balanced_zero_union_interior
- \+/\- *lemma* sub_rev
- \+/\- *lemma* mem_ball
- \+/\- *lemma* mem_ball_zero
- \+/\- *lemma* ball_zero_eq
- \+/\- *lemma* balanced_ball_zero
- \+/\- *lemma* absorbent_ball_zero
- \+/\- *lemma* symmetric_ball_zero
- \+/\- *lemma* balanced.absorbs_self
- \+/\- *lemma* balanced.univ
- \+/\- *lemma* balanced.union
- \+/\- *lemma* balanced.inter
- \+/\- *lemma* balanced.add
- \+/\- *lemma* balanced.smul
- \+/\- *lemma* balanced.subset_smul
- \+/\- *lemma* balanced.smul_eq
- \+/\- *lemma* balanced_zero_union_interior
- \+/\- *lemma* sub_rev
- \+/\- *lemma* mem_ball
- \+/\- *lemma* mem_ball_zero
- \+/\- *lemma* ball_zero_eq
- \+/\- *lemma* balanced_ball_zero
- \+/\- *lemma* absorbent_ball_zero
- \+/\- *lemma* symmetric_ball_zero
- \+/\- *def* ball
- \+/\- *def* ball



## [2021-12-23 19:11:39](https://github.com/leanprover-community/mathlib/commit/cce09a6)
feat(ring_theory/finiteness): prove that a surjective endomorphism of a finite module over a comm ring is injective ([#10944](https://github.com/leanprover-community/mathlib/pull/10944))
Using an approach of Vasconcelos, treating the module as a module over the polynomial ring, with action induced by the endomorphism.
This result was rescued from [#1822](https://github.com/leanprover-community/mathlib/pull/1822).
#### Estimated changes
Modified src/ring_theory/finiteness.lean
- \+ *lemma* module_polynomial_of_endo.is_scalar_tower
- \+ *theorem* module.finite.injective_of_surjective_endomorphism
- \+ *def* module_polynomial_of_endo



## [2021-12-23 19:11:38](https://github.com/leanprover-community/mathlib/commit/327bacc)
feat(field_theory/adjoin): `intermediate_field.to_subalgebra` distributes over supremum ([#10937](https://github.com/leanprover-community/mathlib/pull/10937))
This PR proves `(E1 ⊔ E2).to_subalgebra = E1.to_subalgebra ⊔ E2.to_subalgebra`, under the assumption that `E1` and `E2` are finite-dimensional over `F`.
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* le_sup_to_subalgebra
- \+ *lemma* sup_to_subalgebra



## [2021-12-23 19:11:37](https://github.com/leanprover-community/mathlib/commit/e6f4852)
feat(group_theory/exponent): exponent G = ⨆ g : G, order_of g ([#10767](https://github.com/leanprover-community/mathlib/pull/10767))
Precursor to [#10692](https://github.com/leanprover-community/mathlib/pull/10692).
#### Estimated changes
Modified src/data/nat/lattice.lean
- \+ *lemma* _root_.set.infinite.nat.Sup_eq_zero

Modified src/group_theory/exponent.lean
- \+ *lemma* exponent_eq_zero_iff
- \+ *lemma* exponent_eq_zero_of_order_zero
- \+/\- *lemma* exponent_dvd_of_forall_pow_eq_one
- \+/\- *lemma* lcm_order_of_dvd_exponent
- \+ *lemma* _root_.nat.prime.exists_order_of_eq_pow_padic_val_nat_exponent
- \+ *lemma* exponent_ne_zero_iff_range_order_of_finite
- \+ *lemma* exponent_eq_zero_iff_range_order_of_infinite
- \+/\- *lemma* lcm_order_eq_exponent
- \+ *lemma* exponent_ne_zero_of_fintype
- \+ *lemma* exponent_eq_supr_order_of
- \+ *lemma* exponent_eq_supr_order_of'
- \+ *lemma* exponent_eq_max'_order_of
- \+/\- *lemma* exponent_dvd_of_forall_pow_eq_one
- \+/\- *lemma* lcm_order_of_dvd_exponent
- \+/\- *lemma* lcm_order_eq_exponent



## [2021-12-23 19:11:36](https://github.com/leanprover-community/mathlib/commit/1107693)
feat(combinatorics/simple_graph/basic): add lemmas about the neighbor set of a vertex in the complement graph ([#7138](https://github.com/leanprover-community/mathlib/pull/7138))
Add lemmas about the neighbor set of a vertex in the complement graph, including a lemma proving that the complement of a regular graph is regular. Part of [#5698](https://github.com/leanprover-community/mathlib/pull/5698) in order to prove facts about strongly regular graphs.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* card_neighbor_set_union_compl_neighbor_set
- \+ *lemma* neighbor_set_compl
- \+ *lemma* degree_compl
- \+ *lemma* is_regular_compl_of_is_regular



## [2021-12-23 18:32:08](https://github.com/leanprover-community/mathlib/commit/63a0936)
ci(.github/workflows/*): cleanup after upload step ([#11008](https://github.com/leanprover-community/mathlib/pull/11008))
cf. https://github.com/actions/upload-artifact/issues/256
#### Estimated changes
Modified .github/workflows/bors.yml

Modified .github/workflows/build.yml

Modified .github/workflows/build.yml.in

Modified .github/workflows/build_fork.yml



## [2021-12-23 16:33:07](https://github.com/leanprover-community/mathlib/commit/cf34598)
chore(tactic/norm_cast): minor cleanup ([#10993](https://github.com/leanprover-community/mathlib/pull/10993))
#### Estimated changes
Modified src/tactic/norm_cast.lean



## [2021-12-23 16:33:06](https://github.com/leanprover-community/mathlib/commit/1a57c79)
feat(analysis/calculus): assorted simple lemmas ([#10975](https://github.com/leanprover-community/mathlib/pull/10975))
Various lemmas from the formalization of the Cauchy integral formula ([#10000](https://github.com/leanprover-community/mathlib/pull/10000) and some later developments on top of it).
Also add `@[measurability]` attrs to theorems like `measurable_fderiv`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *theorem* has_deriv_within_at.scomp_has_deriv_at

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable_on.differentiable_at
- \+ *lemma* differentiable_on.eventually_differentiable_at

Modified src/analysis/calculus/fderiv_measurable.lean
- \+/\- *lemma* measurable_fderiv
- \+/\- *lemma* measurable_fderiv_apply_const
- \+/\- *lemma* measurable_deriv
- \+/\- *lemma* measurable_fderiv
- \+/\- *lemma* measurable_fderiv_apply_const
- \+/\- *lemma* measurable_deriv

Modified src/analysis/calculus/mean_value.lean
- \+ *theorem* _root_.lipschitz_with_of_nnnorm_deriv_le
- \+ *theorem* _root_.is_const_of_deriv_eq_zero



## [2021-12-23 16:33:04](https://github.com/leanprover-community/mathlib/commit/35ede3d)
chore(algebra/algebra/*): add some `simp` lemmas ([#10969](https://github.com/leanprover-community/mathlib/pull/10969))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* coe_of_bijective
- \+ *lemma* of_bijective_apply

Modified src/algebra/algebra/subalgebra.lean
- \+ *def* top_equiv

Modified src/field_theory/adjoin.lean
- \+ *lemma* top_equiv_symm_apply_coe
- \- *lemma* top_equiv_def
- \+ *def* top_equiv



## [2021-12-23 16:33:03](https://github.com/leanprover-community/mathlib/commit/7defe7d)
feat(field_theory/separable): add expand_eval and expand_monic ([#10965](https://github.com/leanprover-community/mathlib/pull/10965))
Simple properties of `polynomial.expand`.
#### Estimated changes
Modified src/field_theory/separable.lean
- \+ *lemma* monic.expand
- \+ *lemma* expand_eval



## [2021-12-23 16:33:01](https://github.com/leanprover-community/mathlib/commit/2be37b0)
feat(combinatorics/set_family/shadow): Upper shadow of a set family ([#10956](https://github.com/leanprover-community/mathlib/pull/10956))
This defines the upper shadow of `𝒜 : finset (finset α)`, which is the dual of the shadow. Instead of removing each element from each set, we add each element not in each set.
#### Estimated changes
Modified src/combinatorics/set_family/shadow.lean
- \+ *lemma* up_shadow_empty
- \+ *lemma* up_shadow_monotone
- \+ *lemma* mem_up_shadow_iff
- \+ *lemma* insert_mem_up_shadow
- \+ *lemma* mem_up_shadow_iff_erase_mem
- \+ *lemma* mem_up_shadow_iff_exists_mem_card_add_one
- \+ *lemma* exists_subset_of_mem_up_shadow
- \+ *lemma* mem_up_shadow_iff_exists_mem_card_add
- \+ *lemma* shadow_image_compl
- \+ *lemma* up_shadow_image_compl
- \+ *def* up_shadow



## [2021-12-23 16:33:00](https://github.com/leanprover-community/mathlib/commit/60c2b68)
feat(data/sigma/order): The lexicographical order has a bot/top ([#10905](https://github.com/leanprover-community/mathlib/pull/10905))
Also fix localized instances declarations. They weren't using fully qualified names and I had forgotten `sigma.lex.linear_order`.
#### Estimated changes
Modified src/data/sigma/order.lean
- \- *def* lex.has_le
- \- *def* lex.has_lt
- \- *def* lex.preorder
- \- *def* lex.partial_order
- \- *def* lex.linear_order



## [2021-12-23 16:32:59](https://github.com/leanprover-community/mathlib/commit/87fa060)
feat(combinatorics/configuration): Define `line_count` and `point_count` ([#10884](https://github.com/leanprover-community/mathlib/pull/10884))
Adds definitions for the number of lines through a given point and the number of points through a given line.
#### Estimated changes
Modified src/combinatorics/configuration.lean



## [2021-12-23 16:32:57](https://github.com/leanprover-community/mathlib/commit/bd164c7)
feat(data/polynomial/ring_division): add `polynomial.card_le_degree_of_subset_roots` ([#10824](https://github.com/leanprover-community/mathlib/pull/10824))
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+ *theorem* card_le_degree_of_subset_roots



## [2021-12-23 16:32:55](https://github.com/leanprover-community/mathlib/commit/ec6d9a7)
feat(topology/algebra/group): definitionally better lattice ([#10792](https://github.com/leanprover-community/mathlib/pull/10792))
This provides `(⊓)`, `⊤`, and `⊥` explicitly such that the associated `to_topological_space` lemmas are definitionally equal.
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *lemma* continuous_mul'
- \+ *lemma* continuous_inv'
- \+ *lemma* to_topological_space_injective
- \+/\- *lemma* ext'
- \+ *lemma* to_topological_space_le
- \+ *lemma* to_topological_space_top
- \+ *lemma* to_topological_space_bot
- \+ *lemma* to_topological_space_inf
- \+ *lemma* to_topological_space_Inf
- \+ *lemma* to_topological_space_infi
- \+/\- *lemma* ext'

Modified src/topology/constructions.lean
- \+ *lemma* continuous_inf_dom_left₂
- \+ *lemma* continuous_inf_dom_right₂
- \+ *lemma* continuous_Inf_dom₂



## [2021-12-23 16:32:53](https://github.com/leanprover-community/mathlib/commit/6e9b011)
feat(linear_algebra/orientation): composing with linear equivs and determinant ([#10737](https://github.com/leanprover-community/mathlib/pull/10737))
Add lemmas that composing an alternating map with a linear equiv using
`comp_linear_map`, or composing a basis with a linear equiv using
`basis.map`, produces the same orientation if and only if the
determinant of that linear equiv is positive.
#### Estimated changes
Modified src/algebra/order/ring.lean
- \+ *lemma* units.inv_pos
- \+ *lemma* units.inv_neg

Modified src/analysis/normed_space/units.lean

Modified src/linear_algebra/determinant.lean
- \+ *lemma* basis.det_map'

Modified src/linear_algebra/orientation.lean
- \+ *lemma* orientation_map
- \+ *lemma* map_orientation_eq_det_inv_smul
- \+ *lemma* units_inv_smul
- \+ *lemma* orientation_ne_iff_eq_neg
- \+ *lemma* orientation_comp_linear_equiv_eq_iff_det_pos
- \+ *lemma* orientation_comp_linear_equiv_eq_neg_iff_det_neg
- \+ *lemma* ne_iff_eq_neg
- \+ *lemma* map_eq_det_inv_smul
- \+ *lemma* map_eq_iff_det_pos
- \+ *lemma* map_eq_neg_iff_det_neg

Modified src/ring_theory/subring/basic.lean



## [2021-12-23 14:26:41](https://github.com/leanprover-community/mathlib/commit/3499323)
chore(data/vector3): Make linter happy ([#10998](https://github.com/leanprover-community/mathlib/pull/10998))
and clean up a bit.
#### Estimated changes
Modified src/data/vector3.lean
- \+ *lemma* cons_fz
- \+ *lemma* cons_fs
- \+ *lemma* eq_nil
- \+ *lemma* cons_head_tail
- \+ *lemma* cons_elim_cons
- \+ *lemma* rec_on_nil
- \+ *lemma* rec_on_cons
- \+ *lemma* append_nil
- \+ *lemma* append_cons
- \+ *lemma* append_left
- \+ *lemma* append_add
- \+ *lemma* insert_fz
- \+ *lemma* insert_fs
- \+ *lemma* append_insert
- \+ *lemma* exists_vector_zero
- \+ *lemma* exists_vector_succ
- \+ *lemma* vector_ex_iff_exists
- \+ *lemma* vector_all_iff_forall
- \+ *lemma* vector_allp_nil
- \+ *lemma* vector_allp_singleton
- \+ *lemma* vector_allp_cons
- \+ *lemma* vector_allp_iff_forall
- \+ *lemma* vector_allp.imp
- \- *theorem* cons_fz
- \- *theorem* cons_fs
- \- *theorem* eq_nil
- \- *theorem* cons_head_tail
- \- *theorem* cons_elim_cons
- \- *theorem* rec_on_nil
- \- *theorem* rec_on_cons
- \- *theorem* append_nil
- \- *theorem* append_cons
- \- *theorem* append_left
- \- *theorem* append_add
- \- *theorem* insert_fz
- \- *theorem* insert_fs
- \- *theorem* append_insert
- \- *theorem* exists_vector_zero
- \- *theorem* exists_vector_succ
- \- *theorem* vector_ex_iff_exists
- \- *theorem* vector_all_iff_forall
- \- *theorem* vector_allp_nil
- \- *theorem* vector_allp_singleton
- \- *theorem* vector_allp_cons
- \- *theorem* vector_allp_iff_forall
- \- *theorem* vector_allp.imp
- \+/\- *def* nil
- \+/\- *def* cons
- \+/\- *def* nth
- \+/\- *def* of_fn
- \+/\- *def* head
- \+/\- *def* tail
- \+/\- *def* nil_elim
- \+/\- *def* cons_elim
- \+/\- *def* append
- \+/\- *def* insert
- \+/\- *def* vector_ex
- \+/\- *def* vector_all
- \+/\- *def* vector_allp
- \+/\- *def* nil
- \+/\- *def* cons
- \+/\- *def* nth
- \+/\- *def* of_fn
- \+/\- *def* head
- \+/\- *def* tail
- \+/\- *def* nil_elim
- \+/\- *def* cons_elim
- \+/\- *def* append
- \+/\- *def* insert
- \+/\- *def* vector_ex
- \+/\- *def* vector_all
- \+/\- *def* vector_allp



## [2021-12-23 14:26:40](https://github.com/leanprover-community/mathlib/commit/72b4541)
feat(data/option): simple lemmas about orelse ([#10972](https://github.com/leanprover-community/mathlib/pull/10972))
Some simple lemmas about orelse. Analogous to `bind_eq_some` and friends.
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* orelse_eq_some
- \+ *lemma* orelse_eq_some'
- \+ *lemma* orelse_eq_none
- \+ *lemma* orelse_eq_none'



## [2021-12-23 14:26:39](https://github.com/leanprover-community/mathlib/commit/db1788c)
feat(ring_theory/tensor_product): Supremum of finite dimensional subalgebras ([#10922](https://github.com/leanprover-community/mathlib/pull/10922))
The supremum of finite dimensional subalgebras is finite dimensional.
#### Estimated changes
Modified src/ring_theory/tensor_product.lean
- \+ *lemma* subalgebra.finite_dimensional_sup



## [2021-12-23 12:54:33](https://github.com/leanprover-community/mathlib/commit/f3b380e)
feat(algebraic_geometry): Prime spectrum is sober. ([#10989](https://github.com/leanprover-community/mathlib/pull/10989))
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+ *lemma* is_closed_iff_zero_locus_ideal
- \+ *lemma* is_closed_iff_zero_locus_radical_ideal
- \+ *lemma* is_irreducible_zero_locus_iff_of_radical
- \+ *lemma* is_irreducible_zero_locus_iff

Modified src/topology/sober.lean
- \+ *lemma* is_generic_point_iff_forall_closed

Modified src/topology/subset_properties.lean
- \+ *lemma* irreducible_space_def



## [2021-12-23 10:36:41](https://github.com/leanprover-community/mathlib/commit/086469f)
chore(order/*): Change `order_hom` notation ([#10988](https://github.com/leanprover-community/mathlib/pull/10988))
This changes the notation for `order_hom` from `α →ₘ β` to `α →o β` to match `order_embedding` and `order_iso`, which are respectively `α ↪o β` and `α ≃o β`. This also solves the conflict with measurable functions.
#### Estimated changes
Modified src/algebra/lie/solvable.lean

Modified src/algebraic_topology/simplex_category.lean
- \+/\- *def* mk
- \+/\- *def* mk_hom
- \+/\- *def* mk
- \+/\- *def* mk_hom

Modified src/combinatorics/additive/salem_spencer.lean
- \+/\- *def* mul_roth_number
- \+/\- *def* roth_number_nat
- \+/\- *def* mul_roth_number
- \+/\- *def* roth_number_nat

Modified src/control/lawful_fix.lean
- \+/\- *lemma* to_unit_cont
- \+/\- *lemma* to_unit_cont
- \+/\- *def* to_unit_mono
- \+/\- *def* to_unit_mono

Modified src/data/finset/option.lean
- \+/\- *def* erase_none
- \+/\- *def* erase_none

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* coe_supr_of_chain
- \+/\- *lemma* mem_supr_of_chain
- \+/\- *lemma* coe_supr_of_chain
- \+/\- *lemma* mem_supr_of_chain
- \+/\- *def* iterate_range
- \+/\- *def* iterate_ker
- \+/\- *def* iterate_range
- \+/\- *def* iterate_ker

Modified src/linear_algebra/eigenspace.lean
- \+/\- *def* generalized_eigenspace
- \+/\- *def* generalized_eigenspace

Modified src/linear_algebra/prod.lean
- \+/\- *def* tunnel
- \+/\- *def* tunnel

Modified src/order/closure.lean

Modified src/order/fixed_points.lean
- \+/\- *lemma* lfp_lfp
- \+/\- *lemma* gfp_gfp
- \+/\- *lemma* lfp_lfp
- \+/\- *lemma* gfp_gfp
- \+/\- *def* lfp
- \+/\- *def* gfp
- \+/\- *def* lfp
- \+/\- *def* gfp

Modified src/order/hom/basic.lean
- \+/\- *lemma* to_fun_eq_coe
- \+/\- *lemma* ext
- \+/\- *lemma* le_def
- \+/\- *lemma* coe_le_coe
- \+/\- *lemma* apply_mono
- \+/\- *lemma* curry_apply
- \+/\- *lemma* curry_symm_apply
- \+/\- *lemma* comp_mono
- \+/\- *lemma* comp_id
- \+/\- *lemma* id_comp
- \+/\- *lemma* const_comp
- \+/\- *lemma* comp_const
- \+/\- *lemma* prod_mono
- \+/\- *lemma* comp_prod_comp_same
- \+/\- *lemma* fst_prod_snd
- \+/\- *lemma* fst_comp_prod
- \+/\- *lemma* snd_comp_prod
- \+/\- *lemma* order_hom_eq_id
- \+/\- *lemma* to_fun_eq_coe
- \+/\- *lemma* ext
- \+/\- *lemma* le_def
- \+/\- *lemma* coe_le_coe
- \+/\- *lemma* apply_mono
- \+/\- *lemma* curry_apply
- \+/\- *lemma* curry_symm_apply
- \+/\- *lemma* comp_mono
- \+/\- *lemma* comp_id
- \+/\- *lemma* id_comp
- \+/\- *lemma* const_comp
- \+/\- *lemma* comp_const
- \+/\- *lemma* prod_mono
- \+/\- *lemma* comp_prod_comp_same
- \+/\- *lemma* fst_prod_snd
- \+/\- *lemma* fst_comp_prod
- \+/\- *lemma* snd_comp_prod
- \+/\- *lemma* order_hom_eq_id
- \+/\- *def* id
- \+/\- *def* curry
- \+/\- *def* comp
- \+/\- *def* compₘ
- \+/\- *def* const
- \+/\- *def* prodₘ
- \+/\- *def* diag
- \+/\- *def* on_diag
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* prod_iso
- \+/\- *def* prod_map
- \+/\- *def* _root_.pi.eval_order_hom
- \+/\- *def* coe_fn_hom
- \+/\- *def* apply
- \+/\- *def* pi
- \+/\- *def* pi_iso
- \+/\- *def* subtype.val
- \+/\- *def* unique
- \+/\- *def* to_order_hom
- \+/\- *def* to_order_hom
- \+/\- *def* id
- \+/\- *def* curry
- \+/\- *def* comp
- \+/\- *def* compₘ
- \+/\- *def* const
- \+/\- *def* prodₘ
- \+/\- *def* diag
- \+/\- *def* on_diag
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* prod_iso
- \+/\- *def* prod_map
- \+/\- *def* _root_.pi.eval_order_hom
- \+/\- *def* coe_fn_hom
- \+/\- *def* apply
- \+/\- *def* pi
- \+/\- *def* pi_iso
- \+/\- *def* subtype.val
- \+/\- *def* unique
- \+/\- *def* to_order_hom
- \+/\- *def* to_order_hom

Modified src/order/hom/lattice.lean
- \+/\- *lemma* Inf_apply
- \+/\- *lemma* infi_apply
- \+/\- *lemma* coe_infi
- \+/\- *lemma* Sup_apply
- \+/\- *lemma* supr_apply
- \+/\- *lemma* coe_supr
- \+/\- *lemma* iterate_sup_le_sup_iff
- \+/\- *lemma* Inf_apply
- \+/\- *lemma* infi_apply
- \+/\- *lemma* coe_infi
- \+/\- *lemma* Sup_apply
- \+/\- *lemma* supr_apply
- \+/\- *lemma* coe_supr
- \+/\- *lemma* iterate_sup_le_sup_iff

Modified src/order/omega_complete_partial_order.lean
- \+/\- *lemma* map_le_map
- \+/\- *lemma* continuous.of_bundled'
- \+/\- *lemma* continuous'_coe
- \+/\- *lemma* inf_continuous
- \+/\- *lemma* Sup_continuous
- \+/\- *lemma* supr_continuous
- \+/\- *lemma* sup_continuous
- \+/\- *lemma* ωSup_bind
- \+/\- *lemma* coe_apply
- \+/\- *lemma* map_le_map
- \+/\- *lemma* continuous.of_bundled'
- \+/\- *lemma* continuous'_coe
- \+/\- *lemma* inf_continuous
- \+/\- *lemma* Sup_continuous
- \+/\- *lemma* supr_continuous
- \+/\- *lemma* sup_continuous
- \+/\- *lemma* ωSup_bind
- \+/\- *lemma* coe_apply
- \+/\- *def* bind
- \+/\- *def* continuous
- \+/\- *def* of_mono
- \+/\- *def* apply
- \+/\- *def* to_mono
- \+/\- *def* bind
- \+/\- *def* continuous
- \+/\- *def* of_mono
- \+/\- *def* apply
- \+/\- *def* to_mono

Modified src/order/order_iso_nat.lean

Modified src/order/partial_sups.lean
- \+/\- *lemma* partial_sups_mono
- \+/\- *lemma* partial_sups_mono
- \+/\- *def* partial_sups
- \+/\- *def* partial_sups.gi
- \+/\- *def* partial_sups
- \+/\- *def* partial_sups.gi

Modified src/ring_theory/artinian.lean
- \+/\- *theorem* is_artinian.monotone_stabilizes
- \+/\- *theorem* is_artinian.monotone_stabilizes

Modified src/ring_theory/noetherian.lean

Modified src/set_theory/schroeder_bernstein.lean

Modified src/topology/omega_complete_partial_order.lean

Modified src/topology/opens.lean
- \+/\- *def* comap
- \+/\- *def* comap



## [2021-12-23 10:36:40](https://github.com/leanprover-community/mathlib/commit/03062ea)
feat(ring_theory/integral_closure): The product of the leading coeff and the root is integral. ([#10807](https://github.com/leanprover-community/mathlib/pull/10807))
#### Estimated changes
Modified src/ring_theory/integral_closure.lean
- \+ *lemma* normalize_scale_roots_coeff_mul_leading_coeff_pow
- \+ *lemma* leading_coeff_smul_normalize_scale_roots
- \+ *lemma* normalize_scale_roots_support
- \+ *lemma* normalize_scale_roots_degree
- \+ *lemma* normalize_scale_roots_eval₂_leading_coeff_mul
- \+ *lemma* normalize_scale_roots_monic
- \+ *lemma* ring_hom.is_integral_elem_leading_coeff_mul
- \+ *lemma* is_integral_leading_coeff_smul
- \+ *def* normalize_scale_roots



## [2021-12-23 08:49:38](https://github.com/leanprover-community/mathlib/commit/2cfa052)
feat(data/list/count): countp of true and false ([#10986](https://github.com/leanprover-community/mathlib/pull/10986))
#### Estimated changes
Modified src/data/list/count.lean
- \+ *lemma* countp_true
- \+ *lemma* countp_false



## [2021-12-23 07:22:33](https://github.com/leanprover-community/mathlib/commit/08b13ec)
feat(field_theory/adjoin): add dim_bot, finrank_bot ([#10964](https://github.com/leanprover-community/mathlib/pull/10964))
Added two simp lemmas, showing that the dimension and finrank respectively of bottom intermediate fields are 1.
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* dim_bot
- \+ *lemma* finrank_bot



## [2021-12-23 05:35:04](https://github.com/leanprover-community/mathlib/commit/f4e46fd)
feat(data/list/count): count_le_length ([#10982](https://github.com/leanprover-community/mathlib/pull/10982))
#### Estimated changes
Modified src/data/list/count.lean
- \+ *lemma* countp_le_length
- \+ *lemma* count_le_length



## [2021-12-23 03:43:57](https://github.com/leanprover-community/mathlib/commit/04779a3)
feat(order/complete_boolean_algebra): lemmas about binfi ([#10852](https://github.com/leanprover-community/mathlib/pull/10852))
Adds corresponding `binfi` and `Inf` lemmas for existing `infi` results, especially where `rw` struggles to achieve the same thing alone.
#### Estimated changes
Modified src/order/complete_boolean_algebra.lean
- \+ *theorem* bsupr_inf_eq
- \+ *theorem* inf_bsupr_eq
- \+ *theorem* binfi_sup_eq
- \+ *theorem* sup_binfi_eq

Modified src/order/galois_connection.lean
- \+ *lemma* l_bsupr_u
- \+ *lemma* l_Sup_u_image
- \+ *lemma* l_binfi_u
- \+ *lemma* l_Inf_u_image
- \+ *lemma* l_binfi_of_ul_eq_self
- \+ *lemma* u_Inf_l_image
- \+ *lemma* u_bsupr_l
- \+ *lemma* u_Sup_l_image
- \+ *lemma* u_bsupr_of_lu_eq_self



## [2021-12-23 02:02:13](https://github.com/leanprover-community/mathlib/commit/f00007d)
feat(analysis/normed_space/pointwise): more on pointwise operations on sets in normed spaces  ([#10820](https://github.com/leanprover-community/mathlib/pull/10820))
Also move all related results to a new file `analysis/normed_space/pointwise`, to shorten `normed_space/basic` a little bit.
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *lemma* mem_closed_ball_zero_iff
- \+/\- *lemma* preimage_add_ball
- \+/\- *lemma* preimage_add_closed_ball
- \+/\- *lemma* preimage_add_ball
- \+/\- *lemma* preimage_add_closed_ball

Created src/analysis/normed/group/pointwise.lean
- \+ *lemma* bounded_iff_exists_norm_le
- \+ *lemma* metric.bounded.add
- \+ *lemma* singleton_add_ball
- \+ *lemma* ball_add_singleton
- \+ *lemma* singleton_add_ball_zero
- \+ *lemma* ball_zero_add_singleton
- \+ *lemma* singleton_add_closed_ball
- \+ *lemma* closed_ball_add_singleton
- \+ *lemma* singleton_add_closed_ball_zero
- \+ *lemma* closed_ball_zero_add_singleton

Modified src/analysis/normed_space/basic.lean
- \- *theorem* smul_ball
- \- *theorem* smul_sphere'
- \- *theorem* normed_space.sphere_nonempty
- \- *theorem* smul_sphere
- \- *theorem* smul_closed_ball'
- \- *theorem* smul_closed_ball

Modified src/analysis/normed_space/finite_dimension.lean

Created src/analysis/normed_space/pointwise.lean
- \+ *lemma* metric.bounded.smul
- \+ *lemma* eventually_singleton_add_smul_subset
- \+ *lemma* set_smul_mem_nhds_zero
- \+ *lemma* set_smul_mem_nhds_zero_iff
- \+ *theorem* smul_ball
- \+ *theorem* smul_sphere'
- \+ *theorem* normed_space.sphere_nonempty
- \+ *theorem* smul_sphere
- \+ *theorem* smul_closed_ball'
- \+ *theorem* smul_closed_ball

Modified src/measure_theory/measure/haar_lebesgue.lean

Modified src/topology/metric_space/basic.lean
- \+ *lemma* bounded.subset_ball_lt



## [2021-12-22 23:07:54](https://github.com/leanprover-community/mathlib/commit/e15e015)
split(data/finset/sigma): Split off `data.finset.basic` ([#10957](https://github.com/leanprover-community/mathlib/pull/10957))
This moves `finset.sigma` to a new file `data.finset.sigma`.
I'm crediting Mario for 16d40d7491d1fe8a733d21e90e516e0dd3f41c5b
#### Estimated changes
Modified src/data/finset/basic.lean
- \- *theorem* mem_sigma
- \- *theorem* sigma_nonempty
- \- *theorem* sigma_eq_empty
- \- *theorem* sigma_mono
- \- *theorem* sigma_eq_bUnion

Modified src/data/finset/lattice.lean
- \- *lemma* sup_sigma
- \- *lemma* inf_sigma

Created src/data/finset/sigma.lean
- \+ *lemma* mem_sigma
- \+ *lemma* sigma_nonempty
- \+ *lemma* sigma_eq_empty
- \+ *lemma* sigma_mono
- \+ *lemma* sigma_eq_bUnion
- \+ *lemma* sup_sigma
- \+ *lemma* inf_sigma

Modified src/data/fintype/basic.lean



## [2021-12-22 23:07:53](https://github.com/leanprover-community/mathlib/commit/3f16409)
feat(data/finset/*): Random lemmas ([#10955](https://github.com/leanprover-community/mathlib/pull/10955))
Prove some `compl` lemmas for `finset`, `(s.erase a).card + 1 = s.card` for `list`, `multiset`, `set`, copy over one more `generalized_boolean_algebra` lemma.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+/\- *lemma* not_mem_sdiff_of_mem_right
- \+/\- *lemma* union_sdiff_symm
- \+/\- *lemma* sdiff_eq_empty_iff_subset
- \+/\- *lemma* sdiff_ssubset
- \+ *lemma* sdiff_sdiff_eq_self
- \+ *lemma* map_nonempty
- \+/\- *lemma* not_mem_sdiff_of_mem_right
- \+/\- *lemma* union_sdiff_symm
- \+/\- *lemma* sdiff_eq_empty_iff_subset
- \+/\- *lemma* sdiff_ssubset
- \- *lemma* nonempty.map
- \+/\- *theorem* mem_sdiff
- \+/\- *theorem* union_sdiff_self_eq_union
- \+/\- *theorem* sdiff_union_self_eq_union
- \+/\- *theorem* mem_sdiff
- \+/\- *theorem* union_sdiff_self_eq_union
- \+/\- *theorem* sdiff_union_self_eq_union

Modified src/data/finset/card.lean
- \+ *lemma* card_erase_add_one

Modified src/data/fintype/basic.lean
- \+ *lemma* eq_univ_iff_forall
- \+/\- *lemma* compl_eq_univ_sdiff
- \+/\- *lemma* mem_compl
- \+ *lemma* not_mem_compl
- \+/\- *lemma* coe_compl
- \+ *lemma* compl_empty
- \+ *lemma* union_compl
- \+ *lemma* compl_erase
- \+ *lemma* compl_insert
- \+ *lemma* insert_compl_self
- \+/\- *lemma* compl_filter
- \+/\- *lemma* compl_ne_univ_iff_nonempty
- \+/\- *lemma* compl_singleton
- \+/\- *lemma* compl_eq_univ_sdiff
- \+/\- *lemma* mem_compl
- \+/\- *lemma* coe_compl
- \+/\- *lemma* compl_filter
- \+/\- *lemma* compl_ne_univ_iff_nonempty
- \+/\- *lemma* compl_singleton
- \- *theorem* union_compl
- \- *theorem* insert_compl_self
- \- *theorem* eq_univ_iff_forall

Modified src/data/list/basic.lean
- \+ *lemma* length_erasep_add_one
- \+ *lemma* length_erase_add_one

Modified src/data/multiset/basic.lean
- \+ *lemma* card_erase_add_one



## [2021-12-22 23:07:52](https://github.com/leanprover-community/mathlib/commit/2b9ab3b)
split(data/psigma/order): Split off `order.lexicographic` ([#10953](https://github.com/leanprover-community/mathlib/pull/10953))
This moves all the stuff about `Σ' i, α i` to a new file `data.psigma.order`. This mimics the file organisation of `sigma`.
I'm crediting:
* Scott for [#820](https://github.com/leanprover-community/mathlib/pull/820)
* Minchao for [#914](https://github.com/leanprover-community/mathlib/pull/914)
#### Estimated changes
Modified src/combinatorics/colex.lean

Modified src/data/list/lex.lean

Created src/data/psigma/order.lean

Modified src/data/sigma/lex.lean

Modified src/data/sigma/order.lean

Modified src/order/lexicographic.lean



## [2021-12-22 23:07:51](https://github.com/leanprover-community/mathlib/commit/4315973)
feat(quadratic_form/prod): quadratic forms on product and pi types ([#10939](https://github.com/leanprover-community/mathlib/pull/10939))
In order to provide the `pos_def` members, some new API was needed.
#### Estimated changes
Modified src/linear_algebra/clifford_algebra/equivs.lean
- \+/\- *def* Q
- \+/\- *def* Q

Modified src/linear_algebra/quadratic_form/basic.lean
- \+ *lemma* anisotropic.eq_zero_iff
- \+ *lemma* pos_def.nonneg
- \+ *lemma* pos_def.anisotropic
- \+ *lemma* pos_def_of_nonneg
- \+ *lemma* pos_def_iff_nonneg
- \+ *def* sq

Created src/linear_algebra/quadratic_form/prod.lean
- \+ *lemma* equivalent.prod
- \+ *lemma* anisotropic_of_prod
- \+ *lemma* nonneg_prod_iff
- \+ *lemma* pos_def_prod_iff
- \+ *lemma* pos_def.prod
- \+ *lemma* pi_apply
- \+ *lemma* equivalent.pi
- \+ *lemma* anisotropic_of_pi
- \+ *lemma* nonneg_pi_iff
- \+ *lemma* pos_def_pi_iff
- \+ *def* prod
- \+ *def* isometry.prod
- \+ *def* pi
- \+ *def* isometry.pi



## [2021-12-22 23:07:50](https://github.com/leanprover-community/mathlib/commit/c8f0afc)
feat(group_theory/index): Transitivity of finite relative index. ([#10936](https://github.com/leanprover-community/mathlib/pull/10936))
If `H` has finite relative index in `K`, and `K` has finite relative index in `L`, then `H` has finite relative index in `L`. Golfed from [#9545](https://github.com/leanprover-community/mathlib/pull/9545).
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* relindex_inf_mul_relindex
- \+ *lemma* relindex_ne_zero_trans



## [2021-12-22 23:07:49](https://github.com/leanprover-community/mathlib/commit/24cefb5)
feat(data/real/ennreal): add monotonicity lemmas for ennreal.to_nnreal ([#10556](https://github.com/leanprover-community/mathlib/pull/10556))
Add four lemmas about monotonicity of `to_nnreal` on extended nonnegative reals, `to_nnreal_mono`, `to_nnreal_le_to_nnreal`, `to_nnreal_strict_mono`, `to_nnreal_lt_to_nnreal` (analogous to `to_real_mono`, `to_real_le_to_nnreal`, `to_real_strict_mono`, `to_real_lt_to_real`).
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* to_nnreal_mono
- \+ *lemma* to_nnreal_le_to_nnreal
- \+ *lemma* to_nnreal_strict_mono
- \+ *lemma* to_nnreal_lt_to_nnreal



## [2021-12-22 21:32:02](https://github.com/leanprover-community/mathlib/commit/c5bb320)
refactor(*): Random lemmas and modifications from the shifting refactor. ([#10940](https://github.com/leanprover-community/mathlib/pull/10940))
#### Estimated changes
Modified src/algebra/homology/differential_object.lean
- \+ *lemma* _root_.category_theory.differential_object.X_eq_to_hom_refl
- \+ *lemma* eq_to_hom_d
- \+ *lemma* d_eq_to_hom
- \+ *lemma* eq_to_hom_f

Modified src/category_theory/differential_object.lean
- \+ *lemma* eq_to_hom_f
- \+ *def* mk_iso

Modified src/category_theory/equivalence.lean
- \+ *lemma* as_equivalence_unit
- \+ *lemma* as_equivalence_counit

Modified src/category_theory/graded_object.lean
- \+ *lemma* eq_to_hom_apply

Modified src/category_theory/limits/has_limits.lean
- \+ *lemma* has_smallest_limits_of_has_limits
- \+ *lemma* has_smallest_colimits_of_has_colimits

Modified src/category_theory/monoidal/End.lean
- \+ *lemma* μ_inv_naturalityₗ
- \+ *lemma* μ_inv_naturalityᵣ

Modified src/category_theory/monoidal/discrete.lean

Modified src/category_theory/natural_isomorphism.lean

Modified src/category_theory/triangulated/basic.lean
- \+/\- *def* triangle.mk
- \+/\- *def* triangle.mk



## [2021-12-22 20:39:43](https://github.com/leanprover-community/mathlib/commit/ee25d58)
feat(linear_algebra/quadratic_form/basic): `linear_map.comp_quadratic_form` ([#10950](https://github.com/leanprover-community/mathlib/pull/10950))
The name is taken to mirror `linear_map.comp_multilinear_map`
#### Estimated changes
Modified src/linear_algebra/quadratic_form/basic.lean
- \+ *lemma* polar_comp
- \+ *lemma* map_smul_of_tower
- \+ *def* _root_.linear_map.comp_quadratic_form



## [2021-12-22 20:39:42](https://github.com/leanprover-community/mathlib/commit/b2e881b)
feat(linear_algebra/eigenspace): the eigenvalues of a linear endomorphism are in its spectrum ([#10912](https://github.com/leanprover-community/mathlib/pull/10912))
This PR shows that the eigenvalues of `f : End R M` are in `spectrum R f`.
#### Estimated changes
Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* has_eigenvector.apply_eq_smul
- \+ *lemma* mem_spectrum_of_has_eigenvalue



## [2021-12-22 18:48:37](https://github.com/leanprover-community/mathlib/commit/12ee59f)
feat(data/{finset,multiset}/locally_finite): When an `Icc` is a singleton, cardinality generalization ([#10925](https://github.com/leanprover-community/mathlib/pull/10925))
This proves `Icc a b = {c} ↔ a = c ∧ b = c` for sets and finsets, gets rid of the `a ≤ b` assumption in `card_Ico_eq_card_Icc_sub_one` and friends and proves them for multisets.
#### Estimated changes
Modified src/data/finset/interval.lean

Modified src/data/finset/locally_finite.lean
- \+ *lemma* Icc_eq_singleton_iff
- \+/\- *lemma* card_Ico_eq_card_Icc_sub_one
- \+/\- *lemma* card_Ioc_eq_card_Icc_sub_one
- \+/\- *lemma* card_Ioo_eq_card_Ico_sub_one
- \+/\- *lemma* card_Ioo_eq_card_Icc_sub_two
- \+/\- *lemma* card_Ico_eq_card_Icc_sub_one
- \+/\- *lemma* card_Ioc_eq_card_Icc_sub_one
- \+/\- *lemma* card_Ioo_eq_card_Ico_sub_one
- \+/\- *lemma* card_Ioo_eq_card_Icc_sub_two

Modified src/data/multiset/locally_finite.lean
- \+ *lemma* card_Ico_eq_card_Icc_sub_one
- \+ *lemma* card_Ioc_eq_card_Icc_sub_one
- \+ *lemma* card_Ioo_eq_card_Ico_sub_one
- \+ *lemma* card_Ioo_eq_card_Icc_sub_two

Modified src/data/set/intervals/basic.lean
- \+ *lemma* Icc_eq_singleton_iff



## [2021-12-22 18:07:18](https://github.com/leanprover-community/mathlib/commit/da07a99)
feat(ring_theory/tensor_product): Range of `tensor_product.product_map` ([#10882](https://github.com/leanprover-community/mathlib/pull/10882))
This PR proves `(product_map f g).range = f.range ⊔ g.range`.
#### Estimated changes
Modified src/ring_theory/tensor_product.lean
- \+ *lemma* map_range
- \+ *lemma* product_map_range



## [2021-12-22 16:18:16](https://github.com/leanprover-community/mathlib/commit/dda469d)
chore(analysis/normed_space/exponential + logic/function/iterate): fix typos in doc-strings ([#10968](https://github.com/leanprover-community/mathlib/pull/10968))
One `m` was missing in 3 different places.
#### Estimated changes
Modified src/analysis/normed_space/exponential.lean

Modified src/logic/function/iterate.lean



## [2021-12-22 14:28:32](https://github.com/leanprover-community/mathlib/commit/7ca68f8)
chore(*): fix some doc ([#10966](https://github.com/leanprover-community/mathlib/pull/10966))
#### Estimated changes
Modified src/data/nat/factorial/basic.lean

Modified src/ring_theory/polynomial/pochhammer.lean



## [2021-12-22 12:04:48](https://github.com/leanprover-community/mathlib/commit/af683b1)
feat(topology/tietze_extension): Tietze extension theorem ([#10701](https://github.com/leanprover-community/mathlib/pull/10701))
#### Estimated changes
Created src/data/set/intervals/monotone.lean
- \+ *lemma* strict_mono_of_odd_strict_mono_on_nonneg
- \+ *lemma* monotone_of_odd_of_monotone_on_nonneg
- \+ *def* order_iso_Ioo_neg_one_one

Modified src/order/hom/basic.lean
- \+ *def* strict_mono.order_iso_of_right_inverse

Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* norm_comp_continuous_le

Created src/topology/tietze_extension.lean
- \+ *lemma* tietze_extension_step
- \+ *lemma* exists_extension_norm_eq_of_closed_embedding'
- \+ *lemma* exists_extension_norm_eq_of_closed_embedding
- \+ *lemma* exists_norm_eq_restrict_eq_of_closed
- \+ *lemma* exists_extension_forall_mem_Icc_of_closed_embedding
- \+ *lemma* exists_extension_forall_exists_le_ge_of_closed_embedding
- \+ *lemma* exists_extension_forall_mem_of_closed_embedding
- \+ *lemma* exists_forall_mem_restrict_eq_of_closed
- \+ *lemma* exists_extension_forall_mem_of_closed_embedding
- \+ *lemma* exists_extension_of_closed_embedding
- \+ *lemma* exists_restrict_eq_forall_mem_of_closed
- \+ *lemma* exists_restrict_eq_of_closed

Modified src/topology/urysohns_bounded.lean



## [2021-12-21 23:32:37](https://github.com/leanprover-community/mathlib/commit/fc66d88)
refactor(ring_theory/derivation): use weaker TC assumptions ([#10952](https://github.com/leanprover-community/mathlib/pull/10952))
Don't assume `[add_cancel_comm_monoid M]`, add `map_one_eq_zero` as an axiom instead. Add a constructor `derivation.mk'` that deduces `map_one_eq_zero` from `leibniz`.
Also generalize `smul`/`module` instances.
#### Estimated changes
Modified src/geometry/manifold/algebra/left_invariant_derivation.lean

Modified src/geometry/manifold/derivation_bundle.lean

Modified src/ring_theory/derivation.lean
- \+/\- *lemma* mk_coe
- \+/\- *lemma* map_one_eq_zero
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul_linear_map
- \+/\- *lemma* smul_apply
- \+ *lemma* coe_mk'
- \+ *lemma* coe_mk'_linear_map
- \+/\- *lemma* mk_coe
- \+/\- *lemma* map_one_eq_zero
- \- *lemma* coe_Rsmul
- \- *lemma* coe_Rsmul_linear_map
- \- *lemma* Rsmul_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul_linear_map
- \+/\- *lemma* smul_apply
- \+ *def* mk'



## [2021-12-21 19:23:31](https://github.com/leanprover-community/mathlib/commit/55f575f)
feat(linear_algebra/quadratic_form/complex): all non-degenerate quadratic forms over ℂ are equivalent ([#10951](https://github.com/leanprover-community/mathlib/pull/10951))
#### Estimated changes
Modified src/linear_algebra/quadratic_form/complex.lean
- \+ *theorem* complex_equivalent



## [2021-12-21 18:06:48](https://github.com/leanprover-community/mathlib/commit/b434a0d)
feat(data/nat/prime): `prime.dvd_prod_iff`; golf `mem_list_primes_of_dvd_prod` ([#10624](https://github.com/leanprover-community/mathlib/pull/10624))
Adds a generalisation of `prime.dvd_mul`: prime `p` divides the product of `L : list ℕ` iff it divides some `a ∈ L`.   The `.mp` direction of this lemma is the second part of Theorem 1.9 in Apostol (1976) Introduction to Analytic Number Theory.
Also adds the converse `prime.not_dvd_prod`, and uses `dvd_prod_iff` to golf the proof of `mem_list_primes_of_dvd_prod`.
#### Estimated changes
Modified src/algebra/big_operators/associated.lean
- \+ *lemma* prime.dvd_prod_iff

Modified src/data/nat/prime.lean
- \+ *lemma* prime.dvd_prod_iff
- \+ *lemma* prime.not_dvd_prod



## [2021-12-21 16:21:11](https://github.com/leanprover-community/mathlib/commit/ca554be)
chore(group_theory/quotient_group): make pow definitionally equal ([#10833](https://github.com/leanprover-community/mathlib/pull/10833))
Motivated by a TODO comment.
#### Estimated changes
Modified src/group_theory/congruence.lean

Modified src/group_theory/quotient_group.lean
- \+/\- *lemma* coe_div
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_zpow
- \+/\- *lemma* coe_div
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_zpow



## [2021-12-21 16:21:10](https://github.com/leanprover-community/mathlib/commit/cea1988)
feat(data/finsupp/basic): add lemma `disjoint_prod_add` ([#10799](https://github.com/leanprover-community/mathlib/pull/10799))
For disjoint finsupps `f1` and `f2`, and function `g`, the product of the products of `g` over `f1` and `f2` equals the product of `g` over `f1 + f2`
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* prod_add_index_of_disjoint



## [2021-12-21 15:17:17](https://github.com/leanprover-community/mathlib/commit/4aa7ac6)
feat(data/mv_polynomial): add `mv_polynomial.linear_map_ext` ([#10945](https://github.com/leanprover-community/mathlib/pull/10945))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* linear_map_ext



## [2021-12-21 12:42:47](https://github.com/leanprover-community/mathlib/commit/8dafccc)
chore(data/nat/digits): Eliminate `finish` ([#10947](https://github.com/leanprover-community/mathlib/pull/10947))
Removing uses of finish, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/data/nat/digits.lean



## [2021-12-21 12:42:46](https://github.com/leanprover-community/mathlib/commit/7e48e35)
feat(algebra/module/submodule_lattice, linear_algebra/projection): two lemmas about `is_compl` ([#10709](https://github.com/leanprover-community/mathlib/pull/10709))
#### Estimated changes
Modified src/algebra/module/submodule_lattice.lean
- \+ *lemma* eq_zero_of_coe_mem_of_disjoint
- \+ *theorem* disjoint_def
- \+ *theorem* disjoint_def'

Modified src/linear_algebra/basic.lean
- \- *theorem* disjoint_def
- \- *theorem* disjoint_def'

Modified src/linear_algebra/prod.lean
- \+ *def* prod_comm

Modified src/linear_algebra/projection.lean
- \+ *lemma* prod_comm_trans_prod_equiv_of_is_compl
- \+ *lemma* linear_proj_add_linear_proj_of_is_compl_eq_self



## [2021-12-21 12:42:45](https://github.com/leanprover-community/mathlib/commit/a6b2f94)
refactor(linear_algebra/sesquilinear_form): Use similar definition as used in `bilinear_map` ([#10443](https://github.com/leanprover-community/mathlib/pull/10443))
Define sesquilinear forms as `M →ₗ[R] M →ₛₗ[I] R`.
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+/\- *def* sesq_form_of_inner
- \+/\- *def* sesq_form_of_inner

Modified src/linear_algebra/sesquilinear_form.lean
- \+ *lemma* is_ortho_def
- \+ *lemma* is_ortho_zero_left
- \+ *lemma* is_ortho_zero_right
- \+ *lemma* ortho_smul_left
- \+ *lemma* ortho_smul_right
- \+/\- *lemma* eq_zero
- \+/\- *lemma* ortho_comm
- \+/\- *lemma* is_refl
- \+/\- *lemma* ortho_comm
- \+/\- *lemma* self_eq_zero
- \+/\- *lemma* neg
- \+/\- *lemma* is_refl
- \+/\- *lemma* ortho_comm
- \- *lemma* add_left
- \- *lemma* smul_left
- \- *lemma* add_right
- \- *lemma* smul_right
- \- *lemma* zero_left
- \- *lemma* zero_right
- \- *lemma* neg_left
- \- *lemma* neg_right
- \- *lemma* sub_left
- \- *lemma* sub_right
- \- *lemma* ext
- \- *lemma* ortho_zero
- \- *lemma* sum_left
- \- *lemma* sum_right
- \- *lemma* comp_left_comp_right
- \- *lemma* comp_right_comp_left
- \- *lemma* comp_comp
- \- *lemma* comp_apply
- \- *lemma* comp_left_apply
- \- *lemma* comp_right_apply
- \- *lemma* comp_injective
- \+/\- *lemma* eq_zero
- \+/\- *lemma* ortho_comm
- \+/\- *lemma* is_refl
- \+/\- *lemma* ortho_comm
- \+/\- *lemma* self_eq_zero
- \+/\- *lemma* neg
- \+/\- *lemma* is_refl
- \+/\- *lemma* ortho_comm
- \- *theorem* ortho_smul_left
- \- *theorem* ortho_smul_right
- \+/\- *def* is_ortho
- \+/\- *def* is_refl
- \+/\- *def* is_symm
- \+/\- *def* is_alt
- \+/\- *def* is_ortho
- \- *def* linear_map_left
- \- *def* add_monoid_hom_right
- \- *def* comp
- \- *def* comp_left
- \- *def* comp_right
- \+/\- *def* is_refl
- \+/\- *def* is_symm
- \+/\- *def* is_alt



## [2021-12-21 10:53:02](https://github.com/leanprover-community/mathlib/commit/d565373)
feat(order/galois_connection, linear_algebra/basic): `x ∈ R ∙ y` is a transitive relation ([#10943](https://github.com/leanprover-community/mathlib/pull/10943))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* subset_span_trans
- \+ *lemma* mem_span_singleton_trans

Modified src/order/galois_connection.lean
- \+ *lemma* le_u_l_trans
- \+ *lemma* l_u_le_trans



## [2021-12-21 07:22:28](https://github.com/leanprover-community/mathlib/commit/2ceda78)
feat(order/monovary): Monovariance of a pair of functions. ([#10890](https://github.com/leanprover-community/mathlib/pull/10890))
`f` monovaries with `g` if `g i < g j → f i ≤ f j`. `f` antivaries with `g` if `g i < g j → f j ≤ f i`.
This is a way to talk about functions being monotone together, without needing an order on the index type.
#### Estimated changes
Modified src/order/monotone.lean
- \+ *lemma* monotone_iff_forall_lt
- \+ *lemma* antitone_iff_forall_lt
- \+ *lemma* monotone_on_iff_forall_lt
- \+ *lemma* antitone_on_iff_forall_lt
- \+ *lemma* monotone_on.reflect_lt
- \+ *lemma* antitone_on.reflect_lt

Created src/order/monovary.lean
- \+ *lemma* monovary_on_univ
- \+ *lemma* antivary_on_univ
- \+ *lemma* monovary_const_left
- \+ *lemma* antivary_const_left
- \+ *lemma* monovary_const_right
- \+ *lemma* antivary_const_right
- \+ *lemma* monovary_self
- \+ *lemma* monovary_on_self
- \+ *lemma* subsingleton.monovary
- \+ *lemma* subsingleton.antivary
- \+ *lemma* subsingleton.monovary_on
- \+ *lemma* subsingleton.antivary_on
- \+ *lemma* monovary_on_const_left
- \+ *lemma* antivary_on_const_left
- \+ *lemma* monovary_on_const_right
- \+ *lemma* antivary_on_const_right
- \+ *lemma* monovary.comp_right
- \+ *lemma* antivary.comp_right
- \+ *lemma* monovary.dual
- \+ *lemma* antivary.dual
- \+ *lemma* monovary.dual_left
- \+ *lemma* antivary.dual_left
- \+ *lemma* monovary.dual_right
- \+ *lemma* antivary.dual_right
- \+ *lemma* monovary_on.dual
- \+ *lemma* antivary_on.dual
- \+ *lemma* monovary_on.dual_left
- \+ *lemma* antivary_on.dual_left
- \+ *lemma* monovary_on.dual_right
- \+ *lemma* antivary_on.dual_right
- \+ *lemma* monovary_id_iff
- \+ *lemma* antivary_id_iff
- \+ *lemma* monovary_on_id_iff
- \+ *lemma* antivary_on_id_iff
- \+ *def* monovary
- \+ *def* antivary
- \+ *def* monovary_on
- \+ *def* antivary_on



## [2021-12-21 01:43:24](https://github.com/leanprover-community/mathlib/commit/d145e8e)
chore(combinatorics/simple_graph/basic): Golf and cleanup ([#10942](https://github.com/leanprover-community/mathlib/pull/10942))
This kills a few `simp` and fixes typos.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* common_neighbors_subset_neighbor_set_left
- \+ *lemma* common_neighbors_subset_neighbor_set_right
- \- *lemma* common_neighbors_subset_neighbor_set



## [2021-12-20 23:36:13](https://github.com/leanprover-community/mathlib/commit/5ac4cd3)
feat(analysis/special_functions/non_integrable): examples of non-integrable functions ([#10788](https://github.com/leanprover-community/mathlib/pull/10788))
#### Estimated changes
Modified src/analysis/calculus/fderiv_measurable.lean
- \+ *lemma* ae_measurable_deriv

Created src/analysis/special_functions/non_integrable.lean
- \+ *lemma* not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_filter
- \+ *lemma* not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_within_diff_singleton
- \+ *lemma* not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_punctured
- \+ *lemma* not_interval_integrable_of_sub_inv_is_O_punctured
- \+ *lemma* interval_integrable_sub_inv_iff
- \+ *lemma* interval_integrable_inv_iff

Modified src/data/set/intervals/unordered_interval.lean
- \+ *lemma* interval_oc_subset_interval_oc_of_interval_subset_interval
- \+ *lemma* interval_oc_swap

Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* mono_fun
- \+ *lemma* mono_fun'
- \+ *lemma* norm_integral_min_max
- \+/\- *lemma* norm_integral_eq_norm_integral_Ioc
- \+ *lemma* abs_integral_eq_abs_integral_interval_oc
- \+ *lemma* abs_integral_mono_interval
- \+/\- *lemma* norm_integral_eq_norm_integral_Ioc

Modified src/order/filter/basic.lean

Modified src/order/filter/interval.lean
- \+ *lemma* tendsto.interval

Modified src/topology/continuous_on.lean
- \+/\- *lemma* diff_mem_nhds_within_compl
- \+ *lemma* diff_mem_nhds_within_diff
- \+/\- *lemma* diff_mem_nhds_within_compl



## [2021-12-20 21:49:20](https://github.com/leanprover-community/mathlib/commit/c88943f)
feat(algebra/algebra/subalgebra): define the center of a (unital) algebra ([#10910](https://github.com/leanprover-community/mathlib/pull/10910))
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* _root_.set.algebra_map_mem_center
- \+ *lemma* coe_center
- \+ *lemma* center_to_subsemiring
- \+ *lemma* center_to_subring
- \+ *lemma* center_eq_top
- \+ *lemma* mem_center_iff
- \+ *def* center



## [2021-12-20 21:49:18](https://github.com/leanprover-community/mathlib/commit/3b6bd99)
chore(data/finset/prod): eliminate `finish` ([#10904](https://github.com/leanprover-community/mathlib/pull/10904))
Removing uses of finish, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/data/finset/prod.lean



## [2021-12-20 20:42:22](https://github.com/leanprover-community/mathlib/commit/ed250f7)
feat(topology/[path_]connected): add random [path-]connectedness lemmas ([#10932](https://github.com/leanprover-community/mathlib/pull/10932))
From sphere-eversion
#### Estimated changes
Modified src/topology/connected.lean
- \+ *lemma* preconnected_space_iff_connected_component
- \+ *lemma* preconnected_space.connected_component_eq_univ

Modified src/topology/path_connected.lean
- \+ *lemma* is_path_connected.is_connected



## [2021-12-20 19:47:57](https://github.com/leanprover-community/mathlib/commit/7555ea7)
feat(ring_theory/integral_closure): Supremum of integral subalgebras ([#10935](https://github.com/leanprover-community/mathlib/pull/10935))
The supremum of integral subalgebras is integral.
#### Estimated changes
Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_integral_sup



## [2021-12-20 19:47:56](https://github.com/leanprover-community/mathlib/commit/5dd0ede)
refactor(algebra/category/CommRing/constructions): Squeeze a slow simp ([#10934](https://github.com/leanprover-community/mathlib/pull/10934))
`prod_fan_is_limit` was causing timeouts on CI for another PR, so I squeezed one of the simps.
#### Estimated changes
Modified src/algebra/category/CommRing/constructions.lean



## [2021-12-20 18:57:10](https://github.com/leanprover-community/mathlib/commit/082665e)
feat(group_theory/index): relindex_eq_zero_of_le_right ([#10928](https://github.com/leanprover-community/mathlib/pull/10928))
If H has infinite index in K, then so does any L ≥ K.
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* relindex_eq_zero_of_le_right



## [2021-12-20 16:29:56](https://github.com/leanprover-community/mathlib/commit/d910e83)
chore(*): ensure all open_locales work without any open namespaces ([#10913](https://github.com/leanprover-community/mathlib/pull/10913))
Inspired by [#10905](https://github.com/leanprover-community/mathlib/pull/10905) we clean up the localized notation in all locales by using the full names of declarations, this should mean that `open_locale blah` should almost never error.
The cases I'm aware of where this doesn't hold still are the locales:
- `witt` which hard codes the variable name `p`, if there is no `p` in context this will fail
- `list.func` and `topological_space` opening `list.func` breaks the notation in `topological_space` due to ``notation as `{` m ` ↦ ` a `}` := list.func.set a as m`` in `list.func` and ``localized "notation `𝓝[≠] ` x:100 := nhds_within x {x}ᶜ" in topological_space``
- likewise for `parser` and `kronecker` due to ``localized "infix ` ⊗ₖ `:100 := matrix.kronecker_map (*)" in kronecker``
But we don't fix these in this PR.
There may be others instances like this too as these errors can depend on the ordering chosen and  I didn't check them all.
A very basic script to check this sort of thing is at https://github.com/leanprover-community/mathlib/tree/alexjbest/check_localized
#### Estimated changes
Modified src/category_theory/types.lean

Modified src/data/nat/count.lean

Modified src/data/vector3.lean

Modified src/dynamics/omega_limit.lean

Modified src/linear_algebra/special_linear_group.lean

Modified src/number_theory/arithmetic_function.lean

Modified src/number_theory/dioph.lean

Modified src/number_theory/modular.lean



## [2021-12-20 16:29:55](https://github.com/leanprover-community/mathlib/commit/d14ac1f)
feat(*) : added missing lemma for pointwise smul of  submonoid, add_subgroup, add_submonoid, subsemiring, and semiring. ([#10908](https://github.com/leanprover-community/mathlib/pull/10908))
#### Estimated changes
Modified src/group_theory/subgroup/pointwise.lean
- \+ *lemma* mem_smul_pointwise_iff_exists
- \+ *lemma* mem_smul_pointwise_iff_exists

Modified src/group_theory/submonoid/pointwise.lean
- \+ *lemma* mem_smul_pointwise_iff_exists
- \+ *lemma* mem_smul_pointwise_iff_exists

Modified src/ring_theory/subring/pointwise.lean
- \+ *lemma* mem_smul_pointwise_iff_exists

Modified src/ring_theory/subsemiring/pointwise.lean
- \+ *lemma* mem_smul_pointwise_iff_exists



## [2021-12-20 16:29:54](https://github.com/leanprover-community/mathlib/commit/c2debc4)
refactor(combinatorics/configuration): Implicit arguments for `nondegenerate.eq_or_eq` ([#10885](https://github.com/leanprover-community/mathlib/pull/10885))
The arguments `p₁`, `p₂`, `l₁`, `l₂` can be implicit, since they can be inferred from `p₁ ∈ l₁`, `p₂ ∈ l₁`, `p₁ ∈ l₂`, `p₂ ∈ l₂`.
#### Estimated changes
Modified src/combinatorics/configuration.lean



## [2021-12-20 15:51:29](https://github.com/leanprover-community/mathlib/commit/b9fbef8)
feat(tactic/observe): have a claim proved by library_search under the hood ([#10878](https://github.com/leanprover-community/mathlib/pull/10878))
#### Estimated changes
Modified scripts/lint-style.py

Created src/tactic/observe.lean

Created test/observe.lean



## [2021-12-20 13:27:04](https://github.com/leanprover-community/mathlib/commit/ab654e5)
feat(topology/sober): Specialization & generic points & sober spaces ([#10914](https://github.com/leanprover-community/mathlib/pull/10914))
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* is_closed.mem_iff_closure_subset

Modified src/topology/maps.lean
- \+ *lemma* closed_embedding.closure_image_eq

Modified src/topology/separation.lean
- \+ *lemma* indistinguishable.eq
- \+ *lemma* is_preirreducible_iff_subsingleton
- \+ *lemma* is_irreducible_iff_singleton

Created src/topology/sober.lean
- \+ *lemma* specializes_def
- \+ *lemma* specializes_iff_closure_subset
- \+ *lemma* specializes_rfl
- \+ *lemma* specializes_refl
- \+ *lemma* specializes.trans
- \+ *lemma* specializes_iff_forall_closed
- \+ *lemma* specializes_iff_forall_open
- \+ *lemma* indistinguishable_iff_specializes_and
- \+ *lemma* specializes_antisymm
- \+ *lemma* specializes.map
- \+ *lemma* continuous_map.map_specialization
- \+ *lemma* specializes.eq
- \+ *lemma* specializes_iff_eq
- \+ *lemma* specialization_order.monotone_of_continuous
- \+ *lemma* is_generic_point_def
- \+ *lemma* is_generic_point.def
- \+ *lemma* is_generic_point_closure
- \+ *lemma* is_generic_point.specializes
- \+ *lemma* is_generic_point.mem
- \+ *lemma* is_generic_point.is_closed
- \+ *lemma* is_generic_point.is_irreducible
- \+ *lemma* is_generic_point.eq
- \+ *lemma* is_generic_point.mem_open_set_iff
- \+ *lemma* is_generic_point.disjoint_iff
- \+ *lemma* is_generic_point.mem_closed_set_iff
- \+ *lemma* is_generic_point.image
- \+ *lemma* is_irreducible.generic_point_spec
- \+ *lemma* is_irreducible.generic_point_closure_eq
- \+ *lemma* generic_point_spec
- \+ *lemma* generic_point_closure
- \+ *lemma* generic_point_specializes
- \+ *lemma* closed_embedding.sober
- \+ *lemma* open_embedding.sober
- \+ *lemma* sober_of_open_cover
- \+ *def* specializes
- \+ *def* specialization_preorder
- \+ *def* specialization_order
- \+ *def* is_generic_point
- \+ *def* is_irreducible.generic_point
- \+ *def* generic_point
- \+ *def* irreducible_set_equiv_points

Modified src/topology/subset_properties.lean
- \+ *lemma* is_preirreducible_of_subsingleton
- \+ *lemma* irreducible_space.is_irreducible_univ
- \+ *lemma* subset_closure_inter_of_is_preirreducible_of_is_open
- \+ *lemma* is_preirreducible.subset_irreducible
- \+ *lemma* is_preirreducible.open_subset
- \+ *lemma* is_preirreducible.interior
- \+ *lemma* is_preirreducible.preimage



## [2021-12-20 13:27:01](https://github.com/leanprover-community/mathlib/commit/e473898)
feat(category_theory/glue_data): Some more API for glue_data ([#10881](https://github.com/leanprover-community/mathlib/pull/10881))
#### Estimated changes
Modified src/category_theory/glue_data.lean
- \+ *lemma* types_π_surjective
- \+ *lemma* types_ι_jointly_surjective
- \+ *lemma* has_colimit_multispan_comp
- \+ *lemma* has_colimit_map_glue_data_diagram
- \+ *lemma* ι_glued_iso_hom
- \+ *lemma* ι_glued_iso_inv
- \+ *lemma* ι_jointly_surjective
- \+ *def* glued_iso
- \+ *def* V_pullback_cone_is_limit_of_map



## [2021-12-20 13:26:57](https://github.com/leanprover-community/mathlib/commit/6cfc8d8)
feat(algebraic_geometry/locally_ringed_space): LocallyRingedSpace is cocomplete. ([#10791](https://github.com/leanprover-community/mathlib/pull/10791))
#### Estimated changes
Modified src/algebraic_geometry/locally_ringed_space.lean

Modified src/algebraic_geometry/locally_ringed_space/has_colimits.lean
- \+ *lemma* image_basic_open_image_preimage
- \+ *lemma* image_basic_open_image_open
- \+ *lemma* is_local_ring_hom_stalk_map_congr
- \+ *def* image_basic_open
- \+ *def* coequalizer
- \+ *def* coequalizer_cofork
- \+ *def* coequalizer_cofork_is_colimit

Modified src/algebraic_geometry/sheafed_space.lean
- \+ *lemma* comp_c_app'
- \+ *lemma* congr_app

Modified src/category_theory/limits/shapes/types.lean
- \+ *lemma* coequalizer_preimage_image_eq_of_preimage_eq

Modified src/ring_theory/ideal/local_ring.lean
- \+ *lemma* _root_.ring_hom.domain_local_ring
- \+ *lemma* is_local_ring_hom_of_comp



## [2021-12-20 11:53:20](https://github.com/leanprover-community/mathlib/commit/b02e2ea)
feat(group_theory/coset): Embeddings of quotients ([#10901](https://github.com/leanprover-community/mathlib/pull/10901))
If `K ≤ L`, then there is an embedding `K ⧸ (H.subgroup_of K) ↪ L ⧸ (H.subgroup_of L)`. Golfed from [#9545](https://github.com/leanprover-community/mathlib/pull/9545).
#### Estimated changes
Modified src/group_theory/coset.lean
- \+ *def* quotient_subgroup_of_embedding_of_le



## [2021-12-20 11:53:19](https://github.com/leanprover-community/mathlib/commit/b4961da)
feat(analysis/calculus/{f,}deriv): generalize `has_fderiv_at_filter.is_O_sub_rev` ([#10897](https://github.com/leanprover-community/mathlib/pull/10897))
Also add `has_deriv_at.is_O_sub_rev`
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *theorem* has_deriv_at_filter.is_O_sub_rev
- \+/\- *theorem* has_deriv_at.has_fderiv_at_equiv
- \+/\- *theorem* has_deriv_at.has_fderiv_at_equiv

Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* has_fderiv_at_filter.is_O_sub_rev
- \+/\- *lemma* has_fderiv_at_filter.is_O_sub_rev



## [2021-12-20 10:07:40](https://github.com/leanprover-community/mathlib/commit/bcf20b0)
feat(combinatorics/simple_graph/matching): is_matching iff all degrees = 1 ([#10864](https://github.com/leanprover-community/mathlib/pull/10864))
#### Estimated changes
Modified src/combinatorics/simple_graph/matching.lean
- \+ *lemma* is_matching_iff_forall_degree

Modified src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* finset_card_neighbor_set_eq_degree
- \+ *lemma* degree_eq_one_iff_unique_adj



## [2021-12-20 10:07:38](https://github.com/leanprover-community/mathlib/commit/1929025)
feat(ring_theory/polynomial/cyclotomic): generalize a few results to domains ([#10741](https://github.com/leanprover-community/mathlib/pull/10741))
Primarily for flt-regular
#### Estimated changes
Modified src/data/multiset/basic.lean

Modified src/data/polynomial/degree/definitions.lean
- \+/\- *lemma* degree_X_add_C
- \+/\- *lemma* degree_X_sub_C
- \+/\- *lemma* degree_X_sub_C
- \+/\- *lemma* degree_X_add_C

Modified src/data/polynomial/field_division.lean
- \+/\- *lemma* prod_multiset_root_eq_finset_root
- \+/\- *lemma* roots_C_mul
- \+/\- *lemma* roots_normalize
- \+/\- *lemma* prod_multiset_root_eq_finset_root
- \+/\- *lemma* roots_C_mul
- \+/\- *lemma* roots_normalize

Modified src/field_theory/splitting_field.lean
- \- *lemma* prod_multiset_X_sub_C_of_monic_of_roots_card_eq_of_field
- \- *lemma* C_leading_coeff_mul_prod_multiset_X_sub_C_of_field

Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+/\- *lemma* X_pow_sub_one_eq_prod
- \+/\- *lemma* prod_cyclotomic'_eq_X_pow_sub_one
- \+/\- *lemma* cyclotomic'_eq_X_pow_sub_one_div
- \+/\- *lemma* int_coeff_of_cyclotomic'
- \+/\- *lemma* unique_int_coeff_of_cycl
- \+/\- *lemma* cyclotomic_eq_prod_X_sub_primitive_roots
- \+/\- *lemma* X_pow_sub_one_eq_prod
- \+/\- *lemma* prod_cyclotomic'_eq_X_pow_sub_one
- \+/\- *lemma* cyclotomic'_eq_X_pow_sub_one_div
- \+/\- *lemma* int_coeff_of_cyclotomic'
- \+/\- *lemma* unique_int_coeff_of_cycl
- \+/\- *lemma* cyclotomic_eq_prod_X_sub_primitive_roots

Modified src/ring_theory/roots_of_unity.lean



## [2021-12-20 09:01:19](https://github.com/leanprover-community/mathlib/commit/5a79047)
feat(group_theory/index): `relindex_eq_zero_of_le_left` ([#10902](https://github.com/leanprover-community/mathlib/pull/10902))
If `K` has infinite index in `L`, then so does any `H ≤ K`.
The `right`-version is forthcoming.
Making the subgroups explicit in `relindex_mul_relindex` makes rewriting much easier (both in this situation, and in others).
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* relindex_eq_zero_of_le_left



## [2021-12-20 09:01:18](https://github.com/leanprover-community/mathlib/commit/5c05ca2)
feat(ring_theory/integral_closure): `is_field_iff_is_field` ([#10875](https://github.com/leanprover-community/mathlib/pull/10875))
If `R/S` is an integral extension, then `R` is a field if and only if `S` is a field. One direction was already in mathlib, and this PR proves the converse direction.
#### Estimated changes
Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_field_of_is_integral_of_is_field'
- \+ *lemma* is_integral.is_field_iff_is_field



## [2021-12-20 09:01:16](https://github.com/leanprover-community/mathlib/commit/d5de8ea)
feat(data/polynomial): add some simp attributes and commuted versions of coeff_mul_X_pow ([#10868](https://github.com/leanprover-community/mathlib/pull/10868))
I couldn't find these before and accidentally rewrote them from scratch, I think part of the reason is that I would have expected all of these vesions to be simp lemmas, so we add some more versions of these lemmas and tag everything as simp.
From flt-regular
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *lemma* commute_X_pow

Modified src/data/polynomial/coeff.lean
- \+ *lemma* coeff_X_pow_mul'
- \+ *theorem* coeff_X_pow_mul
- \+ *theorem* coeff_X_mul



## [2021-12-20 07:48:27](https://github.com/leanprover-community/mathlib/commit/ade581e)
feat(algebraic_geometry): Open immersions of locally ringed spaces have pullbacks ([#10917](https://github.com/leanprover-community/mathlib/pull/10917))
#### Estimated changes
Modified src/algebraic_geometry/locally_ringed_space.lean
- \+ *lemma* comp_val
- \+ *def* of_restrict

Modified src/algebraic_geometry/open_immersion.lean
- \+ *lemma* pullback_snd_is_iso_of_range_subset
- \+ *lemma* lift_fac
- \+ *lemma* lift_uniq
- \+ *lemma* lift_range
- \+ *def* pullback_cone_of_left
- \+ *def* pullback_cone_of_left_is_limit
- \+ *def* lift

Modified src/category_theory/reflects_isomorphisms.lean



## [2021-12-20 05:51:57](https://github.com/leanprover-community/mathlib/commit/093aef5)
feat(order/monotone): Functions from/to subsingletons are monotone ([#10903](https://github.com/leanprover-community/mathlib/pull/10903))
A few really trivial results about monotonicity/antitonicity of `f : α → β` where `subsingleton α` or `subsingleton β`.
Also fixes the markdown heading levels in this file
#### Estimated changes
Modified src/order/monotone.lean
- \+ *lemma* monotone'
- \+ *lemma* antitone'



## [2021-12-20 04:47:45](https://github.com/leanprover-community/mathlib/commit/1067556)
refactor(data/polynomial/eval): Golf `hom_eval₂` ([#10920](https://github.com/leanprover-community/mathlib/pull/10920))
Here's a much easier proof of `hom_eval₂`.
#### Estimated changes
Modified src/data/polynomial/eval.lean



## [2021-12-20 01:54:00](https://github.com/leanprover-community/mathlib/commit/c40c701)
feat(docs/references) : Added reference for [#10791](https://github.com/leanprover-community/mathlib/pull/10791) ([#10915](https://github.com/leanprover-community/mathlib/pull/10915))
#### Estimated changes
Modified docs/references.bib



## [2021-12-20 01:53:58](https://github.com/leanprover-community/mathlib/commit/9cbd828)
feat(data/finset/basic): add image_congr ([#10911](https://github.com/leanprover-community/mathlib/pull/10911))
Add `finset.image_congr`
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* image_congr



## [2021-12-20 01:53:57](https://github.com/leanprover-community/mathlib/commit/f7b24fa)
refactor(ring_theory/tensor_product): Speed up slow proofs ([#10883](https://github.com/leanprover-community/mathlib/pull/10883))
`alg_hom_of_linear_map_tensor_product` was causing timeouts, due to many uses of `simp`. This refactor speeds up the proofs.
#### Estimated changes
Modified src/ring_theory/tensor_product.lean



## [2021-12-20 00:57:04](https://github.com/leanprover-community/mathlib/commit/6ab0f90)
chore(category_theory/filtered): avoid `finish` ([#10918](https://github.com/leanprover-community/mathlib/pull/10918))
Removing uses of finish, as discussed on Zulip (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers).
#### Estimated changes
Modified src/category_theory/filtered.lean



## [2021-12-19 20:49:08](https://github.com/leanprover-community/mathlib/commit/5dd3537)
feat(algebra/algebra/subalgebra): `subalgebra.map` commutes with supremum ([#10899](https://github.com/leanprover-community/mathlib/pull/10899))
This PR proves `(S ⊔ T).map f = S.map f ⊔ T.map f`.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* map_sup



## [2021-12-19 18:51:43](https://github.com/leanprover-community/mathlib/commit/41ced1c)
feat(ring_theory/tensor_product): The tensor product `A ⊗ B` is generated by tensors `a ⊗ₜ b` ([#10900](https://github.com/leanprover-community/mathlib/pull/10900))
The tensor product is generated by tensors, in terms of `algebra.adjoin`. This is an immediate consequence of `span_tmul_eq_top`.
#### Estimated changes
Modified src/ring_theory/tensor_product.lean
- \+ *lemma* adjoin_tmul_eq_top



## [2021-12-19 18:51:42](https://github.com/leanprover-community/mathlib/commit/194bde8)
feat(order/monotone): add `monotone_int_of_le_succ` etc ([#10895](https://github.com/leanprover-community/mathlib/pull/10895))
Also use new lemmas to golf `zpow_strict_mono` and prove `zpow_strict_anti`.
#### Estimated changes
Modified src/algebra/field_power.lean
- \+ *lemma* zpow_strict_anti

Modified src/data/complex/exponential.lean

Modified src/order/monotone.lean
- \+ *lemma* nat.rel_of_forall_rel_succ_of_le_of_lt
- \+ *lemma* nat.rel_of_forall_rel_succ_of_le_of_le
- \+ *lemma* nat.rel_of_forall_rel_succ_of_lt
- \+ *lemma* nat.rel_of_forall_rel_succ_of_le
- \+/\- *lemma* monotone_nat_of_le_succ
- \+/\- *lemma* strict_mono_nat_of_lt_succ
- \+/\- *lemma* strict_anti_nat_of_succ_lt
- \+ *lemma* int.rel_of_forall_rel_succ_of_lt
- \+ *lemma* int.rel_of_forall_rel_succ_of_le
- \+ *lemma* monotone_int_of_le_succ
- \+ *lemma* antitone_int_of_succ_le
- \+ *lemma* strict_mono_int_of_lt_succ
- \+ *lemma* strict_anti_int_of_succ_lt
- \+/\- *lemma* monotone_nat_of_le_succ
- \+/\- *lemma* strict_mono_nat_of_lt_succ
- \+/\- *lemma* strict_anti_nat_of_succ_lt
- \- *lemma* forall_ge_le_of_forall_le_succ

Modified src/order/order_iso_nat.lean



## [2021-12-19 18:51:41](https://github.com/leanprover-community/mathlib/commit/a60ef7c)
feat(data/list/sort): subperm sorted implies sublist ([#10892](https://github.com/leanprover-community/mathlib/pull/10892))
A "sub" version of the lemma directly above.
#### Estimated changes
Modified src/data/list/sort.lean
- \+ *theorem* sublist_of_subperm_of_sorted



## [2021-12-19 18:51:40](https://github.com/leanprover-community/mathlib/commit/faee358)
feat (order/lexicographic):  add API lemmas ([#10887](https://github.com/leanprover-community/mathlib/pull/10887))
#### Estimated changes
Modified src/order/lexicographic.lean
- \+ *lemma* lex_le_iff
- \+ *lemma* lex_lt_iff



## [2021-12-19 18:51:40](https://github.com/leanprover-community/mathlib/commit/45ed9de)
chore(order/complete_lattice): eliminate `finish` ([#10876](https://github.com/leanprover-community/mathlib/pull/10876))
Removing uses of finish, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/order/complete_lattice.lean



## [2021-12-19 17:06:17](https://github.com/leanprover-community/mathlib/commit/68d9b42)
feat(data/list/count): add lemma `list.count_singleton'` ([#10880](https://github.com/leanprover-community/mathlib/pull/10880))
A generalisation of `count_singleton`: `count a [b] = ite (a = b) 1 0`
#### Estimated changes
Modified src/data/list/count.lean
- \+ *lemma* count_singleton'



## [2021-12-19 12:15:00](https://github.com/leanprover-community/mathlib/commit/9e5cbc1)
feat(algebra/group_power/basic): generalize `zpow_neg_one` to `div_inv_monoid` ([#10894](https://github.com/leanprover-community/mathlib/pull/10894))
Drop `zpow_neg_one₀`
#### Estimated changes
Modified src/algebra/field_power.lean

Modified src/algebra/group_power/basic.lean
- \+/\- *theorem* zpow_neg_one
- \+/\- *theorem* zpow_neg_one

Modified src/algebra/group_with_zero/power.lean
- \- *theorem* zpow_neg_one₀

Modified src/analysis/calculus/deriv.lean

Modified src/measure_theory/covering/differentiation.lean



## [2021-12-19 11:16:32](https://github.com/leanprover-community/mathlib/commit/3fc32e3)
feat(analysis/asymptotics): add `is_O.inv_rev`, `is_o.inv_rev` ([#10896](https://github.com/leanprover-community/mathlib/pull/10896))
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+ *theorem* is_O_with.inv_rev
- \+ *theorem* is_O.inv_rev
- \+ *theorem* is_o.inv_rev



## [2021-12-19 10:01:23](https://github.com/leanprover-community/mathlib/commit/7222463)
chore(algebra/iterate_hom): use to_additive to fill missing lemmas ([#10886](https://github.com/leanprover-community/mathlib/pull/10886))
#### Estimated changes
Modified src/algebra/iterate_hom.lean
- \+ *lemma* monoid.End.coe_pow
- \+ *lemma* add_monoid.End.coe_pow
- \+ *theorem* iterate_map_div
- \+/\- *theorem* iterate_map_pow
- \+/\- *theorem* iterate_map_zpow
- \+/\- *theorem* iterate_map_pow
- \+/\- *theorem* iterate_map_zpow
- \- *theorem* iterate_map_sub



## [2021-12-19 02:48:13](https://github.com/leanprover-community/mathlib/commit/a2c3b29)
chore(scripts): update nolints.txt ([#10893](https://github.com/leanprover-community/mathlib/pull/10893))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt



## [2021-12-18 20:11:21](https://github.com/leanprover-community/mathlib/commit/ee17ab3)
refactor(measure_theory/measure/hausdorff): change Hausdorff measure definition at 0 ([#10859](https://github.com/leanprover-community/mathlib/pull/10859))
Currently, our definition of the Hausdorff measure ensures that it has no atom. This differs from the standard definition of the 0-Hausdorff measure, which is the counting measure -- and this convention is better behaved in many respects, for instance in a `d`-dimensional space the `d`-Hausdorff measure is proportional to Lebesgue measure, while currently we only have this for `d > 0`.
This PR refactors the definition of the Hausdorff measure, to conform to the standard definition.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* nonempty_of_nonempty_preimage

Modified src/measure_theory/measure/hausdorff.lean
- \+/\- *lemma* mk_metric_mono
- \+/\- *lemma* le_mk_metric
- \+/\- *lemma* mk_metric_mono
- \+/\- *lemma* le_mk_metric
- \+/\- *lemma* le_hausdorff_measure
- \+/\- *lemma* hausdorff_measure_apply
- \+ *lemma* no_atoms_hausdorff
- \+ *lemma* hausdorff_measure_zero_singleton
- \+ *lemma* one_le_hausdorff_measure_zero_of_nonempty
- \+ *lemma* hausdorff_measure_le_one_of_subsingleton
- \+/\- *lemma* mk_metric_mono
- \+/\- *lemma* le_mk_metric
- \+/\- *lemma* mk_metric_mono
- \+/\- *lemma* le_mk_metric
- \+/\- *lemma* le_hausdorff_measure
- \- *lemma* hausdorff_measure_apply'
- \+/\- *lemma* hausdorff_measure_apply
- \+/\- *theorem* hausdorff_measure_pi_real
- \+/\- *theorem* hausdorff_measure_pi_real

Modified src/topology/metric_space/hausdorff_dimension.lean



## [2021-12-18 20:11:20](https://github.com/leanprover-community/mathlib/commit/289ebe5)
chore(category_theory/monoidal/End): Adding API for monoidal functors into `C ⥤ C` ([#10841](https://github.com/leanprover-community/mathlib/pull/10841))
Needed for the shift refactor
#### Estimated changes
Modified src/category_theory/functor_category.lean
- \+ *lemma* map_hom_inv_app
- \+ *lemma* map_inv_hom_app

Modified src/category_theory/monoidal/End.lean
- \+ *lemma* μ_hom_inv_app
- \+ *lemma* μ_inv_hom_app
- \+ *lemma* ε_hom_inv_app
- \+ *lemma* ε_inv_hom_app
- \+ *lemma* ε_naturality
- \+ *lemma* ε_inv_naturality
- \+ *lemma* μ_naturality
- \+ *lemma* μ_inv_naturality
- \+ *lemma* μ_naturality₂
- \+ *lemma* μ_naturalityₗ
- \+ *lemma* μ_naturalityᵣ
- \+ *lemma* left_unitality_app
- \+ *lemma* obj_ε_app
- \+ *lemma* obj_ε_inv_app
- \+ *lemma* right_unitality_app
- \+ *lemma* ε_app_obj
- \+ *lemma* ε_inv_app_obj
- \+ *lemma* associativity_app
- \+ *lemma* obj_μ_app
- \+ *lemma* obj_μ_inv_app
- \+ *lemma* obj_zero_map_μ_app
- \+ *lemma* obj_μ_zero_app
- \+/\- *def* tensoring_right_monoidal
- \+ *def* unit_of_tensor_iso_unit
- \+ *def* equiv_of_tensor_iso_unit
- \+/\- *def* tensoring_right_monoidal

Modified src/category_theory/monoidal/functor.lean
- \+/\- *lemma* map_tensor
- \+/\- *lemma* map_left_unitor
- \+/\- *lemma* map_right_unitor
- \+ *lemma* μ_iso_hom
- \+ *lemma* μ_inv_hom_id
- \+ *lemma* μ_hom_inv_id
- \+ *lemma* ε_iso_hom
- \+ *lemma* ε_inv_hom_id
- \+ *lemma* ε_hom_inv_id
- \+/\- *lemma* map_tensor
- \+/\- *lemma* map_left_unitor
- \+/\- *lemma* map_right_unitor
- \+/\- *def* μ_nat_iso
- \+/\- *def* μ_nat_iso

Modified src/category_theory/natural_isomorphism.lean
- \+ *lemma* inv_inv_app



## [2021-12-18 20:11:19](https://github.com/leanprover-community/mathlib/commit/9f1b9bc)
feat(linear_algebra/determinant): more properties of the determinant of linear maps ([#10809](https://github.com/leanprover-community/mathlib/pull/10809))
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* is_unit_det
- \+ *lemma* finite_dimensional_of_det_ne_one
- \+ *lemma* range_lt_top_of_det_eq_zero
- \+ *lemma* bot_lt_ker_of_det_eq_zero
- \+ *lemma* linear_equiv.det_coe_symm

Modified src/linear_algebra/eigenspace.lean

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* is_unit_iff_ker_eq_bot
- \+ *lemma* is_unit_iff_range_eq_top
- \- *lemma* is_unit_iff



## [2021-12-18 20:11:18](https://github.com/leanprover-community/mathlib/commit/0d47369)
feat(topology/metric/hausdorff_distance): more properties of cthickening ([#10808](https://github.com/leanprover-community/mathlib/pull/10808))
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* eventually_closed_ball_subset
- \+ *lemma* bounded_range_of_tendsto

Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* _root_.is_compact.exists_inf_edist_eq_edist
- \+ *lemma* bounded.thickening
- \+ *lemma* mem_cthickening_of_edist_le
- \+ *lemma* mem_cthickening_of_dist_le
- \+ *lemma* bounded.cthickening



## [2021-12-18 18:09:36](https://github.com/leanprover-community/mathlib/commit/a6179f6)
feat(linear_algebra/affine_space/affine_equiv): isomorphism with the units ([#10798](https://github.com/leanprover-community/mathlib/pull/10798))
This adds:
* `affine_equiv.equiv_units_affine_map` (the main point in this PR)
* `affine_map.linear_hom`
* `affine_equiv.linear_hom`
* `simps` configuration for `affine_equiv`. In order to makes `simp` happy, we adjust the order of the implicit variables to all lemmas in this file, so that they match the order of the arguments to `affine_equiv`.
The new definition can be used to majorly golf `homothety_units_mul_hom`
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_equiv.lean
- \- *lemma* linear_vadd_const
- \- *lemma* vadd_const_apply
- \- *lemma* vadd_const_symm_apply
- \- *lemma* linear_const_vadd
- \- *lemma* const_vadd_apply
- \- *lemma* const_vadd_symm_apply
- \+ *def* simps.apply
- \+ *def* simps.symm_apply
- \+ *def* linear_hom
- \+ *def* equiv_units_affine_map

Modified src/linear_algebra/affine_space/affine_map.lean
- \+ *def* linear_hom



## [2021-12-18 18:09:35](https://github.com/leanprover-community/mathlib/commit/2c4e66f)
split(data/finset/*): Split `data.finset.card` and `data.finset.fin` off `data.finset.basic` ([#10796](https://github.com/leanprover-community/mathlib/pull/10796))
This moves stuff from `data.finset.basic` in two new files:
* Stuff about `finset.card` goes into `data.finset.card`
* Stuff about `finset.fin_range` and `finset.attach_fin` goes into `data.finset.fin`. I expect this file to be shortlived as I'm planning on killing `fin_range`.
I reordered lemmas thematically and it appeared that there were two pairs of duplicated lemmas:
* `finset.one_lt_card`, `finset.one_lt_card_iff`. They differ only for binder order.
* `finset.card_union_eq`, `finset.card_disjoint_union`. They are literally the same.
All are used so I will clean up in a later PR.
I'm crediting:
* Microsoft Corporation, Leonardo, Jeremy for 8dbee5b1ca9680a22ffe90751654f51d6852d7f0
* Chris Hughes for [#231](https://github.com/leanprover-community/mathlib/pull/231)
* Scott for [#3319](https://github.com/leanprover-community/mathlib/pull/3319)
#### Estimated changes
Modified src/combinatorics/set_family/compression/uv.lean

Modified src/data/finset/basic.lean
- \+ *lemma* _root_.multiset.to_finset_map
- \- *lemma* card_mk
- \- *lemma* card_mono
- \- *lemma* card_le_one_iff_subset_singleton
- \- *lemma* card_le_one_of_subsingleton
- \- *lemma* exists_ne_of_one_lt_card
- \- *lemma* one_lt_card_iff
- \- *lemma* card_singleton_inter
- \- *lemma* list.card_to_finset
- \- *lemma* fiber_card_ne_zero_iff_mem_image
- \- *lemma* card_map
- \- *lemma* card_subtype
- \- *lemma* card_eq_of_bijective
- \- *lemma* card_eq_succ
- \- *lemma* card_eq_two
- \- *lemma* card_eq_three
- \- *lemma* filter_card_eq
- \- *lemma* card_lt_card
- \- *lemma* card_le_card_of_inj_on
- \- *lemma* exists_ne_map_eq_of_card_lt_of_maps_to
- \- *lemma* le_card_of_inj_on_range
- \- *lemma* strong_induction_eq
- \- *lemma* strong_induction_on_eq
- \- *lemma* case_strong_induction_on
- \- *lemma* strong_downward_induction_eq
- \- *lemma* strong_downward_induction_on_eq
- \- *lemma* card_congr
- \- *lemma* card_union_add_card_inter
- \- *lemma* card_union_le
- \- *lemma* card_union_eq
- \- *lemma* surj_on_of_inj_on_of_card_le
- \- *lemma* inj_on_of_surj_on_of_card_le
- \- *lemma* length_to_list
- \- *lemma* card_sdiff_add_card
- \- *lemma* filter_card_add_filter_neg_card_eq_card
- \- *lemma* exists_intermediate_set
- \- *lemma* exists_smaller_set
- \- *lemma* exists_subset_or_subset_of_two_mul_lt_card
- \- *lemma* fin_range_card
- \- *lemma* mem_fin_range
- \- *lemma* coe_fin_range
- \- *lemma* mem_attach_fin
- \- *lemma* card_attach_fin
- \- *theorem* multiset.to_finset_map
- \- *theorem* card_def
- \- *theorem* card_empty
- \- *theorem* card_le_of_subset
- \- *theorem* card_eq_zero
- \- *theorem* card_pos
- \- *theorem* card_ne_zero_of_mem
- \- *theorem* card_eq_one
- \- *theorem* card_le_one
- \- *theorem* card_le_one_iff
- \- *theorem* one_lt_card
- \- *theorem* card_cons
- \- *theorem* card_insert_of_not_mem
- \- *theorem* card_insert_of_mem
- \- *theorem* card_insert_le
- \- *theorem* card_insert_eq_ite
- \- *theorem* card_singleton
- \- *theorem* card_erase_of_mem
- \- *theorem* card_erase_lt_of_mem
- \- *theorem* card_erase_le
- \- *theorem* pred_card_le_card_erase
- \- *theorem* card_erase_eq_ite
- \- *theorem* card_range
- \- *theorem* card_attach
- \- *theorem* multiset.to_finset_card_le
- \- *theorem* list.to_finset_card_le
- \- *theorem* card_image_le
- \- *theorem* card_image_of_inj_on
- \- *theorem* inj_on_of_card_image_eq
- \- *theorem* card_image_eq_iff_inj_on
- \- *theorem* card_image_of_injective
- \- *theorem* card_filter_le
- \- *theorem* eq_of_subset_of_card_le
- \- *theorem* card_disjoint_union
- \- *theorem* card_sdiff
- \- *theorem* lt_wf
- \- *theorem* to_finset_card_of_nodup
- \- *theorem* to_finset_card_of_nodup
- \- *def* card
- \- *def* strong_induction
- \- *def* strong_induction_on
- \- *def* strong_downward_induction
- \- *def* strong_downward_induction_on
- \- *def* fin_range
- \- *def* attach_fin

Created src/data/finset/card.lean
- \+ *lemma* card_def
- \+ *lemma* card_mk
- \+ *lemma* card_empty
- \+ *lemma* card_le_of_subset
- \+ *lemma* card_mono
- \+ *lemma* card_eq_zero
- \+ *lemma* card_pos
- \+ *lemma* card_ne_zero_of_mem
- \+ *lemma* card_singleton
- \+ *lemma* card_singleton_inter
- \+ *lemma* card_cons
- \+ *lemma* card_insert_of_not_mem
- \+ *lemma* card_insert_of_mem
- \+ *lemma* card_insert_le
- \+ *lemma* card_insert_eq_ite
- \+ *lemma* card_erase_of_mem
- \+ *lemma* card_erase_lt_of_mem
- \+ *lemma* card_erase_le
- \+ *lemma* pred_card_le_card_erase
- \+ *lemma* card_erase_eq_ite
- \+ *lemma* card_range
- \+ *lemma* card_attach
- \+ *lemma* multiset.card_to_finset
- \+ *lemma* multiset.to_finset_card_le
- \+ *lemma* multiset.to_finset_card_of_nodup
- \+ *lemma* list.card_to_finset
- \+ *lemma* list.to_finset_card_le
- \+ *lemma* list.to_finset_card_of_nodup
- \+ *lemma* length_to_list
- \+ *lemma* card_image_le
- \+ *lemma* card_image_of_inj_on
- \+ *lemma* inj_on_of_card_image_eq
- \+ *lemma* card_image_eq_iff_inj_on
- \+ *lemma* card_image_of_injective
- \+ *lemma* fiber_card_ne_zero_iff_mem_image
- \+ *lemma* card_map
- \+ *lemma* card_subtype
- \+ *lemma* card_filter_le
- \+ *lemma* eq_of_subset_of_card_le
- \+ *lemma* filter_card_eq
- \+ *lemma* card_lt_card
- \+ *lemma* card_eq_of_bijective
- \+ *lemma* card_congr
- \+ *lemma* card_le_card_of_inj_on
- \+ *lemma* exists_ne_map_eq_of_card_lt_of_maps_to
- \+ *lemma* le_card_of_inj_on_range
- \+ *lemma* surj_on_of_inj_on_of_card_le
- \+ *lemma* inj_on_of_surj_on_of_card_le
- \+ *lemma* card_union_add_card_inter
- \+ *lemma* card_union_le
- \+ *lemma* card_union_eq
- \+ *lemma* card_disjoint_union
- \+ *lemma* card_sdiff
- \+ *lemma* card_sdiff_add_card
- \+ *lemma* filter_card_add_filter_neg_card_eq_card
- \+ *lemma* exists_intermediate_set
- \+ *lemma* exists_smaller_set
- \+ *lemma* exists_subset_or_subset_of_two_mul_lt_card
- \+ *lemma* card_eq_one
- \+ *lemma* card_le_one
- \+ *lemma* card_le_one_iff
- \+ *lemma* card_le_one_iff_subset_singleton
- \+ *lemma* card_le_one_of_subsingleton
- \+ *lemma* one_lt_card
- \+ *lemma* one_lt_card_iff
- \+ *lemma* exists_ne_of_one_lt_card
- \+ *lemma* card_eq_succ
- \+ *lemma* card_eq_two
- \+ *lemma* card_eq_three
- \+ *lemma* strong_induction_eq
- \+ *lemma* strong_induction_on_eq
- \+ *lemma* case_strong_induction_on
- \+ *lemma* strong_downward_induction_eq
- \+ *lemma* strong_downward_induction_on_eq
- \+ *lemma* lt_wf
- \+ *def* card
- \+ *def* strong_induction
- \+ *def* strong_induction_on
- \+ *def* strong_downward_induction
- \+ *def* strong_downward_induction_on

Created src/data/finset/fin.lean
- \+ *lemma* fin_range_card
- \+ *lemma* mem_fin_range
- \+ *lemma* coe_fin_range
- \+ *lemma* mem_attach_fin
- \+ *lemma* card_attach_fin
- \+ *def* fin_range
- \+ *def* attach_fin

Modified src/data/finset/nat_antidiagonal.lean

Modified src/data/finset/option.lean

Modified src/data/finset/prod.lean

Modified src/data/fintype/basic.lean

Modified src/group_theory/perm/support.lean



## [2021-12-18 18:09:34](https://github.com/leanprover-community/mathlib/commit/fa46ef1)
feat(linear_algebra/affine_space/combination): vsub distributivity lemmas ([#10786](https://github.com/leanprover-community/mathlib/pull/10786))
Add lemmas about weighted sums of `-ᵥ` expressions in terms of
`weighted_vsub_of_point`, `weighted_vsub` and `affine_combination`,
with special cases where the points on one side of the subtractions
are constant, and lemmas about those three functions for constant
points used to prove those special cases.
These were suggested by one of the lemmas in [#10632](https://github.com/leanprover-community/mathlib/pull/10632); the lemma
`affine_basis.vsub_eq_coord_smul_sum` is a very specific case, but
showed up that these distributivity lemmas were missing (and should
follow immediately from
`sum_smul_const_vsub_eq_vsub_affine_combination` in this PR).
#### Estimated changes
Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* weighted_vsub_of_point_apply_const
- \+ *lemma* sum_smul_vsub_eq_weighted_vsub_of_point_sub
- \+ *lemma* sum_smul_vsub_const_eq_weighted_vsub_of_point_sub
- \+ *lemma* sum_smul_const_vsub_eq_sub_weighted_vsub_of_point
- \+ *lemma* weighted_vsub_apply_const
- \+ *lemma* sum_smul_vsub_eq_weighted_vsub_sub
- \+ *lemma* sum_smul_vsub_const_eq_weighted_vsub
- \+ *lemma* sum_smul_const_vsub_eq_neg_weighted_vsub
- \+ *lemma* affine_combination_apply_const
- \+ *lemma* sum_smul_vsub_eq_affine_combination_vsub
- \+ *lemma* sum_smul_vsub_const_eq_affine_combination_vsub
- \+ *lemma* sum_smul_const_vsub_eq_vsub_affine_combination



## [2021-12-18 18:09:32](https://github.com/leanprover-community/mathlib/commit/ecec43a)
feat(algebraic_geometry/open_immersion): Easy results about open immersions. ([#10776](https://github.com/leanprover-community/mathlib/pull/10776))
#### Estimated changes
Modified src/algebraic_geometry/open_immersion.lean
- \+ *lemma* to_SheafedSpace_to_PresheafedSpace
- \+ *lemma* to_SheafedSpace_hom_base
- \+ *lemma* to_SheafedSpace_hom_c
- \+ *lemma* SheafedSpace_to_SheafedSpace
- \+ *lemma* to_LocallyRingedSpace_to_SheafedSpace
- \+ *lemma* to_LocallyRingedSpace_hom_val
- \+ *lemma* LocallyRingedSpace_to_LocallyRingedSpace
- \+ *lemma* of_stalk_iso
- \+ *def* to_SheafedSpace
- \+ *def* to_SheafedSpace_hom
- \+ *def* to_LocallyRingedSpace
- \+ *def* to_LocallyRingedSpace_hom



## [2021-12-18 18:09:31](https://github.com/leanprover-community/mathlib/commit/6e59fbe)
feat(field_theory/splitting_field): generalize some results from field to domain ([#10726](https://github.com/leanprover-community/mathlib/pull/10726))
This PR does a few things generalizing / golfing facts related to polynomials and splitting fields.
- Generalize some results in `data.polynomial.field_division` to division rings
- generalize `C_leading_coeff_mul_prod_multiset_X_sub_C` from a field to a domain
- same for `prod_multiset_X_sub_C_of_monic_of_roots_card_eq`
- add a supporting useful lemma `roots_map_of_injective_card_eq_total_degree` saying that if we already have a full (multi)set of roots over a domain, passing along an injection gives the set of roots of the mapped polynomial
Inspired by needs of flt-regular.
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *theorem* count_map
- \+ *theorem* count_map_eq_count'

Modified src/data/polynomial/field_division.lean
- \+/\- *lemma* is_unit_iff_degree_eq_zero
- \+/\- *lemma* prod_multiset_root_eq_finset_root
- \+/\- *lemma* roots_C_mul
- \+/\- *lemma* roots_normalize
- \+/\- *lemma* is_unit_iff_degree_eq_zero
- \+/\- *lemma* prod_multiset_root_eq_finset_root
- \+/\- *lemma* roots_C_mul
- \+/\- *lemma* roots_normalize

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* le_root_multiplicity_map
- \+ *lemma* count_map_roots
- \+ *lemma* roots_map_of_injective_card_eq_total_degree

Modified src/field_theory/splitting_field.lean
- \+ *lemma* prod_multiset_X_sub_C_of_monic_of_roots_card_eq_of_field
- \+/\- *lemma* prod_multiset_X_sub_C_of_monic_of_roots_card_eq
- \+ *lemma* C_leading_coeff_mul_prod_multiset_X_sub_C_of_field
- \+/\- *lemma* C_leading_coeff_mul_prod_multiset_X_sub_C
- \+/\- *lemma* prod_multiset_X_sub_C_of_monic_of_roots_card_eq
- \+/\- *lemma* C_leading_coeff_mul_prod_multiset_X_sub_C



## [2021-12-18 18:09:30](https://github.com/leanprover-community/mathlib/commit/fec084c)
feat(order/cover): The covering relation ([#10676](https://github.com/leanprover-community/mathlib/pull/10676))
This defines `a ⋖ b` to mean that `a < b` and there is no element in between. It is generally useful, but in particular in the context of polytopes and successor orders.
#### Estimated changes
Modified src/order/atoms.lean
- \+/\- *lemma* eq_bot_or_eq_of_le_atom
- \+/\- *lemma* is_atom.Iic
- \+/\- *lemma* is_atom.of_is_atom_coe_Iic
- \+ *lemma* bot_covers_iff
- \+/\- *lemma* eq_top_or_eq_of_coatom_le
- \+/\- *lemma* is_coatom.Ici
- \+/\- *lemma* is_coatom.of_is_coatom_coe_Ici
- \+ *lemma* covers_top_iff
- \+ *lemma* bot_covers_top
- \+/\- *lemma* eq_bot_or_eq_of_le_atom
- \+/\- *lemma* is_atom.Iic
- \+/\- *lemma* is_atom.of_is_atom_coe_Iic
- \+/\- *lemma* eq_top_or_eq_of_coatom_le
- \+/\- *lemma* is_coatom.Ici
- \+/\- *lemma* is_coatom.of_is_coatom_coe_Ici

Modified src/order/basic.lean
- \+ *lemma* eq_of_le_of_not_lt
- \+ *lemma* eq_of_ge_of_not_gt

Created src/order/cover.lean
- \+ *lemma* covers.lt
- \+ *lemma* not_covers_iff
- \+ *lemma* to_dual_covers_to_dual_iff
- \+ *lemma* not_covers
- \+ *lemma* covers.le
- \+ *lemma* covers.ne'
- \+ *lemma* covers.Ioo_eq
- \+ *lemma* covers.Ico_eq
- \+ *lemma* covers.Ioc_eq
- \+ *lemma* covers.Icc_eq
- \+ *def* covers

Modified src/order/succ_pred.lean
- \+ *lemma* covers_succ_of_nonempty_Ioi
- \+ *lemma* covers_succ
- \+ *lemma* _root_.covers.succ_eq
- \+ *lemma* _root_.covers_iff_succ_eq
- \+ *lemma* pred_covers_of_nonempty_Iio
- \+ *lemma* pred_covers
- \+ *lemma* _root_.covers.pred_eq
- \+ *lemma* _root_.covers_iff_pred_eq
- \+ *lemma* succ_pred_of_nonempty_Iio
- \+ *lemma* pred_succ_of_nonempty_Ioi
- \+ *lemma* succ_pred
- \+ *lemma* pred_succ



## [2021-12-18 16:15:43](https://github.com/leanprover-community/mathlib/commit/011203d)
feat(algebra/group/inj_surj): _pow definitions for surjective too ([#10832](https://github.com/leanprover-community/mathlib/pull/10832))
We already have these three variants for the injective counterparts, added in [#10152](https://github.com/leanprover-community/mathlib/pull/10152).
#### Estimated changes
Modified src/algebra/group/inj_surj.lean



## [2021-12-18 16:15:42](https://github.com/leanprover-community/mathlib/commit/5915254)
feat(data/matrix/rank): rank of a matrix ([#10826](https://github.com/leanprover-community/mathlib/pull/10826))
#### Estimated changes
Modified docs/undergrad.yaml

Created src/data/matrix/rank.lean
- \+ *lemma* rank_one
- \+ *lemma* rank_zero
- \+ *lemma* rank_le_card_width
- \+ *lemma* rank_le_width
- \+ *lemma* rank_mul_le
- \+ *lemma* rank_unit
- \+ *lemma* rank_of_is_unit
- \+ *lemma* rank_eq_finrank_range_to_lin
- \+ *lemma* rank_le_card_height
- \+ *lemma* rank_le_height

Modified src/linear_algebra/matrix/to_lin.lean



## [2021-12-18 16:15:41](https://github.com/leanprover-community/mathlib/commit/915e2b5)
feat(linear_algebra/orientation): add orientation.map ([#10815](https://github.com/leanprover-community/mathlib/pull/10815))
This also adds `alternating_map.dom_lcongr` following the naming established by `finsupp.dom_lcongr`.
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *lemma* dom_lcongr_refl
- \+ *lemma* dom_lcongr_symm
- \+ *lemma* dom_lcongr_trans
- \+/\- *lemma* comp_linear_equiv_eq_zero_iff
- \+/\- *lemma* comp_linear_equiv_eq_zero_iff
- \+ *def* dom_lcongr

Modified src/linear_algebra/orientation.lean
- \+ *lemma* orientation.map_apply
- \+ *lemma* orientation.map_refl
- \+ *lemma* orientation.map_symm
- \+ *def* orientation.map



## [2021-12-18 16:15:40](https://github.com/leanprover-community/mathlib/commit/e70faf3)
feat(ring_theory/prinicipal_ideal_domain): Bézout's lemma for PIDs ([#10810](https://github.com/leanprover-community/mathlib/pull/10810))
#### Estimated changes
Modified docs/undergrad.yaml

Modified src/ring_theory/principal_ideal_domain.lean
- \+ *theorem* gcd_dvd_iff_exists
- \+ *theorem* exists_gcd_eq_mul_add_mul



## [2021-12-18 16:15:39](https://github.com/leanprover-community/mathlib/commit/47c676e)
feat(linear_algebra/affine_space/affine_subspace): affine_subspace.comap ([#10795](https://github.com/leanprover-community/mathlib/pull/10795))
This copies a handful of lemmas from `group_theory/subgroup/basic.lean` to get things started.
#### Estimated changes
Modified src/geometry/euclidean/circumcenter.lean

Modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* coe_injective
- \+ *lemma* coe_map
- \+ *lemma* mem_map
- \+ *lemma* map_id
- \+ *lemma* map_map
- \+ *lemma* coe_comap
- \+ *lemma* mem_comap
- \+ *lemma* comap_mono
- \+ *lemma* comap_top
- \+ *lemma* comap_id
- \+ *lemma* comap_comap
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* gc_map_comap
- \+ *lemma* map_comap_le
- \+ *lemma* le_comap_map
- \+ *lemma* map_sup
- \+ *lemma* map_supr
- \+ *lemma* comap_inf
- \+ *lemma* comap_supr
- \- *lemma* ext
- \- *lemma* map_coe
- \+ *def* comap



## [2021-12-18 16:15:38](https://github.com/leanprover-community/mathlib/commit/00454f2)
feat(topology/algebra/mul_action): add an instance in the presence of `is_central_scalar` ([#10787](https://github.com/leanprover-community/mathlib/pull/10787))
#### Estimated changes
Modified src/topology/algebra/mul_action.lean



## [2021-12-18 16:15:38](https://github.com/leanprover-community/mathlib/commit/5603398)
feat(ring_theory/local_properties): Being finite / of finite type is local. ([#10775](https://github.com/leanprover-community/mathlib/pull/10775))
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* span_eq_top_iff_finite

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* mem_of_span_eq_top_of_smul_pow_mem

Modified src/ring_theory/local_properties.lean
- \+ *lemma* ring_hom.of_localization_span_iff_finite
- \+ *lemma* ring_hom.localization_away_of_localization_preserves
- \+ *lemma* localization_finite
- \+ *lemma* localization_away_map_finite
- \+ *lemma* is_localization.smul_mem_finset_integer_multiple_span
- \+ *lemma* multiple_mem_span_of_mem_localization_span
- \+ *lemma* multiple_mem_adjoin_of_mem_localization_adjoin
- \+ *lemma* finite_of_localization_span
- \+ *lemma* localization_finite_type
- \+ *lemma* localization_away_map_finite_type
- \+ *lemma* is_localization.lift_mem_adjoin_finset_integer_multiple
- \+ *lemma* finite_type_of_localization_span
- \+ *def* ring_hom.localization_preserves
- \+ *def* ring_hom.of_localization_finite_span
- \+ *def* ring_hom.of_localization_span

Modified src/ring_theory/localization.lean
- \+ *def* map



## [2021-12-18 16:15:36](https://github.com/leanprover-community/mathlib/commit/c10a872)
feat(order): define a `rel_hom_class` for types of relation-preserving maps ([#10755](https://github.com/leanprover-community/mathlib/pull/10755))
Use the design of [#9888](https://github.com/leanprover-community/mathlib/pull/9888) to define a class `rel_hom_class F r s` for types of maps such that all `f : F` satisfy `r a b → s (f a) (f b)`. Requested by @YaelDillies.
`order_hom_class F α β` is defined as an abbreviation for `rel_hom_class F (≤) (≤)`.
#### Estimated changes
Modified src/algebra/lie/subalgebra.lean

Modified src/algebra/lie/submodule.lean

Modified src/order/compactly_generated.lean

Modified src/order/hom/basic.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified src/order/rel_iso.lean
- \+/\- *lemma* map_inf
- \+/\- *lemma* map_sup
- \+/\- *lemma* map_inf
- \+/\- *lemma* map_sup
- \+/\- *theorem* coe_fn_injective
- \+/\- *theorem* coe_fn_injective
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+/\- *theorem* to_equiv_injective
- \+/\- *theorem* coe_fn_injective
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \- *theorem* map_rel
- \+/\- *theorem* coe_fn_injective
- \+/\- *theorem* coe_fn_injective
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+/\- *theorem* to_equiv_injective
- \+/\- *theorem* coe_fn_injective
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff

Modified src/ring_theory/int/basic.lean

Modified src/ring_theory/polynomial/basic.lean

Modified src/ring_theory/unique_factorization_domain.lean



## [2021-12-18 14:23:59](https://github.com/leanprover-community/mathlib/commit/af682d3)
feat(algebraic_geometry): A scheme is reduced iff its stalks are reduced. ([#10879](https://github.com/leanprover-community/mathlib/pull/10879))
#### Estimated changes
Modified src/algebraic_geometry/properties.lean
- \+ *lemma* is_reduced_of_stalk_is_reduced

Modified src/ring_theory/nilpotent.lean
- \+ *lemma* is_nilpotent.mk



## [2021-12-18 14:23:58](https://github.com/leanprover-community/mathlib/commit/65118e5)
feat(analysis/calculus/deriv): add `has_deriv_at.tendsto_punctured_nhds` ([#10877](https://github.com/leanprover-community/mathlib/pull/10877))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_at.tendsto_punctured_nhds

Modified src/analysis/special_functions/trigonometric/complex_deriv.lean



## [2021-12-18 14:23:57](https://github.com/leanprover-community/mathlib/commit/0108884)
feat(ring_theory/integral_closure): A subalgebra is contained in the integral closure iff it is integral ([#10874](https://github.com/leanprover-community/mathlib/pull/10874))
A subalgebra is contained in the integral closure iff it is integral.
#### Estimated changes
Modified src/ring_theory/integral_closure.lean
- \+ *lemma* le_integral_closure_iff_is_integral



## [2021-12-18 14:23:56](https://github.com/leanprover-community/mathlib/commit/7de517b)
feat(algebra/algebra/subalgebra): Elements of supremum ([#10872](https://github.com/leanprover-community/mathlib/pull/10872))
Adds a few lemmas about elements of a supremum of subalgebras (essentially copied from the analogous lemmas in `group_theory/subgroup.basic`).
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* mem_sup_left
- \+ *lemma* mem_sup_right
- \+ *lemma* mul_mem_sup



## [2021-12-18 14:23:55](https://github.com/leanprover-community/mathlib/commit/df11302)
feat(algebra/algebra/subalgebra): Lemmas about `alg_hom.range` ([#10871](https://github.com/leanprover-community/mathlib/pull/10871))
This PR adds a few lemmas about `alg_hom.range`.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *theorem* range_comp
- \+ *theorem* range_comp_le_range
- \+ *theorem* range_id



## [2021-12-18 14:23:54](https://github.com/leanprover-community/mathlib/commit/ac10136)
feat(algebraic_geometry): The underlying topological space of a Scheme is T0 ([#10869](https://github.com/leanprover-community/mathlib/pull/10869))
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum/basic.lean

Modified src/algebraic_geometry/properties.lean

Modified src/logic/basic.lean
- \+ *theorem* not_xor
- \+ *theorem* xor_iff_not_iff

Modified src/topology/separation.lean
- \+ *lemma* t0_space_def
- \+ *lemma* t0_space_iff_distinguishable
- \+ *lemma* indistinguishable_iff_closed
- \+ *lemma* indistinguishable_iff_closure
- \+ *lemma* subtype_indistinguishable_iff
- \+ *lemma* t0_space_of_injective_of_continuous
- \+ *theorem* t0_space_iff_or_not_mem_closure
- \+ *def* indistinguishable



## [2021-12-18 14:23:53](https://github.com/leanprover-community/mathlib/commit/cb0a6f7)
feat(data/int): various lemmas ([#10862](https://github.com/leanprover-community/mathlib/pull/10862))
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* abs_sign_of_nonzero
- \+ *lemma* is_unit_iff_abs_eq
- \+ *lemma* of_nat_is_unit

Modified src/data/int/parity.lean
- \+ *lemma* four_dvd_add_or_sub_of_odd

Modified src/ring_theory/int/basic.lean
- \+ *lemma* int.exists_prime_and_dvd



## [2021-12-18 14:23:52](https://github.com/leanprover-community/mathlib/commit/04e2f5f)
feat(algebra/group/basic): add a few lemmas ([#10856](https://github.com/leanprover-community/mathlib/pull/10856))
* move `inv_eq_one`, `one_eq_inv`, and `inv_ne_one` up;
* move `div_one'` below `div_eq_one` to golf the proof;
* add `div_eq_inv_iff`;
* golf 2 proofs.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+/\- *lemma* div_one'
- \+/\- *lemma* div_one'
- \+/\- *theorem* inv_eq_one
- \+/\- *theorem* one_eq_inv
- \+/\- *theorem* inv_ne_one
- \+ *theorem* div_eq_inv_self
- \+/\- *theorem* inv_eq_one
- \+/\- *theorem* one_eq_inv
- \+/\- *theorem* inv_ne_one



## [2021-12-18 14:23:51](https://github.com/leanprover-community/mathlib/commit/5859ec0)
feat(analysis/normed_space/lattice_ordered_group): prove `order_closed_topology` for `normed_lattice_add_comm_group` ([#10838](https://github.com/leanprover-community/mathlib/pull/10838))
#### Estimated changes
Modified src/analysis/normed_space/lattice_ordered_group.lean
- \+ *lemma* norm_sup_sub_sup_le_norm
- \+ *lemma* norm_inf_sub_inf_le_norm
- \+ *lemma* lipschitz_with_sup_right
- \+ *lemma* lipschitz_with_pos
- \+ *lemma* continuous_pos
- \+ *lemma* continuous_neg'
- \+ *lemma* is_closed_nonneg
- \+ *lemma* is_closed_le_of_is_closed_nonneg



## [2021-12-18 12:49:52](https://github.com/leanprover-community/mathlib/commit/6353d6b)
chore(*): more assorted proof simplifications ([#10863](https://github.com/leanprover-community/mathlib/pull/10863))
A few more random small golfs found by linters
#### Estimated changes
Modified src/analysis/normed_space/spectrum.lean

Modified src/data/dfinsupp.lean

Modified src/data/ordmap/ordset.lean

Modified src/data/polynomial/field_division.lean



## [2021-12-18 11:01:55](https://github.com/leanprover-community/mathlib/commit/0e995a3)
refactor(*): kill a few uses of finish ([#10860](https://github.com/leanprover-community/mathlib/pull/10860))
#### Estimated changes
Modified src/algebra/big_operators/ring.lean

Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex_empty
- \+/\- *lemma* convex_empty

Modified src/analysis/normed_space/lattice_ordered_group.lean

Modified src/data/set/constructions.lean

Modified src/data/set/lattice.lean



## [2021-12-18 10:22:17](https://github.com/leanprover-community/mathlib/commit/ec2f350)
feat(field_theory/intermediate_field): Range of `intermediate_field.val` ([#10873](https://github.com/leanprover-community/mathlib/pull/10873))
The range of the algebra homomorphism `S.val` equals `S.to_subalgebra`.
#### Estimated changes
Modified src/field_theory/intermediate_field.lean
- \+ *lemma* range_val



## [2021-12-18 10:22:16](https://github.com/leanprover-community/mathlib/commit/718ea93)
feat(category_theory): Glue data ([#10436](https://github.com/leanprover-community/mathlib/pull/10436))
#### Estimated changes
Created src/category_theory/glue_data.lean
- \+ *lemma* t'_iij
- \+ *lemma* t'_jii
- \+ *lemma* t'_iji
- \+ *lemma* t_inv
- \+ *lemma* t'_inv
- \+ *lemma* t'_comp_eq_pullback_symmetry
- \+ *lemma* diagram_L
- \+ *lemma* diagram_R
- \+ *lemma* diagram_fst_from
- \+ *lemma* diagram_snd_from
- \+ *lemma* diagram_fst
- \+ *lemma* diagram_snd
- \+ *lemma* diagram_left
- \+ *lemma* diagram_right
- \+ *lemma* glue_condition
- \+ *lemma* diagram_iso_app_left
- \+ *lemma* diagram_iso_app_right
- \+ *lemma* diagram_iso_hom_app_left
- \+ *lemma* diagram_iso_hom_app_right
- \+ *lemma* diagram_iso_inv_app_left
- \+ *lemma* diagram_iso_inv_app_right
- \+ *def* sigma_opens
- \+ *def* diagram
- \+ *def* glued
- \+ *def* ι
- \+ *def* π
- \+ *def* map_glue_data
- \+ *def* diagram_iso



## [2021-12-18 06:26:17](https://github.com/leanprover-community/mathlib/commit/a252427)
chore(algebra/algebra/basic): fix instances names to make doc links work ([#10834](https://github.com/leanprover-community/mathlib/pull/10834))
The blank lines avoid sentences being pulled into the bulleted list above them.
#### Estimated changes
Modified src/algebra/algebra/basic.lean

Modified src/number_theory/bernoulli.lean



## [2021-12-17 23:05:39](https://github.com/leanprover-community/mathlib/commit/2043748)
feat(data/finset/basic): add to_list_insert and to_list_cons ([#10840](https://github.com/leanprover-community/mathlib/pull/10840))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* to_list_cons
- \+ *lemma* to_list_insert



## [2021-12-17 21:25:06](https://github.com/leanprover-community/mathlib/commit/fc09b17)
feat(measure_theory/integral/bochner): prove `set_integral_eq_subtype` ([#10858](https://github.com/leanprover-community/mathlib/pull/10858))
Relate integral w.r.t. `μ.restrict s` and w.r.t. `comap (coe : s → α) μ`.
#### Estimated changes
Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* set_integral_eq_subtype



## [2021-12-17 19:23:39](https://github.com/leanprover-community/mathlib/commit/86493f1)
feat(data/nat): decidable exists le instance ([#10857](https://github.com/leanprover-community/mathlib/pull/10857))
Adds the `le` instance for a corresponding `lt` instance above.
#### Estimated changes
Modified src/data/nat/basic.lean



## [2021-12-17 19:23:38](https://github.com/leanprover-community/mathlib/commit/70f4ba0)
feat(algebra/group/hom): generalize `semiconj_by.map` and `commute.map` ([#10854](https://github.com/leanprover-community/mathlib/pull/10854))
This generalizes the results in 2 ways: from `monoid_hom` to `mul_hom` and from `mul_hom` to `mul_hom_class`. For use in [#10783](https://github.com/leanprover-community/mathlib/pull/10783).
#### Estimated changes
Modified src/algebra/group/hom.lean



## [2021-12-17 19:23:37](https://github.com/leanprover-community/mathlib/commit/0b5f0a2)
feat(data/finset/basic): add ite_subset_union, inter_subset_ite for finset ([#10586](https://github.com/leanprover-community/mathlib/pull/10586))
Just a couple of lemmas to simplify expressions involving ite and union / inter on finsets, note that this is not related to `set.ite`.
From flt-regular.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* ite_subset_union
- \+ *lemma* inter_subset_ite

Modified src/order/lattice.lean
- \+ *lemma* ite_le_sup
- \+ *lemma* inf_le_ite



## [2021-12-17 17:22:44](https://github.com/leanprover-community/mathlib/commit/e5a844e)
feat(data/finsupp/basic): add two versions of `finsupp.mul_prod_erase` ([#10708](https://github.com/leanprover-community/mathlib/pull/10708))
Adding a counterpart for `finsupp` of `finset.mul_prod_erase`
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* mul_prod_erase
- \+ *lemma* mul_prod_erase'



## [2021-12-17 15:21:19](https://github.com/leanprover-community/mathlib/commit/c9fe6d1)
feat(algebra/algebra): instantiate `ring_hom_class` for `alg_hom` ([#10853](https://github.com/leanprover-community/mathlib/pull/10853))
This PR provides a `ring_hom_class` instance for `alg_hom`, to be used in [#10783](https://github.com/leanprover-community/mathlib/pull/10783). I'm not quite finished with my design of morphism classes for linear maps, but I expect this instance will stick around anyway: to avoid a dangerous instance `alg_hom_class F R A B → ring_hom_class F A B` (where the base ring `R` can't be inferred), `alg_hom_class` will probably have to be unbundled and take a `ring_hom_class` as a parameter.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+/\- *lemma* coe_to_monoid_hom
- \+/\- *lemma* coe_to_add_monoid_hom
- \+/\- *lemma* map_add
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_one
- \+/\- *lemma* map_pow
- \+/\- *lemma* map_bit0
- \+/\- *lemma* map_bit1
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* coe_to_monoid_hom
- \+/\- *lemma* coe_to_add_monoid_hom
- \+/\- *lemma* map_add
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_one
- \+/\- *lemma* map_pow
- \+/\- *lemma* map_bit0
- \+/\- *lemma* map_bit1
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *theorem* coe_fn_injective
- \+/\- *theorem* coe_fn_inj
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+/\- *theorem* coe_fn_injective
- \+/\- *theorem* coe_fn_inj
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff



## [2021-12-17 15:21:18](https://github.com/leanprover-community/mathlib/commit/ba24b38)
feat(ring_theory/noetherian): fg_pi ([#10845](https://github.com/leanprover-community/mathlib/pull/10845))
#### Estimated changes
Modified src/linear_algebra/free_module/strong_rank_condition.lean

Modified src/linear_algebra/pi.lean
- \+ *lemma* pi_empty
- \+ *lemma* pi_top
- \+ *lemma* pi_mono

Modified src/ring_theory/finiteness.lean

Modified src/ring_theory/noetherian.lean
- \+ *theorem* fg_pi



## [2021-12-17 13:26:57](https://github.com/leanprover-community/mathlib/commit/5a59800)
feat(data/set/function): Cancelling composition on a set ([#10803](https://github.com/leanprover-community/mathlib/pull/10803))
A few stupid lemmas
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* eq_on.comp_left
- \+ *lemma* eq_on.comp_right
- \+ *lemma* eq_on.cancel_left
- \+ *lemma* inj_on.cancel_left
- \+ *lemma* image_eq_iff_surj_on_maps_to
- \+ *lemma* eq_on.cancel_right
- \+ *lemma* surj_on.cancel_right
- \+ *lemma* eq_on_comp_right_iff



## [2021-12-17 12:31:31](https://github.com/leanprover-community/mathlib/commit/6838233)
feat(combinatorics/configuration): New file ([#10773](https://github.com/leanprover-community/mathlib/pull/10773))
This PR defines abstract configurations of points and lines, and provides some basic definitions. Actual results are in the followup PR.
#### Estimated changes
Created src/combinatorics/configuration.lean
- \+ *lemma* has_points.exists_unique_point
- \+ *lemma* has_lines.exists_unique_line
- \+ *def* dual



## [2021-12-17 12:31:30](https://github.com/leanprover-community/mathlib/commit/8743573)
feat(data/nat/count): The count function on naturals ([#9457](https://github.com/leanprover-community/mathlib/pull/9457))
Defines `nat.count` a generic counting function on `ℕ`, computing how many numbers under `k` satisfy a given predicate".
Co-authored by:
Yaël Dillies, yael.dillies@gmail.com
Vladimir Goryachev, gor050299@gmail.com
Kyle Miller, kmill31415@gmail.com
Scott Morrison, scott@tqft.net
Eric Rodriguez, ericrboidi@gmail.com
#### Estimated changes
Created src/data/nat/count.lean
- \+ *lemma* count_zero
- \+ *lemma* count_eq_card_filter_range
- \+ *lemma* count_eq_card_fintype
- \+ *lemma* count_monotone
- \+ *lemma* count_succ
- \+ *lemma* count_add
- \+ *lemma* count_add'
- \+ *lemma* count_one
- \+ *lemma* count_succ'
- \+ *lemma* count_succ_eq_succ_count_iff
- \+ *lemma* count_succ_eq_count_iff
- \+ *lemma* count_le_cardinal
- \+ *lemma* lt_of_count_lt_count
- \+ *lemma* count_mono_left
- \+ *def* count
- \+ *def* count_set.fintype



## [2021-12-17 10:49:01](https://github.com/leanprover-community/mathlib/commit/081cb8a)
chore(algebra/associated): split off dependencies of `big_operators` ([#10848](https://github.com/leanprover-community/mathlib/pull/10848))
This prepares for the replacement of `nat.prime` with `_root_.prime` by reducing the amount of dependencies needed to define `_root_.prime`.
Note that there wouldn't be an import loop without this change, just that `data/nat/prime.lean` would have a bigger amount of imports.
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/nat.2Eprime
#### Estimated changes
Modified src/algebra/associated.lean
- \- *lemma* exists_mem_multiset_dvd
- \- *lemma* exists_mem_multiset_map_dvd
- \- *lemma* exists_mem_finset_dvd
- \- *lemma* exists_associated_mem_of_dvd_prod
- \- *lemma* exists_mem_multiset_le_of_prime
- \- *lemma* prod_ne_zero_of_prime
- \- *theorem* prod_mk
- \- *theorem* rel_associated_iff_map_eq_map
- \- *theorem* prod_eq_one_iff
- \- *theorem* prod_le_prod

Created src/algebra/big_operators/associated.lean
- \+ *lemma* exists_mem_multiset_dvd
- \+ *lemma* exists_mem_multiset_map_dvd
- \+ *lemma* exists_mem_finset_dvd
- \+ *lemma* exists_associated_mem_of_dvd_prod
- \+ *lemma* exists_mem_multiset_le_of_prime
- \+ *lemma* prod_ne_zero_of_prime
- \+ *theorem* prod_mk
- \+ *theorem* rel_associated_iff_map_eq_map
- \+ *theorem* prod_eq_one_iff
- \+ *theorem* prod_le_prod

Modified src/ring_theory/unique_factorization_domain.lean



## [2021-12-17 10:49:00](https://github.com/leanprover-community/mathlib/commit/862a68c)
feat(algebra/big_operators/basic): add finset.prod_to_list ([#10842](https://github.com/leanprover-community/mathlib/pull/10842))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_to_list



## [2021-12-17 09:42:27](https://github.com/leanprover-community/mathlib/commit/5558fd9)
feat(topology/subset_properties): open/closed sets are locally compact spaces ([#10844](https://github.com/leanprover-community/mathlib/pull/10844))
* add `inducing.image_mem_nhds_within`;
* move `inducing.is_compact_iff` up, use it to prove `embedding.is_compact_iff_is_compact_image`;
* prove `closed_embedding.is_compact_preimage`, use it to prove `closed_embedding.tendsto_cocompact`;
* prove `closed_embedding.locally_compact_space`, `open_embedding.locally_compact_space`;
* specialize to `is_closed.locally_compact_space`, `is_open.locally_compact_space`;
* rename `locally_finite.countable_of_sigma_compact` to `locally_finite.countable_univ`, provide `locally_finite.encodable`.
#### Estimated changes
Modified src/topology/maps.lean
- \+ *lemma* inducing.image_mem_nhds_within

Modified src/topology/subset_properties.lean
- \+/\- *lemma* inducing.is_compact_iff
- \+ *lemma* closed_embedding.is_compact_preimage
- \+/\- *lemma* inducing.is_compact_iff
- \- *lemma* locally_finite.countable_of_sigma_compact



## [2021-12-17 02:13:44](https://github.com/leanprover-community/mathlib/commit/b100af6)
feat(combinatorics/simple_graph/basic): Incidence set lemmas ([#10839](https://github.com/leanprover-community/mathlib/pull/10839))
Some more `simple_graph.incidence_set` API.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+/\- *lemma* adj_symm
- \+/\- *lemma* ne_of_adj
- \+/\- *lemma* mem_edge_set
- \+ *lemma* adj_iff_exists_edge_coe
- \+/\- *lemma* incidence_set_subset
- \+ *lemma* mk_mem_incidence_set_iff
- \+ *lemma* mk_mem_incidence_set_left_iff
- \+ *lemma* mk_mem_incidence_set_right_iff
- \+ *lemma* edge_mem_incidence_set_iff
- \+ *lemma* incidence_set_inter_incidence_set_subset
- \+ *lemma* incidence_set_inter_incidence_set
- \+ *lemma* adj_of_mem_incidence_set
- \+/\- *lemma* adj_symm
- \+/\- *lemma* ne_of_adj
- \+/\- *lemma* incidence_set_subset
- \+/\- *lemma* mem_edge_set
- \+/\- *def* incidence_set
- \+/\- *def* incidence_set



## [2021-12-16 21:36:33](https://github.com/leanprover-community/mathlib/commit/9f9015c)
refactor(category_theory/sites/*): Redefine the category of sheaves. ([#10678](https://github.com/leanprover-community/mathlib/pull/10678))
This refactor redefines sheaves and morphisms of sheaves using bespoke structures.
This is an attempt to make automation more useful when dealing with categories of sheaves.
See the associated [zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Redefining.20Sheaves/near/263308542)
#### Estimated changes
Modified src/category_theory/sites/adjunction.lean
- \+ *lemma* adjunction_to_types_unit_app_val
- \+ *lemma* adjunction_to_types_counit_app_val
- \- *lemma* adjunction_hom_equiv_apply
- \- *lemma* adjunction_hom_equiv_symm_apply
- \- *lemma* adjunction_unit_app
- \- *lemma* adjunction_counit_app
- \- *lemma* adjunction_to_types_hom_equiv_apply
- \- *lemma* adjunction_to_types_hom_equiv_symm_apply
- \- *lemma* adjunction_to_types_unit_app
- \- *lemma* adjunction_to_types_counit_app

Modified src/category_theory/sites/cover_lifting.lean

Modified src/category_theory/sites/cover_preserving.lean

Modified src/category_theory/sites/dense_subsite.lean

Modified src/category_theory/sites/limits.lean

Modified src/category_theory/sites/sheaf.lean
- \- *lemma* id_app
- \- *lemma* comp_app
- \- *lemma* Sheaf_to_presheaf_obj
- \+/\- *def* Sheaf_to_presheaf
- \+ *def* sheaf_over
- \- *def* Sheaf
- \+/\- *def* Sheaf_to_presheaf

Modified src/category_theory/sites/sheaf_of_types.lean
- \- *lemma* id_app
- \- *lemma* comp_app
- \- *lemma* SheafOfTypes_to_presheaf_obj
- \- *def* SheafOfTypes

Modified src/category_theory/sites/sheafification.lean
- \- *lemma* sheafification_adjunction_unit_app
- \- *lemma* sheafification_iso_hom
- \- *lemma* sheafification_iso_inv

Modified src/category_theory/sites/types.lean
- \+/\- *lemma* yoneda'_comp
- \+/\- *lemma* yoneda'_comp

Modified src/category_theory/sites/whiskering.lean

Modified src/topology/sheaves/sheaf_condition/sites.lean



## [2021-12-16 17:52:29](https://github.com/leanprover-community/mathlib/commit/601f2ab)
fix(ring_theory/ideal/basic): remove universe restriction ([#10843](https://github.com/leanprover-community/mathlib/pull/10843))
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+/\- *lemma* mem_supr_of_mem
- \+/\- *lemma* mem_infi
- \+/\- *lemma* mem_supr_of_mem
- \+/\- *lemma* mem_infi



## [2021-12-16 16:16:13](https://github.com/leanprover-community/mathlib/commit/905d887)
chore(field_theory/ratfunc): to_fraction_ring_ring_equiv ([#10806](https://github.com/leanprover-community/mathlib/pull/10806))
Rename the underlying `ratfunc.aux_equiv` for discoverability.
#### Estimated changes
Modified src/field_theory/ratfunc.lean
- \+ *lemma* to_fraction_ring_ring_equiv_symm_eq
- \- *lemma* aux_equiv_eq
- \+ *def* to_fraction_ring_ring_equiv
- \- *def* aux_equiv



## [2021-12-16 10:58:20](https://github.com/leanprover-community/mathlib/commit/eeef771)
chore(field_theory/ratfunc): has_scalar in terms of localization ([#10828](https://github.com/leanprover-community/mathlib/pull/10828))
Now that `localization.has_scalar` is general enough, fix a TODO
#### Estimated changes
Modified src/field_theory/ratfunc.lean
- \+ *lemma* of_fraction_ring_smul
- \+ *lemma* to_fraction_ring_smul



## [2021-12-16 10:58:19](https://github.com/leanprover-community/mathlib/commit/542471f)
feat(data/set/function): Congruence lemmas for `monotone_on` and friends ([#10817](https://github.com/leanprover-community/mathlib/pull/10817))
Congruence lemmas for `monotone_on`, `antitone_on`, `strict_mono_on`, `strict_anti_on` using `set.eq_on`.
`data.set.function` imports `order.monotone` so we must put them here.
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* _root_.monotone_on.congr
- \+ *lemma* _root_.antitone_on.congr
- \+ *lemma* _root_.strict_mono_on.congr
- \+ *lemma* _root_.strict_anti_on.congr
- \+ *lemma* eq_on.congr_monotone_on
- \+ *lemma* eq_on.congr_antitone_on
- \+ *lemma* eq_on.congr_strict_mono_on
- \+ *lemma* eq_on.congr_strict_anti_on



## [2021-12-16 10:58:18](https://github.com/leanprover-community/mathlib/commit/b5b19a6)
feat(ring_theory/local_property): Being reduced is a local property. ([#10734](https://github.com/leanprover-community/mathlib/pull/10734))
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* mem_annihilator_span
- \+ *lemma* mem_annihilator_span_singleton

Created src/ring_theory/local_properties.lean
- \+ *lemma* ideal_eq_zero_of_localization
- \+ *lemma* eq_zero_of_localization
- \+ *lemma* localization_is_reduced
- \+ *lemma* is_reduced_of_localization_maximal
- \+ *def* localization_preserves
- \+ *def* of_localization_maximal

Modified src/ring_theory/localization.lean
- \+ *lemma* map_eq_zero_iff

Modified src/ring_theory/nilpotent.lean
- \+ *lemma* is_nilpotent.map



## [2021-12-16 09:07:54](https://github.com/leanprover-community/mathlib/commit/68ced9a)
chore(analysis/mean_inequalities_pow): nnreal versions of some ennreal inequalities ([#10836](https://github.com/leanprover-community/mathlib/pull/10836))
Make `nnreal` versions of the existing `ennreal` lemmas
```lean
lemma add_rpow_le_rpow_add {p : ℝ} (a b : ℝ≥0∞) (hp1 : 1 ≤ p) :
  a ^ p + b ^ p ≤ (a + b) ^ p 
```
and similar, introduced by @RemyDegenne in [#5828](https://github.com/leanprover-community/mathlib/pull/5828).  Refactor the proofs of the `ennreal` versions to pass through these.
#### Estimated changes
Modified src/analysis/mean_inequalities_pow.lean
- \+ *lemma* add_rpow_le_rpow_add
- \+ *lemma* rpow_add_rpow_le_add
- \+ *lemma* rpow_add_le_add_rpow
- \+ *theorem* rpow_add_rpow_le

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* le_rpow_one_div_iff
- \+ *lemma* rpow_le_self_of_le_one

Modified src/order/bounded_order.lean
- \+ *lemma* eq_top_or_lt_top
- \+ *lemma* eq_bot_or_bot_lt



## [2021-12-16 09:07:53](https://github.com/leanprover-community/mathlib/commit/d212f3e)
feat(measure_theory/measure): new class is_finite_measure_on_compacts ([#10827](https://github.com/leanprover-community/mathlib/pull/10827))
We have currently four independent type classes guaranteeing that a measure of compact sets is finite: `is_locally_finite_measure`, `is_regular_measure`, `is_haar_measure` and `is_add_haar_measure`. Instead of repeting lemmas for all these classes, we introduce a new typeclass saying that a measure is finite on compact sets.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean

Modified src/measure_theory/covering/besicovitch_vector_space.lean

Modified src/measure_theory/group/basic.lean
- \- *lemma* _root_.is_compact.haar_lt_top

Modified src/measure_theory/group/prod.lean

Modified src/measure_theory/measure/content.lean

Modified src/measure_theory/measure/haar.lean

Modified src/measure_theory/measure/haar_lebesgue.lean
- \- *lemma* add_haar_closed_ball_lt_top
- \- *lemma* add_haar_ball_lt_top

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* _root_.is_compact.measure_lt_top
- \+ *lemma* _root_.metric.bounded.measure_lt_top
- \+ *lemma* measure_closed_ball_lt_top
- \+ *lemma* measure_ball_lt_top
- \- *lemma* measure_lt_top
- \- *lemma* metric.bounded.measure_lt_top

Modified src/measure_theory/measure/regular.lean



## [2021-12-16 08:30:05](https://github.com/leanprover-community/mathlib/commit/87e2f24)
feat(category_theory/adjunction/evaluation): Evaluation has a left and a right adjoint. ([#10793](https://github.com/leanprover-community/mathlib/pull/10793))
#### Estimated changes
Created src/category_theory/adjunction/evaluation.lean
- \+ *lemma* nat_trans.mono_iff_app_mono
- \+ *lemma* nat_trans.epi_iff_app_epi
- \+ *def* evaluation_left_adjoint
- \+ *def* evaluation_adjunction_right
- \+ *def* evaluation_right_adjoint
- \+ *def* evaluation_adjunction_left



## [2021-12-16 02:33:43](https://github.com/leanprover-community/mathlib/commit/8e4b3b0)
chore(data/polynomial/field_division): beta-reduce ([#10835](https://github.com/leanprover-community/mathlib/pull/10835))
#### Estimated changes
Modified src/data/polynomial/field_division.lean



## [2021-12-15 21:49:21](https://github.com/leanprover-community/mathlib/commit/5a835b7)
chore(*): tweaks taken from gh-8889 ([#10829](https://github.com/leanprover-community/mathlib/pull/10829))
That PR is stale, but contained some trivial changes we should just take.
#### Estimated changes
Modified src/analysis/complex/circle.lean

Modified src/group_theory/quotient_group.lean
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_zpow
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_zpow



## [2021-12-15 21:49:20](https://github.com/leanprover-community/mathlib/commit/8218a78)
feat(analysis/normed_space/basic): formula for `c • sphere x r` ([#10814](https://github.com/leanprover-community/mathlib/pull/10814))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *theorem* smul_sphere'
- \+ *theorem* normed_space.sphere_nonempty
- \+ *theorem* smul_sphere
- \+/\- *theorem* smul_closed_ball'
- \+/\- *theorem* smul_closed_ball'

Modified src/topology/metric_space/basic.lean
- \+ *lemma* sphere_zero



## [2021-12-15 21:49:19](https://github.com/leanprover-community/mathlib/commit/b82c0d2)
feat(topology/metric_space/isometry): (pre)image of a (closed) ball or a sphere ([#10813](https://github.com/leanprover-community/mathlib/pull/10813))
Also specialize for translations in a normed add torsor.
#### Estimated changes
Modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* vadd_ball
- \+ *lemma* vadd_closed_ball
- \+ *lemma* vadd_sphere
- \+ *def* isometric.vadd_const
- \+ *def* isometric.const_vadd
- \+ *def* isometric.const_vsub

Modified src/analysis/normed_space/mazur_ulam.lean

Modified src/topology/metric_space/isometry.lean
- \+/\- *lemma* isometry.tendsto_nhds_iff
- \+ *lemma* isometry.maps_to_emetric_ball
- \+ *lemma* isometry.maps_to_emetric_closed_ball
- \+ *lemma* diam_image
- \+ *lemma* diam_range
- \+ *lemma* maps_to_ball
- \+ *lemma* maps_to_sphere
- \+ *lemma* maps_to_closed_ball
- \+ *lemma* preimage_emetric_ball
- \+ *lemma* preimage_emetric_closed_ball
- \+ *lemma* image_emetric_ball
- \+ *lemma* image_emetric_closed_ball
- \+ *lemma* preimage_ball
- \+ *lemma* preimage_sphere
- \+ *lemma* preimage_closed_ball
- \+ *lemma* image_ball
- \+ *lemma* image_sphere
- \+ *lemma* image_closed_ball
- \+/\- *lemma* isometry.tendsto_nhds_iff
- \- *lemma* isometry.diam_image
- \- *lemma* isometry.diam_range



## [2021-12-15 21:49:18](https://github.com/leanprover-community/mathlib/commit/21c9d3b)
feat(topology/metric_space/hausdorff_distance): add more topological properties API to thickenings ([#10661](https://github.com/leanprover-community/mathlib/pull/10661))
More lemmas about thickenings, especially topological properties, still in preparation for the portmanteau theorem on characterizations of weak convergence of Borel probability measures.
#### Estimated changes
Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* cthickening_of_nonpos
- \+ *lemma* thickening_subset_interior_cthickening
- \+ *lemma* closure_thickening_subset_cthickening
- \+/\- *lemma* closure_subset_cthickening
- \+ *lemma* closure_subset_thickening
- \+ *lemma* self_subset_thickening
- \+ *lemma* self_subset_cthickening
- \+ *lemma* cthickening_eq_Inter_cthickening'
- \+/\- *lemma* cthickening_eq_Inter_cthickening
- \+ *lemma* cthickening_eq_Inter_thickening'
- \+ *lemma* cthickening_eq_Inter_thickening
- \+ *lemma* closure_eq_Inter_cthickening'
- \+/\- *lemma* closure_eq_Inter_cthickening
- \+ *lemma* closure_eq_Inter_thickening'
- \+ *lemma* closure_eq_Inter_thickening
- \+ *lemma* frontier_thickening_subset
- \+ *lemma* frontier_cthickening_subset
- \+/\- *lemma* closure_subset_cthickening
- \+/\- *lemma* cthickening_eq_Inter_cthickening
- \+/\- *lemma* closure_eq_Inter_cthickening



## [2021-12-15 19:58:19](https://github.com/leanprover-community/mathlib/commit/ef69cac)
chore(topology/continuous_function/bounded): remove extra typeclass assumption ([#10823](https://github.com/leanprover-community/mathlib/pull/10823))
Remove `[normed_star_monoid β]` from the typeclass assumptions of `[cstar_ring (α →ᵇ β)]` -- it was doing no harm, since it's implied by the assumption `[cstar_ring β]`, but it's unnecessary.
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean



## [2021-12-15 19:58:18](https://github.com/leanprover-community/mathlib/commit/00c55f5)
feat(algebra/module/linear_map): interaction of linear maps and pointwise operations on sets ([#10821](https://github.com/leanprover-community/mathlib/pull/10821))
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *lemma* image_smul_setₛₗ
- \+ *lemma* image_smul_set
- \+ *lemma* preimage_smul_setₛₗ
- \+ *lemma* preimage_smul_set

Modified src/algebra/pointwise.lean
- \+ *lemma* smul_add_set

Modified src/data/equiv/module.lean
- \+ *lemma* image_smul_setₛₗ
- \+ *lemma* preimage_smul_setₛₗ
- \+ *lemma* image_smul_set
- \+ *lemma* preimage_smul_set

Modified src/topology/algebra/module.lean
- \+ *lemma* image_smul_setₛₗ
- \+ *lemma* image_smul_set
- \+ *lemma* preimage_smul_setₛₗ
- \+ *lemma* preimage_smul_set
- \+ *lemma* image_smul_setₛₗ
- \+ *lemma* preimage_smul_setₛₗ
- \+ *lemma* image_smul_set
- \+ *lemma* preimage_smul_set



## [2021-12-15 19:58:17](https://github.com/leanprover-community/mathlib/commit/dfb78f7)
feat(analysis/special_functions/complex): range of `complex.exp (↑x * I)` ([#10816](https://github.com/leanprover-community/mathlib/pull/10816))
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* range_exp_mul_I



## [2021-12-15 19:58:16](https://github.com/leanprover-community/mathlib/commit/81e58c9)
feat(analysis/mean_inequalities): corollary of Hölder inequality ([#10789](https://github.com/leanprover-community/mathlib/pull/10789))
Several versions of the fact that
```
(∑ i in s, f i) ^ p ≤ (card s) ^ (p - 1) * ∑ i in s, (f i) ^ p
```
for `1 ≤ p`.
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *theorem* rpow_sum_le_const_mul_sum_rpow
- \+ *theorem* rpow_sum_le_const_mul_sum_rpow
- \+ *theorem* rpow_sum_le_const_mul_sum_rpow_of_nonneg
- \+ *theorem* rpow_sum_le_const_mul_sum_rpow

Modified src/data/real/conjugate_exponents.lean
- \+ *lemma* div_conj_eq_sub_one



## [2021-12-15 19:58:15](https://github.com/leanprover-community/mathlib/commit/026e692)
chore(combinatorics/simple_graph): fix name mixup ([#10785](https://github.com/leanprover-community/mathlib/pull/10785))
Fixes the name mixup from [#10778](https://github.com/leanprover-community/mathlib/pull/10778) and reorders lemmas to make the difference more clear.
#### Estimated changes
Modified src/combinatorics/simple_graph/subgraph.lean
- \+/\- *lemma* top_adj_iff
- \+/\- *lemma* bot_verts
- \+ *lemma* not_bot_adj
- \+/\- *lemma* top_adj_iff
- \- *lemma* bot_adj_iff
- \+/\- *lemma* bot_verts



## [2021-12-15 19:58:13](https://github.com/leanprover-community/mathlib/commit/204aa7e)
feat(data/int/basic): more int.sign API ([#10781](https://github.com/leanprover-community/mathlib/pull/10781))
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* nat_abs_sign
- \+ *lemma* nat_abs_sign_of_nonzero
- \+ *lemma* sign_coe_nat_of_nonzero
- \+ *lemma* sign_neg



## [2021-12-15 19:58:12](https://github.com/leanprover-community/mathlib/commit/75b4e5f)
chore(*): remove edge case assumptions from lemmas  ([#10774](https://github.com/leanprover-community/mathlib/pull/10774))
Remove edge case assumptions from lemmas when the result is easy to prove without the assumption.
We clean up a few lemmas in the library which assume something like `n \ne 0`,  `0 < n`, or `set.nonempty` but where the result is easy to prove by case splitting on this instead and then simplifying.
Removing these unneeded assumptions makes such lemmas easier to apply, and lets us minorly golf a few other proofs along the way.
The main external changes are to remove assumptions to around 30 lemmas, and make some arguments explicit when they were no longer inferable, all other lines are just fixing up the proofs, which shortens some proofs in the process.
I also added a couple of lemmas to help simp in a couple of examples.
The code I used to find these is in the branch https://github.com/leanprover-community/mathlib/tree/alexjbest/simple_edge_cases_linter
#### Estimated changes
Modified src/algebra/group_with_zero/power.lean
- \+/\- *lemma* div_sq_cancel
- \+/\- *lemma* div_sq_cancel

Modified src/analysis/complex/roots_of_unity.lean
- \+/\- *lemma* card_primitive_roots
- \+/\- *lemma* card_primitive_roots

Modified src/data/bitvec/core.lean

Modified src/data/int/basic.lean
- \+/\- *lemma* div_dvd_of_ne_zero_dvd
- \+/\- *lemma* div_dvd_of_ne_zero_dvd

Modified src/data/nat/digits.lean
- \+/\- *lemma* digits_last
- \+/\- *lemma* digits_last

Modified src/data/nat/pow.lean
- \+/\- *theorem* mod_pow_succ
- \+/\- *theorem* mod_pow_succ

Modified src/data/polynomial/field_division.lean
- \+/\- *lemma* prod_multiset_root_eq_finset_root
- \+/\- *lemma* prod_multiset_root_eq_finset_root

Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* card_roots'
- \+/\- *lemma* count_roots
- \+ *lemma* nth_roots_finset_zero
- \+/\- *lemma* card_roots'
- \+/\- *lemma* count_roots

Modified src/field_theory/is_alg_closed/basic.lean
- \+/\- *lemma* degree_eq_one_of_irreducible
- \+/\- *lemma* degree_eq_one_of_irreducible

Modified src/field_theory/ratfunc.lean
- \+/\- *lemma* denom_div_dvd
- \+/\- *lemma* denom_div_dvd

Modified src/field_theory/separable.lean
- \+/\- *lemma* root_multiplicity_le_one_of_separable
- \+/\- *lemma* root_multiplicity_le_one_of_separable
- \+/\- *theorem* map_expand
- \+/\- *theorem* map_expand

Modified src/field_theory/splitting_field.lean

Modified src/geometry/euclidean/monge_point.lean
- \+/\- *lemma* monge_point_mem_monge_plane
- \+/\- *lemma* direction_monge_plane
- \+/\- *lemma* monge_point_mem_monge_plane
- \+/\- *lemma* direction_monge_plane

Modified src/group_theory/exponent.lean
- \+/\- *lemma* exponent_dvd_of_forall_pow_eq_one
- \+/\- *lemma* exponent_dvd_of_forall_pow_eq_one

Modified src/number_theory/padics/hensel.lean

Modified src/number_theory/padics/padic_norm.lean
- \+/\- *lemma* padic_val_nat_zero
- \+/\- *lemma* padic_val_nat_zero
- \+/\- *theorem* min_le_padic_val_rat_add
- \+/\- *theorem* min_le_padic_val_rat_add

Modified src/number_theory/pell.lean
- \+/\- *theorem* eq_of_xn_modeq_le
- \+/\- *theorem* eq_of_xn_modeq
- \+/\- *theorem* eq_of_xn_modeq_le
- \+/\- *theorem* eq_of_xn_modeq

Modified src/ring_theory/eisenstein_criterion.lean

Modified src/ring_theory/hahn_series.lean

Modified src/ring_theory/polynomial/cyclotomic/basic.lean

Modified src/ring_theory/roots_of_unity.lean
- \+/\- *lemma* card_primitive_roots
- \+/\- *lemma* disjoint
- \+/\- *lemma* nth_roots_one_eq_bUnion_primitive_roots
- \+/\- *lemma* card_primitive_roots
- \+/\- *lemma* disjoint
- \+/\- *lemma* nth_roots_one_eq_bUnion_primitive_roots

Modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *theorem* count_mul_of_coprime
- \+/\- *theorem* count_mul_of_coprime'
- \+/\- *theorem* dvd_count_of_dvd_count_mul
- \+/\- *theorem* count_mul_of_coprime
- \+/\- *theorem* count_mul_of_coprime'
- \+/\- *theorem* dvd_count_of_dvd_count_mul



## [2021-12-15 19:58:10](https://github.com/leanprover-community/mathlib/commit/3f55e02)
feat(data/{multiset, finset}/basic): add card_mono ([#10771](https://github.com/leanprover-community/mathlib/pull/10771))
Add a `@[mono]` lemma for `finset.card`. Also `multiset.card_mono` as an alias of a preexisting lemma.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* card_mono

Modified src/data/multiset/basic.lean
- \+ *theorem* card_mono



## [2021-12-15 19:58:08](https://github.com/leanprover-community/mathlib/commit/a0b6bab)
split(logic/nonempty): Split off `logic.basic` ([#10762](https://github.com/leanprover-community/mathlib/pull/10762))
This moves the lemmas about `nonempty` to a new file `logic.basic`
I'm crediting Johannes for 79483182abffcac3a1ddd7098d47a475e75a5ed2
#### Estimated changes
Modified src/logic/basic.lean
- \- *lemma* exists_true_iff_nonempty
- \- *lemma* nonempty_Prop
- \- *lemma* not_nonempty_iff_imp_false
- \- *lemma* nonempty_sigma
- \- *lemma* nonempty_subtype
- \- *lemma* nonempty_prod
- \- *lemma* nonempty_pprod
- \- *lemma* nonempty_sum
- \- *lemma* nonempty_psum
- \- *lemma* nonempty_psigma
- \- *lemma* nonempty_empty
- \- *lemma* nonempty_ulift
- \- *lemma* nonempty_plift
- \- *lemma* nonempty.forall
- \- *lemma* nonempty.exists
- \- *lemma* classical.nonempty_pi
- \- *lemma* nonempty.map
- \- *lemma* nonempty.elim_to_inhabited
- \- *lemma* subsingleton_of_not_nonempty

Modified src/logic/function/basic.lean

Created src/logic/nonempty.lean
- \+ *lemma* exists_true_iff_nonempty
- \+ *lemma* nonempty_Prop
- \+ *lemma* not_nonempty_iff_imp_false
- \+ *lemma* nonempty_sigma
- \+ *lemma* nonempty_subtype
- \+ *lemma* nonempty_prod
- \+ *lemma* nonempty_pprod
- \+ *lemma* nonempty_sum
- \+ *lemma* nonempty_psum
- \+ *lemma* nonempty_psigma
- \+ *lemma* nonempty_empty
- \+ *lemma* nonempty_ulift
- \+ *lemma* nonempty_plift
- \+ *lemma* nonempty.forall
- \+ *lemma* nonempty.exists
- \+ *lemma* classical.nonempty_pi
- \+ *lemma* nonempty.map
- \+ *lemma* nonempty.elim_to_inhabited
- \+ *lemma* subsingleton_of_not_nonempty

Modified src/tactic/derive_fintype.lean

Modified src/tactic/interactive.lean



## [2021-12-15 19:58:07](https://github.com/leanprover-community/mathlib/commit/02cdc81)
refactor(order/sup_indep): Get rid of decidable equality assumption ([#10673](https://github.com/leanprover-community/mathlib/pull/10673))
The `erase` in the definition required a `decidable_eq`. We can make do without it while keeping it functionally the same.
#### Estimated changes
Modified src/order/sup_indep.lean
- \+/\- *lemma* sup_indep_empty
- \+/\- *lemma* sup_indep.pairwise_disjoint
- \+ *lemma* sup_indep_iff_disjoint_erase
- \+/\- *lemma* sup_indep_iff_pairwise_disjoint
- \+/\- *lemma* sup_indep.sup
- \+/\- *lemma* sup_indep.bUnion
- \+/\- *lemma* complete_lattice.independent_iff_sup_indep
- \+/\- *lemma* sup_indep_empty
- \+/\- *lemma* sup_indep.sup
- \+/\- *lemma* sup_indep.bUnion
- \+/\- *lemma* sup_indep.pairwise_disjoint
- \+/\- *lemma* sup_indep_iff_pairwise_disjoint
- \+/\- *lemma* complete_lattice.independent_iff_sup_indep
- \+/\- *def* sup_indep
- \+/\- *def* sup_indep



## [2021-12-15 19:58:06](https://github.com/leanprover-community/mathlib/commit/9525f5e)
feat(order/zorn): Added some results about chains ([#10658](https://github.com/leanprover-community/mathlib/pull/10658))
Added `chain_empty`, `chain_subsingleton`, and `chain.max_chain_of_chain`.
The first two of these are immediate yet useful lemmas. The last one is a consequence of Zorn's lemma, which generalizes Hausdorff's maximality principle.
#### Estimated changes
Modified src/order/zorn.lean
- \+ *lemma* chain_empty
- \+ *lemma* _root_.set.subsingleton.chain
- \+ *theorem* chain.max_chain_of_chain



## [2021-12-15 19:58:04](https://github.com/leanprover-community/mathlib/commit/accdb8f)
feat(measure_theory/integral/divergence_theorem): specialize for `f : ℝ → E` and `f g : ℝ × ℝ → E` ([#10616](https://github.com/leanprover-community/mathlib/pull/10616))
#### Estimated changes
Modified src/measure_theory/integral/divergence_theorem.lean
- \+ *lemma* integral_divergence_of_has_fderiv_within_at_off_countable'
- \+ *lemma* integral_divergence_of_has_fderiv_within_at_off_countable_of_equiv
- \+ *lemma* integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le
- \+ *lemma* integral2_divergence_prod_of_has_fderiv_within_at_off_countable
- \+ *theorem* integral_eq_of_has_deriv_within_at_off_countable_of_le
- \+ *theorem* integral_eq_of_has_deriv_within_at_off_countable



## [2021-12-15 18:06:00](https://github.com/leanprover-community/mathlib/commit/4ff9b82)
feat(data/set/lattice): new lemma Union_singleton_eq_range ([#10819](https://github.com/leanprover-community/mathlib/pull/10819))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* range_id'

Modified src/data/set/intervals/proj_Icc.lean

Modified src/data/set/lattice.lean
- \+ *lemma* Union_singleton_eq_range
- \+/\- *lemma* Union_of_singleton
- \+/\- *lemma* Union_of_singleton_coe
- \+/\- *lemma* Union_of_singleton
- \+/\- *lemma* Union_of_singleton_coe

Modified src/measure_theory/constructions/borel_space.lean

Modified src/measure_theory/integral/lebesgue.lean



## [2021-12-15 18:05:59](https://github.com/leanprover-community/mathlib/commit/dc732a3)
feat(logic/basic): When an If-Then-Else is not one of its arguments ([#10800](https://github.com/leanprover-community/mathlib/pull/10800))
Conditions for `ite P a b ≠ a` and `ite P a b ≠ b`.
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* imp_iff_not
- \+ *lemma* ite_ne_left_iff
- \+ *lemma* ite_ne_right_iff



## [2021-12-15 18:05:58](https://github.com/leanprover-community/mathlib/commit/7130d75)
chore(*): introduce notation for left/right/punctured nhds ([#10694](https://github.com/leanprover-community/mathlib/pull/10694))
New notation:
* `𝓝[≤] x`: the filter `nhds_within x (set.Iic x)` of left-neighborhoods of `x`;
* `𝓝[≥] x`: the filter `nhds_within x (set.Ici x)` of right-neighborhoods of `x`;
* `𝓝[<] x`: the filter `nhds_within x (set.Iio x)` of punctured left-neighborhoods of `x`;
* `𝓝[>] x`: the filter `nhds_within x (set.Ioi x)` of punctured right-neighborhoods of `x`;
* `𝓝[≠] x`: the filter `nhds_within x {x}ᶜ` of punctured neighborhoods of `x`.
#### Estimated changes
Modified src/analysis/ODE/gronwall.lean

Modified src/analysis/analytic/basic.lean

Modified src/analysis/analytic/inverse.lean

Modified src/analysis/asymptotics/asymptotics.lean

Modified src/analysis/box_integral/divergence_theorem.lean

Modified src/analysis/calculus/deriv.lean

Modified src/analysis/calculus/extend_deriv.lean

Modified src/analysis/calculus/fderiv.lean

Modified src/analysis/calculus/fderiv_symmetric.lean

Modified src/analysis/calculus/lhopital.lean

Modified src/analysis/calculus/local_extr.lean

Modified src/analysis/calculus/mean_value.lean

Modified src/analysis/calculus/specific_functions.lean

Modified src/analysis/normed/group/basic.lean
- \+/\- *lemma* tendsto_norm_nhds_within_zero
- \+/\- *lemma* tendsto_norm_nhds_within_zero

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* punctured_nhds_ne_bot
- \+/\- *lemma* punctured_nhds_ne_bot

Modified src/analysis/special_functions/exp.lean
- \+/\- *lemma* tendsto_exp_at_bot_nhds_within
- \+/\- *lemma* map_exp_at_bot
- \+/\- *lemma* comap_exp_nhds_within_Ioi_zero
- \+/\- *lemma* tendsto_exp_at_bot_nhds_within
- \+/\- *lemma* map_exp_at_bot
- \+/\- *lemma* comap_exp_nhds_within_Ioi_zero

Modified src/analysis/special_functions/log.lean
- \+/\- *lemma* tendsto_log_nhds_within_zero
- \+/\- *lemma* tendsto_log_nhds_within_zero

Modified src/analysis/special_functions/log_deriv.lean

Modified src/analysis/special_functions/pow.lean

Modified src/analysis/special_functions/trigonometric/arctan_deriv.lean

Modified src/analysis/special_functions/trigonometric/basic.lean
- \+/\- *lemma* tendsto_sin_pi_div_two
- \+/\- *lemma* tendsto_cos_pi_div_two
- \+/\- *lemma* tendsto_tan_pi_div_two
- \+/\- *lemma* tendsto_sin_neg_pi_div_two
- \+/\- *lemma* tendsto_cos_neg_pi_div_two
- \+/\- *lemma* tendsto_tan_neg_pi_div_two
- \+/\- *lemma* tendsto_sin_pi_div_two
- \+/\- *lemma* tendsto_cos_pi_div_two
- \+/\- *lemma* tendsto_tan_pi_div_two
- \+/\- *lemma* tendsto_sin_neg_pi_div_two
- \+/\- *lemma* tendsto_cos_neg_pi_div_two
- \+/\- *lemma* tendsto_tan_neg_pi_div_two

Modified src/analysis/special_functions/trigonometric/complex_deriv.lean

Modified src/analysis/special_functions/trigonometric/inverse_deriv.lean

Modified src/analysis/specific_limits.lean

Modified src/measure_theory/covering/differentiation.lean

Modified src/measure_theory/group/basic.lean

Modified src/measure_theory/integral/interval_integral.lean

Modified src/measure_theory/measure/haar_lebesgue.lean

Modified src/measure_theory/measure/hausdorff.lean
- \+/\- *lemma* mk_metric_mono
- \+/\- *lemma* mk_metric_mono
- \+/\- *lemma* mk_metric_mono
- \+/\- *lemma* mk_metric_mono

Modified src/measure_theory/measure/stieltjes.lean
- \+/\- *lemma* tendsto_left_lim
- \+/\- *lemma* tendsto_left_lim

Modified src/topology/alexandroff.lean
- \+/\- *lemma* nhds_within_compl_infty_eq
- \+/\- *lemma* nhds_within_compl_infty_eq

Modified src/topology/algebra/floor_ring.lean

Modified src/topology/algebra/group.lean

Modified src/topology/algebra/module.lean
- \+/\- *lemma* module.punctured_nhds_ne_bot
- \+/\- *lemma* module.punctured_nhds_ne_bot

Modified src/topology/algebra/ordered/basic.lean
- \+/\- *lemma* tendsto_abs_nhds_within_zero
- \+/\- *lemma* tendsto_inv_zero_at_top
- \+/\- *lemma* tendsto_inv_at_top_zero'
- \+/\- *lemma* filter.tendsto.inv_tendsto_zero
- \+/\- *lemma* comap_coe_Ioi_nhds_within_Ioi
- \+/\- *lemma* tendsto_abs_nhds_within_zero
- \+/\- *lemma* tendsto_inv_zero_at_top
- \+/\- *lemma* tendsto_inv_at_top_zero'
- \+/\- *lemma* filter.tendsto.inv_tendsto_zero
- \+/\- *lemma* comap_coe_Ioi_nhds_within_Ioi

Modified src/topology/algebra/ordered/extend_from.lean

Modified src/topology/algebra/ordered/intermediate_value.lean

Modified src/topology/algebra/ordered/left_right.lean

Modified src/topology/algebra/ordered/monotone_continuity.lean

Modified src/topology/basic.lean
- \+/\- *lemma* dense_compl_singleton
- \+/\- *lemma* closure_compl_singleton
- \+/\- *lemma* interior_singleton
- \+/\- *lemma* dense_compl_singleton
- \+/\- *lemma* closure_compl_singleton
- \+/\- *lemma* interior_singleton

Modified src/topology/continuous_on.lean
- \+/\- *theorem* nhds_within_compl_singleton_sup_pure
- \+/\- *theorem* nhds_within_compl_singleton_sup_pure

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* nhds_within_Ioi_coe_ne_bot
- \+/\- *lemma* nhds_within_Ioi_zero_ne_bot
- \+/\- *lemma* nhds_within_Ioi_coe_ne_bot
- \+/\- *lemma* nhds_within_Ioi_zero_ne_bot

Modified src/topology/local_extr.lean

Modified src/topology/local_homeomorph.lean

Modified src/topology/separation.lean
- \+/\- *lemma* dense.diff_singleton
- \+/\- *lemma* dense.diff_finset
- \+/\- *lemma* dense.diff_finite
- \+/\- *lemma* infinite_of_mem_nhds
- \+/\- *lemma* dense.diff_singleton
- \+/\- *lemma* dense.diff_finset
- \+/\- *lemma* dense.diff_finite
- \+/\- *lemma* infinite_of_mem_nhds



## [2021-12-15 18:05:57](https://github.com/leanprover-community/mathlib/commit/6043522)
refactor(order/basic): Change definition of `<` on `α × β` ([#10667](https://github.com/leanprover-community/mathlib/pull/10667))
This prove that `a < b` on `prod` is equivalent to `a.1 < b.1 ∧ a.2 ≤ b.2 ∨ a.1 ≤ b.1 ∧ a.2 < b.2`.
#### Estimated changes
Modified src/order/basic.lean
- \+/\- *lemma* le_def
- \+/\- *lemma* mk_le_mk
- \+ *lemma* lt_iff
- \+ *lemma* mk_lt_mk
- \+/\- *lemma* le_def
- \+/\- *lemma* mk_le_mk



## [2021-12-15 18:05:56](https://github.com/leanprover-community/mathlib/commit/6530769)
doc(algebra/algebra/basic): expand the docstring ([#10221](https://github.com/leanprover-community/mathlib/pull/10221))
This doesn't rule out having a better way to spell "non-unital non-associative algebra" in future, but let's document how it can be done today.
Much of this description is taken from [my talk at CICM's FMM](https://eric-wieser.github.io/fmm-2021/#/algebras).
#### Estimated changes
Modified src/algebra/algebra/basic.lean



## [2021-12-15 17:00:14](https://github.com/leanprover-community/mathlib/commit/bb51df3)
chore(computability/regular_expressions): eliminate `finish` ([#10811](https://github.com/leanprover-community/mathlib/pull/10811))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
#### Estimated changes
Modified src/computability/regular_expressions.lean



## [2021-12-15 17:00:12](https://github.com/leanprover-community/mathlib/commit/5658241)
feat(ring_theory/localization,group_theory/monoid_localization): other scalar action instances ([#10804](https://github.com/leanprover-community/mathlib/pull/10804))
As requested by @pechersky. With this instance it's possible to state:
```lean
import field_theory.ratfunc
import data.complex.basic
import ring_theory.laurent_series
noncomputable example : ratfunc ℂ ≃ₐ[ℂ] fraction_ring (polynomial ℂ) := sorry
```
#### Estimated changes
Modified src/group_theory/monoid_localization.lean
- \+ *lemma* smul_mk

Modified src/ring_theory/localization.lean
- \- *lemma* smul_mk



## [2021-12-15 17:00:11](https://github.com/leanprover-community/mathlib/commit/930ae46)
chore(analysis/special_functions/pow): remove duplicate lemmas concerning monotonicity of `rpow` ([#10794](https://github.com/leanprover-community/mathlib/pull/10794))
The lemmas `rpow_left_monotone_of_nonneg` and `rpow_left_strict_mono_of_pos` were duplicates of `monotone_rpow_of_nonneg` and `strict_mono_rpow_of_pos`, respectively. The duplicates are removed as well as references to them in mathlib in `measure_theory/function/{continuous_function_dense, lp_space}`
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \- *lemma* rpow_left_monotone_of_nonneg
- \- *lemma* rpow_left_strict_mono_of_pos

Modified src/measure_theory/function/continuous_map_dense.lean

Modified src/measure_theory/function/lp_space.lean



## [2021-12-15 15:40:27](https://github.com/leanprover-community/mathlib/commit/61949af)
doc(linear_algebra/std_basis): update module doc ([#10818](https://github.com/leanprover-community/mathlib/pull/10818))
The old module documentation for this file still referred to the removed old `is_basis`-based definitions. This PR updates the documentation to refer to the new bundled `basis`-based definitions.
#### Estimated changes
Modified src/linear_algebra/std_basis.lean



## [2021-12-15 12:44:42](https://github.com/leanprover-community/mathlib/commit/9f787c2)
doc(undergrad): Link the affine group ([#10797](https://github.com/leanprover-community/mathlib/pull/10797))
This is the statement `group (P₁ ≃ᵃ[k] P₁)`. Per the "Undergrad TODO trivial targets" wiki page, this should [match wikipedia](https://en.wikipedia.org/wiki/Affine_group), which says:
> In mathematics, the affine group or general affine group of any affine space over a field K is the group of all invertible affine transformations from the space into itself.
I guess you could also ask for the statement that `(P₁ ≃ᵃ[k] P₁) ≃ units (P₁ →ᵃ[k] P₁)`, but I'll PR that separately.
#### Estimated changes
Modified docs/undergrad.yaml



## [2021-12-15 10:36:10](https://github.com/leanprover-community/mathlib/commit/c574e38)
feat(data/finsupp/basic): Add `finsupp.erase_of_not_mem_support` ([#10689](https://github.com/leanprover-community/mathlib/pull/10689))
Analogous to `list.erase_of_not_mem`
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* erase_of_not_mem_support



## [2021-12-15 09:53:43](https://github.com/leanprover-community/mathlib/commit/03a250a)
chore(data/sym/sym2): Better lemma names ([#10801](https://github.com/leanprover-community/mathlib/pull/10801))
Renames
* `mk_has_mem` to `mk_mem_left`
* `mk_has_mem_right` to `mk_mem_right`. Just doesn't follow the convention.
* `mem_other` to `other` in lemma names. The `mem` is confusing and is only part of the fully qualified name for dot notation to work.
* `sym2.elems_iff_eq` to `mem_and_mem_iff`. `elems` is never used elsewhere. Could also be `mem_mem_iff`.
* `is_diag_iff_eq` to `mk_is_diag_iff`. The form of the argument was ambiguous. Adding `mk` solves it.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* edge_other_incident_set
- \- *lemma* edge_mem_other_incident_set

Modified src/data/sym/sym2.lean
- \+/\- *lemma* lift_mk
- \+/\- *lemma* coe_lift_symm_apply
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_map
- \+/\- *lemma* map_pair_eq
- \+/\- *lemma* map.injective
- \+ *lemma* mem_mk_left
- \+ *lemma* mem_mk_right
- \+ *lemma* other_spec
- \+ *lemma* other_mem
- \+ *lemma* mem_and_mem_iff
- \+ *lemma* mk_is_diag_iff
- \+/\- *lemma* diag_is_diag
- \+ *lemma* other_ne
- \+/\- *lemma* from_rel_proj_prop
- \+/\- *lemma* from_rel_prop
- \+/\- *lemma* rel_bool_spec
- \+ *lemma* other_spec'
- \+ *lemma* other_mem'
- \+/\- *lemma* other_invol'
- \+/\- *lemma* other_invol
- \+/\- *lemma* lift_mk
- \+/\- *lemma* coe_lift_symm_apply
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_map
- \+/\- *lemma* map_pair_eq
- \+/\- *lemma* map.injective
- \- *lemma* mk_has_mem
- \- *lemma* mk_has_mem_right
- \- *lemma* mem_other_spec
- \- *lemma* mem_other_mem
- \- *lemma* elems_iff_eq
- \- *lemma* sym2_ext
- \- *lemma* is_diag_iff_eq
- \+/\- *lemma* diag_is_diag
- \- *lemma* mem_other_ne
- \+/\- *lemma* from_rel_proj_prop
- \+/\- *lemma* from_rel_prop
- \+/\- *lemma* rel_bool_spec
- \- *lemma* mem_other_spec'
- \- *lemma* mem_other_mem'
- \+/\- *lemma* other_invol'
- \+/\- *lemma* other_invol
- \+/\- *def* lift
- \+/\- *def* map
- \+/\- *def* sym2_equiv_sym'
- \+/\- *def* lift
- \+/\- *def* map
- \+/\- *def* sym2_equiv_sym'



## [2021-12-15 07:05:10](https://github.com/leanprover-community/mathlib/commit/40cfdec)
chore(algebra/algebra/basic): alg_equiv.map_smul ([#10805](https://github.com/leanprover-community/mathlib/pull/10805))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* map_smul



## [2021-12-15 06:22:11](https://github.com/leanprover-community/mathlib/commit/8f5031a)
docs(undergrad): more links ([#10790](https://github.com/leanprover-community/mathlib/pull/10790))
The only change to existing declaration links is removing wrong claims of having proving Sylvester's law of inertia (we don't have that the number of 1 and -1 is independent from the basis).
#### Estimated changes
Modified docs/undergrad.yaml



## [2021-12-14 14:14:24](https://github.com/leanprover-community/mathlib/commit/e3eb0eb)
feat(measure_theory/integral/set_to_l1): various properties of the set_to_fun construction ([#10713](https://github.com/leanprover-community/mathlib/pull/10713))
#### Estimated changes
Modified src/measure_theory/function/l1_space.lean
- \+/\- *lemma* mem_ℒp_one_iff_integrable
- \+ *lemma* integrable.of_measure_le_smul
- \+/\- *lemma* mem_ℒp_one_iff_integrable

Modified src/measure_theory/function/lp_space.lean
- \+ *lemma* mem_ℒp.of_measure_le_smul

Modified src/measure_theory/integral/bochner.lean

Modified src/measure_theory/integral/set_to_l1.lean
- \+ *lemma* set_to_simple_func_zero'
- \+ *lemma* set_to_simple_func_congr_left
- \+ *lemma* set_to_simple_func_smul_left
- \+ *lemma* set_to_simple_func_smul_left'
- \+ *lemma* norm_set_to_simple_func_le_sum_mul_norm
- \+ *lemma* set_to_simple_func_const'
- \+ *lemma* set_to_simple_func_const
- \+ *lemma* set_to_L1s_zero_left
- \+ *lemma* set_to_L1s_zero_left'
- \+ *lemma* set_to_L1s_congr_left
- \+ *lemma* set_to_L1s_congr_measure
- \+ *lemma* set_to_L1s_add_left
- \+ *lemma* set_to_L1s_add_left'
- \+ *lemma* set_to_L1s_smul_left
- \+ *lemma* set_to_L1s_smul_left'
- \+ *lemma* set_to_L1s_neg
- \+ *lemma* set_to_L1s_sub
- \+/\- *lemma* set_to_L1s_indicator_const
- \+ *lemma* set_to_L1s_const
- \+ *lemma* set_to_L1s_clm_zero_left
- \+ *lemma* set_to_L1s_clm_zero_left'
- \+ *lemma* set_to_L1s_clm_congr_left
- \+ *lemma* set_to_L1s_clm_congr_left'
- \+ *lemma* set_to_L1s_clm_congr_measure
- \+ *lemma* set_to_L1s_clm_add_left
- \+ *lemma* set_to_L1s_clm_add_left'
- \+ *lemma* set_to_L1s_clm_smul_left
- \+ *lemma* set_to_L1s_clm_smul_left'
- \+ *lemma* set_to_L1s_clm_const
- \+ *lemma* set_to_L1_zero_left
- \+ *lemma* set_to_L1_zero_left'
- \+ *lemma* set_to_L1_congr_left
- \+ *lemma* set_to_L1_congr_left'
- \+ *lemma* set_to_L1_add_left
- \+ *lemma* set_to_L1_add_left'
- \+ *lemma* set_to_L1_smul_left
- \+ *lemma* set_to_L1_smul_left'
- \+ *lemma* set_to_L1_simple_func_indicator_const
- \+ *lemma* set_to_L1_const
- \+ *lemma* set_to_fun_congr_left
- \+ *lemma* set_to_fun_congr_left'
- \+ *lemma* set_to_fun_add_left
- \+ *lemma* set_to_fun_add_left'
- \+ *lemma* set_to_fun_smul_left
- \+ *lemma* set_to_fun_smul_left'
- \+ *lemma* set_to_fun_zero_left
- \+ *lemma* set_to_fun_zero_left'
- \+ *lemma* set_to_fun_finset_sum'
- \+ *lemma* set_to_fun_finset_sum
- \+ *lemma* set_to_fun_measure_zero
- \+ *lemma* set_to_fun_measure_zero'
- \+ *lemma* set_to_fun_const
- \+ *lemma* continuous_L1_to_L1
- \+ *lemma* set_to_fun_congr_measure_of_integrable
- \+ *lemma* set_to_fun_congr_measure
- \+ *lemma* set_to_fun_congr_measure_of_add_right
- \+ *lemma* set_to_fun_congr_measure_of_add_left
- \+ *lemma* set_to_fun_top_smul_measure
- \+ *lemma* set_to_fun_congr_smul_measure
- \+/\- *lemma* set_to_L1s_indicator_const

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* absolutely_continuous_of_le_smul



## [2021-12-14 12:57:08](https://github.com/leanprover-community/mathlib/commit/1367c19)
feat(algebraic_geometry): LocallyRingedSpace has coproducts. ([#10665](https://github.com/leanprover-community/mathlib/pull/10665))
#### Estimated changes
Created src/algebraic_geometry/locally_ringed_space/has_colimits.lean
- \+ *lemma* is_colimit_exists_rep
- \+ *lemma* colimit_exists_rep
- \+ *def* coproduct
- \+ *def* coproduct_cofan
- \+ *def* coproduct_cofan_is_colimit

Modified src/algebraic_geometry/open_immersion.lean
- \+ *lemma* sigma_ι_open_embedding
- \+ *lemma* image_preimage_is_empty

Modified src/algebraic_geometry/sheafed_space.lean

Modified src/topology/category/Top/basic.lean
- \+ *lemma* open_embedding_iff_comp_is_iso
- \+ *lemma* open_embedding_iff_is_iso_comp

Modified src/topology/maps.lean
- \+ *lemma* open_embedding_of_open_embedding_compose
- \+ *lemma* open_embedding_iff_open_embedding_compose



## [2021-12-14 11:07:17](https://github.com/leanprover-community/mathlib/commit/9078914)
feat(algebra/group): make `map_[z]pow` generic in `monoid_hom_class` ([#10749](https://github.com/leanprover-community/mathlib/pull/10749))
This PR makes `map_pow` take a `monoid_hom_class` instead of specifically a `monoid_hom`.
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *theorem* map_pow
- \+ *theorem* map_zpow'
- \+/\- *theorem* map_zpow
- \- *theorem* monoid_hom.map_pow
- \- *theorem* monoid_hom.map_zpow'
- \+/\- *theorem* map_zpow

Modified src/algebra/group_power/basic.lean
- \- *lemma* map_pow

Modified src/category_theory/preadditive/default.lean

Modified src/data/polynomial/derivative.lean

Modified src/data/polynomial/eval.lean
- \- *lemma* map_pow

Modified src/data/polynomial/lifts.lean

Modified src/field_theory/abel_ruffini.lean

Modified src/field_theory/finite/basic.lean

Modified src/field_theory/finite/galois_field.lean

Modified src/linear_algebra/tensor_product.lean
- \- *lemma* map_pow

Modified src/ring_theory/polynomial/cyclotomic/basic.lean

Modified src/ring_theory/polynomial/dickson.lean

Modified src/ring_theory/polynomial/vieta.lean

Modified src/ring_theory/power_series/well_known.lean

Modified src/ring_theory/roots_of_unity.lean



## [2021-12-14 09:33:38](https://github.com/leanprover-community/mathlib/commit/f46a7a0)
chore(data/equiv/ring): inv_fun_eq_symm ([#10779](https://github.com/leanprover-community/mathlib/pull/10779))
Like what we have for `alg_equiv`.
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+ *lemma* inv_fun_eq_symm



## [2021-12-14 09:33:37](https://github.com/leanprover-community/mathlib/commit/6d15ea4)
feat(combinatorics/simple_graph): simp lemmas about spanning coe ([#10778](https://github.com/leanprover-community/mathlib/pull/10778))
A couple of lemmas from [#8737](https://github.com/leanprover-community/mathlib/pull/8737) which don't involve connectivity, plus some extra related results.
cc @kmill
#### Estimated changes
Modified src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* top_adj_iff
- \+ *lemma* top_verts
- \+ *lemma* bot_adj_iff
- \+ *lemma* bot_verts
- \+ *lemma* spanning_coe_top
- \+ *lemma* map_spanning_top.injective
- \+/\- *def* _root_.simple_graph.to_subgraph
- \+ *def* map_spanning_top
- \+/\- *def* _root_.simple_graph.to_subgraph



## [2021-12-14 09:33:36](https://github.com/leanprover-community/mathlib/commit/05d8767)
feat(group_theory/order_of_element): additivize ([#10766](https://github.com/leanprover-community/mathlib/pull/10766))
#### Estimated changes
Modified src/algebra/pointwise.lean

Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* commute.order_of_mul_dvd_lcm
- \+ *lemma* mem_powers_iff_mem_range_order_of'
- \+/\- *lemma* pow_coprime_one
- \+/\- *lemma* pow_coprime_inv
- \- *lemma* is_periodic_pt_add_iff_nsmul_eq_zero
- \- *lemma* is_of_fin_add_order_iff_nsmul_eq_zero
- \+/\- *lemma* commute.order_of_mul_dvd_lcm
- \- *lemma* commute.order_of_mul_dvd_lcm_order_of
- \- *lemma* add_order_of_eq_prime
- \+/\- *lemma* pow_coprime_one
- \+/\- *lemma* pow_coprime_inv
- \- *lemma* image_range_add_order_of
- \- *def* pow_coprime



## [2021-12-14 07:40:55](https://github.com/leanprover-community/mathlib/commit/85cb4a8)
chore(measure_theory/decomposition/signed_hahn): Fixed a few typos ([#10777](https://github.com/leanprover-community/mathlib/pull/10777))
#### Estimated changes
Modified src/measure_theory/decomposition/signed_hahn.lean



## [2021-12-14 07:40:54](https://github.com/leanprover-community/mathlib/commit/f070a69)
move(algebra/order/lattice_group): Move from `algebra.lattice_ordered_group` ([#10763](https://github.com/leanprover-community/mathlib/pull/10763))
Rename `algebra.lattice_ordered_group` in `algebra/order/lattice_group`.
#### Estimated changes
Renamed src/algebra/lattice_ordered_group.lean to src/algebra/order/lattice_group.lean

Modified src/analysis/normed_space/lattice_ordered_group.lean



## [2021-12-14 07:40:53](https://github.com/leanprover-community/mathlib/commit/f727e12)
chore(logic/basic): tidy `ite` section and misplaced lemmas ([#10761](https://github.com/leanprover-community/mathlib/pull/10761))
Moves a few lemmas down and use `variables`.
#### Estimated changes
Modified src/data/matrix/basis.lean

Modified src/logic/basic.lean
- \+/\- *lemma* ite_eq_iff
- \+/\- *lemma* ite_eq_left_iff
- \+/\- *lemma* ite_eq_right_iff
- \+/\- *lemma* ite_eq_or_eq
- \+/\- *lemma* dite_eq_ite
- \+/\- *lemma* apply_dite
- \+/\- *lemma* apply_ite
- \+/\- *lemma* apply_dite2
- \+/\- *lemma* apply_ite2
- \+/\- *lemma* dite_apply
- \+/\- *lemma* ite_apply
- \+/\- *lemma* dite_not
- \+/\- *lemma* ite_not
- \+/\- *lemma* ite_and
- \+/\- *lemma* ite_eq_iff
- \+/\- *lemma* ite_eq_left_iff
- \+/\- *lemma* ite_eq_right_iff
- \+/\- *lemma* ite_eq_or_eq
- \+/\- *lemma* dite_eq_ite
- \+/\- *lemma* apply_dite
- \+/\- *lemma* apply_ite
- \+/\- *lemma* apply_dite2
- \+/\- *lemma* apply_ite2
- \+/\- *lemma* dite_apply
- \+/\- *lemma* ite_apply
- \+/\- *lemma* dite_not
- \+/\- *lemma* ite_not
- \+/\- *lemma* ite_and



## [2021-12-14 07:40:52](https://github.com/leanprover-community/mathlib/commit/dda8a10)
feat(data/mv_polynomial/basic): add `mv_polynomial.support_sum` ([#10731](https://github.com/leanprover-community/mathlib/pull/10731))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* support_finset_sum

Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* support_zero
- \+ *lemma* support_sum



## [2021-12-14 07:40:51](https://github.com/leanprover-community/mathlib/commit/9af43e4)
feat(analysis/inner_product_space/basic): inner product as a (continuous) sesquilinear map ([#10684](https://github.com/leanprover-community/mathlib/pull/10684))
This PR replaces `inner_right (v : E) : E →L[𝕜] 𝕜` (the inner product with a fixed left element as a continuous linear map) by `innerₛₗ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 ` and `innerSL : E →L⋆[𝕜] E →L[𝕜] 𝕜 `, which bundle the inner product as a sesquilinear map and as a continuous sesquilinear map respectively.
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* innerₛₗ_apply_coe
- \+ *lemma* innerₛₗ_apply
- \+ *lemma* innerSL_apply_coe
- \+ *lemma* innerSL_apply
- \+ *lemma* innerSL_apply_norm
- \+/\- *lemma* orthogonal_eq_inter
- \- *lemma* inner_right_coe
- \- *lemma* inner_right_apply
- \+/\- *lemma* orthogonal_eq_inter
- \+ *def* innerₛₗ
- \+ *def* innerSL
- \- *def* inner_right

Modified src/analysis/inner_product_space/calculus.lean

Modified src/analysis/inner_product_space/dual.lean
- \+ *lemma* innerSL_norm

Modified src/analysis/inner_product_space/rayleigh.lean

Modified src/analysis/normed_space/star.lean

Modified src/geometry/manifold/instances/sphere.lean

Modified src/measure_theory/integral/set_integral.lean



## [2021-12-14 05:36:16](https://github.com/leanprover-community/mathlib/commit/f3fa5e3)
feat(data/mv_polynomial/variables): add `mv_polynomial.degree_of_zero` ([#10768](https://github.com/leanprover-community/mathlib/pull/10768))
#### Estimated changes
Modified src/data/mv_polynomial/variables.lean
- \+ *lemma* degree_of_zero



## [2021-12-14 05:36:15](https://github.com/leanprover-community/mathlib/commit/ee78812)
feat(number_theory/padics/padic_norm): lemmas ([#10765](https://github.com/leanprover-community/mathlib/pull/10765))
#### Estimated changes
Modified src/number_theory/padics/padic_norm.lean
- \+/\- *lemma* padic_val_nat_self
- \+/\- *lemma* padic_val_nat_self
- \- *lemma* padic_val_nat_prime_pow



## [2021-12-14 05:36:14](https://github.com/leanprover-community/mathlib/commit/9b1a832)
feat(data/nat/prime): dvd_of_factors_subperm ([#10764](https://github.com/leanprover-community/mathlib/pull/10764))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* dvd_of_factors_subperm



## [2021-12-14 05:36:13](https://github.com/leanprover-community/mathlib/commit/d9edeea)
refactor(linear_algebra/orientation): add refl, symm, and trans lemma ([#10753](https://github.com/leanprover-community/mathlib/pull/10753))
This restates the `reflexive`, `symmetric`, and `transitive` lemmas in a form understood by `@[refl]`, `@[symm]`, and `@[trans]`.
As a bonus, these versions also work with dot notation.
I've discarded the original statements, since they're always recoverable via the fields of equivalence_same_ray, and keeping them is just noise.
#### Estimated changes
Modified src/linear_algebra/orientation.lean
- \+ *lemma* same_ray.refl
- \+ *lemma* same_ray.symm
- \+ *lemma* same_ray.trans
- \+ *lemma* same_ray_comm
- \+/\- *lemma* equivalence_same_ray
- \- *lemma* symmetric_same_ray
- \- *lemma* transitive_same_ray
- \- *lemma* reflexive_same_ray
- \+/\- *lemma* equivalence_same_ray



## [2021-12-14 05:36:12](https://github.com/leanprover-community/mathlib/commit/0000497)
feat(order/basic, order/bounded_order): Generalized `preorder` to `has_lt` ([#10695](https://github.com/leanprover-community/mathlib/pull/10695))
This is a continuation of [#10664](https://github.com/leanprover-community/mathlib/pull/10664).
#### Estimated changes
Modified src/order/basic.lean
- \+/\- *lemma* no_top
- \+/\- *lemma* no_bot
- \+/\- *lemma* no_top
- \+/\- *lemma* no_bot

Modified src/order/bounded_order.lean
- \+ *lemma* not_lt_none
- \+/\- *lemma* well_founded_lt
- \+/\- *lemma* well_founded_lt
- \+/\- *lemma* well_founded_lt
- \+/\- *lemma* well_founded_lt
- \+ *theorem* not_none_lt



## [2021-12-14 04:24:23](https://github.com/leanprover-community/mathlib/commit/32c24f1)
chore(set_theory/ordinal_arithmetic): simplified proof of `is_normal.le_self` ([#10770](https://github.com/leanprover-community/mathlib/pull/10770))
Thanks to [#10732](https://github.com/leanprover-community/mathlib/pull/10732), this proof is now a one-liner.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean



## [2021-12-14 01:29:31](https://github.com/leanprover-community/mathlib/commit/cd462cd)
feat(topology/algebra/*, analysis/normed_space/operator_norm): construct bundled {monoid_hom, linear_map} from limits of such maps ([#10700](https://github.com/leanprover-community/mathlib/pull/10700))
Given a function which is a pointwise limit of {`monoid_hom`, `add_monoid_hom`, `linear_map`} maps, construct a bundled version of the corresponding type with that function as its `to_fun`. Then this construction is used to replace the existing in-proof construction that the continuous linear maps into a banach space is itself complete.
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean

Modified src/topology/algebra/module.lean
- \+ *def* linear_map_of_tendsto

Modified src/topology/algebra/monoid.lean
- \+ *def* monoid_hom_of_tendsto



## [2021-12-14 00:37:44](https://github.com/leanprover-community/mathlib/commit/77e5248)
feat(algebra/triv_sq_zero_ext): universal property ([#10754](https://github.com/leanprover-community/mathlib/pull/10754))
#### Estimated changes
Modified src/algebra/triv_sq_zero_ext.lean
- \+ *lemma* ind
- \+ *lemma* linear_map_ext
- \+ *lemma* alg_hom_ext
- \+ *lemma* alg_hom_ext'
- \+ *lemma* lift_aux_apply_inr
- \+ *lemma* lift_aux_comp_inr_hom
- \+ *lemma* lift_aux_inr_hom
- \+ *def* lift_aux
- \+ *def* lift



## [2021-12-13 23:34:29](https://github.com/leanprover-community/mathlib/commit/c3391c2)
feat(analysis/convex/simplicial_complex): Simplicial complexes ([#9762](https://github.com/leanprover-community/mathlib/pull/9762))
This introduces simplicial complexes in modules.
#### Estimated changes
Created src/analysis/convex/simplicial_complex/basic.lean
- \+ *lemma* mem_space_iff
- \+ *lemma* convex_hull_subset_space
- \+ *lemma* convex_hull_inter_convex_hull
- \+ *lemma* disjoint_or_exists_inter_eq_convex_hull
- \+ *lemma* mem_vertices
- \+ *lemma* vertices_eq
- \+ *lemma* vertices_subset_space
- \+ *lemma* vertex_mem_convex_hull_iff
- \+ *lemma* face_subset_face_iff
- \+ *lemma* mem_facets
- \+ *lemma* facets_subset
- \+ *lemma* not_facet_iff_subface
- \+ *lemma* faces_bot
- \+ *lemma* space_bot
- \+ *lemma* facets_bot
- \+ *def* space
- \+ *def* of_erase
- \+ *def* of_subcomplex
- \+ *def* vertices
- \+ *def* facets



## [2021-12-13 21:33:22](https://github.com/leanprover-community/mathlib/commit/7181b3a)
chore(order/hom): rearrange definitions of `order_{hom,iso,embedding}` ([#10752](https://github.com/leanprover-community/mathlib/pull/10752))
We symmetrize the locations of `rel_{hom,iso,embedding}` and `order_{hom,iso,embedding}` by putting the `rel_` definitions in `order/rel_iso.lean` and the `order_` definitions in `order/hom/basic.lean`. (`order_hom.lean` needed to be split up to fix an import loop.) Requested by @YaelDillies.
## Moved definitions
 * `order_hom`, `order_iso`, `order_embedding` are now in `order/hom/basic.lean`
 * `order_hom.has_sup` ... `order_hom.complete_lattice` are now in `order/hom/lattice.lean`
## Other changes
Some import cleanup.
#### Estimated changes
Modified src/algebra/lie/solvable.lean

Modified src/algebra/order/monoid.lean

Modified src/combinatorics/set_family/shadow.lean

Modified src/data/finset/option.lean

Modified src/data/nat/fib.lean

Modified src/linear_algebra/eigenspace.lean

Modified src/order/category/Preorder.lean

Modified src/order/closure.lean

Modified src/order/fixed_points.lean

Created src/order/hom/basic.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_fun_mk
- \+ *lemma* ext
- \+ *lemma* le_def
- \+ *lemma* coe_le_coe
- \+ *lemma* mk_le_mk
- \+ *lemma* apply_mono
- \+ *lemma* curry_apply
- \+ *lemma* curry_symm_apply
- \+ *lemma* comp_mono
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* const_comp
- \+ *lemma* comp_const
- \+ *lemma* prod_mono
- \+ *lemma* comp_prod_comp_same
- \+ *lemma* fst_prod_snd
- \+ *lemma* fst_comp_prod
- \+ *lemma* snd_comp_prod
- \+ *lemma* order_hom_eq_id
- \+ *lemma* rel_embedding.order_embedding_of_lt_embedding_apply
- \+ *lemma* lt_embedding_apply
- \+ *lemma* eq_iff_eq
- \+ *lemma* coe_of_map_le_iff
- \+ *lemma* coe_of_strict_mono
- \+ *lemma* rel_embedding.to_order_hom_injective
- \+ *lemma* coe_to_order_embedding
- \+ *lemma* range_eq
- \+ *lemma* apply_eq_iff_eq
- \+ *lemma* coe_refl
- \+ *lemma* refl_apply
- \+ *lemma* refl_to_equiv
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+ *lemma* symm_refl
- \+ *lemma* apply_eq_iff_eq_symm_apply
- \+ *lemma* symm_symm
- \+ *lemma* symm_injective
- \+ *lemma* to_equiv_symm
- \+ *lemma* symm_image_image
- \+ *lemma* image_symm_image
- \+ *lemma* image_eq_preimage
- \+ *lemma* preimage_symm_preimage
- \+ *lemma* symm_preimage_preimage
- \+ *lemma* image_preimage
- \+ *lemma* preimage_image
- \+ *lemma* coe_trans
- \+ *lemma* trans_apply
- \+ *lemma* refl_trans
- \+ *lemma* trans_refl
- \+ *lemma* le_iff_le
- \+ *lemma* le_symm_apply
- \+ *lemma* symm_apply_le
- \+ *lemma* lt_iff_lt
- \+ *lemma* fun_unique_symm_apply
- \+ *lemma* coe_to_order_iso
- \+ *lemma* to_order_iso_to_equiv
- \+ *lemma* order_iso.map_bot'
- \+ *lemma* order_iso.map_bot
- \+ *lemma* order_iso.map_top'
- \+ *lemma* order_iso.map_top
- \+ *lemma* order_embedding.map_inf_le
- \+ *lemma* order_iso.map_inf
- \+ *lemma* disjoint.map_order_iso
- \+ *lemma* disjoint_map_order_iso_iff
- \+ *lemma* order_embedding.le_map_sup
- \+ *lemma* order_iso.map_sup
- \+ *lemma* order_iso.is_compl
- \+ *lemma* order_iso.is_complemented
- \+ *theorem* le_iff_le
- \+ *theorem* lt_iff_lt
- \+ *theorem* symm_apply_eq
- \+ *theorem* order_iso.is_compl_iff
- \+ *theorem* order_iso.is_complemented_iff
- \+ *def* id
- \+ *def* curry
- \+ *def* comp
- \+ *def* compₘ
- \+ *def* const
- \+ *def* prodₘ
- \+ *def* diag
- \+ *def* on_diag
- \+ *def* fst
- \+ *def* snd
- \+ *def* prod_iso
- \+ *def* prod_map
- \+ *def* _root_.pi.eval_order_hom
- \+ *def* coe_fn_hom
- \+ *def* apply
- \+ *def* pi
- \+ *def* pi_iso
- \+ *def* subtype.val
- \+ *def* unique
- \+ *def* dual_iso
- \+ *def* rel_embedding.order_embedding_of_lt_embedding
- \+ *def* lt_embedding
- \+ *def* of_map_le_iff
- \+ *def* of_strict_mono
- \+ *def* subtype
- \+ *def* to_order_hom
- \+ *def* to_order_hom
- \+ *def* to_order_embedding
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans
- \+ *def* of_cmp_eq_cmp
- \+ *def* set_congr
- \+ *def* set.univ
- \+ *def* fun_unique
- \+ *def* to_order_iso

Created src/order/hom/lattice.lean
- \+ *lemma* Inf_apply
- \+ *lemma* infi_apply
- \+ *lemma* coe_infi
- \+ *lemma* Sup_apply
- \+ *lemma* supr_apply
- \+ *lemma* coe_supr
- \+ *lemma* iterate_sup_le_sup_iff

Modified src/order/omega_complete_partial_order.lean

Deleted src/order/order_hom.lean
- \- *lemma* to_fun_eq_coe
- \- *lemma* coe_fun_mk
- \- *lemma* ext
- \- *lemma* le_def
- \- *lemma* coe_le_coe
- \- *lemma* mk_le_mk
- \- *lemma* apply_mono
- \- *lemma* curry_apply
- \- *lemma* curry_symm_apply
- \- *lemma* comp_mono
- \- *lemma* comp_id
- \- *lemma* id_comp
- \- *lemma* const_comp
- \- *lemma* comp_const
- \- *lemma* prod_mono
- \- *lemma* comp_prod_comp_same
- \- *lemma* fst_prod_snd
- \- *lemma* fst_comp_prod
- \- *lemma* snd_comp_prod
- \- *lemma* order_hom_eq_id
- \- *lemma* Inf_apply
- \- *lemma* infi_apply
- \- *lemma* coe_infi
- \- *lemma* Sup_apply
- \- *lemma* supr_apply
- \- *lemma* coe_supr
- \- *lemma* iterate_sup_le_sup_iff
- \- *lemma* rel_embedding.to_order_hom_injective
- \- *def* id
- \- *def* curry
- \- *def* comp
- \- *def* compₘ
- \- *def* const
- \- *def* prodₘ
- \- *def* diag
- \- *def* on_diag
- \- *def* fst
- \- *def* snd
- \- *def* prod_iso
- \- *def* prod_map
- \- *def* _root_.pi.eval_order_hom
- \- *def* coe_fn_hom
- \- *def* apply
- \- *def* pi
- \- *def* pi_iso
- \- *def* subtype.val
- \- *def* unique
- \- *def* dual_iso
- \- *def* to_order_hom
- \- *def* to_order_hom

Modified src/order/order_iso_nat.lean

Modified src/order/partial_sups.lean

Modified src/order/rel_iso.lean
- \- *lemma* order_embedding_of_lt_embedding_apply
- \- *lemma* lt_embedding_apply
- \- *lemma* eq_iff_eq
- \- *lemma* coe_of_map_le_iff
- \- *lemma* coe_of_strict_mono
- \- *lemma* coe_to_order_embedding
- \- *lemma* range_eq
- \- *lemma* apply_eq_iff_eq
- \- *lemma* coe_refl
- \- *lemma* refl_apply
- \- *lemma* refl_to_equiv
- \- *lemma* apply_symm_apply
- \- *lemma* symm_apply_apply
- \- *lemma* symm_refl
- \- *lemma* apply_eq_iff_eq_symm_apply
- \- *lemma* symm_symm
- \- *lemma* symm_injective
- \- *lemma* to_equiv_symm
- \- *lemma* symm_image_image
- \- *lemma* image_symm_image
- \- *lemma* image_eq_preimage
- \- *lemma* preimage_symm_preimage
- \- *lemma* symm_preimage_preimage
- \- *lemma* image_preimage
- \- *lemma* preimage_image
- \- *lemma* coe_trans
- \- *lemma* trans_apply
- \- *lemma* refl_trans
- \- *lemma* trans_refl
- \- *lemma* le_iff_le
- \- *lemma* le_symm_apply
- \- *lemma* symm_apply_le
- \- *lemma* lt_iff_lt
- \- *lemma* fun_unique_symm_apply
- \- *lemma* coe_to_order_iso
- \- *lemma* to_order_iso_to_equiv
- \- *lemma* order_iso.map_bot'
- \- *lemma* order_iso.map_bot
- \- *lemma* order_iso.map_top'
- \- *lemma* order_iso.map_top
- \- *lemma* order_embedding.map_inf_le
- \- *lemma* order_iso.map_inf
- \- *lemma* disjoint.map_order_iso
- \- *lemma* disjoint_map_order_iso_iff
- \- *lemma* order_embedding.le_map_sup
- \- *lemma* order_iso.map_sup
- \- *lemma* order_iso.is_compl
- \- *lemma* order_iso.is_complemented
- \- *theorem* le_iff_le
- \- *theorem* lt_iff_lt
- \- *theorem* symm_apply_eq
- \- *theorem* order_iso.is_compl_iff
- \- *theorem* order_iso.is_complemented_iff
- \- *def* order_embedding_of_lt_embedding
- \- *def* lt_embedding
- \- *def* of_map_le_iff
- \- *def* of_strict_mono
- \- *def* subtype
- \- *def* to_order_embedding
- \- *def* refl
- \- *def* symm
- \- *def* trans
- \- *def* of_cmp_eq_cmp
- \- *def* set_congr
- \- *def* set.univ
- \- *def* fun_unique
- \- *def* to_order_iso



## [2021-12-13 19:31:53](https://github.com/leanprover-community/mathlib/commit/b351ca9)
chore(algebra/algebra/tower): golf ext lemma ([#10756](https://github.com/leanprover-community/mathlib/pull/10756))
It turns out that we have both `algebra.ext` and `algebra.algebra_ext`, with slightly different statements.
This changes one to be proved in terms of the other.
#### Estimated changes
Modified src/algebra/algebra/tower.lean



## [2021-12-13 19:31:52](https://github.com/leanprover-community/mathlib/commit/3b2cf53)
feat(order/well_founded) Added `strict_mono.id_le_of_wo` ([#10732](https://github.com/leanprover-community/mathlib/pull/10732))
This generalizes `strict_mono.id_le`.
#### Estimated changes
Modified src/order/well_founded.lean
- \+ *theorem* well_founded.self_le_of_strict_mono



## [2021-12-13 19:31:51](https://github.com/leanprover-community/mathlib/commit/c895ddd)
feat(topology/algebra/group): add homeomorph.prod_units ([#10725](https://github.com/leanprover-community/mathlib/pull/10725))
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *def* homeomorph.prod_units



## [2021-12-13 19:31:50](https://github.com/leanprover-community/mathlib/commit/ad88a83)
feat(probability_theory/martingale): add super/sub-martingales ([#10710](https://github.com/leanprover-community/mathlib/pull/10710))
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean

Modified src/probability_theory/martingale.lean
- \+ *lemma* set_integral_eq
- \+ *lemma* supermartingale
- \+ *lemma* submartingale
- \+ *lemma* martingale_iff
- \+ *lemma* adapted
- \+ *lemma* measurable
- \+ *lemma* integrable
- \+ *lemma* condexp_ae_le
- \+ *lemma* set_integral_le
- \+ *lemma* add
- \+ *lemma* add_martingale
- \+ *lemma* neg
- \+ *lemma* adapted
- \+ *lemma* measurable
- \+ *lemma* integrable
- \+ *lemma* ae_le_condexp
- \+ *lemma* add
- \+ *lemma* add_martingale
- \+ *lemma* neg
- \+ *lemma* set_integral_le
- \+ *lemma* sub_supermartingale
- \+ *lemma* sub_martingale
- \+ *lemma* sub_submartingale
- \+ *lemma* sub_martingale
- \+ *lemma* smul_nonneg
- \+ *lemma* smul_nonpos
- \+ *lemma* smul_nonneg
- \+ *lemma* smul_nonpos
- \+ *def* supermartingale
- \+ *def* submartingale



## [2021-12-13 19:31:49](https://github.com/leanprover-community/mathlib/commit/c7e355d)
feat(algebra/big_operators/finprod): add div lemmas ([#10472](https://github.com/leanprover-community/mathlib/pull/10472))
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_inv_distrib₀
- \+ *lemma* finprod_cond_ne
- \+/\- *lemma* finprod_div_distrib
- \+ *lemma* finprod_div_distrib₀
- \+ *lemma* finprod_mem_inv_distrib₀
- \+/\- *lemma* finprod_mem_div_distrib
- \+ *lemma* finprod_mem_div_distrib₀
- \+ *lemma* mul_finprod_cond_ne
- \+/\- *lemma* finprod_div_distrib
- \+/\- *lemma* finprod_mem_div_distrib

Modified src/data/equiv/mul_add.lean
- \+ *lemma* mul_equiv.inv₀_symm
- \+ *def* mul_equiv.inv₀



## [2021-12-13 17:35:09](https://github.com/leanprover-community/mathlib/commit/0c0ee7b)
refactor(data/set/pairwise): Make arguments of `set.pairwise` semi-implicit ([#10740](https://github.com/leanprover-community/mathlib/pull/10740))
The previous definition was `∀ x ∈ s, ∀ y ∈ s, x ≠ y → r x y`. It now is `∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → r x y`.
The explicitness resulted in a lot of useless `_` and general pain using `set.pairwise`, `set.pairwise_disjoint`, `zorn.chain`, `is_antichain`...
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+/\- *lemma* finprod_mem_sUnion
- \+/\- *lemma* finprod_mem_sUnion

Modified src/analysis/box_integral/partition/basic.lean

Modified src/analysis/convex/basic.lean

Modified src/analysis/convex/function.lean

Modified src/analysis/convex/strict.lean

Modified src/combinatorics/simple_graph/partition.lean

Modified src/data/finset/pairwise.lean

Modified src/data/list/pairwise.lean

Modified src/data/mv_polynomial/variables.lean

Modified src/data/set/pairwise.lean

Modified src/geometry/euclidean/circumcenter.lean

Modified src/group_theory/perm/cycle_type.lean

Modified src/group_theory/perm/cycles.lean

Modified src/measure_theory/covering/besicovitch.lean

Modified src/measure_theory/covering/vitali.lean

Modified src/order/antichain.lean

Modified src/order/sup_indep.lean

Modified src/order/zorn.lean

Modified src/ring_theory/coprime/lemmas.lean

Modified src/topology/bases.lean

Modified src/topology/uniform_space/separation.lean



## [2021-12-13 15:33:28](https://github.com/leanprover-community/mathlib/commit/ee8de4c)
doc(linear_algebra/finite_dimensional): update doc to new definition ([#10758](https://github.com/leanprover-community/mathlib/pull/10758))
`finite_dimensional` is now (since a couple of months) defined to be `module.finite`. The lines modified by this PR are about the old definition.
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean



## [2021-12-13 15:33:27](https://github.com/leanprover-community/mathlib/commit/108eb0b)
feat(combinatorics/additive/salem_spencer): Salem-Spencer sets and Roth numbers ([#10509](https://github.com/leanprover-community/mathlib/pull/10509))
This defines Salem-Spencer sets and Roth numbers in (additive) monoids.
#### Estimated changes
Modified src/algebra/regular/basic.lean
- \+ *lemma* mul_left_embedding_eq_mul_right_embedding

Created src/combinatorics/additive/salem_spencer.lean
- \+ *lemma* mul_salem_spencer.mono
- \+ *lemma* mul_salem_spencer_empty
- \+ *lemma* set.subsingleton.mul_salem_spencer
- \+ *lemma* mul_salem_spencer_singleton
- \+ *lemma* mul_salem_spencer.prod
- \+ *lemma* mul_salem_spencer_pi
- \+ *lemma* mul_salem_spencer_insert
- \+ *lemma* mul_salem_spencer_pair
- \+ *lemma* mul_salem_spencer.mul_left
- \+ *lemma* mul_salem_spencer.mul_right
- \+ *lemma* mul_salem_spencer_mul_left_iff
- \+ *lemma* mul_salem_spencer_mul_right_iff
- \+ *lemma* mul_salem_spencer_insert_of_lt
- \+ *lemma* mul_salem_spencer.mul_left₀
- \+ *lemma* mul_salem_spencer.mul_right₀
- \+ *lemma* mul_salem_spencer_mul_left_iff₀
- \+ *lemma* mul_salem_spencer_mul_right_iff₀
- \+ *lemma* add_salem_spencer_iff_eq_right
- \+ *lemma* mul_roth_number_le
- \+ *lemma* mul_roth_number_spec
- \+ *lemma* mul_salem_spencer.le_mul_roth_number
- \+ *lemma* mul_salem_spencer.roth_number_eq
- \+ *lemma* mul_roth_number_empty
- \+ *lemma* mul_roth_number_singleton
- \+ *lemma* mul_roth_number_union_le
- \+ *lemma* le_mul_roth_number_product
- \+ *lemma* mul_roth_number_lt_of_forall_not_mul_salem_spencer
- \+ *lemma* mul_roth_number_map_mul_left
- \+ *lemma* mul_roth_number_map_mul_right
- \+ *lemma* roth_number_nat_def
- \+ *lemma* roth_number_nat_le
- \+ *lemma* roth_number_nat_spec
- \+ *lemma* add_salem_spencer.le_roth_number_nat
- \+ *lemma* roth_number_nat_add_le
- \+ *lemma* roth_number_nat_zero
- \+ *lemma* add_roth_number_Ico
- \+ *lemma* roth_number_nat_is_O_with_id
- \+ *lemma* roth_number_nat_is_O_id
- \+ *def* mul_salem_spencer
- \+ *def* mul_roth_number
- \+ *def* roth_number_nat

Modified src/data/finset/preimage.lean
- \+ *lemma* preimage_subset
- \+ *lemma* subset_map_iff



## [2021-12-13 15:33:26](https://github.com/leanprover-community/mathlib/commit/e174736)
feat(ring_theory/unique_factorization_domain): add count lemmas ([#10475](https://github.com/leanprover-community/mathlib/pull/10475))
#### Estimated changes
Modified src/algebra/associated.lean

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* factors_subsingleton
- \+ *lemma* factors_eq_none_iff_zero
- \+ *lemma* factors_eq_some_iff_ne_zero
- \+ *theorem* eq_factors_of_eq_counts
- \+ *theorem* eq_of_eq_counts
- \+ *theorem* count_ne_zero_iff_dvd



## [2021-12-13 15:33:25](https://github.com/leanprover-community/mathlib/commit/efbbb76)
feat(ring_theory/graded_algebra): `homogeneous_element` ([#10118](https://github.com/leanprover-community/mathlib/pull/10118))
This pr is about what `homogeneous_element` of graded ring is.
We need this definition to make the definition of homogeneous ideal more natural, i.e. we can say that a homogeneous ideal is just an ideal spanned by homogeneous elements.
#### Estimated changes
Modified src/algebra/direct_sum/internal.lean
- \+ *lemma* set_like.is_homogeneous_zero_submodule
- \+ *lemma* set_like.is_homogeneous.smul

Modified src/algebra/graded_monoid.lean
- \+ *lemma* set_like.is_homogeneous_one
- \+ *lemma* set_like.is_homogeneous.mul
- \+ *def* set_like.is_homogeneous
- \+ *def* set_like.homogeneous_submonoid

Modified src/ring_theory/graded_algebra/basic.lean
- \+/\- *lemma* graded_algebra.mem_support_iff
- \+/\- *lemma* graded_algebra.mem_support_iff



## [2021-12-13 13:35:58](https://github.com/leanprover-community/mathlib/commit/1589c7b)
feat(linear_algebra/determinant): determinant of a linear equivalence as a unit ([#10751](https://github.com/leanprover-community/mathlib/pull/10751))
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* coe_det
- \+ *lemma* coe_inv_det
- \+ *lemma* det_refl
- \+ *lemma* det_trans
- \+ *lemma* det_symm



## [2021-12-13 13:35:57](https://github.com/leanprover-community/mathlib/commit/324a605)
chore(order): rename `preorder_hom` to `order_hom` ([#10750](https://github.com/leanprover-community/mathlib/pull/10750))
For consistency with `order_embedding` and `order_iso`, this PR renames `preorder_hom` to `order_hom`, at the request of @YaelDillies.
#### Estimated changes
Modified src/algebra/lie/solvable.lean

Modified src/algebraic_topology/cech_nerve.lean

Modified src/algebraic_topology/simplex_category.lean
- \+ *lemma* mk_to_order_hom
- \+ *lemma* to_order_hom_mk
- \+ *lemma* mk_to_order_hom_apply
- \- *lemma* mk_to_preorder_hom
- \- *lemma* to_preorder_hom_mk
- \- *lemma* mk_to_preorder_hom_apply
- \+ *def* to_order_hom
- \- *def* to_preorder_hom

Modified src/algebraic_topology/simplicial_set.lean
- \+ *def* as_order_hom
- \- *def* as_preorder_hom

Modified src/control/lawful_fix.lean

Modified src/data/finset/option.lean

Modified src/linear_algebra/eigenspace.lean

Modified src/order/category/Preorder.lean

Modified src/order/category/omega_complete_partial_order.lean

Modified src/order/closure.lean

Modified src/order/fixed_points.lean

Modified src/order/omega_complete_partial_order.lean
- \+/\- *lemma* map_id
- \+/\- *lemma* continuous_id
- \+/\- *lemma* continuous_const
- \+/\- *lemma* map_id
- \+/\- *lemma* continuous_id
- \+/\- *lemma* continuous_const

Renamed src/order/preorder_hom.lean to src/order/order_hom.lean
- \+ *lemma* order_hom_eq_id
- \+ *lemma* rel_embedding.to_order_hom_injective
- \- *lemma* preorder_hom_eq_id
- \- *lemma* rel_embedding.to_preorder_hom_injective
- \+ *def* _root_.pi.eval_order_hom
- \+ *def* to_order_hom
- \+ *def* to_order_hom
- \- *def* _root_.pi.eval_preorder_hom
- \- *def* to_preorder_hom
- \- *def* to_preorder_hom

Modified src/order/order_iso_nat.lean

Modified src/order/partial_sups.lean

Modified src/topology/omega_complete_partial_order.lean

Modified src/topology/opens.lean
- \+/\- *lemma* comap_id
- \+/\- *lemma* comap_id



## [2021-12-13 13:35:56](https://github.com/leanprover-community/mathlib/commit/35cd7c0)
refactor(set_theory/ordinal_arithmetic) Separate `is_normal.lt_iff` ([#10745](https://github.com/leanprover-community/mathlib/pull/10745))
We split off `is_normal.strict_mono` from `is_normal.lt_iff`. The reasoning is that normal functions are usually defined as being strictly monotone, so this should be a separate theorem.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* is_normal.strict_mono
- \+/\- *theorem* is_normal.lt_iff
- \+/\- *theorem* is_normal.lt_iff



## [2021-12-13 11:53:34](https://github.com/leanprover-community/mathlib/commit/7697ec6)
feat(analysis/special_function/integrals): integral of `x ^ r`, `r : ℝ`, and `x ^ n`, `n : ℤ` ([#10650](https://github.com/leanprover-community/mathlib/pull/10650))
Also generalize `has_deriv_at.div_const` etc.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_at.div_const
- \+ *lemma* has_deriv_within_at.div_const
- \+ *lemma* has_strict_deriv_at.div_const
- \+/\- *lemma* differentiable_within_at.div_const
- \+/\- *lemma* differentiable_at.div_const
- \+/\- *lemma* differentiable_on.div_const
- \+/\- *lemma* differentiable.div_const
- \+/\- *lemma* deriv_within_div_const
- \+/\- *lemma* deriv_div_const
- \+/\- *lemma* differentiable_within_at.div_const
- \+/\- *lemma* differentiable_at.div_const
- \+/\- *lemma* differentiable_on.div_const
- \+/\- *lemma* differentiable.div_const
- \+/\- *lemma* deriv_within_div_const
- \+/\- *lemma* deriv_div_const

Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* interval_integrable_zpow
- \+ *lemma* interval_integrable_rpow
- \+ *lemma* integral_rpow
- \+ *lemma* integral_zpow
- \+/\- *lemma* integral_pow
- \+/\- *lemma* integral_pow

Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* rpow_int_cast
- \+/\- *lemma* rpow_nat_cast
- \+/\- *lemma* rpow_int_cast
- \+/\- *lemma* rpow_nat_cast



## [2021-12-13 09:36:41](https://github.com/leanprover-community/mathlib/commit/779517b)
feat(algebra/order/floor): Floor of `a / n` and other lemmas ([#10748](https://github.com/leanprover-community/mathlib/pull/10748))
A few floor lemmas + one `tsub` lemma
#### Estimated changes
Modified src/algebra/order/floor.lean
- \+ *lemma* floor_le_ceil
- \+ *lemma* floor_sub_nat
- \+ *lemma* floor_div_nat
- \+ *lemma* floor_div_eq_div
- \+ *lemma* floor_le_ceil

Modified src/algebra/order/sub.lean
- \+ *lemma* tsub_nonpos



## [2021-12-13 09:36:40](https://github.com/leanprover-community/mathlib/commit/563c364)
chore(topology/maps): golf, use section vars ([#10747](https://github.com/leanprover-community/mathlib/pull/10747))
Also add `quotient_map.is_closed_preimage`
#### Estimated changes
Modified src/topology/maps.lean
- \- *lemma* inducing.continuous
- \- *lemma* inducing.is_open_map



## [2021-12-13 09:36:38](https://github.com/leanprover-community/mathlib/commit/10fb7f9)
feat(archive/imo): IMO 2005 problem 4 (modular arithmetic) ([#10746](https://github.com/leanprover-community/mathlib/pull/10746))
#### Estimated changes
Created archive/imo/imo2005_q4.lean
- \+ *lemma* find_specified_factor
- \+ *def* a

Modified src/field_theory/finite/basic.lean
- \+ *lemma* int.modeq.pow_card_sub_one_eq_one



## [2021-12-13 09:36:37](https://github.com/leanprover-community/mathlib/commit/9d73418)
split(data/set/prod): split off `data.set.basic` ([#10739](https://github.com/leanprover-community/mathlib/pull/10739))
This moves `set.prod`, `set.pi` and `set.diagonal` from `data.set.basic` to a new file `data.set.prod`.
I'm crediting
* Mario for `set.prod` from bd013e8089378e8057dc7e93c9eaf2c8ebaf25a2
* Johannes for `set.pi` from da7bbd7fc2c80a785f7992bb7751304f6cafe235
* Patrick for `set.diagonal` from [#3118](https://github.com/leanprover-community/mathlib/pull/3118)
#### Estimated changes
Modified archive/imo/imo1972_b2.lean

Modified archive/imo/imo2008_q2.lean

Modified src/algebra/ring/basic.lean

Modified src/data/set/basic.lean
- \+ *lemma* image_swap_eq_preimage_swap
- \- *lemma* mem_diagonal
- \- *lemma* preimage_coe_coe_diagonal
- \- *lemma* diagonal_eq_range
- \- *lemma* prod_eq
- \- *lemma* mk_mem_prod
- \- *lemma* prod_subset_iff
- \- *lemma* forall_prod_set
- \- *lemma* exists_prod_set
- \- *lemma* univ_prod
- \- *lemma* prod_univ
- \- *lemma* prod_preimage_left
- \- *lemma* prod_preimage_right
- \- *lemma* preimage_prod_map_prod
- \- *lemma* mk_preimage_prod
- \- *lemma* mk_preimage_prod_left
- \- *lemma* mk_preimage_prod_right
- \- *lemma* mk_preimage_prod_left_eq_empty
- \- *lemma* mk_preimage_prod_right_eq_empty
- \- *lemma* mk_preimage_prod_left_eq_if
- \- *lemma* mk_preimage_prod_right_eq_if
- \- *lemma* mk_preimage_prod_left_fn_eq_if
- \- *lemma* mk_preimage_prod_right_fn_eq_if
- \- *lemma* range_pair_subset
- \- *lemma* prod_sub_preimage_iff
- \- *lemma* fst_image_prod_subset
- \- *lemma* prod_subset_preimage_fst
- \- *lemma* fst_image_prod
- \- *lemma* snd_image_prod_subset
- \- *lemma* prod_subset_preimage_snd
- \- *lemma* snd_image_prod
- \- *lemma* prod_diff_prod
- \- *lemma* prod_subset_prod_iff
- \- *lemma* mem_pi
- \- *lemma* mem_univ_pi
- \- *lemma* empty_pi
- \- *lemma* pi_univ
- \- *lemma* pi_mono
- \- *lemma* pi_inter_distrib
- \- *lemma* pi_congr
- \- *lemma* pi_eq_empty
- \- *lemma* univ_pi_eq_empty
- \- *lemma* pi_nonempty_iff
- \- *lemma* univ_pi_nonempty_iff
- \- *lemma* pi_eq_empty_iff
- \- *lemma* univ_pi_eq_empty_iff
- \- *lemma* univ_pi_empty
- \- *lemma* range_dcomp
- \- *lemma* insert_pi
- \- *lemma* singleton_pi
- \- *lemma* singleton_pi'
- \- *lemma* pi_if
- \- *lemma* union_pi
- \- *lemma* pi_inter_compl
- \- *lemma* pi_update_of_not_mem
- \- *lemma* pi_update_of_mem
- \- *lemma* univ_pi_update
- \- *lemma* univ_pi_update_univ
- \- *lemma* eval_image_pi
- \- *lemma* eval_image_univ_pi
- \- *lemma* eval_preimage
- \- *lemma* eval_preimage'
- \- *lemma* update_preimage_pi
- \- *lemma* update_preimage_univ_pi
- \- *lemma* subset_pi_eval_image
- \- *lemma* univ_pi_ite
- \- *lemma* image_prod
- \- *theorem* mem_prod_eq
- \- *theorem* mem_prod
- \- *theorem* prod_mk_mem_set_prod_eq
- \- *theorem* prod_mono
- \- *theorem* prod_empty
- \- *theorem* empty_prod
- \- *theorem* univ_prod_univ
- \- *theorem* singleton_prod
- \- *theorem* prod_singleton
- \- *theorem* singleton_prod_singleton
- \- *theorem* union_prod
- \- *theorem* prod_union
- \- *theorem* prod_inter_prod
- \- *theorem* insert_prod
- \- *theorem* prod_insert
- \- *theorem* prod_preimage_eq
- \- *theorem* image_swap_eq_preimage_swap
- \- *theorem* preimage_swap_prod
- \- *theorem* image_swap_prod
- \- *theorem* prod_image_image_eq
- \- *theorem* prod_range_range_eq
- \- *theorem* range_prod_map
- \- *theorem* prod_range_univ_eq
- \- *theorem* prod_univ_range_eq
- \- *theorem* nonempty.prod
- \- *theorem* nonempty.fst
- \- *theorem* nonempty.snd
- \- *theorem* prod_nonempty_iff
- \- *theorem* prod_eq_empty_iff
- \- *def* diagonal
- \- *def* pi

Modified src/data/set/function.lean

Modified src/data/set/intervals/basic.lean

Created src/data/set/prod.lean
- \+ *lemma* prod_eq
- \+ *lemma* mem_prod_eq
- \+ *lemma* mem_prod
- \+ *lemma* prod_mk_mem_set_prod_eq
- \+ *lemma* mk_mem_prod
- \+ *lemma* prod_mono
- \+ *lemma* prod_subset_iff
- \+ *lemma* forall_prod_set
- \+ *lemma* exists_prod_set
- \+ *lemma* prod_empty
- \+ *lemma* empty_prod
- \+ *lemma* univ_prod_univ
- \+ *lemma* univ_prod
- \+ *lemma* prod_univ
- \+ *lemma* singleton_prod
- \+ *lemma* prod_singleton
- \+ *lemma* singleton_prod_singleton
- \+ *lemma* union_prod
- \+ *lemma* prod_union
- \+ *lemma* prod_inter_prod
- \+ *lemma* insert_prod
- \+ *lemma* prod_insert
- \+ *lemma* prod_preimage_eq
- \+ *lemma* prod_preimage_left
- \+ *lemma* prod_preimage_right
- \+ *lemma* preimage_prod_map_prod
- \+ *lemma* mk_preimage_prod
- \+ *lemma* mk_preimage_prod_left
- \+ *lemma* mk_preimage_prod_right
- \+ *lemma* mk_preimage_prod_left_eq_empty
- \+ *lemma* mk_preimage_prod_right_eq_empty
- \+ *lemma* mk_preimage_prod_left_eq_if
- \+ *lemma* mk_preimage_prod_right_eq_if
- \+ *lemma* mk_preimage_prod_left_fn_eq_if
- \+ *lemma* mk_preimage_prod_right_fn_eq_if
- \+ *lemma* preimage_swap_prod
- \+ *lemma* image_swap_prod
- \+ *lemma* prod_image_image_eq
- \+ *lemma* prod_range_range_eq
- \+ *lemma* range_prod_map
- \+ *lemma* prod_range_univ_eq
- \+ *lemma* prod_univ_range_eq
- \+ *lemma* range_pair_subset
- \+ *lemma* nonempty.prod
- \+ *lemma* nonempty.fst
- \+ *lemma* nonempty.snd
- \+ *lemma* prod_nonempty_iff
- \+ *lemma* prod_eq_empty_iff
- \+ *lemma* prod_sub_preimage_iff
- \+ *lemma* fst_image_prod_subset
- \+ *lemma* prod_subset_preimage_fst
- \+ *lemma* fst_image_prod
- \+ *lemma* snd_image_prod_subset
- \+ *lemma* prod_subset_preimage_snd
- \+ *lemma* snd_image_prod
- \+ *lemma* prod_diff_prod
- \+ *lemma* prod_subset_prod_iff
- \+ *lemma* image_prod
- \+ *lemma* mem_diagonal
- \+ *lemma* preimage_coe_coe_diagonal
- \+ *lemma* diagonal_eq_range
- \+ *lemma* mem_pi
- \+ *lemma* mem_univ_pi
- \+ *lemma* empty_pi
- \+ *lemma* pi_univ
- \+ *lemma* pi_mono
- \+ *lemma* pi_inter_distrib
- \+ *lemma* pi_congr
- \+ *lemma* pi_eq_empty
- \+ *lemma* univ_pi_eq_empty
- \+ *lemma* pi_nonempty_iff
- \+ *lemma* univ_pi_nonempty_iff
- \+ *lemma* pi_eq_empty_iff
- \+ *lemma* univ_pi_eq_empty_iff
- \+ *lemma* univ_pi_empty
- \+ *lemma* range_dcomp
- \+ *lemma* insert_pi
- \+ *lemma* singleton_pi
- \+ *lemma* singleton_pi'
- \+ *lemma* pi_if
- \+ *lemma* union_pi
- \+ *lemma* pi_inter_compl
- \+ *lemma* pi_update_of_not_mem
- \+ *lemma* pi_update_of_mem
- \+ *lemma* univ_pi_update
- \+ *lemma* univ_pi_update_univ
- \+ *lemma* eval_image_pi
- \+ *lemma* eval_image_univ_pi
- \+ *lemma* eval_preimage
- \+ *lemma* eval_preimage'
- \+ *lemma* update_preimage_pi
- \+ *lemma* update_preimage_univ_pi
- \+ *lemma* subset_pi_eval_image
- \+ *lemma* univ_pi_ite
- \+ *def* diagonal
- \+ *def* pi

Modified src/topology/algebra/nonarchimedean/basic.lean

Modified test/lift.lean



## [2021-12-13 09:36:36](https://github.com/leanprover-community/mathlib/commit/e60899c)
feat(linear_algebra/orientation): inherit an action by `units R` on `module.ray R M` ([#10738](https://github.com/leanprover-community/mathlib/pull/10738))
This action is just the action inherited on the elements of the module under the quotient.
We provide it generally for any group `G` that satisfies the required properties, but are only really interested in `G = units R`.
This PR also provides `module.ray.map`, for sending a ray through a linear equivalence.
This generalization also provides us with `mul_action (M ≃ₗ[R] M) (module.ray R M)`, which might also turn out to be useful.
#### Estimated changes
Modified src/linear_algebra/orientation.lean
- \+ *lemma* same_ray.map
- \+ *lemma* same_ray_map_iff
- \+ *lemma* same_ray.smul
- \+ *lemma* module.ray.map_apply
- \+ *lemma* module.ray.map_refl
- \+ *lemma* module.ray.map_symm
- \+ *lemma* module.ray.linear_equiv_smul_eq_map
- \+ *lemma* smul_ray_of_ne_zero
- \+ *lemma* units_smul_of_pos
- \+ *lemma* units_smul_of_neg
- \+/\- *lemma* same_ray_smul_right_iff
- \+/\- *lemma* same_ray_smul_left_iff
- \+/\- *lemma* same_ray_neg_smul_right_iff
- \+/\- *lemma* same_ray_neg_smul_left_iff
- \+ *lemma* units_smul_eq_self_iff
- \+ *lemma* units_smul_eq_neg_iff
- \+/\- *lemma* same_ray_smul_right_iff
- \+/\- *lemma* same_ray_smul_left_iff
- \+/\- *lemma* same_ray_neg_smul_right_iff
- \+/\- *lemma* same_ray_neg_smul_left_iff
- \+ *def* ray_vector.map_linear_equiv
- \+ *def* module.ray.map



## [2021-12-13 09:36:35](https://github.com/leanprover-community/mathlib/commit/ea88bd6)
refactor(algebra/triv_sq_zero_ext): generalize and cleanup ([#10729](https://github.com/leanprover-community/mathlib/pull/10729))
This:
* Generalizes typeclass assumptions on many lemmas
* Generalizes and adds missing typeclass instances on `triv_sq_zero_ext`, most notably the algebra structure over a different ring.
* Reorders many of the lemmas in the file to ensure that the right arguments are implicit / explicit
#### Estimated changes
Modified src/algebra/triv_sq_zero_ext.lean
- \+/\- *lemma* fst_zero
- \+/\- *lemma* snd_zero
- \+/\- *lemma* fst_add
- \+/\- *lemma* snd_add
- \+/\- *lemma* fst_neg
- \+/\- *lemma* snd_neg
- \+/\- *lemma* fst_smul
- \+/\- *lemma* snd_smul
- \+/\- *lemma* inl_zero
- \+/\- *lemma* inl_add
- \+/\- *lemma* inl_neg
- \+ *lemma* inl_smul
- \+/\- *lemma* inr_zero
- \+/\- *lemma* inr_add
- \+/\- *lemma* inr_neg
- \+/\- *lemma* inr_smul
- \+/\- *lemma* inl_fst_add_inr_snd_eq
- \+/\- *lemma* fst_one
- \+/\- *lemma* snd_one
- \+/\- *lemma* inl_one
- \+/\- *lemma* inr_mul_inr
- \+ *lemma* algebra_map_eq_inl
- \+ *lemma* algebra_map_eq_inl_hom
- \+ *lemma* algebra_map_eq_inl'
- \+/\- *lemma* fst_zero
- \+/\- *lemma* snd_zero
- \+/\- *lemma* inl_zero
- \+/\- *lemma* inr_zero
- \+/\- *lemma* fst_add
- \+/\- *lemma* snd_add
- \+/\- *lemma* fst_neg
- \+/\- *lemma* snd_neg
- \+/\- *lemma* inl_add
- \+/\- *lemma* inr_add
- \+/\- *lemma* inl_fst_add_inr_snd_eq
- \+/\- *lemma* inl_neg
- \+/\- *lemma* inr_neg
- \+/\- *lemma* fst_smul
- \+/\- *lemma* snd_smul
- \+/\- *lemma* inr_smul
- \+/\- *lemma* fst_one
- \+/\- *lemma* snd_one
- \+/\- *lemma* inl_one
- \+/\- *lemma* inr_mul_inr
- \+/\- *def* triv_sq_zero_ext
- \+/\- *def* snd_hom
- \+/\- *def* inl_hom
- \+/\- *def* fst_hom
- \+/\- *def* triv_sq_zero_ext
- \+/\- *def* inl_hom
- \+/\- *def* fst_hom
- \+/\- *def* snd_hom

Modified src/linear_algebra/exterior_algebra.lean



## [2021-12-13 09:36:34](https://github.com/leanprover-community/mathlib/commit/e70e22f)
feat(data/{list, multiset, finset}/range): add range_add ([#10706](https://github.com/leanprover-community/mathlib/pull/10706))
Adds `range_add` lemmas
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* range_add

Modified src/data/list/range.lean
- \+ *lemma* range_add

Modified src/data/multiset/range.lean
- \+ *lemma* range_add
- \+ *lemma* range_disjoint_map_add
- \+ *lemma* range_add_eq_union



## [2021-12-13 09:36:32](https://github.com/leanprover-community/mathlib/commit/e4b6b5c)
feat(order/galois_connection): add lt_iff_lt ([#10702](https://github.com/leanprover-community/mathlib/pull/10702))
A lemma for galois connections on linear orders.
#### Estimated changes
Modified src/order/galois_connection.lean
- \+ *lemma* lt_iff_lt



## [2021-12-13 09:36:31](https://github.com/leanprover-community/mathlib/commit/29fecae)
feat(data/polynomial/degree/definitions): add pow lemmas ([#10698](https://github.com/leanprover-community/mathlib/pull/10698))
Add lemmas `nat_degree_pow_le` and `coeff_pow_degree_mul_degree`
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* nat_degree_pow_le
- \+ *lemma* coeff_pow_mul_nat_degree



## [2021-12-13 09:36:30](https://github.com/leanprover-community/mathlib/commit/fb81950)
feat(analysis/convex/basic): lemmas about midpoint and segment ([#10682](https://github.com/leanprover-community/mathlib/pull/10682))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* midpoint_mem_segment
- \+ *lemma* mem_segment_sub_add
- \+ *lemma* mem_segment_add_sub

Modified src/linear_algebra/affine_space/midpoint.lean
- \+ *lemma* midpoint_self_neg
- \+ *lemma* midpoint_neg_self
- \+ *lemma* midpoint_sub_add
- \+ *lemma* midpoint_add_sub



## [2021-12-13 09:36:28](https://github.com/leanprover-community/mathlib/commit/f8171e0)
feat(algebra/graded_monoid): dependent products ([#10674](https://github.com/leanprover-community/mathlib/pull/10674))
This introduces `list.dprod`, which takes the (possibly non-commutative) product of a list of graded elements of type `A i`. This definition primarily exist to allow `graded_monoid.mk` and `direct_sum.of` to be pulled outside a product, such as in the new `graded_monoid.mk_list_dprod` and `direct_sum.of_list_dprod` lemmas added in this PR.
#### Estimated changes
Modified src/algebra/direct_sum/ring.lean
- \+ *lemma* of_list_dprod
- \+ *lemma* list_prod_of_fn_of_eq_dprod

Modified src/algebra/graded_monoid.lean
- \+ *lemma* list.dprod_index_nil
- \+ *lemma* list.dprod_index_cons
- \+ *lemma* list.dprod_index_eq_map_sum
- \+ *lemma* list.dprod_nil
- \+ *lemma* list.dprod_cons
- \+ *lemma* graded_monoid.mk_list_dprod
- \+ *lemma* graded_monoid.list_prod_map_eq_dprod
- \+ *lemma* graded_monoid.list_prod_of_fn_eq_dprod
- \+ *lemma* list.dprod_monoid
- \+ *lemma* set_like.coe_list_dprod
- \+ *lemma* set_like.list_dprod_eq
- \+ *def* list.dprod_index
- \+ *def* list.dprod



## [2021-12-13 09:36:27](https://github.com/leanprover-community/mathlib/commit/309da20)
feat(*): Random lemmas about adjoin/span. ([#10666](https://github.com/leanprover-community/mathlib/pull/10666))
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* pow_smul_mem_closure_smul

Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* map_powers

Modified src/linear_algebra/basic.lean
- \+ *lemma* span_attach_bUnion
- \+ *lemma* span_smul_le
- \+ *lemma* span_smul_eq_of_is_unit

Modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* adjoin_eq_Inf
- \+ *lemma* adjoin_Union
- \+ *lemma* adjoin_attach_bUnion
- \+ *lemma* pow_smul_mem_adjoin_smul

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* union_eq_smul_set
- \+ *lemma* ideal_span_singleton_smul
- \+ *lemma* span_smul_eq
- \+ *lemma* mem_of_span_top_of_smul_mem



## [2021-12-13 09:36:26](https://github.com/leanprover-community/mathlib/commit/e19473a)
feat(algebra/pointwise): Multiplying a singleton  ([#10660](https://github.com/leanprover-community/mathlib/pull/10660))
and other lemmas about `finset.product` and singletons.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* mem_one
- \+ *lemma* mul_singleton
- \+ *lemma* singleton_mul
- \+ *lemma* singleton_mul_singleton
- \+ *lemma* mul_zero_subset
- \+ *lemma* zero_mul_subset
- \+ *lemma* nonempty.mul_zero
- \+ *lemma* nonempty.zero_mul
- \- *lemma* mul_singleton_zero_subset
- \- *lemma* singleton_zero_mul_subset
- \+ *theorem* one_subset

Modified src/data/finset/prod.lean
- \+ *lemma* singleton_product
- \+ *lemma* product_singleton
- \+ *lemma* singleton_product_singleton



## [2021-12-13 09:36:25](https://github.com/leanprover-community/mathlib/commit/ec48e3b)
feat(analysis/convex/strict): Strictly convex sets ([#10648](https://github.com/leanprover-community/mathlib/pull/10648))
This defines strictly convex sets.
#### Estimated changes
Created src/analysis/convex/strict.lean
- \+ *lemma* strict_convex_iff_open_segment_subset
- \+ *lemma* strict_convex.open_segment_subset
- \+ *lemma* strict_convex_empty
- \+ *lemma* strict_convex_univ
- \+ *lemma* directed.strict_convex_Union
- \+ *lemma* directed_on.strict_convex_sUnion
- \+ *lemma* is_open.strict_convex_iff
- \+ *lemma* strict_convex_singleton
- \+ *lemma* set.subsingleton.strict_convex
- \+ *lemma* strict_convex.linear_image
- \+ *lemma* strict_convex.is_linear_image
- \+ *lemma* strict_convex.linear_preimage
- \+ *lemma* strict_convex.is_linear_preimage
- \+ *lemma* strict_convex_Iic
- \+ *lemma* strict_convex_Ici
- \+ *lemma* strict_convex_Icc
- \+ *lemma* strict_convex_Iio
- \+ *lemma* strict_convex_Ioi
- \+ *lemma* strict_convex_Ioo
- \+ *lemma* strict_convex_Ico
- \+ *lemma* strict_convex_Ioc
- \+ *lemma* strict_convex_interval
- \+ *lemma* strict_convex.preimage_add_right
- \+ *lemma* strict_convex.preimage_add_left
- \+ *lemma* strict_convex.add_left
- \+ *lemma* strict_convex.add_right
- \+ *lemma* strict_convex.add
- \+ *lemma* strict_convex.preimage_smul
- \+ *lemma* strict_convex.eq_of_open_segment_subset_frontier
- \+ *lemma* strict_convex.add_smul_mem
- \+ *lemma* strict_convex.smul_mem_of_zero_mem
- \+ *lemma* strict_convex.add_smul_sub_mem
- \+ *lemma* strict_convex.affine_preimage
- \+ *lemma* strict_convex.affine_image
- \+ *lemma* strict_convex.neg
- \+ *lemma* strict_convex.neg_preimage
- \+ *lemma* strict_convex.smul
- \+ *lemma* strict_convex.affinity
- \+ *lemma* strict_convex_iff_div
- \+ *lemma* strict_convex.mem_smul_of_zero_mem
- \+ *lemma* strict_convex_iff_convex
- \+ *lemma* strict_convex_iff_ord_connected
- \+ *def* strict_convex



## [2021-12-13 09:36:23](https://github.com/leanprover-community/mathlib/commit/2d47c1d)
feat(ring_theory/polynomial/cyclotomic/*): ɸₙ(1) = 1 ([#10483](https://github.com/leanprover-community/mathlib/pull/10483))
(for `n` not a prime power)
#### Estimated changes
Modified src/ring_theory/polynomial/cyclotomic/eval.lean
- \+ *lemma* eval_one_cyclotomic_not_prime_pow



## [2021-12-13 07:53:00](https://github.com/leanprover-community/mathlib/commit/7cd8adb)
chore(category_theory/limits): Generalize universe for preserving limits ([#10736](https://github.com/leanprover-community/mathlib/pull/10736))
#### Estimated changes
Modified src/category_theory/closed/functor.lean

Modified src/category_theory/closed/ideal.lean

Modified src/category_theory/limits/comma.lean

Modified src/category_theory/limits/constructions/finite_products_of_binary_products.lean

Modified src/category_theory/limits/constructions/limits_of_products_and_equalizers.lean

Modified src/category_theory/limits/creates.lean
- \+/\- *lemma* has_limits_of_has_limits_creates_limits
- \+/\- *lemma* has_colimits_of_has_colimits_creates_colimits
- \+/\- *lemma* has_limits_of_has_limits_creates_limits
- \+/\- *lemma* has_colimits_of_has_colimits_creates_colimits
- \+/\- *def* creates_limits_of_nat_iso
- \+/\- *def* creates_colimits_of_nat_iso
- \+/\- *def* creates_limits_of_nat_iso
- \+/\- *def* creates_colimits_of_nat_iso

Modified src/category_theory/limits/functor_category.lean

Modified src/category_theory/limits/preserves/basic.lean
- \+/\- *def* preserves_limits_of_nat_iso
- \+/\- *def* preserves_limits_of_shape_of_equiv
- \+/\- *def* preserves_colimits_of_nat_iso
- \+/\- *def* preserves_colimits_of_shape_of_equiv
- \+/\- *def* preserves_limits_of_reflects_of_preserves
- \+/\- *def* reflects_limits_of_nat_iso
- \+/\- *def* preserves_colimits_of_reflects_of_preserves
- \+/\- *def* reflects_colimits_of_nat_iso
- \+/\- *def* fully_faithful_reflects_limits
- \+/\- *def* fully_faithful_reflects_colimits
- \+/\- *def* preserves_limits_of_nat_iso
- \+/\- *def* preserves_limits_of_shape_of_equiv
- \+/\- *def* preserves_colimits_of_nat_iso
- \+/\- *def* preserves_colimits_of_shape_of_equiv
- \+/\- *def* preserves_limits_of_reflects_of_preserves
- \+/\- *def* reflects_limits_of_nat_iso
- \+/\- *def* preserves_colimits_of_reflects_of_preserves
- \+/\- *def* reflects_colimits_of_nat_iso
- \+/\- *def* fully_faithful_reflects_limits
- \+/\- *def* fully_faithful_reflects_colimits

Modified src/category_theory/limits/preserves/finite.lean

Modified src/category_theory/limits/preserves/functor_category.lean

Modified src/category_theory/monad/limits.lean

Modified src/category_theory/monad/monadicity.lean

Modified src/category_theory/sites/limits.lean

Modified src/category_theory/sites/sheaf.lean



## [2021-12-13 07:52:59](https://github.com/leanprover-community/mathlib/commit/381b954)
feat(algebraic_geometry): An integral scheme is reduced and irreducible ([#10733](https://github.com/leanprover-community/mathlib/pull/10733))
#### Estimated changes
Modified src/algebra/category/CommRing/constructions.lean
- \+ *lemma* subsingleton_of_is_terminal

Modified src/algebra/ring/prod.lean
- \+ *lemma* false_of_nontrivial_of_product_domain

Modified src/algebraic_geometry/Scheme.lean

Modified src/algebraic_geometry/locally_ringed_space.lean

Created src/algebraic_geometry/properties.lean

Modified src/ring_theory/nilpotent.lean



## [2021-12-13 07:52:58](https://github.com/leanprover-community/mathlib/commit/214a80f)
feat(data/mv_polynomial/variables): API for mv_polynomial.degree_of ([#10646](https://github.com/leanprover-community/mathlib/pull/10646))
This PR provides some API for `mv_polynomial.degree_of` for `comm_ring` and `comm_semiring`. I don't know which of these lemmas should be simp lemmas.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* count_finset_sup
- \- *lemma* count_sup

Modified src/data/finsupp/basic.lean
- \+/\- *lemma* support_neg
- \+ *lemma* support_sub
- \+/\- *lemma* support_neg

Modified src/data/mv_polynomial/comm_ring.lean
- \+ *lemma* support_sub
- \+ *lemma* degree_of_sub_lt

Modified src/data/mv_polynomial/variables.lean
- \+ *lemma* degree_of_eq_sup
- \+ *lemma* degree_of_lt_iff
- \+ *lemma* degree_of_C
- \+ *lemma* degree_of_X
- \+ *lemma* degree_of_add_le
- \+ *lemma* monomial_le_degree_of
- \+ *lemma* degree_of_mul_le
- \+ *lemma* degree_of_mul_X_ne
- \+ *lemma* degree_of_mul_X_eq

Modified src/ring_theory/mv_polynomial/basic.lean



## [2021-12-13 07:52:57](https://github.com/leanprover-community/mathlib/commit/8b8f08d)
feat(category_theory/limits): The associativity of pullbacks and pushouts. ([#10619](https://github.com/leanprover-community/mathlib/pull/10619))
Also provides the pasting lemma for pullback (pushout) squares
#### Estimated changes
Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* pullback_right_pullback_fst_iso_hom_fst
- \+ *lemma* pullback_right_pullback_fst_iso_hom_snd
- \+ *lemma* pullback_right_pullback_fst_iso_inv_fst
- \+ *lemma* pullback_right_pullback_fst_iso_inv_snd_snd
- \+ *lemma* pullback_right_pullback_fst_iso_inv_snd_fst
- \+ *lemma* inl_pushout_left_pushout_inr_iso_inv
- \+ *lemma* inr_pushout_left_pushout_inr_iso_hom
- \+ *lemma* inr_pushout_left_pushout_inr_iso_inv
- \+ *lemma* inl_inl_pushout_left_pushout_inr_iso_hom
- \+ *lemma* inr_inl_pushout_left_pushout_inr_iso_hom
- \+ *lemma* has_pullback_assoc
- \+ *lemma* has_pullback_assoc_symm
- \+ *lemma* pullback_assoc_inv_fst_fst
- \+ *lemma* pullback_assoc_hom_fst
- \+ *lemma* pullback_assoc_hom_snd_fst
- \+ *lemma* pullback_assoc_hom_snd_snd
- \+ *lemma* pullback_assoc_inv_fst_snd
- \+ *lemma* pullback_assoc_inv_snd
- \+ *lemma* has_pushout_assoc
- \+ *lemma* has_pushout_assoc_symm
- \+ *lemma* inl_inl_pushout_assoc_hom
- \+ *lemma* inr_inl_pushout_assoc_hom
- \+ *lemma* inr_inr_pushout_assoc_inv
- \+ *lemma* inl_pushout_assoc_inv
- \+ *lemma* inl_inr_pushout_assoc_inv
- \+ *lemma* inr_pushout_assoc_hom
- \+ *def* big_square_is_pullback
- \+ *def* big_square_is_pushout
- \+ *def* left_square_is_pullback
- \+ *def* right_square_is_pushout
- \+ *def* pullback_right_pullback_fst_iso
- \+ *def* pushout_left_pushout_inr_iso
- \+ *def* pullback_pullback_left_is_pullback
- \+ *def* pullback_assoc_is_pullback
- \+ *def* pullback_pullback_right_is_pullback
- \+ *def* pullback_assoc_symm_is_pullback
- \+ *def* pullback_assoc
- \+ *def* pushout_pushout_left_is_pushout
- \+ *def* pushout_assoc_is_pushout
- \+ *def* pushout_pushout_right_is_pushout
- \+ *def* pushout_assoc_symm_is_pushout
- \+ *def* pushout_assoc



## [2021-12-13 07:52:56](https://github.com/leanprover-community/mathlib/commit/b6b47ed)
feat(algebraic_geometry/presheafed_space): Open immersions of presheafed spaces has pullbacks. ([#10069](https://github.com/leanprover-community/mathlib/pull/10069))
#### Estimated changes
Modified src/algebraic_geometry/open_immersion.lean
- \+ *lemma* pullback_cone_of_left_condition
- \+ *lemma* pullback_cone_of_left_lift_fst
- \+ *lemma* pullback_cone_of_left_lift_snd
- \+ *lemma* pullback_snd_is_iso_of_range_subset
- \+ *lemma* lift_fac
- \+ *lemma* lift_uniq
- \+ *def* pullback_cone_of_left_fst
- \+ *def* pullback_cone_of_left
- \+ *def* pullback_cone_of_left_lift
- \+ *def* pullback_cone_of_left_is_limit
- \+ *def* lift
- \+ *def* iso_of_range_eq



## [2021-12-13 07:15:39](https://github.com/leanprover-community/mathlib/commit/fcd0f11)
feat(category_theory/flat_functor): Generalize results into algebraic categories. ([#10735](https://github.com/leanprover-community/mathlib/pull/10735))
Also proves that the identity is flat, and compositions of flat functors are flat.
#### Estimated changes
Modified src/category_theory/flat_functors.lean
- \+/\- *def* Lan_evaluation_iso_colim
- \+/\- *def* Lan_evaluation_iso_colim



## [2021-12-13 00:12:14](https://github.com/leanprover-community/mathlib/commit/0690542)
feat(data/nat/prime): add `prime.dvd_mul_of_dvd_ne` ([#10727](https://github.com/leanprover-community/mathlib/pull/10727))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* prime.dvd_mul_of_dvd_ne



## [2021-12-13 00:12:12](https://github.com/leanprover-community/mathlib/commit/0c248b7)
feat(algebra/{group,ring}/opposite): `{ring,monoid}_hom.from_opposite` ([#10723](https://github.com/leanprover-community/mathlib/pull/10723))
We already have the `to_opposite` versions.
#### Estimated changes
Modified src/algebra/group/opposite.lean
- \+ *def* monoid_hom.from_opposite

Modified src/algebra/ring/opposite.lean
- \+ *def* ring_hom.from_opposite



## [2021-12-13 00:12:11](https://github.com/leanprover-community/mathlib/commit/4b07949)
chore(algebra/module/submodule): missing is_central_scalar instance ([#10720](https://github.com/leanprover-community/mathlib/pull/10720))
#### Estimated changes
Modified src/algebra/module/submodule.lean

Modified src/group_theory/group_action/sub_mul_action.lean



## [2021-12-13 00:12:10](https://github.com/leanprover-community/mathlib/commit/41def6a)
feat(algebra/tropical/big_operators): sum, prod, Inf ([#10544](https://github.com/leanprover-community/mathlib/pull/10544))
#### Estimated changes
Created src/algebra/tropical/big_operators.lean
- \+ *lemma* list.trop_sum
- \+ *lemma* multiset.trop_sum
- \+ *lemma* trop_sum
- \+ *lemma* list.untrop_prod
- \+ *lemma* multiset.untrop_prod
- \+ *lemma* untrop_prod
- \+ *lemma* list.trop_minimum
- \+ *lemma* multiset.trop_inf
- \+ *lemma* finset.trop_inf
- \+ *lemma* trop_Inf_image
- \+ *lemma* trop_infi
- \+ *lemma* multiset.untrop_sum
- \+ *lemma* finset.untrop_sum'
- \+ *lemma* untrop_sum_eq_Inf_image
- \+ *lemma* untrop_sum
- \+ *lemma* finset.untrop_sum

Created src/algebra/tropical/lattice.lean



## [2021-12-12 23:25:29](https://github.com/leanprover-community/mathlib/commit/b9f2440)
chore(linear_algebra/orientation): golf a proof ([#10742](https://github.com/leanprover-community/mathlib/pull/10742))
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* alternating_map.map_basis_eq_zero_iff
- \+ *lemma* alternating_map.map_basis_ne_zero_iff

Modified src/linear_algebra/orientation.lean



## [2021-12-12 21:34:23](https://github.com/leanprover-community/mathlib/commit/19dd4be)
chore(tactic/reserved_notation): change precedence of sup and inf ([#10623](https://github.com/leanprover-community/mathlib/pull/10623))
Put the precedence of `⊔` and `⊓` at 68 and 69 respectively, which is above `+` (65), `∑` and `∏` (67), and below `*` (70). This makes sure that inf and sup behave in the same way in expressions where arithmetic operations appear (which was not the case before).
Discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/inf.20and.20sup.20don't.20bind.20similarly
#### Estimated changes
Modified src/algebra/lattice_ordered_group.lean
- \+/\- *lemma* inf_mul_sup
- \+/\- *lemma* inf_mul_sup

Modified src/tactic/reserved_notation.lean



## [2021-12-12 15:54:29](https://github.com/leanprover-community/mathlib/commit/61b0f41)
refactor(data/{mv_,}polynomial): lemmas about `adjoin` ([#10670](https://github.com/leanprover-community/mathlib/pull/10670))
Prove `adjoin {X} = ⊤` and `adjoin (range X) = ⊤` for `polynomial`s
and `mv_polynomial`s much earlier and use these equalities to golf
some proofs.
Also drop some `comm_` in typeclass assumptions.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* coe_map

Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* alg_hom_ext
- \+ *lemma* adjoin_range_X
- \+ *lemma* _root_.algebra.adjoin_range_eq_range_aeval
- \+/\- *lemma* alg_hom_ext
- \+ *theorem* _root_.algebra.adjoin_eq_range

Modified src/data/mv_polynomial/supported.lean

Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* adjoin_X
- \+/\- *lemma* alg_hom_ext
- \+/\- *lemma* alg_hom_ext
- \+/\- *theorem* aeval_alg_hom
- \+ *theorem* aeval_X_left
- \+ *theorem* _root_.algebra.adjoin_singleton_eq_range_aeval
- \+/\- *theorem* aeval_alg_hom

Modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* adjoin_le_equalizer
- \+ *lemma* ext_of_adjoin_eq_top

Modified src/ring_theory/adjoin/fg.lean

Deleted src/ring_theory/adjoin/polynomial.lean
- \- *lemma* adjoin_range_eq_range_aeval
- \- *theorem* adjoin_eq_range
- \- *theorem* adjoin_singleton_eq_range_aeval



## [2021-12-12 06:54:07](https://github.com/leanprover-community/mathlib/commit/e68fcf8)
move(data/bool/*): Move `bool` files in one folder ([#10718](https://github.com/leanprover-community/mathlib/pull/10718))
* renames `data.bool` to `data.bool.basic`
* renames `data.set.bool` to `data.bool.set`
* splits `data.bool.all_any` off `data.list.basic`
#### Estimated changes
Created src/data/bool/all_any.lean
- \+ *theorem* all_nil
- \+ *theorem* all_cons
- \+ *theorem* all_iff_forall
- \+ *theorem* all_iff_forall_prop
- \+ *theorem* any_nil
- \+ *theorem* any_cons
- \+ *theorem* any_iff_exists
- \+ *theorem* any_iff_exists_prop
- \+ *theorem* any_of_mem

Renamed src/data/bool.lean to src/data/bool/basic.lean
- \+/\- *lemma* not_ff
- \+/\- *lemma* not_ff

Renamed src/data/set/bool.lean to src/data/bool/set.lean

Modified src/data/list/basic.lean
- \- *theorem* all_nil
- \- *theorem* all_cons
- \- *theorem* all_iff_forall
- \- *theorem* all_iff_forall_prop
- \- *theorem* any_nil
- \- *theorem* any_cons
- \- *theorem* any_iff_exists
- \- *theorem* any_iff_exists_prop
- \- *theorem* any_of_mem

Modified src/data/multiset/basic.lean

Modified src/order/complete_lattice.lean

Modified src/tactic/clear.lean

Modified src/tactic/find_unused.lean

Modified src/tactic/lint/misc.lean

Modified src/tactic/lint/type_classes.lean

Modified src/tactic/suggest.lean



## [2021-12-12 01:37:53](https://github.com/leanprover-community/mathlib/commit/50e318e)
feat(algebra/order/ring): pos_iff_pos_of_mul_pos, neg_iff_neg_of_mul_pos ([#10634](https://github.com/leanprover-community/mathlib/pull/10634))
Add four lemmas, deducing equivalence of `a` and `b` being positive or
negative from such a hypothesis for their product, that don't currently
seem to be present.
#### Estimated changes
Modified src/algebra/order/ring.lean
- \+ *lemma* pos_iff_pos_of_mul_pos
- \+/\- *lemma* neg_of_mul_pos_left
- \+/\- *lemma* neg_of_mul_pos_right
- \+ *lemma* neg_iff_neg_of_mul_pos
- \+ *lemma* neg_iff_pos_of_mul_neg
- \+ *lemma* pos_iff_neg_of_mul_neg
- \+/\- *lemma* neg_of_mul_pos_left
- \+/\- *lemma* neg_of_mul_pos_right



## [2021-12-11 21:21:53](https://github.com/leanprover-community/mathlib/commit/f361373)
chore(order/boolean_algebra): add `compl_sdiff` ([#10722](https://github.com/leanprover-community/mathlib/pull/10722))
Also mark `sdiff_compl` and `top_sdiff` as `@[simp]`.
#### Estimated changes
Modified src/order/boolean_algebra.lean
- \+ *lemma* compl_sdiff
- \+/\- *theorem* sdiff_compl
- \+/\- *theorem* top_sdiff
- \+/\- *theorem* sdiff_compl
- \+/\- *theorem* top_sdiff



## [2021-12-11 21:21:52](https://github.com/leanprover-community/mathlib/commit/f9fff7c)
feat(measure_theory): integral is mono in measure ([#10721](https://github.com/leanprover-community/mathlib/pull/10721))
* Bochner integral of a nonnegative function is monotone in measure;
* set integral of a nonnegative function is monotone in set (generalize existing lemma);
* interval integral of a nonnegative function is monotone in interval.
#### Estimated changes
Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* integral_mono_measure

Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* integral_mono_interval

Modified src/measure_theory/integral/set_integral.lean
- \+/\- *lemma* set_integral_mono_set
- \+/\- *lemma* set_integral_mono_set



## [2021-12-11 21:21:51](https://github.com/leanprover-community/mathlib/commit/cc5ff8c)
feat(group_theory/submonoid): The submonoid of left inverses of a submonoid ([#10679](https://github.com/leanprover-community/mathlib/pull/10679))
#### Estimated changes
Modified src/algebra/group/units.lean

Modified src/group_theory/submonoid/basic.lean

Created src/group_theory/submonoid/inverses.lean
- \+ *lemma* is_unit.submonoid.coe_inv
- \+ *lemma* left_inv_left_inv_le
- \+ *lemma* unit_mem_left_inv
- \+ *lemma* left_inv_left_inv_eq
- \+ *lemma* mul_from_left_inv
- \+ *lemma* from_left_inv_one
- \+ *lemma* from_left_inv_mul
- \+ *lemma* left_inv_le_is_unit
- \+ *lemma* from_left_inv_eq_iff
- \+ *lemma* from_left_inv_left_inv_equiv_symm
- \+ *lemma* left_inv_equiv_symm_from_left_inv
- \+ *lemma* left_inv_equiv_mul
- \+ *lemma* mul_left_inv_equiv
- \+ *lemma* left_inv_equiv_symm_mul
- \+ *lemma* mul_left_inv_equiv_symm
- \+ *lemma* left_inv_eq_inv
- \+ *lemma* from_left_inv_eq_inv
- \+ *lemma* left_inv_equiv_symm_eq_inv
- \+ *def* left_inv
- \+ *def* from_left_inv
- \+ *def* from_comm_left_inv
- \+ *def* left_inv_equiv



## [2021-12-11 21:21:50](https://github.com/leanprover-community/mathlib/commit/1c2b742)
feat(ring_theory/polynomial/cyclotomic/eval): `cyclotomic_pos` ([#10482](https://github.com/leanprover-community/mathlib/pull/10482))
#### Estimated changes
Modified counterexamples/cyclotomic_105.lean

Modified src/data/nat/basic.lean
- \+ *lemma* two_lt_of_ne

Modified src/number_theory/primes_congruent_one.lean

Renamed src/ring_theory/polynomial/cyclotomic.lean to src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* prod_cyclotomic_eq_geom_sum
- \- *lemma* eval_one_cyclotomic_prime
- \- *lemma* eval₂_one_cyclotomic_prime
- \- *lemma* eval_one_cyclotomic_prime_pow
- \- *lemma* eval₂_one_cyclotomic_prime_pow

Created src/ring_theory/polynomial/cyclotomic/eval.lean
- \+ *lemma* eval_one_cyclotomic_prime
- \+ *lemma* eval₂_one_cyclotomic_prime
- \+ *lemma* eval_one_cyclotomic_prime_pow
- \+ *lemma* eval₂_one_cyclotomic_prime_pow
- \+ *lemma* cyclotomic_pos



## [2021-12-11 19:31:57](https://github.com/leanprover-community/mathlib/commit/f068b9d)
refactor(algebra/group/basic): Migrate add_comm_group section into comm_group section ([#10565](https://github.com/leanprover-community/mathlib/pull/10565))
Currently mathlib has a rich set of lemmas connecting the addition, subtraction and negation additive commutative group operations, but a far thinner collection of results for multiplication, division and inverse multiplicative commutative group operations, despite the fact that the former can be generated easily from the latter via to_additive.
This PR refactors the additive results in the `add_comm_group` section as the equivalent multiplicative results in the `comm_group` section and then recovers the additive results via to_additive. There is a complication in that unfortunately the multiplicative forms of the names of some of the `add_comm_group` lemmas collide with existing names in `group_with_zero`. I have worked around this by appending an apostrophe to the name and then manually overriding the names generated by to_additive. In a few cases, names with `1...n` appended apostrophes already existed. In these cases I have appended `n+1` apostrophes.
Previous discussion
The `add_group` section was previously tackled in [#10532](https://github.com/leanprover-community/mathlib/pull/10532).
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* div_mul_eq_div_div
- \+ *lemma* inv_mul_eq_div
- \+ *lemma* div_mul_eq_mul_div'
- \+ *lemma* div_div
- \+ *lemma* div_mul
- \+ *lemma* mul_div_mul_left_eq_div
- \+ *lemma* eq_div_of_mul_eq''
- \+ *lemma* eq_mul_of_div_eq'
- \+ *lemma* mul_eq_of_eq_div'
- \+ *lemma* div_div_self'
- \+ *lemma* mul_div_comm'
- \+ *lemma* div_eq_div_mul_div
- \+ *lemma* inv_inv_div_inv
- \+ *lemma* div_div_cancel
- \+ *lemma* div_eq_inv_mul'
- \+ *lemma* div_div_cancel_left
- \+ *lemma* inv_div_inv
- \+ *lemma* eq_div_iff_mul_eq''
- \+ *lemma* div_eq_iff_eq_mul'
- \+ *lemma* mul_div_cancel'''
- \+ *lemma* mul_div_cancel'_right
- \+ *lemma* div_mul_cancel''
- \+ *lemma* mul_mul_inv_cancel'_right
- \+ *lemma* div_right_comm'
- \+ *lemma* mul_mul_div_cancel
- \+ *lemma* div_mul_mul_cancel
- \+ *lemma* div_mul_div_cancel''
- \+ *lemma* mul_div_div_cancel
- \+ *lemma* div_div_div_cancel_left
- \+ *lemma* div_eq_div_iff_mul_eq_mul
- \+ *lemma* div_eq_div_iff_div_eq_div
- \- *lemma* sub_add_eq_sub_sub
- \- *lemma* neg_add_eq_sub
- \- *lemma* sub_add_eq_add_sub
- \- *lemma* sub_sub
- \- *lemma* sub_add
- \- *lemma* add_sub_add_left_eq_sub
- \- *lemma* eq_sub_of_add_eq'
- \- *lemma* eq_add_of_sub_eq'
- \- *lemma* add_eq_of_eq_sub'
- \- *lemma* sub_sub_self
- \- *lemma* add_sub_comm
- \- *lemma* sub_eq_sub_add_sub
- \- *lemma* neg_neg_sub_neg
- \- *lemma* sub_sub_cancel
- \- *lemma* sub_sub_cancel_left
- \- *lemma* sub_eq_neg_add
- \- *lemma* neg_sub_neg
- \- *lemma* eq_sub_iff_add_eq'
- \- *lemma* sub_eq_iff_eq_add'
- \- *lemma* add_sub_cancel'
- \- *lemma* add_sub_cancel'_right
- \- *lemma* sub_add_cancel'
- \- *lemma* add_add_neg_cancel'_right
- \- *lemma* sub_right_comm
- \- *lemma* add_add_sub_cancel
- \- *lemma* sub_add_add_cancel
- \- *lemma* sub_add_sub_cancel'
- \- *lemma* add_sub_sub_cancel
- \- *lemma* sub_sub_sub_cancel_left
- \- *lemma* sub_eq_sub_iff_add_eq_add
- \- *lemma* sub_eq_sub_iff_sub_eq_sub
- \+ *theorem* inv_mul'
- \- *theorem* neg_add'



## [2021-12-11 13:03:44](https://github.com/leanprover-community/mathlib/commit/294753e)
Fix comment typo ([#10715](https://github.com/leanprover-community/mathlib/pull/10715))
#### Estimated changes
Modified src/topology/order.lean



## [2021-12-11 11:06:55](https://github.com/leanprover-community/mathlib/commit/9741766)
feat(analysis/normed_space): normed space is homeomorphic to the unit ball ([#10690](https://github.com/leanprover-community/mathlib/pull/10690))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *def* homeomorph_unit_ball



## [2021-12-11 09:33:55](https://github.com/leanprover-community/mathlib/commit/08d30d6)
chore(algebra/pointwise): Better `variables` management ([#10686](https://github.com/leanprover-community/mathlib/pull/10686))
Moves a few variables from lemma statements to `variables`.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+/\- *lemma* smul_mem_smul_set_iff
- \+/\- *lemma* mem_smul_set_iff_inv_smul_mem
- \+/\- *lemma* mem_inv_smul_set_iff
- \+/\- *lemma* set_smul_subset_set_smul_iff
- \+/\- *lemma* set_smul_subset_iff
- \+/\- *lemma* subset_set_smul_iff
- \+/\- *lemma* mul_def
- \+/\- *lemma* mem_mul
- \+/\- *lemma* coe_mul
- \+/\- *lemma* mul_mem_mul
- \+/\- *lemma* mul_card_le
- \+/\- *lemma* empty_mul
- \+/\- *lemma* mul_empty
- \+/\- *lemma* mul_nonempty_iff
- \+/\- *lemma* mul_subset_mul
- \+ *lemma* mul_singleton_zero_subset
- \+ *lemma* singleton_zero_mul_subset
- \+/\- *lemma* mul_subset
- \+/\- *lemma* mul_subset_closure
- \+/\- *lemma* smul_mem_smul_set_iff
- \+/\- *lemma* mem_smul_set_iff_inv_smul_mem
- \+/\- *lemma* mem_inv_smul_set_iff
- \+/\- *lemma* set_smul_subset_set_smul_iff
- \+/\- *lemma* set_smul_subset_iff
- \+/\- *lemma* subset_set_smul_iff
- \+/\- *lemma* mul_def
- \+/\- *lemma* mem_mul
- \+/\- *lemma* coe_mul
- \+/\- *lemma* mul_mem_mul
- \+/\- *lemma* mul_card_le
- \+/\- *lemma* empty_mul
- \+/\- *lemma* mul_empty
- \+/\- *lemma* mul_nonempty_iff
- \+/\- *lemma* mul_subset_mul
- \- *lemma* mul_singleton_zero
- \- *lemma* singleton_zero_mul
- \+/\- *lemma* mul_subset
- \+/\- *lemma* mul_subset_closure
- \+/\- *theorem* range_smul_range
- \+/\- *theorem* range_smul_range



## [2021-12-11 04:23:13](https://github.com/leanprover-community/mathlib/commit/d856bf9)
feat(ring_theory/localization): Clearing denominators ([#10668](https://github.com/leanprover-community/mathlib/pull/10668))
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *lemma* map_integer_multiple
- \+ *lemma* finset_integer_multiple_image
- \+ *def* common_denom
- \+ *def* integer_multiple
- \+ *def* common_denom_of_finset
- \+ *def* finset_integer_multiple



## [2021-12-10 23:48:44](https://github.com/leanprover-community/mathlib/commit/0b87b0a)
chore(algebra/group_with_zero/defs: Rename `comm_cancel_monoid_with_zero` to `cancel_comm_monoid_with_zero` ([#10669](https://github.com/leanprover-community/mathlib/pull/10669))
We currently have `cancel_comm_monoid` but `comm_cancel_monoid_with_zero`. This renames the latter to follow the former.
Replaced `comm_cancel_` by `cancel_comm_` everywhere.
#### Estimated changes
Modified src/algebra/associated.lean
- \+/\- *lemma* dvd_and_not_dvd_iff
- \+/\- *lemma* pow_dvd_pow_iff
- \+/\- *lemma* prime.left_dvd_or_dvd_right_of_dvd_mul
- \+/\- *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \+/\- *lemma* exists_associated_mem_of_dvd_prod
- \+/\- *lemma* prime.associated_of_dvd
- \+/\- *lemma* associated.of_mul_left
- \+/\- *lemma* associated.of_mul_right
- \+/\- *lemma* prod_ne_zero_of_prime
- \+/\- *lemma* dvd_and_not_dvd_iff
- \+/\- *lemma* pow_dvd_pow_iff
- \+/\- *lemma* prime.left_dvd_or_dvd_right_of_dvd_mul
- \+/\- *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \+/\- *lemma* exists_associated_mem_of_dvd_prod
- \+/\- *lemma* prime.associated_of_dvd
- \+/\- *lemma* associated.of_mul_left
- \+/\- *lemma* associated.of_mul_right
- \+/\- *lemma* prod_ne_zero_of_prime
- \+/\- *theorem* prime.dvd_prime_iff_associated
- \+/\- *theorem* prime.dvd_prime_iff_associated

Modified src/algebra/divisibility.lean
- \+/\- *theorem* mul_dvd_mul_iff_right
- \+/\- *theorem* mul_dvd_mul_iff_right

Modified src/algebra/gcd_monoid/basic.lean

Modified src/algebra/gcd_monoid/finset.lean

Modified src/algebra/gcd_monoid/multiset.lean

Modified src/algebra/group_with_zero/basic.lean

Modified src/algebra/group_with_zero/defs.lean

Modified src/algebra/punit_instances.lean

Modified src/algebra/ring/basic.lean

Modified src/algebra/squarefree.lean
- \+/\- *lemma* prime.squarefree
- \+/\- *lemma* prime.squarefree

Modified src/data/nat/basic.lean

Modified src/ring_theory/dedekind_domain.lean

Modified src/ring_theory/multiplicity.lean

Modified src/ring_theory/prime.lean

Modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *lemma* ufm_of_gcd_of_wf_dvd_monoid
- \+/\- *lemma* prime_factors_unique
- \+/\- *lemma* prime_factors_irreducible
- \+/\- *lemma* ufm_of_gcd_of_wf_dvd_monoid
- \+/\- *lemma* prime_factors_unique
- \+/\- *lemma* prime_factors_irreducible
- \+/\- *theorem* wf_dvd_monoid.of_well_founded_associates
- \+/\- *theorem* wf_dvd_monoid.iff_well_founded_associates
- \+/\- *theorem* unique_factorization_monoid.iff_exists_prime_factors
- \+/\- *theorem* irreducible_iff_prime_of_exists_unique_irreducible_factors
- \+/\- *theorem* wf_dvd_monoid.of_well_founded_associates
- \+/\- *theorem* wf_dvd_monoid.iff_well_founded_associates
- \+/\- *theorem* unique_factorization_monoid.iff_exists_prime_factors
- \+/\- *theorem* irreducible_iff_prime_of_exists_unique_irreducible_factors
- \+/\- *def* {u}
- \+/\- *def* {u}



## [2021-12-10 21:59:37](https://github.com/leanprover-community/mathlib/commit/52c2f74)
docs(topology/homotopy): add namespace in docstring to fix links ([#10711](https://github.com/leanprover-community/mathlib/pull/10711))
Currently all the occurences of `homotopy` in the docs link to `algebra/homology/homotopy`.
#### Estimated changes
Modified src/topology/homotopy/basic.lean



## [2021-12-10 21:59:36](https://github.com/leanprover-community/mathlib/commit/a12fc70)
feat(logic/function/basic): surjective function is an epimorphism ([#10691](https://github.com/leanprover-community/mathlib/pull/10691))
* Move proofs about `surjective`/`injective` and `epi`/`mono` to `logic.function.basic` (formulated in terms of injectivity of composition), make them universe polymorphic.
* drop `forall_iff_forall_surj`, use `function.surjective.forall` instead.
#### Estimated changes
Modified src/algebra/group/hom.lean

Modified src/algebra/ring/basic.lean

Modified src/category_theory/types.lean

Modified src/logic/basic.lean
- \- *theorem* forall_iff_forall_surj

Modified src/logic/function/basic.lean
- \+/\- *lemma* surjective.of_comp_iff'
- \+ *lemma* surjective.injective_comp_right
- \+ *lemma* surjective_of_right_cancellable_Prop
- \+/\- *lemma* surjective.comp_left
- \+/\- *lemma* bijective.comp_left
- \+ *lemma* injective.surjective_comp_right'
- \+ *lemma* injective.surjective_comp_right
- \+ *lemma* bijective.comp_right
- \+/\- *lemma* surjective.of_comp_iff'
- \+/\- *lemma* surjective.comp_left
- \+/\- *lemma* bijective.comp_left



## [2021-12-10 20:23:28](https://github.com/leanprover-community/mathlib/commit/3e1d4d3)
feat(algebra/gcd_monoid): `associates` lemmas ([#10705](https://github.com/leanprover-community/mathlib/pull/10705))
#### Estimated changes
Modified src/algebra/gcd_monoid/basic.lean
- \+/\- *lemma* out_mk
- \+ *lemma* mk_out
- \+ *lemma* out_injective
- \+/\- *lemma* out_mk
- \+ *def* associates_equiv_of_unique_units

Modified src/ring_theory/int/basic.lean



## [2021-12-10 19:12:57](https://github.com/leanprover-community/mathlib/commit/b7ac833)
feat(ring_theory/discriminant): add the discriminant of a family of vectors ([#10350](https://github.com/leanprover-community/mathlib/pull/10350))
We add the definition and some basic results about the discriminant.
From FLT-regular.
- [x] depends on: [#10657](https://github.com/leanprover-community/mathlib/pull/10657)
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* minor_mul_transpose_minor

Modified src/linear_algebra/alternating.lean

Modified src/linear_algebra/finite_dimensional.lean

Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* fintype.not_linear_independent_iff
- \+ *theorem* not_linear_independent_iff
- \- *theorem* linear_dependent_iff

Created src/ring_theory/discriminant.lean
- \+ *lemma* discr_def
- \+ *lemma* discr_zero_of_not_linear_independent
- \+ *lemma* discr_of_matrix_vec_mul
- \+ *lemma* discr_of_matrix_mul_vec
- \+ *lemma* discr_not_zero_of_linear_independent
- \+ *lemma* discr_eq_det_embeddings_matrix_reindex_pow_two
- \+ *lemma* discr_power_basis_eq_prod
- \+ *def* discr

Modified src/ring_theory/trace.lean
- \+ *lemma* trace_matrix_def
- \+ *lemma* trace_matrix_of_matrix_vec_mul
- \+ *lemma* trace_matrix_of_matrix_mul_vec
- \+ *lemma* trace_matrix_of_basis
- \+ *lemma* embeddings_matrix_reindex_eq_vandermonde
- \+ *lemma* trace_matrix_eq_embeddings_matrix_mul_trans
- \+ *lemma* trace_matrix_eq_embeddings_matrix_reindex_mul_trans
- \+ *lemma* det_trace_matrix_ne_zero'
- \- *lemma* det_trace_form_ne_zero'
- \+ *def* trace_matrix
- \+ *def* embeddings_matrix
- \+ *def* embeddings_matrix_reindex



## [2021-12-10 17:07:55](https://github.com/leanprover-community/mathlib/commit/71e9f90)
feat(order/basic): Slightly generalized `densely_ordered` ([#10664](https://github.com/leanprover-community/mathlib/pull/10664))
Changed `[preorder α]` to `[has_lt α]`.
#### Estimated changes
Modified src/order/basic.lean
- \+/\- *lemma* exists_between
- \+/\- *lemma* exists_between



## [2021-12-10 15:16:09](https://github.com/leanprover-community/mathlib/commit/12e18e8)
feat(data/nat/gcd): coprime add mul lemmas ([#10588](https://github.com/leanprover-community/mathlib/pull/10588))
Adds `coprime m (n + k * m) ↔ coprime m n` for nats, (and permutations thereof).
#### Estimated changes
Modified src/data/nat/fib.lean

Modified src/data/nat/gcd.lean
- \+ *lemma* gcd_add_mul_right_right
- \+ *lemma* gcd_add_mul_left_right
- \+ *lemma* gcd_mul_right_add_right
- \+ *lemma* gcd_mul_left_add_right
- \+ *lemma* gcd_add_mul_right_left
- \+ *lemma* gcd_add_mul_left_left
- \+ *lemma* gcd_mul_right_add_left
- \+ *lemma* gcd_mul_left_add_left
- \+ *lemma* coprime_add_mul_right_right
- \+ *lemma* coprime_add_mul_left_right
- \+ *lemma* coprime_mul_right_add_right
- \+ *lemma* coprime_mul_left_add_right
- \+ *lemma* coprime_add_mul_right_left
- \+ *lemma* coprime_add_mul_left_left
- \+ *lemma* coprime_mul_right_add_left
- \+ *lemma* coprime_mul_left_add_left
- \- *lemma* gcd_add_mul_self
- \+/\- *theorem* gcd_eq_zero_iff
- \+/\- *theorem* gcd_eq_zero_iff



## [2021-12-10 15:16:08](https://github.com/leanprover-community/mathlib/commit/18ce3a8)
feat(group_theory/group_action/defs): add a typeclass to show that an action is central (aka symmetric) ([#10543](https://github.com/leanprover-community/mathlib/pull/10543))
This adds a new `is_central_scalar` typeclass to indicate that `op m • a = m • a` (or rather, to indicate that a type has the same right and left scalar action on another type).
The main instance for this is `comm_semigroup.is_central_scalar`, for when `m • a = m * a` and `op m • a = a * m`, and then all the other instances follow transitively when `has_scalar R (f M)` is derived from `has_scalar R M`:
* `prod`
* `pi`
* `ulift`
* `finsupp`
* `dfinsupp`
* `monoid_algebra`
* `add_monoid_algebra`
* `polynomial`
* `mv_polynomial`
* `matrix`
* `add_monoid_hom`
* `linear_map`
* `complex`
* `pointwise` instances on:
  * `set`
  * `submonoid`
  * `add_submonoid`
  * `subgroup`
  * `add_subgroup`
  * `subsemiring`
  * `subring`
  * `submodule`
#### Estimated changes
Modified src/algebra/module/hom.lean

Modified src/algebra/module/linear_map.lean

Modified src/algebra/module/submodule_pointwise.lean

Modified src/algebra/module/ulift.lean

Modified src/algebra/monoid_algebra/basic.lean

Modified src/algebra/pointwise.lean

Modified src/data/complex/module.lean

Modified src/data/dfinsupp.lean

Modified src/data/finsupp/basic.lean

Modified src/data/matrix/basic.lean

Modified src/data/mv_polynomial/basic.lean

Modified src/data/polynomial/basic.lean

Modified src/group_theory/group_action/defs.lean
- \+ *lemma* is_central_scalar.unop_smul_eq_smul

Modified src/group_theory/group_action/opposite.lean
- \+ *lemma* op_smul_eq_op_smul_op
- \+ *lemma* unop_smul_eq_unop_smul_unop

Modified src/group_theory/group_action/pi.lean

Modified src/group_theory/group_action/prod.lean

Modified src/group_theory/subgroup/pointwise.lean

Modified src/group_theory/submonoid/pointwise.lean

Modified src/ring_theory/subring/pointwise.lean

Modified src/ring_theory/subsemiring/pointwise.lean



## [2021-12-10 13:26:26](https://github.com/leanprover-community/mathlib/commit/94d51b9)
chore(algebraic_geometry/presheafed_space): Make `has_colimits` work faster ([#10703](https://github.com/leanprover-community/mathlib/pull/10703))
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space/has_colimits.lean
- \+ *lemma* colimit_carrier
- \+ *lemma* colimit_presheaf
- \+ *lemma* desc_fac
- \+ *def* desc



## [2021-12-10 13:26:25](https://github.com/leanprover-community/mathlib/commit/c29b706)
feat(data/int/gcd): another version of Euclid's lemma ([#10622](https://github.com/leanprover-community/mathlib/pull/10622))
We already have something described as "Euclid's lemma" in `ring_theory/unique_factorization_domain`, but not this specific statement of the lemma.
This is Theorem 1.5 in Apostol (1976) Introduction to Analytic Number Theory
#### Estimated changes
Modified src/data/int/gcd.lean
- \+ *lemma* dvd_of_dvd_mul_left_of_gcd_one
- \+ *lemma* dvd_of_dvd_mul_right_of_gcd_one



## [2021-12-10 13:26:24](https://github.com/leanprover-community/mathlib/commit/4471de6)
feat(order/lattice): define a lattice structure using an injective map to another lattice ([#10615](https://github.com/leanprover-community/mathlib/pull/10615))
This is done similarly to `function.injective.group` etc.
#### Estimated changes
Modified src/order/lattice.lean



## [2021-12-10 13:26:23](https://github.com/leanprover-community/mathlib/commit/ebbb991)
feat(ring_theory/principal_ideal_domain): add some corollaries about is_coprime ([#10601](https://github.com/leanprover-community/mathlib/pull/10601))
#### Estimated changes
Modified src/ring_theory/euclidean_domain.lean

Modified src/ring_theory/principal_ideal_domain.lean
- \+ *theorem* is_coprime_of_irreducible_dvd
- \+ *theorem* is_coprime_of_prime_dvd
- \+ *theorem* irreducible.coprime_iff_not_dvd
- \+ *theorem* prime.coprime_iff_not_dvd



## [2021-12-10 13:26:22](https://github.com/leanprover-community/mathlib/commit/46ac3c4)
feat(*): introduce classes for types of homomorphism ([#9888](https://github.com/leanprover-community/mathlib/pull/9888))
This PR is the main proof-of-concept in my plan to use typeclasses to reduce duplication surrounding `hom` classes. Essentially, I want to take each type of bundled homs, such as `monoid_hom`, and add a class `monoid_hom_class` which has an instance for each *type* extending `monoid_hom`. Declarations that now take a parameter of the specific type `monoid_hom M N` can instead take a more general `{F : Type*} [monoid_hom_class F M N] (f : F)`; this means we don't need to duplicate e.g. `monoid_hom.map_prod` to `ring_hom.map_prod`, `mul_equiv.map_prod`, `ring_equiv.map_prod`, or `monoid_hom.map_div` to `ring_hom.map_div`, `mul_equiv.map_div`, `ring_equiv.map_div`, ...
Basically, instead of having `O(n * k)` declarations for `n` types of homs and `k` lemmas, following the plan we only need `O(n + k)`.
## Overview
 * Change `has_coe_to_fun` to include the type of the function as a parameter (rather than a field of the structure) (**done** as part of [#7033](https://github.com/leanprover-community/mathlib/pull/7033))
 * Define a class `fun_like`, analogous to `set_like`, for types of bundled function + proof (**done** in [#10286](https://github.com/leanprover-community/mathlib/pull/10286))
 * Extend `fun_like` for each `foo_hom` to create a `foo_hom_class` (**done** in this PR for `ring_hom` and its ancestors, **todo** in follow-up for the rest)
 * Change parameters of type `foo_hom A B` to take `{F : Type*} [foo_hom_class F A B] (f : F)` instead (**done** in this PR for `map_{add,zero,mul,one,sub,div}`, **todo** in follow-up for remaining declarations)
## API changes
Lemmas matching `*_hom.map_{add,zero,mul,one,sub,div}` are deprecated. Use the new `simp` lemmas called simply `map_add`, `map_zero`, ...
Namespaced lemmas of the form `map_{add,zero,mul,one,sub,div}` are now protected. This includes e.g. `polynomial.map_add` and `multiset.map_add`, which involve `polynomial.map` and `multiset.map` respectively. In fact, it should be possible to turn those `map` definitions into bundled maps, so we don't even need to worry about the name change.
## New classes
 * `zero_hom_class`, `one_hom_class` defines `map_zero`, `map_one`
 * `add_hom_class`, `mul_hom_class` defines `map_add`, `map_mul`
 * `add_monoid_hom_class`, `monoid_hom_class` extends `{zero,one}_hom_class`, `{add,mul}_hom_class`
 * `monoid_with_zero_hom_class` extends `monoid_hom_class` and `zero_hom_class`
 * `ring_hom_class` extends `monoid_hom_class`, `add_monoid_hom_class` and `monoid_with_zero_hom_class`
## Classes still to be implemented
Some of the core algebraic homomorphisms are still missing their corresponding classes:
 * `mul_action_hom_class` defines `map_smul`
 * `distrib_mul_action_hom_class`, `mul_semiring_action_hom_class` extends the above
 * `linear_map_class` extends `add_hom_class` and defines `map_smulₛₗ`
 * `alg_hom_class` extends `ring_hom_class` and defines `commutes`
We could also add an `equiv_like` and its descendants `add_equiv_class`, `mul_equiv_class`, `ring_equiv_class`, `linear_equiv_class`, ...
## Other changes
`coe_fn_coe_base` now has an appropriately low priority, so it doesn't take precedence over `fun_like.has_coe_to_fun`.
## Why are you unbundling the morphisms again?
It's not quite the same thing as unbundling. When using unbundled morphisms, parameters have the form `(f : A → B) (hf : is_foo_hom f)`; bundled morphisms look like `(f : foo_hom A B)` (where `foo_hom A B` is equivalent to `{ f : A → B // is_foo_hom f }`; typically you would use a custom structure instead of `subtype`). This plan puts a predicate on the *type* `foo_hom` rather than the *elements* of the type as you would with unbundled morphisms. I believe this will preserve the advantages of the bundled approach (being able to talk about the identity map, making it work with `simp`), while addressing one of its disadvantages (needing to duplicate all the lemmas whenever extending the type of morphisms).
## Discussion
Main Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclasses.20for.20morphisms
Some other threads referencing this plan:
 * https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Morphism.20refactor
 * https://leanprover.zulipchat.com/#narrow/stream/263328-triage/topic/issue.20.231044.3A.20bundling.20morphisms
 * [#1044](https://github.com/leanprover-community/mathlib/pull/1044)
 * [#4985](https://github.com/leanprover-community/mathlib/pull/4985)
#### Estimated changes
Modified src/algebra/category/Module/basic.lean

Modified src/algebra/category/Module/limits.lean

Modified src/algebra/group/hom.lean
- \+ *lemma* map_one
- \+ *lemma* map_mul
- \+ *lemma* map_mul_eq_one
- \+ *lemma* map_div
- \- *lemma* one_hom.map_one
- \- *lemma* monoid_hom.map_one
- \- *lemma* monoid_with_zero_hom.map_one
- \- *lemma* monoid_with_zero_hom.map_zero
- \- *lemma* mul_hom.map_mul
- \- *lemma* monoid_hom.map_mul
- \- *lemma* monoid_with_zero_hom.map_mul
- \+/\- *theorem* map_inv
- \+/\- *theorem* map_mul_inv
- \+/\- *theorem* map_inv
- \+/\- *theorem* map_mul_inv
- \- *theorem* map_div

Modified src/algebra/module/linear_map.lean
- \+/\- *lemma* to_fun_eq_coe
- \+/\- *lemma* to_fun_eq_coe
- \- *lemma* map_add
- \- *lemma* map_zero
- \- *lemma* map_neg
- \- *lemma* map_sub
- \+/\- *theorem* ext
- \+/\- *theorem* ext

Modified src/algebra/ring/basic.lean
- \+/\- *lemma* map_bit0
- \+/\- *lemma* map_bit1
- \- *lemma* map_zero
- \- *lemma* map_one
- \- *lemma* map_add
- \- *lemma* map_mul
- \+/\- *lemma* map_bit0
- \+/\- *lemma* map_bit1
- \- *theorem* map_neg
- \- *theorem* map_sub

Modified src/analysis/complex/basic.lean

Modified src/analysis/normed_space/bounded_linear_maps.lean

Modified src/analysis/normed_space/dual.lean

Modified src/analysis/normed_space/finite_dimension.lean

Modified src/category_theory/preadditive/default.lean

Modified src/data/equiv/module.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \- *theorem* map_add
- \- *theorem* map_zero

Modified src/linear_algebra/dual.lean

Modified src/linear_algebra/multilinear/basic.lean
- \- *lemma* map_add

Modified src/ring_theory/derivation.lean
- \+ *lemma* to_fun_eq_coe
- \+/\- *lemma* congr_fun
- \+/\- *lemma* map_smul
- \+/\- *lemma* congr_fun
- \- *lemma* map_add
- \- *lemma* map_zero
- \+/\- *lemma* map_smul
- \- *lemma* map_neg
- \- *lemma* map_sub

Modified src/ring_theory/tensor_product.lean

Modified src/topology/algebra/module.lean
- \- *lemma* map_zero
- \- *lemma* map_add
- \- *lemma* map_sum
- \- *lemma* map_neg
- \- *lemma* map_sub
- \+/\- *theorem* coe_injective
- \+/\- *theorem* coe_injective



## [2021-12-10 11:52:56](https://github.com/leanprover-community/mathlib/commit/165e055)
refactor(group_theory/quotient_group): use `con` ([#10699](https://github.com/leanprover-community/mathlib/pull/10699))
Use `con` to define `group` structure on `G ⧸ N` instead of repeating the construction in this case.
#### Estimated changes
Modified src/group_theory/quotient_group.lean



## [2021-12-10 11:52:55](https://github.com/leanprover-community/mathlib/commit/9a24b3e)
chore(ring_theory/noetherian): rename `submodule.fg_map` to `submodule.fg.map` ([#10688](https://github.com/leanprover-community/mathlib/pull/10688))
This renames:
* `submodule.fg_map` to `submodule.fg.map` (to match `submonoid.fg.map` and enable dot notation)
* `submodule.map_fg_of_fg` to `ideal.fg.map`
* `submodule.fg_ker_ring_hom_comp` to `ideal.fg_ker_comp` to match `submodule.fg_ker_comp`
and defines a new `ideal.fg` alias to avoid unfolding to `submodule R R` and `submodule.span`.
#### Estimated changes
Modified src/ring_theory/finiteness.lean

Modified src/ring_theory/fractional_ideal.lean

Modified src/ring_theory/localization.lean

Modified src/ring_theory/nakayama.lean

Modified src/ring_theory/noetherian.lean
- \+ *lemma* _root_.ideal.fg.map
- \+ *lemma* _root_.ideal.fg_ker_comp
- \- *lemma* map_fg_of_fg
- \- *lemma* fg_ker_ring_hom_comp
- \+ *theorem* fg.map
- \- *theorem* fg_map
- \+ *def* _root_.ideal.fg



## [2021-12-10 11:52:54](https://github.com/leanprover-community/mathlib/commit/24cf723)
feat(ring_theory/polynomial/cyclotomic): generalize `is_root_cyclotomic` ([#10687](https://github.com/leanprover-community/mathlib/pull/10687))
#### Estimated changes
Modified src/ring_theory/polynomial/cyclotomic.lean
- \+/\- *lemma* is_root_cyclotomic
- \+/\- *lemma* is_root_cyclotomic



## [2021-12-10 11:52:52](https://github.com/leanprover-community/mathlib/commit/3dcdf93)
feat(group_theory/finiteness): Lemmas about finitely generated submonoids ([#10681](https://github.com/leanprover-community/mathlib/pull/10681))
#### Estimated changes
Modified src/group_theory/finiteness.lean
- \+ *lemma* submonoid.fg.map
- \+ *lemma* submonoid.fg.map_injective
- \+ *lemma* monoid.fg_iff_submonoid_fg
- \+ *lemma* monoid.fg_of_surjective
- \+ *lemma* submonoid.powers_fg



## [2021-12-10 11:52:50](https://github.com/leanprover-community/mathlib/commit/508fc18)
feat(ring_theory/ideal): Power of a spanning set is a spanning set ([#10656](https://github.com/leanprover-community/mathlib/pull/10656))
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+ *theorem* pow_multiset_sum_mem_span_pow
- \+ *theorem* sum_pow_mem_span_pow
- \+ *theorem* span_pow_eq_top



## [2021-12-10 09:20:23](https://github.com/leanprover-community/mathlib/commit/ce0e2c4)
feat(category_theory/limits): Pullback API ([#10620](https://github.com/leanprover-community/mathlib/pull/10620))
Needed for constructing fibered products of Schemes
#### Estimated changes
Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* pullback.congr_hom_inv
- \+ *lemma* pushout.congr_hom_inv
- \+ *def* is_limit_of_comp_mono
- \+ *def* is_colimit_of_epi_comp
- \+ *def* pullback.congr_hom
- \+ *def* pushout.congr_hom
- \+ *def* pullback_is_pullback_of_comp_mono
- \+ *def* pushout_is_pushout_of_epi_comp



## [2021-12-10 03:16:48](https://github.com/leanprover-community/mathlib/commit/e7959fb)
chore(scripts): update nolints.txt ([#10697](https://github.com/leanprover-community/mathlib/pull/10697))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt



## [2021-12-10 00:34:16](https://github.com/leanprover-community/mathlib/commit/1ecdf71)
chore(algebra/punit_instances): add `comm_cancel_monoid_with_zero`, `normalized_gcd_monoid`, and scalar action instances ([#10312](https://github.com/leanprover-community/mathlib/pull/10312))
Motivated by [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Is.200.20not.20equal.20to.201.3F/near/261366868). 
This also moves the simp lemmas closer to the instances they refer to.
#### Estimated changes
Modified src/algebra/punit_instances.lean
- \+/\- *lemma* one_eq
- \+/\- *lemma* mul_eq
- \+/\- *lemma* div_eq
- \+/\- *lemma* inv_eq
- \+ *lemma* gcd_eq
- \+ *lemma* lcm_eq
- \+ *lemma* norm_unit_eq
- \+/\- *lemma* top_eq
- \+/\- *lemma* bot_eq
- \+/\- *lemma* sup_eq
- \+/\- *lemma* inf_eq
- \+/\- *lemma* Sup_eq
- \+/\- *lemma* Inf_eq
- \+ *lemma* compl_eq
- \+ *lemma* sdiff_eq
- \+/\- *lemma* not_lt
- \+/\- *lemma* smul_eq
- \- *lemma* zero_eq
- \+/\- *lemma* one_eq
- \- *lemma* add_eq
- \+/\- *lemma* mul_eq
- \+/\- *lemma* div_eq
- \- *lemma* neg_eq
- \+/\- *lemma* inv_eq
- \+/\- *lemma* smul_eq
- \+/\- *lemma* top_eq
- \+/\- *lemma* bot_eq
- \+/\- *lemma* sup_eq
- \+/\- *lemma* inf_eq
- \+/\- *lemma* Sup_eq
- \+/\- *lemma* Inf_eq
- \+/\- *lemma* not_lt

Modified src/analysis/calculus/times_cont_diff.lean



## [2021-12-09 21:51:35](https://github.com/leanprover-community/mathlib/commit/61dd343)
feat(probability_theory/martingale): define martingales ([#10625](https://github.com/leanprover-community/mathlib/pull/10625))
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean
- \+ *lemma* condexp_condexp_of_le

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* trim_trim

Created src/probability_theory/martingale.lean
- \+ *lemma* martingale_zero
- \+ *lemma* adapted
- \+ *lemma* measurable
- \+ *lemma* condexp_ae_eq
- \+ *lemma* integrable
- \+ *lemma* add
- \+ *lemma* neg
- \+ *lemma* sub
- \+ *lemma* smul
- \+ *lemma* martingale_condexp
- \+ *def* martingale



## [2021-12-09 19:38:25](https://github.com/leanprover-community/mathlib/commit/e618cfe)
feat(topology/continuous_function/bounded): register instances of `star` structures ([#10570](https://github.com/leanprover-community/mathlib/pull/10570))
Prove that the bounded continuous functions which take values in a normed C⋆-ring themselves form a C⋆-ring. Moreover, if the codomain is a normed algebra and a star module over a normed ⋆-ring, then so are the bounded continuous functions. Thus the bounded continuous functions form a C⋆-algebra when the codomain is a C⋆-algebra.
#### Estimated changes
Modified src/analysis/normed_space/star.lean
- \+ *lemma* star_isometry
- \+ *def* star_normed_group_hom

Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* coe_star
- \+ *lemma* star_apply



## [2021-12-09 17:18:51](https://github.com/leanprover-community/mathlib/commit/2538626)
fix(tactic/ring): instantiate metavariables ([#10589](https://github.com/leanprover-community/mathlib/pull/10589))
Fixes the issue reported in [#10572](https://github.com/leanprover-community/mathlib/pull/10572).
- [x] depends on: [#10572](https://github.com/leanprover-community/mathlib/pull/10572)
#### Estimated changes
Modified src/geometry/manifold/instances/sphere.lean

Modified src/tactic/ring.lean

Modified test/ring.lean



## [2021-12-09 16:26:29](https://github.com/leanprover-community/mathlib/commit/94783be)
feat(algebra/algebra/spectrum): lemmas when scalars are a field ([#10476](https://github.com/leanprover-community/mathlib/pull/10476))
Prove some properties of the spectrum when the underlying scalar ring
is a field, and mostly assuming the algebra is itself nontrivial.
Show that the spectrum of a scalar (i.e., `algebra_map 𝕜 A k`) is
the singleton `{k}`. Prove that `σ (a * b) \ {0} = σ (b * a) \ {0}`.
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean
- \+/\- *lemma* is_unit.smul_sub_iff_sub_inv_smul
- \+ *lemma* zero_eq
- \+ *lemma* one_eq
- \+/\- *lemma* is_unit.smul_sub_iff_sub_inv_smul
- \+ *theorem* unit_smul_eq_smul
- \+ *theorem* scalar_eq
- \+/\- *theorem* smul_eq_smul
- \+ *theorem* nonzero_mul_eq_swap_mul
- \+/\- *theorem* smul_eq_smul



## [2021-12-09 14:52:57](https://github.com/leanprover-community/mathlib/commit/08215b5)
feat(data/finsupp/basic): lemmas on the support of the `tsub` of `finsupp`s ([#10651](https://github.com/leanprover-community/mathlib/pull/10651))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* support_tsub
- \+ *lemma* subset_support_tsub



## [2021-12-09 14:52:56](https://github.com/leanprover-community/mathlib/commit/9ef122d)
feat(measure_theory/integral/set_to_l1): properties of (dominated_)fin_meas_additive ([#10590](https://github.com/leanprover-community/mathlib/pull/10590))
Various properties of `fin_meas_additive` and `dominated_fin_meas_additive` which will be useful to generalize results about integrals to `set_to_fun`.
#### Estimated changes
Modified src/measure_theory/integral/set_to_l1.lean
- \+ *lemma* zero
- \+ *lemma* add
- \+ *lemma* smul
- \+ *lemma* of_eq_top_imp_eq_top
- \+ *lemma* of_smul_measure
- \+ *lemma* smul_measure
- \+ *lemma* smul_measure_iff
- \+ *lemma* map_empty_eq_zero
- \+/\- *lemma* map_Union_fin_meas_set_eq_sum
- \+ *lemma* zero
- \+ *lemma* eq_zero_of_measure_zero
- \+ *lemma* eq_zero
- \+ *lemma* add
- \+ *lemma* smul
- \+ *lemma* of_measure_le
- \+ *lemma* add_measure_right
- \+ *lemma* add_measure_left
- \+ *lemma* of_smul_measure
- \+ *lemma* of_measure_le_smul
- \- *lemma* map_empty_eq_zero_of_map_union
- \+/\- *lemma* map_Union_fin_meas_set_eq_sum
- \+/\- *def* dominated_fin_meas_additive
- \+/\- *def* dominated_fin_meas_additive



## [2021-12-09 13:20:38](https://github.com/leanprover-community/mathlib/commit/c23b54c)
feat(group_theory/submonoid): The monoid_hom from a submonoid to its image. ([#10680](https://github.com/leanprover-community/mathlib/pull/10680))
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup_map_surjective
- \+ *def* subgroup_comap
- \+ *def* subgroup_map

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* submonoid_map_surjective
- \+ *def* submonoid_comap
- \+ *def* submonoid_map



## [2021-12-09 13:20:36](https://github.com/leanprover-community/mathlib/commit/97e4468)
feat(analysis/calculus/deriv): generalize some lemmas ([#10639](https://github.com/leanprover-community/mathlib/pull/10639))
Generalize lemmas about the chain rule to work with different fields.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+/\- *theorem* has_deriv_within_at.scomp
- \+/\- *theorem* has_deriv_within_at.comp
- \+/\- *theorem* has_deriv_within_at.scomp
- \+/\- *theorem* has_deriv_within_at.comp

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_at_filter.restrict_scalars
- \+/\- *theorem* has_fderiv_at_filter.comp
- \+/\- *theorem* has_fderiv_at.comp_has_fderiv_within_at
- \+/\- *theorem* has_fderiv_at_filter.comp
- \+/\- *theorem* has_fderiv_at.comp_has_fderiv_within_at

Modified src/measure_theory/integral/interval_integral.lean



## [2021-12-09 11:18:26](https://github.com/leanprover-community/mathlib/commit/bfe595d)
feat(order/filter,topology/instances/real): lemmas about `at_top`, `at_bot`, and `cocompact` ([#10652](https://github.com/leanprover-community/mathlib/pull/10652))
* prove `comap abs at_top = at_bot ⊔ at_top`;
* prove `comap coe at_top = at_top` and `comap coe at_bot = at_bot` for coercion from `ℕ`, `ℤ`, or `ℚ` to an archimedian semiring, ring, or field, respectively;
* prove `cocompact ℤ = at_bot ⊔ at_top` and `cocompact ℝ = at_bot ⊔ at_top`.
#### Estimated changes
Modified src/algebra/order/group.lean
- \+/\- *lemma* abs_le
- \+ *lemma* le_abs'
- \+/\- *lemma* abs_le

Modified src/order/filter/archimedean.lean
- \+ *lemma* nat.comap_coe_at_top
- \+ *lemma* int.comap_coe_at_top
- \+ *lemma* int.comap_coe_at_bot
- \+ *lemma* tendsto_coe_int_at_bot_iff
- \+ *lemma* rat.comap_coe_at_top
- \+ *lemma* rat.comap_coe_at_bot
- \+ *lemma* tendsto_coe_rat_at_bot_iff

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* comap_abs_at_top
- \+ *lemma* comap_embedding_at_top
- \+ *lemma* comap_embedding_at_bot

Modified src/topology/instances/real.lean
- \+ *lemma* cocompact_eq
- \+ *lemma* real.cocompact_eq



## [2021-12-09 09:57:14](https://github.com/leanprover-community/mathlib/commit/e3d9adf)
chore(measure_theory/function/conditional_expectation): change condexp notation ([#10584](https://github.com/leanprover-community/mathlib/pull/10584))
The previous definition and notation showed the `measurable_space` argument only through the other argument `m \le m0`, which tends to be replaced by `_` in the goal view if it becomes complicated.
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean
- \+/\- *lemma* condexp_const
- \+/\- *lemma* condexp_ae_eq_condexp_L1
- \+/\- *lemma* condexp_undef
- \+/\- *lemma* condexp_zero
- \+/\- *lemma* measurable_condexp
- \+/\- *lemma* integrable_condexp
- \+/\- *lemma* integral_condexp
- \+/\- *lemma* condexp_smul
- \+/\- *lemma* condexp_neg
- \+/\- *lemma* condexp_const
- \+/\- *lemma* condexp_ae_eq_condexp_L1
- \+/\- *lemma* condexp_undef
- \+/\- *lemma* condexp_zero
- \+/\- *lemma* measurable_condexp
- \+/\- *lemma* integrable_condexp
- \+/\- *lemma* integral_condexp
- \+/\- *lemma* condexp_smul
- \+/\- *lemma* condexp_neg

Modified src/probability_theory/notation.lean



## [2021-12-09 08:54:18](https://github.com/leanprover-community/mathlib/commit/70171ac)
feat(topology/instances/real_vector_space): add an `is_scalar_tower` instance ([#10490](https://github.com/leanprover-community/mathlib/pull/10490))
There is at most one topological real vector space structure on a topological additive group, so `[is_scalar_tower real A E]` holds automatically as long as `A` is a topological real algebra and `E` is a topological module over `A`.
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean

Modified src/analysis/calculus/parametric_integral.lean

Modified src/analysis/calculus/parametric_interval_integral.lean

Modified src/analysis/complex/conformal.lean

Modified src/analysis/complex/real_deriv.lean

Modified src/analysis/inner_product_space/basic.lean
- \+/\- *lemma* is_bounded_bilinear_map_inner
- \+/\- *lemma* is_bounded_bilinear_map_inner

Modified src/analysis/inner_product_space/calculus.lean

Modified src/analysis/inner_product_space/projection.lean

Modified src/analysis/inner_product_space/rayleigh.lean

Modified src/data/complex/is_R_or_C.lean

Modified src/measure_theory/function/conditional_expectation.lean
- \+/\- *lemma* integral_condexp_L2_eq
- \+/\- *lemma* integral_condexp_L2_eq

Modified src/measure_theory/function/l2_space.lean
- \+/\- *lemma* inner_def
- \+/\- *lemma* inner_def

Modified src/measure_theory/function/lp_space.lean

Modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* integral_const_mul
- \+/\- *lemma* integral_mul_const
- \+/\- *lemma* integral_div
- \+/\- *lemma* integral_const_mul
- \+/\- *lemma* integral_mul_const
- \+/\- *lemma* integral_div

Modified src/measure_theory/integral/set_integral.lean
- \+/\- *lemma* integral_smul_const
- \+/\- *lemma* integral_smul_const

Modified src/topology/instances/real_vector_space.lean
- \+ *def* add_equiv.to_real_linear_equiv



## [2021-12-09 07:29:46](https://github.com/leanprover-community/mathlib/commit/4efa9d8)
chore(algebra/direct_limit): remove module.directed_system ([#10636](https://github.com/leanprover-community/mathlib/pull/10636))
This typeclass duplicated `_root_.directed_system`
#### Estimated changes
Modified src/algebra/category/Module/limits.lean

Modified src/algebra/direct_limit.lean
- \+ *lemma* directed_system.map_self
- \+ *lemma* directed_system.map_map
- \+ *lemma* totalize_of_le
- \+ *lemma* totalize_of_not_le
- \- *lemma* totalize_apply



## [2021-12-09 05:38:21](https://github.com/leanprover-community/mathlib/commit/11bf7e5)
feat(analysis/normed_space/weak_dual): add polar sets in preparation for Banach-Alaoglu theorem ([#9836](https://github.com/leanprover-community/mathlib/pull/9836))
The first of two parts to add the Banach-Alaoglu theorem about the compactness of the closed unit ball (and more generally polar sets of neighborhoods of the origin) of the dual of a normed space in the weak-star topology.
This first half is about polar sets (for a set `s` in a normed space `E`, the `polar s` is the subset of `weak_dual _ E` consisting of the functionals that evaluate to something of norm at most one at all elements of `s`).
#### Estimated changes
Modified src/analysis/normed_space/dual.lean
- \+ *lemma* zero_mem_polar
- \+ *lemma* polar_eq_Inter
- \+ *lemma* polar_empty
- \+ *lemma* smul_mem_polar
- \+ *lemma* polar_closed_ball
- \+ *lemma* polar_bounded_of_nhds_zero
- \+ *def* polar

Modified src/analysis/normed_space/weak_dual.lean
- \+ *lemma* to_normed_dual.preimage_closed_unit_ball
- \+ *lemma* weak_dual.is_closed_polar
- \+ *def* polar



## [2021-12-09 03:56:43](https://github.com/leanprover-community/mathlib/commit/fc3116f)
doc(data/nat/prime): fix links ([#10677](https://github.com/leanprover-community/mathlib/pull/10677))
#### Estimated changes
Modified src/data/nat/prime.lean



## [2021-12-09 03:56:42](https://github.com/leanprover-community/mathlib/commit/ab31673)
feat(data/finset/basic): val_le_iff_val_subset ([#10603](https://github.com/leanprover-community/mathlib/pull/10603))
I'm not sure if we have something like this already on mathlib. The application of `val_le_of_val_subset` that I have in mind is to deduce
```
theorem polynomial.card_roots'' {F : Type u} [field F]{p : polynomial F}(h : p ≠ 0)
{Z : finset F} (hZ : ∀ z ∈ Z, polynomial.eval z p = 0) : Z.card ≤ p.nat_degree
```
from [polynomial.card_roots' ](https://github.com/leanprover-community/mathlib/blob/1376f53dacd3c3ccd3c345b6b8552cce96c5d0c8/src/data/polynomial/ring_division.lean#L318)
If this approach seems right, I will send the proof of `polynomial.card_roots''` in a follow up PR.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* val_le_iff_val_subset

Modified src/data/multiset/basic.lean
- \+ *theorem* one_le_count_iff_mem



## [2021-12-09 01:13:05](https://github.com/leanprover-community/mathlib/commit/60c1d60)
feat(data/mv_polynomial/basic)  induction_on'' ([#10621](https://github.com/leanprover-community/mathlib/pull/10621))
A new flavor of `induction_on` which is useful when we do not have ` h_add : ∀p q, M p → M q → M (p + q)` but we have
```
h_add_weak : ∀ (a : σ →₀ ℕ) (b : R) (f : (σ →₀ ℕ) →₀ R),  a ∉ f.support → b ≠ 0 → M f → M (monomial a b + f)
```
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* induction_on_monomial
- \+ *lemma* induction_on'''
- \+ *lemma* induction_on''
- \+/\- *lemma* induction_on
- \+/\- *lemma* induction_on



## [2021-12-09 01:13:04](https://github.com/leanprover-community/mathlib/commit/e14dc11)
feat(data/int/basic): add `nat_abs_eq_nat_abs_iff_*` lemmas for nonnegative and nonpositive arguments ([#10611](https://github.com/leanprover-community/mathlib/pull/10611))
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* nat_abs_inj_of_nonneg_of_nonneg
- \+ *lemma* nat_abs_inj_of_nonpos_of_nonpos
- \+ *lemma* nat_abs_inj_of_nonneg_of_nonpos
- \+ *lemma* nat_abs_inj_of_nonpos_of_nonneg
- \+ *lemma* strict_mono_on_nat_abs
- \+ *lemma* strict_anti_on_nat_abs
- \+ *lemma* inj_on_nat_abs_Ici
- \+ *lemma* inj_on_nat_abs_Iic



## [2021-12-08 22:28:20](https://github.com/leanprover-community/mathlib/commit/baab5d3)
refactor(data/matrix): reverse the direction of `matrix.minor_mul_equiv` ([#10657](https://github.com/leanprover-community/mathlib/pull/10657))
In [#10350](https://github.com/leanprover-community/mathlib/pull/10350) this change was proposed, since we apparently use that backwards way more than we use it forwards.
We also change `reindex_linear_equiv_mul`, which is similarly much more popular backwards than forwards.
Closes: [#10638](https://github.com/leanprover-community/mathlib/pull/10638)
#### Estimated changes
Modified src/algebra/lie/matrix.lean

Modified src/data/matrix/basic.lean

Modified src/linear_algebra/charpoly/to_matrix.lean

Modified src/linear_algebra/determinant.lean

Modified src/linear_algebra/matrix/reindex.lean



## [2021-12-08 22:28:19](https://github.com/leanprover-community/mathlib/commit/2ea1fb6)
feat(data/list/range): fin_range_succ_eq_map ([#10654](https://github.com/leanprover-community/mathlib/pull/10654))
#### Estimated changes
Modified src/data/list/range.lean
- \+ *lemma* map_coe_fin_range
- \+ *lemma* fin_range_succ_eq_map



## [2021-12-08 22:28:18](https://github.com/leanprover-community/mathlib/commit/fdb773a)
chore(algebra/tropical/basic): golf and clean ([#10633](https://github.com/leanprover-community/mathlib/pull/10633))
#### Estimated changes
Modified src/algebra/tropical/basic.lean
- \+/\- *lemma* untrop_pow
- \+ *lemma* trop_smul
- \+/\- *lemma* untrop_pow



## [2021-12-08 22:28:16](https://github.com/leanprover-community/mathlib/commit/bcd9a74)
refactor(data/complex/is_R_or_C): `finite_dimensional.proper_is_R_or_C` is not an `instance` anymore ([#10629](https://github.com/leanprover-community/mathlib/pull/10629))
This instance caused a search for `[finite_dimensional ?x E]` with an unknown `?x`. Turn it into a lemma and add `haveI` to some proofs. Also add an instance for `K ∙ x`.
#### Estimated changes
Modified src/analysis/inner_product_space/projection.lean
- \+ *lemma* orthogonal_family.submodule_is_internal_iff_of_is_complete

Modified src/analysis/inner_product_space/rayleigh.lean

Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* proper_is_R_or_C



## [2021-12-08 22:28:15](https://github.com/leanprover-community/mathlib/commit/e289343)
feat(algebra/graded_monoid): add lemmas about power and product membership ([#10627](https://github.com/leanprover-community/mathlib/pull/10627))
This adds:
* `set_like.graded_monoid.pow_mem`
* `set_like.graded_monoid.list_prod_map_mem`
* `set_like.graded_monoid.list_prod_of_fn_mem`
It doesn't bother to add the multiset and finset versions for now, because these are not imported at this point, and require the ring to be commutative.
#### Estimated changes
Modified src/algebra/graded_monoid.lean
- \+ *lemma* pow_mem
- \+ *lemma* list_prod_map_mem
- \+ *lemma* list_prod_of_fn_mem
- \+ *lemma* set_like.coe_gnpow
- \- *lemma* set_like.coe_gpow



## [2021-12-08 18:44:55](https://github.com/leanprover-community/mathlib/commit/1d0bb86)
fix(data/finsupp/basic): add missing decidable arguments ([#10672](https://github.com/leanprover-community/mathlib/pull/10672))
`finsupp` is classical, meaning that `def`s should just use noncomputable decidable instances rather than taking arguments that make more work for mathematicians.
However, this doesn't mean that lemma _statements_ should use noncomputable decidable instances, as this just makes the lemma less general and harder to apply (as shown by the `congr` removed elsewhere in the diff).
These were found by removing `open_locale classical` from the top of the file, adding `by classical; exact` to some definitions, and then fixing the broken lemma statements. In future we should detect this type of mistake with a linter.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+/\- *lemma* single_eq_update
- \+/\- *lemma* single_eq_pi_single
- \+/\- *lemma* support_single_disjoint
- \+/\- *lemma* equiv_fun_on_fintype_single
- \+/\- *lemma* equiv_fun_on_fintype_symm_single
- \+/\- *lemma* coe_update
- \+/\- *lemma* support_update
- \+/\- *lemma* support_update_zero
- \+/\- *lemma* support_update_ne_zero
- \+/\- *lemma* to_multiset_symm_apply
- \+/\- *lemma* single_eq_update
- \+/\- *lemma* single_eq_pi_single
- \+/\- *lemma* support_single_disjoint
- \+/\- *lemma* equiv_fun_on_fintype_single
- \+/\- *lemma* equiv_fun_on_fintype_symm_single
- \+/\- *lemma* coe_update
- \+/\- *lemma* support_update
- \+/\- *lemma* support_update_zero
- \+/\- *lemma* support_update_ne_zero
- \+/\- *lemma* to_multiset_symm_apply

Modified src/data/finsupp/lattice.lean
- \+/\- *lemma* support_inf
- \+/\- *lemma* support_sup
- \+/\- *lemma* disjoint_iff
- \+/\- *lemma* support_inf
- \+/\- *lemma* support_sup
- \+/\- *lemma* disjoint_iff

Modified src/data/finsupp/pointwise.lean
- \+/\- *lemma* support_mul
- \+/\- *lemma* support_mul

Modified src/data/polynomial/basic.lean



## [2021-12-08 17:16:46](https://github.com/leanprover-community/mathlib/commit/2ce95ca)
refactor(data/finsupp): use `{f : α →₀ M | ∃ a b, f = single a b}` instead of union of ranges ([#10671](https://github.com/leanprover-community/mathlib/pull/10671))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* add_closure_set_of_eq_single
- \- *lemma* add_closure_Union_range_single



## [2021-12-08 17:16:44](https://github.com/leanprover-community/mathlib/commit/8ab1b3b)
feat(measure_theory/probability_mass_function): Calculate supports of pmf constructions ([#10371](https://github.com/leanprover-community/mathlib/pull/10371))
This PR gives explicit descriptions for the `support` of the various `pmf` constructions in mathlib. 
This also tries to clean up the variable declarations in the different sections, so that all the lemmas don't need to specify them explicitly.
#### Estimated changes
Modified src/measure_theory/probability_mass_function/basic.lean
- \+/\- *lemma* mem_support_iff
- \+/\- *lemma* apply_eq_zero_iff
- \+/\- *lemma* pure_apply
- \+ *lemma* support_pure
- \+ *lemma* mem_support_pure_iff:
- \+/\- *lemma* bind_apply
- \+ *lemma* support_bind
- \+ *lemma* mem_support_bind_iff
- \+/\- *lemma* mem_support_iff
- \+/\- *lemma* apply_eq_zero_iff
- \+/\- *lemma* pure_apply
- \- *lemma* mem_support_pure_iff
- \+/\- *lemma* bind_apply

Modified src/measure_theory/probability_mass_function/constructions.lean
- \+ *lemma* map_apply
- \+ *lemma* support_map
- \+ *lemma* mem_support_map_iff
- \+/\- *lemma* bind_pure_comp
- \+/\- *lemma* map_id
- \+/\- *lemma* map_comp
- \+/\- *lemma* pure_map
- \+ *lemma* seq_apply
- \+ *lemma* support_seq
- \+ *lemma* mem_support_seq_iff
- \+/\- *lemma* of_finset_apply
- \+ *lemma* support_of_finset
- \+ *lemma* mem_support_of_finset_iff
- \+/\- *lemma* of_finset_apply_of_not_mem
- \+/\- *lemma* of_fintype_apply
- \+ *lemma* support_of_fintype
- \+ *lemma* mem_support_of_fintype_iff
- \+/\- *lemma* of_multiset_apply
- \+ *lemma* support_of_multiset
- \+ *lemma* mem_support_of_multiset_iff
- \+/\- *lemma* of_multiset_apply_of_not_mem
- \+/\- *lemma* uniform_of_finset_apply
- \+/\- *lemma* uniform_of_finset_apply_of_mem
- \+/\- *lemma* uniform_of_finset_apply_of_not_mem
- \+ *lemma* support_uniform_of_finset
- \+ *lemma* mem_support_uniform_of_finset_iff
- \+/\- *lemma* uniform_of_fintype_apply
- \+ *lemma* support_uniform_of_fintype
- \+ *lemma* mem_support_uniform_of_fintype_iff
- \+/\- *lemma* normalize_apply
- \+ *lemma* support_normalize
- \+ *lemma* mem_support_normalize_iff
- \+/\- *lemma* filter_apply
- \+/\- *lemma* filter_apply_eq_zero_of_not_mem
- \+ *lemma* support_filter
- \+ *lemma* mem_support_filter_iff
- \+/\- *lemma* filter_apply_eq_zero_iff
- \+/\- *lemma* filter_apply_ne_zero_iff
- \+ *lemma* bernoulli_apply
- \+ *lemma* support_bernoulli
- \+ *lemma* mem_support_bernoulli_iff
- \+/\- *lemma* bind_on_support_apply
- \+ *lemma* support_bind_on_support
- \+/\- *lemma* mem_support_bind_on_support_iff
- \+/\- *lemma* coe_bind_on_support_apply
- \+/\- *lemma* bind_on_support_eq_zero_iff
- \+/\- *lemma* pure_bind_on_support
- \+/\- *lemma* bind_pure_comp
- \+/\- *lemma* map_id
- \+/\- *lemma* map_comp
- \+/\- *lemma* pure_map
- \+/\- *lemma* of_finset_apply
- \+/\- *lemma* of_finset_apply_of_not_mem
- \+/\- *lemma* of_fintype_apply
- \+/\- *lemma* of_multiset_apply
- \+/\- *lemma* of_multiset_apply_of_not_mem
- \+/\- *lemma* uniform_of_finset_apply
- \+/\- *lemma* uniform_of_finset_apply_of_mem
- \+/\- *lemma* uniform_of_finset_apply_of_not_mem
- \+/\- *lemma* uniform_of_fintype_apply
- \+/\- *lemma* normalize_apply
- \+/\- *lemma* filter_apply
- \+/\- *lemma* filter_apply_eq_zero_of_not_mem
- \+/\- *lemma* filter_apply_eq_zero_iff
- \+/\- *lemma* filter_apply_ne_zero_iff
- \- *lemma* bernuolli_apply
- \+/\- *lemma* bind_on_support_apply
- \+/\- *lemma* coe_bind_on_support_apply
- \+/\- *lemma* mem_support_bind_on_support_iff
- \+/\- *lemma* bind_on_support_eq_zero_iff
- \+/\- *lemma* pure_bind_on_support
- \+/\- *def* seq
- \+/\- *def* of_finset
- \+/\- *def* of_fintype
- \+/\- *def* filter
- \+/\- *def* bind_on_support
- \+/\- *def* seq
- \+/\- *def* of_finset
- \+/\- *def* of_fintype
- \+/\- *def* filter
- \+/\- *def* bind_on_support



## [2021-12-08 15:28:51](https://github.com/leanprover-community/mathlib/commit/678566f)
feat(topology/algebra/group): Addition of interiors ([#10659](https://github.com/leanprover-community/mathlib/pull/10659))
This proves `interior s * t ⊆ interior (s * t)`, a few prerequisites, and generalizes to `is_open.mul_left`/`is_open.mul_right`.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* mul_subset_mul_left
- \+ *lemma* mul_subset_mul_right

Modified src/data/set/basic.lean
- \+/\- *lemma* inclusion_self
- \+ *lemma* image2_subset_left
- \+ *lemma* image2_subset_right
- \+/\- *lemma* inclusion_self
- \+/\- *theorem* image_preimage_subset
- \+/\- *theorem* image_preimage_subset

Modified src/topology/algebra/group.lean
- \+/\- *lemma* is_open.mul_left
- \+/\- *lemma* is_open.mul_right
- \+ *lemma* subset_interior_mul_left
- \+ *lemma* subset_interior_mul_right
- \+ *lemma* subset_interior_mul
- \+ *lemma* is_open.inv
- \+ *lemma* is_closed.inv
- \+/\- *lemma* is_open.mul_left
- \+/\- *lemma* is_open.mul_right



## [2021-12-08 13:44:00](https://github.com/leanprover-community/mathlib/commit/eedb906)
feat(measure_theory/integral): `∫ x in b..b+a, f x = ∫ x in c..c + a, f x` for a periodic `f` ([#10477](https://github.com/leanprover-community/mathlib/pull/10477))
#### Estimated changes
Modified src/algebra/periodic.lean
- \+ *lemma* periodic.map_vadd_zmultiples
- \+ *lemma* periodic.map_vadd_multiples

Modified src/group_theory/coset.lean
- \+ *lemma* quotient_lift_on_coe

Modified src/group_theory/quotient_group.lean
- \+ *lemma* coe_div

Modified src/measure_theory/group/arithmetic.lean

Modified src/measure_theory/group/fundamental_domain.lean
- \+ *lemma* mk'

Created src/measure_theory/integral/periodic.lean
- \+ *lemma* is_add_fundamental_domain_Ioc
- \+ *lemma* interval_integral_add_eq_of_pos
- \+ *lemma* interval_integral_add_eq



## [2021-12-08 05:53:32](https://github.com/leanprover-community/mathlib/commit/4d56716)
fix(data/finsupp/basic): add missing decidable argument ([#10649](https://github.com/leanprover-community/mathlib/pull/10649))
While `finsupp.erase` is classical and requires no decidability, `finset.erase` is not so.
Without this argument, this lemma does not apply in the general case, and introduces mismatching decidable instances. With it, a `congr` is no longer needed elsewhere in mathlib.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+/\- *lemma* support_erase
- \+/\- *lemma* support_erase

Modified src/data/polynomial/basic.lean



## [2021-12-08 05:53:31](https://github.com/leanprover-community/mathlib/commit/e5ba338)
fix(algebra/direct_sum): change `ring_hom_ext` to not duplicate `ring_hom_ext'` ([#10640](https://github.com/leanprover-community/mathlib/pull/10640))
These two lemmas differed only in the explicitness of their binders.
The statement of the unprimed version has been changed to be fully applied.
This also renames `alg_hom_ext` to `alg_hom_ext'` to make way for the fully applied version. This is consistent with `direct_sum.add_hom_ext` vs `direct_sum.add_hom_ext'`.
#### Estimated changes
Modified src/algebra/direct_sum/algebra.lean
- \+ *lemma* alg_hom_ext'
- \+/\- *lemma* alg_hom_ext
- \+/\- *lemma* alg_hom_ext

Modified src/algebra/direct_sum/ring.lean
- \+/\- *lemma* ring_hom_ext'
- \+/\- *lemma* ring_hom_ext
- \+/\- *lemma* ring_hom_ext'
- \+/\- *lemma* ring_hom_ext



## [2021-12-08 04:59:26](https://github.com/leanprover-community/mathlib/commit/b495fdf)
feat(category_theory): Filtered colimits preserves finite limits in algebraic categories ([#10604](https://github.com/leanprover-community/mathlib/pull/10604))
#### Estimated changes
Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean

Modified src/category_theory/limits/preserves/functor_category.lean

Modified src/category_theory/limits/preserves/limits.lean
- \+ *def* preserves_limit_nat_iso
- \+ *def* preserves_colimit_nat_iso



## [2021-12-08 03:50:05](https://github.com/leanprover-community/mathlib/commit/2bfa768)
feat(analysis/normed_space/operator_norm): module and norm instances on continuous semilinear maps ([#10494](https://github.com/leanprover-community/mathlib/pull/10494))
This PR adds a module and a norm instance on continuous semilinear maps, generalizes most of the results in `operator_norm.lean` to the semilinear case. Many of these results require the ring homomorphism to be isometric, which is expressed via the new typeclass `[ring_hom_isometric σ]`.
#### Estimated changes
Modified src/analysis/calculus/fderiv_measurable.lean

Modified src/analysis/normed_space/basic.lean

Modified src/analysis/normed_space/dual.lean

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* norm_image_of_norm_zero
- \+/\- *lemma* linear_map.bound_of_shell_semi_normed
- \+/\- *lemma* linear_map.bound_of_continuous
- \+/\- *lemma* norm_def
- \+/\- *lemma* bounds_nonempty
- \+/\- *lemma* bounds_bdd_below
- \+/\- *lemma* op_norm_le_bound
- \+/\- *lemma* op_norm_eq_of_bounds
- \+/\- *lemma* op_norm_neg
- \+/\- *lemma* op_norm_le_of_shell
- \+/\- *lemma* op_norm_le_of_ball
- \+/\- *lemma* op_norm_le_of_nhds_zero
- \+/\- *lemma* op_norm_le_of_shell'
- \+/\- *lemma* op_norm_comp_le
- \+/\- *lemma* op_norm_prod
- \+/\- *lemma* isometry_iff_norm
- \+/\- *lemma* norm_to_continuous_linear_map_le
- \+/\- *lemma* mk_continuous_norm_le
- \+/\- *lemma* mk_continuous_norm_le'
- \+/\- *lemma* mk_continuous₂_apply
- \+/\- *lemma* mk_continuous₂_norm_le'
- \+/\- *lemma* mk_continuous₂_norm_le
- \+/\- *lemma* flip_apply
- \+/\- *lemma* flip_flip
- \+/\- *lemma* op_norm_flip
- \+/\- *lemma* flip_add
- \+/\- *lemma* flip_smul
- \+ *lemma* flipₗᵢ'_symm
- \+ *lemma* coe_flipₗᵢ'
- \+/\- *lemma* flipₗᵢ_symm
- \+/\- *lemma* coe_flipₗᵢ
- \+ *lemma* apply_apply'
- \+/\- *lemma* apply_apply
- \+ *lemma* compSL_apply
- \+/\- *lemma* compL_apply
- \+/\- *lemma* norm_restrict_scalars
- \+/\- *lemma* homothety_inverse
- \+/\- *lemma* bilinear_comp_apply
- \+/\- *lemma* coe_deriv₂
- \+/\- *lemma* map_add₂
- \+/\- *lemma* linear_map.bound_of_shell
- \+/\- *lemma* homothety_norm
- \+/\- *lemma* extend_unique
- \+/\- *lemma* extend_zero
- \+/\- *lemma* norm_to_continuous_linear_map
- \+/\- *lemma* op_norm_comp_linear_isometry_equiv
- \+/\- *lemma* norm_smul_right_apply
- \+/\- *lemma* nnnorm_smul_right_apply
- \+/\- *lemma* norm_smul_rightL_apply
- \+/\- *lemma* norm_smul_rightL
- \+/\- *lemma* uniform_embedding
- \+/\- *lemma* one_le_norm_mul_norm_symm
- \+/\- *lemma* norm_pos
- \+/\- *lemma* norm_symm_pos
- \+/\- *lemma* nnnorm_symm_pos
- \+/\- *lemma* subsingleton_or_norm_symm_pos
- \+/\- *lemma* subsingleton_or_nnnorm_symm_pos
- \+/\- *lemma* linear_equiv.uniform_embedding
- \+/\- *lemma* linear_map.bound_of_shell_semi_normed
- \+/\- *lemma* norm_image_of_norm_zero
- \+/\- *lemma* linear_map.bound_of_continuous
- \+/\- *lemma* norm_def
- \+/\- *lemma* bounds_nonempty
- \+/\- *lemma* bounds_bdd_below
- \+/\- *lemma* op_norm_le_bound
- \+/\- *lemma* op_norm_le_of_shell
- \+/\- *lemma* op_norm_le_of_ball
- \+/\- *lemma* op_norm_le_of_nhds_zero
- \+/\- *lemma* op_norm_le_of_shell'
- \+/\- *lemma* op_norm_eq_of_bounds
- \+/\- *lemma* op_norm_neg
- \+/\- *lemma* op_norm_comp_le
- \+/\- *lemma* op_norm_prod
- \+/\- *lemma* isometry_iff_norm
- \+/\- *lemma* norm_to_continuous_linear_map_le
- \+/\- *lemma* mk_continuous_norm_le
- \+/\- *lemma* mk_continuous_norm_le'
- \+/\- *lemma* mk_continuous₂_apply
- \+/\- *lemma* mk_continuous₂_norm_le'
- \+/\- *lemma* mk_continuous₂_norm_le
- \+/\- *lemma* flip_apply
- \+/\- *lemma* flip_flip
- \+/\- *lemma* op_norm_flip
- \+/\- *lemma* flip_add
- \+/\- *lemma* flip_smul
- \+/\- *lemma* flipₗᵢ_symm
- \+/\- *lemma* coe_flipₗᵢ
- \+/\- *lemma* apply_apply
- \+/\- *lemma* compL_apply
- \+/\- *lemma* norm_restrict_scalars
- \+/\- *lemma* homothety_inverse
- \+/\- *lemma* bilinear_comp_apply
- \+/\- *lemma* coe_deriv₂
- \+/\- *lemma* map_add₂
- \+/\- *lemma* linear_map.bound_of_shell
- \+/\- *lemma* homothety_norm
- \+/\- *lemma* extend_unique
- \+/\- *lemma* extend_zero
- \+/\- *lemma* norm_to_continuous_linear_map
- \+/\- *lemma* op_norm_comp_linear_isometry_equiv
- \+/\- *lemma* norm_smul_right_apply
- \+/\- *lemma* nnnorm_smul_right_apply
- \+/\- *lemma* norm_smul_rightL_apply
- \+/\- *lemma* norm_smul_rightL
- \+/\- *lemma* uniform_embedding
- \+/\- *lemma* one_le_norm_mul_norm_symm
- \+/\- *lemma* norm_pos
- \+/\- *lemma* norm_symm_pos
- \+/\- *lemma* nnnorm_symm_pos
- \+/\- *lemma* subsingleton_or_norm_symm_pos
- \+/\- *lemma* subsingleton_or_nnnorm_symm_pos
- \+/\- *lemma* linear_equiv.uniform_embedding
- \+/\- *theorem* bound
- \+/\- *theorem* op_norm_le_of_lipschitz
- \+/\- *theorem* op_norm_zero
- \+/\- *theorem* op_norm_le_bound₂
- \+/\- *theorem* le_op_norm₂
- \+/\- *theorem* is_O_with_comp
- \+/\- *theorem* is_O_comp
- \+/\- *theorem* is_O_with_sub
- \+/\- *theorem* is_O_sub
- \+/\- *theorem* is_O_comp_rev
- \+/\- *theorem* is_O_sub_rev
- \+/\- *theorem* antilipschitz_of_uniform_embedding
- \+/\- *theorem* bound
- \+/\- *theorem* op_norm_le_of_lipschitz
- \+/\- *theorem* op_norm_zero
- \+/\- *theorem* le_op_norm₂
- \+/\- *theorem* op_norm_le_bound₂
- \+/\- *theorem* is_O_with_comp
- \+/\- *theorem* is_O_comp
- \+/\- *theorem* is_O_with_sub
- \+/\- *theorem* is_O_sub
- \+/\- *theorem* is_O_comp_rev
- \+/\- *theorem* is_O_sub_rev
- \+/\- *theorem* antilipschitz_of_uniform_embedding
- \+/\- *def* of_homothety
- \+/\- *def* op_norm
- \+/\- *def* prodₗᵢ
- \+/\- *def* mk_continuous₂
- \+/\- *def* flip
- \+ *def* flipₗᵢ'
- \+/\- *def* flipₗᵢ
- \+ *def* apply'
- \+/\- *def* apply
- \+ *def* compSL
- \+/\- *def* compL
- \+/\- *def* restrict_scalars_isometry
- \+/\- *def* restrict_scalarsL
- \+/\- *def* of_homothety
- \+/\- *def* linear_equiv.to_continuous_linear_equiv_of_bounds
- \+/\- *def* bilinear_comp
- \+/\- *def* deriv₂
- \+/\- *def* extend
- \+/\- *def* smul_rightL
- \+/\- *def* of_homothety
- \+/\- *def* op_norm
- \+/\- *def* prodₗᵢ
- \+/\- *def* mk_continuous₂
- \+/\- *def* flip
- \+/\- *def* flipₗᵢ
- \+/\- *def* apply
- \+/\- *def* compL
- \+/\- *def* restrict_scalars_isometry
- \+/\- *def* restrict_scalarsL
- \+/\- *def* of_homothety
- \+/\- *def* linear_equiv.to_continuous_linear_equiv_of_bounds
- \+/\- *def* bilinear_comp
- \+/\- *def* deriv₂
- \+/\- *def* extend
- \+/\- *def* smul_rightL

Modified src/data/complex/is_R_or_C.lean

Modified src/topology/algebra/module.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul'
- \+/\- *lemma* comp_smul
- \+/\- *lemma* prod_ext_iff
- \+/\- *lemma* prod_ext
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul'
- \+/\- *lemma* comp_smul
- \+/\- *lemma* prod_ext_iff
- \+/\- *lemma* prod_ext
- \+/\- *def* prod_equiv
- \+/\- *def* prodₗ
- \+/\- *def* coe_lm
- \+ *def* coe_lmₛₗ
- \+/\- *def* prod_equiv
- \+/\- *def* prodₗ
- \+/\- *def* coe_lm



## [2021-12-08 02:36:46](https://github.com/leanprover-community/mathlib/commit/1a92bc9)
chore(scripts): update nolints.txt ([#10662](https://github.com/leanprover-community/mathlib/pull/10662))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt



## [2021-12-07 21:13:01](https://github.com/leanprover-community/mathlib/commit/eaa9e87)
chore(measure_theory/integral/set_to_l1): change definition of dominated_fin_meas_additive ([#10585](https://github.com/leanprover-community/mathlib/pull/10585))
Change the definition to check the property only on measurable sets with finite measure (like every other property in that file).
Also make some arguments of `set_to_fun` explicit to improve readability.
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean

Modified src/measure_theory/integral/bochner.lean

Modified src/measure_theory/integral/set_to_l1.lean
- \+ *lemma* norm_set_to_simple_func_le_sum_mul_norm_of_integrable
- \+/\- *lemma* norm_set_to_L1s_le
- \- *lemma* norm_set_to_simple_func_le_sum_mul_norm
- \+/\- *lemma* norm_set_to_L1s_le



## [2021-12-07 19:16:26](https://github.com/leanprover-community/mathlib/commit/54aeec7)
feat(topology/algebra/ordered/basic): Interior of `{x | f x ≤ g x}` ([#10653](https://github.com/leanprover-community/mathlib/pull/10653))
and golf the dual one: `closure_lt_subset_le`
#### Estimated changes
Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* lt_subset_interior_le



## [2021-12-07 18:28:16](https://github.com/leanprover-community/mathlib/commit/a803e21)
feat(measure_theory/lattice): define typeclasses for measurability of lattice operations, define a lattice on ae_eq_fun ([#10591](https://github.com/leanprover-community/mathlib/pull/10591))
As was previously done for measurability of arithmetic operations, I define typeclasses for the measurability of sup and inf in a lattice. In the borel_space file, instances of these are provided when the lattice operations are continuous.
Finally I've put a lattice structure on `ae_eq_fun`.
#### Estimated changes
Modified src/analysis/normed_space/lattice_ordered_group.lean

Modified src/measure_theory/constructions/borel_space.lean

Modified src/measure_theory/function/ae_eq_fun.lean
- \+ *lemma* coe_fn_sup
- \+ *lemma* coe_fn_inf

Created src/measure_theory/lattice.lean
- \+ *lemma* measurable.const_sup
- \+ *lemma* ae_measurable.const_sup
- \+ *lemma* measurable.sup_const
- \+ *lemma* ae_measurable.sup_const
- \+ *lemma* measurable.sup'
- \+ *lemma* measurable.sup
- \+ *lemma* ae_measurable.sup'
- \+ *lemma* ae_measurable.sup
- \+ *lemma* measurable.const_inf
- \+ *lemma* ae_measurable.const_inf
- \+ *lemma* measurable.inf_const
- \+ *lemma* ae_measurable.inf_const
- \+ *lemma* measurable.inf'
- \+ *lemma* measurable.inf
- \+ *lemma* ae_measurable.inf'
- \+ *lemma* ae_measurable.inf

Modified src/topology/order/lattice.lean



## [2021-12-07 15:39:30](https://github.com/leanprover-community/mathlib/commit/ae7a88d)
feat(field_theory/finite/basic): generalize lemma from field to integral domain ([#10655](https://github.com/leanprover-community/mathlib/pull/10655))
#### Estimated changes
Modified src/field_theory/finite/basic.lean
- \+/\- *lemma* prod_univ_units_id_eq_neg_one
- \+/\- *lemma* prod_univ_units_id_eq_neg_one



## [2021-12-07 15:39:28](https://github.com/leanprover-community/mathlib/commit/9a2c299)
feat(data/pi): add `pi.single_inj` ([#10644](https://github.com/leanprover-community/mathlib/pull/10644))
#### Estimated changes
Modified src/data/pi.lean
- \+ *lemma* single_inj



## [2021-12-07 15:39:27](https://github.com/leanprover-community/mathlib/commit/03dd404)
feat(algebra/category): (co)limits in CommRing ([#10593](https://github.com/leanprover-community/mathlib/pull/10593))
#### Estimated changes
Created src/algebra/category/CommRing/constructions.lean
- \+ *lemma* pushout_cocone_inl
- \+ *lemma* pushout_cocone_inr
- \+ *lemma* pushout_cocone_X
- \+ *def* pushout_cocone
- \+ *def* pushout_cocone_is_colimit
- \+ *def* punit_is_terminal
- \+ *def* Z_is_initial
- \+ *def* prod_fan
- \+ *def* prod_fan_is_limit
- \+ *def* equalizer_fork
- \+ *def* equalizer_fork_is_limit

Deleted src/algebra/category/CommRing/pushout.lean
- \- *lemma* pushout_cocone_inl
- \- *lemma* pushout_cocone_inr
- \- *lemma* pushout_cocone_X
- \- *def* pushout_cocone
- \- *def* pushout_cocone_is_colimit

Modified src/ring_theory/ideal/local_ring.lean



## [2021-12-07 14:45:55](https://github.com/leanprover-community/mathlib/commit/173a21a)
feat(topology/sheaves): `F(U ⨿ V) = F(U) × F(V)` ([#10597](https://github.com/leanprover-community/mathlib/pull/10597))
#### Estimated changes
Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean
- \+ *lemma* inter_union_pullback_cone_X
- \+ *lemma* inter_union_pullback_cone_fst
- \+ *lemma* inter_union_pullback_cone_snd
- \+ *lemma* inter_union_pullback_cone_lift_left
- \+ *lemma* inter_union_pullback_cone_lift_right
- \+ *def* inter_union_pullback_cone
- \+ *def* inter_union_pullback_cone_lift
- \+ *def* is_limit_pullback_cone
- \+ *def* is_product_of_disjoint



## [2021-12-07 06:39:50](https://github.com/leanprover-community/mathlib/commit/ba1cbfa)
feat(topology/algebra/ordered/basic): Add alternative formulations of four lemmas. ([#10630](https://github.com/leanprover-community/mathlib/pull/10630))
Add alternative formulations of lemmas about interiors and frontiers of `Iic` and `Ici`. The existing formulations make typeclass assumptions `[no_top_order]` or `[no_bot_order]`. These alternative formulations assume instead that the endpoint of the interval is not top or bottom; and as such they can be applied in, e.g., `nnreal` and `ennreal`.
Also, some lemmas now assume `(Ioi a).nonempty` or `(Iio a).nonempty` instead of `{b} (h : a < b)` or `{b} (h : b < a)`, respectively.
#### Estimated changes
Modified src/topology/algebra/ordered/basic.lean
- \+/\- *lemma* closure_Ioi'
- \+/\- *lemma* closure_Iio'
- \+ *lemma* interior_Ici'
- \+/\- *lemma* interior_Ici
- \+ *lemma* interior_Iic'
- \+/\- *lemma* interior_Iic
- \+ *lemma* frontier_Ici'
- \+/\- *lemma* frontier_Ici
- \+ *lemma* frontier_Iic'
- \+/\- *lemma* frontier_Iic
- \+ *lemma* frontier_Ioi'
- \+/\- *lemma* frontier_Ioi
- \+ *lemma* frontier_Iio'
- \+/\- *lemma* frontier_Iio
- \+/\- *lemma* nhds_within_Ioi_ne_bot'
- \+/\- *lemma* nhds_within_Ioi_self_ne_bot'
- \+/\- *lemma* nhds_within_Iio_ne_bot'
- \+/\- *lemma* nhds_within_Iio_self_ne_bot'
- \+/\- *lemma* closure_Ioi'
- \+/\- *lemma* closure_Iio'
- \+/\- *lemma* interior_Ici
- \+/\- *lemma* interior_Iic
- \+/\- *lemma* frontier_Ici
- \+/\- *lemma* frontier_Iic
- \+/\- *lemma* frontier_Ioi
- \+/\- *lemma* frontier_Iio
- \+/\- *lemma* nhds_within_Ioi_ne_bot'
- \+/\- *lemma* nhds_within_Ioi_self_ne_bot'
- \+/\- *lemma* nhds_within_Iio_ne_bot'
- \+/\- *lemma* nhds_within_Iio_self_ne_bot'

Modified src/topology/algebra/ordered/intermediate_value.lean

Modified src/topology/instances/ennreal.lean



## [2021-12-07 00:26:04](https://github.com/leanprover-community/mathlib/commit/9031989)
chore(*): fix last line length and notation style linter errors ([#10642](https://github.com/leanprover-community/mathlib/pull/10642))
These are the last non-module doc style linter errors (from https://github.com/leanprover-community/mathlib/blob/master/scripts/style-exceptions.txt).
#### Estimated changes
Modified src/data/pfunctor/multivariate/M.lean

Modified src/data/pfunctor/multivariate/W.lean

Modified src/data/qpf/multivariate/constructions/cofix.lean

Modified src/data/qpf/multivariate/constructions/fix.lean

Modified src/tactic/induction.lean

Modified src/tactic/reserved_notation.lean



## [2021-12-07 00:26:03](https://github.com/leanprover-community/mathlib/commit/cd857f7)
feat(data/int/basic): four lemmas about integer divisibility ([#10602](https://github.com/leanprover-community/mathlib/pull/10602))
Theorem 1.1, parts (c), (i), (j), and (k) of Apostol (1976) Introduction to Analytic Number Theory
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* has_dvd.dvd.linear_comb

Modified src/data/int/basic.lean
- \+ *lemma* nat_abs_le_of_dvd_ne_zero
- \+ *lemma* nat_abs_eq_of_dvd_dvd
- \+ *lemma* div_dvd_of_ne_zero_dvd



## [2021-12-06 22:38:00](https://github.com/leanprover-community/mathlib/commit/eec4b70)
feat(algebra/geom_sum): criteria for 0 < geom_sum ([#10567](https://github.com/leanprover-community/mathlib/pull/10567))
#### Estimated changes
Modified src/algebra/geom_sum.lean
- \+ *lemma* geom_sum_succ
- \+ *lemma* geom_sum_succ'
- \+ *lemma* geom_sum_two
- \+ *lemma* zero_geom_sum
- \+/\- *lemma* one_geom_sum
- \+/\- *lemma* op_geom_sum
- \+/\- *lemma* op_geom_sum₂
- \+ *lemma* neg_one_geom_sum
- \+ *lemma* geom_sum_pos
- \+ *lemma* geom_sum_pos_and_lt_one
- \+ *lemma* geom_sum_alternating_of_lt_neg_one
- \+ *lemma* geom_sum_pos_of_odd
- \+ *lemma* geom_sum_pos_iff
- \+ *lemma* geom_sum_eq_zero_iff_neg_one
- \+ *lemma* geom_sum_neg_iff
- \+/\- *lemma* one_geom_sum
- \+/\- *lemma* op_geom_sum
- \+/\- *lemma* op_geom_sum₂
- \+/\- *theorem* geom_sum_def
- \+/\- *theorem* geom_sum_zero
- \+/\- *theorem* geom_sum_one
- \+/\- *theorem* geom_sum₂_def
- \+/\- *theorem* geom_sum₂_zero
- \+/\- *theorem* geom_sum₂_one
- \+/\- *theorem* geom_sum₂_with_one
- \+/\- *theorem* geom_sum_def
- \+/\- *theorem* geom_sum_zero
- \+/\- *theorem* geom_sum_one
- \+/\- *theorem* geom_sum₂_def
- \+/\- *theorem* geom_sum₂_zero
- \+/\- *theorem* geom_sum₂_one
- \+/\- *theorem* geom_sum₂_with_one
- \+/\- *def* geom_sum
- \+/\- *def* geom_sum₂
- \+/\- *def* geom_sum
- \+/\- *def* geom_sum₂

Modified src/logic/basic.lean
- \+ *lemma* decidable.and_or_imp
- \+ *theorem* and_or_imp



## [2021-12-06 21:05:46](https://github.com/leanprover-community/mathlib/commit/a8c086f)
feat(linear_algebra/determinant): linear_equiv.det_mul_det_symm ([#10635](https://github.com/leanprover-community/mathlib/pull/10635))
Add lemmas that the determinants of a `linear_equiv` and its
inverse multiply to 1.  There are a few other lemmas involving
determinants and `linear_equiv`, but apparently not this one.
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* linear_equiv.det_mul_det_symm
- \+ *lemma* linear_equiv.det_symm_mul_det



## [2021-12-06 19:23:02](https://github.com/leanprover-community/mathlib/commit/1d5202a)
feat(data/multiset): add some lemmas about filter (eq x) ([#10626](https://github.com/leanprover-community/mathlib/pull/10626))
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* filter_eq'
- \+ *lemma* filter_eq
- \+ *lemma* pow_count
- \+ *theorem* count_filter



## [2021-12-06 14:45:34](https://github.com/leanprover-community/mathlib/commit/8124314)
feat(linear_algebra/multilinear/basic,linear_algebra/alternating): comp_linear_map lemmas ([#10631](https://github.com/leanprover-community/mathlib/pull/10631))
Add more lemmas about composing multilinear and alternating maps with
linear maps in each argument.
Where I wanted a lemma for either of multilinear or alternating maps,
I added it for both.  There are however some lemmas for
`alternating_map.comp_linear_map` that don't have equivalents at
present for `multilinear_map.comp_linear_map` (I added one such
equivalent `multilinear_map.zero_comp_linear_map` because I needed it
for another lemma, but didn't try adding such equivalents of existing
lemmas where I didn't need them).
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *lemma* comp_linear_map_assoc
- \+ *lemma* comp_linear_map_id
- \+ *lemma* comp_linear_map_injective
- \+ *lemma* comp_linear_map_inj
- \+ *lemma* comp_linear_equiv_eq_zero_iff

Modified src/linear_algebra/multilinear/basic.lean
- \+ *lemma* comp_linear_map_assoc
- \+ *lemma* zero_comp_linear_map
- \+ *lemma* comp_linear_map_id
- \+ *lemma* comp_linear_map_injective
- \+ *lemma* comp_linear_map_inj
- \+ *lemma* comp_linear_equiv_eq_zero_iff



## [2021-12-06 13:25:54](https://github.com/leanprover-community/mathlib/commit/f50984d)
chore(linear_algebra/affine_space/basis): remove unhelpful coercion ([#10637](https://github.com/leanprover-community/mathlib/pull/10637))
It is more useful to have a statement of equality of linear maps than
of raw functions.
#### Estimated changes
Modified src/linear_algebra/affine_space/basis.lean
- \+ *lemma* linear_eq_sum_coords
- \- *lemma* coe_linear



## [2021-12-06 06:48:34](https://github.com/leanprover-community/mathlib/commit/e6ad0f2)
chore(analysis/inner_product/projections): generalize some lemmas ([#10608](https://github.com/leanprover-community/mathlib/pull/10608))
* generalize a few lemmas from `[finite_dimensional 𝕜 ?x]` to `[complete_space ?x]`;
* drop unneeded TC assumption in `isometry.tendsto_nhds_iff`;
* image of a complete set/submodule under an isometry is a complete set/submodule.
#### Estimated changes
Modified src/analysis/inner_product_space/projection.lean
- \+ *lemma* linear_isometry.map_orthogonal_projection

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* is_complete_image_iff
- \+ *lemma* is_complete_map_iff

Modified src/topology/metric_space/isometry.lean
- \+/\- *lemma* isometry.tendsto_nhds_iff
- \+/\- *lemma* isometry.tendsto_nhds_iff



## [2021-12-06 05:02:03](https://github.com/leanprover-community/mathlib/commit/e726945)
refactor(order/atoms): is_simple_order from is_simple_lattice ([#10537](https://github.com/leanprover-community/mathlib/pull/10537))
Rename `is_simple_lattice` to `is_simple_order`, still stating that every element is either `bot` or `top` are, and that it is nontrivial.
To state `is_simple_order`, `has_le` and `bounded_order` are required to be defined. This allows for an order where `⊤ ≤ ⊥` (the always true order). 
Many proofs/statements about `is_simple_order`s have been generalized to require solely `partial_order` and not `lattice`. The statements themselves have not been changed. 
The `is_simple_order.distrib_lattice` instance has been downgraded into a `def` to prevent loops.
Helper defs have been added like `is_simple_order.preorder` (which is true given the `has_le` `bounded_order` axioms) `is_simple_order.linear_order`, and `is_simple_order.lattice` (which are true when `partial_order`, implying `⊥ < ⊤`.).
#### Estimated changes
Modified src/group_theory/specific_groups/cyclic.lean

Modified src/group_theory/subgroup/basic.lean

Modified src/order/atoms.lean
- \+ *lemma* is_simple_order.bot_ne_top
- \+ *lemma* is_simple_order_iff
- \+ *lemma* is_simple_order
- \- *lemma* is_simple_lattice_iff
- \- *lemma* is_simple_lattice
- \+ *theorem* is_simple_order_iff_is_simple_order_order_dual
- \+ *theorem* is_simple_order_iff_is_atom_top
- \+ *theorem* is_simple_order_iff_is_coatom_bot
- \+ *theorem* is_simple_order_Iic_iff_is_atom
- \+ *theorem* is_simple_order_Ici_iff_is_coatom
- \- *theorem* is_simple_lattice_iff_is_simple_lattice_order_dual
- \- *theorem* is_simple_lattice_iff_is_atom_top
- \- *theorem* is_simple_lattice_iff_is_coatom_bot
- \- *theorem* is_simple_lattice_Iic_iff_is_atom
- \- *theorem* is_simple_lattice_Ici_iff_is_coatom
- \+ *def* equiv_bool
- \+/\- *def* order_iso_bool
- \+/\- *def* order_iso_bool

Modified src/order/bounded_order.lean

Modified src/ring_theory/simple_module.lean



## [2021-12-05 19:54:45](https://github.com/leanprover-community/mathlib/commit/e7bd49f)
chore(scripts/mk_all.sh): allow 'mk_all.sh ../test' ([#10628](https://github.com/leanprover-community/mathlib/pull/10628))
Helpful for mathport CI, cf https://github.com/leanprover-community/mathport/pull/64
#### Estimated changes
Modified scripts/mk_all.sh



## [2021-12-05 18:05:59](https://github.com/leanprover-community/mathlib/commit/2b2d116)
chore(combinatorics/simple_graph/coloring): remove extra asterisk ([#10618](https://github.com/leanprover-community/mathlib/pull/10618))
#### Estimated changes
Modified src/combinatorics/simple_graph/partition.lean



## [2021-12-05 16:33:11](https://github.com/leanprover-community/mathlib/commit/8c1f2b5)
feat(ring_theory/graded_algebra): projection map of graded algebra ([#10116](https://github.com/leanprover-community/mathlib/pull/10116))
This pr defines and proves some property about `graded_algebra.proj : A →ₗ[R] A`
#### Estimated changes
Modified src/algebra/direct_sum/basic.lean
- \+ *lemma* coe_of_add_submonoid_apply
- \+ *lemma* coe_of_add_subgroup_apply

Modified src/algebra/direct_sum/internal.lean
- \+ *lemma* direct_sum.coe_mul_apply_add_submonoid
- \+ *lemma* direct_sum.coe_mul_apply_add_subgroup
- \+ *lemma* direct_sum.coe_mul_apply_submodule

Modified src/algebra/direct_sum/module.lean
- \+ *lemma* coe_of_submodule_apply

Modified src/algebra/direct_sum/ring.lean
- \+ *lemma* mul_eq_sum_support_ghas_mul

Modified src/group_theory/subgroup/basic.lean
- \+ *theorem* coe_list_prod
- \+ *theorem* coe_multiset_prod
- \+ *theorem* coe_finset_prod

Modified src/ring_theory/graded_algebra/basic.lean
- \+ *lemma* graded_algebra.is_internal
- \+ *lemma* graded_algebra.proj_apply
- \+ *lemma* graded_algebra.proj_recompose
- \+ *lemma* graded_algebra.decompose_coe
- \+ *lemma* graded_algebra.decompose_of_mem
- \+ *lemma* graded_algebra.decompose_of_mem_same
- \+ *lemma* graded_algebra.decompose_of_mem_ne
- \+ *lemma* graded_algebra.mem_support_iff
- \+ *lemma* graded_algebra.sum_support_decompose
- \- *lemma* graded_ring.is_internal
- \+ *def* graded_algebra.proj
- \+ *def* graded_algebra.support



## [2021-12-05 11:46:50](https://github.com/leanprover-community/mathlib/commit/428b9e5)
feat(topology/continuous_function/bounded): continuous bounded real-valued functions form a normed vector lattice ([#10322](https://github.com/leanprover-community/mathlib/pull/10322))
feat(topology/continuous_function/bounded): continuous bounded real-valued functions form a normed vector lattice
#### Estimated changes
Modified src/analysis/normed_space/lattice_ordered_group.lean
- \+ *lemma* norm_sup_sub_sup_le_add_norm
- \- *lemma* norm_two_inf_sub_two_inf_le
- \- *lemma* norm_two_sup_sub_two_sup_le

Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* coe_fn_sup
- \+ *lemma* coe_fn_abs



## [2021-12-05 03:46:59](https://github.com/leanprover-community/mathlib/commit/37f343c)
chore(data/stream): merge `basic` into `init` ([#10617](https://github.com/leanprover-community/mathlib/pull/10617))
#### Estimated changes
Modified src/combinatorics/hindman.lean

Modified src/data/seq/seq.lean

Deleted src/data/stream/basic.lean
- \- *lemma* head_drop

Modified src/data/stream/init.lean
- \+ *lemma* head_drop

Modified test/ext.lean



## [2021-12-04 15:25:01](https://github.com/leanprover-community/mathlib/commit/6eeb54e)
fix(topology/algebra/uniform_field): remove unnecessary topological_r… ([#10614](https://github.com/leanprover-community/mathlib/pull/10614))
…ing variable
Right now the last three definitions in `topology.algebra.uniform_field` (after line 115) have `[topological_division_ring K]` and `[topological_ring K]`. For example
```
mul_hat_inv_cancel :
  ∀ {K : Type u_1} [_inst_1 : field K] [_inst_2 : uniform_space K] [_inst_3 : topological_division_ring K]
  [_inst_4 : completable_top_field K] [_inst_5 : uniform_add_group K] [_inst_6 : topological_ring K]
  {x : uniform_space.completion K}, x ≠ 0 → x * hat_inv x = 1
```
Whilst it is not obvious from the notation, both of these are `Prop`s so there is no danger of diamonds. The full logic is: `field` and `uniform_space` are data, and the rest are Props (so should be called things like `is_topological_ring` etc IMO). `topological_division_ring` is the assertion of continuity of `add`, `neg`, `mul` and `inv` (away from 0), `completable_top_field` is another assertion about how inversion plays well with the topology (and which is not implied by `topological_division_ring`), `uniform_add_group` is the assertion about `add` and `neg` playing well with the uniform structure, and then `topological_ring` is a prop which is implied by `topological_division_ring`. I am not sure I see the benefits of carrying around the extra `topological_ring` for these three definitions so I've removed it to see if mathlib still compiles. Edit: it does.
#### Estimated changes
Modified src/topology/algebra/uniform_field.lean



## [2021-12-04 15:25:00](https://github.com/leanprover-community/mathlib/commit/c940e47)
chore(topology/continuous_function): remove forget_boundedness ([#10612](https://github.com/leanprover-community/mathlib/pull/10612))
It is the same as `to_continuous_map`.
#### Estimated changes
Modified src/measure_theory/function/lp_space.lean
- \+ *lemma* to_Lp_comp_to_continuous_map
- \- *lemma* to_Lp_comp_forget_boundedness

Modified src/topology/continuous_function/bounded.lean
- \- *lemma* forget_boundedness_coe
- \+ *def* to_continuous_map_add_hom
- \+ *def* to_continuous_map_linear_map
- \- *def* forget_boundedness
- \- *def* forget_boundedness_add_hom
- \- *def* forget_boundedness_linear_map

Modified src/topology/continuous_function/compact.lean
- \+ *lemma* _root_.bounded_continuous_function.dist_to_continuous_map
- \+ *lemma* _root_.bounded_continuous_function.norm_to_continuous_map_eq
- \- *lemma* _root_.bounded_continuous_function.dist_forget_boundedness
- \- *lemma* _root_.bounded_continuous_function.norm_forget_boundedness_eq



## [2021-12-04 13:36:16](https://github.com/leanprover-community/mathlib/commit/b3b7fe6)
chore(algebra/module): generalize `char_zero.of_algebra` to `char_zero.of_module` ([#10609](https://github.com/leanprover-community/mathlib/pull/10609))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *lemma* of_algebra

Modified src/algebra/module/basic.lean
- \+ *lemma* eq_zero_of_two_nsmul_eq_zero
- \+ *lemma* char_zero.of_module
- \- *lemma* eq_zero_of_smul_two_eq_zero

Modified src/number_theory/number_field.lean



## [2021-12-04 08:58:37](https://github.com/leanprover-community/mathlib/commit/5d0e65a)
chore(order/galois_connection): upgrade `is_glb_l` to `is_least_l` ([#10606](https://github.com/leanprover-community/mathlib/pull/10606))
* upgrade `galois_connection.is_glb_l` to `galois_connection.is_least_l`;
* upgrade `galois_connection.is_lub_l` to `galois_connection.is_greatest_l`.
#### Estimated changes
Modified src/order/galois_connection.lean
- \+ *lemma* is_least_l
- \+ *lemma* is_greatest_u
- \+/\- *lemma* is_glb_l
- \+/\- *lemma* is_lub_u
- \+/\- *lemma* is_glb_l
- \+/\- *lemma* is_lub_u



## [2021-12-04 07:14:54](https://github.com/leanprover-community/mathlib/commit/3479b7f)
chore(order/complete_lattice): golf a proof ([#10607](https://github.com/leanprover-community/mathlib/pull/10607))
Also reformulate `le_Sup_iff` in terms of `upper_bounds`.
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+/\- *lemma* le_Sup_iff
- \+/\- *lemma* le_Sup_iff



## [2021-12-04 05:05:06](https://github.com/leanprover-community/mathlib/commit/9c4e41a)
feat(number_theory/modular): the action of `SL(2, ℤ)` on the upper half plane ([#8611](https://github.com/leanprover-community/mathlib/pull/8611))
We define the action of `SL(2,ℤ)` on `ℍ` (via restriction of the `SL(2,ℝ)` action in `analysis.complex.upper_half_plane`). We then define the standard fundamental domain `𝒟` for this action and show that any point in `ℍ` can be moved inside `𝒟`.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* coe_fn_general_linear_equiv

Modified src/linear_algebra/general_linear_group.lean
- \+ *lemma* coe_to_linear
- \+ *lemma* to_linear_apply
- \+ *def* mk_of_det_ne_zero
- \+ *def* to_linear
- \+ *def* plane_conformal_matrix

Modified src/linear_algebra/special_linear_group.lean
- \+ *lemma* coe_mk
- \+ *lemma* coe_matrix_coe
- \+ *lemma* coe_int_neg
- \+ *def* map

Modified src/measure_theory/group/basic.lean

Created src/number_theory/modular.lean
- \+ *lemma* coe_smul
- \+ *lemma* re_smul
- \+ *lemma* smul_coe
- \+ *lemma* neg_smul
- \+ *lemma* im_smul
- \+ *lemma* im_smul_eq_div_norm_sq
- \+ *lemma* denom_apply
- \+ *lemma* bottom_row_coprime
- \+ *lemma* bottom_row_surj
- \+ *lemma* tendsto_norm_sq_coprime_pair
- \+ *lemma* lc_row0_apply
- \+ *lemma* lc_row0_apply'
- \+ *lemma* smul_eq_lc_row0_add
- \+ *lemma* tendsto_abs_re_smul
- \+ *lemma* exists_max_im
- \+ *lemma* exists_row_one_eq_and_min_re
- \+ *lemma* im_lt_im_S_smul
- \+ *lemma* exists_smul_mem_fundamental_domain
- \+ *theorem* tendsto_lc_row0
- \+ *def* lc_row0
- \+ *def* lc_row0_extend
- \+ *def* T
- \+ *def* T'
- \+ *def* S
- \+ *def* fundamental_domain

Modified src/topology/algebra/group.lean
- \+ *lemma* homeomorph.coe_mul_right
- \+ *lemma* homeomorph.mul_right_symm

Modified src/topology/homeomorph.lean
- \+ *lemma* trans_apply



## [2021-12-04 03:25:04](https://github.com/leanprover-community/mathlib/commit/2da25ed)
feat(combinatorics/simple_graph): Graph coloring and partitions ([#10287](https://github.com/leanprover-community/mathlib/pull/10287))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *def* complete_bipartite_graph
- \+ *def* map_spanning_subgraphs
- \+ *def* complete_graph.of_embedding

Created src/combinatorics/simple_graph/coloring.lean
- \+ *lemma* coloring.valid
- \+ *lemma* coloring.mem_color_class
- \+ *lemma* coloring.color_classes_is_partition
- \+ *lemma* coloring.mem_color_classes
- \+ *lemma* coloring.color_classes_finite_of_fintype
- \+ *lemma* coloring.card_color_classes_le
- \+ *lemma* coloring.not_adj_of_mem_color_class
- \+ *lemma* coloring.color_classes_independent
- \+ *lemma* colorable_of_is_empty
- \+ *lemma* is_empty_of_colorable_zero
- \+ *lemma* colorable.of_le
- \+ *lemma* coloring.to_colorable
- \+ *lemma* colorable_of_fintype
- \+ *lemma* colorable_iff_exists_bdd_nat_coloring
- \+ *lemma* colorable_set_nonempty_of_colorable
- \+ *lemma* chromatic_number_bdd_below
- \+ *lemma* chromatic_number_le_of_colorable
- \+ *lemma* chromatic_number_le_card
- \+ *lemma* colorable_chromatic_number
- \+ *lemma* colorable_chromatic_number_of_fintype
- \+ *lemma* chromatic_number_le_one_of_subsingleton
- \+ *lemma* chromatic_number_eq_zero_of_isempty
- \+ *lemma* is_empty_of_chromatic_number_eq_zero
- \+ *lemma* zero_lt_chromatic_number
- \+ *lemma* colorable_of_le_colorable
- \+ *lemma* chromatic_number_le_of_forall_imp
- \+ *lemma* chromatic_number_le_of_le_colorable
- \+ *lemma* chromatic_number_eq_card_of_forall_surj
- \+ *lemma* chromatic_number_bot
- \+ *lemma* chromatic_number_complete_graph
- \+ *lemma* complete_bipartite_graph.chromatic_number
- \+ *def* coloring.mk
- \+ *def* coloring.color_class
- \+ *def* coloring.color_classes
- \+ *def* colorable
- \+ *def* coloring_of_is_empty
- \+ *def* self_coloring
- \+ *def* recolor_of_embedding
- \+ *def* recolor_of_equiv
- \+ *def* complete_bipartite_graph.bicoloring

Created src/combinatorics/simple_graph/partition.lean
- \+ *lemma* part_of_vertex_mem
- \+ *lemma* mem_part_of_vertex
- \+ *lemma* part_of_vertex_ne_of_adj
- \+ *lemma* to_colorable
- \+ *lemma* partitionable_iff_colorable
- \+ *def* partition.parts_card_le
- \+ *def* partitionable
- \+ *def* part_of_vertex
- \+ *def* to_coloring
- \+ *def* to_coloring'
- \+ *def* coloring.to_partition

Modified src/data/fintype/basic.lean
- \+ *lemma* card_range_le

Modified src/data/setoid/partition.lean
- \+ *lemma* classes_ker_subset_fiber_set
- \+ *lemma* nonempty_fintype_classes_ker
- \+ *lemma* card_classes_ker_le



## [2021-12-04 01:52:50](https://github.com/leanprover-community/mathlib/commit/ef3540a)
chore(measure_theory/function/conditional_expectation): golf condexp_L1 proofs using set_to_fun lemmas ([#10592](https://github.com/leanprover-community/mathlib/pull/10592))
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean
- \+/\- *lemma* condexp_L1_neg
- \+/\- *lemma* condexp_L1_smul
- \+/\- *lemma* condexp_L1_neg
- \+/\- *lemma* condexp_L1_smul



## [2021-12-04 01:52:49](https://github.com/leanprover-community/mathlib/commit/23dfe70)
feat(*): `A ⧸ B` notation for quotients in algebra ([#10501](https://github.com/leanprover-community/mathlib/pull/10501))
We introduce a class `has_quotient` that provides `⧸` (U+29F8 BIG SOLIDUS) notation for quotients, e.g. if `H : subgroup G` then `quotient_group.quotient H` is now written as `G ⧸ H`. Thanks to @jcommelin for suggesting the initial design.
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Notation.20for.20group.28module.2Cideal.29.20quotients
#### Estimated changes
Modified docs/overview.yaml

Modified docs/undergrad.yaml

Modified src/algebra/category/Group/colimits.lean

Modified src/algebra/category/Module/abelian.lean

Modified src/algebra/category/Module/kernels.lean

Modified src/algebra/char_p/quotient.lean

Modified src/algebra/direct_limit.lean

Modified src/algebra/group_action_hom.lean
- \+/\- *def* to_quotient
- \+/\- *def* to_quotient

Modified src/algebra/lie/cartan_matrix.lean
- \+/\- *def* matrix.to_lie_algebra
- \+/\- *def* matrix.to_lie_algebra

Modified src/algebra/lie/quotient.lean
- \+/\- *lemma* lie_module_hom_ext
- \+/\- *lemma* lie_module_hom_ext
- \+/\- *def* action_as_endo_map
- \+/\- *def* action_as_endo_map_bracket
- \+/\- *def* mk'
- \+/\- *def* action_as_endo_map
- \+/\- *def* action_as_endo_map_bracket
- \+/\- *def* mk'

Modified src/algebra/polynomial/group_ring_action.lean

Created src/algebra/quotient.lean
- \+ *def* has_quotient.quotient

Modified src/algebra/ring_quot.lean

Modified src/analysis/normed/group/SemiNormedGroup/kernels.lean

Modified src/analysis/normed/group/quotient.lean
- \+/\- *lemma* quotient_norm_neg
- \+/\- *lemma* quotient_norm_sub_rev
- \+/\- *lemma* quotient_norm_nonneg
- \+/\- *lemma* norm_mk_lt
- \+/\- *lemma* quotient_norm_add_le
- \+/\- *lemma* norm_mk_zero
- \+/\- *lemma* quotient_norm_neg
- \+/\- *lemma* quotient_norm_sub_rev
- \+/\- *lemma* quotient_norm_nonneg
- \+/\- *lemma* norm_mk_lt
- \+/\- *lemma* quotient_norm_add_le
- \+/\- *lemma* norm_mk_zero
- \+/\- *def* normed_mk
- \+/\- *def* normed_mk

Modified src/analysis/normed_space/complemented.lean

Modified src/analysis/special_functions/trigonometric/angle.lean

Modified src/category_theory/action.lean

Modified src/data/zmod/quotient.lean

Modified src/field_theory/is_alg_closed/algebraic_closure.lean

Modified src/group_theory/abelianization.lean

Modified src/group_theory/coset.lean
- \+/\- *lemma* induction_on
- \+/\- *lemma* induction_on'
- \+/\- *lemma* forall_coe
- \+/\- *lemma* eq'
- \+/\- *lemma* out_eq'
- \+/\- *lemma* mk_out'_eq_mul
- \+/\- *lemma* mk_mul_of_mem
- \+/\- *lemma* induction_on
- \+/\- *lemma* induction_on'
- \+/\- *lemma* forall_coe
- \+/\- *lemma* eq'
- \+/\- *lemma* out_eq'
- \+/\- *lemma* mk_out'_eq_mul
- \+/\- *lemma* mk_mul_of_mem
- \- *def* quotient

Modified src/group_theory/group_action/basic.lean
- \+/\- *def* of_quotient_stabilizer
- \+/\- *def* of_quotient_stabilizer

Modified src/group_theory/index.lean
- \+/\- *lemma* index_eq_card
- \+/\- *lemma* index_ne_zero_of_fintype
- \+/\- *lemma* one_lt_index_of_ne_top
- \+/\- *lemma* index_eq_card
- \+/\- *lemma* index_ne_zero_of_fintype
- \+/\- *lemma* one_lt_index_of_ne_top

Modified src/group_theory/nilpotent.lean

Modified src/group_theory/order_of_element.lean

Modified src/group_theory/p_group.lean
- \+/\- *lemma* index
- \+/\- *lemma* index

Modified src/group_theory/presented_group.lean

Modified src/group_theory/quotient_group.lean
- \+/\- *lemma* coe_mk'
- \+/\- *lemma* monoid_hom_ext
- \+/\- *lemma* eq_one_iff
- \+/\- *lemma* quotient_quotient_equiv_quotient_aux_coe
- \+/\- *lemma* coe_mk'
- \+/\- *lemma* monoid_hom_ext
- \+/\- *lemma* eq_one_iff
- \+/\- *lemma* quotient_quotient_equiv_quotient_aux_coe
- \+/\- *def* mk'
- \+/\- *def* ker_lift
- \+/\- *def* range_ker_lift
- \+/\- *def* quotient_bot
- \+/\- *def* mk'
- \+/\- *def* ker_lift
- \+/\- *def* range_ker_lift
- \+/\- *def* quotient_bot

Modified src/group_theory/schur_zassenhaus.lean

Modified src/group_theory/solvable.lean

Modified src/group_theory/sylow.lean

Modified src/linear_algebra/adic_completion.lean
- \+/\- *def* adic_completion
- \+/\- *def* eval
- \+/\- *def* adic_completion
- \+/\- *def* eval

Modified src/linear_algebra/alternating.lean

Modified src/linear_algebra/basis.lean

Modified src/linear_algebra/dimension.lean

Modified src/linear_algebra/dual.lean

Modified src/linear_algebra/finite_dimensional.lean

Modified src/linear_algebra/invariant_basis_number.lean

Modified src/linear_algebra/isomorphisms.lean
- \+/\- *lemma* quotient_quotient_equiv_quotient_aux_mk
- \+/\- *lemma* quotient_quotient_equiv_quotient_aux_mk

Modified src/linear_algebra/projection.lean
- \+/\- *lemma* mk_quotient_equiv_of_is_compl_apply
- \+/\- *lemma* mk_quotient_equiv_of_is_compl_apply
- \+/\- *def* quotient_equiv_of_is_compl
- \+/\- *def* quotient_equiv_of_is_compl

Modified src/linear_algebra/quotient.lean
- \+/\- *lemma* nontrivial_of_lt_top
- \+/\- *lemma* quot_hom_ext
- \+/\- *lemma* linear_map_qext
- \+/\- *lemma* le_comap_mkq
- \+/\- *lemma* comap_mkq_embedding_eq
- \+/\- *lemma* nontrivial_of_lt_top
- \+/\- *lemma* quot_hom_ext
- \+/\- *lemma* linear_map_qext
- \+/\- *lemma* le_comap_mkq
- \+/\- *lemma* comap_mkq_embedding_eq
- \+/\- *theorem* mk'_eq_mk
- \+/\- *theorem* quot_mk_eq_mk
- \+/\- *theorem* mk_zero
- \+/\- *theorem* mk_eq_zero
- \+/\- *theorem* mk_add
- \+/\- *theorem* mk_neg
- \+/\- *theorem* mk_sub
- \+/\- *theorem* mk_smul
- \+/\- *theorem* map_liftq
- \+/\- *theorem* mk'_eq_mk
- \+/\- *theorem* quot_mk_eq_mk
- \+/\- *theorem* mk_zero
- \+/\- *theorem* mk_eq_zero
- \+/\- *theorem* mk_add
- \+/\- *theorem* mk_neg
- \+/\- *theorem* mk_sub
- \+/\- *theorem* mk_smul
- \+/\- *theorem* map_liftq
- \+/\- *def* mk
- \+/\- *def* mkq
- \+/\- *def* liftq
- \+/\- *def* quot_equiv_of_eq_bot
- \+/\- *def* quot_equiv_of_eq
- \+/\- *def* mapq_linear
- \- *def* quotient
- \+/\- *def* mk
- \+/\- *def* mkq
- \+/\- *def* liftq
- \+/\- *def* quot_equiv_of_eq_bot
- \+/\- *def* quot_equiv_of_eq
- \+/\- *def* mapq_linear

Modified src/linear_algebra/smodeq.lean

Modified src/measure_theory/measurable_space.lean

Modified src/number_theory/basic.lean

Modified src/ring_theory/adjoin_root.lean

Modified src/ring_theory/artinian.lean

Modified src/ring_theory/class_group.lean
- \+/\- *def* class_group
- \+/\- *def* class_group

Modified src/ring_theory/eisenstein_criterion.lean

Modified src/ring_theory/finiteness.lean

Modified src/ring_theory/ideal/local_ring.lean
- \+/\- *def* residue_field
- \+/\- *def* residue_field

Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* quotient.mkₐ_ker
- \+/\- *lemma* ker_lift.map_smul
- \+/\- *lemma* quotient.mkₐ_ker
- \+/\- *lemma* ker_lift.map_smul
- \+/\- *def* ker_lift
- \+/\- *def* quotient.mkₐ
- \+/\- *def* ker_lift_alg
- \+/\- *def* quot_left_to_quot_sup
- \+/\- *def* quot_quot_to_quot_sup
- \+/\- *def* quot_quot_mk
- \+/\- *def* lift_sup_quot_quot_mk
- \+/\- *def* quot_quot_equiv_quot_sup
- \+/\- *def* quot_quot_equiv_comm
- \+/\- *def* ker_lift
- \+/\- *def* quotient.mkₐ
- \+/\- *def* ker_lift_alg
- \+/\- *def* quot_left_to_quot_sup
- \+/\- *def* quot_quot_to_quot_sup
- \+/\- *def* quot_quot_mk
- \+/\- *def* lift_sup_quot_quot_mk
- \+/\- *def* quot_quot_equiv_quot_sup
- \+/\- *def* quot_quot_equiv_comm

Modified src/ring_theory/ideal/over.lean
- \+/\- *lemma* comap_eq_of_scalar_tower_quotient
- \+/\- *lemma* comap_eq_of_scalar_tower_quotient

Modified src/ring_theory/ideal/quotient.lean
- \+/\- *lemma* ring_hom_ext
- \+/\- *lemma* is_domain_iff_prime
- \+/\- *lemma* ring_hom_ext
- \+/\- *lemma* is_domain_iff_prime
- \+/\- *theorem* mk_eq_mk
- \+/\- *theorem* zero_eq_one_iff
- \+/\- *theorem* zero_ne_one_iff
- \+/\- *theorem* mk_eq_mk
- \+/\- *theorem* zero_eq_one_iff
- \+/\- *theorem* zero_ne_one_iff
- \+/\- *def* mk
- \+/\- *def* factor
- \- *def* quotient
- \+/\- *def* mk
- \+/\- *def* factor

Modified src/ring_theory/integral_closure.lean

Modified src/ring_theory/jacobson.lean

Modified src/ring_theory/jacobson_ideal.lean

Modified src/ring_theory/noetherian.lean

Modified src/ring_theory/nullstellensatz.lean

Modified src/ring_theory/perfection.lean

Modified src/ring_theory/polynomial/basic.lean

Modified src/ring_theory/valuation/basic.lean
- \+/\- *lemma* self_le_supp_comap
- \+/\- *lemma* comap_on_quot_eq
- \+/\- *lemma* self_le_supp_comap
- \+/\- *lemma* comap_on_quot_eq
- \+/\- *lemma* self_le_supp_comap
- \+/\- *lemma* comap_on_quot_eq
- \+/\- *lemma* self_le_supp_comap
- \+/\- *lemma* comap_on_quot_eq
- \+/\- *def* on_quot_val
- \+/\- *def* on_quot_val

Modified src/topology/algebra/group.lean
- \+/\- *lemma* quotient_group.is_open_map_coe
- \+/\- *lemma* quotient_group.is_open_map_coe

Modified src/topology/algebra/ring.lean

Modified src/topology/algebra/uniform_ring.lean



## [2021-12-04 00:14:36](https://github.com/leanprover-community/mathlib/commit/0bd9b6a)
feat(group_theory/order_of_element): order of a product of elements ([#10399](https://github.com/leanprover-community/mathlib/pull/10399))
The lemma is: If `x` and `y` are commuting elements of coprime orders, then the order of `x * y` is the product of the orders of `x` and `y`. This also gives a version for the minimal period in dynamics from which the algebraic statement is derived.
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+ *theorem* lcm_dvd_mul

Modified src/dynamics/periodic_pts.lean
- \+ *lemma* comp
- \+ *lemma* comp_lcm
- \+ *lemma* left_of_comp
- \+ *lemma* iterate_mod_apply
- \+ *lemma* commute.minimal_period_of_comp_dvd_mul
- \+ *lemma* commute.minimal_period_of_comp_eq_mul_of_coprime

Modified src/group_theory/order_of_element.lean
- \+ *lemma* commute.order_of_mul_dvd_lcm_order_of
- \+ *lemma* commute.order_of_mul_dvd_mul_order_of
- \+ *lemma* commute.order_of_mul_eq_mul_order_of_of_coprime



## [2021-12-03 20:46:31](https://github.com/leanprover-community/mathlib/commit/1376f53)
feat(analysis.normed_space.lattice_ordered_group): Add `two_inf_sub_two_inf_le`, `two_sup_sub_two_sup_le` and supporting lemmas ([#10514](https://github.com/leanprover-community/mathlib/pull/10514))
feat(analysis.normed_space.lattice_ordered_group): Add `two_inf_sub_two_inf_le`, `two_sup_sub_two_sup_le` and supporting lemmas
#### Estimated changes
Modified src/algebra/lattice_ordered_group.lean
- \+ *lemma* inf_sq_eq_mul_div_abs_div
- \+ *lemma* abs_inv_comm
- \+ *lemma* abs_abs_div_abs_le
- \- *lemma* two_inf_eq_mul_div_abs_div

Modified src/analysis/normed_space/lattice_ordered_group.lean
- \+ *lemma* norm_abs_sub_abs
- \+ *lemma* norm_two_inf_sub_two_inf_le
- \+ *lemma* norm_two_sup_sub_two_sup_le



## [2021-12-03 19:27:08](https://github.com/leanprover-community/mathlib/commit/cd2230b)
chore(data/nat/prime): golf some proofs ([#10599](https://github.com/leanprover-community/mathlib/pull/10599))
#### Estimated changes
Modified src/data/nat/prime.lean



## [2021-12-03 19:27:05](https://github.com/leanprover-community/mathlib/commit/bddc16a)
fix(tactic/abel): handle smul on groups ([#10587](https://github.com/leanprover-community/mathlib/pull/10587))
The issue was that `abel` expects to see only `smulg` used for groups and only `smul` for monoids, but you can also use `smul` on groups so we have to normalize that away.
fixes [#8456](https://github.com/leanprover-community/mathlib/pull/8456)
#### Estimated changes
Modified src/tactic/abel.lean
- \+ *lemma* subst_into_smul_upcast

Modified test/abel.lean



## [2021-12-03 17:46:34](https://github.com/leanprover-community/mathlib/commit/46e9a23)
feat(probability_theory/stopping): generalize a lemma ([#10598](https://github.com/leanprover-community/mathlib/pull/10598))
#### Estimated changes
Modified src/probability_theory/stopping.lean
- \+/\- *lemma* measurable
- \+/\- *lemma* measurable
- \- *def* measurable_space



## [2021-12-03 17:46:33](https://github.com/leanprover-community/mathlib/commit/1e89745)
feat(data/finset/lattice): add sup_eq_bot_iff and inf_eq_top_iff ([#10596](https://github.com/leanprover-community/mathlib/pull/10596))
From flt-regular.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* sup_eq_bot_iff
- \+ *lemma* inf_eq_top_iff



## [2021-12-03 17:46:32](https://github.com/leanprover-community/mathlib/commit/92fafba)
feat(data/(mv_)polynomial): add aeval_prod and aeval_sum for (mv_)polynomial ([#10594](https://github.com/leanprover-community/mathlib/pull/10594))
Another couple of small polynomial helper lemmas from flt-regular.
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* aeval_sum
- \+ *lemma* aeval_prod

Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* aeval_sum
- \+ *lemma* aeval_prod



## [2021-12-03 17:46:31](https://github.com/leanprover-community/mathlib/commit/4de0773)
feat(category_theory/limits): Strict terminal objects. ([#10582](https://github.com/leanprover-community/mathlib/pull/10582))
#### Estimated changes
Modified src/category_theory/limits/shapes/strict_initial.lean
- \+ *lemma* is_terminal.is_iso_from
- \+ *lemma* is_terminal.strict_hom_ext
- \+ *lemma* is_terminal.subsingleton_to
- \+ *lemma* limit_π_is_iso_of_is_strict_terminal
- \+ *lemma* terminal.hom_ext
- \+ *lemma* terminal.subsingleton_to
- \+ *lemma* has_strict_terminal_objects_of_terminal_is_strict



## [2021-12-03 17:46:29](https://github.com/leanprover-community/mathlib/commit/d45708f)
feat(topology/sheaves): The empty component of a sheaf is terminal ([#10578](https://github.com/leanprover-community/mathlib/pull/10578))
#### Estimated changes
Modified src/category_theory/sites/sheaf.lean
- \+ *def* Sheaf.is_terminal_of_bot_cover

Modified src/topology/sheaves/sheaf_condition/sites.lean
- \+ *def* is_terminal_of_empty
- \+ *def* is_terminal_of_eq_empty



## [2021-12-03 16:11:45](https://github.com/leanprover-community/mathlib/commit/1e18e93)
chore(algebra/lattice_ordered_group): review (names, spaces, golf...) ([#10595](https://github.com/leanprover-community/mathlib/pull/10595))
This is a review of `algebra/lattice_ordered_group` and `analysis/normed_space/lattice_ordered_group`:
- delete or add spaces at many places
- add brackets around goals
- replace `apply` by `exact` when closing a goal
- change many names to better fit the naming convention
- cut some big proofs into several lemmas
- add a few `simp` attributes
- remove a non-terminal simp
- golf
- add some simple API lemmas
I did not do anything about the docstrings of the lemmas. Some of them don't interact correctly with `to_additive` (the additive comment is shown for the multiplicative lemma in the doc, for example).
#### Estimated changes
Modified src/algebra/lattice_ordered_group.lean
- \+ *lemma* mul_sup
- \+ *lemma* mul_inf
- \+ *lemma* pos_one
- \+ *lemma* neg_one
- \+/\- *lemma* neg_eq_inv_inf_one
- \+ *lemma* one_le_pos
- \+ *lemma* one_le_neg
- \+ *lemma* pos_le_one_iff
- \+ *lemma* neg_le_one_iff
- \+ *lemma* pos_eq_one_iff
- \+ *lemma* neg_eq_one_iff'
- \+ *lemma* neg_eq_one_iff
- \+ *lemma* inv_le_neg
- \+/\- *lemma* neg_eq_pos_inv
- \+ *lemma* pos_div_neg
- \+/\- *lemma* pos_inf_neg_eq_one
- \+ *lemma* m_neg_abs
- \+ *lemma* m_pos_abs
- \+ *lemma* one_le_abs
- \+ *lemma* pos_of_one_le
- \+ *lemma* pos_of_le_one
- \+ *lemma* neg_of_one_le_inv
- \+ *lemma* neg_of_inv_le_one
- \+ *lemma* neg_of_le_one
- \+ *lemma* neg_of_one_le
- \+ *lemma* mabs_of_one_le
- \+ *lemma* m_abs_abs
- \+ *lemma* mabs_sup_div_sup_le_mabs
- \+ *lemma* mabs_inf_div_inf_le_mabs
- \+ *lemma* mabs_mul_le
- \- *lemma* mul_sup_eq_mul_sup_mul
- \- *lemma* m_pos_pos
- \- *lemma* m_neg_pos
- \- *lemma* m_le_neg
- \+/\- *lemma* neg_eq_pos_inv
- \+/\- *lemma* neg_eq_inv_inf_one
- \- *lemma* pos_inv_neg
- \- *lemma* pos_div_neg'
- \+/\- *lemma* pos_inf_neg_eq_one
- \- *lemma* m_pos_pos_id
- \- *lemma* mabs_pos_eq
- \- *lemma* mabs_pos
- \- *lemma* mabs_idempotent
- \- *lemma* mabs_triangle

Modified src/analysis/normed_space/lattice_ordered_group.lean
- \+/\- *lemma* dual_solid
- \+/\- *lemma* norm_abs_eq_norm
- \+ *lemma* norm_inf_sub_inf_le_add_norm
- \+/\- *lemma* dual_solid
- \+/\- *lemma* norm_abs_eq_norm



## [2021-12-03 16:11:43](https://github.com/leanprover-community/mathlib/commit/a7b4018)
fix(tactic/ring): bugfixes in ring_nf ([#10572](https://github.com/leanprover-community/mathlib/pull/10572))
As reported by @hrmacbeth:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60ring_nf.60.20behaves.20strangely.20with.20def.20in.20original.20goal
#### Estimated changes
Modified src/geometry/euclidean/basic.lean

Modified src/geometry/manifold/instances/sphere.lean

Modified src/tactic/ring.lean

Modified test/ring.lean



## [2021-12-03 16:11:41](https://github.com/leanprover-community/mathlib/commit/df93166)
feat(algebraic_geometry): Explicit description of the colimit of presheafed spaces. ([#10466](https://github.com/leanprover-community/mathlib/pull/10466))
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space/has_colimits.lean
- \+ *lemma* colimit_presheaf_obj_iso_componentwise_limit_inv_ι_app
- \+ *lemma* colimit_presheaf_obj_iso_componentwise_limit_hom_π
- \+ *def* componentwise_diagram
- \+ *def* colimit_presheaf_obj_iso_componentwise_limit



## [2021-12-03 16:11:40](https://github.com/leanprover-community/mathlib/commit/b7ed03f)
feat(algebraic_geometry): Open immersions of presheafed spaces ([#10437](https://github.com/leanprover-community/mathlib/pull/10437))
#### Estimated changes
Created src/algebraic_geometry/open_immersion.lean
- \+ *lemma* iso_restrict_hom_of_restrict
- \+ *lemma* iso_restrict_inv_of_restrict
- \+ *lemma* inv_naturality
- \+ *lemma* inv_inv_app
- \+ *lemma* inv_app_app
- \+ *lemma* app_inv_app
- \+ *lemma* app_inv_app'
- \+ *lemma* to_iso
- \+ *def* iso_restrict
- \+ *def* inv_app

Modified src/algebraic_geometry/stalks.lean
- \+ *lemma* restrict_stalk_iso_inv_eq_of_restrict

Modified src/topology/sheaves/stalks.lean
- \+ *lemma* stalk_pushforward_iso_of_open_embedding



## [2021-12-03 16:11:38](https://github.com/leanprover-community/mathlib/commit/2f44ac8)
feat(algebra/monoid_algebra/grading): internal graded structure for an arbitrary degree function ([#10435](https://github.com/leanprover-community/mathlib/pull/10435))
This gives an internal graded structure of an additive monoid algebra for the grading given by an arbitrary degree function. The grading in the original file is redefined as the grading for the identity degree function.
#### Estimated changes
Modified src/algebra/monoid_algebra/grading.lean
- \+ *lemma* grade_by_id
- \+ *lemma* mem_grade_by_iff
- \+ *lemma* mem_grade_iff
- \+ *lemma* mem_grade_iff'
- \+ *lemma* grade_eq_lsingle_range
- \+ *lemma* single_mem_grade_by
- \+ *lemma* single_mem_grade
- \+ *lemma* to_grades_by_single'
- \+ *lemma* to_grades_by_single
- \+ *lemma* to_grades_by_coe
- \+ *lemma* of_grades_by_of
- \+ *lemma* of_grades_by_comp_to_grades_by
- \+/\- *lemma* of_grades_comp_to_grades
- \+ *lemma* of_grades_by_to_grades_by
- \+ *lemma* to_grades_by_comp_of_grades_by
- \+/\- *lemma* to_grades_comp_of_grades
- \+ *lemma* to_grades_by_of_grades_by
- \+ *lemma* grade_by.is_internal
- \+/\- *lemma* of_grades_comp_to_grades
- \+/\- *lemma* to_grades_comp_of_grades
- \+ *def* to_grades_by
- \+/\- *def* to_grades
- \+ *def* of_grades_by
- \+ *def* equiv_grades_by
- \+/\- *def* to_grades



## [2021-12-03 16:11:37](https://github.com/leanprover-community/mathlib/commit/f0a1cd1)
feat(category_theory/*): Representably flat functors ([#9519](https://github.com/leanprover-community/mathlib/pull/9519))
Defined representably flat functors as functors `F : C ⥤ D` such that `(X/F)` is cofiltered for each `X : C`.
- Proved that if `C` has all finite limits and `F` preserves them, then `F` is flat.
- Proved that flat functors preserves finite limits.
In particular, if `C` is finitely complete, then flat iff left exact.
- Proved that if `C, D` are small, then `F` flat implies `Lan F.op` preserves finite limits implies `F` preserves finite limits.
In particular, if `C` is finitely cocomplete, then flat iff `Lan F.op` is left exact.
#### Estimated changes
Modified src/category_theory/comma.lean
- \+ *lemma* eq_to_hom_left
- \+ *lemma* eq_to_hom_right

Created src/category_theory/flat_functors.lean
- \+ *lemma* flat_of_preserves_finite_limits
- \+ *lemma* fac
- \+ *lemma* uniq
- \+ *lemma* flat_iff_Lan_flat
- \+ *def* to_diagram
- \+ *def* diagram_to_cone
- \+ *def* to_cone
- \+ *def* preserves_finite_limits_of_flat
- \+ *def* preserves_finite_limits_iff_flat
- \+ *def* Lan_evaluation_iso_colim
- \+ *def* preserves_finite_limits_iff_Lan_preserves_finite_limits

Created src/category_theory/limits/bicones.lean
- \+ *def* bicone_mk

Modified src/category_theory/limits/constructions/limits_of_products_and_equalizers.lean

Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean

Created src/category_theory/limits/preserves/finite.lean
- \+ *def* comp_preserves_finite_limits
- \+ *def* comp_preserves_finite_colimits

Modified src/category_theory/limits/preserves/functor_category.lean
- \+ *def* preserves_limit_of_Lan_presesrves_limit

Modified src/category_theory/limits/presheaf.lean
- \+ *def* extend_of_comp_yoneda_iso_Lan
- \+ *def* comp_yoneda_iso_yoneda_comp_Lan

Modified src/category_theory/limits/shapes/finite_limits.lean
- \- *lemma* has_finite_limits_of_has_limits
- \- *lemma* has_finite_colimits_of_has_colimits

Modified src/category_theory/structured_arrow.lean



## [2021-12-03 14:32:19](https://github.com/leanprover-community/mathlib/commit/8bb26a7)
chore(*): protect `to_fun` and `map_{add,zero,mul,one,div}` ([#10580](https://github.com/leanprover-community/mathlib/pull/10580))
This PR prepares for [#9888](https://github.com/leanprover-community/mathlib/pull/9888) by namespacing all usages of `to_fun` and `map_{add,zero,mul,one,div}` that do not involve the classes of [#9888](https://github.com/leanprover-community/mathlib/pull/9888). This includes e.g. `polynomial.map_add` and `multiset.map_add`, which involve `polynomial.map` and `multiset.map` respectively.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean

Modified src/algebra/direct_sum/ring.lean

Modified src/algebra/monoid_algebra/to_direct_sum.lean

Modified src/analysis/normed_space/extend.lean

Modified src/control/fold.lean

Modified src/data/complex/is_R_or_C.lean

Modified src/data/finset/fold.lean

Modified src/data/polynomial/basic.lean

Modified src/data/polynomial/denoms_clearable.lean

Modified src/data/polynomial/eval.lean

Modified src/deprecated/subgroup.lean

Modified src/field_theory/abel_ruffini.lean

Modified src/field_theory/finite/basic.lean

Modified src/field_theory/finite/galois_field.lean

Modified src/field_theory/fixed.lean

Modified src/group_theory/perm/cycle_type.lean

Modified src/group_theory/quotient_group.lean

Modified src/linear_algebra/pi_tensor_product.lean

Modified src/measure_theory/integral/bochner.lean

Modified src/ring_theory/dedekind_domain.lean
- \+ *lemma* one_inv
- \- *lemma* fractional_ideal.one_inv

Modified src/ring_theory/jacobson.lean

Modified src/ring_theory/polynomial/chebyshev.lean

Modified src/ring_theory/polynomial/pochhammer.lean

Modified src/ring_theory/polynomial/vieta.lean

Modified src/ring_theory/roots_of_unity.lean



## [2021-12-03 14:32:17](https://github.com/leanprover-community/mathlib/commit/235e583)
feat(topology/metric_space/hausdorff_distance): add definition and lemmas about closed thickenings of subsets ([#10542](https://github.com/leanprover-community/mathlib/pull/10542))
Add definition and basic API about closed thickenings of subsets in metric spaces, in preparation for the portmanteau theorem on characterizations of weak convergence of Borel probability measures.
#### Estimated changes
Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* mem_thickening_iff_exists_edist_lt
- \+ *lemma* cthickening_eq_preimage_inf_edist
- \+ *lemma* is_closed_cthickening
- \+ *lemma* cthickening_empty
- \+ *lemma* cthickening_zero
- \+ *lemma* cthickening_mono
- \+ *lemma* closure_subset_cthickening
- \+ *lemma* cthickening_subset_of_subset
- \+ *lemma* cthickening_subset_thickening
- \+ *lemma* cthickening_subset_thickening'
- \+ *lemma* thickening_subset_cthickening
- \+ *lemma* thickening_subset_cthickening_of_le
- \+ *lemma* cthickening_eq_Inter_cthickening
- \+ *lemma* closure_eq_Inter_cthickening
- \+ *def* cthickening



## [2021-12-03 12:40:48](https://github.com/leanprover-community/mathlib/commit/6533500)
feat(data/mv_polynomial): add total_degree_add_of_total_degree_lt ([#10571](https://github.com/leanprover-community/mathlib/pull/10571))
A helpful lemma to compute total degrees from flt-regular.
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* support_sdiff_support_subset_support_add
- \+ *lemma* support_symm_diff_support_subset_support_add

Modified src/data/mv_polynomial/variables.lean
- \+ *lemma* total_degree_add_eq_left_of_total_degree_lt
- \+ *lemma* total_degree_add_eq_right_of_total_degree_lt



## [2021-12-03 12:40:47](https://github.com/leanprover-community/mathlib/commit/672e2b2)
feat(src/algebra/gcd_monoid,src/ring_theory): add some exists_associated_pow_of_mul_eq_pow variants ([#10560](https://github.com/leanprover-community/mathlib/pull/10560))
#### Estimated changes
Modified src/algebra/gcd_monoid/basic.lean
- \+ *theorem* exists_eq_pow_of_mul_eq_pow

Modified src/ring_theory/int/basic.lean
- \+ *theorem* eq_pow_of_mul_eq_pow_bit1_left
- \+ *theorem* eq_pow_of_mul_eq_pow_bit1_right
- \+ *theorem* eq_pow_of_mul_eq_pow_bit1

Modified src/ring_theory/principal_ideal_domain.lean
- \+ *theorem* exists_associated_pow_of_mul_eq_pow'



## [2021-12-03 12:40:46](https://github.com/leanprover-community/mathlib/commit/89697a2)
feat(data/fintype/order): complete order instances for fintype ([#7123](https://github.com/leanprover-community/mathlib/pull/7123))
This PR adds several instances (as defs) for fintypes:
* `order_bot` from `semilattice_inf`, `order_top` from `semilattice_sup`, `bounded_order` from `lattice`.
* `complete_lattice` from `lattice`.
* `complete_linear_order` from `linear_order`.
We use this last one to give a `complete_linear_order` instance for `fin (n + 1)` .
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* fold_inf_univ
- \+ *lemma* fold_sup_univ

Created src/data/fintype/order.lean
- \+ *def* fintype.to_order_bot
- \+ *def* fintype.to_order_top
- \+ *def* fintype.to_bounded_order



## [2021-12-03 10:55:10](https://github.com/leanprover-community/mathlib/commit/e0c27fe)
feat(order/bounded_order): a few more `simp` lemmas ([#10533](https://github.com/leanprover-community/mathlib/pull/10533))
Inspired by [#10486](https://github.com/leanprover-community/mathlib/pull/10486)
#### Estimated changes
Modified src/order/bounded_order.lean
- \+ *lemma* min_bot_left
- \+ *lemma* min_bot_right
- \+ *lemma* max_top_left
- \+ *lemma* max_top_right
- \+ *lemma* min_eq_bot
- \+ *lemma* max_eq_top
- \+ *lemma* max_eq_bot
- \+ *lemma* min_eq_top



## [2021-12-03 10:55:09](https://github.com/leanprover-community/mathlib/commit/970f074)
feat(analysis/convex/star): Star-convex sets ([#10524](https://github.com/leanprover-community/mathlib/pull/10524))
This defines `star_convex 𝕜 x s` to mean that a set is star-convex (aka star-shaped, radially convex, or a star domain) at `x`. This means that every segment from `x` to a point in `s` is a subset of `s`.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* set_vadd_singleton
- \- *lemma* vadd_singleton

Modified src/algebra/pointwise.lean
- \+ *lemma* smul_singleton

Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex.sub
- \+/\- *lemma* convex.sub

Created src/analysis/convex/star.lean
- \+ *lemma* convex_iff_forall_star_convex
- \+ *lemma* star_convex_iff_segment_subset
- \+ *lemma* star_convex.segment_subset
- \+ *lemma* star_convex.open_segment_subset
- \+ *lemma* star_convex_iff_pointwise_add_subset
- \+ *lemma* star_convex_empty
- \+ *lemma* star_convex_univ
- \+ *lemma* star_convex.inter
- \+ *lemma* star_convex_sInter
- \+ *lemma* star_convex_Inter
- \+ *lemma* star_convex.union
- \+ *lemma* star_convex_Union
- \+ *lemma* star_convex_sUnion
- \+ *lemma* star_convex.prod
- \+ *lemma* star_convex_pi
- \+ *lemma* star_convex.mem
- \+ *lemma* convex.star_convex_iff
- \+ *lemma* star_convex_iff_forall_pos
- \+ *lemma* star_convex_iff_forall_ne_pos
- \+ *lemma* star_convex_iff_open_segment_subset
- \+ *lemma* star_convex_singleton
- \+ *lemma* star_convex.linear_image
- \+ *lemma* star_convex.is_linear_image
- \+ *lemma* star_convex.linear_preimage
- \+ *lemma* star_convex.is_linear_preimage
- \+ *lemma* star_convex.add
- \+ *lemma* star_convex.add_left
- \+ *lemma* star_convex.add_right
- \+ *lemma* star_convex.preimage_add_right
- \+ *lemma* star_convex.preimage_add_left
- \+ *lemma* star_convex.sub
- \+ *lemma* star_convex.smul
- \+ *lemma* star_convex.preimage_smul
- \+ *lemma* star_convex.affinity
- \+ *lemma* star_convex.add_smul_mem
- \+ *lemma* star_convex.smul_mem
- \+ *lemma* star_convex.add_smul_sub_mem
- \+ *lemma* star_convex.affine_preimage
- \+ *lemma* star_convex.affine_image
- \+ *lemma* star_convex.neg
- \+ *lemma* star_convex.neg_preimage
- \+ *lemma* star_convex_iff_div
- \+ *lemma* star_convex.mem_smul
- \+ *lemma* set.ord_connected.star_convex
- \+ *lemma* star_convex_iff_ord_connected
- \+ *lemma* submodule.star_convex
- \+ *lemma* subspace.star_convex
- \+ *def* star_convex

Modified src/data/set/intervals/ord_connected.lean
- \+/\- *lemma* ord_connected_interval
- \+/\- *lemma* ord_connected.interval_subset
- \+/\- *lemma* ord_connected_iff_interval_subset
- \+ *lemma* ord_connected_iff_interval_subset_left
- \+ *lemma* ord_connected_iff_interval_subset_right
- \+/\- *lemma* ord_connected_interval
- \+/\- *lemma* ord_connected.interval_subset
- \+/\- *lemma* ord_connected_iff_interval_subset

Modified src/data/set/intervals/unordered_interval.lean
- \+/\- *lemma* not_mem_interval_of_lt
- \+/\- *lemma* not_mem_interval_of_gt
- \+ *lemma* interval_subset_interval_union_interval
- \+/\- *lemma* not_mem_interval_of_lt
- \+/\- *lemma* not_mem_interval_of_gt



## [2021-12-03 10:55:08](https://github.com/leanprover-community/mathlib/commit/44b649c)
doc(algebra.lattice_ordered_group): Remove verbose docstrings ([#10468](https://github.com/leanprover-community/mathlib/pull/10468))
doc(algebra.lattice_ordered_group): Remove verbose docstrings
#### Estimated changes
Modified src/algebra/lattice_ordered_group.lean

Modified src/analysis/normed_space/lattice_ordered_group.lean



## [2021-12-03 08:57:31](https://github.com/leanprover-community/mathlib/commit/2648e68)
chore(int/*): dedup lemma ([#10583](https://github.com/leanprover-community/mathlib/pull/10583))
#### Estimated changes
Modified src/data/int/basic.lean
- \+/\- *lemma* nat_abs_dvd_iff_dvd
- \+/\- *lemma* nat_abs_dvd_iff_dvd

Modified src/data/int/gcd.lean
- \- *theorem* nat_abs_dvd_abs_iff

Modified src/ring_theory/int/basic.lean



## [2021-12-03 08:57:30](https://github.com/leanprover-community/mathlib/commit/0453320)
feat(category_theory/limits): The product is the pullback over the terminal objects. ([#10581](https://github.com/leanprover-community/mathlib/pull/10581))
#### Estimated changes
Modified src/category_theory/limits/constructions/binary_products.lean
- \+ *lemma* has_binary_coproducts_of_initial_and_pushouts
- \+ *def* is_product_of_is_terminal_is_pullback
- \+ *def* is_pullback_of_is_terminal_is_product
- \+ *def* is_coproduct_of_is_initial_is_pushout
- \+ *def* is_pushout_of_is_initial_is_coproduct



## [2021-12-03 08:57:28](https://github.com/leanprover-community/mathlib/commit/bfccd1b)
chore(topology/{metric_space,instances/real}): cleanup ([#10577](https://github.com/leanprover-community/mathlib/pull/10577))
* merge `real.ball_eq` and `real.ball_eq_Ioo` into `real.ball_eq_Ioo`;
* merge `real.closed_ball_eq` and `real.closed_ball_eq_Icc` into `real.closed_ball_eq_Icc`;
* add missing `real.Icc_eq_closed_ball`;
* generalize lemmas about `*bounded_Ixx` so that they work for (indexed) products of conditionally complete linear orders.
#### Estimated changes
Modified src/analysis/seminorm.lean

Modified src/measure_theory/measure/lebesgue.lean

Modified src/number_theory/liouville/basic.lean

Modified src/topology/instances/real.lean
- \+ *theorem* ball_eq_Ioo
- \+ *theorem* closed_ball_eq_Icc
- \- *theorem* ball_eq
- \- *theorem* closed_ball_eq
- \- *theorem* real.ball_eq_Ioo
- \- *theorem* real.Ioo_eq_ball

Modified src/topology/metric_space/basic.lean
- \+ *lemma* real.ball_eq_Ioo
- \+ *lemma* real.closed_ball_eq_Icc
- \- *lemma* real.ball_eq
- \- *lemma* real.closed_ball_eq
- \+ *theorem* real.Ioo_eq_ball
- \+ *theorem* real.Icc_eq_closed_ball



## [2021-12-03 08:57:27](https://github.com/leanprover-community/mathlib/commit/158263c)
feat(ring_theory): Nilradical and reduced ring ([#10576](https://github.com/leanprover-community/mathlib/pull/10576))
#### Estimated changes
Modified src/ring_theory/nilpotent.lean
- \+/\- *lemma* is_nilpotent.eq_zero
- \+/\- *lemma* is_nilpotent_iff_eq_zero
- \+ *lemma* mem_nilradical
- \+ *lemma* nilradical_eq_Inf
- \+ *lemma* nilpotent_iff_mem_prime
- \+ *lemma* nilradical_le_prime
- \+ *lemma* nilradical_eq_zero
- \+/\- *lemma* is_nilpotent.eq_zero
- \+/\- *lemma* is_nilpotent_iff_eq_zero
- \+ *def* nilradical



## [2021-12-03 08:57:26](https://github.com/leanprover-community/mathlib/commit/c176aa5)
refactor(data/stream): swap args of `stream.nth` ([#10559](https://github.com/leanprover-community/mathlib/pull/10559))
This way it agrees with (a) `list.nth`; (b) a possible redefinition
```lean
structure stream (α : Type*) := (nth : nat → α)
```
#### Estimated changes
Modified src/data/stream/defs.lean
- \+/\- *def* nth
- \+/\- *def* all
- \+/\- *def* any
- \+/\- *def* nth
- \+/\- *def* all
- \+/\- *def* any

Modified src/data/stream/init.lean
- \+/\- *theorem* nth_zero_cons
- \+/\- *theorem* nth_drop
- \+/\- *theorem* nth_succ
- \+/\- *theorem* all_def
- \+/\- *theorem* any_def
- \+/\- *theorem* mem_of_nth_eq
- \+/\- *theorem* nth_map
- \+/\- *theorem* nth_const
- \+/\- *theorem* nth_zero_iterate
- \+/\- *theorem* nth_unfolds_head_tail
- \+/\- *theorem* nth_interleave_left
- \+/\- *theorem* nth_interleave_right
- \+/\- *theorem* nth_even
- \+/\- *theorem* nth_odd
- \+/\- *theorem* nth_take_succ
- \+/\- *theorem* nth_tails
- \+/\- *theorem* nth_inits
- \+/\- *theorem* nth_nats
- \+/\- *theorem* nth_zero_cons
- \+/\- *theorem* nth_drop
- \+/\- *theorem* nth_succ
- \+/\- *theorem* all_def
- \+/\- *theorem* any_def
- \+/\- *theorem* mem_of_nth_eq
- \+/\- *theorem* nth_map
- \+/\- *theorem* nth_const
- \+/\- *theorem* nth_zero_iterate
- \+/\- *theorem* nth_unfolds_head_tail
- \+/\- *theorem* nth_interleave_left
- \+/\- *theorem* nth_interleave_right
- \+/\- *theorem* nth_even
- \+/\- *theorem* nth_odd
- \+/\- *theorem* nth_take_succ
- \+/\- *theorem* nth_tails
- \+/\- *theorem* nth_inits
- \+/\- *theorem* nth_nats

Modified test/ext.lean



## [2021-12-03 08:57:25](https://github.com/leanprover-community/mathlib/commit/55b64b6)
chore(group_theory/*): additivise! ([#10557](https://github.com/leanprover-community/mathlib/pull/10557))
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+/\- *lemma* mul_zpow_neg_one
- \+/\- *lemma* mul_zpow_neg_one

Modified src/group_theory/coset.lean
- \+/\- *lemma* card_subgroup_dvd_card
- \+/\- *lemma* card_quotient_dvd_card
- \+/\- *lemma* card_dvd_of_injective
- \+/\- *lemma* card_dvd_of_le
- \+/\- *lemma* card_comap_dvd_of_injective
- \+/\- *lemma* card_subgroup_dvd_card
- \+/\- *lemma* card_quotient_dvd_card
- \+/\- *lemma* card_dvd_of_injective
- \+/\- *lemma* card_dvd_of_le
- \+/\- *lemma* card_comap_dvd_of_injective

Modified src/group_theory/specific_groups/cyclic.lean
- \+ *lemma* is_add_cyclic_of_card_pow_eq_one_le
- \+ *lemma* is_add_cyclic.card_order_of_eq_totient
- \- *lemma* card_pow_eq_one_eq_order_of_aux

Modified src/tactic/group.lean



## [2021-12-03 08:57:23](https://github.com/leanprover-community/mathlib/commit/56c9cab)
feat(data/sigma{lex,order}): Lexicographic and disjoint orders on a sigma type ([#10552](https://github.com/leanprover-community/mathlib/pull/10552))
This defines the two natural order on a sigma type: the one where we just juxtapose the summands with their respective order, and the one where we also add in an order between summands.
#### Estimated changes
Modified src/data/list/lex.lean

Created src/data/sigma/lex.lean
- \+ *lemma* lex_iff
- \+ *lemma* lex.mono
- \+ *lemma* lex.mono_left
- \+ *lemma* lex.mono_right
- \+ *lemma* lex_iff
- \+ *lemma* lex.mono
- \+ *lemma* lex.mono_left
- \+ *lemma* lex.mono_right

Created src/data/sigma/order.lean
- \+ *def* lex.has_le
- \+ *def* lex.has_lt
- \+ *def* lex.preorder
- \+ *def* lex.partial_order
- \+ *def* lex.linear_order

Modified src/order/lexicographic.lean



## [2021-12-03 08:57:22](https://github.com/leanprover-community/mathlib/commit/d62b517)
feat(category_theory/limits): Walking parallel pair equiv to its op. ([#10516](https://github.com/leanprover-community/mathlib/pull/10516))
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* walking_parallel_pair_op_zero
- \+ *lemma* walking_parallel_pair_op_one
- \+ *lemma* walking_parallel_pair_op_left
- \+ *lemma* walking_parallel_pair_op_right
- \+ *lemma* walking_parallel_pair_op_equiv_unit_iso_zero
- \+ *lemma* walking_parallel_pair_op_equiv_unit_iso_one
- \+ *lemma* walking_parallel_pair_op_equiv_counit_iso_zero
- \+ *lemma* walking_parallel_pair_op_equiv_counit_iso_one
- \+ *def* walking_parallel_pair_op
- \+ *def* walking_parallel_pair_op_equiv



## [2021-12-03 08:57:21](https://github.com/leanprover-community/mathlib/commit/c151a12)
feat(algebra/gcd_monoid/*): assorted lemmas ([#10508](https://github.com/leanprover-community/mathlib/pull/10508))
From flt-regular.
#### Estimated changes
Modified src/algebra/gcd_monoid/finset.lean
- \+ *theorem* gcd_image
- \+ *theorem* gcd_eq_gcd_image

Created src/algebra/gcd_monoid/nat.lean
- \+ *theorem* coprime_of_div_gcd



## [2021-12-03 08:57:20](https://github.com/leanprover-community/mathlib/commit/c093d04)
feat(data/nat/basic): Monotonicity of `nat.find_greatest` ([#10507](https://github.com/leanprover-community/mathlib/pull/10507))
This proves that `nat.find_greatest` is monotone in both arguments.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* find_greatest_succ
- \+/\- *lemma* find_greatest_eq
- \+/\- *lemma* find_greatest_of_not
- \+/\- *lemma* find_greatest_eq_iff
- \+/\- *lemma* find_greatest_eq_zero_iff
- \+/\- *lemma* find_greatest_spec
- \+/\- *lemma* find_greatest_le
- \+/\- *lemma* le_find_greatest
- \+ *lemma* find_greatest_mono_right
- \+ *lemma* find_greatest_mono_left
- \+ *lemma* find_greatest_mono
- \+/\- *lemma* find_greatest_is_greatest
- \+/\- *lemma* find_greatest_of_ne_zero
- \+/\- *lemma* find_greatest_eq
- \+/\- *lemma* find_greatest_of_not
- \+/\- *lemma* find_greatest_eq_iff
- \+/\- *lemma* find_greatest_eq_zero_iff
- \+/\- *lemma* find_greatest_spec
- \+/\- *lemma* find_greatest_le
- \+/\- *lemma* le_find_greatest
- \+/\- *lemma* find_greatest_is_greatest
- \+/\- *lemma* find_greatest_of_ne_zero

Modified src/measure_theory/measurable_space.lean



## [2021-12-03 08:57:19](https://github.com/leanprover-community/mathlib/commit/00e9e90)
feat(topology/urysohns_bounded): +2 versions of Urysohn's lemma ([#10479](https://github.com/leanprover-community/mathlib/pull/10479))
#### Estimated changes
Created src/topology/urysohns_bounded.lean
- \+ *lemma* exists_bounded_zero_one_of_closed
- \+ *lemma* exists_bounded_mem_Icc_of_closed_of_le



## [2021-12-03 07:10:46](https://github.com/leanprover-community/mathlib/commit/403d9c0)
feat(category_theory/adjunction): Added simp lemmas for `left_adjoint_uniq` and `right_adjoint_uniq` ([#10551](https://github.com/leanprover-community/mathlib/pull/10551))
#### Estimated changes
Modified src/category_theory/adjunction/opposites.lean
- \+ *lemma* hom_equiv_left_adjoint_uniq_hom_app
- \+ *lemma* unit_left_adjoint_uniq_hom
- \+ *lemma* unit_left_adjoint_uniq_hom_app
- \+ *lemma* left_adjoint_uniq_hom_counit
- \+ *lemma* left_adjoint_uniq_hom_app_counit
- \+ *lemma* left_adjoint_uniq_inv_app
- \+ *lemma* left_adjoint_uniq_trans
- \+ *lemma* left_adjoint_uniq_trans_app
- \+ *lemma* left_adjoint_uniq_refl
- \+ *lemma* hom_equiv_symm_right_adjoint_uniq_hom_app
- \+ *lemma* unit_right_adjoint_uniq_hom_app
- \+ *lemma* unit_right_adjoint_uniq_hom
- \+ *lemma* right_adjoint_uniq_hom_app_counit
- \+ *lemma* right_adjoint_uniq_hom_counit
- \+ *lemma* right_adjoint_uniq_inv_app
- \+ *lemma* right_adjoint_uniq_trans_app
- \+ *lemma* right_adjoint_uniq_trans
- \+ *lemma* right_adjoint_uniq_refl
- \+/\- *def* adjoint_of_op_adjoint_op
- \+/\- *def* op_adjoint_op_of_adjoint
- \+/\- *def* adjoint_of_op_adjoint_op
- \+/\- *def* op_adjoint_op_of_adjoint



## [2021-12-03 07:10:45](https://github.com/leanprover-community/mathlib/commit/30185dc)
feat(topology/algebra/group): group topologies on a given group form a complete lattice ([#10531](https://github.com/leanprover-community/mathlib/pull/10531))
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *lemma* ext'
- \+ *lemma* coinduced_continuous
- \+ *def* coinduced

Modified src/topology/algebra/ring.lean
- \+ *def* to_add_group_topology
- \+ *def* to_add_group_topology.order_embedding



## [2021-12-03 07:10:44](https://github.com/leanprover-community/mathlib/commit/cfecf72)
feat(algebra/module): push forward the action of `R` on `M` along `f : R → S` ([#10502](https://github.com/leanprover-community/mathlib/pull/10502))
If `f : R →+* S` is compatible with the `R`-module structure on `M`, and the scalar action of `S` on `M`, then `M` gets an `S`-module structure too. Additionally, if `R` is a ring and the kernel of `f` acts on `M` by sending it to `0`, then we don't need to specify the scalar action of `S` on `M` (but it is still possible for defeq purposes).
These definitions should allow you to turn an action of `R` on `M` into an action of `R/I` on `M/N` via the (previously defined) action of `R` on `M/N`.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *def* function.surjective.module_left

Modified src/group_theory/group_action/defs.lean
- \+ *def* function.surjective.mul_action_left
- \+ *def* function.surjective.distrib_mul_action_left



## [2021-12-03 07:10:43](https://github.com/leanprover-community/mathlib/commit/461051a)
feat(algebraic_geometry): Localization map is an embedding. ([#10471](https://github.com/leanprover-community/mathlib/pull/10471))
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+ *lemma* localization_comap_inducing
- \+ *lemma* localization_comap_injective
- \+ *lemma* localization_comap_embedding
- \+ *lemma* localization_comap_range
- \+ *lemma* localization_away_comap_range
- \+ *lemma* localization_away_open_embedding



## [2021-12-03 07:10:41](https://github.com/leanprover-community/mathlib/commit/6bd6b45)
feat(algebraic_geometry): Isomorphisms of presheafed space. ([#10461](https://github.com/leanprover-community/mathlib/pull/10461))
#### Estimated changes
Modified src/algebraic_geometry/Spec.lean

Modified src/algebraic_geometry/presheafed_space.lean
- \+/\- *lemma* comp_c_app
- \+ *lemma* is_iso_of_components
- \+/\- *lemma* comp_c_app
- \+ *def* iso_of_components
- \+ *def* sheaf_iso_of_iso

Modified src/algebraic_geometry/presheafed_space/has_colimits.lean

Modified src/category_theory/limits/has_limits.lean
- \+/\- *lemma* colimit.pre_desc
- \+/\- *lemma* colimit.pre_desc

Modified src/topology/category/Top/opens.lean
- \+ *def* map_map_iso

Modified src/topology/sheaves/presheaf.lean
- \+ *lemma* to_pushforward_of_iso_app
- \+ *lemma* pushforward_to_of_iso_app
- \+ *lemma* pullback_obj_eq_pullback_obj
- \+ *def* presheaf_equiv_of_iso
- \+ *def* to_pushforward_of_iso
- \+ *def* pushforward_to_of_iso
- \+ *def* pullback_hom_iso_pushforward_inv
- \+ *def* pullback_inv_iso_pushforward_hom



## [2021-12-03 07:10:40](https://github.com/leanprover-community/mathlib/commit/f8f28da)
feat(linear_algebra/orientation): orientations of modules and rays in modules ([#10306](https://github.com/leanprover-community/mathlib/pull/10306))
Define orientations of modules, along the lines of a definition
suggested by @hrmacbeth: equivalence classes of nonzero alternating
maps.  See:
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/adding.20angles/near/243856522
Rays are defined in an arbitrary module over an
`ordered_comm_semiring`, then orientations are considered as the case
of rays for the space of alternating maps.  That definition uses an
arbitrary index type; the motivating use case is where this has the
cardinality of a basis (two-dimensional use cases will use an index
type that is definitionally `fin 2`, for example).
The motivating use case is over the reals, but the definitions and
lemmas are for `ordered_comm_semiring`, `ordered_comm_ring`,
`linear_ordered_comm_ring` or `linear_ordered_field` as appropriate (a
`nontrivial` `ordered_comm_semiring` looks like it's the weakest case
for which much useful can be done with this definition).
Given an intended use case (oriented angles for Euclidean geometry)
where it will make sense for many proofs (and notation) to fix a
choice of orientation throughout, there is also a `module.oriented`
type class so the choice of orientation can be implicit in such proofs
and the lemmas they use.  However, nothing yet makes use of the type
class; everything so far is for explicit rays or orientations.
I expect more definitions and lemmas about orientations will need
adding to make much use of orientations.  In particular, I expect to
need to add more about orientations in relation to bases
(e.g. extracting a basis that gives a given orientation, in positive
dimension).
#### Estimated changes
Modified docs/undergrad.yaml

Created src/linear_algebra/orientation.lean
- \+ *lemma* symmetric_same_ray
- \+ *lemma* transitive_same_ray
- \+ *lemma* reflexive_same_ray
- \+ *lemma* equivalence_same_ray
- \+ *lemma* same_ray_pos_smul_right
- \+ *lemma* same_ray.pos_smul_right
- \+ *lemma* same_ray_pos_smul_left
- \+ *lemma* same_ray.pos_smul_left
- \+ *lemma* equiv_iff_same_ray
- \+ *lemma* module.ray.ind
- \+ *lemma* ray_eq_iff
- \+ *lemma* ray_pos_smul
- \+ *lemma* some_ray_vector_ray
- \+ *lemma* some_vector_ne_zero
- \+ *lemma* some_vector_ray
- \+ *lemma* same_ray.neg
- \+ *lemma* same_ray_neg_iff
- \+ *lemma* same_ray_neg_swap
- \+ *lemma* eq_zero_of_same_ray_self_neg
- \+ *lemma* coe_neg
- \+ *lemma* equiv_neg_iff
- \+ *lemma* ray_neg
- \+ *lemma* ne_neg_self
- \+ *lemma* same_ray_of_mem_orbit
- \+ *lemma* same_ray_smul_right_iff
- \+ *lemma* same_ray_smul_left_iff
- \+ *lemma* same_ray_neg_smul_right_iff
- \+ *lemma* same_ray_neg_smul_left_iff
- \+ *lemma* orientation_eq_iff_det_pos
- \+ *lemma* orientation_eq_or_eq_neg
- \+ *lemma* same_ray_iff_mem_orbit
- \+ *lemma* same_ray_setoid_eq_orbit_rel
- \+ *lemma* eq_or_eq_neg
- \+ *def* same_ray
- \+ *def* same_ray_setoid
- \+ *def* ray_vector
- \+ *def* ray_vector.same_ray_setoid
- \+ *def* module.ray
- \+ *def* some_ray_vector
- \+ *def* some_vector



## [2021-12-03 07:10:39](https://github.com/leanprover-community/mathlib/commit/2bb627f)
feat(analysis/convex/[basic, topology]): generalize path connectedness of convex sets to topological real vector spaces ([#10011](https://github.com/leanprover-community/mathlib/pull/10011))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* segment_eq_image_line_map
- \+ *lemma* open_segment_eq_image_line_map

Modified src/analysis/convex/topology.lean
- \+/\- *lemma* convex.is_path_connected
- \+/\- *lemma* convex.is_path_connected

Modified src/tactic/lint/type_classes.lean



## [2021-12-03 06:35:10](https://github.com/leanprover-community/mathlib/commit/8915dc8)
feat(ring_theory/polynomial/cyclotomic): `is_root_cyclotomic_iff` ([#10422](https://github.com/leanprover-community/mathlib/pull/10422))
From the flt-regular project.
#### Estimated changes
Modified src/number_theory/primes_congruent_one.lean

Modified src/ring_theory/polynomial/cyclotomic.lean
- \+ *lemma* _root_.is_root_of_unity_iff
- \+ *lemma* is_root_cyclotomic_iff
- \- *lemma* order_of_root_cyclotomic_eq



## [2021-12-03 05:24:46](https://github.com/leanprover-community/mathlib/commit/6f745cd)
feat(category_theory/limits): Lemmas about preserving pullbacks ([#10438](https://github.com/leanprover-community/mathlib/pull/10438))
#### Estimated changes
Modified src/category_theory/limits/preserves/shapes/pullbacks.lean
- \+ *lemma* preserves_pullback.iso_hom_fst
- \+ *lemma* preserves_pullback.iso_hom_snd
- \+ *lemma* preserves_pullback.iso_inv_fst
- \+ *lemma* preserves_pullback.iso_inv_snd
- \+ *lemma* preserves_pushout.iso_hom
- \+ *lemma* preserves_pushout.inl_iso_hom
- \+ *lemma* preserves_pushout.inr_iso_hom
- \+ *lemma* preserves_pushout.inl_iso_inv
- \+ *lemma* preserves_pushout.inr_iso_inv
- \+ *def* preserves_pullback_symmetry
- \+ *def* is_colimit_map_cocone_pushout_cocone_equiv
- \+ *def* is_colimit_pushout_cocone_map_of_is_colimit
- \+ *def* is_colimit_of_is_colimit_pushout_cocone_map
- \+ *def* is_colimit_of_has_pushout_of_preserves_colimit
- \+ *def* preserves_pushout.of_iso_comparison
- \+ *def* preserves_pushout_symmetry
- \+ *def* preserves_pushout.iso

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* inl_comp_pushout_comparison
- \+ *lemma* inr_comp_pushout_comparison
- \+ *lemma* pushout_comparison_map_desc
- \+ *def* pullback_cone.iso_mk
- \+ *def* pushout_cocone.iso_mk
- \+ *def* pushout_comparison



## [2021-12-02 23:23:50](https://github.com/leanprover-community/mathlib/commit/c791747)
feat(algebra/tropical/basic): various API ([#10487](https://github.com/leanprover-community/mathlib/pull/10487))
Generalize some order instance to just require `has_le` of the base `R`.
`(un)trop_monotone`
`trop_(min|inf)`
iffs between addition and order
`tropical.add_comm_monoid` (in parallel to [#10486](https://github.com/leanprover-community/mathlib/pull/10486))
`(co|contra)variant` instances
#### Estimated changes
Modified src/algebra/tropical/basic.lean
- \+/\- *lemma* untrop_le_iff
- \+ *lemma* untrop_lt_iff
- \+ *lemma* trop_monotone
- \+ *lemma* untrop_monotone
- \+/\- *lemma* le_zero
- \+ *lemma* trop_min
- \+ *lemma* trop_inf
- \+ *lemma* add_eq_left_iff
- \+ *lemma* add_eq_right_iff
- \+ *lemma* trop_add
- \+ *lemma* trop_zero
- \+/\- *lemma* untrop_one
- \+ *lemma* untrop_zpow
- \+ *lemma* trop_zsmul
- \+/\- *lemma* succ_nsmul
- \+/\- *lemma* untrop_le_iff
- \+/\- *lemma* le_zero
- \+/\- *lemma* untrop_one
- \+/\- *lemma* succ_nsmul



## [2021-12-02 22:04:36](https://github.com/leanprover-community/mathlib/commit/ac76745)
feat(data/finsupp/basic): add `finsupp.prod_congr` and `sum_congr` ([#10568](https://github.com/leanprover-community/mathlib/pull/10568))
These are the counterparts for `finsupp` of a simpler form of `finset.prod_congr`
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* prod_congr



## [2021-12-02 20:44:25](https://github.com/leanprover-community/mathlib/commit/42d3cbc)
feat(data/finsupp/basic): add `nat.cast_finsupp_prod` and 3 others ([#10579](https://github.com/leanprover-community/mathlib/pull/10579))
Add counterparts for `finsupp` of `nat.cast_prod` etc., as discussed in this thread https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/push_cast
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* cast_finsupp_prod
- \+ *lemma* cast_finsupp_sum
- \+ *lemma* cast_finsupp_prod
- \+ *lemma* cast_finsupp_sum



## [2021-12-02 19:28:48](https://github.com/leanprover-community/mathlib/commit/4cfe637)
chore(category_theory/sites/*): Adjust some `simp` lemmas. ([#10574](https://github.com/leanprover-community/mathlib/pull/10574))
The primary change is removing some `simp` tags from the definition of `sheafify` and friends, so that the sheafification related constructions are not unfolded to the `plus` constructions.
Also -- added coercion from Sheaves to presheaves, and some `rfl` simp lemmas which help some proofs move along.
Some proofs cleaned up as well.
#### Estimated changes
Modified src/category_theory/sites/adjunction.lean
- \+ *lemma* adjunction_to_types_hom_equiv_symm_apply
- \- *lemma* adjunction_to_types_hom_equiv_symm_apply'

Modified src/category_theory/sites/compatible_plus.lean

Modified src/category_theory/sites/compatible_sheafification.lean

Modified src/category_theory/sites/cover_preserving.lean

Modified src/category_theory/sites/limits.lean

Modified src/category_theory/sites/plus.lean
- \+ *lemma* iso_to_plus_hom
- \+ *lemma* iso_to_plus_inv
- \+ *lemma* plus_map_plus_lift

Modified src/category_theory/sites/sheaf.lean
- \+ *lemma* id_app
- \+ *lemma* comp_app
- \+ *lemma* Sheaf_to_presheaf_obj

Modified src/category_theory/sites/sheaf_of_types.lean
- \+ *lemma* id_app
- \+ *lemma* comp_app
- \+ *lemma* SheafOfTypes_to_presheaf_obj

Modified src/category_theory/sites/sheafification.lean
- \+ *lemma* sheafify_map_id
- \+ *lemma* sheafify_map_comp
- \+ *lemma* to_sheafify_naturality
- \+ *lemma* sheafification_map
- \+ *lemma* iso_sheafify_hom
- \+ *lemma* iso_sheafify_inv
- \+ *lemma* sheafify_map_sheafify_lift
- \+ *lemma* sheafification_adjunction_unit_app
- \- *lemma* sheafification_map_sheafify_lift
- \+ *def* sheafify_map

Modified src/category_theory/sites/whiskering.lean
- \- *lemma* Sheaf_compose_obj_to_presheaf
- \- *lemma* Sheaf_compose_map_to_presheaf
- \- *lemma* Sheaf_compose_map_app
- \- *lemma* Sheaf_compose_map_app_app
- \- *lemma* Sheaf_compose_map_id
- \- *lemma* Sheaf_compose_map_comp
- \- *def* Sheaf_compose_map

Modified src/topology/sheaves/sheaf.lean
- \+ *lemma* id_app
- \+ *lemma* comp_app

Modified src/topology/sheaves/sheaf_condition/sites.lean



## [2021-12-02 19:28:46](https://github.com/leanprover-community/mathlib/commit/cbb2d2c)
feat(data/nat/prime): Add lemma `count_factors_mul_of_pos` ([#10536](https://github.com/leanprover-community/mathlib/pull/10536))
Adding the counterpart to `count_factors_mul_of_coprime` for positive `a` and `b`
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* count_factors_mul_of_pos



## [2021-12-02 17:52:35](https://github.com/leanprover-community/mathlib/commit/38ae0c9)
feat(data/nat/prime): add coprime_of_prime lemmas ([#10534](https://github.com/leanprover-community/mathlib/pull/10534))
Adds `coprime_of_lt_prime` and `eq_or_coprime_of_le_prime`, which help one to prove a number is coprime to a prime. Spun off of [#9080](https://github.com/leanprover-community/mathlib/pull/9080).
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* coprime_of_lt_prime
- \+ *lemma* eq_or_coprime_of_le_prime



## [2021-12-02 14:23:28](https://github.com/leanprover-community/mathlib/commit/5e02292)
feat(data/finset/*): Diverse lemmas ([#10388](https://github.com/leanprover-community/mathlib/pull/10388))
A bunch of simple lemmas
#### Estimated changes
Modified src/analysis/box_integral/basic.lean

Modified src/data/finset/basic.lean
- \+ *lemma* subset_erase
- \+ *lemma* sdiff_erase
- \+ *lemma* filter_bUnion

Modified src/data/finset/lattice.lean
- \+ *lemma* sup_comm
- \+ *lemma* sup_sigma
- \+ *lemma* sup_product_left
- \+ *lemma* sup_product_right
- \+ *lemma* inf_comm
- \+ *lemma* inf_sigma
- \+ *lemma* inf_product_left
- \+ *lemma* inf_product_right

Modified src/data/finset/prod.lean
- \+ *lemma* coe_product
- \+ *lemma* product_eq_bUnion_right

Modified src/data/fintype/basic.lean
- \+/\- *lemma* univ_eq_empty
- \+/\- *lemma* univ_unique
- \+ *lemma* univ_option
- \+/\- *lemma* univ_eq_empty
- \+/\- *lemma* univ_unique
- \- *lemma* univ_is_empty

Modified src/data/nat/interval.lean
- \+ *lemma* range_add_eq_union

Modified src/data/set/basic.lean
- \+ *lemma* univ_unique

Modified src/geometry/euclidean/monge_point.lean

Modified src/linear_algebra/basis.lean



## [2021-12-02 14:23:27](https://github.com/leanprover-community/mathlib/commit/790d637)
feat(combinatorics/set_family/compression/uv): UV-compression of a set family ([#10238](https://github.com/leanprover-community/mathlib/pull/10238))
This defines the UV-compression of a set family, along with a bunch of preliminary definitions and some basic results.
#### Estimated changes
Created src/combinatorics/set_family/compression/uv.lean
- \+ *lemma* sup_sdiff_inj_on
- \+ *lemma* compress_of_disjoint_of_le
- \+ *lemma* mem_compression
- \+ *lemma* compress_self
- \+ *lemma* compression_self
- \+ *lemma* is_compressed_self
- \+ *lemma* compress_disjoint
- \+ *lemma* compress_idem
- \+ *lemma* compress_mem_compression
- \+ *lemma* compress_mem_compression_of_mem_compression
- \+ *lemma* compression_idem
- \+ *lemma* card_compression
- \+ *lemma* sup_sdiff_mem_of_mem_compression
- \+ *lemma* mem_of_mem_compression
- \+ *lemma* card_compress
- \+ *def* compress
- \+ *def* compression
- \+ *def* is_compressed

Modified src/order/boolean_algebra.lean
- \+ *lemma* le_sdiff_iff



## [2021-12-02 12:47:03](https://github.com/leanprover-community/mathlib/commit/17c2209)
feat(probability_theory/stopping): define filtration and stopping time ([#10553](https://github.com/leanprover-community/mathlib/pull/10553))
This PR defines filtrations and stopping times which are used in stochastic processes. This is the first step towards creating a theory of martingales in lean.
#### Estimated changes
Modified src/measure_theory/measurable_space_def.lean
- \+ *lemma* measurable.le

Created src/probability_theory/stopping.lean
- \+ *lemma* measurable_set_of_filtration
- \+ *lemma* add
- \+ *lemma* neg
- \+ *lemma* smul
- \+ *lemma* adapted_zero
- \+ *lemma* adapted_natural
- \+ *lemma* is_stopping_time.measurable_set_eq
- \+ *lemma* is_stopping_time.measurable_set_eq_le
- \+ *lemma* is_stopping_time_of_measurable_set_eq
- \+ *lemma* is_stopping_time_const
- \+ *lemma* max
- \+ *lemma* min
- \+ *lemma* add_const
- \+ *lemma* measurable_set
- \+ *lemma* measurable_space_mono
- \+ *lemma* measurable_space_le
- \+ *lemma* measurable_set_eq_const
- \+ *lemma* measurable
- \+ *def* const_filtration
- \+ *def* adapted
- \+ *def* natural
- \+ *def* is_stopping_time
- \+ *def* measurable_space



## [2021-12-02 12:47:02](https://github.com/leanprover-community/mathlib/commit/6806050)
feat(category_theory/sites/adjunction): Adjunctions between categories of sheaves. ([#10541](https://github.com/leanprover-community/mathlib/pull/10541))
We construct adjunctions between categories of sheaves obtained by composition (and sheafification) with functors which form a given adjunction.
Will be used in LTE.
#### Estimated changes
Created src/category_theory/sites/adjunction.lean
- \+ *lemma* adjunction_hom_equiv_apply
- \+ *lemma* adjunction_hom_equiv_symm_apply
- \+ *lemma* adjunction_unit_app
- \+ *lemma* adjunction_counit_app
- \+ *lemma* adjunction_to_types_hom_equiv_apply
- \+ *lemma* adjunction_to_types_hom_equiv_symm_apply'
- \+ *lemma* adjunction_to_types_unit_app
- \+ *lemma* adjunction_to_types_counit_app
- \+ *def* compose_equiv
- \+ *def* adjunction
- \+ *def* adjunction_to_types



## [2021-12-02 12:47:00](https://github.com/leanprover-community/mathlib/commit/3e72feb)
feat(ring_theory/localization): The localization of a localization is a localization. ([#10456](https://github.com/leanprover-community/mathlib/pull/10456))
Also provides an easy consequence : the map of `Spec M⁻¹R ⟶ Spec R` is isomorphic on stalks.
#### Estimated changes
Modified src/algebraic_geometry/Spec.lean
- \+ *lemma* Spec_map_localization_is_iso

Modified src/ring_theory/localization.lean
- \+ *lemma* mem_localization_localization_submodule
- \+ *lemma* localization_localization_map_units
- \+ *lemma* localization_localization_surj
- \+ *lemma* localization_localization_eq_iff_exists
- \+ *lemma* localization_localization_is_localization
- \+ *lemma* localization_localization_is_localization_of_has_all_units
- \+ *lemma* is_localization_is_localization_at_prime_is_localization
- \+ *def* localization_localization_submodule
- \+ *def* localization_localization_at_prime_iso_localization



## [2021-12-02 11:02:49](https://github.com/leanprover-community/mathlib/commit/fed2929)
chore(*): golf some proofs ([#10575](https://github.com/leanprover-community/mathlib/pull/10575))
Also add `strict_mono_on.monotone_on` and `strict_anti_on.antitone_on`.
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean

Modified src/order/monotone.lean

Modified src/order/rel_iso.lean



## [2021-12-02 05:21:48](https://github.com/leanprover-community/mathlib/commit/665c13a)
chore(*): clean up/golf proofs with unneeded or case splits ([#10569](https://github.com/leanprover-community/mathlib/pull/10569))
Golf/simplify/clean up some more proofs with unnecessary case splits, this time found by linting for `or.dcases_on` with branches proving the more general fact.
#### Estimated changes
Modified src/analysis/normed_space/bounded_linear_maps.lean

Modified src/analysis/normed_space/units.lean

Modified src/data/matrix/basis.lean

Modified src/data/nat/log.lean

Modified src/data/ordmap/ordset.lean

Modified src/data/rat/order.lean

Modified src/data/rbtree/insert.lean

Modified src/data/real/ennreal.lean

Modified src/linear_algebra/matrix/adjugate.lean

Modified src/linear_algebra/matrix/zpow.lean

Modified src/measure_theory/measure/measure_space.lean

Modified src/number_theory/primorial.lean

Modified src/number_theory/pythagorean_triples.lean



## [2021-12-02 03:37:51](https://github.com/leanprover-community/mathlib/commit/34758d3)
doc(group_theory/index): add a theorem name and fix a to_additive ([#10564](https://github.com/leanprover-community/mathlib/pull/10564))
I wanted to find the theorem I know as "Lagrange's theorem" but couldn't by searching.
This PR adds the name Lagrange's theorem to the relevant file, and also fixes an extra eager `to_additive` renaming that creates a lemma `add_subgroup.index_add_card` which talks about multiplication previously.
#### Estimated changes
Modified src/group_theory/index.lean
- \+/\- *lemma* index_mul_card
- \+/\- *lemma* index_mul_card



## [2021-12-02 03:37:50](https://github.com/leanprover-community/mathlib/commit/7043521)
chore(algebra/order/*): drop some `[nontrivial _]` assumptions ([#10550](https://github.com/leanprover-community/mathlib/pull/10550))
Use `pullback_nonzero` to deduce `nontrivial _` in some `function.injective.*` constructors.
#### Estimated changes
Modified src/algebra/order/field.lean

Modified src/algebra/order/ring.lean



## [2021-12-02 03:37:49](https://github.com/leanprover-community/mathlib/commit/0f12400)
chore(*): more cleanups of by_cases ([#10549](https://github.com/leanprover-community/mathlib/pull/10549))
Follow up  [#10523](https://github.com/leanprover-community/mathlib/pull/10523) with more tool-assisted golfing, see that PR for details.
#### Estimated changes
Modified src/data/dfinsupp.lean

Modified src/data/multiset/pi.lean

Modified src/data/polynomial/div.lean

Modified src/group_theory/perm/cycles.lean

Modified src/group_theory/perm/support.lean

Modified src/measure_theory/function/conditional_expectation.lean

Modified src/number_theory/padics/padic_integers.lean

Modified src/number_theory/padics/ring_homs.lean

Modified src/probability_theory/density.lean

Modified src/ring_theory/power_basis.lean



## [2021-12-01 17:04:54](https://github.com/leanprover-community/mathlib/commit/c09501d)
feat(*): assorted `finset` lemmas ([#10566](https://github.com/leanprover-community/mathlib/pull/10566))
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+ *lemma* one_lt_prod
- \+ *lemma* prod_lt_one

Modified src/data/finset/basic.lean
- \+ *lemma* range_sdiff_zero



## [2021-12-01 11:46:33](https://github.com/leanprover-community/mathlib/commit/cc60470)
feat(data/nat/prime): Add lemma `factors_count_pow` ([#10554](https://github.com/leanprover-community/mathlib/pull/10554))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* factors_count_pow



## [2021-12-01 03:17:51](https://github.com/leanprover-community/mathlib/commit/599a511)
feat(analysis/normed_space/star and data/complex/is_R_or_C): register instances of `cstar_ring` ([#10555](https://github.com/leanprover-community/mathlib/pull/10555))
Register instances `cstar_ring ℝ` and `cstar_ring K` when `[is_R_or_C K]`
#### Estimated changes
Modified src/analysis/normed_space/star.lean

Modified src/data/complex/is_R_or_C.lean



## [2021-12-01 02:41:28](https://github.com/leanprover-community/mathlib/commit/3f7d0cf)
chore(scripts): update nolints.txt ([#10563](https://github.com/leanprover-community/mathlib/pull/10563))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt

