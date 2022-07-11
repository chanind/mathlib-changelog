## [2021-05-31 21:08:06](https://github.com/leanprover-community/mathlib/commit/bec3e59)
feat(data/finset): provide the coercion `finset α → Type*` ([#7575](https://github.com/leanprover-community/mathlib/pull/7575))
There doesn't seem to be a good reason that `finset` doesn't have a `coe_to_sort` like `set` does. Before the change in this PR, we had to suffer the inconvenience of writing `(↑s : set _)` whenever we want the subtype of all elements of `s`. Now you can just write `s`.
I removed the obvious instances of the `((↑s : set _) : Type*)` pattern, although it definitely remains in some places. I'd rather do those in separate PRs since it does not really do any harm except for being annoying to type. There are also some parts of the API (`polynomial.root_set` stands out to me) that could be designed around the use of `finset`s rather than `set`s that are later proved to be finite, which I again would like to declare out of scope.
#### Estimated changes
Modified archive/100-theorems-list/16_abel_ruffini.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/combinatorics/hall.lean


Modified src/data/finset/basic.lean
- \+ *lemma* coe_sort_coe
- \+ *lemma* apply_coe_mem_map

Modified src/data/finset/sort.lean
- \+/\- *lemma* order_iso_of_fin_symm_apply
- \+/\- *def* order_iso_of_fin

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.univ_eq_attach

Modified src/data/set/finite.lean
- \+ *lemma* finite.coe_sort_to_finset

Modified src/field_theory/finiteness.lean
- \+ *lemma* coe_sort_finset_basis_index

Modified src/field_theory/polynomial_galois_group.lean


Modified src/field_theory/separable.lean


Modified src/geometry/euclidean/monge_point.lean


Modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* vector_span_eq_span_vsub_finset_right_ne

Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* of_finset_basis
- \+ *lemma* finrank_span_finset_le_card
- \+ *lemma* finrank_span_finset_eq_card

Modified src/linear_algebra/lagrange.lean
- \+/\- *def* linterpolate
- \+/\- *def* fun_equiv_degree_lt

Modified src/set_theory/cardinal.lean
- \+/\- *lemma* finset_card

Modified src/topology/separation.lean




## [2021-05-31 21:08:05](https://github.com/leanprover-community/mathlib/commit/ca740b6)
feat(data/finset/powerset): ssubsets and decidability ([#7543](https://github.com/leanprover-community/mathlib/pull/7543))
A few more little additions to finset-world that I found useful.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* ssubset_iff_subset_ne

Modified src/data/finset/powerset.lean
- \+ *lemma* mem_ssubsets
- \+ *lemma* empty_mem_ssubsets
- \+ *def* decidable_exists_of_decidable_subsets'
- \+ *def* decidable_forall_of_decidable_subsets'
- \+ *def* ssubsets
- \+ *def* decidable_exists_of_decidable_ssubsets'
- \+ *def* decidable_forall_of_decidable_ssubsets'



## [2021-05-31 17:20:15](https://github.com/leanprover-community/mathlib/commit/d272343)
chore(order/lexicographic): add module docstring ([#7768](https://github.com/leanprover-community/mathlib/pull/7768))
add module docstring
#### Estimated changes
Modified src/order/lexicographic.lean




## [2021-05-31 17:20:14](https://github.com/leanprover-community/mathlib/commit/033a131)
chore(order/zorn): add module docstring ([#7767](https://github.com/leanprover-community/mathlib/pull/7767))
add module docstring, tidy up notation a bit
#### Estimated changes
Modified src/order/zorn.lean
- \+ *lemma* chain.total_of_refl
- \+ *lemma* chain.mono
- \+ *lemma* chain.directed_on
- \+ *lemma* chain_insert
- \+ *lemma* succ_spec
- \+ *lemma* chain_succ
- \+ *lemma* super_of_not_max
- \+ *lemma* succ_increasing
- \+ *lemma* chain_closure_empty
- \+ *lemma* chain_closure_closure
- \+ *lemma* chain_closure_total
- \+ *lemma* chain_closure_succ_fixpoint
- \+ *lemma* chain_closure_succ_fixpoint_iff
- \+ *lemma* chain_chain_closure
- \+ *lemma* chain.symm
- \+ *lemma* chain.total
- \+ *lemma* chain.image
- \+ *lemma* directed_of_chain
- \- *theorem* chain.total_of_refl
- \- *theorem* chain.mono
- \- *theorem* chain.directed_on
- \- *theorem* chain_insert
- \- *theorem* succ_spec
- \- *theorem* chain_succ
- \- *theorem* super_of_not_max
- \- *theorem* succ_increasing
- \- *theorem* chain_closure_empty
- \- *theorem* chain_closure_closure
- \- *theorem* chain_closure_total
- \- *theorem* chain_closure_succ_fixpoint
- \- *theorem* chain_closure_succ_fixpoint_iff
- \- *theorem* chain_chain_closure
- \- *theorem* chain.symm
- \- *theorem* chain.total
- \- *theorem* chain.image
- \- *theorem* directed_of_chain



## [2021-05-31 15:49:23](https://github.com/leanprover-community/mathlib/commit/d0ebc8e)
feat(ring_theory/laurent_series): Defines Laurent series and their localization map ([#7604](https://github.com/leanprover-community/mathlib/pull/7604))
Defines `laurent_series` as an abbreviation of `hahn_series Z`
Defines `laurent_series.power_series_part`
Shows that the map from power series to Laurent series is a `localization_map`.
#### Estimated changes
Modified src/ring_theory/hahn_series.lean
- \+ *lemma* of_power_series_injective
- \+ *lemma* of_power_series_apply
- \+ *lemma* of_power_series_apply_coeff
- \+/\- *def* of_power_series

Created src/ring_theory/laurent_series.lean
- \+ *lemma* coe_power_series
- \+ *lemma* coeff_coe_power_series
- \+ *lemma* power_series_part_coeff
- \+ *lemma* power_series_part_zero
- \+ *lemma* power_series_part_eq_zero
- \+ *lemma* single_order_mul_power_series_part
- \+ *lemma* of_power_series_power_series_part
- \+ *lemma* of_power_series_X
- \+ *lemma* of_power_series_X_pow
- \+ *def* power_series_part
- \+ *def* of_power_series_localization



## [2021-05-31 14:35:07](https://github.com/leanprover-community/mathlib/commit/4555798)
feat(topology/semicontinuous): semicontinuity of compositions ([#7763](https://github.com/leanprover-community/mathlib/pull/7763))
#### Estimated changes
Modified src/topology/semicontinuous.lean
- \+ *lemma* continuous_at.comp_lower_semicontinuous_within_at
- \+ *lemma* continuous_at.comp_lower_semicontinuous_at
- \+ *lemma* continuous.comp_lower_semicontinuous_on
- \+ *lemma* continuous.comp_lower_semicontinuous
- \+ *lemma* continuous_at.comp_lower_semicontinuous_within_at_antimono
- \+ *lemma* continuous_at.comp_lower_semicontinuous_at_antimono
- \+ *lemma* continuous.comp_lower_semicontinuous_on_antimono
- \+ *lemma* continuous.comp_lower_semicontinuous_antimono
- \+ *lemma* continuous_at.comp_upper_semicontinuous_within_at
- \+ *lemma* continuous_at.comp_upper_semicontinuous_at
- \+ *lemma* continuous.comp_upper_semicontinuous_on
- \+ *lemma* continuous.comp_upper_semicontinuous
- \+ *lemma* continuous_at.comp_upper_semicontinuous_within_at_antimono
- \+ *lemma* continuous_at.comp_upper_semicontinuous_at_antimono
- \+ *lemma* continuous.comp_upper_semicontinuous_on_antimono
- \+ *lemma* continuous.comp_upper_semicontinuous_antimono
- \+/\- *def* upper_semicontinuous_within_at
- \+/\- *def* upper_semicontinuous_on
- \+/\- *def* upper_semicontinuous_at
- \+/\- *def* upper_semicontinuous



## [2021-05-31 13:18:14](https://github.com/leanprover-community/mathlib/commit/2af6912)
feat(linear_algebra): the determinant of an endomorphism ([#7635](https://github.com/leanprover-community/mathlib/pull/7635))
 `linear_map.det` is the determinant of an endomorphism, which is defined independent of a basis. If there is no finite basis, the determinant is defined to be equal to `1`.
This approach is inspired by `linear_map.trace`.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/linear_algebra/determinant.lean
- \+ *lemma* det_to_matrix_eq_det_to_matrix
- \+ *lemma* det_aux_def
- \+ *lemma* det_aux_def'
- \+ *lemma* det_aux_id
- \+ *lemma* det_aux_comp
- \+ *lemma* coe_det
- \+ *lemma* det_eq_det_to_matrix_of_finite_set
- \+ *lemma* det_to_matrix
- \+ *lemma* det_comp
- \+ *lemma* det_id
- \+ *lemma* det_zero
- \+ *def* det_aux



## [2021-05-31 13:18:13](https://github.com/leanprover-community/mathlib/commit/7fe456d)
feat(algebra/homology): projective resolutions ([#7486](https://github.com/leanprover-community/mathlib/pull/7486))
# Projective resolutions
A projective resolution `P : ProjectiveResolution Z` of an object `Z : C` consists of
a `ℕ`-indexed chain complex `P.complex` of projective objects,
along with a chain map `P.π` from `C` to the chain complex consisting just of `Z` in degree zero,
so that the augmented chain complex is exact.
When `C` is abelian, this exactness condition is equivalent to `π` being a quasi-isomorphism.
It turns out that this formulation allows us to set up the basic theory derived functors
without even assuming `C` is abelian.
(Typically, however, to show `has_projective_resolutions C`
one will assume `enough_projectives C` and `abelian C`.
This construction appears in `category_theory.abelian.projectives`.)
We show that give `P : ProjectiveResolution X` and `Q : ProjectiveResolution Y`,
any morphism `X ⟶ Y` admits a lift to a chain map `P.complex ⟶ Q.complex`.
(It is a lift in the sense that
the projection maps `P.π` and `Q.π` intertwine the lift and the original morphism.)
Moreover, we show that any two such lifts are homotopic.
As a consequence, if every object admits a projective resolution,
we can construct a functor `projective_resolutions C : C ⥤ homotopy_category C`.
#### Estimated changes
Created src/category_theory/preadditive/projective_resolution.lean
- \+ *lemma* π_f_succ
- \+ *lemma* lift_f_one_zero_comm
- \+ *lemma* lift_commutes
- \+ *lemma* homotopy_equiv_hom_π
- \+ *lemma* homotopy_equiv_inv_π
- \+ *def* self
- \+ *def* lift_f_zero
- \+ *def* lift_f_one
- \+ *def* lift_f_succ
- \+ *def* lift
- \+ *def* lift_homotopy_zero_zero
- \+ *def* lift_homotopy_zero_one
- \+ *def* lift_homotopy_zero_succ
- \+ *def* lift_homotopy_zero
- \+ *def* lift_homotopy
- \+ *def* lift_id_homotopy
- \+ *def* lift_comp_homotopy
- \+ *def* homotopy_equiv
- \+ *def* projective_resolutions



## [2021-05-31 06:45:22](https://github.com/leanprover-community/mathlib/commit/1a92c0d)
feat(order/basic): add simp attribute on le_refl, zero_le_one and zero_lt_one ([#7733](https://github.com/leanprover-community/mathlib/pull/7733))
These ones show up so often that they would have deserved a simp attribute long ago.
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* zero_le_one
- \+/\- *lemma* zero_lt_one

Modified src/analysis/complex/isometry.lean


Modified src/data/complex/basic.lean


Modified src/data/real/golden_ratio.lean


Modified src/geometry/euclidean/basic.lean


Modified src/order/basic.lean


Modified src/testing/slim_check/sampleable.lean


Modified src/topology/path_connected.lean
- \+/\- *lemma* extend_zero
- \+/\- *lemma* extend_one

Modified src/topology/unit_interval.lean
- \+ *lemma* mk_zero
- \+ *lemma* mk_one

Modified test/nontriviality.lean




## [2021-05-30 21:09:58](https://github.com/leanprover-community/mathlib/commit/fd48ac5)
chore(data/list): extract sublists to a separate file ([#7757](https://github.com/leanprover-community/mathlib/pull/7757))
Minor splitting in `data/list/basic`, splitting out `sublists` to its own file, thereby delaying importing `data.nat.choose` in the `list` development.
#### Estimated changes
Modified src/data/list/basic.lean
- \- *lemma* sublists_len_aux_append
- \- *lemma* sublists_len_aux_eq
- \- *lemma* sublists_len_aux_zero
- \- *lemma* sublists_len_zero
- \- *lemma* sublists_len_succ_nil
- \- *lemma* sublists_len_succ_cons
- \- *lemma* length_sublists_len
- \- *lemma* sublists_len_sublist_sublists'
- \- *lemma* sublists_len_sublist_of_sublist
- \- *lemma* length_of_sublists_len
- \- *lemma* mem_sublists_len_self
- \- *lemma* mem_sublists_len
- \- *theorem* sublists'_nil
- \- *theorem* sublists'_singleton
- \- *theorem* map_sublists'_aux
- \- *theorem* sublists'_aux_append
- \- *theorem* sublists'_aux_eq_sublists'
- \- *theorem* sublists'_cons
- \- *theorem* mem_sublists'
- \- *theorem* length_sublists'
- \- *theorem* sublists_nil
- \- *theorem* sublists_singleton
- \- *theorem* sublists_aux₁_eq_sublists_aux
- \- *theorem* sublists_aux_cons_eq_sublists_aux₁
- \- *theorem* sublists_aux_eq_foldr.aux
- \- *theorem* sublists_aux_eq_foldr
- \- *theorem* sublists_aux_cons_cons
- \- *theorem* sublists_aux₁_append
- \- *theorem* sublists_aux₁_concat
- \- *theorem* sublists_aux₁_bind
- \- *theorem* sublists_aux_cons_append
- \- *theorem* sublists_append
- \- *theorem* sublists_concat
- \- *theorem* sublists_reverse
- \- *theorem* sublists_eq_sublists'
- \- *theorem* sublists'_reverse
- \- *theorem* sublists'_eq_sublists
- \- *theorem* sublists_aux_ne_nil
- \- *theorem* mem_sublists
- \- *theorem* length_sublists
- \- *theorem* map_ret_sublist_sublists
- \- *def* sublists_len_aux
- \- *def* sublists_len

Modified src/data/list/pairwise.lean


Created src/data/list/sublists.lean
- \+ *lemma* sublists_len_aux_append
- \+ *lemma* sublists_len_aux_eq
- \+ *lemma* sublists_len_aux_zero
- \+ *lemma* sublists_len_zero
- \+ *lemma* sublists_len_succ_nil
- \+ *lemma* sublists_len_succ_cons
- \+ *lemma* length_sublists_len
- \+ *lemma* sublists_len_sublist_sublists'
- \+ *lemma* sublists_len_sublist_of_sublist
- \+ *lemma* length_of_sublists_len
- \+ *lemma* mem_sublists_len_self
- \+ *lemma* mem_sublists_len
- \+ *theorem* sublists'_nil
- \+ *theorem* sublists'_singleton
- \+ *theorem* map_sublists'_aux
- \+ *theorem* sublists'_aux_append
- \+ *theorem* sublists'_aux_eq_sublists'
- \+ *theorem* sublists'_cons
- \+ *theorem* mem_sublists'
- \+ *theorem* length_sublists'
- \+ *theorem* sublists_nil
- \+ *theorem* sublists_singleton
- \+ *theorem* sublists_aux₁_eq_sublists_aux
- \+ *theorem* sublists_aux_cons_eq_sublists_aux₁
- \+ *theorem* sublists_aux_eq_foldr.aux
- \+ *theorem* sublists_aux_eq_foldr
- \+ *theorem* sublists_aux_cons_cons
- \+ *theorem* sublists_aux₁_append
- \+ *theorem* sublists_aux₁_concat
- \+ *theorem* sublists_aux₁_bind
- \+ *theorem* sublists_aux_cons_append
- \+ *theorem* sublists_append
- \+ *theorem* sublists_concat
- \+ *theorem* sublists_reverse
- \+ *theorem* sublists_eq_sublists'
- \+ *theorem* sublists'_reverse
- \+ *theorem* sublists'_eq_sublists
- \+ *theorem* sublists_aux_ne_nil
- \+ *theorem* mem_sublists
- \+ *theorem* length_sublists
- \+ *theorem* map_ret_sublist_sublists
- \+ *def* sublists_len_aux
- \+ *def* sublists_len



## [2021-05-30 21:09:57](https://github.com/leanprover-community/mathlib/commit/14b597c)
feat(analysis/normed_space): ∥n • a∥ ≤ n * ∥a∥ ([#7745](https://github.com/leanprover-community/mathlib/pull/7745))
From LTE.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_nsmul_le
- \+ *lemma* norm_gsmul_le
- \+ *lemma* nnnorm_nsmul_le
- \+ *lemma* nnnorm_gsmul_le



## [2021-05-30 19:15:46](https://github.com/leanprover-community/mathlib/commit/0d842f0)
fix(order/closure): unincorporated reviewer comments from [#7446](https://github.com/leanprover-community/mathlib/pull/7446) ([#7761](https://github.com/leanprover-community/mathlib/pull/7761))
#### Estimated changes
Modified src/analysis/convex/basic.lean


Modified src/order/closure.lean




## [2021-05-30 15:26:33](https://github.com/leanprover-community/mathlib/commit/33d803a)
refactor(convex/basic): make convex_hull into a closure operator ([#7446](https://github.com/leanprover-community/mathlib/pull/7446))
Bundle convex_hull as a closure operator, simplify duplicate proofs
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+/\- *def* convex_hull

Modified src/order/closure.lean




## [2021-05-30 09:54:50](https://github.com/leanprover-community/mathlib/commit/25e36be)
chore(data/fintype/basic): `fintype α/β` from `fintype α ⊕ β` ([#7736](https://github.com/leanprover-community/mathlib/pull/7736))
Also renaming the equivalent `α × β` versions, for consistency.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *def* fintype.prod_left
- \+ *def* fintype.prod_right
- \- *def* fintype.fintype_prod_left
- \- *def* fintype.fintype_prod_right

Modified src/group_theory/order_of_element.lean




## [2021-05-30 09:54:50](https://github.com/leanprover-community/mathlib/commit/4ea253b)
feat(measure_theory/integration): in a sigma finite space, there exists an integrable positive function ([#7721](https://github.com/leanprover-community/mathlib/pull/7721))
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+ *lemma* measurable.nnreal_tsum

Modified src/measure_theory/integration.lean
- \+ *lemma* exists_integrable_pos_of_sigma_finite

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* tsum_pos

Modified src/topology/instances/ennreal.lean
- \+ *lemma* tsum_eq_to_nnreal_tsum
- \+ *lemma* has_sum_lt
- \+ *lemma* has_sum_strict_mono
- \+ *lemma* tsum_lt_tsum
- \+ *lemma* tsum_strict_mono
- \+ *lemma* tsum_pos



## [2021-05-30 08:29:40](https://github.com/leanprover-community/mathlib/commit/8e25bb6)
feat(algebra/homology): complexes in functor categories ([#7744](https://github.com/leanprover-community/mathlib/pull/7744))
From LTE.
#### Estimated changes
Created src/algebra/homology/functor.lean
- \+ *def* as_functor
- \+ *def* complex_of_functors_to_functor_to_complex



## [2021-05-30 08:29:39](https://github.com/leanprover-community/mathlib/commit/f4d145e)
feat(algebra/homology): construct isomorphisms of complexes ([#7741](https://github.com/leanprover-community/mathlib/pull/7741))
From LTE.
#### Estimated changes
Modified src/algebra/homology/homological_complex.lean
- \+ *lemma* iso_of_components_app
- \+ *def* iso_app
- \+ *def* iso_of_components



## [2021-05-30 08:29:38](https://github.com/leanprover-community/mathlib/commit/08bb112)
chore(ring_theory/hahn_series): extract lemmas from slow definitions ([#7737](https://github.com/leanprover-community/mathlib/pull/7737))
This doesn't make them much faster, but it makes it easier to tell which bits are slow
#### Estimated changes
Modified src/ring_theory/hahn_series.lean
- \+ *lemma* emb_domain_add
- \+ *lemma* emb_domain_smul
- \+ *lemma* emb_domain_mul
- \+ *lemma* emb_domain_one
- \+/\- *def* emb_domain_linear_map



## [2021-05-30 04:33:33](https://github.com/leanprover-community/mathlib/commit/e2168e5)
feat(src/ring_theory/derivation): merge duplicates `derivation.comp` and `linear_map.comp_der` ([#7727](https://github.com/leanprover-community/mathlib/pull/7727))
I propose keeping the version introduced in [#7715](https://github.com/leanprover-community/mathlib/pull/7715) since it also contains
the statement that the push forward is linear, but moving it to the `linear_map`
namespace to enable dot notation.
Thanks to @Nicknamen for alerting me to the duplication: https://github.com/leanprover-community/mathlib/pull/7715#issuecomment-849192370
#### Estimated changes
Modified src/ring_theory/derivation.lean
- \- *lemma* comp_der_apply
- \+ *def* _root_.linear_map.comp_der
- \- *def* comp
- \- *def* comp_der



## [2021-05-30 04:33:32](https://github.com/leanprover-community/mathlib/commit/9d63c38)
feat(topology/continuous_function/algebra): add `coe_fn_(linear_map|ring_hom|alg_hom)` ([#7720](https://github.com/leanprover-community/mathlib/pull/7720))
#### Estimated changes
Modified src/topology/continuous_function/algebra.lean
- \+ *def* coe_fn_ring_hom
- \+ *def* coe_fn_linear_map
- \+ *def* continuous_map.coe_fn_alg_hom



## [2021-05-30 01:16:52](https://github.com/leanprover-community/mathlib/commit/a3ba4d4)
feat(algebra/homology): eval and forget functors ([#7742](https://github.com/leanprover-community/mathlib/pull/7742))
From LTE.
#### Estimated changes
Modified src/algebra/homology/additive.lean


Modified src/algebra/homology/differential_object.lean


Modified src/algebra/homology/homological_complex.lean
- \+ *def* eval
- \+ *def* forget
- \+ *def* forget_eval
- \- *def* eval_at

Modified src/category_theory/graded_object.lean
- \+ *def* eval



## [2021-05-29 18:15:17](https://github.com/leanprover-community/mathlib/commit/035aa60)
feat(analysis/normed_space): SemiNormedGroup.has_zero_object ([#7740](https://github.com/leanprover-community/mathlib/pull/7740))
From LTE.
#### Estimated changes
Modified src/analysis/normed_space/SemiNormedGroup.lean
- \+ *lemma* coe_comp
- \+ *lemma* zero_apply



## [2021-05-29 02:32:43](https://github.com/leanprover-community/mathlib/commit/1ac49b0)
chore(category_theory): dualize filtered categories to cofiltered categories ([#7731](https://github.com/leanprover-community/mathlib/pull/7731))
Per request on [zulip](https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/status.20update/near/240548989).
I have not attempted to dualize "filtered colimits commute with finite limits", as I've never heard of that being used.
#### Estimated changes
Modified src/category_theory/filtered.lean
- \+ *lemma* eq_condition
- \+ *lemma* inf_objs_exists
- \+ *lemma* inf_exists
- \+ *lemma* inf_to_commutes
- \+ *lemma* cone_nonempty
- \+ *lemma* of_left_adjoint
- \+ *lemma* of_is_left_adjoint
- \+ *lemma* of_equivalence
- \+ *def* inf
- \+ *def* inf_to



## [2021-05-28 19:12:47](https://github.com/leanprover-community/mathlib/commit/f74a375)
chore(linear_algebra/finsupp): remove useless lemma ([#7734](https://github.com/leanprover-community/mathlib/pull/7734))
The lemma is not used in mathlib, it's mathematically useless (you'd never have a surjective function from an indexing set to a module), and it's badly named, so I propose removing it entirely.
#### Estimated changes
Modified src/linear_algebra/finsupp.lean
- \- *theorem* total_range



## [2021-05-28 15:21:27](https://github.com/leanprover-community/mathlib/commit/13746fe)
feat(group_theory/subgroup linear_algebra/prod): add ker_prod_map ([#7729](https://github.com/leanprover-community/mathlib/pull/7729))
The kernel of the product of two `group_hom` is the product of the kernels (and similarly for monoids).
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* prod_map_comap_prod
- \+ *lemma* ker_prod_map

Modified src/linear_algebra/prod.lean
- \+ *lemma* prod_map_comap_prod
- \+ *lemma* ker_prod_map



## [2021-05-28 11:55:01](https://github.com/leanprover-community/mathlib/commit/5fff3b1)
feat(ring_theory/mv_polynomial/basic): add polynomial.basis_monomials ([#7728](https://github.com/leanprover-community/mathlib/pull/7728))
We add `polynomial.basis_monomials` : the monomials form a basis on `polynomial R`.
Because of the structure of the import, it seems to me a little complicated to do it directly, so I use `mv_polynomial.punit_alg_equiv`
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+/\- *def* equiv_fun_on_fintype

Modified src/data/polynomial/algebra_map.lean
- \+/\- *lemma* C_eq_algebra_map
- \+ *def* to_finsupp_iso_alg

Modified src/data/polynomial/basic.lean
- \+/\- *lemma* monomial_one_right_eq_X_pow

Modified src/data/polynomial/monomial.lean


Modified src/ring_theory/mv_polynomial/basic.lean
- \+ *lemma* coe_basis_monomials



## [2021-05-27 09:01:17](https://github.com/leanprover-community/mathlib/commit/5360e47)
feat(algebra/module/linear_map): `linear_(map|equiv).restrict_scalars` is injective ([#7725](https://github.com/leanprover-community/mathlib/pull/7725))
So as not to repeat them for the lemmas, I moved the typeclasses into a `variables` statement.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *lemma* restrict_scalars_injective
- \+ *lemma* restrict_scalars_inj
- \+/\- *def* restrict_scalars



## [2021-05-27 05:47:47](https://github.com/leanprover-community/mathlib/commit/6109558)
chore(category_theory/*): provide aliases quiver.hom.le and has_le.le.hom ([#7677](https://github.com/leanprover-community/mathlib/pull/7677))
#### Estimated changes
Modified src/algebra/category/Module/limits.lean


Modified src/category_theory/category/default.lean
- \+/\- *lemma* hom_of_le_refl
- \+/\- *lemma* le_of_hom_hom_of_le
- \+/\- *lemma* hom_of_le_le_of_hom

Modified src/category_theory/category/pairwise.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/functor.lean


Modified src/category_theory/isomorphism.lean
- \+/\- *lemma* iso.to_eq

Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/opposites.lean
- \+/\- *lemma* le_of_op_hom
- \+/\- *def* op_hom_of_le

Modified src/category_theory/sites/spaces.lean


Modified src/category_theory/skeletal.lean


Modified src/category_theory/subobject/basic.lean


Modified src/category_theory/subobject/lattice.lean


Modified src/category_theory/subobject/types.lean


Modified src/topology/category/Profinite/as_limit.lean


Modified src/topology/category/Top/limits.lean


Modified src/topology/category/Top/open_nhds.lean


Modified src/topology/category/Top/opens.lean
- \+/\- *def* inf_le_left
- \+/\- *def* inf_le_right
- \+/\- *def* le_supr
- \+/\- *def* bot_le
- \+/\- *def* le_top

Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean


Modified src/topology/sheaves/sheaf_condition/unique_gluing.lean




## [2021-05-27 00:46:29](https://github.com/leanprover-community/mathlib/commit/a85fbda)
feat(algebra/opposites): add units.op_equiv ([#7723](https://github.com/leanprover-community/mathlib/pull/7723))
#### Estimated changes
Modified src/algebra/opposites.lean
- \+ *lemma* units.coe_unop_op_equiv
- \+ *lemma* units.coe_op_equiv_symm
- \+ *def* units.op_equiv



## [2021-05-27 00:46:28](https://github.com/leanprover-community/mathlib/commit/20291d0)
feat(topology/semicontinuous): basics on lower and upper semicontinuous functions ([#7693](https://github.com/leanprover-community/mathlib/pull/7693))
We mimick the interface for continuity, by introducing predicates `lower_semicontinuous_within_at`, `lower_semicontinuous_at`, `lower_semicontinuous_on` and `lower_semicontinuous` (and similarly for upper semicontinuity).
#### Estimated changes
Modified src/algebra/ordered_monoid.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/constructions.lean
- \+ *lemma* mem_nhds_prod_iff'

Created src/topology/semicontinuous.lean
- \+ *lemma* lower_semicontinuous_within_at.mono
- \+ *lemma* lower_semicontinuous_within_at_univ_iff
- \+ *lemma* lower_semicontinuous_at.lower_semicontinuous_within_at
- \+ *lemma* lower_semicontinuous_on.lower_semicontinuous_within_at
- \+ *lemma* lower_semicontinuous_on.mono
- \+ *lemma* lower_semicontinuous_on_univ_iff
- \+ *lemma* lower_semicontinuous.lower_semicontinuous_at
- \+ *lemma* lower_semicontinuous.lower_semicontinuous_within_at
- \+ *lemma* lower_semicontinuous.lower_semicontinuous_on
- \+ *lemma* lower_semicontinuous_within_at_const
- \+ *lemma* lower_semicontinuous_at_const
- \+ *lemma* lower_semicontinuous_on_const
- \+ *lemma* lower_semicontinuous_const
- \+ *lemma* is_open.lower_semicontinuous_indicator
- \+ *lemma* is_open.lower_semicontinuous_on_indicator
- \+ *lemma* is_open.lower_semicontinuous_at_indicator
- \+ *lemma* is_open.lower_semicontinuous_within_at_indicator
- \+ *lemma* is_closed.lower_semicontinuous_indicator
- \+ *lemma* is_closed.lower_semicontinuous_on_indicator
- \+ *lemma* is_closed.lower_semicontinuous_at_indicator
- \+ *lemma* is_closed.lower_semicontinuous_within_at_indicator
- \+ *lemma* lower_semicontinuous.is_open_preimage
- \+ *lemma* continuous_within_at.lower_semicontinuous_within_at
- \+ *lemma* continuous_at.lower_semicontinuous_at
- \+ *lemma* continuous_on.lower_semicontinuous_on
- \+ *lemma* continuous.lower_semicontinuous
- \+ *lemma* lower_semicontinuous_within_at.add'
- \+ *lemma* lower_semicontinuous_at.add'
- \+ *lemma* lower_semicontinuous_on.add'
- \+ *lemma* lower_semicontinuous.add'
- \+ *lemma* lower_semicontinuous_within_at.add
- \+ *lemma* lower_semicontinuous_at.add
- \+ *lemma* lower_semicontinuous_on.add
- \+ *lemma* lower_semicontinuous.add
- \+ *lemma* lower_semicontinuous_within_at_sum
- \+ *lemma* lower_semicontinuous_at_sum
- \+ *lemma* lower_semicontinuous_on_sum
- \+ *lemma* lower_semicontinuous_sum
- \+ *lemma* lower_semicontinuous_within_at_supr
- \+ *lemma* lower_semicontinuous_within_at_bsupr
- \+ *lemma* lower_semicontinuous_at_supr
- \+ *lemma* lower_semicontinuous_at_bsupr
- \+ *lemma* lower_semicontinuous_on_supr
- \+ *lemma* lower_semicontinuous_on_bsupr
- \+ *lemma* lower_semicontinuous_supr
- \+ *lemma* lower_semicontinuous_bsupr
- \+ *lemma* lower_semicontinuous_within_at_tsum
- \+ *lemma* lower_semicontinuous_at_tsum
- \+ *lemma* lower_semicontinuous_on_tsum
- \+ *lemma* lower_semicontinuous_tsum
- \+ *lemma* upper_semicontinuous_within_at.mono
- \+ *lemma* upper_semicontinuous_within_at_univ_iff
- \+ *lemma* upper_semicontinuous_at.upper_semicontinuous_within_at
- \+ *lemma* upper_semicontinuous_on.upper_semicontinuous_within_at
- \+ *lemma* upper_semicontinuous_on.mono
- \+ *lemma* upper_semicontinuous_on_univ_iff
- \+ *lemma* upper_semicontinuous.upper_semicontinuous_at
- \+ *lemma* upper_semicontinuous.upper_semicontinuous_within_at
- \+ *lemma* upper_semicontinuous.upper_semicontinuous_on
- \+ *lemma* upper_semicontinuous_within_at_const
- \+ *lemma* upper_semicontinuous_at_const
- \+ *lemma* upper_semicontinuous_on_const
- \+ *lemma* upper_semicontinuous_const
- \+ *lemma* is_open.upper_semicontinuous_indicator
- \+ *lemma* is_open.upper_semicontinuous_on_indicator
- \+ *lemma* is_open.upper_semicontinuous_at_indicator
- \+ *lemma* is_open.upper_semicontinuous_within_at_indicator
- \+ *lemma* is_closed.upper_semicontinuous_indicator
- \+ *lemma* is_closed.upper_semicontinuous_on_indicator
- \+ *lemma* is_closed.upper_semicontinuous_at_indicator
- \+ *lemma* is_closed.upper_semicontinuous_within_at_indicator
- \+ *lemma* upper_semicontinuous.is_open_preimage
- \+ *lemma* continuous_within_at.upper_semicontinuous_within_at
- \+ *lemma* continuous_at.upper_semicontinuous_at
- \+ *lemma* continuous_on.upper_semicontinuous_on
- \+ *lemma* continuous.upper_semicontinuous
- \+ *lemma* upper_semicontinuous_within_at.add'
- \+ *lemma* upper_semicontinuous_at.add'
- \+ *lemma* upper_semicontinuous_on.add'
- \+ *lemma* upper_semicontinuous.add'
- \+ *lemma* upper_semicontinuous_within_at.add
- \+ *lemma* upper_semicontinuous_at.add
- \+ *lemma* upper_semicontinuous_on.add
- \+ *lemma* upper_semicontinuous.add
- \+ *lemma* upper_semicontinuous_within_at_sum
- \+ *lemma* upper_semicontinuous_at_sum
- \+ *lemma* upper_semicontinuous_on_sum
- \+ *lemma* upper_semicontinuous_sum
- \+ *lemma* upper_semicontinuous_within_at_infi
- \+ *lemma* upper_semicontinuous_within_at_binfi
- \+ *lemma* upper_semicontinuous_at_infi
- \+ *lemma* upper_semicontinuous_at_binfi
- \+ *lemma* upper_semicontinuous_on_infi
- \+ *lemma* upper_semicontinuous_on_binfi
- \+ *lemma* upper_semicontinuous_infi
- \+ *lemma* upper_semicontinuous_binfi
- \+ *lemma* continuous_within_at_iff_lower_upper_semicontinuous_within_at
- \+ *lemma* continuous_at_iff_lower_upper_semicontinuous_at
- \+ *lemma* continuous_on_iff_lower_upper_semicontinuous_on
- \+ *lemma* continuous_iff_lower_upper_semicontinuous
- \+ *theorem* lower_semicontinuous_iff_is_open
- \+ *theorem* upper_semicontinuous_iff_is_open
- \+ *def* lower_semicontinuous_within_at
- \+ *def* lower_semicontinuous_on
- \+ *def* lower_semicontinuous_at
- \+ *def* lower_semicontinuous
- \+ *def* upper_semicontinuous_within_at
- \+ *def* upper_semicontinuous_on
- \+ *def* upper_semicontinuous_at
- \+ *def* upper_semicontinuous



## [2021-05-26 21:50:17](https://github.com/leanprover-community/mathlib/commit/0970fda)
feat(measure_theory/regular): more material on regular measures ([#7680](https://github.com/leanprover-community/mathlib/pull/7680))
This PR:
* defines weakly regular measures
* shows that for weakly regular measures any finite measure set can be approximated from inside by closed sets
* shows that for regular measures any finite measure set can be approximated from inside by compact sets
* shows that any finite measure on a metric space is weakly regular
* shows that any locally finite measure on a sigma compact locally compact metric space is regular
#### Estimated changes
Modified docs/references.bib


Modified src/analysis/specific_limits.lean
- \+ *theorem* exists_pos_sum_of_encodable'

Modified src/measure_theory/regular.lean
- \+ *lemma* _root_.measurable_set.measure_eq_infi_is_open'
- \+ *lemma* _root_.measurable_set.exists_is_open_lt_of_lt'
- \+ *lemma* _root_.is_open.measure_eq_supr_is_compact
- \+ *lemma* _root_.is_open.exists_lt_is_compact
- \+ *lemma* _root_.measurable_set.measure_eq_infi_is_open
- \+ *lemma* _root_.measurable_set.exists_is_open_lt_of_lt
- \+ *lemma* _root_.is_open.measure_eq_supr_is_closed
- \+ *lemma* _root_.is_open.exists_lt_is_closed_of_gt
- \+ *lemma* exists_subset_is_open_measure_lt_top
- \+ *lemma* exists_closed_subset_self_subset_open_of_pos
- \+ *lemma* restrict_of_is_open
- \+ *lemma* _root_.measurable_set.measure_eq_supr_is_closed_of_finite_measure
- \+ *lemma* _root_.measurable_set.measure_eq_supr_is_closed_of_lt_top
- \+ *lemma* _root_.measurable_set.exists_lt_is_closed_of_lt_top
- \+ *lemma* _root_.measurable_set.exists_lt_is_closed_of_lt_top_of_pos
- \+ *lemma* restrict_of_measurable_set
- \+ *lemma* inner_regular_of_pseudo_emetric_space
- \+ *lemma* _root_.measurable_set.measure_eq_supr_is_compact_of_lt_top
- \+ *lemma* _root_.measurable_set.exists_lt_is_compact_of_lt_top
- \+ *lemma* _root_.measurable_set.exists_lt_is_compact_of_lt_top_of_pos
- \- *lemma* outer_regular_eq
- \- *lemma* inner_regular_eq
- \+ *theorem* weakly_regular_of_inner_regular_of_finite_measure

Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* _root_.is_open.exists_Union_is_closed



## [2021-05-26 21:50:16](https://github.com/leanprover-community/mathlib/commit/a2e8b3c)
feat(special_functions/polynomials): Generalize some polynomial asymptotics to iff statements. ([#7545](https://github.com/leanprover-community/mathlib/pull/7545))
#### Estimated changes
Modified src/analysis/asymptotics/asymptotic_equivalent.lean
- \+ *lemma* is_equivalent_zero_iff_is_O_zero

Modified src/analysis/special_functions/polynomials.lean
- \+ *lemma* tendsto_at_top_iff_leading_coeff_nonneg
- \+ *lemma* tendsto_at_bot_iff_leading_coeff_nonpos
- \+ *lemma* abs_is_bounded_under_iff
- \+ *lemma* abs_tendsto_at_top_iff
- \+ *lemma* tendsto_nhds_iff
- \+ *lemma* div_tendsto_zero_iff_degree_lt
- \+ *lemma* abs_div_tendsto_at_top_of_degree_gt
- \- *lemma* eval_div_tendsto_at_top_of_degree_gt

Modified src/data/nat/with_bot.lean
- \+ *lemma* with_bot.one_le_iff_zero_lt

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* tendsto_const_mul_pow_at_top_iff
- \+ *lemma* tendsto_neg_const_mul_pow_at_top_iff

Modified src/order/liminf_limsup.lean
- \+ *lemma* not_is_bounded_under_of_tendsto_at_top
- \+ *lemma* not_is_bounded_under_of_tendsto_at_bot

Modified src/topology/algebra/ordered/basic.lean
- \+/\- *lemma* nhds_basis_Ioo'
- \+/\- *lemma* nhds_basis_Ioo
- \+ *lemma* nhds_basis_Ioo_pos
- \+ *lemma* nhds_basis_abs_sub_lt
- \+ *lemma* nhds_basis_zero_abs_sub_lt
- \+ *lemma* nhds_basis_Ioo_pos_of_pos
- \+ *lemma* mul_tendsto_nhds_zero_right
- \+ *lemma* mul_tendsto_nhds_zero_left
- \+ *lemma* nhds_eq_map_mul_left_nhds_one
- \+ *lemma* nhds_eq_map_mul_right_nhds_one
- \+ *lemma* mul_tendsto_nhds_one_nhds_one
- \+ *lemma* tendsto_const_mul_fpow_at_top_zero
- \+ *lemma* tendsto_const_mul_pow_nhds_iff
- \+ *lemma* tendsto_const_mul_fpow_at_top_zero_iff

Modified src/topology/separation.lean
- \+ *lemma* tendsto_const_nhds_iff



## [2021-05-26 19:17:45](https://github.com/leanprover-community/mathlib/commit/fd43ce0)
feat(linear_algebra/matrix): generalize `basis.to_matrix_mul_to_matrix` ([#7670](https://github.com/leanprover-community/mathlib/pull/7670))
Now the second family of vectors does not have to form a basis.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *lemma* sum_repr_mul_repr

Modified src/linear_algebra/matrix/basis.lean




## [2021-05-26 13:34:28](https://github.com/leanprover-community/mathlib/commit/fa27c0c)
feat(ring_theory/derivation): define push forward of derivations ([#7715](https://github.com/leanprover-community/mathlib/pull/7715))
#### Estimated changes
Modified src/ring_theory/derivation.lean
- \+ *lemma* mk_coe
- \+ *lemma* coe_to_linear_map_comp
- \+ *lemma* coe_comp
- \+ *def* comp



## [2021-05-26 13:34:27](https://github.com/leanprover-community/mathlib/commit/b059708)
feat(data/nnreal): filling out some lemmas ([#7710](https://github.com/leanprover-community/mathlib/pull/7710))
From LTE.
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* div_le_iff'
- \+ *lemma* le_div_iff
- \+ *lemma* le_div_iff'
- \+/\- *lemma* div_lt_iff
- \+ *lemma* div_lt_iff'
- \+ *lemma* lt_div_iff'



## [2021-05-26 13:34:26](https://github.com/leanprover-community/mathlib/commit/273546e)
feat(group_theory/sub{group,monoid,semiring,ring}): subobjects inherit the actions of their carrier type ([#7665](https://github.com/leanprover-community/mathlib/pull/7665))
This acts as a generalization of `algebra.of_subsemiring` and `algebra.of_subring`, and transfers the weaker action structures too.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/group_theory/subgroup.lean
- \+ *lemma* smul_def

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* smul_def

Modified src/ring_theory/subring.lean
- \+ *lemma* smul_def

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* smul_def



## [2021-05-26 13:34:25](https://github.com/leanprover-community/mathlib/commit/66ec15c)
feat(analysis/complex/isometry): add linear_isometry_complex ([#6923](https://github.com/leanprover-community/mathlib/pull/6923))
add proof about the isometries in the complex plane
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* conj_li_apply

Created src/analysis/complex/isometry.lean
- \+ *lemma* linear_isometry.re_apply_eq_re_of_add_conj_eq
- \+ *lemma* linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re
- \+ *lemma* linear_isometry.abs_apply_sub_one_eq_abs_sub_one
- \+ *lemma* linear_isometry.im_apply_eq_im
- \+ *lemma* linear_isometry.re_apply_eq_re
- \+ *lemma* linear_isometry_complex_aux
- \+ *lemma* linear_isometry_complex

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry.id_apply
- \+ *lemma* linear_isometry.id_to_linear_map

Modified src/data/complex/basic.lean
- \+ *lemma* conj_sub
- \+ *lemma* conj_one



## [2021-05-26 08:25:18](https://github.com/leanprover-community/mathlib/commit/a741f64)
docs(*): spelling ([#7719](https://github.com/leanprover-community/mathlib/pull/7719))
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space/has_colimits.lean


Modified src/algebraic_topology/Moore_complex.lean


Modified src/analysis/normed_space/normed_group_quotient.lean


Modified src/category_theory/category/pairwise.lean


Modified src/category_theory/limits/cofinal.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/monad/equiv_mon.lean


Modified src/category_theory/subobject/lattice.lean


Modified src/meta/expr.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/tactic/group.lean


Modified src/tactic/lint/misc.lean


Modified src/tactic/simps.lean




## [2021-05-26 08:25:17](https://github.com/leanprover-community/mathlib/commit/58c57ca)
fix(linear_algebra/tensor_product): relax from module to distrib_mul_action ([#7709](https://github.com/leanprover-community/mathlib/pull/7709))
This was an accident in [#7516](https://github.com/leanprover-community/mathlib/pull/7516) where the wrong variable was used. `R'` is the base of a distrib_mul_action, `R''`, is the base of a module.
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean




## [2021-05-26 08:25:16](https://github.com/leanprover-community/mathlib/commit/71dcb64)
feat(order/conditionally_complete_lattice): add lemmas ([#7689](https://github.com/leanprover-community/mathlib/pull/7689))
These lemmas names match the version that already exist without the `c` prefix.
This also renames `finset.sup_eq_Sup` to `finset.sup_id_eq_Sup`, and introduces a new `finset.sup_eq_Sup_image`.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* sup_id_eq_Sup
- \+ *lemma* sup_eq_Sup_image
- \+ *lemma* inf_id_eq_Inf
- \+ *lemma* inf_eq_Inf_image
- \- *lemma* sup_eq_Sup
- \- *lemma* inf_eq_Inf

Modified src/order/compactly_generated.lean


Modified src/order/complete_lattice.lean
- \+/\- *theorem* infi_true
- \+/\- *theorem* supr_true

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* le_csupr_of_le
- \+ *lemma* cinfi_le_of_le
- \+ *lemma* csupr_pos
- \+ *lemma* cinfi_pos
- \+/\- *lemma* cSup_empty
- \+ *lemma* csupr_neg
- \+ *lemma* sup'_eq_cSup_image
- \+ *lemma* inf'_eq_cInf_image
- \+ *lemma* sup'_id_eq_cSup
- \+ *lemma* inf'_id_eq_cInf
- \+ *theorem* with_top.cInf_empty
- \+/\- *theorem* with_bot.cSup_empty

Modified src/ring_theory/noetherian.lean




## [2021-05-26 08:25:15](https://github.com/leanprover-community/mathlib/commit/00394b7)
feat(tactic/simps): implement prefix names ([#7596](https://github.com/leanprover-community/mathlib/pull/7596))
* You can now write `initialize_simps_projections equiv (to_fun → coe as_prefix)` to add the projection name as a prefix to the simp lemmas: if you then write `@[simps coe] def foo ...` you get a lemma named `coe_foo`.
* Remove the `short_name` option from `simps_cfg`. This was unused and not that useful. 
* Refactor some tuples used in the functions into structures.
* Implements one item of [#5489](https://github.com/leanprover-community/mathlib/pull/5489).
#### Estimated changes
Modified src/data/list/defs.lean
- \+ *def* zip_with3
- \+ *def* zip_with4
- \+ *def* zip_with5

Modified src/meta/expr.lean
- \+ *def* update_last
- \+ *def* append_to_last

Modified src/tactic/reserved_notation.lean


Modified src/tactic/simps.lean
- \- *lemma* {simp_lemma}.
- \- *lemma* {nm}.
- \- *lemma* {nm.append_suffix

Modified test/simps.lean
- \- *lemma* specify.specify1_fst_fst.
- \- *lemma* specify.specify1_foo_fst.
- \- *lemma* specify.specify1_snd_bar.
- \- *lemma* specify.specify5_snd_snd.
- \+ *def* equiv.symm
- \+ *def* equiv.simps.symm_apply
- \+ *def* foo
- \- *def* short_name1



## [2021-05-26 06:48:35](https://github.com/leanprover-community/mathlib/commit/1f566bc)
chore(scripts): update nolints.txt ([#7718](https://github.com/leanprover-community/mathlib/pull/7718))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-05-26 06:48:34](https://github.com/leanprover-community/mathlib/commit/f7f0a30)
feat(scripts/lint-style.py): add linter that disables importing omega ([#7646](https://github.com/leanprover-community/mathlib/pull/7646))
* Files in mathlib are not allowed to `import tactic` or `import tactic.omega`. This adds a style linter to enforce this.
* `tactic.default` is allowed to import `tactic.omega` (other files that only import other files are excluded from these checks, so a malicious user still could get around this linter, but it's hard to imagine this happening accidentally)
* Remove `import tactic` from 3 files (in `archive/` and `test/`)
#### Estimated changes
Modified archive/imo/imo1964_q1.lean


Modified scripts/lint-style.py
- \+ *def* import_omega_check(lines,

Modified test/examples.lean


Modified test/traversable.lean




## [2021-05-26 00:55:46](https://github.com/leanprover-community/mathlib/commit/fd1c8e7)
feat(data/list/forall2): add two lemmas about forall₂ and reverse ([#7714](https://github.com/leanprover-community/mathlib/pull/7714))
rel_reverse shows that forall₂ is preserved across reversed lists,
forall₂_iff_reverse uses rel_reverse to show that it is preserved in
both directions.
#### Estimated changes
Modified src/data/list/forall2.lean
- \+ *lemma* rel_reverse
- \+ *lemma* forall₂_reverse_iff



## [2021-05-25 23:21:27](https://github.com/leanprover-community/mathlib/commit/360ca9c)
feat(analysis/special_functions/integrals): `interval_integrable_log` ([#7713](https://github.com/leanprover-community/mathlib/pull/7713))
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* interval_integrable.log
- \+ *lemma* interval_integrable_log



## [2021-05-25 23:21:26](https://github.com/leanprover-community/mathlib/commit/f1425b6)
feat(measure_theory/interval_integral): `integral_comp_add_left` ([#7712](https://github.com/leanprover-community/mathlib/pull/7712))
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* integral_comp_add_left



## [2021-05-25 19:48:36](https://github.com/leanprover-community/mathlib/commit/82e78ce)
feat(algebra/big_operators/finprod): add lemma `finprod_mem_finset_of_product` ([#7439](https://github.com/leanprover-community/mathlib/pull/7439))
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_mem_mul_support
- \+ *lemma* finset.mul_support_of_fiberwise_prod_subset_image
- \+ *lemma* finprod_mem_finset_product'
- \+ *lemma* finprod_mem_finset_product
- \+ *lemma* finprod_mem_finset_product₃
- \+ *lemma* finprod_curry
- \+ *lemma* finprod_curry₃

Modified src/data/support.lean
- \+ *lemma* mul_support_along_fiber_subset
- \+ *lemma* mul_support_along_fiber_finite_of_finite



## [2021-05-25 17:19:09](https://github.com/leanprover-community/mathlib/commit/8078eca)
feat(linear_algebra): `det (M ⬝ N ⬝ M') = det N`, where `M'` is an inverse of `M` ([#7633](https://github.com/leanprover-community/mathlib/pull/7633))
This is an important step towards showing the determinant of `linear_map.to_matrix` does not depend on the choice of basis.
    
The main difficulty is allowing the two indexing types of `M` to be (a priori) different. They are in bijection though (using `basis.index_equiv` from [#7631](https://github.com/leanprover-community/mathlib/pull/7631)), so using `reindex_linear_equiv` we can turn everything into square matrices and apply the "usual" proof.
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* matrix.det_conj
- \+ *def* equiv_of_pi_lequiv_pi
- \+ *def* matrix.index_equiv_of_inv

Modified src/linear_algebra/matrix/reindex.lean
- \+ *lemma* reindex_linear_equiv_mul
- \+ *lemma* reindex_alg_equiv_mul

Modified src/linear_algebra/matrix/to_lin.lean
- \+ *lemma* matrix.to_lin'_mul_apply
- \+ *lemma* matrix.to_lin_mul_apply
- \+ *def* matrix.to_lin'_of_inv
- \+ *def* matrix.to_lin_of_inv



## [2021-05-25 15:58:58](https://github.com/leanprover-community/mathlib/commit/c17c738)
feat(logic/girard): move file to counterexamples ([#7706](https://github.com/leanprover-community/mathlib/pull/7706))
Since the file feels like a counterexample, I suggest putting it in that folder.
#### Estimated changes
Renamed src/logic/girard.lean to counterexamples/girard.lean




## [2021-05-25 15:58:57](https://github.com/leanprover-community/mathlib/commit/a617d0a)
feat(algebra/category/Module): R-mod has enough projectives ([#7113](https://github.com/leanprover-community/mathlib/pull/7113))
Another piece of @TwoFX's `projective` branch, lightly edited.
#### Estimated changes
Created src/algebra/category/Module/projective.lean
- \+ *lemma* projective_of_free
- \+ *theorem* is_projective.iff_projective

Modified src/algebra/module/projective.lean
- \+ *theorem* of_lifting_property'
- \+/\- *theorem* of_lifting_property



## [2021-05-25 11:18:58](https://github.com/leanprover-community/mathlib/commit/bbf6150)
feat(measure_theory/measurable_space): add instances for subtypes ([#7702](https://github.com/leanprover-community/mathlib/pull/7702))
#### Estimated changes
Modified src/measure_theory/measurable_space.lean
- \+ *lemma* mem_coe
- \+ *lemma* coe_empty
- \+ *lemma* coe_insert
- \+ *lemma* coe_compl
- \+ *lemma* coe_union
- \+ *lemma* coe_inter
- \+ *lemma* coe_sdiff
- \+ *lemma* coe_bot
- \+ *lemma* coe_top



## [2021-05-25 11:18:57](https://github.com/leanprover-community/mathlib/commit/75e07d1)
feat(linear_algebra/matrix/determinant): lemmas about commutativity under det ([#7685](https://github.com/leanprover-community/mathlib/pull/7685))
#### Estimated changes
Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* det_mul_comm
- \+ *lemma* det_mul_left_comm
- \+ *lemma* det_mul_right_comm
- \+ *lemma* det_units_conj
- \+ *lemma* det_units_conj'



## [2021-05-25 11:18:56](https://github.com/leanprover-community/mathlib/commit/4abbe10)
feat(group_theory/group_action/units): group actions on and by units ([#7438](https://github.com/leanprover-community/mathlib/pull/7438))
This removes all the lemmas about `(u : α) • x` and `(↑u⁻¹ : α) • x` in favor of granting `units α` its very own `has_scalar` structure, along with providing the stronger variants to make it usable elsewhere.
This means that downstream code need only reason about `[group G] [mul_action G M]` instead of needing to handle groups and `units` separately.
The (multiplicative versions of the) removed and moved lemmas are:
* `units.inv_smul_smul` &rarr; `inv_smul_smul`
* `units.smul_inv_smul` &rarr; `smul_inv_smul`
* `units.smul_perm_hom`, `mul_action.to_perm` &rarr; `mul_action.to_perm_hom`
* `units.smul_perm` &rarr; `mul_action.to_perm`
* `units.smul_left_cancel` &rarr; `smul_left_cancel`
* `units.smul_eq_iff_eq_inv_smul` &rarr; `smul_eq_iff_eq_inv_smul`
* `units.smul_eq_zero` &rarr; `smul_eq_zero_iff_eq` (to avoid clashing with `smul_eq_zero`)
* `units.smul_ne_zero` &rarr; `smul_ne_zero_iff_ne`
* `homeomorph.smul_of_unit` &rarr; `homeomorph.smul` (the latter already existed, and the former was a special case)
* `units.measurable_const_smul_iff` &rarr; `measurable_const_smul_iff`
* `units.ae_measurable_const_smul_iff` &rarr; `ae_measurable_const_smul_iff`
The new lemmas are:
* `smul_eq_zero_iff_eq'`, a `group_with_zero` version of `smul_eq_zero_iff_eq`
* `smul_ne_zero_iff_ne'`, a `group_with_zero` version of `smul_ne_zero_iff_ne`
* `units.neg_smul`, a version of `neg_smul` for units. We don't currently have typeclasses about `neg` on objects without `+`.
We also end up needing some new typeclass instances downstream
* `units.measurable_space`
* `units.has_measurable_smul`
* `units.has_continuous_smul`
This goes on to remove lots of coercions from `alternating_map`, `matrix.det`, and some lie algebra stuff.
This makes the theorem statement cleaner, but occasionally requires rewriting through `units.smul_def` to add or remove the coercion.
#### Estimated changes
Modified src/algebra/group_ring_action.lean


Modified src/algebra/lie/classical.lean


Modified src/algebra/lie/skew_adjoint.lean


Modified src/algebra/module/basic.lean
- \+ *theorem* units.neg_smul

Modified src/algebra/module/linear_map.lean


Modified src/algebra/module/ordered.lean


Modified src/group_theory/group_action/group.lean
- \+/\- *lemma* inv_smul_smul
- \+/\- *lemma* smul_inv_smul
- \+/\- *lemma* inv_smul_eq_iff
- \+/\- *lemma* eq_inv_smul_iff
- \+/\- *lemma* smul_inv
- \+/\- *lemma* smul_left_cancel
- \+/\- *lemma* smul_left_cancel_iff
- \+ *lemma* smul_eq_iff_eq_inv_smul
- \- *lemma* units.inv_smul_smul
- \- *lemma* units.smul_inv_smul
- \- *lemma* units.smul_left_cancel
- \- *lemma* units.smul_eq_iff_eq_inv_smul
- \- *lemma* is_unit.smul_left_cancel
- \+ *theorem* smul_eq_zero_iff_eq
- \+ *theorem* smul_ne_zero_iff_ne
- \+ *theorem* smul_eq_zero_iff_eq'
- \+ *theorem* smul_ne_zero_iff_ne'
- \+ *theorem* smul_eq_zero
- \- *theorem* units.smul_eq_zero
- \- *theorem* units.smul_ne_zero
- \- *theorem* is_unit.smul_eq_zero
- \+/\- *def* mul_action.to_perm
- \+ *def* mul_action.to_perm_hom
- \+ *def* add_action.to_perm_hom
- \- *def* units.smul_perm
- \- *def* units.smul_perm_hom
- \- *def* add_units.vadd_perm_hom

Created src/group_theory/group_action/units.lean
- \+ *lemma* smul_def
- \+ *lemma* coe_smul
- \+ *lemma* smul_inv

Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/matrix/determinant.lean


Modified src/linear_algebra/matrix/nonsingular_inverse.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/measure_theory/arithmetic.lean
- \+/\- *lemma* measurable_const_smul_iff
- \+/\- *lemma* ae_measurable_const_smul_iff
- \- *lemma* units.measurable_const_smul_iff
- \- *lemma* units.ae_measurable_const_smul_iff

Modified src/topology/algebra/mul_action.lean
- \+/\- *lemma* tendsto_const_smul_iff
- \+/\- *lemma* continuous_within_at_const_smul_iff
- \+/\- *lemma* continuous_on_const_smul_iff
- \+/\- *lemma* continuous_at_const_smul_iff
- \+/\- *lemma* continuous_const_smul_iff
- \+/\- *lemma* is_open_map_smul
- \+/\- *lemma* is_closed_map_smul
- \- *lemma* units.tendsto_const_smul_iff
- \- *lemma* is_unit.tendsto_const_smul_iff
- \- *lemma* is_unit.continuous_within_at_const_smul_iff
- \- *lemma* is_unit.continuous_on_const_smul_iff
- \- *lemma* is_unit.continuous_at_const_smul_iff
- \- *lemma* is_unit.continuous_const_smul_iff
- \- *lemma* is_unit.is_open_map_smul
- \- *lemma* is_unit.is_closed_map_smul



## [2021-05-25 05:41:54](https://github.com/leanprover-community/mathlib/commit/d81fcda)
feat(algebra/group_with_zero): add some equational lemmas ([#7705](https://github.com/leanprover-community/mathlib/pull/7705))
Add some equations for `group_with_zero` that are direct analogues of lemmas for `group`.
Useful for [#6923](https://github.com/leanprover-community/mathlib/pull/6923).
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* mul_inv_cancel_right'
- \+/\- *lemma* mul_inv_cancel_left'
- \+/\- *lemma* inv_ne_zero
- \+/\- *lemma* inv_mul_cancel
- \+/\- *lemma* group_with_zero.mul_left_injective
- \+/\- *lemma* group_with_zero.mul_right_injective
- \+/\- *lemma* inv_mul_cancel_right'
- \+/\- *lemma* inv_mul_cancel_left'
- \+/\- *lemma* eq_inv_of_mul_right_eq_one
- \+/\- *lemma* eq_inv_of_mul_left_eq_one
- \+/\- *lemma* inv_inj'
- \+/\- *lemma* inv_eq_iff
- \+ *lemma* eq_inv_iff
- \+/\- *lemma* inv_eq_one'
- \+ *lemma* eq_mul_inv_iff_mul_eq'
- \+ *lemma* eq_inv_mul_iff_mul_eq'
- \+ *lemma* inv_mul_eq_iff_eq_mul'
- \+ *lemma* mul_inv_eq_iff_eq_mul'
- \+ *lemma* mul_inv_eq_one'
- \+ *lemma* inv_mul_eq_one'
- \+ *lemma* mul_eq_one_iff_eq_inv'
- \+ *lemma* mul_eq_one_iff_inv_eq'



## [2021-05-25 00:46:31](https://github.com/leanprover-community/mathlib/commit/a880ea4)
feat(ring_theory/coprime): add some lemmas ([#7650](https://github.com/leanprover-community/mathlib/pull/7650))
#### Estimated changes
Modified src/ring_theory/coprime.lean
- \+ *lemma* not_coprime_zero_zero
- \+ *lemma* neg_left
- \+ *lemma* neg_left_iff
- \+ *lemma* neg_right
- \+ *lemma* neg_right_iff
- \+ *lemma* neg_neg
- \+ *lemma* neg_neg_iff
- \+ *theorem* is_coprime.pow_left_iff
- \+ *theorem* is_coprime.pow_right_iff
- \+ *theorem* is_coprime.pow_iff
- \+ *theorem* is_coprime.of_coprime_of_dvd_left
- \+ *theorem* is_coprime.of_coprime_of_dvd_right
- \+ *theorem* is_coprime.is_unit_of_dvd'



## [2021-05-25 00:46:30](https://github.com/leanprover-community/mathlib/commit/c3dcb7d)
feat(category_theory/limits): comma category colimit construction ([#7535](https://github.com/leanprover-community/mathlib/pull/7535))
As well as the duals. Also adds some autoparams for consistency with `has_limit` and some missing instances which are basically just versions of existing things
#### Estimated changes
Modified src/category_theory/arrow.lean
- \+ *def* left_func
- \+ *def* right_func
- \+ *def* left_to_right

Created src/category_theory/limits/comma.lean
- \+ *def* limit_auxiliary_cone
- \+ *def* cone_of_preserves
- \+ *def* cone_of_preserves_is_limit
- \+ *def* colimit_auxiliary_cocone
- \+ *def* cocone_of_preserves
- \+ *def* cocone_of_preserves_is_colimit

Modified src/category_theory/limits/creates.lean


Modified src/category_theory/limits/kan_extension.lean


Modified src/category_theory/limits/over.lean
- \- *def* to_cocone
- \- *def* to_cone

Modified src/category_theory/limits/preserves/basic.lean


Modified src/category_theory/limits/punit.lean
- \+ *def* punit_cone
- \+ *def* punit_cocone

Modified src/category_theory/over.lean


Modified src/category_theory/punit.lean


Modified src/category_theory/structured_arrow.lean
- \+ *lemma* w
- \+/\- *lemma* eq_mk
- \+/\- *def* proj



## [2021-05-24 19:29:16](https://github.com/leanprover-community/mathlib/commit/17f3b80)
feat(100-theorems-list/16_abel_ruffini): some simplifications ([#7699](https://github.com/leanprover-community/mathlib/pull/7699))
#### Estimated changes
Modified archive/100-theorems-list/16_abel_ruffini.lean
- \+/\- *lemma* irreducible_Phi

Modified docs/100.yaml




## [2021-05-24 19:29:15](https://github.com/leanprover-community/mathlib/commit/51526ae)
chore(topology): rename mem_nhds_sets and mem_of_nhds and mem_nhds_sets_iff ([#7690](https://github.com/leanprover-community/mathlib/pull/7690))
Rename `mem_nhds_sets` to `is_open.mem_nhds`, and `mem_nhds_sets_iff` to `mem_nhds_iff`, and `mem_of_nhds` to `mem_of_mem_nhds`.
#### Estimated changes
Modified src/algebra/ordered_monoid.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/inverse.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/normed_group_quotient.lean


Modified src/analysis/normed_space/units.lean


Modified src/analysis/seminorm.lean


Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/special_functions/pow.lean


Modified src/data/analysis/topology.lean


Modified src/data/real/ennreal.lean


Modified src/dynamics/omega_limit.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/bump_function.lean
- \+/\- *lemma* c_mem_support

Modified src/geometry/manifold/charted_space.lean


Modified src/geometry/manifold/local_invariant_properties.lean


Modified src/geometry/manifold/mfderiv.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/pi.lean


Modified src/measure_theory/set_integral.lean


Modified src/order/basic.lean


Modified src/topology/G_delta.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/nonarchimedean/basic.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/algebra/ordered/liminf_limsup.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean
- \+ *lemma* mem_nhds_iff
- \+ *lemma* mem_of_mem_nhds
- \+ *lemma* is_open.mem_nhds
- \- *lemma* mem_nhds_sets_iff
- \- *lemma* mem_of_nhds
- \- *lemma* mem_nhds_sets

Modified src/topology/category/Compactum.lean


Modified src/topology/compact_open.lean


Modified src/topology/constructions.lean
- \+ *lemma* prod_is_open.mem_nhds
- \- *lemma* prod_mem_nhds_sets

Modified src/topology/continuous_function/bounded.lean


Modified src/topology/continuous_function/stone_weierstrass.lean


Modified src/topology/continuous_on.lean
- \+ *theorem* nhds_within_le_nhds

Modified src/topology/dense_embedding.lean


Modified src/topology/extend_from.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/real.lean


Modified src/topology/list.lean


Modified src/topology/local_homeomorph.lean


Modified src/topology/locally_constant/basic.lean


Modified src/topology/maps.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/opens.lean


Modified src/topology/order.lean


Modified src/topology/paracompact.lean


Modified src/topology/path_connected.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean


Modified src/topology/topological_fiber_bundle.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/compact_separated.lean


Modified src/topology/uniform_space/separation.lean


Modified src/topology/uniform_space/uniform_embedding.lean


Modified src/topology/urysohns_lemma.lean




## [2021-05-24 14:07:33](https://github.com/leanprover-community/mathlib/commit/91a547e)
feat(algebra/opposites): `(un)op_ne_zero_iff` ([#7698](https://github.com/leanprover-community/mathlib/pull/7698))
#### Estimated changes
Modified src/algebra/opposites.lean
- \+ *lemma* unop_ne_zero_iff
- \+ *lemma* op_ne_zero_iff



## [2021-05-24 14:07:32](https://github.com/leanprover-community/mathlib/commit/a09ddc7)
feat(measure_theory/interval_integral): `interval_integrable.mono` ([#7679](https://github.com/leanprover-community/mathlib/pull/7679))
`interval_integrable f ν a b → interval c d ⊆ interval a b → μ ≤ ν → interval_integrable f μ c d`
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* interval_integrable_iff
- \+ *lemma* interval_integrable.def
- \+/\- *lemma* measure_theory.integrable.interval_integrable
- \+/\- *lemma* trans
- \+ *lemma* mono
- \+ *lemma* mono_set
- \+ *lemma* mono_measure
- \+ *lemma* mono_set_ae



## [2021-05-24 11:01:13](https://github.com/leanprover-community/mathlib/commit/0b51a72)
feat(linear_algebra/determinant): specialize `is_basis.iff_det` ([#7668](https://github.com/leanprover-community/mathlib/pull/7668))
After the bundled basis refactor, applying `is_basis.iff_det` in the forward direction is slightly more involved (since defining the `iff` requires an unbundled basis), so I added a lemma that does the necessary translation between "unbundled basis" and "bundled basis" for you.
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* is_basis_iff_det
- \+ *lemma* basis.is_unit_det
- \- *lemma* is_basis.iff_det



## [2021-05-24 11:01:12](https://github.com/leanprover-community/mathlib/commit/8ff2783)
feat(counterexamples/cyclotomic_105): add coeff_cyclotomic_105 ([#7648](https://github.com/leanprover-community/mathlib/pull/7648))
We show that `coeff (cyclotomic 105 ℤ) 7 = -2`, proving that not all coefficients of cyclotomic polynomials are `0`, `-1` or `1`.
#### Estimated changes
Created counterexamples/cyclotomic_105.lean
- \+ *lemma* prime_3
- \+ *lemma* prime_5
- \+ *lemma* prime_7
- \+ *lemma* proper_divisors_15
- \+ *lemma* proper_divisors_21
- \+ *lemma* proper_divisors_35
- \+ *lemma* proper_divisors_105
- \+ *lemma* cyclotomic_3
- \+ *lemma* cyclotomic_5
- \+ *lemma* cyclotomic_7
- \+ *lemma* cyclotomic_15
- \+ *lemma* cyclotomic_21
- \+ *lemma* cyclotomic_35
- \+ *lemma* cyclotomic_105
- \+ *lemma* coeff_cyclotomic_105
- \+ *lemma* not_forall_coeff_cyclotomic_neg_one_zero_one
- \+ *theorem* `not_forall_coeff_cyclotomic_neg_one_zero_one`.

Modified src/data/polynomial/coeff.lean
- \+ *lemma* coeff_bit0_mul
- \+ *lemma* coeff_bit1_mul



## [2021-05-24 05:13:08](https://github.com/leanprover-community/mathlib/commit/16733c8)
chore(data/nat/basic): move unique {units/add_units} instances ([#7701](https://github.com/leanprover-community/mathlib/pull/7701))
#### Estimated changes
Modified src/data/nat/basic.lean


Modified src/ring_theory/int/basic.lean




## [2021-05-23 23:25:01](https://github.com/leanprover-community/mathlib/commit/2734d91)
fix(data/nat/factorial): fix factorial_zero ([#7697](https://github.com/leanprover-community/mathlib/pull/7697))
#### Estimated changes
Modified src/data/nat/factorial.lean
- \+/\- *theorem* factorial_zero



## [2021-05-23 16:33:37](https://github.com/leanprover-community/mathlib/commit/6cffc9f)
chore(logic/unique): a true prop is unique ([#7688](https://github.com/leanprover-community/mathlib/pull/7688))
I found myself needing to construct this instance by hand somewhere; since we already need it to construct `unique true`, we may as well make a def.
#### Estimated changes
Modified src/logic/unique.lean
- \+ *def* unique_prop



## [2021-05-23 13:50:13](https://github.com/leanprover-community/mathlib/commit/57cd5ef)
refactor(*): remove some uses of omega in the library ([#7700](https://github.com/leanprover-community/mathlib/pull/7700))
#### Estimated changes
Modified src/algebra/homology/augment.lean


Modified src/algebra/homology/single.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/ring_theory/polynomial/bernstein.lean


Modified src/ring_theory/witt_vector/structure_polynomial.lean




## [2021-05-22 21:53:35](https://github.com/leanprover-community/mathlib/commit/97a5276)
doc(number_theory/bernoulli): write statements in math mode ([#7696](https://github.com/leanprover-community/mathlib/pull/7696))
* It took me some work to see the difference between the two statements, so I added the statements in math mode.
* Change name `sum_range_pow'` -> `sum_Ico_pow`
#### Estimated changes
Modified docs/100.yaml


Modified src/number_theory/bernoulli.lean
- \+ *theorem* sum_Ico_pow
- \- *theorem* sum_range_pow'



## [2021-05-22 16:17:14](https://github.com/leanprover-community/mathlib/commit/fb95362)
fix(algebra/homology): imports ([#7655](https://github.com/leanprover-community/mathlib/pull/7655))
#### Estimated changes
Modified src/algebra/homology/homology.lean


Modified src/algebra/homology/image_to_kernel.lean




## [2021-05-22 12:15:37](https://github.com/leanprover-community/mathlib/commit/0e216ce)
feat(order): if s is finite then Sup s ∈ s ([#7682](https://github.com/leanprover-community/mathlib/pull/7682))
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* set.nonempty.cSup_mem
- \+ *lemma* finset.nonempty.cSup_mem
- \+ *lemma* set.nonempty.cInf_mem
- \+ *lemma* finset.nonempty.cInf_mem



## [2021-05-22 12:15:36](https://github.com/leanprover-community/mathlib/commit/418dc04)
feat(100-theorems-list/16_abel_ruffini): The Abel-Ruffini Theorem ([#7562](https://github.com/leanprover-community/mathlib/pull/7562))
It's done!
#### Estimated changes
Created archive/100-theorems-list/16_abel_ruffini.lean
- \+ *lemma* map_Phi
- \+ *lemma* coeff_zero_Phi
- \+ *lemma* coeff_five_Phi
- \+ *lemma* degree_Phi
- \+ *lemma* nat_degree_Phi
- \+ *lemma* leading_coeff_Phi
- \+ *lemma* monic_Phi
- \+ *lemma* irreducible_Phi
- \+ *lemma* real_roots_Phi_le
- \+ *lemma* real_roots_Phi_ge_aux
- \+ *lemma* real_roots_Phi_ge
- \+ *lemma* complex_roots_Phi
- \+ *lemma* gal_Phi
- \+ *theorem* not_solvable_by_rad
- \+ *theorem* not_solvable_by_rad'
- \+ *theorem* exists_not_solvable_by_rad

Modified docs/100.yaml


Modified src/field_theory/separable.lean
- \+ *lemma* card_root_set_eq_nat_degree



## [2021-05-22 06:50:13](https://github.com/leanprover-community/mathlib/commit/b29d40c)
fix(algebra): change local transparency to semireducible ([#7687](https://github.com/leanprover-community/mathlib/pull/7687))
* When a type is `[irreducible]` it should locally be made `[semireducible]` and (almost) never `[reducible]`. 
* If it is made `[reducible]`, type-class inference will unfold this definition, and will apply instances that would not type-check when the definition is `[irreducible]`
#### Estimated changes
Modified src/algebra/opposites.lean
- \+/\- *lemma* unop_eq_zero_iff
- \+/\- *lemma* op_eq_zero_iff
- \+/\- *lemma* unop_eq_one_iff
- \+/\- *lemma* op_eq_one_iff

Modified src/algebra/ordered_monoid.lean


Modified src/data/polynomial/ring_division.lean




## [2021-05-21 21:35:13](https://github.com/leanprover-community/mathlib/commit/f8530d5)
feat(ring_theory/ideal/operations): `ideal.span_singleton_pow` ([#7660](https://github.com/leanprover-community/mathlib/pull/7660))
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* span_singleton_pow



## [2021-05-21 16:38:59](https://github.com/leanprover-community/mathlib/commit/f70e160)
chore(order/conditionally_complete_lattice): golf proofs with `order_dual` ([#7684](https://github.com/leanprover-community/mathlib/pull/7684))
Even in the places where this doesn't result in a shorter proof, it makes it obvious that the `inf` lemmas have a matching `sup` lemma.
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+/\- *theorem* cinfi_const
- \+/\- *theorem* infi_unique
- \+/\- *theorem* infi_unit



## [2021-05-21 11:28:01](https://github.com/leanprover-community/mathlib/commit/233eff0)
feat(data/fintype/card_embedding): the birthday problem ([#7363](https://github.com/leanprover-community/mathlib/pull/7363))
#### Estimated changes
Created archive/100-theorems-list/93_birthday_problem.lean
- \+ *theorem* birthday

Modified docs/100.yaml


Modified src/data/equiv/basic.lean
- \+ *def* subtype_prod_equiv_sigma_subtype

Created src/data/equiv/embedding.lean
- \+ *def* sum_embedding_equiv_prod_embedding_disjoint
- \+ *def* cod_restrict
- \+ *def* prod_embedding_disjoint_equiv_sigma_embedding_restricted
- \+ *def* sum_embedding_equiv_sigma_embedding_restricted
- \+ *def* unique_embedding_equiv_result

Modified src/data/fintype/basic.lean
- \+ *lemma* is_empty_of_card_lt

Created src/data/fintype/card_embedding.lean
- \+ *lemma* card_embedding_of_unique
- \+ *lemma* card_embedding_eq_infinite
- \+ *theorem* card_embedding
- \+ *theorem* card_embedding_eq_zero
- \+ *theorem* card_embedding_eq_if

Modified src/data/nat/factorial.lean
- \+ *lemma* desc_fac_of_sub

Modified src/logic/embedding.lean
- \+ *lemma* mk_coe
- \+ *lemma* embedding_congr_refl
- \+ *lemma* embedding_congr_trans
- \+ *lemma* embedding_congr_symm
- \+ *lemma* embedding_congr_apply_trans
- \+ *def* subtype_injective_equiv_embedding
- \+ *def* embedding_congr

Modified src/ring_theory/polynomial/pochhammer.lean




## [2021-05-21 00:33:53](https://github.com/leanprover-community/mathlib/commit/1924742)
feat(data/set/basic): allow dot notation for trans and antisymm ([#7681](https://github.com/leanprover-community/mathlib/pull/7681))
Allow to write
```lean
example {α : Type*} {a b c : set α} (h : a ⊆ b)  (h': b ⊆ c) : a ⊆ c :=
h.trans h'
example {α : Type*} {a b : set α} (h : a ⊆ b)  (h': b ⊆ a) : 
  a = b := h.antisymm h'
example {α : Type*} {a b c : finset α} (h : a ⊆ b)  (h': b ⊆ c) : a ⊆ c :=
h.trans h'
example {α : Type*} {a b : finset α} (h : a ⊆ b)  (h': b ⊆ a) : a = b :=
h.antisymm h'
```
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* has_subset.subset.trans
- \+ *lemma* has_subset.subset.antisymm
- \+ *lemma* has_ssubset.ssubset.trans
- \+ *lemma* has_ssubset.ssubset.asymm



## [2021-05-21 00:33:52](https://github.com/leanprover-community/mathlib/commit/53e2307)
feat(ring_theory): every left-noetherian ring has invariant basis number ([#7678](https://github.com/leanprover-community/mathlib/pull/7678))
This is a lovely case where we get more for less.
By directly proving that every left-noetherian ring has invariant basis number, we don't need to import `linear_algebra.finite_dimensional` in order to do the `field` case. This means that in a future PR we can instead import `ring_theory.invariant_basis_number` in `linear_algebra.finite_dimensional`, and set up the theory of bases in greater generality.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *lemma* map_eq_zero_iff

Modified src/linear_algebra/basic.lean
- \+ *theorem* fun_left_surjective_of_injective
- \+ *theorem* fun_left_injective_of_surjective

Modified src/linear_algebra/invariant_basis_number.lean
- \+ *lemma* le_of_fin_injective
- \+ *lemma* le_of_fin_surjective
- \- *lemma* invariant_basis_number_field



## [2021-05-21 00:33:51](https://github.com/leanprover-community/mathlib/commit/c63c6d1)
feat(order/closure): make closure operators implementable ([#7608](https://github.com/leanprover-community/mathlib/pull/7608))
introduce `lower_adjoint` as a way to talk about closure operators whose input and output types do not match
#### Estimated changes
Modified src/order/closure.lean
- \+/\- *lemma* closure_top
- \+/\- *lemma* top_mem_closed
- \+/\- *lemma* closure_inf_le
- \+/\- *lemma* closure_sup_closure_le
- \+/\- *lemma* closure_sup_closure_left
- \+/\- *lemma* closure_sup_closure_right
- \+/\- *lemma* closure_sup_closure
- \+/\- *lemma* closure_supr_closure
- \+/\- *lemma* closure_bsupr_closure
- \+ *lemma* gc
- \+ *lemma* ext
- \+ *lemma* monotone
- \+ *lemma* le_closure
- \+ *lemma* idempotent
- \+ *lemma* le_closure_iff
- \+ *lemma* mem_closed_iff
- \+ *lemma* closure_eq_self_of_mem_closed
- \+ *lemma* mem_closed_iff_closure_le
- \+ *lemma* closure_is_closed
- \+ *lemma* closed_eq_range_close
- \+ *lemma* closure_le_closed_iff_le
- \+ *lemma* subset_closure
- \+ *lemma* le_iff_subset
- \+ *lemma* mem_iff
- \+ *lemma* eq_of_le
- \+ *lemma* closure_union_closure_subset
- \+ *lemma* closure_union_closure_left
- \+ *lemma* closure_union_closure_right
- \+ *lemma* closure_union_closure
- \+ *lemma* closure_Union_closure
- \+ *lemma* closure_bUnion_closure
- \+/\- *lemma* closure_operator_gi_self
- \+ *def* simps.apply
- \+ *def* closure_operator
- \+ *def* closed
- \+ *def* to_closed
- \+ *def* galois_connection.lower_adjoint
- \+/\- *def* galois_connection.closure_operator
- \+ *def* closure_operator.gi
- \- *def* closure_operator.simps.apply
- \- *def* gi



## [2021-05-20 19:10:37](https://github.com/leanprover-community/mathlib/commit/32b433d)
refactor(*): remove some uses of omega in the library ([#7620](https://github.com/leanprover-community/mathlib/pull/7620))
In [#6129](https://github.com/leanprover-community/mathlib/pull/6129), we stopped using `omega` to avoid porting it to lean4.
Some new uses were added since then.
#### Estimated changes
Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified archive/imo/imo1988_q6.lean


Modified src/algebra/homology/augment.lean


Modified src/algebra/homology/single.lean


Modified src/algebra/ordered_monoid.lean
- \+ *lemma* pos_of_gt

Modified src/number_theory/arithmetic_function.lean


Modified src/ring_theory/polynomial/bernstein.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/ring_theory/witt_vector/structure_polynomial.lean




## [2021-05-20 15:24:52](https://github.com/leanprover-community/mathlib/commit/d47a6e3)
feat(topology): clopens form a topology basis for profinite sets ([#7671](https://github.com/leanprover-community/mathlib/pull/7671))
from LTE
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* exists_open_set_nhds
- \+ *lemma* exists_open_set_nhds'

Modified src/topology/separation.lean
- \+ *lemma* exists_subset_nhd_of_compact
- \+ *lemma* nhds_basis_clopen
- \+ *lemma* is_topological_basis_clopen

Modified src/topology/subset_properties.lean
- \+ *lemma* exists_subset_nhd_of_compact'
- \+ *lemma* exists_subset_nhd_of_compact_space
- \+ *lemma* is_clopen_Union
- \+ *lemma* is_clopen_bUnion



## [2021-05-20 13:34:18](https://github.com/leanprover-community/mathlib/commit/d3ec77c)
feat(category_theory/limits): reflecting limits of isomorphic diagram ([#7674](https://github.com/leanprover-community/mathlib/pull/7674))
#### Estimated changes
Modified src/category_theory/limits/preserves/basic.lean
- \+ *def* reflects_limit_of_iso_diagram
- \+ *def* reflects_colimit_of_iso_diagram



## [2021-05-20 08:06:42](https://github.com/leanprover-community/mathlib/commit/c5951f3)
feat(ring_theory/noetherian): a surjective endomorphism of a noetherian module is injective ([#7676](https://github.com/leanprover-community/mathlib/pull/7676))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *def* iterate_range
- \+ *def* iterate_ker

Modified src/ring_theory/noetherian.lean
- \+ *theorem* monotone_stabilizes_iff_noetherian
- \+ *theorem* is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot
- \+ *theorem* is_noetherian.injective_of_surjective_endomorphism
- \+ *theorem* is_noetherian.bijective_of_surjective_endomorphism



## [2021-05-20 08:06:41](https://github.com/leanprover-community/mathlib/commit/ff51159)
feat(algebra/homology/*): add hypotheses to the d_comp_d' axiom ([#7673](https://github.com/leanprover-community/mathlib/pull/7673))
#### Estimated changes
Modified src/algebra/homology/additive.lean


Modified src/algebra/homology/augment.lean


Modified src/algebra/homology/differential_object.lean


Modified src/algebra/homology/flip.lean


Modified src/algebra/homology/homological_complex.lean
- \+ *lemma* d_comp_d



## [2021-05-20 08:06:40](https://github.com/leanprover-community/mathlib/commit/2d414d0)
feat(algebra/homology/homological_complex): add condition to hom.comm' ([#7666](https://github.com/leanprover-community/mathlib/pull/7666))
#### Estimated changes
Modified src/algebra/homology/additive.lean


Modified src/algebra/homology/differential_object.lean


Modified src/algebra/homology/flip.lean


Modified src/algebra/homology/homological_complex.lean
- \+ *lemma* hom.comm

Modified src/algebra/homology/single.lean




## [2021-05-20 08:06:39](https://github.com/leanprover-community/mathlib/commit/0cb7ecc)
fix(category_theory/limits/shapes/zero): use fully qualified names in locale ([#7619](https://github.com/leanprover-community/mathlib/pull/7619))
#### Estimated changes
Modified src/category_theory/limits/shapes/zero.lean




## [2021-05-20 02:00:39](https://github.com/leanprover-community/mathlib/commit/5a67f2c)
chore(topology): rename compact to is_compact in theorem names ([#7672](https://github.com/leanprover-community/mathlib/pull/7672))
Some time ago, we switched from `compact` to `is_compact`, for coherence with `is_open`, `is_closed` and so on. However, several lemma names were not changed at the time. This PR fixes some of them. Plus a few minor stuff (notably, introduce `le_self_add` to replace the dozen of uses of `le_add_right (le_refl _)` in the library -- and weaken some `metric` assumptions to `pseudo_metric`, without touching the proofs).
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/algebra/ordered_monoid.lean
- \+ *lemma* le_mul_self
- \+ *lemma* le_self_mul

Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/specific_limits.lean
- \+/\- *lemma* ennreal.tsum_geometric

Modified src/data/equiv/denumerable.lean


Modified src/data/list/basic.lean


Modified src/data/pnat/factors.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* one_sub_inv_two

Modified src/data/real/nnreal.lean


Modified src/dynamics/omega_limit.lean


Modified src/measure_theory/haar_measure.lean


Modified src/measure_theory/hausdorff_measure.lean


Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_add_measure_compl

Modified src/set_theory/cardinal.lean


Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* cauchy_seq_of_edist_le_of_summable
- \+/\- *lemma* cauchy_seq_of_dist_le_of_summable
- \+/\- *lemma* cauchy_seq_of_summable_dist
- \+/\- *lemma* dist_le_tsum_of_dist_le_of_tendsto
- \+/\- *lemma* dist_le_tsum_of_dist_le_of_tendsto₀
- \+/\- *lemma* dist_le_tsum_dist_of_tendsto
- \+/\- *lemma* dist_le_tsum_dist_of_tendsto₀

Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/category/CompHaus.lean


Modified src/topology/category/Compactum.lean


Modified src/topology/category/Top/limits.lean


Modified src/topology/compact_open.lean


Modified src/topology/compacts.lean


Modified src/topology/continuous_function/bounded.lean


Modified src/topology/discrete_quotient.lean


Modified src/topology/homeomorph.lean


Modified src/topology/instances/ennreal.lean
- \+ *lemma* tendsto_nat_tsum

Modified src/topology/locally_constant/basic.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* mem_iff_inf_edist_zero_of_closed
- \+/\- *lemma* Hausdorff_edist_def
- \- *lemma* mem_iff_ind_edist_zero_of_closed
- \+/\- *def* Hausdorff_edist

Modified src/topology/metric_space/kuratowski.lean


Modified src/topology/paracompact.lean


Modified src/topology/separation.lean


Modified src/topology/sequences.lean


Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean
- \+ *lemma* is_compact.diff
- \+ *lemma* is_compact_iff_ultrafilter_le_nhds
- \+ *lemma* is_compact_of_finite_subcover
- \+ *lemma* is_compact_iff_finite_subcover
- \+ *lemma* is_compact_empty
- \+ *lemma* is_compact_singleton
- \+ *lemma* is_closed.is_compact
- \+ *lemma* is_compact_range
- \+ *lemma* embedding.is_compact_iff_is_compact_image
- \+ *lemma* is_compact_iff_is_compact_univ
- \+ *lemma* is_compact_iff_compact_space
- \+ *lemma* is_compact_pi_infinite
- \+ *lemma* is_compact_univ_pi
- \- *lemma* compact_diff
- \- *lemma* compact_iff_ultrafilter_le_nhds
- \- *lemma* compact_of_finite_subcover
- \- *lemma* compact_iff_finite_subcover
- \- *lemma* compact_empty
- \- *lemma* compact_singleton
- \- *lemma* is_closed.compact
- \- *lemma* compact_range
- \- *lemma* embedding.compact_iff_compact_image
- \- *lemma* compact_iff_compact_univ
- \- *lemma* compact_iff_compact_space
- \- *lemma* compact_pi_infinite
- \- *lemma* compact_univ_pi
- \+ *theorem* is_compact_of_finite_subfamily_closed
- \+ *theorem* is_compact_iff_finite_subfamily_closed
- \+ *theorem* is_closed_proj_of_is_compact
- \- *theorem* compact_of_finite_subfamily_closed
- \- *theorem* compact_iff_finite_subfamily_closed
- \- *theorem* is_closed_proj_of_compact

Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/compact_separated.lean




## [2021-05-20 02:00:37](https://github.com/leanprover-community/mathlib/commit/1016a14)
refactor(linear_algebra/finite_dimensional): generalize finite_dimensional.iff_fg to division rings ([#7644](https://github.com/leanprover-community/mathlib/pull/7644))
Replace `finite_dimensional.iff_fg` (working over a field) with `is_noetherian.iff_fg` (working over a division ring). Also, use the `module.finite` predicate.
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/field_theory/finite/polynomial.lean


Created src/field_theory/finiteness.lean
- \+ *lemma* iff_dim_lt_omega
- \+ *lemma* dim_lt_omega
- \+ *lemma* finite_basis_index
- \+ *lemma* coe_finset_basis_index
- \+ *lemma* range_finset_basis
- \+ *lemma* iff_fg

Modified src/field_theory/fixed.lean


Modified src/field_theory/splitting_field.lean


Modified src/field_theory/tower.lean


Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* basis.nonempty_fintype_index_of_dim_lt_omega
- \+/\- *lemma* basis.finite_index_of_dim_lt_omega
- \+/\- *lemma* basis.finite_of_vector_space_index_of_dim_lt_omega

Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finite_dimensional.lean
- \- *lemma* finite_dimensional_iff_dim_lt_omega
- \- *lemma* dim_lt_omega
- \- *lemma* finite_basis_index
- \- *lemma* coe_finset_basis_index
- \- *lemma* range_finset_basis
- \- *lemma* iff_fg

Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/ring_theory/finiteness.lean
- \+/\- *lemma* finite_def

Modified src/ring_theory/noetherian.lean
- \+/\- *lemma* finite_of_linear_independent



## [2021-05-20 02:00:36](https://github.com/leanprover-community/mathlib/commit/641cece)
feat(algebra/homology): the homotopy category ([#7484](https://github.com/leanprover-community/mathlib/pull/7484))
#### Estimated changes
Created src/algebra/homology/homotopy_category.lean
- \+ *lemma* quotient_obj_as
- \+ *lemma* quotient_map_out
- \+ *lemma* eq_of_homotopy
- \+ *lemma* quotient_map_out_comp_out
- \+ *lemma* homology_factors_hom_app
- \+ *lemma* homology_factors_inv_app
- \+ *lemma* homology_functor_map_factors
- \+ *lemma* nat_trans.map_homotopy_category_id
- \+ *lemma* nat_trans.map_homotopy_category_comp
- \+ *def* homotopic
- \+ *def* homotopy_category
- \+ *def* quotient
- \+ *def* homotopy_of_eq
- \+ *def* homotopy_out_map
- \+ *def* iso_of_homotopy_equiv
- \+ *def* homotopy_equiv_of_iso
- \+ *def* homology_functor
- \+ *def* homology_factors
- \+ *def* functor.map_homotopy_category
- \+ *def* nat_trans.map_homotopy_category



## [2021-05-19 19:28:27](https://github.com/leanprover-community/mathlib/commit/116c162)
feat(algebra/opposites): `opposite` of a `group_with_zero` ([#7662](https://github.com/leanprover-community/mathlib/pull/7662))
Co-authored by @eric-wieser
#### Estimated changes
Modified src/algebra/opposites.lean




## [2021-05-19 15:49:00](https://github.com/leanprover-community/mathlib/commit/ed4161c)
feat(data/polynomial/coeff): generalize polynomial.coeff_smul to match mv_polynomial.coeff_smul ([#7663](https://github.com/leanprover-community/mathlib/pull/7663))
Notably this means these lemmas cover `nat` and `int` actions.
#### Estimated changes
Modified src/data/polynomial/coeff.lean
- \+/\- *lemma* coeff_smul
- \+/\- *lemma* support_smul



## [2021-05-19 15:48:58](https://github.com/leanprover-community/mathlib/commit/599712f)
feat(data/int/parity, data/nat/parity): add some lemmas ([#7624](https://github.com/leanprover-community/mathlib/pull/7624))
#### Estimated changes
Modified src/data/int/parity.lean
- \+/\- *theorem* even_pow
- \+ *theorem* even_pow'
- \+/\- *theorem* even_coe_nat
- \+ *theorem* odd_coe_nat
- \+ *theorem* nat_abs_even
- \+ *theorem* nat_abs_odd

Modified src/data/nat/parity.lean
- \+/\- *theorem* even_pow
- \+ *theorem* even_pow'



## [2021-05-19 12:41:13](https://github.com/leanprover-community/mathlib/commit/697c8dd)
refactor(topology/basic): use dot notation in `is_open.union` and friends ([#7647](https://github.com/leanprover-community/mathlib/pull/7647))
The fact that the union of two open sets is open is called `is_open_union`. We rename it to `is_open.union` to enable dot notation. Same with `is_open_inter`, `is_closed_union` and `is_closed_inter` and `is_clopen_union` and `is_clopen_inter` and `is_clopen_diff`.
#### Estimated changes
Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/calculus/fderiv_measurable.lean


Modified src/analysis/convex/topology.lean


Modified src/data/analysis/topology.lean


Modified src/geometry/manifold/bump_function.lean


Modified src/geometry/manifold/charted_space.lean


Modified src/geometry/manifold/local_invariant_properties.lean


Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/content.lean


Modified src/measure_theory/haar_measure.lean


Modified src/topology/G_delta.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean
- \+ *lemma* is_open.inter
- \+ *lemma* is_open.union
- \+ *lemma* is_open.and
- \+ *lemma* is_closed.union
- \+ *lemma* is_open.sdiff
- \+ *lemma* is_closed.inter
- \+ *lemma* is_closed.not
- \- *lemma* is_open_inter
- \- *lemma* is_open_union
- \- *lemma* is_open_and
- \- *lemma* is_closed_union
- \- *lemma* is_open_diff
- \- *lemma* is_closed_inter
- \- *lemma* is_open_neg

Modified src/topology/connected.lean


Modified src/topology/constructions.lean


Modified src/topology/continuous_on.lean


Modified src/topology/dense_embedding.lean


Modified src/topology/discrete_quotient.lean


Modified src/topology/local_homeomorph.lean


Modified src/topology/maps.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/omega_complete_partial_order.lean
- \+ *theorem* is_open.inter
- \- *theorem* is_open_inter

Modified src/topology/opens.lean


Modified src/topology/separation.lean


Modified src/topology/shrinking_lemma.lean


Modified src/topology/subset_properties.lean
- \+ *theorem* is_clopen.union
- \+ *theorem* is_clopen.inter
- \+ *theorem* is_clopen.compl
- \+ *theorem* is_clopen.diff
- \- *theorem* is_clopen_union
- \- *theorem* is_clopen_inter
- \- *theorem* is_clopen_compl
- \- *theorem* is_clopen_diff

Modified src/topology/topological_fiber_bundle.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/compact_separated.lean




## [2021-05-19 09:57:34](https://github.com/leanprover-community/mathlib/commit/c7a5197)
feat(data/polynomial/degree/definitions): `polynomial.degree_C_mul_X_le` ([#7659](https://github.com/leanprover-community/mathlib/pull/7659))
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* degree_C_mul_X_le



## [2021-05-19 09:57:33](https://github.com/leanprover-community/mathlib/commit/040ebea)
fix(analysis/normed_space/normed_group_quotient): put lemmas inside namespace  ([#7653](https://github.com/leanprover-community/mathlib/pull/7653))
#### Estimated changes
Modified src/analysis/normed_space/normed_group_quotient.lean




## [2021-05-19 08:44:51](https://github.com/leanprover-community/mathlib/commit/c1e9f94)
docs(field_theory/polynomial_galois_group): improve existing docs ([#7586](https://github.com/leanprover-community/mathlib/pull/7586))
#### Estimated changes
Modified src/field_theory/polynomial_galois_group.lean
- \+ *lemma* card_complex_roots_eq_card_real_add_card_not_gal_inv
- \- *lemma* gal_action_hom_bijective_of_prime_degree_aux



## [2021-05-19 02:36:44](https://github.com/leanprover-community/mathlib/commit/1d4990e)
chore(scripts): update nolints.txt ([#7658](https://github.com/leanprover-community/mathlib/pull/7658))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-05-19 02:36:43](https://github.com/leanprover-community/mathlib/commit/918dcc0)
chore(algebra/homology): further dualization ([#7657](https://github.com/leanprover-community/mathlib/pull/7657))
#### Estimated changes
Modified src/algebra/homology/augment.lean
- \+ *lemma* chain_complex_d_succ_succ_zero
- \+ *lemma* augment_X_zero
- \+ *lemma* augment_X_succ
- \+ *lemma* augment_d_zero_one
- \+ *lemma* augment_d_succ_succ
- \+ *lemma* truncate_augment_hom_f
- \+ *lemma* truncate_augment_inv_f
- \+/\- *lemma* cochain_complex_d_succ_succ_zero
- \+ *lemma* augment_truncate_hom_f_zero
- \+ *lemma* augment_truncate_hom_f_succ
- \+ *lemma* augment_truncate_inv_f_zero
- \+ *lemma* augment_truncate_inv_f_succ
- \+ *def* truncate
- \+ *def* to_truncate
- \+ *def* augment
- \+ *def* truncate_augment
- \+ *def* augment_truncate
- \+ *def* from_single₀_as_complex

Modified src/algebra/homology/homological_complex.lean
- \+ *lemma* mk_X_0
- \+ *lemma* mk_X_1
- \+ *lemma* mk_X_2
- \+ *lemma* mk_d_1_0
- \+ *lemma* mk_d_2_0
- \+ *lemma* mk'_X_0
- \+ *lemma* mk'_X_1
- \+ *lemma* mk'_d_1_0
- \+ *lemma* mk_hom_f_0
- \+ *lemma* mk_hom_f_1
- \+ *lemma* mk_hom_f_succ_succ
- \+ *def* mk_struct.flat
- \+ *def* mk_aux
- \+ *def* mk
- \+ *def* mk'
- \+ *def* mk_hom_aux
- \+ *def* mk_hom

Modified src/algebra/homology/single.lean
- \+ *lemma* single₀_obj_X_0
- \+ *lemma* single₀_obj_X_succ
- \+ *lemma* single₀_obj_X_d
- \+ *lemma* single₀_obj_X_d_from
- \+ *lemma* single₀_obj_X_d_to
- \+ *lemma* single₀_map_f_0
- \+ *lemma* single₀_map_f_succ
- \+ *def* single₀
- \+ *def* homology_functor_0_single₀
- \+ *def* homology_functor_succ_single₀
- \+ *def* from_single₀_equiv
- \+ *def* single₀_iso_single



## [2021-05-19 02:36:42](https://github.com/leanprover-community/mathlib/commit/aee918b)
feat(algebraic_topology/simplicial_object): Some API for converting between simplicial and cosimplicial ([#7656](https://github.com/leanprover-community/mathlib/pull/7656))
This adds some code which is helpful to convert back and forth between simplicial and cosimplicial object.
For augmented objects, this doesn't follow directly from the existing API in `category_theory/opposite`.
#### Estimated changes
Modified src/algebraic_topology/simplicial_object.lean
- \+ *def* simplicial_cosimplicial_equiv
- \+ *def* simplicial_object.augmented.right_op
- \+ *def* cosimplicial_object.augmented.left_op
- \+ *def* simplicial_object.augmented.right_op_left_op_iso
- \+ *def* cosimplicial_object.augmented.left_op_right_op_iso
- \+ *def* simplicial_to_cosimplicial_augmented
- \+ *def* cosimplicial_to_simplicial_augmented
- \+ *def* simplicial_cosimplicial_augmented_equiv



## [2021-05-19 01:16:47](https://github.com/leanprover-community/mathlib/commit/24d2713)
feat(algebraic_topology/simplicial_object): Whiskering of simplicial objects. ([#7651](https://github.com/leanprover-community/mathlib/pull/7651))
This adds whiskering constructions for (truncated, augmented) (co)simplicial objects.
#### Estimated changes
Modified src/algebraic_topology/simplicial_object.lean
- \+ *def* whiskering
- \+ *def* whiskering_obj



## [2021-05-18 22:27:07](https://github.com/leanprover-community/mathlib/commit/0bcfff9)
feat(linear_algebra/basis) remove several [nontrivial R] ([#7642](https://github.com/leanprover-community/mathlib/pull/7642))
We remove some unnecessary `nontrivial R`.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+/\- *lemma* map_apply
- \+/\- *lemma* reindex_range_self
- \+/\- *lemma* reindex_range_repr_self
- \+/\- *lemma* reindex_range_apply
- \+/\- *lemma* reindex_range_repr'
- \+/\- *lemma* reindex_range_repr
- \+/\- *def* reindex_range

Modified src/linear_algebra/finsupp.lean
- \+ *def* module.subsingleton_equiv

Modified src/linear_algebra/matrix/to_lin.lean
- \+/\- *theorem* linear_map.to_matrix_reindex_range
- \+/\- *theorem* linear_map.to_matrix_alg_equiv_reindex_range



## [2021-05-18 16:02:45](https://github.com/leanprover-community/mathlib/commit/a51d1e0)
feat(algebra/homology/homological_complex): Dualizes some constructions ([#7643](https://github.com/leanprover-community/mathlib/pull/7643))
This PR adds `cochain_complex.of` and `cochain_complex.of_hom`. 
Still not done: `cochain_complex.mk`.
#### Estimated changes
Modified src/algebra/homology/homological_complex.lean
- \+ *lemma* of_X
- \+ *lemma* of_d
- \+ *lemma* of_d_ne
- \+ *def* of
- \+ *def* of_hom



## [2021-05-18 16:02:44](https://github.com/leanprover-community/mathlib/commit/e275604)
chore(data/set/basic): add `set.compl_eq_compl` ([#7641](https://github.com/leanprover-community/mathlib/pull/7641))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* compl_eq_compl



## [2021-05-18 10:47:24](https://github.com/leanprover-community/mathlib/commit/c2114d4)
refactor(linear_algebra/dimension): generalize definition of `module.rank` ([#7634](https://github.com/leanprover-community/mathlib/pull/7634))
The main change is to generalize the definition of `module.rank`. It used to be the infimum over cardinalities of bases, and is now the supremum over cardinalities of linearly independent sets.
I have not attempted to systematically generalize  theorems about the rank; there is lots more work to be done. For now I've just made a few easy generalizations (either replacing `field` with `division_ring`, or `division_ring` with `ring`+`nontrivial`).
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+/\- *lemma* reindex_range_apply
- \+/\- *theorem* vector_space.card_fintype

Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/linear_independent.lean
- \+/\- *lemma* linear_independent_unique_iff
- \+/\- *lemma* linear_independent_singleton
- \+/\- *lemma* linear_independent.insert

Modified src/ring_theory/principal_ideal_domain.lean




## [2021-05-18 10:47:23](https://github.com/leanprover-community/mathlib/commit/e6c787f)
feat(algebra/opposites): add `has_scalar (opposite α) α` instances ([#7630](https://github.com/leanprover-community/mathlib/pull/7630))
The action is defined as:
```lean
lemma op_smul_eq_mul [monoid α] {a a' : α} : op a • a' = a' * a := rfl
```
We have a few of places in the library where we prove things about `r • b`, and then extract a proof of `a * b = a • b` for free. However, we have no way to do this for `b * a` right now unless multiplication is commutative.
By adding this action, we have `b * a = op a • b` so in many cases could reuse the smul lemma.
This instance does not create a diamond:
```lean
-- the two paths to `mul_action (opposite α) (opposite α)` are defeq
example [monoid α] : monoid.to_mul_action (opposite α) = opposite.mul_action α (opposite α) := rfl
```
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Right.20multiplication.20as.20a.20mul_action/near/239012917)
#### Estimated changes
Modified src/algebra/module/opposites.lean


Modified src/algebra/opposites.lean
- \+ *lemma* op_smul_eq_mul



## [2021-05-18 04:50:02](https://github.com/leanprover-community/mathlib/commit/1a2781a)
feat(analysis/normed_space): the category of seminormed groups ([#7617](https://github.com/leanprover-community/mathlib/pull/7617))
From LTE, along with adding `SemiNormedGroup₁`, the subcategory of norm non-increasing maps.
#### Estimated changes
Created src/analysis/normed_space/SemiNormedGroup.lean
- \+ *lemma* coe_of
- \+ *lemma* coe_id
- \+ *lemma* hom_ext
- \+ *lemma* mk_hom_apply
- \+ *lemma* coe_comp
- \+ *lemma* zero_apply
- \+ *lemma* iso_isometry
- \+ *def* SemiNormedGroup
- \+ *def* of
- \+ *def* SemiNormedGroup₁
- \+ *def* mk_hom
- \+ *def* mk_iso

Modified src/analysis/normed_space/normed_group_hom.lean
- \+ *lemma* zero



## [2021-05-18 04:50:01](https://github.com/leanprover-community/mathlib/commit/3694945)
feat(logic/is_empty): Add is_empty typeclass ([#7606](https://github.com/leanprover-community/mathlib/pull/7606))
* Refactor some equivalences that use `empty` or `pempty`.
* Replace `α → false` with `is_empty α` in various places (but not everywhere, we can do that in follow-up PRs).
* `infinite` is proven equivalent to `is_empty (fintype α)`. The old `not_fintype` is renamed to `fintype.false` (to allow projection notation), and there are two useful variants `infinite.false` and `not_fintype` added with different arguments explicit.
* add instance `unique true`.
* Changed the type of `fin_one_equiv` from `fin 1 ≃ punit` to `fin 1 ≃ unit` (it was used only once, where the former formulation required giving an explicit universe level).
* renamings:
`equiv.subsingleton_iff` -> `equiv.subsingleton_congr`
`finprod_of_empty` -> `finprod_of_is_empty`
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_of_is_empty
- \- *lemma* finprod_of_empty

Modified src/algebra/homology/homological_complex.lean


Modified src/analysis/calculus/inverse.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/combinatorics/hall.lean


Modified src/data/equiv/basic.lean
- \+ *lemma* subsingleton_congr
- \+/\- *lemma* sum_empty_apply_inl
- \+/\- *lemma* empty_sum_apply_inr
- \+ *lemma* is_empty_congr
- \- *lemma* subsingleton_iff
- \- *lemma* sum_pempty_apply_inl
- \- *lemma* pempty_sum_apply_inr
- \+/\- *def* equiv_empty
- \+ *def* equiv_empty_equiv
- \+/\- *def* {u'
- \+/\- *def* fun_unique
- \+ *def* arrow_punit_of_is_empty
- \+/\- *def* sum_empty
- \+/\- *def* empty_sum
- \- *def* empty_of_not_nonempty
- \- *def* pempty_of_not_nonempty
- \- *def* sum_pempty
- \- *def* pempty_sum

Modified src/data/equiv/denumerable.lean


Modified src/data/equiv/fin.lean
- \+/\- *def* fin_one_equiv

Modified src/data/fin.lean


Modified src/data/fintype/basic.lean
- \+/\- *lemma* card_eq_zero_iff
- \+ *lemma* not_fintype
- \+ *lemma* is_empty_fintype
- \+/\- *lemma* not_nonempty_fintype
- \+ *def* card_eq_zero_equiv_equiv_empty
- \- *def* card_eq_zero_equiv_equiv_pempty

Modified src/data/option/basic.lean
- \+/\- *lemma* choice_eq_none

Modified src/data/polynomial/ring_division.lean


Modified src/data/set/basic.lean


Modified src/data/zmod/basic.lean


Modified src/field_theory/polynomial_galois_group.lean


Modified src/group_theory/specific_groups/cyclic.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/matrix/block.lean


Created src/logic/is_empty.lean
- \+ *lemma* is_empty_iff
- \+ *lemma* forall_iff
- \+ *lemma* exists_iff
- \+ *lemma* not_nonempty_iff
- \+ *lemma* not_is_empty_iff
- \+ *lemma* is_empty_or_nonempty
- \+ *lemma* not_is_empty_of_nonempty
- \+ *def* is_empty_elim

Modified src/logic/unique.lean
- \- *def* pi.unique_of_empty

Modified src/ring_theory/jacobson.lean


Modified src/set_theory/cardinal.lean
- \+ *lemma* eq_zero_iff_is_empty
- \+ *lemma* eq_one_iff_unique
- \- *lemma* eq_one_iff_subsingleton_and_nonempty

Modified src/set_theory/ordinal.lean


Modified src/set_theory/pgame.lean




## [2021-05-18 04:49:59](https://github.com/leanprover-community/mathlib/commit/1b864c0)
feat(analysis/normed_group): quotients ([#7603](https://github.com/leanprover-community/mathlib/pull/7603))
From LTE.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* mem_ball_0_iff

Created src/analysis/normed_space/normed_group_quotient.lean
- \+ *lemma* image_norm_nonempty
- \+ *lemma* bdd_below_image_norm
- \+ *lemma* quotient_norm_neg
- \+ *lemma* quotient_norm_sub_rev
- \+ *lemma* quotient_norm_mk_le
- \+ *lemma* quotient_norm_mk_eq
- \+ *lemma* quotient_norm_nonneg
- \+ *lemma* norm_mk_nonneg
- \+ *lemma* quotient_norm_eq_zero_iff
- \+ *lemma* norm_mk_lt
- \+ *lemma* norm_mk_lt'
- \+ *lemma* quotient_norm_add_le
- \+ *lemma* norm_mk_zero
- \+ *lemma* norm_zero_eq_zero
- \+ *lemma* quotient_nhd_basis
- \+ *lemma* normed_mk.apply
- \+ *lemma* surjective_normed_mk
- \+ *lemma* ker_normed_mk
- \+ *lemma* norm_normed_mk_le
- \+ *lemma* norm_normed_mk
- \+ *lemma* norm_trivial_quotient_mk
- \+ *lemma* lift_mk
- \+ *lemma* lift_unique
- \+ *lemma* is_quotient_quotient
- \+ *lemma* is_quotient.norm_lift
- \+ *lemma* is_quotient.norm_le
- \+ *def* normed_mk
- \+ *def* lift



## [2021-05-18 02:58:27](https://github.com/leanprover-community/mathlib/commit/f900513)
feat(linear_algebra/matrix): slightly generalize `smul_left_mul_matrix` ([#7632](https://github.com/leanprover-community/mathlib/pull/7632))
Two minor changes that make `smul_left_mul_matrix` slightly easier to apply:
 * the bases `b` and `c` can now be indexed by different types
 * replace `(i, k)` on the LHS with `ik.1 ik.2` on the RHS (so you don't have to introduce the constructor with `rw ← prod.mk.eta` somewhere deep in your expression)
#### Estimated changes
Modified src/linear_algebra/matrix/to_lin.lean
- \+/\- *lemma* smul_left_mul_matrix



## [2021-05-17 23:05:07](https://github.com/leanprover-community/mathlib/commit/b8a6995)
feat(data/polynomial): the `d-1`th coefficient of `polynomial.map` ([#7639](https://github.com/leanprover-community/mathlib/pull/7639))
We prove `polynomial.next_coeff_map` just like `polynomial.leading_coeff_map'`.
#### Estimated changes
Modified src/data/polynomial/degree/lemmas.lean
- \+ *lemma* next_coeff_map



## [2021-05-17 23:05:06](https://github.com/leanprover-community/mathlib/commit/ccf5188)
feat(ring_theory/power_basis): the dimension of a power basis is positive ([#7638](https://github.com/leanprover-community/mathlib/pull/7638))
We already have `pb.dim_ne_zero : pb.dim ≠ 0` (assuming nontriviality), but it's also useful to also have it in the form `0 < pb.dim`.
#### Estimated changes
Modified src/ring_theory/power_basis.lean
- \+ *lemma* dim_pos



## [2021-05-17 18:10:36](https://github.com/leanprover-community/mathlib/commit/4ab0e35)
feat(data/multiset): the product of inverses is the inverse of the product ([#7637](https://github.com/leanprover-community/mathlib/pull/7637))
Entirely analogous to `prod_map_mul` defined above.
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* prod_map_inv



## [2021-05-17 12:38:51](https://github.com/leanprover-community/mathlib/commit/818dffa)
feat(linear_algebra): a finite free module has a unique findim ([#7631](https://github.com/leanprover-community/mathlib/pull/7631))
I needed this easy corollary, so I PR'd it, even though it should be generalizable once we have a better theory of e.g. Gaussian elimination. (I also tried to generalize `mk_eq_mk_of_basis`, but the current proof really requires the existence of multiplicative inverses for the coefficients.)
#### Estimated changes
Modified src/linear_algebra/free_module.lean




## [2021-05-17 12:38:50](https://github.com/leanprover-community/mathlib/commit/36e0127)
feat(linear_algebra/basic): add_monoid_hom_lequiv_int ([#7629](https://github.com/leanprover-community/mathlib/pull/7629))
From LTE.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *lemma* map_nat_module_smul

Modified src/algebra/module/linear_map.lean
- \+ *def* add_monoid_hom.to_nat_linear_map

Modified src/linear_algebra/basic.lean
- \+ *def* add_monoid_hom_lequiv_nat
- \+ *def* add_monoid_hom_lequiv_int



## [2021-05-17 12:38:49](https://github.com/leanprover-community/mathlib/commit/d201a18)
refactor(algebra/homology/homotopy): avoid needing has_zero_object ([#7621](https://github.com/leanprover-community/mathlib/pull/7621))
A refactor of the definition of `homotopy`, so we don't need `has_zero_object`.
#### Estimated changes
Modified src/algebra/homology/homotopy.lean
- \+ *lemma* d_next_eq_d_from_from_next
- \+ *lemma* d_next_eq
- \+ *lemma* d_next_comp_left
- \+ *lemma* d_next_comp_right
- \+ *lemma* prev_d_eq_to_prev_d_to
- \+ *lemma* prev_d_eq
- \+ *lemma* prev_d_comp_left
- \+ *lemma* prev_d_chain_complex
- \+ *lemma* d_next_succ_chain_complex
- \+ *lemma* d_next_zero_chain_complex
- \- *lemma* from_next'_eq
- \- *lemma* from_next'_zero
- \- *lemma* from_next'_add
- \- *lemma* from_next'_neg
- \- *lemma* from_next'_comp_left
- \- *lemma* from_next'_comp_right
- \- *lemma* to_prev'_eq
- \- *lemma* to_prev'_zero
- \- *lemma* to_prev'_add
- \- *lemma* to_prev'_neg
- \- *lemma* to_prev'_comp_left
- \- *lemma* comm
- \- *lemma* to_prev'_chain_complex
- \- *lemma* from_next'_succ_chain_complex
- \- *lemma* from_next'_zero_chain_complex
- \+ *def* d_next
- \+/\- *def* from_next
- \+ *def* prev_d
- \+/\- *def* to_prev
- \- *def* from_next'
- \- *def* to_prev'



## [2021-05-17 12:38:49](https://github.com/leanprover-community/mathlib/commit/07fb3d7)
refactor(data/finsupp/antidiagonal): Make antidiagonal a finset ([#7595](https://github.com/leanprover-community/mathlib/pull/7595))
Pursuant to discussion [here](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/antidiagonals.20having.20multiplicity) 
Refactoring so that `finsupp.antidiagonal` and `multiset.antidiagonal` are finsets.
~~Still TO DO: `multiset.antidiagonal`~~
#### Estimated changes
Modified src/data/finsupp/antidiagonal.lean
- \+ *lemma* mem_antidiagonal
- \+ *lemma* swap_mem_antidiagonal
- \+ *lemma* antidiagonal_filter_fst_eq
- \+ *lemma* antidiagonal_filter_snd_eq
- \+/\- *lemma* antidiagonal_zero
- \+ *lemma* prod_antidiagonal_swap
- \- *lemma* mem_antidiagonal_support
- \- *lemma* swap_mem_antidiagonal_support
- \- *lemma* antidiagonal_support_filter_fst_eq
- \- *lemma* antidiagonal_support_filter_snd_eq
- \- *lemma* prod_antidiagonal_support_swap
- \+ *def* antidiagonal'
- \+/\- *def* antidiagonal

Modified src/data/mv_polynomial/basic.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/ring_theory/polynomial/homogeneous.lean


Modified src/ring_theory/power_series/basic.lean




## [2021-05-17 08:05:30](https://github.com/leanprover-community/mathlib/commit/8394e59)
feat(data/finset/basic): perm_of_nodup_nodup_to_finset_eq ([#7588](https://github.com/leanprover-community/mathlib/pull/7588))
Also `finset.exists_list_nodup_eq`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* nodup.to_finset_inj
- \+ *lemma* perm_of_nodup_nodup_to_finset_eq
- \+ *lemma* exists_list_nodup_eq



## [2021-05-17 06:01:44](https://github.com/leanprover-community/mathlib/commit/739d93c)
feat(algebra/lie/weights): the zero root subalgebra is self-normalizing ([#7622](https://github.com/leanprover-community/mathlib/pull/7622))
#### Estimated changes
Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* mem_mk_iff

Modified src/algebra/lie/weights.lean
- \+ *lemma* mem_zero_root_subalgebra
- \+ *lemma* zero_root_subalgebra_normalizer_eq_self
- \+ *lemma* zero_root_subalgebra_is_cartan_of_eq
- \+ *lemma* coe_weight_space'
- \+ *def* weight_space'



## [2021-05-17 03:57:28](https://github.com/leanprover-community/mathlib/commit/2077c90)
doc(counterexamples/canonically_ordered_comm_semiring_two_mul): fix url ([#7625](https://github.com/leanprover-community/mathlib/pull/7625))
#### Estimated changes
Modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean




## [2021-05-17 02:40:40](https://github.com/leanprover-community/mathlib/commit/d40e40c)
chore(scripts): update nolints.txt ([#7627](https://github.com/leanprover-community/mathlib/pull/7627))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-05-17 01:22:19](https://github.com/leanprover-community/mathlib/commit/72e4cca)
ci(.github/workflows/build.yml): check counterexamples ([#7618](https://github.com/leanprover-community/mathlib/pull/7618))
I meant to add this to [#7553](https://github.com/leanprover-community/mathlib/pull/7553) but I forgot before it got merged.
This also moves the contents of `src/counterexamples` to `counterexamples/`.
#### Estimated changes
Modified .github/workflows/build.yml


Renamed src/counterexamples/canonically_ordered_comm_semiring_two_mul.lean to counterexamples/canonically_ordered_comm_semiring_two_mul.lean


Renamed src/counterexamples/linear_order_with_pos_mul_pos_eq_zero.lean to counterexamples/linear_order_with_pos_mul_pos_eq_zero.lean


Modified scripts/lint-style.sh


Modified scripts/lint_style_sanity_test.py




## [2021-05-17 00:02:12](https://github.com/leanprover-community/mathlib/commit/84a27d6)
feat(set_theory/game): add mul_one and mul_assoc for pgames ([#7610](https://github.com/leanprover-community/mathlib/pull/7610))
and several `simp` lemmas. I also simplified some of the existing proofs using `rw` and `simp` and made them easier to read.
This is the final PR for multiplication of pgames (hopefully)!
Next step:  prove `numeric_mul` and define multiplication for `surreal`.
#### Estimated changes
Modified src/set_theory/game.lean
- \+/\- *lemma* quot_neg
- \+/\- *lemma* quot_add
- \+/\- *lemma* quot_sub
- \- *lemma* left_distrib_equiv_aux
- \- *lemma* left_distrib_equiv_aux'
- \+ *theorem* quot_eq_of_mk_quot_eq
- \+ *theorem* quot_mul_comm
- \+ *theorem* quot_mul_zero
- \+ *theorem* quot_zero_mul
- \+ *theorem* quot_neg_mul
- \+ *theorem* quot_mul_neg
- \+ *theorem* quot_left_distrib
- \+/\- *theorem* left_distrib_equiv
- \+ *theorem* quot_left_distrib_sub
- \+ *theorem* quot_right_distrib
- \+ *theorem* quot_right_distrib_sub
- \+ *theorem* quot_mul_one
- \+ *theorem* mul_one_equiv
- \+ *theorem* quot_one_mul
- \+ *theorem* one_mul_equiv
- \+ *theorem* quot_mul_assoc
- \+ *theorem* mul_assoc_equiv
- \- *def* mul_comm_relabelling



## [2021-05-16 18:58:53](https://github.com/leanprover-community/mathlib/commit/aedd12d)
refactor(measure_theory/haar_measure): move general material to content.lean, make content a structure  ([#7615](https://github.com/leanprover-community/mathlib/pull/7615))
Several facts that are proved only for the Haar measure (including for instance regularity) are true for any measure constructed from a content. We move these facts to the `content.lean` file (and make `content` a structure for easier management). Also, move the notion of regular measure to its own file, and make it a class.
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \- *lemma* outer_regular_eq
- \- *lemma* inner_regular_eq
- \- *lemma* exists_compact_not_null

Modified src/measure_theory/content.lean
- \+ *lemma* apply_eq_coe_to_fun
- \+ *lemma* mono
- \+ *lemma* sup_disjoint
- \+ *lemma* sup_le
- \+ *lemma* lt_top
- \+ *lemma* empty
- \+/\- *lemma* le_inner_content
- \+/\- *lemma* inner_content_le
- \+/\- *lemma* inner_content_of_is_compact
- \+/\- *lemma* inner_content_empty
- \+/\- *lemma* inner_content_mono
- \+/\- *lemma* inner_content_exists_compact
- \+/\- *lemma* inner_content_Sup_nat
- \+/\- *lemma* inner_content_Union_nat
- \+/\- *lemma* inner_content_comap
- \+/\- *lemma* is_mul_left_invariant_inner_content
- \+/\- *lemma* inner_content_mono'
- \+ *lemma* outer_measure_opens
- \+ *lemma* outer_measure_of_is_open
- \+ *lemma* outer_measure_le
- \+ *lemma* le_outer_measure_compacts
- \+ *lemma* outer_measure_eq_infi
- \+ *lemma* outer_measure_interior_compacts
- \+ *lemma* outer_measure_exists_compact
- \+ *lemma* outer_measure_exists_open
- \+ *lemma* outer_measure_preimage
- \+ *lemma* outer_measure_lt_top_of_is_compact
- \+ *lemma* is_mul_left_invariant_outer_measure
- \+ *lemma* outer_measure_caratheodory
- \+ *lemma* outer_measure_pos_of_is_mul_left_invariant
- \+ *lemma* borel_le_caratheodory
- \+ *lemma* measure_apply
- \- *lemma* of_content_opens
- \- *lemma* of_content_le
- \- *lemma* le_of_content_compacts
- \- *lemma* of_content_eq_infi
- \- *lemma* of_content_interior_compacts
- \- *lemma* of_content_exists_compact
- \- *lemma* of_content_exists_open
- \- *lemma* of_content_preimage
- \- *lemma* is_mul_left_invariant_of_content
- \- *lemma* of_content_caratheodory
- \- *lemma* of_content_pos_of_is_mul_left_invariant
- \+/\- *def* inner_content
- \+ *def* measure
- \- *def* of_content

Modified src/measure_theory/group.lean
- \+/\- *lemma* is_mul_left_invariant.null_iff_empty
- \+/\- *lemma* is_mul_left_invariant.null_iff
- \+/\- *lemma* is_mul_left_invariant.measure_ne_zero_iff_nonempty
- \+/\- *lemma* lintegral_eq_zero_of_is_mul_left_invariant
- \- *lemma* regular.inv

Modified src/measure_theory/haar_measure.lean
- \+ *lemma* haar_content_apply
- \+ *lemma* haar_content_self
- \+ *lemma* is_left_invariant_haar_content
- \+ *lemma* haar_content_outer_measure_self_pos
- \- *lemma* echaar_sup_le
- \- *lemma* echaar_mono
- \- *lemma* echaar_self
- \- *lemma* is_left_invariant_echaar
- \- *lemma* haar_outer_measure_eq_infi
- \- *lemma* echaar_le_haar_outer_measure
- \- *lemma* haar_outer_measure_of_is_open
- \- *lemma* haar_outer_measure_le_echaar
- \- *lemma* haar_outer_measure_exists_open
- \- *lemma* haar_outer_measure_exists_compact
- \- *lemma* haar_outer_measure_caratheodory
- \- *lemma* one_le_haar_outer_measure_self
- \- *lemma* haar_outer_measure_pos_of_is_open
- \- *lemma* haar_outer_measure_self_pos
- \- *lemma* haar_outer_measure_lt_top_of_is_compact
- \- *lemma* haar_caratheodory_measurable
- \- *lemma* regular_haar_measure
- \+ *def* haar_content
- \- *def* echaar
- \- *def* haar_outer_measure

Modified src/measure_theory/prod_group.lean


Created src/measure_theory/regular.lean
- \+ *lemma* outer_regular_eq
- \+ *lemma* inner_regular_eq
- \+ *lemma* exists_compact_not_null



## [2021-05-16 18:58:52](https://github.com/leanprover-community/mathlib/commit/1b098c0)
feat(algebra/ordered_group, algebra/ordered_ring): add some lemmas about abs ([#7612](https://github.com/leanprover-community/mathlib/pull/7612))
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* abs_choice
- \+ *lemma* eq_or_eq_neg_of_abs_eq
- \+ *lemma* abs_eq_abs

Modified src/algebra/ordered_ring.lean
- \+ *lemma* abs_dvd
- \+ *lemma* abs_dvd_self
- \+ *lemma* dvd_abs
- \+ *lemma* self_dvd_abs
- \+ *lemma* abs_dvd_abs
- \+ *lemma* even_abs



## [2021-05-16 18:58:51](https://github.com/leanprover-community/mathlib/commit/b98d840)
feat(category_theory/category): initialize simps ([#7605](https://github.com/leanprover-community/mathlib/pull/7605))
Initialize `@[simps]` so that it works better for `category`. It just makes the names of the generated lemmas shorter.
Add `@[simps]` to product categories.
#### Estimated changes
Modified src/category_theory/category/default.lean


Modified src/category_theory/products/basic.lean
- \- *lemma* prod_id_fst
- \- *lemma* prod_id_snd
- \- *lemma* prod_comp_fst
- \- *lemma* prod_comp_snd

Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean




## [2021-05-16 18:58:50](https://github.com/leanprover-community/mathlib/commit/9084a3c)
chore(order/fixed_point): add docstring for Knaster-Tarski theorem ([#7589](https://github.com/leanprover-community/mathlib/pull/7589))
clarify that the def provided constitutes the Knaster-Tarski theorem
#### Estimated changes
Modified src/order/countable_dense_linear_order.lean


Modified src/order/fixed_points.lean
- \+ *lemma* lfp_le
- \+ *lemma* le_lfp
- \+ *lemma* lfp_fixed_point
- \+ *lemma* lfp_induction
- \+ *lemma* monotone_lfp
- \+ *lemma* le_gfp
- \+ *lemma* gfp_le
- \+ *lemma* gfp_fixed_point
- \+ *lemma* gfp_induction
- \+ *lemma* monotone_gfp
- \+ *lemma* lfp_comp
- \+ *lemma* gfp_comp
- \+ *lemma* lfp_lfp
- \+ *lemma* gfp_gfp
- \+ *lemma* prev_le
- \+/\- *lemma* prev_eq
- \+ *lemma* le_next
- \+/\- *lemma* next_eq
- \+ *lemma* sup_le_f_of_fixed_points
- \+ *lemma* f_le_inf_of_fixed_points
- \+ *lemma* Sup_le_f_of_fixed_points
- \+ *lemma* f_le_Inf_of_fixed_points
- \- *theorem* lfp_le
- \- *theorem* le_lfp
- \- *theorem* lfp_eq
- \- *theorem* lfp_induct
- \- *theorem* monotone_lfp
- \- *theorem* le_gfp
- \- *theorem* gfp_le
- \- *theorem* gfp_eq
- \- *theorem* gfp_induct
- \- *theorem* monotone_gfp
- \- *theorem* lfp_comp
- \- *theorem* gfp_comp
- \- *theorem* lfp_lfp
- \- *theorem* gfp_gfp
- \- *theorem* prev_le
- \- *theorem* next_le
- \- *theorem* sup_le_f_of_fixed_points
- \- *theorem* f_le_inf_of_fixed_points
- \- *theorem* Sup_le_f_of_fixed_points
- \- *theorem* f_le_Inf_of_fixed_points

Modified src/set_theory/schroeder_bernstein.lean




## [2021-05-16 13:18:13](https://github.com/leanprover-community/mathlib/commit/c8a2fd7)
feat(analysis/normed_space): normed_group punit ([#7616](https://github.com/leanprover-community/mathlib/pull/7616))
Minor content from LTE.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* punit.norm_eq_zero

Modified src/topology/metric_space/basic.lean


Modified src/topology/uniform_space/basic.lean




## [2021-05-16 13:18:12](https://github.com/leanprover-community/mathlib/commit/2bd4bb6)
fix(tactic/lift): elaborate the type better ([#7598](https://github.com/leanprover-community/mathlib/pull/7598))
* When writing `lift x to t` it will now elaborating `t` using that `t` must be a sort (inserting a coercion if needed).
* Generalize `Type*` to `Sort*` in the tactic
#### Estimated changes
Modified src/tactic/lift.lean


Created test/lift.lean




## [2021-05-16 13:18:11](https://github.com/leanprover-community/mathlib/commit/632783d)
feat(algebra/subalgebra): two equal subalgebras are equivalent ([#7590](https://github.com/leanprover-community/mathlib/pull/7590))
This extends `linear_equiv.of_eq` to an `alg_equiv` between two `subalgebra`s.
[Zulip discussion starts around here](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/towers.20of.20algebras/near/238452076)
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* equiv_of_eq_symm
- \+ *lemma* equiv_of_eq_rfl
- \+ *lemma* equiv_of_eq_trans
- \+ *def* equiv_of_eq



## [2021-05-16 13:18:10](https://github.com/leanprover-community/mathlib/commit/4d909f4)
feat(analysis/calculus/local_extr): A polynomial's roots are bounded by its derivative ([#7571](https://github.com/leanprover-community/mathlib/pull/7571))
An application of Rolle's theorem to polynomials.
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+ *lemma* ring_hom.char_zero
- \+ *lemma* ring_hom.char_zero_iff

Modified src/analysis/calculus/local_extr.lean
- \+ *lemma* card_root_set_le_derivative

Modified src/data/finset/sort.lean
- \+ *lemma* card_le_of_interleaved



## [2021-05-16 13:18:09](https://github.com/leanprover-community/mathlib/commit/ee6a9fa)
fix(tactic/simps): fix bug ([#7433](https://github.com/leanprover-community/mathlib/pull/7433))
* Custom projections that were compositions of multiple projections failed when the projection has additional arguments.
* Also adds an error when two projections are given the same simps-name
#### Estimated changes
Modified src/tactic/simps.lean


Modified test/simps.lean
- \+ *def* another_term
- \+ *def* something.simps.apply
- \+ *def* something2.simps.mul
- \+ *def* thing



## [2021-05-16 13:18:08](https://github.com/leanprover-community/mathlib/commit/f1bcb90)
fix(tactic/simps): remove occurrence of mk_mapp ([#7432](https://github.com/leanprover-community/mathlib/pull/7432))
Fixes the slowdown reported on Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/simps.20is.20very.20slow
On my laptop, the minimized example in that topic now takes 33ms instead of ~5000ms
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/simps.lean


Modified test/simps.lean
- \+ *def* foo_sum



## [2021-05-15 21:20:58](https://github.com/leanprover-community/mathlib/commit/65e7646)
feat(algebraic_topology): cosimplicial objects ([#7614](https://github.com/leanprover-community/mathlib/pull/7614))
Dualize the existing API for `simplicial_object` to provide `cosimplicial_object`, and move the contents of LTE's `for_mathlib/simplicial/augmented.lean` to mathlib.
#### Estimated changes
Modified src/algebraic_topology/simplicial_object.lean
- \+ *lemma* eq_to_iso_refl
- \+ *lemma* δ_comp_δ
- \+ *lemma* δ_comp_δ_self
- \+ *lemma* δ_comp_σ_of_le
- \+ *lemma* δ_comp_σ_self
- \+ *lemma* δ_comp_σ_succ
- \+ *lemma* δ_comp_σ_of_gt
- \+ *lemma* σ_comp_σ
- \+ *def* drop
- \+ *def* point
- \+ *def* cosimplicial_object
- \+ *def* δ
- \+ *def* σ
- \+ *def* eq_to_iso
- \+ *def* truncated
- \+ *def* sk
- \+ *def* augmented



## [2021-05-15 21:20:57](https://github.com/leanprover-community/mathlib/commit/14802d6)
chore(ring_theory/int/basic): remove duplicate lemma nat.prime_iff_prime ([#7611](https://github.com/leanprover-community/mathlib/pull/7611))
#### Estimated changes
Modified src/data/nat/multiplicity.lean


Modified src/ring_theory/int/basic.lean
- \- *lemma* nat.prime_iff_prime

Modified src/ring_theory/roots_of_unity.lean




## [2021-05-15 21:20:56](https://github.com/leanprover-community/mathlib/commit/07dcff7)
feat(logic/relation): reflexive.ne_iff_imp ([#7579](https://github.com/leanprover-community/mathlib/pull/7579))
As suggested in [#7567](https://github.com/leanprover-community/mathlib/pull/7567)
#### Estimated changes
Modified src/logic/relation.lean
- \+ *lemma* is_refl.reflexive
- \+ *lemma* reflexive.rel_of_ne_imp
- \+ *lemma* reflexive.ne_imp_iff
- \+ *lemma* reflexive_ne_imp_iff



## [2021-05-15 21:20:55](https://github.com/leanprover-community/mathlib/commit/82ac80f)
feat(data/set/basic): pairwise_on.imp_on ([#7578](https://github.com/leanprover-community/mathlib/pull/7578))
Provide more helper lemmas for transferring `pairwise_on` between different relations. Provide a rephrase of `pairwise_on.mono'` as `pairwise_on.imp`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* pairwise_on_of_forall
- \+ *lemma* pairwise_on.imp_on
- \+ *lemma* pairwise_on.imp
- \+ *theorem* pairwise_on_top



## [2021-05-15 21:20:54](https://github.com/leanprover-community/mathlib/commit/4c2567f)
chore(group_theory/group_action/group): add `smul_inv` ([#7568](https://github.com/leanprover-community/mathlib/pull/7568))
This renames the existing `smul_inv` to `smul_inv'`, which is consistent with the name of the other lemma about `mul_semiring_action`, `smul_mul'`.
#### Estimated changes
Modified src/algebra/group_ring_action.lean
- \+ *lemma* smul_inv'
- \- *lemma* smul_inv

Modified src/field_theory/fixed.lean


Modified src/field_theory/galois.lean


Modified src/group_theory/group_action/group.lean
- \+ *lemma* smul_inv



## [2021-05-15 21:20:53](https://github.com/leanprover-community/mathlib/commit/467d2b2)
feat(data/logic/basic): `em.swap` and `eq_or_ne` ([#7561](https://github.com/leanprover-community/mathlib/pull/7561))
#### Estimated changes
Modified src/logic/basic.lean
- \+ *theorem* dec_em'
- \+/\- *theorem* em
- \+ *theorem* em'
- \+/\- *theorem* or_not
- \+ *theorem* decidable.eq_or_ne
- \+ *theorem* decidable.ne_or_eq
- \+ *theorem* eq_or_ne
- \+ *theorem* ne_or_eq

Modified src/tactic/lint/type_classes.lean




## [2021-05-15 21:20:52](https://github.com/leanprover-community/mathlib/commit/d338ebd)
feat(counterexamples/*): add counterexamples folder ([#7558](https://github.com/leanprover-community/mathlib/pull/7558))
Several times, there has been a discussion on Zulip about the appropriateness of having counterexamples in mathlib.  This PR introduces a `counterexamples` folder, together with the first couple of counterexamples.
For the most recent discussion, see
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.237553
#### Estimated changes
Created src/counterexamples/canonically_ordered_comm_semiring_two_mul.lean
- \+ *lemma* mem_zmod_2
- \+ *lemma* add_self_zmod_2
- \+ *lemma* lt_def
- \+ *lemma* add_left_cancel
- \+ *lemma* add_le_add_left
- \+ *lemma* le_of_add_le_add_left
- \+ *lemma* zero_le_one
- \+ *lemma* mul_lt_mul_of_pos_left
- \+ *lemma* mul_lt_mul_of_pos_right
- \+ *lemma* add_L
- \+ *lemma* mul_L
- \+ *lemma* bot_le
- \+ *lemma* lt_of_add_lt_add_left
- \+ *lemma* le_iff_exists_add
- \+ *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \+ *def* K
- \+ *def* L

Created src/counterexamples/linear_order_with_pos_mul_pos_eq_zero.lean
- \+ *lemma* aux1_inj
- \+ *lemma* not_mul_pos
- \+ *def* aux1
- \+ *def* mul



## [2021-05-15 21:20:51](https://github.com/leanprover-community/mathlib/commit/56442cf)
feat(data/nnreal): div and pow lemmas ([#7471](https://github.com/leanprover-community/mathlib/pull/7471))
from the liquid tensor experiment
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* pow_mono_decr_exp
- \+ *lemma* div_le_div_left_of_le
- \+ *lemma* div_le_div_left



## [2021-05-15 21:20:50](https://github.com/leanprover-community/mathlib/commit/57b0e68)
chore(*/pi): rename *_hom.apply to pi.eval_*_hom ([#5851](https://github.com/leanprover-community/mathlib/pull/5851))
These definitions state the fact that fixing an `i` and applying a function `(Π i, f i)` maintains the algebraic structure of the function. We already have a name for this operation, `function.eval`.
These isn't a statement about `monoid_hom` or `ring_hom` at all - that just happens to be their type.
For this reason, this commit moves all the definitions of this type into the `pi` namespace:
* `add_monoid_hom.apply` &rarr; `pi.eval_add_monoid_hom`
* `monoid_hom.apply` &rarr; `pi.eval_monoid_hom`
* `ring_hom.apply` &rarr; `pi.eval_ring_hom`
* `pi.alg_hom.apply` [sic] &rarr; `pi.eval_alg_hom`
This scales better, because we might want to say that applying a `linear_map` over a non-commutative ring is an `add_monoid_hom`. Using the naming convention established by this commit, that's easy; it's `linear_map.eval_add_monoid_hom` to mirror `pi.apply_add_monoid_hom`.
This partially addresses [this zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Naming.3A.20eval.20vs.20apply/near/223813950)
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* eval_alg_hom
- \- *def* alg_hom.apply

Modified src/algebra/big_operators/pi.lean


Modified src/algebra/category/Group/biproducts.lean


Modified src/algebra/char_p/pi.lean


Modified src/algebra/group/pi.lean
- \- *lemma* monoid_hom.apply_apply
- \+ *def* pi.eval_monoid_hom
- \- *def* monoid_hom.apply

Modified src/algebra/ring/pi.lean
- \- *lemma* ring_hom.apply_apply
- \+ *def* eval_ring_hom
- \- *def* ring_hom.apply

Modified src/data/dfinsupp.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/linear_algebra/quadratic_form.lean


Modified src/ring_theory/witt_vector/basic.lean
- \+/\- *def* ghost_component



## [2021-05-15 16:28:06](https://github.com/leanprover-community/mathlib/commit/172195b)
feat(algebra/{ordered_monoid, ordered_monoid_lemmas}): split the `ordered_[...]` typeclasses ([#7371](https://github.com/leanprover-community/mathlib/pull/7371))
This PR tries to split the ordering assumptions from the algebraic assumptions on the operations in the `ordered_[...]` hierarchy.
The strategy is to introduce two more flexible typeclasses, `covariant_class` and `contravariant_class`.
* `covariant_class` models the implication `a ≤ b → c * a ≤ c * b` (multiplication is monotone),
* `contravariant_class` models the implication `a * b < a * c → b < c`.
Since `co(ntra)variant_class` takes as input the operation (typically `(+)` or `(*)`) and the order relation (typically `(≤)` or `(<)`), these are the only two typeclasses that I have used.
The general approach is to formulate the lemma that you are interested in and prove it, with the `ordered_[...]` typeclass of your liking.  After that, you convert the single typeclass, say `[ordered_cancel_monoid M]`, to three typeclasses, e.g. `[partial_order M] [left_cancel_semigroup M] [covariant_class M M (function.swap (*)) (≤)]` and have a go at seeing if the proof still works!
Note that it is possible (or even expected) to combine several `co(ntra)variant_class` assumptions together.  Indeed, the usual `ordered` typeclasses arise from assuming the pair `[covariant_class M M (*) (≤)] [contravariant_class M M (*) (<)]` on top of order/algebraic assumptions.
A formal remark is that *normally* `covariant_class` uses the `(≤)`-relation, while `contravariant_class` uses the `(<)`-relation.  This need not be the case in general, but seems to be the most common usage.  In the opposite direction, the implication
`[semigroup α] [partial_order α] [contravariant_class α α (*) (≤)]  => left_cancel_semigroup α`
holds (note the `co*ntra*` assumption and the `(≤)`-relation).
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/ordered.20stuff
#### Estimated changes
Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_monoid.lean
- \+/\- *lemma* zero_lt_coe
- \+/\- *lemma* mul_le_mul_left
- \+/\- *lemma* lt_of_mul_lt_mul_left
- \- *lemma* mul_le_mul_left'
- \- *lemma* mul_le_mul_right'
- \- *lemma* mul_lt_of_mul_lt_left
- \- *lemma* mul_lt_of_mul_lt_right
- \- *lemma* mul_le_of_mul_le_left
- \- *lemma* mul_le_of_mul_le_right
- \- *lemma* lt_mul_of_lt_mul_left
- \- *lemma* lt_mul_of_lt_mul_right
- \- *lemma* le_mul_of_le_mul_left
- \- *lemma* le_mul_of_le_mul_right
- \- *lemma* lt_of_mul_lt_mul_left'
- \- *lemma* lt_of_mul_lt_mul_right'
- \- *lemma* mul_le_mul'
- \- *lemma* mul_le_mul_three
- \- *lemma* le_mul_of_one_le_right'
- \- *lemma* le_mul_of_one_le_left'
- \- *lemma* mul_le_of_le_one_right'
- \- *lemma* mul_le_of_le_one_left'
- \- *lemma* lt_of_mul_lt_of_one_le_left
- \- *lemma* lt_of_mul_lt_of_one_le_right
- \- *lemma* le_of_mul_le_of_one_le_left
- \- *lemma* le_of_mul_le_of_one_le_right
- \- *lemma* lt_of_lt_mul_of_le_one_left
- \- *lemma* lt_of_lt_mul_of_le_one_right
- \- *lemma* le_of_le_mul_of_le_one_left
- \- *lemma* le_of_le_mul_of_le_one_right
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
- \- *lemma* pos_of_gt
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
- \+/\- *def* function.injective.ordered_comm_monoid

Created src/algebra/ordered_monoid_lemmas.lean
- \+ *lemma* lt_of_mul_lt_mul_left'
- \+ *lemma* mul_le_mul_left'
- \+ *lemma* mul_lt_of_mul_lt_left
- \+ *lemma* mul_le_of_mul_le_left
- \+ *lemma* lt_mul_of_lt_mul_left
- \+ *lemma* le_mul_of_le_mul_left
- \+ *lemma* le_mul_of_one_le_right'
- \+ *lemma* mul_le_of_le_one_right'
- \+ *lemma* lt_of_mul_lt_of_one_le_left
- \+ *lemma* le_of_mul_le_of_one_le_left
- \+ *lemma* lt_of_lt_mul_of_le_one_left
- \+ *lemma* le_of_le_mul_of_le_one_left
- \+ *lemma* lt_of_mul_lt_mul_right'
- \+ *lemma* mul_le_mul_right'
- \+ *lemma* mul_lt_of_mul_lt_right
- \+ *lemma* mul_le_of_mul_le_right
- \+ *lemma* lt_mul_of_lt_mul_right
- \+ *lemma* le_mul_of_le_mul_right
- \+ *lemma* le_mul_of_one_le_left'
- \+ *lemma* mul_le_of_le_one_left'
- \+ *lemma* lt_of_mul_lt_of_one_le_right
- \+ *lemma* le_of_mul_le_of_one_le_right
- \+ *lemma* lt_of_lt_mul_of_le_one_right
- \+ *lemma* le_of_le_mul_of_le_one_right
- \+ *lemma* mul_le_mul'
- \+ *lemma* mul_le_mul_three
- \+ *lemma* one_lt_mul_of_lt_of_le'
- \+ *lemma* one_lt_mul'
- \+ *lemma* lt_mul_of_lt_of_one_le'
- \+ *lemma* lt_mul_of_lt_of_one_lt'
- \+ *lemma* one_lt_mul_of_le_of_lt'
- \+ *lemma* lt_mul_of_one_le_of_lt'
- \+ *lemma* lt_mul_of_one_lt_of_lt'
- \+ *lemma* le_mul_of_one_le_of_le
- \+ *lemma* le_mul_of_le_of_one_le
- \+ *lemma* one_le_mul
- \+ *lemma* mul_le_one'
- \+ *lemma* mul_le_of_le_one_of_le'
- \+ *lemma* mul_le_of_le_of_le_one'
- \+ *lemma* mul_lt_one_of_lt_one_of_le_one'
- \+ *lemma* mul_lt_one_of_le_one_of_lt_one'
- \+ *lemma* mul_lt_one'
- \+ *lemma* mul_lt_of_le_one_of_lt'
- \+ *lemma* mul_lt_of_lt_of_le_one'
- \+ *lemma* mul_lt_of_lt_one_of_lt'
- \+ *lemma* mul_lt_of_lt_of_lt_one'
- \+ *lemma* mul_eq_one_iff'
- \+ *lemma* monotone.mul'
- \+ *lemma* monotone.mul_const'
- \+ *lemma* monotone.const_mul'
- \+ *lemma* le_of_mul_le_mul_left'
- \+ *lemma* le_of_mul_le_mul_right'
- \+ *lemma* mul_lt_mul_left'
- \+ *lemma* lt_mul_of_one_lt_right'
- \+ *lemma* mul_le_mul_iff_left
- \+ *lemma* mul_lt_mul_iff_left
- \+ *lemma* le_mul_iff_one_le_right'
- \+ *lemma* lt_mul_iff_one_lt_right'
- \+ *lemma* mul_le_iff_le_one_right'
- \+ *lemma* mul_lt_iff_lt_one_left'
- \+ *lemma* mul_lt_mul_right'
- \+ *lemma* lt_mul_of_one_lt_left'
- \+ *lemma* mul_le_mul_iff_right
- \+ *lemma* mul_lt_mul_iff_right
- \+ *lemma* le_mul_iff_one_le_left'
- \+ *lemma* lt_mul_iff_one_lt_left'
- \+ *lemma* mul_le_iff_le_one_left'
- \+ *lemma* mul_lt_iff_lt_one_right'
- \+ *lemma* mul_lt_mul_of_lt_of_le
- \+ *lemma* mul_lt_one_of_lt_one_of_le_one
- \+ *lemma* lt_mul_of_one_lt_of_le
- \+ *lemma* mul_le_of_le_one_of_le
- \+ *lemma* mul_le_of_le_of_le_one
- \+ *lemma* mul_lt_of_lt_one_of_le
- \+ *lemma* lt_mul_of_lt_of_one_le
- \+ *lemma* mul_lt_of_lt_of_le_one
- \+ *lemma* mul_lt_mul_of_le_of_lt
- \+ *lemma* mul_lt_one_of_le_one_of_lt_one
- \+ *lemma* lt_mul_of_le_of_one_lt
- \+ *lemma* mul_lt_of_le_of_lt_one
- \+ *lemma* lt_mul_of_one_le_of_lt
- \+ *lemma* mul_lt_of_le_one_of_lt
- \+ *lemma* mul_lt_mul'''
- \+ *lemma* mul_eq_one_iff_eq_one_of_one_le
- \+ *lemma* mul_lt_one
- \+ *lemma* lt_mul_of_one_lt_of_lt
- \+ *lemma* lt_mul_of_lt_of_one_lt
- \+ *lemma* mul_lt_of_lt_one_of_lt
- \+ *lemma* mul_lt_of_lt_of_lt_one
- \+ *def* covariant
- \+ *def* contravariant

Modified src/algebra/ordered_ring.lean


Modified src/data/int/basic.lean


Modified src/data/multiset/basic.lean


Modified src/data/real/nnreal.lean


Modified src/measure_theory/measure_space.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean




## [2021-05-15 14:21:15](https://github.com/leanprover-community/mathlib/commit/738c19f)
refactor(linear_algebra/matrix): split matrix.lean into multiple files ([#7593](https://github.com/leanprover-community/mathlib/pull/7593))
The file `linear_algebra/matrix.lean` used to be very big and contain a lot of parts that did not depend on each other, so I split each of those parts into its own little file. Most of the new files ended up in `linear_algebra/matrix/`, except for `linear_algebra/trace.lean` and `linear_algebra/determinant.lean` which did not contain anything matrix-specific.
Apart from the local improvement in `matrix.lean` itself, the import graph is now also a bit cleaner.
Renames:
 * `linear_algebra/determinant.lean` -> `linear_algebra/matrix/determinant.lean`
 * `linear_algebra/nonsingular_inverse.lean` -> `linear_algebra/matrix/nonsingular_inverse.lean`
Split off from `linear_algebra/matrix.lean`:
 * `linear_algebra/matrix/basis.lean`
 * `linear_algebra/matrix/block.lean`
 * `linear_algebra/matrix/diagonal.lean`
 * `linear_algebra/matrix/dot_product.lean`
 * `linear_algebra/matrix/dual.lean`
 * `linear_algebra/matrix/finite_dimensional.lean`
 * `linear_algebra/matrix/reindex.lean`
 * `linear_algebra/matrix/to_lin.lean`
 * `linear_algebra/matrix/to_linear_equiv.lean`
 * `linear_algebra/matrix/trace.lean`
 * `linear_algebra/determinant.lean` (Unfortunately, I could not persuade `git` to remember that I moved the original `determinant.lean` to `matrix/determinant.lean`)
  * `linear_algebra/trace.lean`
#### Estimated changes
Modified src/algebra/lie/classical.lean


Modified src/algebra/lie/matrix.lean


Modified src/analysis/calculus/lagrange_multipliers.lean


Modified src/combinatorics/simple_graph/adj_matrix.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/tower.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/char_poly/basic.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/determinant.lean
- \+ *lemma* linear_equiv.is_unit_det
- \+ *lemma* basis.det_apply
- \+ *lemma* basis.det_self
- \+ *lemma* is_basis.iff_det
- \- *lemma* det_apply
- \- *lemma* det_apply'
- \- *lemma* det_diagonal
- \- *lemma* det_zero
- \- *lemma* det_one
- \- *lemma* det_eq_one_of_card_eq_zero
- \- *lemma* det_fin_zero
- \- *lemma* det_unique
- \- *lemma* det_eq_elem_of_card_eq_one
- \- *lemma* det_mul_aux
- \- *lemma* det_mul
- \- *lemma* det_transpose
- \- *lemma* det_permute
- \- *lemma* det_minor_equiv_self
- \- *lemma* det_reindex_self
- \- *lemma* det_permutation
- \- *lemma* det_smul
- \- *lemma* det_mul_row
- \- *lemma* det_mul_column
- \- *lemma* ring_hom.map_det
- \- *lemma* alg_hom.map_det
- \- *lemma* det_eq_zero_of_row_eq_zero
- \- *lemma* det_eq_zero_of_column_eq_zero
- \- *lemma* det_update_row_add
- \- *lemma* det_update_column_add
- \- *lemma* det_update_row_smul
- \- *lemma* det_update_column_smul
- \- *lemma* det_eq_of_eq_mul_det_one
- \- *lemma* det_eq_of_eq_det_one_mul
- \- *lemma* det_update_row_add_self
- \- *lemma* det_update_column_add_self
- \- *lemma* det_update_row_add_smul_self
- \- *lemma* det_update_column_add_smul_self
- \- *lemma* det_eq_of_forall_row_eq_smul_add_const_aux
- \- *lemma* det_eq_of_forall_row_eq_smul_add_const
- \- *lemma* det_eq_of_forall_row_eq_smul_add_pred_aux
- \- *lemma* det_eq_of_forall_row_eq_smul_add_pred
- \- *lemma* det_eq_of_forall_col_eq_smul_add_pred
- \- *lemma* det_block_diagonal
- \- *lemma* upper_two_block_triangular_det
- \- *lemma* det_succ_column_zero
- \- *lemma* det_succ_row_zero
- \- *lemma* det_succ_row
- \- *lemma* det_succ_column
- \- *theorem* det_zero_of_row_eq
- \- *theorem* det_zero_of_column_eq
- \+ *def* linear_equiv.of_is_unit_det
- \+ *def* basis.det
- \- *def* det_row_multilinear

Modified src/linear_algebra/eigenspace.lean


Deleted src/linear_algebra/matrix.lean
- \- *lemma* matrix.mul_vec_lin_apply
- \- *lemma* matrix.mul_vec_std_basis
- \- *lemma* linear_map.to_matrix'_symm
- \- *lemma* matrix.to_lin'_symm
- \- *lemma* linear_map.to_matrix'_to_lin'
- \- *lemma* matrix.to_lin'_to_matrix'
- \- *lemma* linear_map.to_matrix'_apply
- \- *lemma* matrix.to_lin'_apply
- \- *lemma* matrix.to_lin'_one
- \- *lemma* linear_map.to_matrix'_id
- \- *lemma* matrix.to_lin'_mul
- \- *lemma* linear_map.to_matrix'_comp
- \- *lemma* linear_map.to_matrix'_mul
- \- *lemma* linear_map.to_matrix_alg_equiv'_symm
- \- *lemma* matrix.to_lin_alg_equiv'_symm
- \- *lemma* linear_map.to_matrix_alg_equiv'_to_lin_alg_equiv'
- \- *lemma* matrix.to_lin_alg_equiv'_to_matrix_alg_equiv'
- \- *lemma* linear_map.to_matrix_alg_equiv'_apply
- \- *lemma* matrix.to_lin_alg_equiv'_apply
- \- *lemma* matrix.to_lin_alg_equiv'_one
- \- *lemma* linear_map.to_matrix_alg_equiv'_id
- \- *lemma* matrix.to_lin_alg_equiv'_mul
- \- *lemma* linear_map.to_matrix_alg_equiv'_comp
- \- *lemma* linear_map.to_matrix_alg_equiv'_mul
- \- *lemma* linear_map.to_matrix_symm
- \- *lemma* matrix.to_lin_symm
- \- *lemma* matrix.to_lin_to_matrix
- \- *lemma* linear_map.to_matrix_to_lin
- \- *lemma* linear_map.to_matrix_apply
- \- *lemma* linear_map.to_matrix_transpose_apply
- \- *lemma* linear_map.to_matrix_apply'
- \- *lemma* linear_map.to_matrix_transpose_apply'
- \- *lemma* matrix.to_lin_apply
- \- *lemma* matrix.to_lin_self
- \- *lemma* linear_map.to_matrix_id
- \- *lemma* linear_map.to_matrix_one
- \- *lemma* matrix.to_lin_one
- \- *lemma* linear_map.to_matrix_comp
- \- *lemma* linear_map.to_matrix_mul
- \- *lemma* linear_map.to_matrix_mul_vec_repr
- \- *lemma* matrix.to_lin_mul
- \- *lemma* linear_map.to_matrix_alg_equiv_symm
- \- *lemma* matrix.to_lin_alg_equiv_symm
- \- *lemma* matrix.to_lin_alg_equiv_to_matrix_alg_equiv
- \- *lemma* linear_map.to_matrix_alg_equiv_to_lin_alg_equiv
- \- *lemma* linear_map.to_matrix_alg_equiv_apply
- \- *lemma* linear_map.to_matrix_alg_equiv_transpose_apply
- \- *lemma* linear_map.to_matrix_alg_equiv_apply'
- \- *lemma* linear_map.to_matrix_alg_equiv_transpose_apply'
- \- *lemma* matrix.to_lin_alg_equiv_apply
- \- *lemma* matrix.to_lin_alg_equiv_self
- \- *lemma* linear_map.to_matrix_alg_equiv_id
- \- *lemma* matrix.to_lin_alg_equiv_one
- \- *lemma* linear_map.to_matrix_alg_equiv_comp
- \- *lemma* linear_map.to_matrix_alg_equiv_mul
- \- *lemma* matrix.to_lin_alg_equiv_mul
- \- *lemma* to_matrix_apply
- \- *lemma* to_matrix_transpose_apply
- \- *lemma* to_matrix_eq_to_matrix_constr
- \- *lemma* to_matrix_self
- \- *lemma* to_matrix_update
- \- *lemma* sum_to_matrix_smul_self
- \- *lemma* to_lin_to_matrix
- \- *lemma* basis_to_matrix_mul_linear_map_to_matrix
- \- *lemma* linear_map_to_matrix_mul_basis_to_matrix
- \- *lemma* linear_map.to_matrix_id_eq_basis_to_matrix
- \- *lemma* basis.to_matrix_mul_to_matrix
- \- *lemma* linear_equiv.is_unit_det
- \- *lemma* basis.det_apply
- \- *lemma* basis.det_self
- \- *lemma* is_basis.iff_det
- \- *lemma* linear_map.to_matrix_transpose
- \- *lemma* matrix.to_lin_transpose
- \- *lemma* diag_apply
- \- *lemma* diag_one
- \- *lemma* diag_transpose
- \- *lemma* trace_diag
- \- *lemma* trace_apply
- \- *lemma* trace_one
- \- *lemma* trace_transpose
- \- *lemma* trace_transpose_mul
- \- *lemma* trace_mul_comm
- \- *lemma* proj_diagonal
- \- *lemma* diagonal_comp_std_basis
- \- *lemma* diagonal_to_lin'
- \- *lemma* to_linear_equiv'_apply
- \- *lemma* to_linear_equiv'_symm_apply
- \- *lemma* rank_vec_mul_vec
- \- *lemma* ker_diagonal_to_lin'
- \- *lemma* range_diagonal
- \- *lemma* rank_diagonal
- \- *lemma* ker_to_lin_eq_bot
- \- *lemma* range_to_lin_eq_top
- \- *lemma* finrank_matrix
- \- *lemma* reindex_linear_equiv_apply
- \- *lemma* reindex_linear_equiv_symm
- \- *lemma* reindex_linear_equiv_refl_refl
- \- *lemma* reindex_alg_equiv_apply
- \- *lemma* reindex_alg_equiv_symm
- \- *lemma* reindex_alg_equiv_refl
- \- *lemma* det_reindex_linear_equiv_self
- \- *lemma* det_reindex_alg_equiv
- \- *lemma* to_matrix_lmul'
- \- *lemma* to_matrix_lsmul
- \- *lemma* left_mul_matrix_apply
- \- *lemma* left_mul_matrix_eq_repr_mul
- \- *lemma* left_mul_matrix_mul_vec_repr
- \- *lemma* to_matrix_lmul_eq
- \- *lemma* left_mul_matrix_injective
- \- *lemma* smul_left_mul_matrix
- \- *lemma* smul_left_mul_matrix_algebra_map
- \- *lemma* smul_left_mul_matrix_algebra_map_eq
- \- *lemma* smul_left_mul_matrix_algebra_map_ne
- \- *lemma* trace_aux_def
- \- *lemma* finrank_linear_map
- \- *lemma* matrix.dot_product_std_basis_eq_mul
- \- *lemma* matrix.dot_product_std_basis_one
- \- *lemma* matrix.dot_product_eq
- \- *lemma* matrix.dot_product_eq_iff
- \- *lemma* matrix.dot_product_eq_zero
- \- *lemma* matrix.dot_product_eq_zero_iff
- \- *lemma* det_to_block
- \- *lemma* det_to_square_block
- \- *lemma* det_to_square_block'
- \- *lemma* two_block_triangular_det
- \- *lemma* equiv_block_det
- \- *lemma* to_square_block_det''
- \- *lemma* upper_two_block_triangular'
- \- *lemma* upper_two_block_triangular
- \- *lemma* det_of_block_triangular_matrix
- \- *lemma* det_of_block_triangular_matrix''
- \- *lemma* det_of_block_triangular_matrix'
- \- *lemma* det_of_upper_triangular
- \- *lemma* det_of_lower_triangular
- \- *theorem* linear_map.to_matrix_reindex_range
- \- *theorem* linear_map.to_matrix_alg_equiv_reindex_range
- \- *theorem* trace_aux_eq
- \- *theorem* trace_aux_reindex_range
- \- *theorem* trace_eq_matrix_trace_of_finite_set
- \- *theorem* trace_eq_matrix_trace
- \- *theorem* trace_mul_comm
- \- *def* matrix.mul_vec_lin
- \- *def* linear_map.to_matrix'
- \- *def* matrix.to_lin'
- \- *def* linear_map.to_matrix_alg_equiv'
- \- *def* matrix.to_lin_alg_equiv'
- \- *def* linear_map.to_matrix
- \- *def* matrix.to_lin
- \- *def* linear_map.to_matrix_alg_equiv
- \- *def* matrix.to_lin_alg_equiv
- \- *def* basis.to_matrix
- \- *def* to_matrix_equiv
- \- *def* linear_equiv.of_is_unit_det
- \- *def* basis.det
- \- *def* diag
- \- *def* trace
- \- *def* to_linear_equiv'
- \- *def* to_linear_equiv
- \- *def* reindex_linear_equiv
- \- *def* reindex_alg_equiv
- \- *def* trace_aux
- \- *def* alg_equiv_matrix'
- \- *def* linear_equiv.alg_conj
- \- *def* alg_equiv_matrix
- \- *def* block_triangular_matrix'
- \- *def* block_triangular_matrix

Created src/linear_algebra/matrix/basis.lean
- \+ *lemma* to_matrix_apply
- \+ *lemma* to_matrix_transpose_apply
- \+ *lemma* to_matrix_eq_to_matrix_constr
- \+ *lemma* to_matrix_self
- \+ *lemma* to_matrix_update
- \+ *lemma* sum_to_matrix_smul_self
- \+ *lemma* to_lin_to_matrix
- \+ *lemma* basis_to_matrix_mul_linear_map_to_matrix
- \+ *lemma* linear_map_to_matrix_mul_basis_to_matrix
- \+ *lemma* linear_map.to_matrix_id_eq_basis_to_matrix
- \+ *lemma* basis.to_matrix_mul_to_matrix
- \+ *def* basis.to_matrix
- \+ *def* to_matrix_equiv

Created src/linear_algebra/matrix/block.lean
- \+ *lemma* det_to_block
- \+ *lemma* det_to_square_block
- \+ *lemma* det_to_square_block'
- \+ *lemma* two_block_triangular_det
- \+ *lemma* equiv_block_det
- \+ *lemma* to_square_block_det''
- \+ *lemma* upper_two_block_triangular'
- \+ *lemma* upper_two_block_triangular
- \+ *lemma* det_of_block_triangular_matrix
- \+ *lemma* det_of_block_triangular_matrix''
- \+ *lemma* det_of_block_triangular_matrix'
- \+ *lemma* det_of_upper_triangular
- \+ *lemma* det_of_lower_triangular
- \+ *def* block_triangular_matrix'
- \+ *def* block_triangular_matrix

Created src/linear_algebra/matrix/default.lean


Created src/linear_algebra/matrix/determinant.lean
- \+ *lemma* det_apply
- \+ *lemma* det_apply'
- \+ *lemma* det_diagonal
- \+ *lemma* det_zero
- \+ *lemma* det_one
- \+ *lemma* det_eq_one_of_card_eq_zero
- \+ *lemma* det_fin_zero
- \+ *lemma* det_unique
- \+ *lemma* det_eq_elem_of_card_eq_one
- \+ *lemma* det_mul_aux
- \+ *lemma* det_mul
- \+ *lemma* det_transpose
- \+ *lemma* det_permute
- \+ *lemma* det_minor_equiv_self
- \+ *lemma* det_reindex_self
- \+ *lemma* det_permutation
- \+ *lemma* det_smul
- \+ *lemma* det_mul_row
- \+ *lemma* det_mul_column
- \+ *lemma* ring_hom.map_det
- \+ *lemma* alg_hom.map_det
- \+ *lemma* det_eq_zero_of_row_eq_zero
- \+ *lemma* det_eq_zero_of_column_eq_zero
- \+ *lemma* det_update_row_add
- \+ *lemma* det_update_column_add
- \+ *lemma* det_update_row_smul
- \+ *lemma* det_update_column_smul
- \+ *lemma* det_eq_of_eq_mul_det_one
- \+ *lemma* det_eq_of_eq_det_one_mul
- \+ *lemma* det_update_row_add_self
- \+ *lemma* det_update_column_add_self
- \+ *lemma* det_update_row_add_smul_self
- \+ *lemma* det_update_column_add_smul_self
- \+ *lemma* det_eq_of_forall_row_eq_smul_add_const_aux
- \+ *lemma* det_eq_of_forall_row_eq_smul_add_const
- \+ *lemma* det_eq_of_forall_row_eq_smul_add_pred_aux
- \+ *lemma* det_eq_of_forall_row_eq_smul_add_pred
- \+ *lemma* det_eq_of_forall_col_eq_smul_add_pred
- \+ *lemma* det_block_diagonal
- \+ *lemma* upper_two_block_triangular_det
- \+ *lemma* det_succ_column_zero
- \+ *lemma* det_succ_row_zero
- \+ *lemma* det_succ_row
- \+ *lemma* det_succ_column
- \+ *theorem* det_zero_of_row_eq
- \+ *theorem* det_zero_of_column_eq
- \+ *def* det_row_multilinear

Created src/linear_algebra/matrix/diagonal.lean
- \+ *lemma* proj_diagonal
- \+ *lemma* diagonal_comp_std_basis
- \+ *lemma* diagonal_to_lin'
- \+ *lemma* ker_diagonal_to_lin'
- \+ *lemma* range_diagonal
- \+ *lemma* rank_diagonal

Created src/linear_algebra/matrix/dot_product.lean
- \+ *lemma* dot_product_std_basis_eq_mul
- \+ *lemma* dot_product_std_basis_one
- \+ *lemma* dot_product_eq
- \+ *lemma* dot_product_eq_iff
- \+ *lemma* dot_product_eq_zero
- \+ *lemma* dot_product_eq_zero_iff

Created src/linear_algebra/matrix/dual.lean
- \+ *lemma* linear_map.to_matrix_transpose
- \+ *lemma* matrix.to_lin_transpose

Created src/linear_algebra/matrix/finite_dimensional.lean
- \+ *lemma* finrank_matrix

Renamed src/linear_algebra/nonsingular_inverse.lean to src/linear_algebra/matrix/nonsingular_inverse.lean


Created src/linear_algebra/matrix/reindex.lean
- \+ *lemma* reindex_linear_equiv_apply
- \+ *lemma* reindex_linear_equiv_symm
- \+ *lemma* reindex_linear_equiv_refl_refl
- \+ *lemma* reindex_alg_equiv_apply
- \+ *lemma* reindex_alg_equiv_symm
- \+ *lemma* reindex_alg_equiv_refl
- \+ *lemma* det_reindex_linear_equiv_self
- \+ *lemma* det_reindex_alg_equiv
- \+ *def* reindex_linear_equiv
- \+ *def* reindex_alg_equiv

Created src/linear_algebra/matrix/to_lin.lean
- \+ *lemma* matrix.mul_vec_lin_apply
- \+ *lemma* matrix.mul_vec_std_basis
- \+ *lemma* linear_map.to_matrix'_symm
- \+ *lemma* matrix.to_lin'_symm
- \+ *lemma* linear_map.to_matrix'_to_lin'
- \+ *lemma* matrix.to_lin'_to_matrix'
- \+ *lemma* linear_map.to_matrix'_apply
- \+ *lemma* matrix.to_lin'_apply
- \+ *lemma* matrix.to_lin'_one
- \+ *lemma* linear_map.to_matrix'_id
- \+ *lemma* matrix.to_lin'_mul
- \+ *lemma* linear_map.to_matrix'_comp
- \+ *lemma* linear_map.to_matrix'_mul
- \+ *lemma* linear_map.to_matrix_alg_equiv'_symm
- \+ *lemma* matrix.to_lin_alg_equiv'_symm
- \+ *lemma* linear_map.to_matrix_alg_equiv'_to_lin_alg_equiv'
- \+ *lemma* matrix.to_lin_alg_equiv'_to_matrix_alg_equiv'
- \+ *lemma* linear_map.to_matrix_alg_equiv'_apply
- \+ *lemma* matrix.to_lin_alg_equiv'_apply
- \+ *lemma* matrix.to_lin_alg_equiv'_one
- \+ *lemma* linear_map.to_matrix_alg_equiv'_id
- \+ *lemma* matrix.to_lin_alg_equiv'_mul
- \+ *lemma* linear_map.to_matrix_alg_equiv'_comp
- \+ *lemma* linear_map.to_matrix_alg_equiv'_mul
- \+ *lemma* matrix.rank_vec_mul_vec
- \+ *lemma* linear_map.to_matrix_symm
- \+ *lemma* matrix.to_lin_symm
- \+ *lemma* matrix.to_lin_to_matrix
- \+ *lemma* linear_map.to_matrix_to_lin
- \+ *lemma* linear_map.to_matrix_apply
- \+ *lemma* linear_map.to_matrix_transpose_apply
- \+ *lemma* linear_map.to_matrix_apply'
- \+ *lemma* linear_map.to_matrix_transpose_apply'
- \+ *lemma* matrix.to_lin_apply
- \+ *lemma* matrix.to_lin_self
- \+ *lemma* linear_map.to_matrix_id
- \+ *lemma* linear_map.to_matrix_one
- \+ *lemma* matrix.to_lin_one
- \+ *lemma* linear_map.to_matrix_comp
- \+ *lemma* linear_map.to_matrix_mul
- \+ *lemma* linear_map.to_matrix_mul_vec_repr
- \+ *lemma* matrix.to_lin_mul
- \+ *lemma* linear_map.to_matrix_alg_equiv_symm
- \+ *lemma* matrix.to_lin_alg_equiv_symm
- \+ *lemma* matrix.to_lin_alg_equiv_to_matrix_alg_equiv
- \+ *lemma* linear_map.to_matrix_alg_equiv_to_lin_alg_equiv
- \+ *lemma* linear_map.to_matrix_alg_equiv_apply
- \+ *lemma* linear_map.to_matrix_alg_equiv_transpose_apply
- \+ *lemma* linear_map.to_matrix_alg_equiv_apply'
- \+ *lemma* linear_map.to_matrix_alg_equiv_transpose_apply'
- \+ *lemma* matrix.to_lin_alg_equiv_apply
- \+ *lemma* matrix.to_lin_alg_equiv_self
- \+ *lemma* linear_map.to_matrix_alg_equiv_id
- \+ *lemma* matrix.to_lin_alg_equiv_one
- \+ *lemma* linear_map.to_matrix_alg_equiv_comp
- \+ *lemma* linear_map.to_matrix_alg_equiv_mul
- \+ *lemma* matrix.to_lin_alg_equiv_mul
- \+ *lemma* to_matrix_lmul'
- \+ *lemma* to_matrix_lsmul
- \+ *lemma* left_mul_matrix_apply
- \+ *lemma* left_mul_matrix_eq_repr_mul
- \+ *lemma* left_mul_matrix_mul_vec_repr
- \+ *lemma* to_matrix_lmul_eq
- \+ *lemma* left_mul_matrix_injective
- \+ *lemma* smul_left_mul_matrix
- \+ *lemma* smul_left_mul_matrix_algebra_map
- \+ *lemma* smul_left_mul_matrix_algebra_map_eq
- \+ *lemma* smul_left_mul_matrix_algebra_map_ne
- \+ *lemma* finrank_linear_map
- \+ *theorem* linear_map.to_matrix_reindex_range
- \+ *theorem* linear_map.to_matrix_alg_equiv_reindex_range
- \+ *def* matrix.mul_vec_lin
- \+ *def* linear_map.to_matrix'
- \+ *def* matrix.to_lin'
- \+ *def* linear_map.to_matrix_alg_equiv'
- \+ *def* matrix.to_lin_alg_equiv'
- \+ *def* linear_map.to_matrix
- \+ *def* matrix.to_lin
- \+ *def* linear_map.to_matrix_alg_equiv
- \+ *def* matrix.to_lin_alg_equiv
- \+ *def* alg_equiv_matrix'
- \+ *def* linear_equiv.alg_conj
- \+ *def* alg_equiv_matrix

Created src/linear_algebra/matrix/to_linear_equiv.lean
- \+ *lemma* to_linear_equiv'_apply
- \+ *lemma* to_linear_equiv'_symm_apply
- \+ *lemma* ker_to_lin_eq_bot
- \+ *lemma* range_to_lin_eq_top

Created src/linear_algebra/matrix/trace.lean
- \+ *lemma* diag_apply
- \+ *lemma* diag_one
- \+ *lemma* diag_transpose
- \+ *lemma* trace_diag
- \+ *lemma* trace_apply
- \+ *lemma* trace_one
- \+ *lemma* trace_transpose
- \+ *lemma* trace_transpose_mul
- \+ *lemma* trace_mul_comm
- \+ *def* diag
- \+ *def* trace

Modified src/linear_algebra/quadratic_form.lean


Modified src/linear_algebra/special_linear_group.lean


Created src/linear_algebra/trace.lean
- \+ *lemma* trace_aux_def
- \+ *theorem* trace_aux_eq
- \+ *theorem* trace_aux_reindex_range
- \+ *theorem* trace_eq_matrix_trace_of_finite_set
- \+ *theorem* trace_eq_matrix_trace
- \+ *theorem* trace_mul_comm
- \+ *def* trace_aux
- \+ *def* trace

Modified src/linear_algebra/unitary_group.lean


Modified src/linear_algebra/vandermonde.lean


Modified src/ring_theory/trace.lean


Modified test/matrix.lean




## [2021-05-15 14:21:14](https://github.com/leanprover-community/mathlib/commit/3c27e2e)
feat(algebra/lie/weights): define product of root vectors and weight vectors ([#7591](https://github.com/leanprover-community/mathlib/pull/7591))
Also some related results, most notably that the zero root space is a subalgebra.
#### Estimated changes
Modified src/algebra/lie/abelian.lean


Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* _root_.lie_module_hom.coe_restrict_lie
- \+ *def* _root_.lie_module_hom.restrict_lie

Modified src/algebra/lie/submodule.lean
- \+ *lemma* coe_zero
- \+ *lemma* coe_add
- \+ *lemma* coe_neg
- \+ *lemma* coe_sub
- \+ *lemma* coe_smul
- \+ *lemma* coe_bracket
- \+ *lemma* coe_to_lie_submodule
- \+ *lemma* mem_to_lie_submodule
- \+/\- *lemma* exists_lie_ideal_coe_eq_iff
- \+ *def* to_lie_submodule

Modified src/algebra/lie/weights.lean
- \+ *lemma* lie_mem_weight_space_of_mem_weight_space
- \+ *lemma* coe_root_space_weight_space_product_tmul
- \+ *lemma* root_space_product_def
- \+ *lemma* root_space_product_tmul
- \+ *lemma* coe_zero_root_subalgebra
- \+ *lemma* to_lie_submodule_le_root_space_zero
- \+ *lemma* le_zero_root_subalgebra
- \+ *def* root_space_weight_space_product
- \+ *def* root_space_product
- \+ *def* zero_root_subalgebra



## [2021-05-15 14:21:13](https://github.com/leanprover-community/mathlib/commit/515762a)
feat(category_theory/quotient): congruence relations ([#7501](https://github.com/leanprover-community/mathlib/pull/7501))
Define congruence relations and show that when you quotient a category by a congruence relation, two morphism become equal iff they are related.
#### Estimated changes
Modified src/category_theory/quotient.lean
- \+ *lemma* functor_map_eq_iff
- \+ *def* hom_rel



## [2021-05-15 08:16:35](https://github.com/leanprover-community/mathlib/commit/fc94b47)
feat(counterexamples): a counterexample on the Pettis integral ([#7553](https://github.com/leanprover-community/mathlib/pull/7553))
Phillips (1940) has exhibited under the continuum hypothesis a bounded weakly measurable function which is not Pettis-integrable. We formalize this counterexample.
#### Estimated changes
Created counterexamples/phillips.lean
- \+ *lemma* exists_linear_extension_to_bounded_functions
- \+ *lemma* extension_to_bounded_functions_apply
- \+ *lemma* additive
- \+ *lemma* abs_le_bound
- \+ *lemma* le_bound
- \+ *lemma* empty
- \+ *lemma* neg_apply
- \+ *lemma* restrict_apply
- \+ *lemma* exists_discrete_support_nonpos
- \+ *lemma* exists_discrete_support
- \+ *lemma* countable_discrete_support
- \+ *lemma* apply_countable
- \+ *lemma* eq_add_parts
- \+ *lemma* discrete_part_apply
- \+ *lemma* continuous_part_apply_eq_zero_of_countable
- \+ *lemma* continuous_part_apply_diff
- \+ *lemma* norm_indicator_le_one
- \+ *lemma* continuous_part_eval_clm_eq_zero
- \+ *lemma* to_functions_to_measure
- \+ *lemma* to_functions_to_measure_continuous_part
- \+ *lemma* countable_compl_spf
- \+ *lemma* countable_spf_mem
- \+ *lemma* apply_f_eq_continuous_part
- \+ *lemma* countable_ne
- \+ *lemma* comp_ae_eq_const
- \+ *lemma* integrable_comp
- \+ *lemma* integral_comp
- \+ *lemma* measurable_comp
- \+ *lemma* norm_bound
- \+ *theorem* sierpinski_pathological_family
- \+ *theorem* no_pettis_integral
- \+ *def* discrete_copy
- \+ *def* bounded_integrable_functions
- \+ *def* bounded_integrable_functions_integral_clm
- \+ *def* _root_.measure_theory.measure.extension_to_bounded_functions
- \+ *def* C
- \+ *def* restrict
- \+ *def* discrete_support
- \+ *def* discrete_part
- \+ *def* continuous_part
- \+ *def* _root_.continuous_linear_map.to_bounded_additive_measure
- \+ *def* spf
- \+ *def* f

Modified docs/references.bib


Modified src/data/set/basic.lean
- \+ *lemma* diff_union_inter
- \+ *lemma* union_eq_diff_union_diff_union_inter
- \- *lemma* union_eq_sdiff_union_sdiff_union_inter

Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/lp_space.lean


Modified src/measure_theory/measurable_space.lean
- \+ *lemma* set.countable.measurable_set
- \+ *lemma* measurable.measurable_of_countable_ne

Modified src/measure_theory/measure_space.lean
- \+ *lemma* _root_.set.countable.measure_zero
- \+ *lemma* _root_.set.finite.measure_zero
- \+ *lemma* _root_.finset.measure_zero
- \- *lemma* measure_countable
- \- *lemma* measure_finite
- \- *lemma* measure_finset

Modified src/set_theory/cardinal_ordinal.lean
- \+ *lemma* countable_iff_lt_aleph_one

Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* coe_of_normed_group
- \+ *lemma* coe_of_normed_group_discrete
- \+ *lemma* eval_clm_apply
- \+/\- *theorem* continuous_eval
- \+/\- *theorem* continuous_evalx
- \+ *def* eval_clm



## [2021-05-15 08:16:34](https://github.com/leanprover-community/mathlib/commit/b4b38da)
feat(category_theory/*/projective): refactor treatment of projective objects ([#7485](https://github.com/leanprover-community/mathlib/pull/7485))
#### Estimated changes
Modified src/algebra/homology/exact.lean


Modified src/algebra/homology/homological_complex.lean


Modified src/algebra/homology/image_to_kernel.lean


Modified src/category_theory/abelian/non_preadditive.lean


Modified src/category_theory/abelian/projective.lean
- \- *lemma* factor_thru_comp
- \- *lemma* of_iso
- \- *lemma* iso_iff
- \- *def* factor_thru
- \- *def* over
- \- *def* π
- \- *def* left

Modified src/category_theory/closed/zero.lean


Modified src/category_theory/differential_object.lean


Modified src/category_theory/graded_object.lean


Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/preadditive/additive_functor.lean


Modified src/category_theory/preadditive/default.lean


Created src/category_theory/preadditive/projective.lean
- \+ *lemma* factor_thru_comp
- \+ *lemma* of_iso
- \+ *lemma* iso_iff
- \+ *lemma* exact.lift_comp
- \+ *def* factor_thru
- \+ *def* over
- \+ *def* π
- \+ *def* syzygies
- \+ *def* exact.lift

Modified src/category_theory/simple.lean


Modified src/category_theory/subobject/lattice.lean


Modified src/category_theory/triangulated/basic.lean




## [2021-05-15 08:16:32](https://github.com/leanprover-community/mathlib/commit/c63caeb)
feat(algebra/homology): homotopies between chain maps ([#7483](https://github.com/leanprover-community/mathlib/pull/7483))
#### Estimated changes
Modified src/algebra/homology/additive.lean


Created src/algebra/homology/homotopy.lean
- \+ *lemma* from_next'_eq
- \+ *lemma* from_next'_zero
- \+ *lemma* from_next'_add
- \+ *lemma* from_next'_neg
- \+ *lemma* from_next'_comp_left
- \+ *lemma* from_next'_comp_right
- \+ *lemma* to_prev'_eq
- \+ *lemma* to_prev'_zero
- \+ *lemma* to_prev'_add
- \+ *lemma* to_prev'_neg
- \+ *lemma* to_prev'_comp_left
- \+ *lemma* to_prev'_comp_right
- \+ *lemma* comm
- \+ *lemma* to_prev'_chain_complex
- \+ *lemma* from_next'_succ_chain_complex
- \+ *lemma* from_next'_zero_chain_complex
- \+ *lemma* mk_inductive_aux₃
- \+ *theorem* homology_map_eq_of_homotopy
- \+ *def* from_next'
- \+ *def* to_prev'
- \+ *def* from_next
- \+ *def* to_prev
- \+ *def* equiv_sub_zero
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans
- \+ *def* comp_right
- \+ *def* comp_left
- \+ *def* comp_right_id
- \+ *def* comp_left_id
- \+ *def* mk_inductive_aux₁
- \+ *def* mk_inductive_aux₂
- \+ *def* mk_inductive
- \+ *def* homology_obj_iso_of_homotopy_equiv
- \+ *def* functor.map_homotopy
- \+ *def* functor.map_homotopy_equiv



## [2021-05-15 08:16:31](https://github.com/leanprover-community/mathlib/commit/cc47aff)
feat(algebra/homology): truncation and augmentation of chain complexes ([#7480](https://github.com/leanprover-community/mathlib/pull/7480))
#### Estimated changes
Created src/algebra/homology/augment.lean
- \+ *lemma* augment_X_zero
- \+ *lemma* augment_X_succ
- \+ *lemma* augment_d_one_zero
- \+ *lemma* augment_d_succ_succ
- \+ *lemma* truncate_augment_hom_f
- \+ *lemma* truncate_augment_inv_f
- \+ *lemma* cochain_complex_d_succ_succ_zero
- \+ *lemma* augment_truncate_hom_f_zero
- \+ *lemma* augment_truncate_hom_f_succ
- \+ *lemma* augment_truncate_inv_f_zero
- \+ *lemma* augment_truncate_inv_f_succ
- \+ *def* truncate
- \+ *def* truncate_to
- \+ *def* augment
- \+ *def* truncate_augment
- \+ *def* augment_truncate
- \+ *def* to_single₀_as_complex



## [2021-05-15 08:16:30](https://github.com/leanprover-community/mathlib/commit/5da114c)
feat(algebraic_topology): the Moore complex of a simplicial object ([#6308](https://github.com/leanprover-community/mathlib/pull/6308))
## Moore complex
We construct the normalized Moore complex, as a functor
`simplicial_object C ⥤ chain_complex C ℕ`,
for any abelian category `C`.
The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.
The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.
This functor is one direction of the Dold-Kan equivalence, which we're still working towards.
#### Estimated changes
Modified src/algebra/homology/homological_complex.lean
- \+ *lemma* of_d_ne
- \+ *def* of_hom

Created src/algebraic_topology/Moore_complex.lean
- \+ *lemma* d_squared
- \+ *def* obj_X
- \+ *def* obj_d
- \+ *def* obj
- \+ *def* map
- \+ *def* normalized_Moore_complex



## [2021-05-15 03:59:57](https://github.com/leanprover-community/mathlib/commit/94aae73)
feat(data/nat/factorial) : descending factorial ([#7527](https://github.com/leanprover-community/mathlib/pull/7527))
#### Estimated changes
Modified src/data/nat/choose/basic.lean
- \+ *lemma* desc_fac_eq_factorial_mul_choose
- \+ *lemma* factorial_dvd_desc_fac
- \+ *lemma* choose_eq_desc_fac_div_factorial

Modified src/data/nat/factorial.lean
- \+ *lemma* desc_fac_zero
- \+ *lemma* zero_desc_fac
- \+ *lemma* desc_fac_succ
- \+ *lemma* succ_desc_fac
- \+ *lemma* desc_fac_eq_div
- \+ *theorem* factorial_mul_desc_fac
- \+ *def* desc_fac

Modified src/ring_theory/polynomial/bernstein.lean
- \- *lemma* iterate_derivative_at_0_aux₁
- \- *lemma* iterate_derivative_at_0_aux₂

Modified src/ring_theory/polynomial/pochhammer.lean
- \+ *lemma* pochhammer_nat_eq_desc_fac
- \+ *lemma* pochhammer_nat_eval_succ
- \+ *lemma* pochhammer_eval_succ
- \- *lemma* pochhammer_eval_one'
- \- *lemma* factorial_mul_pochhammer'
- \- *lemma* pochhammer_eval_eq_factorial_div_factorial
- \- *lemma* pochhammer_eval_eq_choose_mul_factorial
- \- *lemma* choose_eq_pochhammer_eval_div_factorial



## [2021-05-15 02:43:25](https://github.com/leanprover-community/mathlib/commit/a648af4)
chore(scripts): update nolints.txt ([#7613](https://github.com/leanprover-community/mathlib/pull/7613))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-05-14 22:42:57](https://github.com/leanprover-community/mathlib/commit/bd923f7)
chore(geometry/euclidean/triangle): minor style fixes ([#7585](https://github.com/leanprover-community/mathlib/pull/7585))
#### Estimated changes
Modified src/geometry/euclidean/triangle.lean




## [2021-05-14 19:19:41](https://github.com/leanprover-community/mathlib/commit/fd3d117)
feat(data/mv_polynomial/basic): Add ring section ([#7507](https://github.com/leanprover-community/mathlib/pull/7507))
A few lemmas about `monomial` analogous to those for the single-variate polynomials over rings.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* single_nat_sub
- \+ *lemma* single_neg
- \+/\- *lemma* single_sub

Modified src/data/mv_polynomial/basic.lean


Modified src/data/mv_polynomial/comm_ring.lean
- \+ *lemma* monomial_neg
- \+ *lemma* monomial_sub



## [2021-05-14 17:28:32](https://github.com/leanprover-community/mathlib/commit/a52f471)
feat(algebra/homology): chain complexes are an additive category ([#7478](https://github.com/leanprover-community/mathlib/pull/7478))
#### Estimated changes
Created src/algebra/homology/additive.lean
- \+ *lemma* zero_f_apply
- \+ *lemma* add_f_apply
- \+ *lemma* neg_f_apply
- \+ *lemma* sub_f_apply
- \+ *lemma* nat_trans.map_homological_complex_id
- \+ *lemma* nat_trans.map_homological_complex_comp
- \+ *lemma* nat_trans.map_homological_complex_naturality
- \+ *lemma* single_map_homological_complex_hom_app_self
- \+ *lemma* single_map_homological_complex_hom_app_ne
- \+ *lemma* single_map_homological_complex_inv_app_self
- \+ *lemma* single_map_homological_complex_inv_app_ne
- \+ *lemma* single₀_map_homological_complex_hom_app_zero
- \+ *lemma* single₀_map_homological_complex_hom_app_succ
- \+ *lemma* single₀_map_homological_complex_inv_app_zero
- \+ *lemma* single₀_map_homological_complex_inv_app_succ
- \+ *def* functor.map_homological_complex
- \+ *def* nat_trans.map_homological_complex
- \+ *def* single_map_homological_complex
- \+ *def* single₀_map_homological_complex

Modified src/algebra/homology/single.lean




## [2021-05-14 14:25:23](https://github.com/leanprover-community/mathlib/commit/f8dc722)
refactor(topology/algebra/ordered): reduce imports ([#7601](https://github.com/leanprover-community/mathlib/pull/7601))
Renames `topology.algebra.ordered` to `topology.algebra.order`, and moves the material about `liminf/limsup` and about `extend_from` to separate files, in order to delay imports.
#### Estimated changes
Modified src/algebra/continued_fractions/computation/approximation_corollaries.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/normed_space/basic.lean


Modified src/topology/algebra/floor_ring.lean


Renamed src/topology/algebra/ordered.lean to src/topology/algebra/ordered/basic.lean
- \- *lemma* is_bounded_le_nhds
- \- *lemma* filter.tendsto.is_bounded_under_le
- \- *lemma* is_cobounded_ge_nhds
- \- *lemma* filter.tendsto.is_cobounded_under_ge
- \- *lemma* is_bounded_ge_nhds
- \- *lemma* filter.tendsto.is_bounded_under_ge
- \- *lemma* is_cobounded_le_nhds
- \- *lemma* filter.tendsto.is_cobounded_under_le
- \- *lemma* continuous_on_Icc_extend_from_Ioo
- \- *lemma* eq_lim_at_left_extend_from_Ioo
- \- *lemma* eq_lim_at_right_extend_from_Ioo
- \- *lemma* continuous_on_Ico_extend_from_Ioo
- \- *lemma* continuous_on_Ioc_extend_from_Ioo
- \- *theorem* lt_mem_sets_of_Limsup_lt
- \- *theorem* gt_mem_sets_of_Liminf_gt
- \- *theorem* le_nhds_of_Limsup_eq_Liminf
- \- *theorem* Limsup_nhds
- \- *theorem* Liminf_nhds
- \- *theorem* Liminf_eq_of_le_nhds
- \- *theorem* Limsup_eq_of_le_nhds
- \- *theorem* filter.tendsto.limsup_eq
- \- *theorem* filter.tendsto.liminf_eq
- \- *theorem* tendsto_of_liminf_eq_limsup
- \- *theorem* tendsto_of_le_liminf_of_limsup_le

Created src/topology/algebra/ordered/extend_from.lean
- \+ *lemma* continuous_on_Icc_extend_from_Ioo
- \+ *lemma* eq_lim_at_left_extend_from_Ioo
- \+ *lemma* eq_lim_at_right_extend_from_Ioo
- \+ *lemma* continuous_on_Ico_extend_from_Ioo
- \+ *lemma* continuous_on_Ioc_extend_from_Ioo

Created src/topology/algebra/ordered/liminf_limsup.lean
- \+ *lemma* is_bounded_le_nhds
- \+ *lemma* filter.tendsto.is_bounded_under_le
- \+ *lemma* is_cobounded_ge_nhds
- \+ *lemma* filter.tendsto.is_cobounded_under_ge
- \+ *lemma* is_bounded_ge_nhds
- \+ *lemma* filter.tendsto.is_bounded_under_ge
- \+ *lemma* is_cobounded_le_nhds
- \+ *lemma* filter.tendsto.is_cobounded_under_le
- \+ *theorem* lt_mem_sets_of_Limsup_lt
- \+ *theorem* gt_mem_sets_of_Liminf_gt
- \+ *theorem* le_nhds_of_Limsup_eq_Liminf
- \+ *theorem* Limsup_nhds
- \+ *theorem* Liminf_nhds
- \+ *theorem* Liminf_eq_of_le_nhds
- \+ *theorem* Limsup_eq_of_le_nhds
- \+ *theorem* filter.tendsto.limsup_eq
- \+ *theorem* filter.tendsto.liminf_eq
- \+ *theorem* tendsto_of_liminf_eq_limsup
- \+ *theorem* tendsto_of_le_liminf_of_limsup_le

Modified src/topology/algebra/ordered/proj_Icc.lean


Modified src/topology/continuous_function/basic.lean


Renamed src/topology/extend_from_subset.lean to src/topology/extend_from.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/topological_fiber_bundle.lean




## [2021-05-14 14:25:22](https://github.com/leanprover-community/mathlib/commit/2373ee6)
refactor(set_theory/{surreal, game}): move `mul` from surreal to game ([#7580](https://github.com/leanprover-community/mathlib/pull/7580))
The next step is to provide several `simp` lemmas for multiplication of pgames in terms of games.
None of these statements involve surreal numbers.
#### Estimated changes
Modified src/set_theory/game.lean
- \+ *lemma* mk_mul_move_left_inl
- \+ *lemma* mul_move_left_inl
- \+ *lemma* mk_mul_move_left_inr
- \+ *lemma* mul_move_left_inr
- \+ *lemma* mk_mul_move_right_inl
- \+ *lemma* mul_move_right_inl
- \+ *lemma* mk_mul_move_right_inr
- \+ *lemma* mul_move_right_inr
- \+ *lemma* left_distrib_equiv_aux
- \+ *lemma* left_distrib_equiv_aux'
- \+ *theorem* mul_comm_equiv
- \+ *theorem* mul_zero_equiv
- \+ *theorem* zero_mul_equiv
- \+ *theorem* left_distrib_equiv
- \+ *theorem* right_distrib_equiv
- \+ *def* mul
- \+ *def* left_moves_mul
- \+ *def* right_moves_mul
- \+ *def* mul_comm_relabelling
- \+ *def* mul_zero_relabelling
- \+ *def* zero_mul_relabelling
- \+ *def* inv_val
- \+ *def* inv'

Modified src/set_theory/surreal.lean
- \- *lemma* mk_mul_move_left_inl
- \- *lemma* mul_move_left_inl
- \- *lemma* mk_mul_move_left_inr
- \- *lemma* mul_move_left_inr
- \- *lemma* mk_mul_move_right_inl
- \- *lemma* mul_move_right_inl
- \- *lemma* mk_mul_move_right_inr
- \- *lemma* mul_move_right_inr
- \- *lemma* left_distrib_equiv_aux
- \- *lemma* left_distrib_equiv_aux'
- \- *theorem* mul_comm_equiv
- \- *theorem* mul_zero_equiv
- \- *theorem* zero_mul_equiv
- \- *theorem* left_distrib_equiv
- \- *theorem* right_distrib_equiv
- \- *def* mul
- \- *def* left_moves_mul
- \- *def* right_moves_mul
- \- *def* mul_comm_relabelling
- \- *def* mul_zero_relabelling
- \- *def* zero_mul_relabelling
- \- *def* inv_val
- \- *def* inv'



## [2021-05-14 12:02:31](https://github.com/leanprover-community/mathlib/commit/87adde4)
feat(category_theory/monoidal): the monoidal opposite ([#7602](https://github.com/leanprover-community/mathlib/pull/7602))
#### Estimated changes
Created src/category_theory/monoidal/opposite.lean
- \+ *lemma* op_injective
- \+ *lemma* unop_injective
- \+ *lemma* op_inj_iff
- \+ *lemma* unop_inj_iff
- \+ *lemma* mop_unmop
- \+ *lemma* unmop_mop
- \+ *lemma* mop_inj
- \+ *lemma* unmop_inj
- \+ *lemma* mop_comp
- \+ *lemma* mop_id
- \+ *lemma* unmop_comp
- \+ *lemma* unmop_id
- \+ *lemma* unmop_id_mop
- \+ *lemma* mop_id_unmop
- \+ *lemma* op_tensor_obj
- \+ *lemma* op_tensor_unit
- \+ *lemma* mop_tensor_obj
- \+ *lemma* mop_tensor_unit
- \+ *def* monoidal_opposite
- \+ *def* mop
- \+ *def* unmop
- \+ *def* quiver.hom.mop
- \+ *def* quiver.hom.unmop



## [2021-05-14 12:02:30](https://github.com/leanprover-community/mathlib/commit/cc1690e)
feat(analysis/calculus/parametric_integral): derivative of parametric integrals ([#7437](https://github.com/leanprover-community/mathlib/pull/7437))
from the sphere eversion project
#### Estimated changes
Created src/analysis/calculus/parametric_integral.lean
- \+ *lemma* has_fderiv_at_of_dominated_loc_of_lip'
- \+ *lemma* has_fderiv_at_of_dominated_loc_of_lip
- \+ *lemma* has_fderiv_at_of_dominated_of_fderiv_le
- \+ *lemma* has_deriv_at_of_dominated_loc_of_lip
- \+ *lemma* has_deriv_at_of_dominated_loc_of_deriv_le

Modified src/data/real/nnreal.lean
- \+ *lemma* real.nnabs_of_nonneg
- \+ *lemma* nnreal.coe_of_real_le



## [2021-05-14 09:48:30](https://github.com/leanprover-community/mathlib/commit/1199a3d)
feat(analysis/special_functions/exp_log): strengthen statement of `continuous_log'` ([#7607](https://github.com/leanprover-community/mathlib/pull/7607))
The proof of `continuous (λ x : {x : ℝ // 0 < x}, log x)` also works for `continuous (λ x : {x : ℝ // x ≠ 0}, log x)`.
I keep the preexisting lemma as well since it is used in a number of places and seems generally useful.
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* continuous_log



## [2021-05-14 09:48:29](https://github.com/leanprover-community/mathlib/commit/3c77167)
feat(linear_algebra/dual): generalize from field to ring ([#7599](https://github.com/leanprover-community/mathlib/pull/7599))
#### Estimated changes
Modified src/linear_algebra/dual.lean
- \+/\- *lemma* to_dual_total_left
- \+/\- *lemma* to_dual_total_right
- \+/\- *lemma* to_dual_apply_left
- \+/\- *lemma* to_dual_apply_right
- \+/\- *lemma* coe_to_dual_self
- \+/\- *lemma* to_dual_flip_apply
- \+/\- *lemma* to_dual_eq_repr
- \+/\- *lemma* to_dual_eq_equiv_fun
- \+/\- *lemma* to_dual_inj
- \+/\- *lemma* total_dual_basis
- \+/\- *lemma* dual_basis_repr
- \+/\- *lemma* dual_basis_equiv_fun
- \+/\- *lemma* dual_basis_apply
- \+ *lemma* eval_range
- \+ *lemma* eval_equiv_to_linear_map
- \+/\- *lemma* total_coord
- \+/\- *lemma* coeffs_apply
- \+/\- *lemma* lc_def
- \+/\- *lemma* dual_lc
- \+/\- *lemma* coeffs_lc
- \+/\- *lemma* lc_coeffs
- \+/\- *lemma* mem_of_mem_span
- \+/\- *theorem* to_dual_ker
- \+/\- *theorem* to_dual_range
- \+ *theorem* eval_ker
- \+/\- *theorem* dual_dim_eq
- \+/\- *def* to_dual
- \+/\- *def* to_dual_flip
- \+/\- *def* to_dual_equiv
- \+/\- *def* dual_basis
- \+ *def* eval_equiv
- \+/\- *def* coeffs
- \+/\- *def* lc
- \+/\- *def* basis



## [2021-05-14 04:49:59](https://github.com/leanprover-community/mathlib/commit/840db09)
chore(category_theory/groupoid): remove unnecessary imports ([#7600](https://github.com/leanprover-community/mathlib/pull/7600))
#### Estimated changes
Modified src/category_theory/core.lean


Modified src/category_theory/epi_mono.lean
- \+ *def* groupoid.of_trunc_split_mono

Modified src/category_theory/groupoid.lean
- \- *def* groupoid.of_trunc_split_mono



## [2021-05-14 04:49:58](https://github.com/leanprover-community/mathlib/commit/3124e1d)
feat(data/finset/lattice): choice-free le_sup_iff and lt_sup_iff ([#7584](https://github.com/leanprover-community/mathlib/pull/7584))
Propagate to `finset` the change to `le_sup_iff [is_total α (≤)]` and `lt_sup_iff [is_total α (≤)]` made in [#7455](https://github.com/leanprover-community/mathlib/pull/7455).
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+/\- *lemma* le_sup_iff
- \+/\- *lemma* lt_sup_iff



## [2021-05-14 04:49:57](https://github.com/leanprover-community/mathlib/commit/bf2750e)
chore(order/atoms): ask for the correct instances ([#7582](https://github.com/leanprover-community/mathlib/pull/7582))
replace bounded_lattice by order_bot/order_top where it can
#### Estimated changes
Modified src/order/atoms.lean
- \+/\- *lemma* is_coatom_dual_iff_is_atom
- \+/\- *lemma* is_atom_dual_iff_is_coatom
- \+/\- *lemma* is_atom_iff
- \+/\- *lemma* is_coatom_iff
- \+/\- *lemma* is_simple_lattice_iff
- \+/\- *lemma* is_simple_lattice
- \+/\- *lemma* is_atomic_iff
- \+/\- *lemma* is_coatomic_iff
- \+/\- *theorem* is_coatomic_dual_iff_is_atomic
- \+/\- *theorem* is_atomic_dual_iff_is_coatomic
- \+/\- *theorem* is_atomic_iff_forall_is_atomic_Iic
- \+/\- *theorem* is_coatomic_iff_forall_is_coatomic_Ici



## [2021-05-14 04:49:56](https://github.com/leanprover-community/mathlib/commit/8829c0d)
feat(algebra/homology): flipping double complexes ([#7482](https://github.com/leanprover-community/mathlib/pull/7482))
#### Estimated changes
Created src/algebra/homology/flip.lean
- \+ *def* flip_obj
- \+ *def* flip
- \+ *def* flip_equivalence_unit_iso
- \+ *def* flip_equivalence_counit_iso
- \+ *def* flip_equivalence



## [2021-05-14 04:49:55](https://github.com/leanprover-community/mathlib/commit/722b5fc)
feat(algebra/homology): homological complexes are the same as differential objects ([#7481](https://github.com/leanprover-community/mathlib/pull/7481))
#### Estimated changes
Created src/algebra/homology/differential_object.lean
- \+ *def* dgo_to_homological_complex
- \+ *def* homological_complex_to_dgo
- \+ *def* dgo_equiv_homological_complex_unit_iso
- \+ *def* dgo_equiv_homological_complex_counit_iso
- \+ *def* dgo_equiv_homological_complex



## [2021-05-14 04:49:54](https://github.com/leanprover-community/mathlib/commit/f5327c9)
feat(algebra/homology): definition of quasi_iso ([#7479](https://github.com/leanprover-community/mathlib/pull/7479))
#### Estimated changes
Created src/algebra/homology/quasi_iso.lean




## [2021-05-14 01:13:30](https://github.com/leanprover-community/mathlib/commit/239908e)
feat(ring_theory/ideal/operations): add apply_coe_mem_map ([#7566](https://github.com/leanprover-community/mathlib/pull/7566))
This is a continuation of [#7459](https://github.com/leanprover-community/mathlib/pull/7459). In this PR:
- We modify `ideal.mem_map_of_mem` in order to be consistent with `submonoid.mem_map_of_mem`.
- We modify `submonoid.apply_coe_mem_map` (and friends) to have the submonoid as an explicit variable. This was the case before [#7459](https://github.com/leanprover-community/mathlib/pull/7459) (but with a different, and not consistent, name). It seems to me that this version makes the code more readable.
- We add `ideal.apply_coe_mem_map` (similar to `submonoid.apply_coe_mem_map`).
Note that `mem_map_of_mem` is used in other places, for example we have `multiset.mem_map_of_mem`, but since a multiset is not a type there is no `apply_coe_mem_map` to add there.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+/\- *lemma* apply_coe_mem_map

Modified src/group_theory/submonoid/operations.lean
- \+/\- *lemma* apply_coe_mem_map

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* apply_coe_mem_map
- \+/\- *theorem* mem_map_of_mem

Modified src/ring_theory/ideal/over.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial/basic.lean




## [2021-05-13 15:18:24](https://github.com/leanprover-community/mathlib/commit/090c9ac)
chore(scripts): update nolints.txt ([#7597](https://github.com/leanprover-community/mathlib/pull/7597))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-05-13 15:18:24](https://github.com/leanprover-community/mathlib/commit/f792356)
chore(order/galois_connection): ask for the correct instances ([#7594](https://github.com/leanprover-community/mathlib/pull/7594))
replace partial_order by preorder where it can and general tidy up of this old style file
#### Estimated changes
Modified src/order/galois_connection.lean
- \+/\- *lemma* u_unique
- \+/\- *lemma* l_Sup
- \+/\- *lemma* u_Inf
- \+/\- *lemma* galois_connection_mul_div
- \+/\- *lemma* strict_mono_u
- \+/\- *def* galois_connection



## [2021-05-13 15:18:23](https://github.com/leanprover-community/mathlib/commit/ce45594)
feat(algebra/homology/single): chain complexes supported in a single degree ([#7477](https://github.com/leanprover-community/mathlib/pull/7477))
#### Estimated changes
Modified src/algebra/homology/homological_complex.lean


Created src/algebra/homology/single.lean
- \+ *lemma* single_map_f_self
- \+ *lemma* single₀_obj_X_0
- \+ *lemma* single₀_obj_X_succ
- \+ *lemma* single₀_obj_X_d
- \+ *lemma* single₀_obj_X_d_to
- \+ *lemma* single₀_obj_X_d_from
- \+ *lemma* single₀_map_f_0
- \+ *lemma* single₀_map_f_succ
- \+ *def* single
- \+ *def* single_obj_X_self
- \+ *def* single₀
- \+ *def* homology_functor_0_single₀
- \+ *def* homology_functor_succ_single₀
- \+ *def* to_single₀_equiv
- \+ *def* single₀_iso_single

Modified src/category_theory/fully_faithful.lean
- \+ *def* full.of_iso



## [2021-05-13 13:44:39](https://github.com/leanprover-community/mathlib/commit/c5faead)
feat(category_theory/preadditive/functor_category): preadditive instance for C \func D ([#7533](https://github.com/leanprover-community/mathlib/pull/7533))
#### Estimated changes
Modified src/category_theory/preadditive/default.lean
- \+/\- *lemma* sub_comp
- \+/\- *lemma* comp_sub
- \+/\- *lemma* neg_comp
- \+/\- *lemma* comp_neg
- \+/\- *lemma* neg_comp_neg
- \+ *lemma* nsmul_comp
- \+ *lemma* comp_nsmul
- \+/\- *lemma* gsmul_comp
- \+/\- *lemma* comp_gsmul
- \+/\- *lemma* comp_sum
- \+/\- *lemma* sum_comp
- \+ *def* comp_hom

Created src/category_theory/preadditive/functor_category.lean
- \+ *lemma* app_zero
- \+ *lemma* app_add
- \+ *lemma* app_sub
- \+ *lemma* app_neg
- \+ *lemma* app_nsmul
- \+ *lemma* app_gsmul
- \+ *lemma* app_sum
- \+ *def* app_hom



## [2021-05-12 16:37:46](https://github.com/leanprover-community/mathlib/commit/43bd924)
feat(topology/category/Profinite): iso_equiv_homeo ([#7529](https://github.com/leanprover-community/mathlib/pull/7529))
From LTE
#### Estimated changes
Modified src/topology/category/Profinite/default.lean
- \+/\- *lemma* is_closed_map
- \+/\- *lemma* is_iso_of_bijective
- \+/\- *def* Fintype.to_Profinite
- \+ *def* iso_of_homeo
- \+ *def* homeo_of_iso
- \+ *def* iso_equiv_homeo



## [2021-05-12 15:10:58](https://github.com/leanprover-community/mathlib/commit/08f4404)
refactor(ring_theory/perfection): remove coercion in the definition of the type ([#7583](https://github.com/leanprover-community/mathlib/pull/7583))
Defining the type `ring.perfection R p` as a plain subtype (but inheriting the semiring or ring instances from a `subsemiring` structure) removes several coercions and helps Lean a lot when elaborating or unifying.
#### Estimated changes
Modified src/ring_theory/perfection.lean
- \+ *def* ring.perfection_subsemiring
- \+ *def* ring.perfection_subring
- \+/\- *def* ring.perfection



## [2021-05-12 10:02:56](https://github.com/leanprover-community/mathlib/commit/6b62b9f)
refactor(algebra/module): rename `smul_injective hx` to `smul_left_injective M hx` ([#7577](https://github.com/leanprover-community/mathlib/pull/7577))
This is a follow-up PR to [#7548](https://github.com/leanprover-community/mathlib/pull/7548).
 * Now that there is also a `smul_right_injective`, we should disambiguate the previous `smul_injective` to `smul_left_injective`.
 * The `M` parameter can't be inferred from arguments before the colon, so we make it explicit in `smul_left_injective` and `smul_right_injective`.
#### Estimated changes
Modified src/algebra/algebra/tower.lean


Modified src/algebra/module/basic.lean
- \+ *lemma* smul_left_injective
- \- *lemma* smul_injective

Modified src/analysis/convex/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/tensor_product.lean




## [2021-05-12 02:19:18](https://github.com/leanprover-community/mathlib/commit/6ee8f0e)
doc(tactic/interactive): link swap and rotate to each other ([#7550](https://github.com/leanprover-community/mathlib/pull/7550))
They both do 'make a different goal the current one'.
#### Estimated changes
Modified src/tactic/interactive.lean




## [2021-05-11 22:59:11](https://github.com/leanprover-community/mathlib/commit/a7e1696)
fix(tactic/derive_fintype): use correct universes ([#7581](https://github.com/leanprover-community/mathlib/pull/7581))
Reported on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/type.20class.20error.20with.20mk_fintype_instance/near/238209823).
#### Estimated changes
Modified src/tactic/derive_fintype.lean


Modified test/derive_fintype.lean




## [2021-05-11 22:59:10](https://github.com/leanprover-community/mathlib/commit/0538d2c)
chore(*): reducing imports ([#7573](https://github.com/leanprover-community/mathlib/pull/7573))
#### Estimated changes
Modified src/analysis/special_functions/bernstein.lean


Created src/data/finsupp/antidiagonal.lean
- \+ *lemma* mem_antidiagonal_support
- \+ *lemma* swap_mem_antidiagonal_support
- \+ *lemma* antidiagonal_support_filter_fst_eq
- \+ *lemma* antidiagonal_support_filter_snd_eq
- \+ *lemma* antidiagonal_zero
- \+ *lemma* prod_antidiagonal_support_swap
- \+ *lemma* mem_Iic_finset
- \+ *lemma* coe_Iic_finset
- \+ *lemma* finite_le_nat
- \+ *lemma* finite_lt_nat
- \+ *def* antidiagonal
- \+ *def* Iic_finset

Modified src/data/finsupp/basic.lean
- \- *lemma* mem_antidiagonal_support
- \- *lemma* swap_mem_antidiagonal_support
- \- *lemma* antidiagonal_support_filter_fst_eq
- \- *lemma* antidiagonal_support_filter_snd_eq
- \- *lemma* antidiagonal_zero
- \- *lemma* prod_antidiagonal_support_swap
- \- *lemma* mem_Iic_finset
- \- *lemma* coe_Iic_finset
- \- *lemma* finite_le_nat
- \- *lemma* finite_lt_nat
- \- *def* antidiagonal
- \- *def* Iic_finset

Modified src/data/mv_polynomial/basic.lean


Modified src/order/order_iso_nat.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/continuous_function/compact.lean


Modified src/topology/continuous_function/weierstrass.lean




## [2021-05-11 18:00:40](https://github.com/leanprover-community/mathlib/commit/9cf732c)
chore(logic/nontrivial): adjust priority of `nonempty` instances ([#7563](https://github.com/leanprover-community/mathlib/pull/7563))
This makes `nontrivial.to_nonempty` and `nonempty_of_inhabited` higher priority so they are tried before things like `add_torsor.nonempty` which starts traversing the algebra heirarchy.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/char_zero/near/238103102)
#### Estimated changes
Modified src/logic/nontrivial.lean




## [2021-05-11 18:00:39](https://github.com/leanprover-community/mathlib/commit/3048d6b)
feat(ring_theory/localization): Define local ring hom on localization at prime ideal ([#7522](https://github.com/leanprover-community/mathlib/pull/7522))
Defines the induced ring homomorphism on the localizations at a prime ideal and proves that it is local and uniquely determined.
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *lemma* map_unique
- \+ *lemma* local_ring_hom_to_map
- \+ *lemma* local_ring_hom_mk'
- \+ *lemma* local_ring_hom_unique



## [2021-05-11 14:57:06](https://github.com/leanprover-community/mathlib/commit/b746e82)
feat(linear_algebra/finsupp): adjust apply lemma for `finsupp.dom_lcongr` ([#7549](https://github.com/leanprover-community/mathlib/pull/7549))
This is a split-off dependency from [#7496](https://github.com/leanprover-community/mathlib/pull/7496).
#### Estimated changes
Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/finsupp.lean
- \+/\- *lemma* dom_lcongr_apply



## [2021-05-11 10:56:56](https://github.com/leanprover-community/mathlib/commit/9191a67)
perf(ci): skip linting and tests on master branch ([#7576](https://github.com/leanprover-community/mathlib/pull/7576))
Do not run lints and tests on the master branch.  These checks have already passed on the staging branch, so there should be no need to repeat them on master.
#### Estimated changes
Modified .github/workflows/build.yml




## [2021-05-11 07:41:53](https://github.com/leanprover-community/mathlib/commit/b4c7654)
feat(algebra/homology): redesign of homological complexes ([#7473](https://github.com/leanprover-community/mathlib/pull/7473))
This is a complete redesign of our library on homological complexes and homology.
This PR replaces the current definition of `chain_complex` which had proved cumbersome to work with.
The fundamental change is that chain complexes are now indexed by a type equipped with a `complex_shape`, rather than by a monoid. A `complex_shape ι` contains a relation `r`, with the intent that we will only allow a differential `X i ⟶ X j` when `r i j`. This allows, for example, complexes indexed either by `nat` or `int`, with differentials going either up or down.
We set up the initial theory without referring to "successors" and "predecessors" in the type `ι`, to ensure we can avoid dependent type theory hell issues involving arithmetic in the index of a chain group. We achieve this by having a chain complex consist of morphisms `d i j : X i ⟶ X j` for all `i j`, but with an additional axiom saying this map is zero unless `r i j`. This means we can easily talk about, e.g., morphisms from `X (i - 1 + 1)` to `X (i + 1)` when we need to.
However after not too long we also set up `option` valued `next` and `prev` functions which make an arbitrary choice of such successors and predecessors if they exist. Using these, we define morphisms `d_to j`, which lands in `X j`, and has source either `X i` for some `r i j`, or the zero object if these isn't such an `i`. These morphisms are very convenient when working "at the edge of a complex", e.g. when indexing by `nat`.
#### Estimated changes
Deleted src/algebra/homology/chain_complex.lean
- \- *lemma* d_squared
- \- *lemma* comm_at
- \- *lemma* comm
- \- *lemma* eq_to_hom_d
- \- *lemma* eq_to_hom_f
- \- *def* map_homological_complex
- \- *def* pushforward_homological_complex

Created src/algebra/homology/complex_shape.lean
- \+ *lemma* symm_symm
- \+ *lemma* next_eq_some
- \+ *lemma* prev_eq_some
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans
- \+ *def* next
- \+ *def* prev
- \+ *def* up'
- \+ *def* down'
- \+ *def* up
- \+ *def* down

Modified src/algebra/homology/exact.lean
- \+ *lemma* preadditive.exact_iff_homology_zero
- \+ *lemma* comp_eq_zero_of_image_eq_kernel
- \+ *lemma* image_to_kernel_is_iso_of_image_eq_kernel
- \+ *lemma* exact_of_image_eq_kernel
- \+ *lemma* exact_iso_comp
- \+ *lemma* exact_comp_iso
- \+ *lemma* exact_kernel_subobject_arrow
- \+ *lemma* exact_kernel_ι
- \+ *lemma* kernel_subobject_arrow_eq_zero_of_exact_zero_left
- \+/\- *lemma* kernel_ι_eq_zero_of_exact_zero_left
- \+/\- *lemma* exact_zero_left_of_mono
- \+ *lemma* mono_iff_exact_zero_left
- \+ *lemma* epi_iff_exact_zero_right
- \- *lemma* exact_comp_hom_inv_comp
- \- *lemma* exact_kernel
- \- *lemma* exact_of_zero

Created src/algebra/homology/homological_complex.lean
- \+ *lemma* prev
- \+ *lemma* next
- \+ *lemma* next_nat_zero
- \+ *lemma* next_nat_succ
- \+ *lemma* prev_nat_zero
- \+ *lemma* prev_nat_succ
- \+ *lemma* id_f
- \+ *lemma* comp_f
- \+ *lemma* hom_f_injective
- \+ *lemma* zero_apply
- \+ *lemma* congr_hom
- \+ *lemma* d_comp_eq_to_hom
- \+ *lemma* eq_to_hom_comp_d
- \+ *lemma* kernel_eq_kernel
- \+ *lemma* image_eq_image
- \+ *lemma* d_to_eq
- \+ *lemma* d_to_eq_zero
- \+ *lemma* d_from_eq
- \+ *lemma* d_from_eq_zero
- \+ *lemma* X_prev_iso_comp_d_to
- \+ *lemma* X_prev_iso_zero_comp_d_to
- \+ *lemma* d_from_comp_X_next_iso
- \+ *lemma* d_from_comp_X_next_iso_zero
- \+ *lemma* d_to_comp_d_from
- \+ *lemma* kernel_from_eq_kernel
- \+ *lemma* image_to_eq_image
- \+ *lemma* prev_eq
- \+ *lemma* next_eq
- \+ *lemma* comm_from
- \+ *lemma* comm_to
- \+ *lemma* sq_from_left
- \+ *lemma* sq_from_right
- \+ *lemma* sq_from_id
- \+ *lemma* sq_from_comp
- \+ *lemma* sq_to_left
- \+ *lemma* sq_to_right
- \+ *lemma* of_X
- \+ *lemma* of_d
- \+ *lemma* mk_X_0
- \+ *lemma* mk_X_1
- \+ *lemma* mk_X_2
- \+ *lemma* mk_d_1_0
- \+ *lemma* mk_d_2_0
- \+ *lemma* mk'_X_0
- \+ *lemma* mk'_X_1
- \+ *lemma* mk'_d_1_0
- \+ *lemma* mk_hom_f_0
- \+ *lemma* mk_hom_f_1
- \+ *lemma* mk_hom_f_succ_succ
- \+ *def* id
- \+ *def* comp
- \+ *def* eval_at
- \+ *def* X_prev
- \+ *def* X_prev_iso
- \+ *def* X_prev_iso_zero
- \+ *def* X_next
- \+ *def* X_next_iso
- \+ *def* X_next_iso_zero
- \+ *def* d_to
- \+ *def* d_from
- \+ *def* prev
- \+ *def* next
- \+ *def* sq_from
- \+ *def* sq_to
- \+ *def* of
- \+ *def* mk_struct.flat
- \+ *def* mk_aux
- \+ *def* mk
- \+ *def* mk'
- \+ *def* mk_hom_aux
- \+ *def* mk_hom

Modified src/algebra/homology/homology.lean
- \+ *lemma* cycles_arrow_d_from
- \+ *lemma* cycles_eq_kernel_subobject
- \+ *lemma* cycles_eq_top
- \+ *lemma* boundaries_eq_image_subobject
- \+ *lemma* boundaries_eq_bot
- \+ *lemma* boundaries_le_cycles
- \+ *lemma* image_to_kernel_as_boundaries_to_cycles
- \+ *lemma* boundaries_to_cycles_arrow
- \+ *lemma* cycles_map_arrow
- \+ *lemma* cycles_map_id
- \+ *lemma* cycles_map_comp
- \+ *lemma* boundaries_to_cycles_naturality
- \- *lemma* kernel_map_condition
- \- *lemma* kernel_map_id
- \- *lemma* kernel_map_comp
- \- *lemma* image_map_ι
- \- *lemma* image_to_kernel_map_condition
- \- *lemma* image_to_kernel_map_comp_kernel_map
- \- *lemma* homology_map_condition
- \- *lemma* homology_map_id
- \- *lemma* homology_map_comp
- \+ *def* cycles
- \+ *def* cycles_iso_kernel
- \+ *def* boundaries_iso_image
- \+ *def* cycles_functor
- \+ *def* boundaries_functor
- \+ *def* boundaries_to_cycles_nat_trans
- \+ *def* homology_functor
- \+ *def* graded_homology_functor
- \- *def* kernel_map
- \- *def* kernel_functor
- \- *def* image_to_kernel_map
- \- *def* homology_group
- \- *def* homology_map
- \- *def* homology
- \- *def* graded_homology

Created src/algebra/homology/image_to_kernel.lean
- \+ *lemma* image_le_kernel
- \+ *lemma* subobject_of_le_as_image_to_kernel
- \+ *lemma* image_to_kernel_arrow
- \+ *lemma* factor_thru_image_subobject_comp_image_to_kernel
- \+ *lemma* image_to_kernel_zero_left
- \+ *lemma* image_to_kernel_zero_right
- \+ *lemma* image_to_kernel_comp_right
- \+ *lemma* image_to_kernel_comp_left
- \+ *lemma* image_to_kernel_comp_mono
- \+ *lemma* image_to_kernel_epi_comp
- \+ *lemma* image_to_kernel_comp_hom_inv_comp
- \+ *lemma* homology.condition
- \+ *lemma* homology.π_desc
- \+ *lemma* homology.ext
- \+ *lemma* image_subobject_map_comp_image_to_kernel
- \+ *lemma* homology.π_map
- \+ *lemma* homology.map_desc
- \+ *def* image_to_kernel
- \+ *def* homology
- \+ *def* homology.π
- \+ *def* homology.desc
- \+ *def* homology_zero_zero
- \+ *def* homology.map
- \+ *def* homology.congr

Deleted src/algebra/homology/image_to_kernel_map.lean
- \- *lemma* image_to_kernel_map_zero_left
- \- *lemma* image_to_kernel_map_zero_right
- \- *lemma* image_to_kernel_map_comp_right
- \- *lemma* image_to_kernel_map_comp_left
- \- *lemma* image_to_kernel_map_comp_iso
- \- *lemma* image_to_kernel_map_iso_comp
- \- *lemma* image_to_kernel_map_comp_hom_inv_comp
- \- *lemma* image_to_kernel_map_epi_of_zero_of_mono
- \- *lemma* image_to_kernel_map_epi_of_epi_of_zero

Modified src/category_theory/abelian/exact.lean
- \- *lemma* mono_iff_exact_zero_left
- \- *lemma* epi_iff_exact_zero_right
- \+ *theorem* exact_iff''
- \+ *theorem* exact_tfae



## [2021-05-11 07:41:52](https://github.com/leanprover-community/mathlib/commit/12c9ddf)
feat(set_theory/{pgame, surreal}): add `left_distrib_equiv` and `right_distrib_equiv` for pgames ([#7440](https://github.com/leanprover-community/mathlib/pull/7440))
and several other auxiliary lemmas.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Surreal.20numbers)
#### Estimated changes
Modified src/set_theory/game.lean
- \+ *lemma* quot_neg
- \+ *lemma* quot_add
- \+ *lemma* quot_sub
- \+/\- *theorem* le_refl
- \+/\- *theorem* le_trans
- \- *def* game

Modified src/set_theory/pgame.lean
- \+ *theorem* equiv_of_mk_equiv
- \+ *theorem* sub_congr
- \+ *theorem* add_right_neg_equiv

Modified src/set_theory/surreal.lean
- \+ *lemma* left_distrib_equiv_aux
- \+ *lemma* left_distrib_equiv_aux'
- \+/\- *theorem* mul_comm_equiv
- \+/\- *theorem* mul_zero_equiv
- \+/\- *theorem* zero_mul_equiv
- \+ *theorem* left_distrib_equiv
- \+ *theorem* right_distrib_equiv
- \- *def* add_sub_relabelling
- \- *def* add_comm_sub_relabelling



## [2021-05-11 05:55:39](https://github.com/leanprover-community/mathlib/commit/ca4024b)
feat(algebraic_topology/cech_nerve): Adds a definition of the Cech nerve associated to an arrow. ([#7547](https://github.com/leanprover-community/mathlib/pull/7547))
Also adds a definition of augmented simplicial objects as a comma category.
#### Estimated changes
Created src/algebraic_topology/cech_nerve.lean
- \+ *def* cech_nerve
- \+ *def* augmented_cech_nerve

Modified src/algebraic_topology/simplicial_object.lean
- \+ *def* augmented

Modified src/category_theory/limits/shapes/wide_pullbacks.lean




## [2021-05-11 04:39:37](https://github.com/leanprover-community/mathlib/commit/8dc848c)
feat(ring_theory/finiteness): add finite_type_iff_group_fg ([#7569](https://github.com/leanprover-community/mathlib/pull/7569))
We add here a simple modification of `monoid_algebra.fg_of_finite_type`: a group algebra is of finite type if and only if the group is finitely generated (as group opposed to as monoid).
#### Estimated changes
Modified src/ring_theory/finiteness.lean
- \+ *lemma* finite_type_iff_group_fg



## [2021-05-11 01:49:43](https://github.com/leanprover-community/mathlib/commit/fab4197)
chore(scripts): update nolints.txt ([#7570](https://github.com/leanprover-community/mathlib/pull/7570))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-05-10 22:45:44](https://github.com/leanprover-community/mathlib/commit/3fd7cc3)
feat(ring_theory/hahn_series): extend the domain of a Hahn series by an `order_embedding` ([#7551](https://github.com/leanprover-community/mathlib/pull/7551))
Defines `hahn_series.emb_domain`, which extends the domain of a Hahn series by embedding it into a larger domain in an order-preserving way.
Bundles `hahn_series.emb_domain` with additional properties as `emb_domain_linear_map`, `emb_domain_ring_hom`, and `emb_domain_alg_hom` under additional conditions.
Defines the ring homomorphism `hahn_series.of_power_series` and the algebra homomorphism `hahn_series.of_power_series_alg`, which map power series to Hahn series over an ordered semiring using `hahn_series.emb_domain` with `nat.cast` as the embedding.
#### Estimated changes
Modified src/ring_theory/hahn_series.lean
- \+ *lemma* emb_domain_coeff
- \+ *lemma* emb_domain_mk_coeff
- \+ *lemma* emb_domain_notin_image_support
- \+ *lemma* support_emb_domain_subset
- \+ *lemma* emb_domain_notin_range
- \+ *lemma* emb_domain_zero
- \+ *lemma* emb_domain_single
- \+ *lemma* emb_domain_injective
- \+ *lemma* emb_domain_ring_hom_C
- \+ *def* emb_domain
- \+ *def* emb_domain_linear_map
- \+ *def* emb_domain_ring_hom
- \+ *def* emb_domain_alg_hom
- \+ *def* of_power_series
- \+ *def* of_power_series_alg



## [2021-05-10 22:45:43](https://github.com/leanprover-community/mathlib/commit/81c98d5)
feat(ring_theory/hahn_series): Hahn series form a field ([#7495](https://github.com/leanprover-community/mathlib/pull/7495))
Uses Higman's Lemma to define `summable_family.powers`, a summable family consisting of the powers of a Hahn series of positive valuation
Uses `summable_family.powers` to define inversion on Hahn series over a field and linear-ordered value group, making the type of Hahn series a field.
Shows that a Hahn series over an integral domain and linear-ordered value group  `is_unit` if and only if its lowest coefficient is.
#### Estimated changes
Modified src/order/well_founded_set.lean
- \+ *lemma* well_founded_on.induction
- \+ *lemma* submonoid_closure
- \+ *theorem* partially_well_ordered_on.image_of_monotone_on
- \- *theorem* partially_well_ordered_on.image_of_monotone

Modified src/ring_theory/hahn_series.lean
- \+ *lemma* is_pwo_Union_support_powers
- \+ *lemma* coe_powers
- \+ *lemma* emb_domain_succ_smul_powers
- \+ *lemma* one_sub_self_mul_hsum_powers
- \+ *lemma* unit_aux
- \+ *lemma* is_unit_iff
- \+ *def* powers



## [2021-05-10 22:45:42](https://github.com/leanprover-community/mathlib/commit/1cbb31d)
feat(analysis/normed_space/normed_group_hom): add lemmas ([#7474](https://github.com/leanprover-community/mathlib/pull/7474))
From LTE.
Written by @PatrickMassot 
- [x] depends on: [#7459](https://github.com/leanprover-community/mathlib/pull/7459)
#### Estimated changes
Modified src/analysis/normed_space/normed_group_hom.lean
- \+ *lemma* norm_incl
- \+ *lemma* comp_range
- \+ *lemma* incl_range
- \+ *lemma* range_comp_incl_top



## [2021-05-10 16:44:24](https://github.com/leanprover-community/mathlib/commit/b7ab74a)
feat(algebra/lie/weights): add lemma `root_space_comap_eq_weight_space` ([#7565](https://github.com/leanprover-community/mathlib/pull/7565))
#### Estimated changes
Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* coe_incl
- \+ *lemma* coe_incl'
- \+ *def* incl
- \+ *def* incl'
- \- *def* lie_subalgebra.incl

Modified src/algebra/lie/submodule.lean
- \+ *lemma* mem_comap

Modified src/algebra/lie/weights.lean
- \+/\- *lemma* coe_weight_space_of_top
- \+ *lemma* root_space_comap_eq_weight_space



## [2021-05-10 16:44:23](https://github.com/leanprover-community/mathlib/commit/ac1f3df)
chore(*): remove unnecessary `import tactic` ([#7560](https://github.com/leanprover-community/mathlib/pull/7560))
#### Estimated changes
Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified src/category_theory/limits/kan_extension.lean


Modified src/combinatorics/colex.lean


Modified src/data/nat/fib.lean


Modified src/data/set/constructions.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/number_theory/divisors.lean


Modified src/ring_theory/polynomial/symmetric.lean


Modified src/ring_theory/witt_vector/structure_polynomial.lean




## [2021-05-10 16:44:22](https://github.com/leanprover-community/mathlib/commit/17cba54)
feat(data/int/basic): sign raised to an odd power ([#7559](https://github.com/leanprover-community/mathlib/pull/7559))
Since sign is either -1, 0, or 1, it is unchanged when raised to an odd power.
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *theorem* sign_pow_bit1



## [2021-05-10 16:44:21](https://github.com/leanprover-community/mathlib/commit/3417ee0)
chore(deprecated/group): relax monoid to mul_one_class ([#7556](https://github.com/leanprover-community/mathlib/pull/7556))
This fixes an annoyance where `monoid_hom.is_monoid_hom` didn't work on non-associative monoids.
#### Estimated changes
Modified src/data/dfinsupp.lean


Modified src/deprecated/group.lean
- \+/\- *lemma* comp
- \+/\- *lemma* additive.is_add_monoid_hom
- \+/\- *lemma* multiplicative.is_monoid_hom
- \+/\- *theorem* is_monoid_hom.of_mul



## [2021-05-10 16:44:20](https://github.com/leanprover-community/mathlib/commit/477af65)
feat(category_theory/limits/shapes/wide_pullbacks): Adds some wrappers around the (co)limit api for wide pullbacks/pushouts ([#7546](https://github.com/leanprover-community/mathlib/pull/7546))
This PR adds some wrappers (mostly abbreviations) around the (co)limit api specifically for wide pullbacks and wide pushouts.
#### Estimated changes
Modified src/category_theory/limits/shapes/wide_pullbacks.lean
- \+ *lemma* π_arrow
- \+ *lemma* lift_π
- \+ *lemma* lift_base
- \+ *lemma* eq_lift_of_comp_eq
- \+ *lemma* hom_eq_lift
- \+ *lemma* hom_ext
- \+ *lemma* arrow_ι
- \+ *lemma* ι_desc
- \+ *lemma* head_desc
- \+ *lemma* eq_desc_of_comp_eq
- \+ *lemma* hom_eq_desc



## [2021-05-10 16:44:19](https://github.com/leanprover-community/mathlib/commit/92395fd)
feat(data/list/rotate): is_rotated ([#7299](https://github.com/leanprover-community/mathlib/pull/7299))
`is_rotated l₁ l₂` or `l₁ ~r l₂` asserts that `l₁` and `l₂` are cyclic permutations
  of each other. This is defined by claiming that `∃ n, l.rotate n = l'`.
#### Estimated changes
Modified src/data/list/rotate.lean
- \+ *lemma* rotate'_eq_drop_append_take
- \+ *lemma* rotate_eq_drop_append_take
- \+ *lemma* rotate_eq_drop_append_take_mod
- \+ *lemma* rotate_perm
- \+ *lemma* nodup_rotate
- \+ *lemma* rotate_eq_nil_iff
- \+ *lemma* rotate_singleton
- \+ *lemma* zip_with_rotate_distrib
- \+ *lemma* zip_with_rotate_one
- \+ *lemma* nth_le_rotate_one
- \+ *lemma* nth_le_rotate
- \+ *lemma* rotate_injective
- \+ *lemma* rotate_eq_rotate
- \+ *lemma* rotate_eq_iff
- \+ *lemma* reverse_rotate
- \+ *lemma* is_rotated.refl
- \+ *lemma* is_rotated.symm
- \+ *lemma* is_rotated_comm
- \+ *lemma* is_rotated.trans
- \+ *lemma* is_rotated.eqv
- \+ *lemma* is_rotated.perm
- \+ *lemma* is_rotated.nodup_iff
- \+ *lemma* is_rotated.mem_iff
- \+ *lemma* is_rotated_nil_iff
- \+ *lemma* is_rotated_nil_iff'
- \+ *lemma* is_rotated_concat
- \+ *lemma* is_rotated.reverse
- \+ *lemma* is_rotated_reverse_comm_iff
- \+ *lemma* is_rotated_reverse_iff
- \+ *lemma* is_rotated_iff_mod
- \+ *lemma* is_rotated_iff_mem_map_range
- \- *lemma* rotate'_eq_take_append_drop
- \- *lemma* rotate_eq_take_append_drop
- \+ *def* is_rotated
- \+ *def* is_rotated.setoid



## [2021-05-10 13:15:31](https://github.com/leanprover-community/mathlib/commit/41c7b1e)
chore(category_theory/Fintype): remove redundant lemmas ([#7531](https://github.com/leanprover-community/mathlib/pull/7531))
These lemmas exist for arbitrary concrete categories.
- [x] depends on: [#7530](https://github.com/leanprover-community/mathlib/pull/7530)
#### Estimated changes
Modified src/category_theory/Fintype.lean
- \- *lemma* coe_id
- \- *lemma* coe_comp
- \- *lemma* id_apply
- \- *lemma* comp_apply



## [2021-05-10 13:15:30](https://github.com/leanprover-community/mathlib/commit/b9f4420)
feat(geometry/euclidean/triangle): add Stewart's Theorem + one similarity lemma ([#7327](https://github.com/leanprover-community/mathlib/pull/7327))
#### Estimated changes
Modified src/geometry/euclidean/triangle.lean
- \+ *lemma* dist_mul_of_eq_angle_of_dist_mul
- \+ *theorem* dist_sq_mul_dist_add_dist_sq_mul_dist
- \+ *theorem* dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq



## [2021-05-10 13:15:28](https://github.com/leanprover-community/mathlib/commit/03b88c1)
feat(algebra/category/Module): Free R C, the free R-linear completion of a category ([#7177](https://github.com/leanprover-community/mathlib/pull/7177))
The free R-linear completion of a category.
#### Estimated changes
Modified src/algebra/category/Module/adjunctions.lean
- \+ *lemma* single_comp_single
- \+ *lemma* lift_map_single
- \+ *def* Free
- \+ *def* Free.of
- \+ *def* embedding
- \+ *def* lift
- \+ *def* embedding_lift_iso
- \+ *def* ext
- \+ *def* lift_unique

Modified src/category_theory/preadditive/additive_functor.lean
- \+ *lemma* map_gsmul

Modified src/category_theory/preadditive/default.lean
- \+ *lemma* comp_gsmul
- \+ *lemma* gsmul_comp

Modified src/linear_algebra/tensor_product.lean




## [2021-05-10 07:36:17](https://github.com/leanprover-community/mathlib/commit/48104c3)
feat(data/set/lattice): (b)Union and (b)Inter lemmas ([#7557](https://github.com/leanprover-community/mathlib/pull/7557))
from LTE
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* Union_prop
- \+ *lemma* Union_prop_pos
- \+ *lemma* Union_prop_neg
- \+ *lemma* mem_bUnion_iff'
- \+ *lemma* bInter_inter
- \+ *lemma* inter_bInter



## [2021-05-10 07:36:16](https://github.com/leanprover-community/mathlib/commit/b577697)
feat(data/matrix/basic): add missing smul instances, generalize lemmas to work on scalar towers ([#7544](https://github.com/leanprover-community/mathlib/pull/7544))
This also fixes the `add_monoid_hom.map_zero` etc lemmas to not require overly strong typeclasses on `α`
This removes the `matrix.smul_apply` lemma since `pi.smul_apply` and `smul_eq_mul` together replace it.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *lemma* map_apply
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_add
- \+/\- *lemma* map_sub
- \+/\- *lemma* add_monoid_hom.map_matrix_apply
- \+/\- *lemma* diagonal_map
- \+/\- *lemma* one_map
- \+/\- *lemma* smul_dot_product
- \+/\- *lemma* dot_product_smul
- \+/\- *lemma* map_mul
- \+/\- *lemma* is_add_monoid_hom_mul_left
- \+/\- *lemma* is_add_monoid_hom_mul_right
- \+/\- *lemma* row_mul_col_apply
- \+/\- *lemma* ring_hom_map_one
- \+/\- *lemma* ring_equiv_map_one
- \+/\- *lemma* zero_hom_map_zero
- \+/\- *lemma* add_monoid_hom_map_zero
- \+/\- *lemma* add_equiv_map_zero
- \+/\- *lemma* linear_map_map_zero
- \+/\- *lemma* linear_equiv_map_zero
- \+/\- *lemma* ring_hom_map_zero
- \+/\- *lemma* ring_equiv_map_zero
- \+/\- *lemma* smul_mul
- \+/\- *lemma* mul_smul
- \+/\- *lemma* transpose_map
- \+/\- *lemma* star_apply
- \+/\- *lemma* star_mul
- \- *lemma* ring_hom.map_matrix_apply
- \- *lemma* smul_apply
- \+/\- *def* map
- \+/\- *def* add_monoid_hom.map_matrix
- \+/\- *def* ring_hom.map_matrix

Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/ring_theory/matrix_algebra.lean


Modified src/ring_theory/polynomial_algebra.lean




## [2021-05-10 07:36:15](https://github.com/leanprover-community/mathlib/commit/38bf2ab)
feat(field_theory/abel_ruffini): Version of solvable_by_rad.is_solvable ([#7509](https://github.com/leanprover-community/mathlib/pull/7509))
This is a version of `solvable_by_rad.is_solvable`, which will be the final step of the abel-ruffini theorem.
#### Estimated changes
Modified src/field_theory/abel_ruffini.lean
- \+ *lemma* is_solvable'

Modified src/field_theory/minpoly.lean
- \+ *lemma* unique''



## [2021-05-10 07:36:14](https://github.com/leanprover-community/mathlib/commit/ef90a7a)
refactor(*): bundle `is_basis` ([#7496](https://github.com/leanprover-community/mathlib/pull/7496))
This PR replaces the definition of a basis used in mathlib and fixes the usages throughout.
Rationale: Previously, `is_basis` was a predicate on a family of vectors, saying this family is linear independent and spans the whole space. We encountered many small annoyances when working with these unbundled definitions, for example complicated `is_basis` arguments being hidden in the goal view or slow elaboration when mapping a basis to a slightly different set of basis vectors. The idea to turn `basis` into a bundled structure originated in the discussion on [#4949](https://github.com/leanprover-community/mathlib/pull/4949). @digama0 suggested on Zulip to identify these "bundled bases" with their map `repr : M ≃ₗ[R] (ι →₀ R)` that sends a vector to its coordinates. (In fact, that specific map used to be only a `linear_map` rather than an equiv.)
Overview of the changes:
 - The `is_basis` predicate has been replaced with the `basis` structure. 
 - Parameters of the form `{b : ι → M} (hb : is_basis R b)` become a single parameter `(b : basis ι R M)`.
 - Constructing a basis from a linear independent family spanning the whole space is now spelled `basis.mk hli hspan`, instead of `and.intro hli hspan`.
 -  You can also use `basis.of_repr` to construct a basis from an equivalence `e : M ≃ₗ[R] (ι →₀ R)`. If `ι` is a `fintype`, you can use `basis.of_equiv_fun (e : M ≃ₗ[R] (ι → R))` instead, saving you from having to work with `finsupp`s.
 - Most declaration names that used to contain `is_basis` are now spelled with `basis`, e.g. `pi.is_basis_fun` is now `pi.basis_fun`.
 - Theorems of the form `exists_is_basis K V : ∃ (s : set V) (b : s -> V), is_basis K b` and `finite_dimensional.exists_is_basis_finset K V : [finite_dimensional K V] -> ∃ (s : finset V) (b : s -> V), is_basis K b` have been replaced with (noncomputable) defs such as `basis.of_vector_space K V : basis (basis.of_vector_space_index K V) K V` and `finite_dimensional.finset_basis : basis (finite_dimensional.finset_basis_index K V) K V`; the indexing sets being a separate definition means we can declare a `fintype (basis.of_vector_space_index K V)` instance on finite dimensional spaces, rather than having to use `cases exists_is_basis_fintype K V with ...` each time.
 - Definitions of a `basis` are now, wherever practical, accompanied by `simp` lemmas giving the values of `coe_fn` and `repr` for that basis.
 - Some auxiliary results like `pi.is_basis_fun₀` have been removed since they are no longer needed.
Basic API overview:
* `basis ι R M` is the type of `ι`-indexed `R`-bases for a module `M`, represented by a linear equiv `M ≃ₗ[R] ι →₀ R`.
* the basis vectors of a basis `b` are given by `b i` for `i : ι`
* `basis.repr` is the isomorphism sending `x : M` to its coordinates `basis.repr b x : ι →₀ R`. The inverse of `b.repr` is `finsupp.total _ _ _ b`. The converse, turning this isomorphism into a basis, is called `basis.of_repr`.
* If `ι` is finite, there is a variant of `repr` called `basis.equiv_fun b : M ≃ₗ[R] ι → R`. The converse, turning this isomorphism into a basis, is called `basis.of_equiv_fun`.
* `basis.constr hv f` constructs a linear map `M₁ →ₗ[R] M₂` given the values `f : ι → M₂` at the
  basis elements `⇑b : ι → M₁`.
* `basis.mk`: a linear independent set of vectors spanning the whole module determines a basis (the converse consists of `basis.linear_independent` and `basis.span_eq`
* `basis.ext` states that two linear maps are equal if they coincide on a basis; similar results are available for linear equivs (if they coincide on the basis vectors), elements (if their coordinates coincide) and the functions `b.repr` and `⇑b`.
* `basis.of_vector_space` states that every vector space has a basis.
* `basis.reindex` uses an equiv to map a basis to a different indexing set, `basis.map` uses a linear equiv to map a basis to a different module
Zulip discussions:
 * https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Bundled.20basis
 * https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.234949
#### Estimated changes
Modified archive/sensitivity.lean


Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/algebra/module/basic.lean
- \+ *lemma* smul_right_injective

Modified src/algebra/module/projective.lean
- \+/\- *theorem* of_free

Modified src/analysis/normed_space/finite_dimension.lean
- \+/\- *lemma* continuous_equiv_fun_basis
- \+ *lemma* basis.coe_constrL
- \+ *lemma* basis.constrL_apply
- \+ *lemma* basis.constrL_basis
- \+ *lemma* basis.sup_norm_le_norm
- \+ *lemma* basis.op_norm_le
- \- *lemma* is_basis.coe_constrL
- \- *lemma* is_basis.constrL_apply
- \- *lemma* is_basis.constrL_basis
- \- *lemma* is_basis.sup_norm_le_norm
- \- *lemma* is_basis.op_norm_le
- \+ *def* basis.constrL
- \+ *def* basis.equiv_funL
- \- *def* is_basis.constrL
- \- *def* is_basis.equiv_funL

Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* coe_basis_of_orthonormal_of_card_eq_finrank
- \+ *lemma* maximal_orthonormal_iff_basis_of_finite_dimensional
- \+ *lemma* orthonormal_basis_orthonormal
- \+ *lemma* coe_orthonormal_basis
- \+ *lemma* fin_orthonormal_basis_orthonormal
- \- *lemma* is_basis_of_orthonormal_of_card_eq_finrank
- \- *lemma* maximal_orthonormal_iff_is_basis_of_finite_dimensional
- \- *lemma* exists_is_orthonormal_basis
- \- *lemma* exists_is_orthonormal_basis'
- \+ *def* basis_of_orthonormal_of_card_eq_finrank
- \+ *def* basis.isometry_euclidean_of_orthonormal
- \+ *def* orthonormal_basis_index
- \+ *def* orthonormal_basis
- \+ *def* fin_orthonormal_basis
- \- *def* is_basis.isometry_euclidean_of_orthonormal

Modified src/data/complex/module.lean
- \+ *lemma* coe_basis_one_I_repr
- \+ *lemma* coe_basis_one_I
- \- *lemma* is_basis_one_I
- \+ *def* basis_one_I

Modified src/field_theory/adjoin.lean
- \- *lemma* power_basis_is_basis

Modified src/field_theory/mv_polynomial.lean


Modified src/field_theory/normal.lean


Modified src/field_theory/tower.lean


Modified src/linear_algebra/affine_space/independent.lean


Modified src/linear_algebra/basis.lean
- \+ *lemma* coe_of_repr
- \+ *lemma* repr_symm_single_one
- \+ *lemma* repr_symm_single
- \+ *lemma* repr_self
- \+ *lemma* repr_self_apply
- \+ *lemma* repr_symm_apply
- \+ *lemma* coe_repr_symm
- \+ *lemma* repr_total
- \+ *lemma* total_repr
- \+ *lemma* repr_range
- \+ *lemma* forall_coord_eq_zero_iff
- \+ *lemma* repr_eq_iff
- \+ *lemma* repr_eq_iff'
- \+ *lemma* apply_eq_iff
- \+ *lemma* repr_apply_eq
- \+ *lemma* eq_of_repr_eq_repr
- \+ *lemma* eq_of_apply_eq
- \+ *lemma* reindex_apply
- \+ *lemma* coe_reindex
- \+ *lemma* coe_reindex_repr
- \+ *lemma* reindex_repr
- \+ *lemma* range_reindex'
- \+ *lemma* range_reindex
- \+ *lemma* finsupp.single_apply_left
- \+ *lemma* reindex_range_self
- \+ *lemma* reindex_range_repr_self
- \+ *lemma* reindex_range_apply
- \+ *lemma* reindex_range_repr'
- \+ *lemma* reindex_range_repr
- \+/\- *lemma* constr_basis
- \+/\- *lemma* constr_eq
- \+/\- *lemma* constr_self
- \+/\- *lemma* constr_range
- \+ *lemma* equiv_apply
- \+ *lemma* equiv_refl
- \+ *lemma* equiv_symm
- \+ *lemma* equiv_trans
- \+ *lemma* map_apply
- \+ *lemma* prod_repr_inl
- \+ *lemma* prod_repr_inr
- \+ *lemma* prod_apply_inl_fst
- \+ *lemma* prod_apply_inr_fst
- \+ *lemma* prod_apply_inl_snd
- \+ *lemma* prod_apply_inr_snd
- \+ *lemma* prod_apply
- \+ *lemma* singleton_apply
- \+ *lemma* singleton_repr
- \+ *lemma* basis_singleton_iff
- \+ *lemma* empty_unique
- \+ *lemma* basis.equiv_fun_symm_apply
- \+ *lemma* basis.equiv_fun_apply
- \+ *lemma* basis.sum_equiv_fun
- \+ *lemma* basis.sum_repr
- \+ *lemma* basis.equiv_fun_self
- \+ *lemma* basis.of_equiv_fun_repr_apply
- \+ *lemma* basis.coe_of_equiv_fun
- \+ *lemma* equiv'_apply
- \+ *lemma* equiv'_symm_apply
- \+ *lemma* mk_repr
- \+ *lemma* mk_apply
- \+ *lemma* coe_mk
- \+ *lemma* extend_apply_self
- \+ *lemma* coe_extend
- \+ *lemma* range_extend
- \+ *lemma* subset_extend
- \+ *lemma* of_vector_space_apply_self
- \+ *lemma* coe_of_vector_space
- \+ *lemma* of_vector_space_index.linear_independent
- \+ *lemma* range_of_vector_space
- \+ *lemma* exists_basis
- \- *lemma* is_basis.mem_span
- \- *lemma* is_basis.comp
- \- *lemma* is_basis.injective
- \- *lemma* is_basis.range
- \- *lemma* is_basis.total_repr
- \- *lemma* is_basis.total_comp_repr
- \- *lemma* is_basis.ext
- \- *lemma* is_basis.repr_ker
- \- *lemma* is_basis.repr_range
- \- *lemma* is_basis.repr_total
- \- *lemma* is_basis.repr_eq_single
- \- *lemma* is_basis.repr_self_apply
- \- *lemma* is_basis.repr_eq_iff
- \- *lemma* is_basis.repr_apply_eq
- \- *lemma* is_basis.range_repr_self
- \- *lemma* is_basis.range_repr
- \- *lemma* constr_zero
- \- *lemma* constr_add
- \- *lemma* constr_neg
- \- *lemma* constr_sub
- \- *lemma* constr_smul
- \- *lemma* linear_equiv_of_is_basis_comp
- \- *lemma* linear_equiv_of_is_basis_refl
- \- *lemma* linear_equiv_of_is_basis_trans_symm
- \- *lemma* linear_equiv_of_is_basis_symm_trans
- \- *lemma* is_basis_inl_union_inr
- \- *lemma* is_basis.repr_eq_zero
- \- *lemma* is_basis.ext_elem
- \- *lemma* is_basis.no_zero_smul_divisors
- \- *lemma* is_basis.smul_eq_zero
- \- *lemma* is_basis_singleton_iff
- \- *lemma* is_basis_singleton_one
- \- *lemma* is_basis_span
- \- *lemma* is_basis_empty
- \- *lemma* is_basis.equiv_fun_symm_apply
- \- *lemma* is_basis.equiv_fun_apply
- \- *lemma* is_basis.equiv_fun_total
- \- *lemma* is_basis.equiv_fun_self
- \- *lemma* exists_subset_is_basis
- \- *lemma* exists_sum_is_basis
- \- *lemma* exists_is_basis
- \+ *theorem* ext
- \+ *theorem* ext'
- \+ *theorem* ext_elem
- \+ *theorem* constr_def
- \+ *theorem* constr_apply
- \+ *theorem* basis.constr_apply_fintype
- \- *theorem* is_basis.constr_apply
- \- *theorem* module_equiv_finsupp_apply_basis
- \- *theorem* is_basis.constr_apply_fintype
- \+ *def* coord
- \+ *def* reindex
- \+ *def* reindex_range
- \+ *def* constr
- \+ *def* basis.equiv_fun
- \+ *def* basis.of_equiv_fun
- \+ *def* equiv'
- \- *def* is_basis
- \- *def* is_basis.repr
- \- *def* is_basis.constr
- \- *def* module_equiv_finsupp
- \- *def* linear_equiv_of_is_basis
- \- *def* linear_equiv_of_is_basis'
- \- *def* is_basis.equiv_fun

Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* basis.equiv_fun_symm_std_basis
- \+ *lemma* matrix.to_bilin_basis_fun
- \+ *lemma* bilin_form.to_matrix_basis_fun
- \+/\- *lemma* le_orthogonal_orthogonal
- \+/\- *lemma* restrict_sym
- \+/\- *lemma* to_dual_def
- \+/\- *lemma* comp_left_injective
- \+/\- *lemma* is_adjoint_pair_unique_of_nondegenerate
- \- *lemma* is_basis.equiv_fun_symm_std_basis
- \- *lemma* matrix.to_bilin_is_basis_fun
- \- *lemma* bilin_form.to_matrix_is_basis_fun

Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/dimension.lean
- \+ *lemma* basis.nonempty_fintype_index_of_dim_lt_omega
- \+ *lemma* basis.finite_index_of_dim_lt_omega
- \+ *lemma* basis.finite_of_vector_space_index_of_dim_lt_omega
- \+ *lemma* basis.of_dim_eq_zero_apply
- \+ *lemma* basis.of_dim_eq_zero'_apply
- \- *lemma* exists_is_basis_fintype
- \- *lemma* is_basis_of_dim_eq_zero
- \- *lemma* is_basis_of_dim_eq_zero'
- \+ *theorem* basis.le_span
- \+/\- *theorem* mk_eq_mk_of_basis
- \+/\- *theorem* mk_eq_mk_of_basis'
- \+ *theorem* basis.mk_eq_dim''
- \+ *theorem* basis.mk_range_eq_dim
- \+ *theorem* basis.mk_eq_dim
- \+/\- *theorem* {m}
- \- *theorem* is_basis.le_span
- \- *theorem* is_basis.mk_eq_dim''
- \- *theorem* is_basis.mk_range_eq_dim
- \- *theorem* is_basis.mk_eq_dim
- \+ *def* basis.of_dim_eq_zero
- \+ *def* basis.of_dim_eq_zero'

Modified src/linear_algebra/dual.lean
- \+/\- *lemma* to_dual_apply_left
- \+/\- *lemma* to_dual_apply_right
- \+ *lemma* coe_to_dual_self
- \+ *lemma* to_dual_flip_apply
- \+/\- *lemma* to_dual_eq_repr
- \+/\- *lemma* to_dual_eq_equiv_fun
- \+/\- *lemma* to_dual_inj
- \+/\- *lemma* dual_basis_apply_self
- \+/\- *lemma* total_dual_basis
- \+/\- *lemma* dual_basis_apply
- \+ *lemma* coe_dual_basis
- \+ *lemma* total_coord
- \+ *lemma* lc_def
- \+ *lemma* lc_coeffs
- \+ *lemma* coe_basis
- \- *lemma* coord_fun_eq_repr
- \- *lemma* to_dual_swap_eq_to_dual
- \- *lemma* decomposition
- \- *lemma* is_basis
- \- *lemma* eq_dual
- \+/\- *theorem* to_dual_ker
- \+/\- *theorem* to_dual_range
- \- *theorem* dual_lin_independent
- \- *theorem* dual_basis_is_basis
- \+/\- *def* to_dual_flip
- \+/\- *def* dual_basis
- \+ *def* basis
- \- *def* coord_fun

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_basis_index
- \+ *lemma* coe_finset_basis_index
- \+ *lemma* range_finset_basis
- \+/\- *lemma* of_fintype_basis
- \+/\- *lemma* of_finite_basis
- \+/\- *lemma* of_finset_basis
- \+/\- *lemma* dim_eq_card_basis
- \+/\- *lemma* finrank_eq_card_basis
- \+/\- *lemma* finrank_eq_card_basis'
- \+/\- *lemma* finrank_eq_card_finset_basis
- \+ *lemma* basis_unique.repr_eq_zero_iff
- \+ *lemma* basis_singleton_apply
- \+ *lemma* range_basis_singleton
- \+ *lemma* basis.subset_extend
- \+ *lemma* finrank_eq_zero_of_basis_imp_not_finite
- \+ *lemma* finrank_eq_zero_of_basis_imp_false
- \+ *lemma* finrank_eq_zero_of_not_exists_basis_finite
- \+ *lemma* coe_basis_of_span_eq_top_of_card_eq_finrank
- \+ *lemma* coe_basis_of_linear_independent_of_card_eq_finrank
- \+ *lemma* coe_finset_basis_of_linear_independent_of_card_eq_finrank
- \+ *lemma* coe_set_basis_of_linear_independent_of_card_eq_finrank
- \+/\- *lemma* finrank_eq_one_iff
- \- *lemma* exists_is_basis_finite
- \- *lemma* exists_is_basis_finset
- \- *lemma* equiv_fin
- \- *lemma* equiv_fin_of_dim_eq
- \- *lemma* fin_basis
- \- *lemma* exists_is_basis_singleton
- \- *lemma* is_basis_of_finrank_zero
- \- *lemma* is_basis_of_finrank_zero'
- \- *lemma* is_basis_of_span_eq_top_of_card_eq_finrank
- \- *lemma* finset_is_basis_of_span_eq_top_of_card_eq_finrank
- \- *lemma* set_is_basis_of_span_eq_top_of_card_eq_finrank
- \- *lemma* is_basis_of_linear_independent_of_card_eq_finrank
- \- *lemma* finset_is_basis_of_linear_independent_of_card_eq_finrank
- \- *lemma* set_is_basis_of_linear_independent_of_card_eq_finrank
- \- *lemma* singleton_is_basis

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* dom_lcongr_apply

Modified src/linear_algebra/finsupp_vector_space.lean
- \+ *lemma* basis_repr
- \+ *lemma* coe_basis
- \+ *lemma* coe_basis_single_one
- \- *lemma* is_basis_single
- \- *lemma* is_basis_single_one
- \- *lemma* is_basis.tensor_product
- \+ *def* basis.tensor_product

Modified src/linear_algebra/free_algebra.lean
- \- *lemma* is_basis_free_monoid

Modified src/linear_algebra/free_module.lean
- \+/\- *lemma* eq_bot_of_rank_eq_zero
- \+/\- *lemma* eq_bot_of_generator_maximal_map_eq_zero
- \+ *lemma* basis.card_le_card_of_linear_independent_aux
- \+ *lemma* basis.card_le_card_of_linear_independent
- \- *lemma* is_basis.card_le_card_of_linear_independent_aux
- \- *lemma* is_basis.card_le_card_of_linear_independent
- \- *lemma* submodule.exists_is_basis_of_le
- \- *lemma* submodule.exists_is_basis_of_le_span
- \- *lemma* module.free_of_finite_type_torsion_free
- \- *lemma* module.free_of_finite_type_torsion_free'
- \- *theorem* submodule.exists_is_basis
- \+/\- *def* submodule.induction_on_rank_aux
- \+/\- *def* submodule.induction_on_rank

Modified src/linear_algebra/invariant_basis_number.lean


Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent.extend_subset
- \+ *lemma* linear_independent.subset_extend
- \+ *lemma* linear_independent.subset_span_extend
- \+ *lemma* linear_independent.linear_independent_extend

Modified src/linear_algebra/matrix.lean
- \+/\- *lemma* linear_map.to_matrix_id
- \+/\- *lemma* linear_map.to_matrix_one
- \+/\- *lemma* matrix.to_lin_one
- \+/\- *lemma* linear_map.to_matrix_alg_equiv_id
- \+/\- *lemma* matrix.to_lin_alg_equiv_one
- \+/\- *lemma* to_matrix_apply
- \+/\- *lemma* to_matrix_transpose_apply
- \+/\- *lemma* to_matrix_self
- \+/\- *lemma* sum_to_matrix_smul_self
- \+/\- *lemma* to_lin_to_matrix
- \+ *lemma* basis_to_matrix_mul_linear_map_to_matrix
- \+ *lemma* linear_map_to_matrix_mul_basis_to_matrix
- \+ *lemma* basis.to_matrix_mul_to_matrix
- \+/\- *lemma* linear_equiv.is_unit_det
- \+ *lemma* basis.det_apply
- \+ *lemma* basis.det_self
- \+/\- *lemma* is_basis.iff_det
- \+ *lemma* matrix.to_lin_transpose
- \+/\- *lemma* left_mul_matrix_injective
- \+/\- *lemma* trace_aux_def
- \- *lemma* is_basis_to_matrix_mul_linear_map_to_matrix
- \- *lemma* linear_map_to_matrix_mul_is_basis_to_matrix
- \- *lemma* is_basis.to_matrix_mul_to_matrix
- \- *lemma* is_basis.det_apply
- \- *lemma* is_basis.det_self
- \- *lemma* linear_map.to_matrix_symm_transpose
- \+ *theorem* linear_map.to_matrix_reindex_range
- \+ *theorem* linear_map.to_matrix_alg_equiv_reindex_range
- \+/\- *theorem* trace_aux_eq
- \+ *theorem* trace_aux_reindex_range
- \+ *theorem* trace_eq_matrix_trace_of_finite_set
- \+/\- *theorem* trace_eq_matrix_trace
- \+/\- *theorem* trace_mul_comm
- \- *theorem* linear_map.to_matrix_range
- \- *theorem* linear_map.to_matrix_alg_equiv_range
- \- *theorem* trace_aux_eq'
- \- *theorem* trace_aux_range
- \+ *def* basis.to_matrix
- \+/\- *def* to_matrix_equiv
- \+/\- *def* linear_equiv.of_is_unit_det
- \+ *def* basis.det
- \+/\- *def* trace_aux
- \+/\- *def* trace
- \- *def* is_basis.to_matrix
- \- *def* is_basis.det

Modified src/linear_algebra/quadratic_form.lean


Modified src/linear_algebra/std_basis.lean
- \+ *lemma* basis_repr_std_basis
- \+ *lemma* basis_apply
- \+ *lemma* basis_repr
- \+ *lemma* basis_fun_apply
- \+ *lemma* basis_fun_repr
- \- *lemma* is_basis_std_basis
- \- *lemma* is_basis_fun₀
- \- *lemma* is_basis_fun
- \- *lemma* is_basis_fun_repr

Modified src/ring_theory/adjoin/power_basis.lean
- \- *lemma* power_basis_is_basis

Modified src/ring_theory/adjoin_root.lean
- \- *lemma* power_basis_is_basis
- \+ *def* power_basis_aux
- \+ *def* power_basis

Modified src/ring_theory/algebra_tower.lean
- \+ *theorem* basis.smul_repr
- \+ *theorem* basis.smul_repr_mk
- \+ *theorem* basis.smul_apply
- \- *theorem* is_basis.smul
- \- *theorem* is_basis.smul_repr
- \- *theorem* is_basis.smul_repr_mk

Modified src/ring_theory/mv_polynomial/basic.lean
- \+ *lemma* coe_basis_monomials
- \- *lemma* is_basis_monomials
- \+ *def* basis_monomials

Modified src/ring_theory/power_basis.lean
- \+ *lemma* coe_basis

Modified src/ring_theory/trace.lean
- \+/\- *lemma* trace_eq_matrix_trace



## [2021-05-10 07:36:13](https://github.com/leanprover-community/mathlib/commit/f985e36)
feat(group_theory/subgroup): add mem_map_of_mem ([#7459](https://github.com/leanprover-community/mathlib/pull/7459))
From LTE.
Written by @PatrickMassot
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* mem_map_of_mem
- \+ *lemma* apply_coe_mem_map

Modified src/group_theory/submonoid/operations.lean
- \+/\- *lemma* mem_map_of_mem
- \+ *lemma* apply_coe_mem_map

Modified src/linear_algebra/basic.lean
- \+ *lemma* apply_coe_mem_map

Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/localization.lean




## [2021-05-10 07:36:12](https://github.com/leanprover-community/mathlib/commit/4a8467a)
feat(data/equiv/basic): equiv.curry ([#7458](https://github.com/leanprover-community/mathlib/pull/7458))
This renames `equiv.arrow_arrow_equiv_prod_arrow` to `(equiv.curry _ _ _).symm` to make it easier to find and match `function.curry`.
* `cardinal.power_mul` is swapped, so that its name makes sense.
* renames `linear_equiv.uncurry` to `linear_equiv.curry` and swaps sides
Also add `@[simps]` to two equivs.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* curry
- \+/\- *def* prod_punit
- \+/\- *def* punit_prod
- \- *def* arrow_arrow_equiv_prod_arrow

Modified src/linear_algebra/basic.lean
- \+ *lemma* coe_curry
- \+ *lemma* coe_curry_symm
- \- *lemma* coe_uncurry
- \- *lemma* coe_uncurry_symm

Modified src/linear_algebra/matrix.lean


Modified src/set_theory/cardinal.lean
- \+/\- *theorem* power_mul

Modified src/set_theory/cardinal_ordinal.lean


Modified src/set_theory/cofinality.lean




## [2021-05-10 06:01:59](https://github.com/leanprover-community/mathlib/commit/7150c90)
refactor(ring_theory/localization): Golf two proofs ([#7520](https://github.com/leanprover-community/mathlib/pull/7520))
Golfing two proofs and changing their order.
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+/\- *lemma* at_prime.comap_maximal_ideal
- \+/\- *lemma* at_prime.map_eq_maximal_ideal



## [2021-05-09 22:18:48](https://github.com/leanprover-community/mathlib/commit/ea0043c)
feat(topology): tiny new lemmas ([#7554](https://github.com/leanprover-community/mathlib/pull/7554))
from LTE
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* has_basis.eq_of_same_basis

Modified src/topology/constructions.lean
- \+ *lemma* quotient.preimage_mem_nhds

Modified src/topology/order.lean
- \+ *lemma* preimage_nhds_coinduced



## [2021-05-09 12:20:12](https://github.com/leanprover-community/mathlib/commit/735a26e)
chore(group_theory): some new convenience lemmas ([#7555](https://github.com/leanprover-community/mathlib/pull/7555))
from LTE
#### Estimated changes
Modified src/group_theory/coset.lean


Modified src/group_theory/quotient_group.lean
- \+ *lemma* coe_mk'
- \+ *lemma* mk'_apply

Modified src/group_theory/subgroup.lean
- \+ *lemma* div_mem_comm_iff
- \+ *lemma* eq_iff

Modified src/topology/algebra/group.lean




## [2021-05-09 12:20:10](https://github.com/leanprover-community/mathlib/commit/581064f)
feat(uniform_space/cauchy): cauchy_seq lemmas ([#7528](https://github.com/leanprover-community/mathlib/pull/7528))
from the Liquid Tensor Experiment
#### Estimated changes
Modified src/analysis/calculus/fderiv_measurable.lean


Modified src/topology/instances/real.lean


Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy_seq_const
- \+ *lemma* cauchy_seq.subseq_subseq_mem
- \+ *lemma* cauchy_seq_iff'
- \+ *lemma* cauchy_seq_iff
- \+ *lemma* cauchy_seq.subseq_mem



## [2021-05-09 10:00:57](https://github.com/leanprover-community/mathlib/commit/bf229dd)
feat(topology/metric_space/basic): dist_ne_zero ([#7552](https://github.com/leanprover-community/mathlib/pull/7552))
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *theorem* dist_ne_zero



## [2021-05-08 13:26:29](https://github.com/leanprover-community/mathlib/commit/132328c)
feat(algebra/lie/weights): define weight spaces of Lie modules ([#7537](https://github.com/leanprover-community/mathlib/pull/7537))
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/lie/cartan_subalgebra.lean


Created src/algebra/lie/character.lean
- \+ *lemma* lie_character_apply_lie
- \+ *lemma* lie_character_apply_of_mem_derived
- \+ *def* lie_character_equiv_linear_dual

Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* lie_equiv.nilpotent_iff_equiv_nilpotent
- \- *lemma* lie_algebra.nilpotent_iff_equiv_nilpotent

Modified src/algebra/lie/submodule.lean
- \+ *lemma* mem_mk_iff
- \+ *lemma* subsingleton_iff
- \+ *lemma* nontrivial_iff

Created src/algebra/lie/weights.lean
- \+ *lemma* mem_pre_weight_space
- \+ *lemma* lie_mem_pre_weight_space_of_mem_pre_weight_space
- \+ *lemma* mem_weight_space
- \+ *lemma* zero_weight_space_eq_top_of_nilpotent'
- \+ *lemma* coe_weight_space_of_top
- \+ *lemma* zero_weight_space_eq_top_of_nilpotent
- \+ *lemma* is_weight_zero_of_nilpotent
- \+ *lemma* zero_root_space_eq_top_of_nilpotent
- \+ *def* pre_weight_space
- \+ *def* weight_space
- \+ *def* is_weight

Modified src/data/nat/basic.lean
- \+ *lemma* le_or_le_of_add_eq_add_pred

Modified src/linear_algebra/basic.lean
- \+ *lemma* pow_map_zero_of_le
- \+ *lemma* commute_pow_left_of_commute



## [2021-05-08 08:13:59](https://github.com/leanprover-community/mathlib/commit/4a8a595)
feat(topology/subset_properties, homeomorph): lemmata about embeddings ([#7431](https://github.com/leanprover-community/mathlib/pull/7431))
Two lemmata: (i) embedding to homeomorphism (ii) a closed embedding is proper
Coauthored with @hrmacbeth
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* self_comp_of_injective_symm

Modified src/topology/homeomorph.lean


Modified src/topology/subset_properties.lean
- \+ *lemma* closed_embedding.tendsto_cocompact



## [2021-05-08 05:52:42](https://github.com/leanprover-community/mathlib/commit/583ad82)
feat(algebraic_geometry/structure_sheaf): Structure sheaf on basic opens ([#7405](https://github.com/leanprover-community/mathlib/pull/7405))
Proves that `to_basic_open` is an isomorphism of commutative rings. Also adds Hartshorne as a reference.
#### Estimated changes
Modified docs/references.bib


Modified src/algebraic_geometry/structure_sheaf.lean
- \+/\- *lemma* to_basic_open_mk'
- \+/\- *lemma* localization_to_basic_open
- \+/\- *lemma* to_basic_open_to_map
- \+ *lemma* to_basic_open_injective
- \+ *lemma* locally_const_basic_open
- \+ *lemma* normalize_finite_fraction_representation
- \+ *lemma* to_basic_open_surjective
- \+/\- *def* to_basic_open
- \+ *def* basic_open_iso



## [2021-05-07 22:54:26](https://github.com/leanprover-community/mathlib/commit/dbcd454)
feat(topology/category/*): Add alternative explicit limit cones for `Top`, etc. and shows `X : Profinite` is a limit of finite sets. ([#7448](https://github.com/leanprover-community/mathlib/pull/7448))
This PR redefines `Top.limit_cone`, and defines similar explicit limit cones for `CompHaus` and `Profinite`.
Using the definition with the subspace topology makes the proofs that the limit is compact, t2 and/or totally disconnected much easier.
This also expresses any `X : Profinite` as a limit of its discrete quotients, which are all finite.
#### Estimated changes
Modified src/topology/category/CompHaus.lean
- \+ *def* limit_cone
- \+ *def* limit_cone_is_limit

Created src/topology/category/Profinite/as_limit.lean
- \+ *def* fintype_diagram
- \+ *def* as_limit_cone
- \+ *def* iso_as_limit_cone_lift
- \+ *def* as_limit_cone_iso
- \+ *def* as_limit
- \+ *def* lim

Renamed src/topology/category/Profinite.lean to src/topology/category/Profinite/default.lean
- \+ *def* limit_cone
- \+ *def* limit_cone_is_limit

Modified src/topology/category/Top/limits.lean




## [2021-05-07 22:54:25](https://github.com/leanprover-community/mathlib/commit/515fb2f)
feat(group_theory/perm/*): lemmas about `extend_domain`, `fin_rotate`, and `fin.cycle_type` ([#7447](https://github.com/leanprover-community/mathlib/pull/7447))
Shows how `disjoint`, `support`, `is_cycle`, and `cycle_type` behave under `extend_domain`
Calculates `support` and `cycle_type` for `fin_rotate` and `fin.cycle_type`
Shows that the normal closure of `fin_rotate 5` in `alternating_group (fin 5)` is the whole alternating group.
#### Estimated changes
Modified src/analysis/normed_space/hahn_banach.lean


Modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* cycle_type_extend_domain

Modified src/group_theory/perm/cycles.lean
- \+ *lemma* is_cycle.extend_domain

Modified src/group_theory/perm/fin.lean
- \+ *lemma* support_fin_rotate
- \+ *lemma* support_fin_rotate_of_le
- \+ *lemma* is_cycle_fin_rotate
- \+ *lemma* is_cycle_fin_rotate_of_le
- \+ *lemma* cycle_type_fin_rotate
- \+ *lemma* cycle_type_fin_rotate_of_le
- \+ *lemma* is_cycle_cycle_range
- \+ *lemma* cycle_type_cycle_range
- \+ *lemma* is_three_cycle_cycle_range_two

Modified src/group_theory/perm/sign.lean
- \+ *lemma* disjoint.extend_domain

Modified src/group_theory/perm/support.lean
- \+ *lemma* support_extend_domain
- \+ *lemma* card_support_extend_domain

Modified src/group_theory/specific_groups/alternating.lean
- \+ *lemma* is_three_cycle.mem_alternating_group
- \+ *lemma* fin_rotate_bit1_mem_alternating_group
- \+ *lemma* is_conj_of
- \+ *lemma* is_three_cycle_is_conj
- \+ *lemma* is_three_cycle.alternating_normal_closure
- \+ *lemma* normal_closure_fin_rotate_five

Modified src/group_theory/subgroup.lean
- \+ *lemma* _root_.subgroup.subtype_range

Modified src/linear_algebra/bilinear_form.lean




## [2021-05-07 20:26:33](https://github.com/leanprover-community/mathlib/commit/5cfcb6a)
feat(ring_theory/hahn_series): order of a nonzero Hahn series, reindexing summable families ([#7444](https://github.com/leanprover-community/mathlib/pull/7444))
Defines `hahn_series.order`, the order of a nonzero Hahn series
Restates `add_val` in terms of `hahn_series.order`
Defines `hahn_series.summable_family.emb_domain`, reindexing a summable family using an embedding
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_dmem
- \+ *lemma* finprod_emb_domain'
- \+ *lemma* finprod_emb_domain

Modified src/ring_theory/hahn_series.lean
- \+ *lemma* ne_zero_of_coeff_ne_zero
- \+ *lemma* single_injective
- \+ *lemma* single_ne_zero
- \+ *lemma* order_zero
- \+ *lemma* order_of_ne
- \+ *lemma* coeff_order_ne_zero
- \+ *lemma* order_le_of_coeff_ne_zero
- \+ *lemma* order_single
- \+ *lemma* min_order_le_order_add
- \+ *lemma* order_one
- \+ *lemma* mul_coeff_order_add_order
- \+ *lemma* order_mul
- \+ *lemma* C_injective
- \+ *lemma* C_ne_zero
- \+ *lemma* order_C
- \+ *lemma* add_val_le_of_coeff_ne_zero
- \+ *lemma* hsum_sub
- \+ *lemma* emb_domain_apply
- \+ *lemma* emb_domain_image
- \+ *lemma* emb_domain_notin_range
- \+ *lemma* hsum_emb_domain
- \- *lemma* coeff_min_ne_zero
- \- *lemma* mul_coeff_min_add_min
- \+ *def* order
- \+ *def* emb_domain



## [2021-05-07 09:30:47](https://github.com/leanprover-community/mathlib/commit/72e151d)
feat(topology/uniform_space): is_closed_of_spread_out ([#7538](https://github.com/leanprover-community/mathlib/pull/7538))
See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/integers.20are.20closed.20in.20reals)
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+ *lemma* ball_inter_left
- \+ *lemma* ball_inter_right
- \+ *lemma* uniform_space.mem_closure_iff_symm_ball
- \+ *lemma* uniform_space.mem_closure_iff_ball

Modified src/topology/uniform_space/separation.lean
- \+ *lemma* eq_of_uniformity
- \+ *lemma* eq_of_uniformity_basis
- \+ *lemma* eq_of_forall_symmetric
- \+ *lemma* is_closed_of_spaced_out



## [2021-05-07 09:30:46](https://github.com/leanprover-community/mathlib/commit/301542a)
feat(group_theory.quotient_group): add eq_iff_div_mem ([#7523](https://github.com/leanprover-community/mathlib/pull/7523))
From LTE.
Written by @PatrickMassot
#### Estimated changes
Modified src/group_theory/quotient_group.lean
- \+ *lemma* eq_one_iff
- \+ *lemma* eq_iff_div_mem

Modified src/group_theory/subgroup.lean
- \+ *lemma* exists_inv_mem_iff_exists_mem



## [2021-05-07 09:30:45](https://github.com/leanprover-community/mathlib/commit/63a1782)
feat(field_theory/polynomial_galois_group): More flexible version of gal_action_hom_bijective_of_prime_degree ([#7508](https://github.com/leanprover-community/mathlib/pull/7508))
Since the number of non-real roots is even, we can make a more flexible version of `gal_action_hom_bijective_of_prime_degree`. This flexibility will be helpful when working with a specific polynomial.
#### Estimated changes
Modified src/field_theory/polynomial_galois_group.lean
- \+/\- *lemma* gal_action_hom_bijective_of_prime_degree_aux
- \+ *lemma* gal_action_hom_bijective_of_prime_degree'

Modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* two_dvd_card_support



## [2021-05-07 09:30:44](https://github.com/leanprover-community/mathlib/commit/565310f)
feat(data/nat/cast): pi.coe_nat and pi.nat_apply ([#7492](https://github.com/leanprover-community/mathlib/pull/7492))
#### Estimated changes
Modified src/data/int/cast.lean
- \+ *lemma* int_apply
- \+ *lemma* coe_int

Modified src/data/nat/cast.lean
- \+ *lemma* nat_apply
- \+ *lemma* coe_nat



## [2021-05-07 09:30:43](https://github.com/leanprover-community/mathlib/commit/190d4e2)
feat(algebra/module/basic): smul_add_hom_one ([#7461](https://github.com/leanprover-community/mathlib/pull/7461))
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *lemma* smul_add_hom_one

Modified src/group_theory/group_action/defs.lean
- \+ *lemma* const_smul_hom_one



## [2021-05-07 09:30:42](https://github.com/leanprover-community/mathlib/commit/91d5aa6)
feat(category_theory/arrow): arrow.mk_inj ([#7456](https://github.com/leanprover-community/mathlib/pull/7456))
From LTE
#### Estimated changes
Modified src/category_theory/arrow.lean
- \+ *theorem* mk_injective
- \+ *theorem* mk_inj



## [2021-05-07 09:30:40](https://github.com/leanprover-community/mathlib/commit/6fc8b2a)
refactor(*): more choice-free proofs ([#7455](https://github.com/leanprover-community/mathlib/pull/7455))
Now that lean v3.30 has landed (and specifically leanprover-community/lean[#560](https://github.com/leanprover-community/mathlib/pull/560)), we can finally make some progress on making a significant fraction of mathlib foundations choice-free. This PR does the following:
* No existing theorem statements have changed (except `linear_nonneg_ring` as noted below).
* A number of new theorems have been added to the `decidable` namespace, proving choice-free versions of lemmas under the assumption that something is decidable. These are primarily concentrated in partial orders and ordered rings, because total orders are already decidable, but there are some interesting lemmas about partial orders that require decidability of `le`.
* `linear_nonneg_ring` was changed to include decidability of `nonneg`, for consistency with linear ordered rings. No one is using this anyway so there shouldn't be any fallout.
* A lot of the `ordered_semiring` lemmas need `decidable` versions now because one of the core axioms, `mul_le_mul_of_nonneg_left`, is derived by LEM from an equivalent statement about lt instead of being an actual axiom. If this is refactored, these theorems can be removed again.
* The main files which were scoured of choicy proofs are: `algebra.ordered_group`,  `algebra.ordered_ring`, `data.nat.basic`, `data.int.basic`, `data.list.basic`, and `computability.halting`.
* The end goal of this was to prove `computable_pred.halting_problem` without assuming choice, finally validating a claim I made more than two years ago in my [paper](https://arxiv.org/abs/1810.08380) on the formalization.
I have not yet investigated a linter for making sure that these proofs stay choice-free; this can be done in a follow-up PR.
#### Estimated changes
Modified src/algebra/order.lean
- \+/\- *lemma* eq_iff_le_not_lt
- \- *lemma* le_imp_le_iff_lt_imp_lt
- \- *lemma* le_iff_le_iff_lt_iff_lt

Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_monoid.lean


Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* mul_le_mul_of_nonneg_left
- \+/\- *lemma* mul_le_mul_of_nonneg_right
- \+/\- *lemma* mul_le_mul
- \+/\- *lemma* mul_nonneg_le_one_le
- \+/\- *lemma* mul_nonneg
- \+/\- *lemma* mul_nonpos_of_nonneg_of_nonpos
- \+/\- *lemma* mul_nonpos_of_nonpos_of_nonneg
- \+/\- *lemma* mul_lt_mul
- \+/\- *lemma* mul_lt_mul'
- \+/\- *lemma* mul_lt_mul''
- \+/\- *lemma* le_mul_of_one_le_right
- \+/\- *lemma* le_mul_of_one_le_left
- \+/\- *lemma* lt_mul_of_one_lt_right
- \+/\- *lemma* lt_mul_of_one_lt_left
- \+/\- *lemma* add_le_mul_two_add
- \+/\- *lemma* one_le_mul_of_one_le_of_one_le
- \+/\- *lemma* one_lt_mul
- \+/\- *lemma* mul_le_one
- \+/\- *lemma* one_lt_mul_of_le_of_lt
- \+/\- *lemma* one_lt_mul_of_lt_of_le
- \+/\- *lemma* mul_le_of_le_one_right
- \+/\- *lemma* mul_le_of_le_one_left
- \+/\- *lemma* mul_lt_one_of_nonneg_of_lt_one_left
- \+/\- *lemma* mul_lt_one_of_nonneg_of_lt_one_right
- \+/\- *lemma* ordered_ring.mul_nonneg
- \+/\- *lemma* ordered_ring.mul_le_mul_of_nonneg_left
- \+/\- *lemma* ordered_ring.mul_le_mul_of_nonneg_right
- \+/\- *lemma* mul_le_mul_of_nonpos_left
- \+/\- *lemma* mul_le_mul_of_nonpos_right
- \+/\- *lemma* mul_nonneg_of_nonpos_of_nonpos
- \+/\- *lemma* le_of_mul_le_of_one_le
- \- *lemma* decidable.mul_le_mul_left
- \- *lemma* decidable.mul_le_mul_right
- \+/\- *theorem* mul_nonneg_iff_right_nonneg_of_pos
- \+/\- *def* to_linear_nonneg_ring

Modified src/computability/halting.lean


Modified src/computability/partrec.lean
- \+ *lemma* fix_aux
- \+ *theorem* _root_.decidable.partrec.const'
- \+/\- *theorem* const'
- \+/\- *theorem* sum_cases_right
- \+/\- *theorem* sum_cases_left
- \+/\- *theorem* fix

Modified src/data/int/basic.lean
- \+/\- *theorem* exists_least_of_bdd
- \+/\- *theorem* exists_greatest_of_bdd
- \+ *def* least_of_bdd
- \+ *def* greatest_of_bdd

Modified src/data/list/basic.lean
- \+ *theorem* _root_.decidable.list.eq_or_ne_mem_of_mem
- \+/\- *theorem* eq_or_ne_mem_of_mem
- \+ *theorem* _root_.decidable.list.lex.ne_iff
- \+/\- *theorem* ne_iff

Modified src/data/list/range.lean


Modified src/data/nat/basic.lean
- \+/\- *lemma* lt_of_div_lt_div

Modified src/data/nat/prime.lean


Modified src/data/nat/sqrt.lean


Modified src/data/set/basic.lean


Modified src/logic/nontrivial.lean
- \+/\- *lemma* exists_ne

Modified src/order/basic.lean


Modified src/order/bounded_lattice.lean
- \+/\- *lemma* lt_top_iff_ne_top

Modified src/order/lattice.lean




## [2021-05-07 09:30:39](https://github.com/leanprover-community/mathlib/commit/dec29aa)
feat(group_theory/solvable): S_5 is not solvable ([#7453](https://github.com/leanprover-community/mathlib/pull/7453))
This is a rather hacky proof that S_5 is not solvable. The proper proof via the simplicity of A_5 will eventually replace this. But until then, this result is needed for abel-ruffini.
Most of the work done by Jordan Brown
#### Estimated changes
Modified src/data/equiv/fintype.lean
- \+ *lemma* equiv.perm.via_fintype_embedding_apply_image
- \+ *lemma* equiv.perm.via_fintype_embedding_apply_mem_range
- \+ *lemma* equiv.perm.via_fintype_embedding_apply_not_mem_range
- \+ *lemma* equiv.perm.via_fintype_embedding_sign
- \- *lemma* equiv.perm.via_embedding_apply_image
- \- *lemma* equiv.perm.via_embedding_apply_mem_range
- \- *lemma* equiv.perm.via_embedding_apply_not_mem_range
- \- *lemma* equiv.perm.via_embedding_sign
- \+ *def* equiv.perm.via_fintype_embedding
- \- *def* equiv.perm.via_embedding

Modified src/group_theory/perm/basic.lean
- \+ *lemma* extend_domain_hom_injective
- \+ *lemma* of_subtype_apply_coe
- \+ *lemma* via_embedding_apply
- \+ *lemma* via_embedding_apply_of_not_mem
- \+ *lemma* via_embedding_hom_apply
- \+ *lemma* via_embedding_hom_injective
- \+ *def* extend_domain_hom

Modified src/group_theory/perm/fin.lean


Modified src/group_theory/solvable.lean
- \+ *lemma* general_commutator_containment
- \+ *lemma* not_solvable_of_mem_derived_series
- \+ *lemma* equiv.perm.fin_5_not_solvable
- \+ *lemma* equiv.perm.not_solvable



## [2021-05-07 09:30:38](https://github.com/leanprover-community/mathlib/commit/95b91b3)
refactor(group_theory/perm/*): disjoint and support in own file ([#7450](https://github.com/leanprover-community/mathlib/pull/7450))
The group_theory/perm/sign file was getting large and too broad in scope. This refactor pulls out `perm.support`, `perm.is_swap`, and `perm.disjoint` into a separate file.
A simpler version of [#7118](https://github.com/leanprover-community/mathlib/pull/7118).
#### Estimated changes
Modified src/group_theory/perm/cycle_type.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean
- \- *lemma* disjoint.symm
- \- *lemma* disjoint_comm
- \- *lemma* disjoint.mul_comm
- \- *lemma* disjoint_one_left
- \- *lemma* disjoint_one_right
- \- *lemma* disjoint.mul_left
- \- *lemma* disjoint.mul_right
- \- *lemma* disjoint_prod_right
- \- *lemma* disjoint_prod_perm
- \- *lemma* nodup_of_pairwise_disjoint
- \- *lemma* pow_apply_eq_self_of_apply_eq_self
- \- *lemma* gpow_apply_eq_self_of_apply_eq_self
- \- *lemma* pow_apply_eq_of_apply_apply_eq_self
- \- *lemma* gpow_apply_eq_of_apply_apply_eq_self
- \- *lemma* disjoint.mul_apply_eq_iff
- \- *lemma* disjoint.mul_eq_one_iff
- \- *lemma* disjoint.gpow_disjoint_gpow
- \- *lemma* disjoint.pow_disjoint_pow
- \- *lemma* mem_support
- \- *lemma* support_eq_empty_iff
- \- *lemma* support_one
- \- *lemma* support_mul_le
- \- *lemma* exists_mem_support_of_mem_support_prod
- \- *lemma* support_pow_le
- \- *lemma* support_inv
- \- *lemma* apply_mem_support
- \- *lemma* pow_apply_mem_support
- \- *lemma* gpow_apply_mem_support
- \- *lemma* is_swap.of_subtype_is_swap
- \- *lemma* ne_and_ne_of_swap_mul_apply_ne_self
- \- *lemma* support_swap_mul_eq
- \- *lemma* card_support_eq_zero
- \- *lemma* one_lt_card_support_of_ne_one
- \- *lemma* card_support_ne_one
- \- *lemma* card_support_le_one
- \- *lemma* two_le_card_support_of_ne_one
- \- *lemma* card_support_swap_mul
- \- *lemma* support_swap
- \- *lemma* card_support_swap
- \- *lemma* card_support_eq_two
- \- *lemma* disjoint_iff_disjoint_support
- \- *lemma* disjoint.disjoint_support
- \- *lemma* disjoint.support_mul
- \- *lemma* disjoint.card_support_mul
- \- *lemma* disjoint_prod_list_of_disjoint
- \- *lemma* card_support_prod_list_of_pairwise_disjoint
- \- *def* disjoint
- \- *def* support
- \- *def* is_swap

Created src/group_theory/perm/support.lean
- \+ *lemma* disjoint.symm
- \+ *lemma* disjoint_comm
- \+ *lemma* disjoint.mul_comm
- \+ *lemma* disjoint_one_left
- \+ *lemma* disjoint_one_right
- \+ *lemma* disjoint_iff_eq_or_eq
- \+ *lemma* disjoint_refl_iff
- \+ *lemma* disjoint.inv_left
- \+ *lemma* disjoint.inv_right
- \+ *lemma* disjoint_inv_left_iff
- \+ *lemma* disjoint_inv_right_iff
- \+ *lemma* disjoint.mul_left
- \+ *lemma* disjoint.mul_right
- \+ *lemma* disjoint_prod_right
- \+ *lemma* disjoint_prod_perm
- \+ *lemma* nodup_of_pairwise_disjoint
- \+ *lemma* pow_apply_eq_self_of_apply_eq_self
- \+ *lemma* gpow_apply_eq_self_of_apply_eq_self
- \+ *lemma* pow_apply_eq_of_apply_apply_eq_self
- \+ *lemma* gpow_apply_eq_of_apply_apply_eq_self
- \+ *lemma* disjoint.mul_apply_eq_iff
- \+ *lemma* disjoint.mul_eq_one_iff
- \+ *lemma* disjoint.gpow_disjoint_gpow
- \+ *lemma* disjoint.pow_disjoint_pow
- \+ *lemma* is_swap.of_subtype_is_swap
- \+ *lemma* ne_and_ne_of_swap_mul_apply_ne_self
- \+ *lemma* mem_support
- \+ *lemma* not_mem_support
- \+ *lemma* support_eq_empty_iff
- \+ *lemma* support_one
- \+ *lemma* support_refl
- \+ *lemma* support_congr
- \+ *lemma* support_mul_le
- \+ *lemma* exists_mem_support_of_mem_support_prod
- \+ *lemma* support_pow_le
- \+ *lemma* support_inv
- \+ *lemma* apply_mem_support
- \+ *lemma* pow_apply_mem_support
- \+ *lemma* gpow_apply_mem_support
- \+ *lemma* disjoint_iff_disjoint_support
- \+ *lemma* disjoint.disjoint_support
- \+ *lemma* disjoint.support_mul
- \+ *lemma* support_prod_of_pairwise_disjoint
- \+ *lemma* support_prod_le
- \+ *lemma* support_gpow_le
- \+ *lemma* support_swap
- \+ *lemma* support_swap_iff
- \+ *lemma* support_swap_mul_swap
- \+ *lemma* support_swap_mul_ge_support_diff
- \+ *lemma* support_swap_mul_eq
- \+ *lemma* mem_support_swap_mul_imp_mem_support_ne
- \+ *lemma* card_support_eq_zero
- \+ *lemma* one_lt_card_support_of_ne_one
- \+ *lemma* card_support_ne_one
- \+ *lemma* card_support_le_one
- \+ *lemma* two_le_card_support_of_ne_one
- \+ *lemma* card_support_swap_mul
- \+ *lemma* card_support_swap
- \+ *lemma* card_support_eq_two
- \+ *lemma* disjoint.card_support_mul
- \+ *lemma* card_support_prod_list_of_pairwise_disjoint
- \+ *def* disjoint
- \+ *def* is_swap
- \+ *def* support



## [2021-05-07 09:30:37](https://github.com/leanprover-community/mathlib/commit/251a42b)
feat(ring_theory/finiteness): add monoid_algebra.ft_iff_fg ([#7445](https://github.com/leanprover-community/mathlib/pull/7445))
We prove here `add monoid_algebra.ft_iff_fg`: the monoid algebra is of finite type if and only if the monoid is finitely generated.
- [x] depends on: [#7409](https://github.com/leanprover-community/mathlib/pull/7409)
#### Estimated changes
Modified src/algebra/monoid_algebra.lean
- \+ *lemma* of'_eq_of

Modified src/ring_theory/finiteness.lean
- \+ *lemma* mem_adjoin_support
- \+ *lemma* exists_finset_adjoin_eq_top
- \+ *lemma* of'_mem_span
- \+ *lemma* mem_closure_of_mem_span_closure
- \+ *lemma* finite_type_iff_fg
- \+ *lemma* fg_of_finite_type
- \+/\- *lemma* mem_adjoint_support
- \+ *lemma* of_mem_span_of_iff



## [2021-05-07 09:30:36](https://github.com/leanprover-community/mathlib/commit/be1af7c)
feat(linear_algebra/quadratic_form): provide `distrib_mul_action S (quadratic_form M R)` when `S` has no addition. ([#7443](https://github.com/leanprover-community/mathlib/pull/7443))
The end goal here is to provide `has_scalar (units R) (quadratic_form M R)` for possible use in [#7427](https://github.com/leanprover-community/mathlib/pull/7427)
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean




## [2021-05-07 09:30:35](https://github.com/leanprover-community/mathlib/commit/5d873a6)
feat(algebra/monoid_algebra): add add_monoid_algebra_ring_equiv_direct_sum ([#7422](https://github.com/leanprover-community/mathlib/pull/7422))
The only interesting result here is:
    add_monoid_algebra_ring_equiv_direct_sum : add_monoid_algebra M ι ≃+* ⨁ i : ι, M
The rest of the new file is just boilerplate to translate `dfinsupp.single` into `direct_sum.of`.
#### Estimated changes
Created src/algebra/monoid_algebra_to_direct_sum.lean
- \+ *lemma* add_monoid_algebra.to_direct_sum_single
- \+ *lemma* direct_sum.to_add_monoid_algebra_of
- \+ *lemma* add_monoid_algebra.to_direct_sum_to_add_monoid_algebra
- \+ *lemma* direct_sum.to_add_monoid_algebra_to_direct_sum
- \+ *lemma* to_direct_sum_zero
- \+ *lemma* to_direct_sum_add
- \+ *lemma* to_direct_sum_mul
- \+ *lemma* to_add_monoid_algebra_zero
- \+ *lemma* to_add_monoid_algebra_add
- \+ *lemma* to_add_monoid_algebra_mul
- \+ *def* add_monoid_algebra.to_direct_sum
- \+ *def* direct_sum.to_add_monoid_algebra
- \+ *def* add_monoid_algebra_equiv_direct_sum



## [2021-05-07 09:30:34](https://github.com/leanprover-community/mathlib/commit/3a5c871)
refactor(polynomial/*): make polynomials irreducible ([#7421](https://github.com/leanprover-community/mathlib/pull/7421))
Polynomials are the most basic objects in field theory. Making them irreducible helps Lean, because it can not try to unfold things too far, and it helps the user because it forces him to use a sane API instead of mixing randomly stuff from finsupp and from polynomials, as used to be the case in mathlib before this PR.
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* monomial_eq_C_mul_X
- \+ *lemma* sum_monomial_eq
- \- *lemma* single_eq_C_mul_X
- \- *lemma* sum_monomial

Modified src/data/mv_polynomial/pderiv.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/basic.lean
- \+ *lemma* forall_iff_forall_finsupp
- \+ *lemma* exists_iff_exists_finsupp
- \+ *lemma* zero_to_finsupp
- \+ *lemma* one_to_finsupp
- \+ *lemma* add_to_finsupp
- \+ *lemma* neg_to_finsupp
- \+ *lemma* mul_to_finsupp
- \+ *lemma* smul_to_finsupp
- \+ *lemma* sum_to_finsupp
- \+/\- *lemma* support_zero
- \+ *lemma* to_finsupp_iso_monomial
- \+ *lemma* to_finsupp_iso_symm_single
- \+/\- *lemma* support_add
- \+/\- *lemma* C_0
- \+ *lemma* C_mul_monomial
- \+ *lemma* monomial_mul_C
- \+/\- *lemma* coeff_one_zero
- \+ *lemma* mem_support_iff
- \+ *lemma* not_mem_support_iff
- \+ *lemma* monomial_eq_C_mul_X
- \+/\- *lemma* add_hom_ext'
- \+ *lemma* sum_def
- \+ *lemma* sum_eq_of_subset
- \+ *lemma* mul_eq_sum_sum
- \+ *lemma* sum_zero_index
- \+ *lemma* sum_monomial_index
- \+/\- *lemma* sum_C_index
- \+ *lemma* sum_X_index
- \+ *lemma* sum_add_index
- \+ *lemma* sum_add'
- \+ *lemma* sum_add
- \+ *lemma* sum_smul_index
- \+ *lemma* support_erase
- \+ *lemma* monomial_add_erase
- \+ *lemma* coeff_erase
- \+ *lemma* erase_zero
- \+ *lemma* erase_monomial
- \+ *lemma* erase_same
- \+ *lemma* erase_ne
- \+/\- *lemma* coeff_neg
- \+/\- *lemma* coeff_sub
- \- *lemma* monomial_def
- \- *lemma* coeff_mk
- \- *lemma* single_eq_C_mul_X
- \+ *def* monomial_fun
- \+ *def* to_finsupp_iso
- \+/\- *def* support
- \+/\- *def* monomial
- \+/\- *def* C
- \+/\- *def* coeff
- \+ *def* sum
- \- *def* polynomial

Modified src/data/polynomial/coeff.lean
- \+/\- *lemma* coeff_add
- \+ *lemma* support_smul
- \+/\- *lemma* coeff_sum
- \- *lemma* sum_def
- \- *lemma* mem_support_iff
- \- *lemma* not_mem_support_iff
- \- *lemma* span_le_of_coeff_mem_C_inverse
- \- *lemma* mem_span_C_coeff
- \- *lemma* exists_coeff_not_mem_C_inverse

Modified src/data/polynomial/degree/definitions.lean
- \+/\- *lemma* nat_degree_le_nat_degree
- \+/\- *lemma* degree_C_le
- \+ *lemma* nat_degree_add_le
- \+ *lemma* degree_smul_le
- \+ *lemma* nat_degree_smul_le

Modified src/data/polynomial/degree/lemmas.lean
- \- *lemma* degree_map_le
- \- *lemma* nat_degree_map_le

Modified src/data/polynomial/degree/trailing_degree.lean
- \+ *lemma* trailing_coeff_zero

Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/div.lean


Modified src/data/polynomial/erase_lead.lean


Modified src/data/polynomial/eval.lean
- \+ *lemma* eval₂_to_finsupp_eq_lift_nc
- \+/\- *lemma* eval_eq_sum
- \+/\- *lemma* eval_eq_finset_sum
- \+ *lemma* degree_map_le
- \+ *lemma* nat_degree_map_le
- \- *lemma* eval₂_eq_lift_nc

Modified src/data/polynomial/identities.lean


Modified src/data/polynomial/induction.lean
- \+ *lemma* span_le_of_coeff_mem_C_inverse
- \+ *lemma* mem_span_C_coeff
- \+ *lemma* exists_coeff_not_mem_C_inverse

Modified src/data/polynomial/integral_normalization.lean


Modified src/data/polynomial/iterated_deriv.lean


Modified src/data/polynomial/lifts.lean


Modified src/data/polynomial/mirror.lean
- \+/\- *lemma* mirror_zero

Modified src/data/polynomial/monic.lean


Modified src/data/polynomial/monomial.lean
- \+ *lemma* monomial_one_eq_iff
- \+ *lemma* card_support_le_one_iff_monomial
- \- *lemma* C_mul_monomial
- \- *lemma* monomial_mul_C

Modified src/data/polynomial/reverse.lean


Modified src/data/polynomial/ring_division.lean


Modified src/field_theory/adjoin.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/minpoly.lean


Modified src/field_theory/separable.lean
- \+/\- *theorem* coeff_contract
- \- *theorem* expand_eq_map_domain

Modified src/field_theory/splitting_field.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/localization.lean
- \+ *lemma* coeff_integer_normalization_of_not_mem_support

Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* frange_zero
- \+ *lemma* mem_frange_iff
- \+ *lemma* frange_one
- \+ *lemma* coeff_mem_frange
- \+ *lemma* support_restriction
- \+ *lemma* support_to_subring
- \+ *lemma* coeff_of_subring
- \+ *lemma* linear_independent_powers_iff_aeval
- \- *lemma* linear_independent_powers_iff_eval₂
- \+/\- *theorem* degree_restriction
- \+/\- *theorem* restriction_zero
- \+/\- *theorem* coeff_to_subring
- \+/\- *theorem* coeff_to_subring'
- \+/\- *theorem* degree_to_subring
- \+/\- *theorem* nat_degree_to_subring
- \+/\- *theorem* to_subring_zero
- \+ *def* frange

Modified src/ring_theory/polynomial/content.lean


Modified src/ring_theory/polynomial/scale_roots.lean


Modified src/ring_theory/polynomial_algebra.lean
- \+ *lemma* support_subset_support_mat_poly_equiv

Modified src/ring_theory/power_basis.lean
- \- *lemma* polynomial.mem_supported_range

Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/roots_of_unity.lean




## [2021-05-07 09:30:33](https://github.com/leanprover-community/mathlib/commit/322ccc5)
feat(finset/basic): downward induction for finsets ([#7379](https://github.com/leanprover-community/mathlib/pull/7379))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* strong_downward_induction_eq
- \+ *lemma* strong_downward_induction_on_eq
- \+ *def* strong_downward_induction
- \+ *def* strong_downward_induction_on

Modified src/data/multiset/basic.lean
- \+ *lemma* strong_downward_induction_eq
- \+ *lemma* strong_downward_induction_on_eq
- \+ *def* strong_downward_induction
- \+ *def* strong_downward_induction_on



## [2021-05-07 09:30:31](https://github.com/leanprover-community/mathlib/commit/11a06de)
feat(order/closure): closure of unions and bUnions ([#7361](https://github.com/leanprover-community/mathlib/pull/7361))
prove closure_closure_union and similar
#### Estimated changes
Modified src/order/closure.lean
- \+ *lemma* closure_mem_mk₃
- \+ *lemma* closure_le_mk₃_iff
- \+/\- *lemma* closure_top
- \+ *lemma* closure_inf_le
- \+ *lemma* closure_sup_closure_le
- \+/\- *lemma* closure_le_closed_iff_le
- \+ *lemma* eq_mk₃_closed
- \+ *lemma* mem_mk₃_closed
- \+ *lemma* closure_sup_closure_left
- \+ *lemma* closure_sup_closure_right
- \+ *lemma* closure_sup_closure
- \+ *lemma* closure_supr_closure
- \+ *lemma* closure_bsupr_closure
- \- *lemma* closure_inter_le
- \- *lemma* closure_union_closure_le
- \+ *def* mk₂
- \+ *def* mk₃

Modified src/order/complete_lattice.lean
- \+ *theorem* Sup_le_Sup_of_subset_insert_bot
- \- *theorem* Sup_le_Sup_of_subset_instert_bot



## [2021-05-07 09:30:30](https://github.com/leanprover-community/mathlib/commit/b20e664)
feat(order/well_founded_set): Higman's Lemma ([#7212](https://github.com/leanprover-community/mathlib/pull/7212))
Proves Higman's Lemma: if `r` is partially well-ordered on `s`, then `list.sublist_forall2` is partially well-ordered on the set of lists whose elements are in `s`.
#### Estimated changes
Modified docs/references.bib


Modified src/order/well_founded_set.lean
- \+ *lemma* iff_forall_not_is_bad_seq
- \+ *lemma* exists_min_bad_of_exists_bad
- \+ *lemma* iff_not_exists_is_min_bad_seq
- \+ *lemma* partially_well_ordered_on_sublist_forall₂
- \+/\- *theorem* partially_well_ordered_on
- \+/\- *theorem* is_pwo
- \+/\- *theorem* well_founded_on
- \+/\- *theorem* is_wf
- \+ *def* is_bad_seq
- \+ *def* is_min_bad_seq



## [2021-05-07 05:00:03](https://github.com/leanprover-community/mathlib/commit/cd5864f)
chore(scripts): update nolints.txt ([#7541](https://github.com/leanprover-community/mathlib/pull/7541))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-05-07 05:00:02](https://github.com/leanprover-community/mathlib/commit/6a7ddcc)
ci(.github/workflows/{build,dependent-issues}.yml): auto-cancel workflows on previous commits ([#7536](https://github.com/leanprover-community/mathlib/pull/7536))
After this is merged, pushing a new commit to a branch in this repo should cancel the "continuous integration" and "dependent issues" workflows running on any older commits on that branch.
#### Estimated changes
Modified .github/workflows/build.yml


Modified .github/workflows/dependent-issues.yml




## [2021-05-07 05:00:01](https://github.com/leanprover-community/mathlib/commit/93f9b3d)
ci(.github/workflows/build.yml): switch to trepplein ([#7532](https://github.com/leanprover-community/mathlib/pull/7532))
Reduces the leanchecker time from 6+57 minutes to 6+16 minutes.
#### Estimated changes
Modified .github/workflows/build.yml




## [2021-05-07 04:59:59](https://github.com/leanprover-community/mathlib/commit/f44a5eb)
feat(category_theory/concrete_category): id_apply, comp_apply ([#7530](https://github.com/leanprover-community/mathlib/pull/7530))
This PR renames
* `category_theory.coe_id` to `category_theory.id_apply`
* `category_theory.coe_comp` to `category_theory.comp_apply`
The names that are hence free up
are then redefined for "unapplied" versions of the same lemmas.
The `elementwise` tactic uses the old lemmas (with their new names).
We need minor fixes in the rest of the library because of the name changes.
#### Estimated changes
Modified src/algebra/category/Group/colimits.lean


Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/category_theory/abelian/diagram_lemmas/four.lean


Modified src/category_theory/concrete_category/basic.lean
- \+/\- *lemma* coe_id
- \+/\- *lemma* coe_comp
- \+ *lemma* id_apply
- \+ *lemma* comp_apply

Modified src/tactic/elementwise.lean


Modified src/topology/sheaves/stalks.lean




## [2021-05-07 04:59:59](https://github.com/leanprover-community/mathlib/commit/0ead8ee)
feat(ring_theory/localization): Characterize units in localization at prime ideal ([#7519](https://github.com/leanprover-community/mathlib/pull/7519))
Adds a few lemmas characterizing units and nonunits (elements of the maximal ideal) in the localization at a prime ideal.
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *lemma* at_prime.is_unit_to_map_iff
- \+ *lemma* at_prime.to_map_mem_maximal_iff
- \+ *lemma* at_prime.is_unit_mk'_iff
- \+ *lemma* at_prime.mk'_mem_maximal_iff



## [2021-05-07 04:59:57](https://github.com/leanprover-community/mathlib/commit/755cb75)
feat(data/list/basic): non-meta to_chunks ([#7517](https://github.com/leanprover-community/mathlib/pull/7517))
A non-meta definition of the `list.to_chunks` method, plus some basic theorems about it.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* to_chunks_nil
- \+ *theorem* to_chunks_aux_eq
- \+ *theorem* to_chunks_eq_cons'
- \+ *theorem* to_chunks_eq_cons
- \+ *theorem* to_chunks_aux_join
- \+ *theorem* to_chunks_join
- \+ *theorem* to_chunks_length_le

Modified src/data/list/defs.lean
- \+ *def* to_chunks_aux
- \+ *def* to_chunks



## [2021-05-07 04:59:56](https://github.com/leanprover-community/mathlib/commit/930485c)
feat(linear_algebra/tensor_product): distrib_mul_actions are inherited ([#7516](https://github.com/leanprover-community/mathlib/pull/7516))
It turns out that `tensor_product.has_scalar` requires only `distrib_mul_action` and not `semimodule` on its components.
As a result, a tensor product can inherit the `distrib_mul_action` structure of its components too.
Notably, this would enable `has_scalar (units R) (M ⊗[R] N)` in future.
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean




## [2021-05-07 04:59:55](https://github.com/leanprover-community/mathlib/commit/b903ea2)
chore(algebra/module/linear_map): add missing rfl lemmas ([#7515](https://github.com/leanprover-community/mathlib/pull/7515))
I've found these most useful for writing along in reverse so that I can use `linear_map.map_smul_of_tower`.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *lemma* add_monoid_hom.coe_to_int_linear_map
- \+ *lemma* add_monoid_hom.coe_to_rat_linear_map



## [2021-05-07 04:59:54](https://github.com/leanprover-community/mathlib/commit/6d25f3a)
feat(category_theory/opposites): Adds equivalences for functor categories. ([#7505](https://github.com/leanprover-community/mathlib/pull/7505))
This PR adds the following equivalences for categories `C` and `D`:
1. `(C ⥤ D)ᵒᵖ ≌ Cᵒᵖ ⥤ Dᵒᵖ` induced by `op` and `unop`.
2.  `(Cᵒᵖ ⥤ D)ᵒᵖ ≌ (C ⥤ Dᵒᵖ)` induced by `left_op` and `right_op`.
#### Estimated changes
Modified src/category_theory/opposites.lean
- \+/\- *def* op_unop_iso
- \+/\- *def* unop_op_iso
- \+ *def* left_op_right_op_iso
- \+ *def* right_op_left_op_iso
- \+ *def* op_unop_equiv
- \+ *def* left_op_right_op_equiv



## [2021-05-07 04:59:53](https://github.com/leanprover-community/mathlib/commit/efb283c)
feat(data/dfinsupp): add `finset_sum_apply` and `coe_finset_sum` ([#7499](https://github.com/leanprover-community/mathlib/pull/7499))
The names of the new`add_monoid_hom`s parallel the names in my recent `quadratic_form` PR, [#7417](https://github.com/leanprover-community/mathlib/pull/7417).
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* coe_finset_sum
- \+ *lemma* finset_sum_apply
- \+ *def* coe_fn_add_monoid_hom
- \+ *def* eval_add_monoid_hom



## [2021-05-07 04:59:51](https://github.com/leanprover-community/mathlib/commit/9acbe58)
feat(normed_space/normed_group_hom): add lemmas ([#7468](https://github.com/leanprover-community/mathlib/pull/7468))
From LTE.
Written by @PatrickMassot
#### Estimated changes
Modified src/analysis/normed_space/normed_group_hom.lean
- \+ *lemma* ker_zero
- \+ *lemma* coe_ker
- \+ *lemma* is_closed_ker

Modified src/group_theory/subgroup.lean
- \+ *lemma* coe_ker
- \+ *lemma* ker_one



## [2021-05-07 04:59:50](https://github.com/leanprover-community/mathlib/commit/154fda2)
feat(category_theory/subobjects): more about kernel and image subobjects ([#7467](https://github.com/leanprover-community/mathlib/pull/7467))
Lemmas about factoring through kernel subobjects, and functoriality of kernel subobjects.
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean


Modified src/category_theory/subobject/limits.lean
- \+ *lemma* factor_thru_kernel_subobject_comp_arrow
- \+ *lemma* kernel_subobject_map_arrow
- \+ *lemma* kernel_subobject_map_id
- \+ *lemma* kernel_subobject_map_comp
- \+ *lemma* image_subobject_arrow_comp_eq_zero
- \+ *def* factor_thru_kernel_subobject
- \+ *def* kernel_subobject_map



## [2021-05-06 22:46:23](https://github.com/leanprover-community/mathlib/commit/bb1fb89)
feat(data/real/basic): add real.Inf_le_iff ([#7524](https://github.com/leanprover-community/mathlib/pull/7524))
From LTE.
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* le_iff_forall_pos_le_add
- \+ *lemma* le_iff_forall_pos_lt_add

Modified src/data/real/basic.lean
- \+ *lemma* lt_Inf_add_pos
- \+ *lemma* add_pos_lt_Sup
- \+ *lemma* Inf_le_iff
- \+ *lemma* le_Sup_iff



## [2021-05-06 22:46:22](https://github.com/leanprover-community/mathlib/commit/e00d6e0)
feat(data/polynomial/*): Specific root sets ([#7510](https://github.com/leanprover-community/mathlib/pull/7510))
Adds lemmas for the root sets of a couple specific polynomials.
#### Estimated changes
Modified src/data/polynomial/field_division.lean
- \+ *lemma* root_set_C_mul_X_pow
- \+ *lemma* root_set_monomial
- \+ *lemma* root_set_X_pow

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* root_set_C



## [2021-05-06 22:46:21](https://github.com/leanprover-community/mathlib/commit/6f27ef7)
chore(data/equiv/basic): Show that `Pi_curry` is really just `sigma.curry` ([#7497](https://github.com/leanprover-community/mathlib/pull/7497))
Extracts some proofs to their own lemmas, and replaces definitions with existing ones.
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/data/sigma/basic.lean
- \+ *lemma* sigma.uncurry_curry
- \+ *lemma* sigma.curry_uncurry



## [2021-05-06 22:46:20](https://github.com/leanprover-community/mathlib/commit/9aed6c9)
feat(data/finsupp,linear_algebra): `finsupp.split` is an equivalence ([#7490](https://github.com/leanprover-community/mathlib/pull/7490))
This PR shows that for finite types `η`, `finsupp.split` is an equivalence between `(Σ (j : η), ιs j) →₀ α` and `Π j, (ιs j →₀ α)`.
To be used in the `bundled-basis` refactor
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* sigma_finsupp_equiv_pi_finsupp_apply
- \+ *lemma* sigma_finsupp_add_equiv_pi_finsupp_apply

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* sigma_finsupp_lequiv_pi_finsupp_apply
- \+ *lemma* sigma_finsupp_lequiv_pi_finsupp_symm_apply



## [2021-05-06 22:46:19](https://github.com/leanprover-community/mathlib/commit/48bdd1e)
feat(data/equiv,linear_algebra): `Pi_congr_right` for `mul_equiv` and `linear_equiv` ([#7489](https://github.com/leanprover-community/mathlib/pull/7489))
This PR generalizes `equiv.Pi_congr_right` to linear equivs, adding the `mul_equiv`/`add_equiv` version as well.
To be used in the `bundled-basis` refactor
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *lemma* Pi_congr_right_refl
- \+ *lemma* Pi_congr_right_symm
- \+ *lemma* Pi_congr_right_trans
- \+ *def* Pi_congr_right

Modified src/linear_algebra/basic.lean
- \+ *lemma* Pi_congr_right_refl
- \+ *lemma* Pi_congr_right_symm
- \+ *lemma* Pi_congr_right_trans
- \+ *def* Pi_congr_right



## [2021-05-06 22:46:18](https://github.com/leanprover-community/mathlib/commit/652357a)
feat(data/nat/choose/sum): alternate forms of the binomial theorem ([#7415](https://github.com/leanprover-community/mathlib/pull/7415))
#### Estimated changes
Modified src/data/nat/choose/sum.lean
- \+ *lemma* add_pow'
- \+ *theorem* add_pow
- \- *theorem* commute.add_pow



## [2021-05-06 10:56:24](https://github.com/leanprover-community/mathlib/commit/9c86e38)
refactor(ring_theory/ideal/operations.lean): make is_prime.comap an instance ([#7518](https://github.com/leanprover-community/mathlib/pull/7518))
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/ideal/operations.lean
- \- *theorem* is_prime.comap



## [2021-05-06 10:56:23](https://github.com/leanprover-community/mathlib/commit/13c41e1)
feat(category_theory/linear): linear functors ([#7369](https://github.com/leanprover-community/mathlib/pull/7369))
#### Estimated changes
Modified src/category_theory/linear/default.lean


Created src/category_theory/linear/linear_functor.lean
- \+ *lemma* map_smul
- \+ *lemma* coe_map_linear_map
- \+ *def* map_linear_map



## [2021-05-06 06:18:21](https://github.com/leanprover-community/mathlib/commit/7040c50)
feat(category_theory): the opposite of an abelian category is abelian ([#7514](https://github.com/leanprover-community/mathlib/pull/7514))
#### Estimated changes
Created src/category_theory/abelian/opposite.lean


Modified src/category_theory/fin_category.lean
- \+ *def* fin_category_opposite

Modified src/category_theory/limits/opposites.lean
- \+ *lemma* has_finite_coproducts_opposite
- \+ *lemma* has_finite_products_opposite
- \+ *lemma* has_finite_colimits_opposite
- \+ *lemma* has_finite_limits_opposite

Modified src/category_theory/limits/shapes/normal_mono.lean
- \+ *def* normal_epi_of_normal_mono_unop
- \+ *def* normal_mono_of_normal_epi_unop

Modified src/category_theory/limits/shapes/zero.lean


Created src/category_theory/preadditive/opposite.lean
- \+ *lemma* unop_zero
- \+ *lemma* unop_add



## [2021-05-06 06:18:20](https://github.com/leanprover-community/mathlib/commit/c4c6cd8)
feat(linear_algebra/finsupp): linear equivalence between `α × β →₀ M` and `α →₀ β →₀ M` ([#7472](https://github.com/leanprover-community/mathlib/pull/7472))
This PR extends the equivalence `finsupp.finsupp_prod_equiv` to a linear equivalence (to be used in the `bundled-basis` refactor).
#### Estimated changes
Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp_prod_lequiv_apply
- \+ *lemma* finsupp_prod_lequiv_symm_apply



## [2021-05-06 06:18:19](https://github.com/leanprover-community/mathlib/commit/9154a83)
feat(algebra/*, ring_theory/valuation/basic): `linear_ordered_add_comm_group_with_top`, `add_valuation.map_sub` ([#7452](https://github.com/leanprover-community/mathlib/pull/7452))
Defines `linear_ordered_add_comm_group_with_top`
Uses that to port a few more facts about `valuation`s to `add_valuation`s.
#### Estimated changes
Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_monoid.lean


Modified src/ring_theory/valuation/basic.lean
- \+ *lemma* map_sub
- \+ *lemma* map_sub_le
- \+ *lemma* map_inv
- \+ *lemma* map_units_inv
- \+ *lemma* map_neg
- \+ *lemma* map_sub_swap
- \+ *lemma* map_le_sub
- \+ *lemma* map_add_of_distinct_val
- \+ *lemma* map_eq_of_lt_sub
- \- *lemma* map_sub_le_max



## [2021-05-06 04:31:52](https://github.com/leanprover-community/mathlib/commit/6af5fbd)
feat(category_theory/.../zero): if a zero morphism is a mono, the source is zero ([#7462](https://github.com/leanprover-community/mathlib/pull/7462))
Some simple lemmas about zero morphisms.
#### Estimated changes
Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* functor.zero_obj
- \+ *lemma* functor.zero_map
- \+ *lemma* is_iso_of_source_target_iso_zero
- \+ *def* iso_zero_of_mono_zero
- \+ *def* iso_zero_of_epi_zero



## [2021-05-05 23:47:55](https://github.com/leanprover-community/mathlib/commit/009be86)
feat(measure_theory/set_integral): continuous_on.measurable_at_filter ([#7511](https://github.com/leanprover-community/mathlib/pull/7511))
#### Estimated changes
Modified src/measure_theory/set_integral.lean
- \+ *lemma* continuous_on.measurable_at_filter
- \+ *lemma* continuous_at.measurable_at_filter



## [2021-05-05 23:47:54](https://github.com/leanprover-community/mathlib/commit/709c73b)
feat(category_theory/Fintype): some lemmas and `Fintype_to_Profinite`.  ([#7491](https://github.com/leanprover-community/mathlib/pull/7491))
Adding some lemmas for morphisms on `Fintype` as functions, as well as `Fintype_to_Profinite`.
Part of the LTE.
#### Estimated changes
Modified src/category_theory/Fintype.lean
- \+ *lemma* coe_id
- \+ *lemma* coe_comp
- \+ *lemma* id_apply
- \+ *lemma* comp_apply

Modified src/topology/category/Profinite.lean
- \+ *def* of
- \+ *def* Fintype.discrete_topology
- \+ *def* Fintype.to_Profinite



## [2021-05-05 23:47:53](https://github.com/leanprover-community/mathlib/commit/1ef04bd)
feat(data/finsupp): prove `f.curry x y = f (x, y)` ([#7475](https://github.com/leanprover-community/mathlib/pull/7475))
This was surprisingly hard to prove actually!
To be used in the `bundled-basis` refactor
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* curry_apply



## [2021-05-05 23:47:52](https://github.com/leanprover-community/mathlib/commit/d3a46a7)
feat(algebra/big_operators): telescopic sums ([#7470](https://github.com/leanprover-community/mathlib/pull/7470))
This is restating things we already have in a form which is
slightly more convenient for the liquid tensor experiment
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* eq_sum_range_sub
- \+ *lemma* eq_sum_range_sub'



## [2021-05-05 23:47:51](https://github.com/leanprover-community/mathlib/commit/18ada66)
feat(order/filter_at_top_bot): extraction lemmas ([#7469](https://github.com/leanprover-community/mathlib/pull/7469))
from the liquid tensor experiment
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* extraction_forall_of_frequently
- \+ *lemma* extraction_forall_of_eventually
- \+ *lemma* extraction_forall_of_eventually'
- \+ *lemma* tendsto.subseq_mem
- \+ *lemma* tendsto_at_bot_diagonal
- \+ *lemma* tendsto_at_top_diagonal
- \+ *lemma* tendsto.prod_map_prod_at_bot
- \+ *lemma* tendsto.prod_map_prod_at_top
- \+ *lemma* tendsto.prod_at_bot
- \+ *lemma* tendsto.prod_at_top
- \+ *lemma* eventually_at_bot_prod_self
- \+ *lemma* eventually_at_top_prod_self
- \+ *lemma* eventually_at_bot_prod_self'
- \+ *lemma* eventually_at_top_prod_self'



## [2021-05-05 23:47:50](https://github.com/leanprover-community/mathlib/commit/7cc367b)
feat(category_theory/subobject): minor tweaks ([#7466](https://github.com/leanprover-community/mathlib/pull/7466))
A few minor tweaks to the `subobject` API that I wanted while working on homology.
#### Estimated changes
Modified src/category_theory/subobject/basic.lean
- \+ *lemma* of_le_mk_le_mk_of_comm

Modified src/category_theory/subobject/factor_thru.lean
- \+ *lemma* factor_thru_of_le
- \- *lemma* factor_thru_comp_of_le

Modified src/category_theory/subobject/lattice.lean
- \+ *lemma* underlying_iso_top_hom
- \- *lemma* underlying_iso_id_eq_top_coe_iso_self
- \- *def* top_coe_iso_self



## [2021-05-05 23:47:49](https://github.com/leanprover-community/mathlib/commit/e25cbe0)
feat(category_theory/quotient): the quotient functor is full and essentially surjective ([#7465](https://github.com/leanprover-community/mathlib/pull/7465))
#### Estimated changes
Modified src/category_theory/quotient.lean
- \+ *lemma* lift_map_functor_map



## [2021-05-05 23:47:48](https://github.com/leanprover-community/mathlib/commit/19b752c)
feat(category_theory/preadditive): reformulation of mono_of_kernel_zero ([#7464](https://github.com/leanprover-community/mathlib/pull/7464))
#### Estimated changes
Modified src/category_theory/preadditive/default.lean
- \+/\- *lemma* epi_of_cokernel_zero
- \+ *lemma* mono_of_kernel_iso_zero
- \+ *lemma* epi_of_cokernel_iso_zero



## [2021-05-05 23:47:47](https://github.com/leanprover-community/mathlib/commit/7794969)
feat(category_theory/.../additive_functor): additive functors preserve zero objects ([#7463](https://github.com/leanprover-community/mathlib/pull/7463))
#### Estimated changes
Modified src/category_theory/preadditive/additive_functor.lean
- \+ *def* map_zero_object



## [2021-05-05 23:47:46](https://github.com/leanprover-community/mathlib/commit/25387b6)
docs(overview): Add Stone-Weierstrass ([#7449](https://github.com/leanprover-community/mathlib/pull/7449))
#### Estimated changes
Modified docs/overview.yaml




## [2021-05-05 23:47:45](https://github.com/leanprover-community/mathlib/commit/f6f810c)
doc(algebraic_hierarchy): advice for adding new typeclasses ([#6854](https://github.com/leanprover-community/mathlib/pull/6854))
This is not intended as document describing all the design decisions behind our algebraic hierarchy, but rather some advice for contributors adding new typeclasses.
It can hopefully serve as a checklist for instances and definitions that should be made for any new algebraic structure being added to mathlib.
Please edit as you see fit, contribute new sections, etc. I haven't written anything yet about interactions with topology or order structures. Please consider this an invitation, or otherwise we can delete those headings later.
Thanks to @eric-wieser for providing the list of instances needed for each typeclass!
#### Estimated changes
Created src/algebra/hierarchy_design.lean




## [2021-05-05 18:50:21](https://github.com/leanprover-community/mathlib/commit/6d2869c)
feat(category_theory/.../images): image.pre_comp_epi_of_epi ([#7460](https://github.com/leanprover-community/mathlib/pull/7460))
The induced map from `image (f ≫ g)` to `image g` is an epimorphism when `f` is an epimorphism.
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean




## [2021-05-05 18:50:20](https://github.com/leanprover-community/mathlib/commit/79edde2)
feat(topology/discrete_quotient): Add a few lemmas about discrete quotients ([#7454](https://github.com/leanprover-community/mathlib/pull/7454))
This PR adds the `discrete_quotient.map` construction and generally improves on the `discrete_quotient` API.
#### Estimated changes
Modified src/topology/discrete_quotient.lean
- \+ *lemma* comap_id
- \+ *lemma* comap_comp
- \+ *lemma* comap_mono
- \+ *lemma* of_le_refl
- \+ *lemma* of_le_refl_apply
- \+ *lemma* of_le_comp
- \+ *lemma* of_le_comp_apply
- \+ *lemma* le_comap_id
- \+ *lemma* le_comap_comp
- \+ *lemma* le_comap_trans
- \+ *lemma* map_continuous
- \+ *lemma* map_proj
- \+ *lemma* map_proj_apply
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *lemma* of_le_map
- \+ *lemma* of_le_map_apply
- \+ *lemma* map_of_le
- \+ *lemma* map_of_le_apply
- \+/\- *def* comap
- \+ *def* le_comap
- \+ *def* map



## [2021-05-05 18:50:19](https://github.com/leanprover-community/mathlib/commit/84d27b4)
refactor(group_theory/group_action/defs): generalize smul_mul_assoc and mul_smul_comm ([#7441](https://github.com/leanprover-community/mathlib/pull/7441))
These lemmas did not need a full algebra structure; written this way, it permits usage on `has_scalar (units R) A` given `algebra R A` (in some future PR).
For now, the old algebra lemmas are left behind, to minimize the scope of this patch.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *lemma* mul_smul_comm
- \- *lemma* smul_mul_assoc
- \- *lemma* smul_mul_smul

Modified src/algebra/algebra/tower.lean


Modified src/group_theory/group_action/defs.lean
- \+ *lemma* mul_smul_comm
- \+ *lemma* smul_mul_assoc
- \+ *lemma* smul_mul_smul



## [2021-05-05 18:50:18](https://github.com/leanprover-community/mathlib/commit/140e17b)
feat(algebra/direct_sum_graded): a direct_sum of copies of a ring is itself a ring ([#7420](https://github.com/leanprover-community/mathlib/pull/7420))
Once this is in, it's straightforward to show `add_monoid_algebra R ι ≃+* ⨁ i : ι, R`
#### Estimated changes
Modified src/algebra/direct_sum_graded.lean
- \+ *lemma* semiring.direct_sum_mul



## [2021-05-05 18:50:17](https://github.com/leanprover-community/mathlib/commit/51bc1ca)
feat(algebra/direct_sum_graded): add direct_sum.to_semiring ([#7380](https://github.com/leanprover-community/mathlib/pull/7380))
This provides a convenient way to construct ring_homs out of `direct_sum`, and is a stronger version of `direct_sum.to_add_monoid` which applies in the presence of a `direct_sum.gmonoid` typeclass.
The new `direct_sum.lift_ring_hom` can be thought of as a universal property akin to `finsupp.lift_add_hom`.
#### Estimated changes
Modified src/algebra/direct_sum_graded.lean
- \+ *lemma* ring_hom_ext'
- \+ *lemma* to_semiring_of
- \+ *lemma* to_semiring_coe_add_monoid_hom
- \+ *def* to_semiring
- \+ *def* lift_ring_hom



## [2021-05-05 18:50:16](https://github.com/leanprover-community/mathlib/commit/93bc7e0)
feat(order): add some missing `pi` and `Prop` instances ([#7268](https://github.com/leanprover-community/mathlib/pull/7268))
#### Estimated changes
Modified src/order/boolean_algebra.lean


Modified src/order/bounded_lattice.lean
- \+ *lemma* le_Prop_eq
- \+ *lemma* sup_Prop_eq
- \+ *lemma* inf_Prop_eq
- \- *lemma* le_iff_imp

Modified src/order/complete_boolean_algebra.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* supr_subtype''
- \+/\- *lemma* Inf_Prop_eq
- \+/\- *lemma* Sup_Prop_eq
- \+/\- *lemma* infi_Prop_eq
- \+/\- *lemma* supr_Prop_eq
- \+/\- *lemma* infi_apply
- \+/\- *lemma* supr_apply

Modified src/topology/omega_complete_partial_order.lean




## [2021-05-05 18:50:15](https://github.com/leanprover-community/mathlib/commit/52268b8)
feat(linear_algebra): Vandermonde matrices and their determinant ([#7116](https://github.com/leanprover-community/mathlib/pull/7116))
This PR defines the `vandermonde` matrix and gives a formula for its determinant.
@paulvanwamelen: if you would like to have `det_vandermonde` in a different form (e.g. swap the order of the variables that are being summed), please let me know!
#### Estimated changes
Created src/linear_algebra/vandermonde.lean
- \+ *lemma* vandermonde_apply
- \+ *lemma* vandermonde_cons
- \+ *lemma* vandermonde_succ
- \+ *lemma* det_vandermonde
- \+ *def* vandermonde



## [2021-05-05 13:56:53](https://github.com/leanprover-community/mathlib/commit/a4d5ccb)
chore(order/complete_boolean_algebra): speed up Inf_sup_Inf ([#7506](https://github.com/leanprover-community/mathlib/pull/7506))
On my machine, avoiding `finish` takes the proof from 13s to 0.3s.
#### Estimated changes
Modified src/order/complete_boolean_algebra.lean




## [2021-05-05 13:56:52](https://github.com/leanprover-community/mathlib/commit/94150f3)
chore(group_theory/nielsen_schreier): typos in module doc-string ([#7500](https://github.com/leanprover-community/mathlib/pull/7500))
This fixes a discrepancy between the doc-string and the rest of the file.
#### Estimated changes
Modified src/group_theory/nielsen_schreier.lean




## [2021-05-05 13:56:51](https://github.com/leanprover-community/mathlib/commit/3a8796d)
feat(category_theory/path_category): extensionality for functors out of path category ([#7494](https://github.com/leanprover-community/mathlib/pull/7494))
This adds an extensionality lemma for functors out of a path category, which simplifies some proofs in the free-forgetful adjunction.
#### Estimated changes
Modified src/category_theory/category/Quiv.lean


Modified src/category_theory/eq_to_hom.lean
- \+ *lemma* eq_conj_eq_to_hom

Modified src/category_theory/path_category.lean
- \+ *lemma* ext_functor



## [2021-05-05 13:56:50](https://github.com/leanprover-community/mathlib/commit/18af6b5)
feat(algebra/module): `linear_equiv.refl.symm = refl` ([#7493](https://github.com/leanprover-community/mathlib/pull/7493))
To be part of the `bundled_basis` refactor
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *lemma* refl_symm



## [2021-05-05 13:56:49](https://github.com/leanprover-community/mathlib/commit/1823aee)
feat(algebra/module): `S`-linear equivs are also `R`-linear equivs ([#7476](https://github.com/leanprover-community/mathlib/pull/7476))
This PR extends `linear_map.restrict_scalars` to `linear_equiv`s.
To be used in the `bundled-basis` refactor.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *def* restrict_scalars



## [2021-05-05 13:56:48](https://github.com/leanprover-community/mathlib/commit/9b1b854)
feat(data/fintype/basic): add set.to_finset_range ([#7426](https://github.com/leanprover-community/mathlib/pull/7426))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* set.to_finset_range



## [2021-05-05 13:56:47](https://github.com/leanprover-community/mathlib/commit/bb9216c)
feat(category_theory/opposites): iso.unop ([#7400](https://github.com/leanprover-community/mathlib/pull/7400))
#### Estimated changes
Modified src/category_theory/opposites.lean
- \+ *lemma* unop_op
- \+ *lemma* op_unop
- \+ *def* unop



## [2021-05-05 13:56:45](https://github.com/leanprover-community/mathlib/commit/78e36a7)
feat(analysis/convex/extreme): extreme sets ([#7357](https://github.com/leanprover-community/mathlib/pull/7357))
define extreme sets
#### Estimated changes
Modified docs/references.bib


Modified src/analysis/convex/basic.lean
- \+/\- *lemma* segment_eq_image
- \+/\- *lemma* segment_eq_image'
- \+/\- *lemma* segment_translate_image
- \+ *lemma* open_segment_subset_segment
- \+ *lemma* mem_open_segment_of_ne_left_right
- \+ *lemma* open_segment_symm
- \+ *lemma* open_segment_same
- \+ *lemma* left_mem_open_segment_iff
- \+ *lemma* right_mem_open_segment_iff
- \+ *lemma* open_segment_eq_image
- \+ *lemma* open_segment_eq_image'
- \+ *lemma* open_segment_eq_image₂
- \+ *lemma* open_segment_eq_Ioo
- \+ *lemma* open_segment_eq_Ioo'
- \+ *lemma* mem_open_segment_translate
- \+ *lemma* open_segment_translate_preimage
- \+ *lemma* open_segment_translate_image
- \+ *lemma* open_segment_image
- \+/\- *lemma* convex_iff_segment_subset
- \+ *lemma* convex_iff_open_segment_subset
- \+/\- *lemma* convex.segment_subset
- \+ *lemma* convex.open_segment_subset
- \+ *lemma* convex.convex_remove_iff_not_mem_convex_hull_remove
- \+ *def* open_segment

Created src/analysis/convex/extreme.lean
- \+ *lemma* refl
- \+ *lemma* trans
- \+ *lemma* antisymm
- \+ *lemma* convex_diff
- \+ *lemma* inter
- \+ *lemma* Inter
- \+ *lemma* bInter
- \+ *lemma* sInter
- \+ *lemma* mono
- \+ *lemma* extreme_points_def
- \+ *lemma* mem_extreme_points_iff_forall_segment
- \+ *lemma* mem_extreme_points_iff_extreme_singleton
- \+ *lemma* extreme_points_subset
- \+ *lemma* extreme_points_empty
- \+ *lemma* extreme_points_singleton
- \+ *lemma* convex.mem_extreme_points_iff_convex_remove
- \+ *lemma* convex.mem_extreme_points_iff_mem_diff_convex_hull_remove
- \+ *lemma* inter_extreme_points_subset_extreme_points_of_subset
- \+ *lemma* extreme_points_subset_extreme_points
- \+ *lemma* extreme_points_eq
- \+ *lemma* extreme_points_convex_hull_subset
- \+ *def* is_extreme
- \+ *def* set.extreme_points

Modified src/data/set/intervals/image_preimage.lean
- \+ *lemma* image_mul_right_Ioo
- \+ *lemma* image_mul_left_Ioo



## [2021-05-05 12:20:10](https://github.com/leanprover-community/mathlib/commit/b765d4e)
Change the bors timeout to 8 hours ([#7513](https://github.com/leanprover-community/mathlib/pull/7513))
We've hit a 6 hour timeout repeatedly in the last few days, resulting in nothing getting built.
#### Estimated changes
Modified bors.toml




## [2021-05-04 02:29:18](https://github.com/leanprover-community/mathlib/commit/5a91d05)
feat(data/finset/lattice): add sup_image ([#7428](https://github.com/leanprover-community/mathlib/pull/7428))
This also renames `finset.map_sup` to `finset.sup_map` to match `finset.sup_insert` and `finset.sup_singleton`.
The `inf` versions are added too.
#### Estimated changes
Modified src/data/finset/fold.lean
- \+ *theorem* fold_image_idem

Modified src/data/finset/lattice.lean
- \+ *lemma* sup_image
- \+ *lemma* sup_map
- \+ *lemma* inf_image
- \+ *lemma* inf_map
- \- *lemma* map_sup
- \- *lemma* map_inf



## [2021-05-03 21:31:42](https://github.com/leanprover-community/mathlib/commit/3773525)
feat(ring_theory/finiteness): add lemmas ([#7409](https://github.com/leanprover-community/mathlib/pull/7409))
I add here some preliminary lemmas to prove that a monoid is finitely generated iff the monoid algebra is.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean
- \+ *lemma* of'_apply
- \+/\- *lemma* mem_span_support
- \+ *lemma* mem_span_support'
- \+ *def* of'

Modified src/ring_theory/finiteness.lean
- \+ *lemma* mem_adjoint_support
- \+ *lemma* support_gen_of_gen
- \+ *lemma* support_gen_of_gen'



## [2021-05-03 21:31:41](https://github.com/leanprover-community/mathlib/commit/67dad97)
chore(data/fintype): rework `fintype.equiv_fin` and dependencies ([#7136](https://github.com/leanprover-community/mathlib/pull/7136))
These changes should make the declarations `fintype.equiv_fin`, `fintype.card_eq`
and `fintype.equiv_of_card_eq` more convenient to use.
Renamed:
 * `fintype.equiv_fin` -> `fintype.trunc_equiv_fin`
Deleted:
 * `fintype.nonempty_equiv_of_card_eq` (use `fintype.equiv_of_card_eq` instead)
 * `fintype.exists_equiv_fin` (use `fintype.card` and `fintype.(trunc_)equiv_fin` instead)
Added:
 * `fintype.equiv_fin`: noncomputable, non-`trunc` version of `fintype.equiv_fin`
 * `fintype.equiv_of_card_eq`: noncomputable, non-`trunc` version of `fintype.trunc_equiv_of_card_eq`
 * `fintype.(trunc_)equiv_fin_of_card_eq` (intermediate result/specialization of `fintype.(trunc_)equiv_of_card_eq`
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60fintype.2Eequiv_fin.60.20.2B.20.60fin.2Ecast.60)
#### Estimated changes
Modified src/category_theory/Fintype.lean


Modified src/category_theory/limits/constructions/finite_products_of_binary_products.lean


Modified src/computability/turing_machine.lean


Modified src/data/equiv/list.lean


Modified src/data/fintype/basic.lean
- \- *lemma* nonempty_equiv_of_card_eq
- \- *theorem* exists_equiv_fin
- \+ *def* trunc_equiv_fin
- \+ *def* trunc_equiv_fin_of_card_eq
- \+ *def* trunc_equiv_of_card_eq
- \- *def* equiv_fin

Modified src/data/mv_polynomial/rename.lean


Modified src/data/set/finite.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/group_theory/perm/sign.lean


Modified src/linear_algebra/free_module.lean


Modified src/logic/small.lean


Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/topology/metric_space/gromov_hausdorff.lean




## [2021-05-03 17:06:15](https://github.com/leanprover-community/mathlib/commit/048240e)
chore(*): update to lean 3.30.0c ([#7264](https://github.com/leanprover-community/mathlib/pull/7264))
There's quite a bit of breakage from no longer reducing `acc.rec` so aggressively.  That is, a well-founded definition like `nat.factors` will no longer reduce definitionally.  Where you could write `rfl` before, you might now need to write `by rw nat.factors` or `by simp [nat.factors]`.
A more inconvenient side-effect of this change is that `dec_trivial` becomes less powerful, since it also relies on the definitional reduction.  For example `nat.factors 1 = []` is no longer true by `dec_trivial` (or `rfl`).  Often you can replace `dec_trivial` by `simp` or `norm_num`.
For extremely simple definitions that only use well-founded relations of rank ω, you could consider rewriting them to use structural recursion on a fuel parameter instead.  The functions `nat.mod` and `nat.div` in core have been rewritten in this way, please consult the [corresponding Lean PR](https://github.com/leanprover-community/lean/pull/570/files) for details on the implementation.
#### Estimated changes
Modified leanpkg.toml


Modified src/algebra/archimedean.lean
- \+ *lemma* round_zero
- \+ *lemma* round_one

Modified src/algebra/order.lean
- \- *lemma* le_of_not_lt
- \- *lemma* lt_or_le
- \- *lemma* le_or_lt
- \- *lemma* le_imp_le_of_lt_imp_lt

Modified src/algebra/ring/basic.lean
- \+ *lemma* to_monoid_with_zero_hom_eq_coe

Modified src/analysis/analytic/inverse.lean


Modified src/category_theory/equivalence.lean
- \+ *def* pow_nat

Modified src/computability/partrec.lean


Modified src/computability/partrec_code.lean


Modified src/computability/primrec.lean


Modified src/computability/turing_machine.lean


Modified src/data/complex/module.lean


Modified src/data/equiv/fin.lean


Modified src/data/equiv/list.lean
- \+/\- *theorem* decode_list_zero
- \+/\- *theorem* list_of_nat_zero

Modified src/data/fin.lean
- \+ *lemma* coe_bit0
- \+ *lemma* coe_bit1
- \+ *lemma* succ_one_eq_two
- \+ *lemma* zero_succ_above

Modified src/data/int/basic.lean
- \+/\- *theorem* zero_mod

Modified src/data/int/parity.lean


Modified src/data/list/rotate.lean
- \+/\- *lemma* rotate_nil

Modified src/data/list/sort.lean


Modified src/data/matrix/notation.lean


Modified src/data/nat/basic.lean
- \+/\- *theorem* size_zero
- \+/\- *theorem* size_one

Modified src/data/nat/bitwise.lean
- \+/\- *lemma* zero_lxor
- \+/\- *lemma* lxor_zero
- \+/\- *lemma* zero_land
- \+/\- *lemma* land_zero
- \+/\- *lemma* zero_lor
- \+/\- *lemma* lor_zero

Modified src/data/nat/digits.lean
- \+/\- *lemma* digits_aux_zero

Modified src/data/nat/log.lean


Modified src/data/nat/modeq.lean
- \+/\- *lemma* odd_mul_odd
- \+/\- *lemma* odd_of_mod_four_eq_one
- \+/\- *lemma* odd_of_mod_four_eq_three

Modified src/data/nat/pairing.lean
- \+ *lemma* unpair_zero

Modified src/data/nat/parity.lean


Modified src/data/nat/prime.lean
- \+/\- *lemma* factors_zero
- \+/\- *lemma* factors_one
- \+/\- *theorem* not_prime_zero
- \+/\- *theorem* not_prime_one
- \+/\- *theorem* prime_three

Modified src/data/nat/sqrt.lean
- \+ *lemma* sqrt_zero

Modified src/data/nat/totient.lean


Modified src/data/num/lemmas.lean
- \+ *theorem* of_nat'_zero
- \+/\- *theorem* of_nat'_eq

Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean
- \+/\- *lemma* coe_one

Modified src/data/pnat/factors.lean
- \+/\- *theorem* factor_multiset_one

Modified src/data/rat/basic.lean
- \+ *lemma* mk_zero_one
- \+ *lemma* mk_one_one
- \+ *lemma* mk_neg_one_one

Modified src/data/rat/cast.lean


Modified src/data/rat/order.lean


Modified src/data/vector2.lean


Modified src/data/zmod/basic.lean
- \+ *lemma* val_one'
- \+ *lemma* val_neg'
- \+ *lemma* val_mul'
- \+ *lemma* int_coe_eq_int_coe_iff'
- \+/\- *lemma* neg_eq_self_mod_two

Modified src/data/zmod/parity.lean


Modified src/data/zsqrtd/gaussian_int.lean


Modified src/field_theory/finite/basic.lean


Modified src/group_theory/perm/fin.lean


Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* univ_fin2

Modified src/linear_algebra/affine_space/independent.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/linear_algebra/matrix.lean


Modified src/number_theory/ADE_inequality.lean


Modified src/number_theory/arithmetic_function.lean
- \+/\- *lemma* card_factors_one
- \+/\- *lemma* card_distinct_factors_zero

Modified src/number_theory/bernoulli.lean
- \+/\- *lemma* bernoulli'_zero
- \+/\- *lemma* bernoulli_zero

Modified src/number_theory/primorial.lean


Modified src/number_theory/pythagorean_triples.lean
- \+ *lemma* sq_ne_two_fin_zmod_four
- \+ *lemma* int.sq_ne_two_mod_four

Modified src/ring_theory/int/basic.lean


Modified src/ring_theory/power_series/well_known.lean
- \+/\- *lemma* constant_coeff_exp

Modified src/set_theory/game/domineering.lean


Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/short.lean


Modified src/set_theory/game/winner.lean


Modified src/set_theory/pgame.lean
- \+/\- *theorem* equiv_refl

Modified src/tactic/norm_fin.lean
- \+/\- *theorem* normalize_fin.zero

Modified src/topology/continuous_function/stone_weierstrass.lean




## [2021-05-03 14:11:12](https://github.com/leanprover-community/mathlib/commit/7da8303)
feat(category_theory/preadditive): Schur's lemma ([#7366](https://github.com/leanprover-community/mathlib/pull/7366))
We prove Schur's lemma for `𝕜`-linear categories with finite dimensional hom spaces,
over an algebraically closed field `𝕜`:
the hom space `X ⟶ Y` between simple objects `X` and `Y` is at most one dimensional,
and is 1-dimensional iff `X` and `Y` are isomorphic.
#### Estimated changes
Modified src/category_theory/endomorphism.lean
- \+ *lemma* is_unit_iff_is_iso
- \+ *def* of
- \+ *def* as_hom

Modified src/category_theory/linear/default.lean


Modified src/category_theory/preadditive/default.lean


Modified src/category_theory/preadditive/schur.lean
- \+/\- *lemma* is_iso_of_hom_simple
- \+ *lemma* is_iso_iff_nonzero
- \+ *lemma* finrank_hom_simple_simple_eq_zero_of_not_iso
- \+ *lemma* finrank_endomorphism_eq_one
- \+ *lemma* finrank_endomorphism_simple_eq_one
- \+ *lemma* endomorphism_simple_eq_smul_id
- \+ *lemma* finrank_hom_simple_simple_le_one
- \+ *lemma* finrank_hom_simple_simple_eq_one_iff
- \+ *lemma* finrank_hom_simple_simple_eq_zero_iff
- \- *def* is_iso_equiv_nonzero

Modified src/category_theory/simple.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finrank_eq_one_iff_of_nonzero'



## [2021-05-03 07:41:58](https://github.com/leanprover-community/mathlib/commit/62c06a5)
feat(data/finset/basic): a finset has card at most one iff it is contained in a singleton ([#7404](https://github.com/leanprover-community/mathlib/pull/7404))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* card_le_one_iff_subset_singleton
- \+ *lemma* card_le_one_of_subsingleton
- \+ *lemma* one_lt_card_iff
- \+/\- *theorem* card_le_of_subset
- \+ *theorem* card_le_one_iff

Modified src/data/fintype/basic.lean
- \- *lemma* finset.card_le_one_iff
- \- *lemma* finset.card_le_one_of_subsingleton
- \- *lemma* finset.one_lt_card_iff



## [2021-05-02 18:59:48](https://github.com/leanprover-community/mathlib/commit/0cc3cd5)
feat(topology/category): Profinite has colimits ([#7434](https://github.com/leanprover-community/mathlib/pull/7434))
Show that a reflective subcategory of a cocomplete category is cocomplete, and derive that `CompHaus` and `Profinite` have colimits.
#### Estimated changes
Modified src/category_theory/monad/limits.lean
- \+ *lemma* has_colimits_of_shape_of_reflective
- \+ *lemma* has_colimits_of_reflective

Modified src/topology/category/CompHaus.lean


Modified src/topology/category/Profinite.lean




## [2021-05-02 14:19:06](https://github.com/leanprover-community/mathlib/commit/c7ba3dd)
refactor(linear_algebra/eigenspace): refactor exists_eigenvalue ([#7345](https://github.com/leanprover-community/mathlib/pull/7345))
We replace the proof of `exists_eigenvalue` with the more general fact:
```
/--
Every element `f` in a nontrivial finite-dimensional algebra `A`
over an algebraically closed field `K`
has non-empty spectrum:
that is, there is some `c : K` so `f - c • 1` is not invertible.
-/
lemma exists_spectrum_of_is_alg_closed_of_finite_dimensional (𝕜 : Type*) [field 𝕜] [is_alg_closed 𝕜]
  {A : Type*} [nontrivial A] [ring A] [algebra 𝕜 A] [I : finite_dimensional 𝕜 A] (f : A) :
  ∃ c : 𝕜, ¬ is_unit (f - algebra_map 𝕜 A c) := ...
```
We can then use this fact to prove Schur's lemma.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* map_list_prod
- \+ *lemma* map_multiset_prod

Modified src/algebra/group/units.lean
- \+ *lemma* is_unit.mul_iff

Modified src/data/list/basic.lean
- \+ *lemma* prod_is_unit

Modified src/data/multiset/basic.lean
- \+ *theorem* prod_to_list

Modified src/field_theory/algebraic_closure.lean
- \+ *lemma* exists_spectrum_of_is_alg_closed_of_finite_dimensional

Modified src/field_theory/splitting_field.lean
- \+ *lemma* eq_prod_roots_of_splits_id
- \+ *lemma* eq_prod_roots_of_monic_of_splits_id

Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* has_eigenvalue_of_has_eigenvector



## [2021-05-02 10:42:35](https://github.com/leanprover-community/mathlib/commit/58e990d)
chore(dynamics/periodic_pts): remove duplicate of nat.dvd_right_iff_eq ([#7435](https://github.com/leanprover-community/mathlib/pull/7435))
#### Estimated changes
Modified src/dynamics/periodic_pts.lean
- \- *lemma* nat_dvd_iff_right



## [2021-05-02 09:28:57](https://github.com/leanprover-community/mathlib/commit/4bd1c83)
feat(topology/category/Profinite): Any continuous bijection of profinite spaces is an isomorphism. ([#7430](https://github.com/leanprover-community/mathlib/pull/7430))
#### Estimated changes
Modified src/topology/category/CompHaus.lean
- \+ *lemma* is_closed_map
- \+ *lemma* is_iso_of_bijective
- \+ *def* iso_of_bijective

Modified src/topology/category/Profinite.lean
- \+/\- *lemma* CompHaus.to_Profinite_obj'
- \+ *lemma* is_closed_map
- \+ *lemma* is_iso_of_bijective
- \+ *def* to_Profinite_adj_to_CompHaus
- \- *def* Profinite.to_Profinite_adj_to_CompHaus



## [2021-05-02 04:27:19](https://github.com/leanprover-community/mathlib/commit/30f3788)
feat(topology/discrete_quotient): Discrete quotients of topological spaces ([#7425](https://github.com/leanprover-community/mathlib/pull/7425))
This PR defines the type of discrete quotients of a topological space and provides a basic API.
In a subsequent PR, this will be used to show that a profinite space is the limit of its finite quotients, which will be needed for the liquid tensor experiment.
#### Estimated changes
Created src/topology/discrete_quotient.lean
- \+ *lemma* refl
- \+ *lemma* symm
- \+ *lemma* trans
- \+ *lemma* proj_surjective
- \+ *lemma* fiber_eq
- \+ *lemma* proj_is_locally_constant
- \+ *lemma* proj_continuous
- \+ *lemma* fiber_closed
- \+ *lemma* fiber_open
- \+ *lemma* fiber_clopen
- \+ *lemma* of_le_continuous
- \+ *lemma* of_le_proj
- \+ *lemma* of_le_proj_apply
- \+ *lemma* eq_of_proj_eq
- \+ *lemma* fiber_le_of_le
- \+ *lemma* exists_of_compat
- \+ *def* of_clopen
- \+ *def* setoid
- \+ *def* proj
- \+ *def* comap
- \+ *def* of_le



## [2021-05-02 04:27:18](https://github.com/leanprover-community/mathlib/commit/6d7e756)
feat(linear_algebra/char_poly): charpoly of `left_mul_matrix`  ([#7397](https://github.com/leanprover-community/mathlib/pull/7397))
This is an important ingredient for showing the field norm resp. trace of `x` is the product resp. sum of `x`'s conjugates.
#### Estimated changes
Modified src/linear_algebra/char_poly/coeff.lean
- \+ *lemma* char_poly_left_mul_matrix



## [2021-05-02 04:27:17](https://github.com/leanprover-community/mathlib/commit/cfc7415)
feat(field_theory/polynomial_galois_group): Galois group is S_p ([#7352](https://github.com/leanprover-community/mathlib/pull/7352))
Proves that a Galois group is isomorphic to S_p, under certain conditions.
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *lemma* eq_conj_iff_im

Modified src/data/complex/module.lean
- \+ *def* conj_alg_equiv

Modified src/data/fintype/basic.lean
- \+/\- *lemma* set.to_finset_empty

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* root_set_finite

Modified src/field_theory/polynomial_galois_group.lean
- \+ *lemma* gal_action_hom_restrict
- \+ *lemma* splits_ℚ_ℂ
- \+ *lemma* gal_action_hom_bijective_of_prime_degree_aux
- \+ *lemma* gal_action_hom_bijective_of_prime_degree

Modified src/group_theory/subgroup.lean
- \+ *lemma* of_left_inverse_apply
- \+ *lemma* of_left_inverse_symm_apply
- \+ *lemma* of_injective_apply
- \+ *def* of_left_inverse



## [2021-05-02 00:17:41](https://github.com/leanprover-community/mathlib/commit/6624bbe)
feat(category_theory/limits): dualizing some results ([#7391](https://github.com/leanprover-community/mathlib/pull/7391))
Requested on [zulip](https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/LocallyConstant.20preserves.20colimits/near/236442281).
#### Estimated changes
Renamed src/category_theory/limits/shapes/constructions/finite_products_of_binary_products.lean to src/category_theory/limits/constructions/finite_products_of_binary_products.lean
- \+ *lemma* has_finite_coproducts_of_has_binary_and_terminal
- \+ *def* extend_cofan
- \+ *def* extend_cofan_is_colimit
- \+ *def* preserves_ulift_fin_of_preserves_binary_and_initial
- \+ *def* preserves_finite_coproducts_of_preserves_binary_and_initial

Modified src/category_theory/limits/constructions/limits_of_products_and_equalizers.lean
- \+ *lemma* has_colimit_of_coequalizer_and_coproduct
- \+ *lemma* colimits_from_coequalizers_and_coproducts
- \+ *lemma* finite_colimits_from_coequalizers_and_finite_coproducts
- \+ *def* build_colimit
- \+ *def* build_is_colimit
- \+ *def* preserves_colimit_of_preserves_coequalizers_and_coproduct
- \+ *def* preserves_finite_colimits_of_preserves_coequalizers_and_finite_coproducts
- \+ *def* preserves_colimits_of_preserves_coequalizers_and_coproducts

Modified src/category_theory/limits/preserves/shapes/binary_products.lean
- \+ *lemma* preserves_limit_pair.iso_hom
- \+ *lemma* preserves_colimit_pair.iso_hom
- \- *lemma* preserves_pair.iso_hom
- \+ *def* preserves_limit_pair.of_iso_prod_comparison
- \+ *def* preserves_limit_pair.iso
- \+ *def* is_colimit_map_cocone_binary_cofan_equiv
- \+ *def* map_is_colimit_of_preserves_of_is_colimit
- \+ *def* is_colimit_of_reflects_of_map_is_colimit
- \+ *def* is_colimit_of_has_binary_coproduct_of_preserves_colimit
- \+ *def* preserves_colimit_pair.of_iso_coprod_comparison
- \+ *def* preserves_colimit_pair.iso
- \- *def* preserves_pair.of_iso_comparison
- \- *def* preserves_pair.iso

Modified src/category_theory/limits/preserves/shapes/products.lean
- \+ *lemma* preserves_coproduct.inv_hom
- \+ *def* is_colimit_map_cocone_cofan_mk_equiv
- \+ *def* is_colimit_cofan_mk_obj_of_is_colimit
- \+ *def* is_colimit_of_is_colimit_cofan_mk_obj
- \+ *def* is_colimit_of_has_coproduct_of_preserves_colimit
- \+ *def* preserves_coproduct.of_iso_comparison
- \+ *def* preserves_coproduct.iso

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* coprod_comparison_inl
- \+ *lemma* coprod_comparison_inr
- \+ *lemma* coprod_comparison_natural
- \+ *lemma* map_inl_inv_coprod_comparison
- \+ *lemma* map_inr_inv_coprod_comparison
- \+ *lemma* coprod_comparison_inv_natural
- \+/\- *def* coprod_is_coprod
- \+ *def* coprod_comparison
- \+ *def* coprod_comparison_nat_trans
- \+ *def* coprod_comparison_nat_iso

Modified src/category_theory/limits/shapes/products.lean
- \+ *def* coproduct_is_coproduct



## [2021-05-02 00:17:39](https://github.com/leanprover-community/mathlib/commit/6e836c4)
feat(group_theory/perm/{cycles, cycle_type}): permutations are conjugate iff they have the same cycle type ([#7335](https://github.com/leanprover-community/mathlib/pull/7335))
Slightly strengthens the induction principle `equiv.perm.cycle_induction_on`
Proves that two permutations are conjugate iff they have the same cycle type: `equiv.perm.is_conj_iff_cycle_type_eq`
#### Estimated changes
Modified src/algebra/group/conj.lean
- \+ *lemma* conj_pow
- \+ *lemma* conj_gpow

Modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* cycle_type_conj
- \+ *lemma* parts_partition
- \+ *lemma* filter_parts_partition_eq_cycle_type
- \+ *lemma* partition_eq_of_is_conj
- \+ *theorem* is_conj_of_cycle_type_eq
- \+ *theorem* is_conj_iff_cycle_type_eq

Modified src/group_theory/perm/cycles.lean
- \+ *lemma* is_cycle.is_cycle_conj
- \+ *lemma* support_conj
- \+ *lemma* card_support_conj
- \+ *theorem* disjoint.is_conj_mul



## [2021-05-02 00:17:38](https://github.com/leanprover-community/mathlib/commit/106ac8e)
feat(category_theory): definition of R-linear category ([#7321](https://github.com/leanprover-community/mathlib/pull/7321))
#### Estimated changes
Modified src/algebra/category/Module/basic.lean


Created src/category_theory/linear/default.lean
- \+ *def* left_comp
- \+ *def* right_comp
- \+ *def* comp



## [2021-05-02 00:17:37](https://github.com/leanprover-community/mathlib/commit/decb556)
feat(geometry/euclidean/basic): lemmas about angles and distances ([#7140](https://github.com/leanprover-community/mathlib/pull/7140))
#### Estimated changes
Modified src/geometry/euclidean/basic.lean
- \+ *lemma* inner_eq_neg_mul_norm_of_angle_eq_pi
- \+ *lemma* inner_eq_mul_norm_of_angle_eq_zero
- \+ *lemma* inner_eq_neg_mul_norm_iff_angle_eq_pi
- \+ *lemma* inner_eq_mul_norm_iff_angle_eq_zero
- \+ *lemma* norm_sub_eq_add_norm_of_angle_eq_pi
- \+ *lemma* norm_add_eq_add_norm_of_angle_eq_zero
- \+ *lemma* norm_sub_eq_abs_sub_norm_of_angle_eq_zero
- \+ *lemma* norm_sub_eq_add_norm_iff_angle_eq_pi
- \+ *lemma* norm_add_eq_add_norm_iff_angle_eq_zero
- \+ *lemma* norm_sub_eq_abs_sub_norm_iff_angle_eq_zero
- \+ *lemma* norm_add_eq_norm_sub_iff_angle_eq_pi_div_two
- \+ *lemma* angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi
- \+ *lemma* left_dist_ne_zero_of_angle_eq_pi
- \+ *lemma* right_dist_ne_zero_of_angle_eq_pi
- \+ *lemma* dist_eq_add_dist_of_angle_eq_pi
- \+ *lemma* dist_eq_add_dist_iff_angle_eq_pi
- \+ *lemma* dist_eq_abs_sub_dist_of_angle_eq_zero
- \+ *lemma* dist_eq_abs_sub_dist_iff_angle_eq_zero
- \+ *lemma* dist_left_midpoint_eq_dist_right_midpoint
- \+ *lemma* angle_midpoint_eq_pi
- \+ *lemma* angle_left_midpoint_eq_pi_div_two_of_dist_eq
- \+ *lemma* angle_right_midpoint_eq_pi_div_two_of_dist_eq



## [2021-05-01 20:07:58](https://github.com/leanprover-community/mathlib/commit/ea379b0)
feat(topology/continuous_function): the Stone-Weierstrass theorem ([#7305](https://github.com/leanprover-community/mathlib/pull/7305))
# The Stone-Weierstrass theorem
If a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact Hausdorff space,
separates points, then it is dense.
We argue as follows.
* In any subalgebra `A` of `C(X, ℝ)`, if `f ∈ A`, then `abs f ∈ A.topological_closure`.
  This follows from the Weierstrass approximation theorem on `[-∥f∥, ∥f∥]` by
  approximating `abs` uniformly thereon by polynomials.
* This ensures that `A.topological_closure` is actually a sublattice:
  if it contains `f` and `g`, then it contains the pointwise supremum `f ⊔ g`
  and the pointwise infimum `f ⊓ g`.
* Any nonempty sublattice `L` of `C(X, ℝ)` which separates points is dense,
  by a nice argument approximating a given `f` above and below using separating functions.
  For each `x y : X`, we pick a function `g x y ∈ L` so `g x y x = f x` and `g x y y = f y`.
  By continuity these functions remain close to `f` on small patches around `x` and `y`.
  We use compactness to identify a certain finitely indexed infimum of finitely indexed supremums
  which is then close to `f` everywhere, obtaining the desired approximation.
* Finally we put these pieces together. `L = A.topological_closure` is a nonempty sublattice
  which separates points since `A` does, and so is dense (in fact equal to `⊤`).
## Future work
Prove the complex version for self-adjoint subalgebras `A`, by separately approximating
the real and imaginary parts using the real subalgebra of real-valued functions in `A`
(which still separates points, by taking the norm-square of a separating function).
Extend to cover the case of subalgebras of the continuous functions vanishing at infinity,
on non-compact Hausdorff spaces.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Modified src/data/finset/lattice.lean
- \+ *lemma* sup'_const
- \+ *lemma* inf'_const

Modified src/order/filter/basic.lean
- \+ *lemma* tendsto.frequently_map

Modified src/topology/algebra/algebra.lean
- \+ *lemma* subalgebra.subalgebra_topological_closure
- \- *lemma* subalgebra.subring_topological_closure

Modified src/topology/algebra/module.lean
- \+ *lemma* submodule.topological_closure_coe

Modified src/topology/algebra/ring.lean
- \+ *lemma* subsemiring.topological_closure_coe

Modified src/topology/continuous_function/basic.lean
- \+ *lemma* continuous_set_coe

Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* algebra_map_apply

Modified src/topology/continuous_function/compact.lean
- \+ *lemma* apply_le_norm
- \+ *lemma* neg_norm_le_apply

Created src/topology/continuous_function/stone_weierstrass.lean
- \+ *lemma* attach_bound_apply_coe
- \+ *lemma* polynomial_comp_attach_bound
- \+ *lemma* polynomial_comp_attach_bound_mem
- \+ *theorem* comp_attach_bound_mem_closure
- \+ *theorem* abs_mem_subalgebra_closure
- \+ *theorem* inf_mem_subalgebra_closure
- \+ *theorem* inf_mem_closed_subalgebra
- \+ *theorem* sup_mem_subalgebra_closure
- \+ *theorem* sup_mem_closed_subalgebra
- \+ *theorem* sublattice_closure_eq_top
- \+ *theorem* subalgebra_topological_closure_eq_top_of_separates_points
- \+ *theorem* continuous_map_mem_subalgebra_closure_of_separates_points
- \+ *theorem* exists_mem_subalgebra_near_continuous_map_of_separates_points
- \+ *theorem* exists_mem_subalgebra_near_continuous_of_separates_points
- \+ *def* attach_bound



## [2021-05-01 18:03:22](https://github.com/leanprover-community/mathlib/commit/d3c565d)
feat(category_theory/monoidal): the monoidal coherence theorem ([#7324](https://github.com/leanprover-community/mathlib/pull/7324))
This PR contains a proof of the monoidal coherence theorem, stated in the following way: if `C` is any type, then the free monoidal category over `C` is a preorder.
This should immediately imply the statement needed in the `coherence` branch.
#### Estimated changes
Modified docs/references.bib


Modified src/category_theory/monoidal/category.lean
- \+/\- *lemma* triangle_assoc_comp_right
- \+/\- *lemma* triangle_assoc_comp_right_inv
- \+/\- *lemma* triangle_assoc_comp_left_inv

Created src/category_theory/monoidal/free/basic.lean
- \+ *lemma* mk_comp
- \+ *lemma* mk_tensor
- \+ *lemma* mk_id
- \+ *lemma* mk_α_hom
- \+ *lemma* mk_α_inv
- \+ *lemma* mk_ρ_hom
- \+ *lemma* mk_ρ_inv
- \+ *lemma* mk_l_hom
- \+ *lemma* mk_l_inv
- \+ *lemma* tensor_eq_tensor
- \+ *lemma* unit_eq_unit
- \+ *def* setoid_hom
- \+ *def* project_obj
- \+ *def* project_map_aux
- \+ *def* project_map
- \+ *def* project

Created src/category_theory/monoidal/free/coherence.lean
- \+ *lemma* normalize_obj_unitor
- \+ *lemma* normalize_obj_tensor
- \+ *lemma* tensor_func_map_app
- \+ *lemma* tensor_func_obj_map
- \+ *lemma* normalize_iso_app_tensor
- \+ *lemma* normalize_iso_app_unitor
- \+ *def* inclusion_obj
- \+ *def* inclusion
- \+ *def* normalize_obj
- \+ *def* normalize_map_aux
- \+ *def* normalize
- \+ *def* normalize'
- \+ *def* full_normalize
- \+ *def* tensor_func
- \+ *def* normalize_iso_app
- \+ *def* normalize_iso_aux
- \+ *def* normalize_iso
- \+ *def* full_normalize_iso
- \+ *def* inverse_aux



## [2021-05-01 15:16:03](https://github.com/leanprover-community/mathlib/commit/790ec6b)
feat(algebra/archimedean): rat.cast_round for non-archimedean fields ([#7424](https://github.com/leanprover-community/mathlib/pull/7424))
The theorem still applies to the non-canonical archimedean instance (at least if you use simp).  I've also added `rat.cast_ceil` because it seems to fit here.
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+/\- *lemma* abs_sub_round
- \+/\- *theorem* rat.cast_floor
- \+ *theorem* rat.cast_ceil
- \+/\- *theorem* rat.cast_round
- \+/\- *def* round

Modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean
- \+/\- *theorem* terminates_iff_rat



## [2021-05-01 15:16:02](https://github.com/leanprover-community/mathlib/commit/92b9048)
chore(topology/continuous_function/algebra): put `coe_fn_monoid_hom `into the `continuous_map` namespace ([#7423](https://github.com/leanprover-community/mathlib/pull/7423))
Rather than adding `continuous_map.` to the definition, this wraps everything in a namespace to make this type of mistake unlikely to happen again.
This also adds `comp_monoid_hom'` to golf a proof.
#### Estimated changes
Modified src/topology/continuous_function/algebra.lean
- \+ *lemma* one_comp
- \+ *lemma* pow_coe
- \+ *lemma* pow_comp
- \+ *lemma* coe_prod
- \+ *lemma* prod_apply
- \+ *lemma* inv_coe
- \+ *lemma* div_coe
- \+ *lemma* inv_comp
- \+ *lemma* div_comp
- \+ *lemma* smul_coe
- \+ *lemma* smul_apply
- \+ *lemma* smul_comp
- \- *lemma* continuous_map.pow_coe
- \- *lemma* continuous_map.pow_comp
- \- *lemma* continuous_map.coe_prod
- \- *lemma* continuous_map.prod_apply
- \- *lemma* continuous_map.inv_coe
- \- *lemma* continuous_map.div_coe
- \- *lemma* continuous_map.inv_comp
- \- *lemma* continuous_map.div_comp
- \- *lemma* continuous_map.smul_coe
- \- *lemma* continuous_map.smul_apply
- \- *lemma* continuous_map.smul_comp
- \+ *def* comp_monoid_hom'



## [2021-05-01 09:09:54](https://github.com/leanprover-community/mathlib/commit/5511275)
chore(measure_theory/ae_eq_fun_metric): remove useless file ([#7419](https://github.com/leanprover-community/mathlib/pull/7419))
The file `measure_theory/ae_eq_fun_metric.lean` used to contain an edistance on the space of equivalence classes of functions. It has been replaced by the use of the `L^1` space in [#5510](https://github.com/leanprover-community/mathlib/pull/5510), so this file is now useless and should be removed.
#### Estimated changes
Deleted src/measure_theory/ae_eq_fun_metric.lean
- \- *lemma* coe_fn_edist
- \- *lemma* edist_mk_mk
- \- *lemma* edist_eq_coe
- \- *lemma* edist_zero_eq_coe
- \- *lemma* edist_mk_mk'
- \- *lemma* edist_eq_coe'
- \- *lemma* edist_add_right
- \- *lemma* edist_smul



## [2021-05-01 09:09:53](https://github.com/leanprover-community/mathlib/commit/d04af20)
feat(linear_algebra/quadratic_form): add lemmas about sums of quadratic forms ([#7417](https://github.com/leanprover-community/mathlib/pull/7417))
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* coe_fn_zero
- \+ *lemma* coe_fn_sum
- \+ *lemma* sum_apply
- \+ *def* coe_fn_add_monoid_hom
- \+ *def* eval_add_monoid_hom



## [2021-05-01 09:09:52](https://github.com/leanprover-community/mathlib/commit/bf0f15a)
chore(algebra/algebra/basic): add missing lemmas ([#7412](https://github.com/leanprover-community/mathlib/pull/7412))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* coe_id
- \+ *lemma* id_to_ring_hom
- \+/\- *lemma* id_apply
- \+ *lemma* coe_comp
- \+/\- *lemma* comp_apply
- \+ *lemma* comp_to_ring_hom
- \+ *lemma* refl_to_alg_hom
- \+/\- *lemma* coe_refl
- \+ *lemma* coe_trans
- \+/\- *lemma* trans_apply
- \+ *theorem* left_inverse_symm
- \+ *theorem* right_inverse_symm



## [2021-05-01 06:41:10](https://github.com/leanprover-community/mathlib/commit/e3de4e3)
fix(algebra/direct_sum_graded): replace badly-stated and slow `simps` lemmas with manual ones  ([#7403](https://github.com/leanprover-community/mathlib/pull/7403))
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/simps.20is.20very.20slow/near/236636962). The `simps mul` attribute on `direct_sum.ghas_mul.of_add_subgroups` was taking 44s, only to produce a lemma that wasn't very useful anyway.
#### Estimated changes
Modified src/algebra/direct_sum_graded.lean
- \+ *lemma* ghas_mul.of_add_submonoids_mul
- \+ *lemma* ghas_mul.of_add_subgroups_mul
- \+ *lemma* ghas_mul.of_submodules_mul



## [2021-05-01 06:41:09](https://github.com/leanprover-community/mathlib/commit/aa37eee)
feat(analysis/special_functions/integrals): integral of `cos x ^ n` ([#7402](https://github.com/leanprover-community/mathlib/pull/7402))
The reduction of `∫ x in a..b, cos x ^ n`, ∀ n ∈ ℕ, 2 ≤ n, as well as the integral of `cos x ^ 2` as a special case.
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* integral_cos_pow_aux
- \+ *lemma* integral_cos_pow
- \+ *lemma* integral_cos_sq

Modified test/integration.lean




## [2021-05-01 06:41:08](https://github.com/leanprover-community/mathlib/commit/2cc8128)
feat(algebra/polynomial): generalize to `multiset` products ([#7399](https://github.com/leanprover-community/mathlib/pull/7399))
This PR generalizes the results in `algebra.polynomial.big_operators` to sums and products of multisets.
The new multiset results are stated for `multiset.prod t`, not `(multiset.map t f).prod`. To get the latter, you can simply rewrite with `multiset.map_map`.
#### Estimated changes
Modified src/algebra/polynomial/big_operators.lean
- \+ *lemma* nat_degree_multiset_prod_le
- \+ *lemma* leading_coeff_multiset_prod'
- \+ *lemma* nat_degree_multiset_prod'
- \+ *lemma* nat_degree_multiset_prod_of_monic
- \+ *lemma* coeff_zero_multiset_prod
- \+ *lemma* multiset_prod_X_sub_C_next_coeff
- \+ *lemma* multiset_prod_X_sub_C_coeff_card_pred
- \+/\- *lemma* prod_X_sub_C_coeff_card_pred
- \+ *lemma* degree_multiset_prod
- \+/\- *lemma* degree_prod
- \+ *lemma* leading_coeff_multiset_prod

Modified src/data/polynomial/monic.lean
- \+ *lemma* monic_multiset_prod_of_monic
- \+ *lemma* monic.next_coeff_multiset_prod
- \+/\- *lemma* monic.next_coeff_prod



## [2021-05-01 00:19:22](https://github.com/leanprover-community/mathlib/commit/d5d22c5)
feat(algebra/squarefree): add sq_mul_squarefree lemmas ([#7282](https://github.com/leanprover-community/mathlib/pull/7282))
Every positive natural number can be expressed as m^2 * n where n is square free. Used in [#7274](https://github.com/leanprover-community/mathlib/pull/7274)
#### Estimated changes
Modified src/algebra/squarefree.lean
- \+ *lemma* sq_mul_squarefree_of_pos
- \+ *lemma* sq_mul_squarefree_of_pos'
- \+ *lemma* sq_mul_squarefree



## [2021-05-01 00:19:21](https://github.com/leanprover-community/mathlib/commit/b51cee2)
feat(data/polynomial/coeff): Add smul_eq_C_mul ([#7240](https://github.com/leanprover-community/mathlib/pull/7240))
Adding a lemma `polynomial.smul_eq_C_mul` for single variate polynomials analogous to `mv_polynomial.smul_eq_C_mul` for multivariate.
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *lemma* monomial_zero_left
- \+ *lemma* C_0
- \+ *lemma* C_1
- \+ *lemma* C_mul
- \+ *lemma* C_add
- \+ *lemma* C_bit0
- \+ *lemma* C_bit1
- \+ *lemma* C_pow
- \+ *lemma* C_eq_nat_cast
- \+ *lemma* sum_C_index
- \+ *lemma* coeff_C
- \+ *lemma* coeff_C_zero
- \+ *lemma* coeff_C_ne_zero
- \+ *lemma* single_eq_C_mul_X
- \+ *lemma* C_inj
- \+ *lemma* C_eq_zero
- \+ *lemma* monomial_eq_smul_X
- \+ *theorem* nontrivial.of_polynomial_ne
- \+ *def* C

Modified src/data/polynomial/coeff.lean


Modified src/data/polynomial/degree/definitions.lean


Modified src/data/polynomial/monomial.lean
- \+ *lemma* smul_eq_C_mul
- \- *lemma* monomial_zero_left
- \- *lemma* C_0
- \- *lemma* C_1
- \- *lemma* C_mul
- \- *lemma* C_add
- \- *lemma* C_bit0
- \- *lemma* C_bit1
- \- *lemma* C_pow
- \- *lemma* C_eq_nat_cast
- \- *lemma* sum_C_index
- \- *lemma* coeff_C
- \- *lemma* coeff_C_zero
- \- *lemma* coeff_C_ne_zero
- \- *lemma* single_eq_C_mul_X
- \- *lemma* C_inj
- \- *lemma* C_eq_zero
- \- *lemma* monomial_eq_smul_X
- \- *theorem* nontrivial.of_polynomial_ne
- \- *def* C



## [2021-05-01 00:19:20](https://github.com/leanprover-community/mathlib/commit/b88a9d1)
feat(category_theory/enriched): abstract enriched categories ([#7175](https://github.com/leanprover-community/mathlib/pull/7175))
# Enriched categories
We set up the basic theory of `V`-enriched categories,
for `V` an arbitrary monoidal category.
We do not assume here that `V` is a concrete category,
so there does not need to be a "honest" underlying category!
Use `X ⟶[V] Y` to obtain the `V` object of morphisms from `X` to `Y`.
This file contains the definitions of `V`-enriched categories and
`V`-functors.
We don't yet define the `V`-object of natural transformations
between a pair of `V`-functors (this requires limits in `V`),
but we do provide a presheaf isomorphic to the Yoneda embedding of this object.
We verify that when `V = Type v`, all these notion reduce to the usual ones.
#### Estimated changes
Modified src/algebra/category/Module/adjunctions.lean


Created src/category_theory/enriched/basic.lean
- \+ *lemma* e_id_comp
- \+ *lemma* e_comp_id
- \+ *lemma* e_assoc
- \+ *lemma* forget_enrichment.to_of
- \+ *lemma* forget_enrichment.of_to
- \+ *lemma* forget_enrichment.hom_to_hom_of
- \+ *lemma* forget_enrichment.hom_of_hom_to
- \+ *lemma* forget_enrichment_id
- \+ *lemma* forget_enrichment_id'
- \+ *lemma* forget_enrichment_comp
- \+ *def* e_id
- \+ *def* e_comp
- \+ *def* transport_enrichment
- \+ *def* category_of_enriched_category_Type
- \+ *def* enriched_category_Type_of_category
- \+ *def* enriched_category_Type_equiv_category
- \+ *def* forget_enrichment
- \+ *def* forget_enrichment.of
- \+ *def* forget_enrichment.to
- \+ *def* forget_enrichment.hom_of
- \+ *def* forget_enrichment.hom_to
- \+ *def* enriched_functor.id
- \+ *def* enriched_functor.comp
- \+ *def* enriched_functor.forget
- \+ *def* enriched_nat_trans_yoneda
- \+ *def* enriched_functor_Type_equiv_functor
- \+ *def* enriched_nat_trans_yoneda_Type_iso_yoneda_nat_trans

Modified src/category_theory/monoidal/braided.lean


Modified src/category_theory/monoidal/category.lean
- \+ *lemma* unitors_inv_equal

Modified src/category_theory/monoidal/center.lean
- \+ *lemma* ext
- \+ *lemma* tensor_unit_β
- \+ *def* of_braided_obj
- \+ *def* of_braided

Modified src/category_theory/monoidal/functor.lean
- \+ *lemma* lax_monoidal_functor.left_unitality_inv
- \+ *lemma* lax_monoidal_functor.right_unitality_inv
- \+ *lemma* lax_monoidal_functor.associativity_inv

Modified src/category_theory/monoidal/internal/types.lean


Modified src/category_theory/monoidal/types.lean
- \+ *def* coyoneda_tensor_unit



## [2021-05-01 00:19:19](https://github.com/leanprover-community/mathlib/commit/802c5b5)
feat(linear_algebra/determinant): various operations preserve the determinant ([#7115](https://github.com/leanprover-community/mathlib/pull/7115))
These are a couple of helper lemmas for computing the determinant of a Vandermonde matrix.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* update_row_eq_self
- \+ *lemma* update_column_eq_self

Modified src/linear_algebra/determinant.lean
- \+ *lemma* det_mul_row
- \+ *lemma* det_mul_column
- \+ *lemma* det_eq_of_eq_mul_det_one
- \+ *lemma* det_eq_of_eq_det_one_mul
- \+ *lemma* det_update_row_add_self
- \+ *lemma* det_update_column_add_self
- \+ *lemma* det_update_row_add_smul_self
- \+ *lemma* det_update_column_add_smul_self
- \+ *lemma* det_eq_of_forall_row_eq_smul_add_const_aux
- \+ *lemma* det_eq_of_forall_row_eq_smul_add_const
- \+ *lemma* det_eq_of_forall_row_eq_smul_add_pred_aux
- \+ *lemma* det_eq_of_forall_row_eq_smul_add_pred
- \+ *lemma* det_eq_of_forall_col_eq_smul_add_pred
- \+ *theorem* det_zero_of_column_eq



## [2021-05-01 00:19:18](https://github.com/leanprover-community/mathlib/commit/6c61779)
refactor(group_theory/order_of_element): use minimal_period for the definition ([#7082](https://github.com/leanprover-community/mathlib/pull/7082))
This PR redefines `order_of_element` in terms of `function.minimal_period`. It furthermore introduces a predicate on elements of a finite group to be of finite order.
Co-authored by: Damiano Testa adomani@gmail.com
#### Estimated changes
Modified src/algebra/char_p/basic.lean


Modified src/algebra/group/basic.lean
- \+ *lemma* one_mul_eq_id
- \+ *lemma* mul_one_eq_id

Modified src/algebra/iterate_hom.lean
- \+/\- *lemma* mul_left_iterate
- \+/\- *lemma* mul_right_iterate
- \+ *lemma* mul_right_iterate_apply_one
- \+ *lemma* semiconj_by.function_semiconj_mul_left
- \+ *lemma* commute.function_commute_mul_left
- \+ *lemma* semiconj_by.function_semiconj_mul_right_swap
- \+ *lemma* commute.function_commute_mul_right
- \+/\- *lemma* add_left_iterate
- \+/\- *lemma* add_right_iterate
- \+ *lemma* add_right_iterate_apply_zero

Modified src/algebra/regular.lean


Modified src/dynamics/periodic_pts.lean
- \+ *lemma* iterate_eq_mod_minimal_period
- \+ *lemma* minimal_period_id
- \+ *lemma* is_fixed_point_iff_minimal_period_eq_one
- \+ *lemma* not_is_periodic_pt_of_pos_of_lt_minimal_period
- \+ *lemma* nat_dvd_iff_right
- \+ *lemma* minimal_period_eq_minimal_period_iff
- \+ *lemma* minimal_period_eq_prime
- \+ *lemma* minimal_period_eq_prime_pow
- \+ *lemma* commute.minimal_period_of_comp_dvd_lcm
- \+ *lemma* minimal_period_iterate_eq_div_gcd
- \+ *lemma* minimal_period_iterate_eq_div_gcd'

Modified src/group_theory/order_of_element.lean
- \+ *lemma* is_periodic_pt_add_iff_nsmul_eq_zero
- \+ *lemma* is_periodic_pt_mul_iff_pow_eq_one
- \+ *lemma* is_of_fin_add_order_of_mul_iff
- \+ *lemma* is_of_fin_order_of_add_iff
- \+ *lemma* is_of_fin_add_order_iff_nsmul_eq_zero
- \+ *lemma* is_of_fin_order_iff_pow_eq_one
- \+/\- *lemma* commute.order_of_mul_dvd_lcm
- \+/\- *lemma* add_order_of_of_mul_eq_order_of
- \+/\- *lemma* order_of_of_add_eq_add_order_of
- \+/\- *lemma* order_of_pos'
- \+/\- *lemma* pow_order_of_eq_one
- \+/\- *lemma* add_order_of_nsmul_eq_zero
- \+/\- *lemma* order_of_eq_zero
- \+ *lemma* nsmul_ne_zero_of_lt_add_order_of'
- \+ *lemma* pow_eq_one_of_lt_order_of'
- \+/\- *lemma* add_order_of_le_of_nsmul_eq_zero
- \+/\- *lemma* order_of_le_of_pow_eq_one
- \+/\- *lemma* order_of_one
- \+/\- *lemma* add_order_of_zero
- \+/\- *lemma* order_of_eq_one_iff
- \+/\- *lemma* add_order_of_eq_one_iff
- \+/\- *lemma* pow_eq_mod_order_of
- \+/\- *lemma* nsmul_eq_mod_add_order_of
- \+/\- *lemma* order_of_dvd_of_pow_eq_one
- \+/\- *lemma* add_order_of_dvd_of_nsmul_eq_zero
- \+/\- *lemma* add_order_of_dvd_iff_nsmul_eq_zero
- \+/\- *lemma* order_of_dvd_iff_pow_eq_one
- \+/\- *lemma* exists_pow_eq_self_of_coprime
- \+/\- *lemma* exists_nsmul_eq_self_of_coprime
- \+/\- *lemma* add_order_of_eq_add_order_of_iff
- \+/\- *lemma* order_of_eq_order_of_iff
- \+/\- *lemma* add_order_of_injective
- \+/\- *lemma* order_of_injective
- \+/\- *lemma* order_of_submonoid
- \+/\- *lemma* order_of_pow''
- \+/\- *lemma* add_order_of_nsmul''
- \+/\- *lemma* add_order_of_eq_prime
- \+/\- *lemma* order_of_eq_prime
- \+/\- *lemma* add_order_of_eq_prime_pow
- \+/\- *lemma* order_of_eq_prime_pow
- \+/\- *lemma* pow_injective_aux
- \+/\- *lemma* pow_injective_of_lt_order_of
- \+/\- *lemma* order_of_subgroup
- \+/\- *lemma* gpow_eq_mod_order_of
- \+/\- *lemma* gsmul_eq_mod_add_order_of
- \+/\- *lemma* sum_card_add_order_of_eq_card_nsmul_eq_zero
- \+/\- *lemma* sum_card_order_of_eq_card_pow_eq_one
- \+/\- *lemma* exists_pow_eq_one
- \+/\- *lemma* exists_nsmul_eq_zero
- \+/\- *lemma* add_order_of_le_card_univ
- \+/\- *lemma* order_of_le_card_univ
- \+/\- *lemma* add_order_of_pos
- \+/\- *lemma* order_of_pos
- \+/\- *lemma* add_order_of_nsmul
- \+/\- *lemma* order_of_pow
- \+/\- *lemma* mem_multiples_iff_mem_range_add_order_of
- \+/\- *lemma* mem_powers_iff_mem_range_order_of
- \+/\- *lemma* fin_equiv_powers_apply
- \+/\- *lemma* fin_equiv_multiples_apply
- \+/\- *lemma* fin_equiv_powers_symm_apply
- \+/\- *lemma* fin_equiv_multiples_symm_apply
- \+/\- *lemma* powers_equiv_powers_apply
- \+/\- *lemma* multiples_equiv_multiples_apply
- \+/\- *lemma* order_eq_card_powers
- \+/\- *lemma* add_order_of_eq_card_multiples
- \+/\- *lemma* exists_gpow_eq_one
- \+/\- *lemma* exists_gsmul_eq_zero
- \+/\- *lemma* mem_multiples_iff_mem_gmultiples
- \+/\- *lemma* mem_powers_iff_mem_gpowers
- \+/\- *lemma* multiples_eq_gmultiples
- \+/\- *lemma* powers_eq_gpowers
- \+/\- *lemma* mem_gmultiples_iff_mem_range_add_order_of
- \+/\- *lemma* mem_gpowers_iff_mem_range_order_of
- \+/\- *lemma* fin_equiv_gpowers_apply
- \+/\- *lemma* fin_equiv_gmultiples_apply
- \+/\- *lemma* fin_equiv_gpowers_symm_apply
- \+/\- *lemma* fin_equiv_gmultiples_symm_apply
- \+/\- *lemma* gpowers_equiv_gpowers_apply
- \+/\- *lemma* gmultiples_equiv_gmultiples_apply
- \+/\- *lemma* order_eq_card_gpowers
- \+/\- *lemma* add_order_eq_card_gmultiples
- \+/\- *lemma* order_of_dvd_card_univ
- \+/\- *lemma* add_order_of_dvd_card_univ
- \+/\- *lemma* pow_card_eq_one
- \+/\- *lemma* card_nsmul_eq_zero
- \+/\- *lemma* image_range_add_order_of
- \+/\- *lemma* image_range_order_of
- \+/\- *lemma* gcd_nsmul_card_eq_zero_iff
- \+/\- *lemma* pow_gcd_card_eq_one_iff
- \- *lemma* add_order_of_pos'
- \- *lemma* add_order_of_eq_zero
- \- *lemma* add_order_of_le_of_nsmul_eq_zero'
- \- *lemma* order_of_le_of_pow_eq_one'
- \+ *def* is_of_fin_add_order
- \+ *def* is_of_fin_order

Modified src/group_theory/specific_groups/dihedral.lean


Modified src/group_theory/specific_groups/quaternion.lean


Modified src/group_theory/sylow.lean


Modified src/topology/algebra/ordered.lean


