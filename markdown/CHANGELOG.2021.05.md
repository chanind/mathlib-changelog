## [2021-05-31 21:08:06](https://github.com/leanprover-community/mathlib/commit/bec3e59)
feat(data/finset): provide the coercion `finset α → Type*` ([#7575](https://github.com/leanprover-community/mathlib/pull/7575))
There doesn't seem to be a good reason that `finset` doesn't have a `coe_to_sort` like `set` does. Before the change in this PR, we had to suffer the inconvenience of writing `(↑s : set _)` whenever we want the subtype of all elements of `s`. Now you can just write `s`.
I removed the obvious instances of the `((↑s : set _) : Type*)` pattern, although it definitely remains in some places. I'd rather do those in separate PRs since it does not really do any harm except for being annoying to type. There are also some parts of the API (`polynomial.root_set` stands out to me) that could be designed around the use of `finset`s rather than `set`s that are later proved to be finite, which I again would like to declare out of scope.
#### Estimated changes
Modified archive/100-theorems-list/16_abel_ruffini.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/combinatorics/hall.lean


Modified src/data/finset/basic.lean
- \+ *lemma* finset.apply_coe_mem_map
- \+ *lemma* finset.coe_sort_coe

Modified src/data/finset/sort.lean
- \+/\- *def* finset.order_iso_of_fin
- \+/\- *lemma* finset.order_iso_of_fin_symm_apply

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.univ_eq_attach

Modified src/data/set/finite.lean
- \+ *lemma* set.finite.coe_sort_to_finset

Modified src/field_theory/finiteness.lean
- \+ *lemma* is_noetherian.coe_sort_finset_basis_index

Modified src/field_theory/polynomial_galois_group.lean


Modified src/field_theory/separable.lean


Modified src/geometry/euclidean/monge_point.lean


Modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* vector_span_eq_span_vsub_finset_right_ne

Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* finite_dimensional.of_finset_basis
- \+ *lemma* finrank_span_finset_eq_card
- \+ *lemma* finrank_span_finset_le_card

Modified src/linear_algebra/lagrange.lean
- \+/\- *def* lagrange.fun_equiv_degree_lt
- \+/\- *def* lagrange.linterpolate

Modified src/set_theory/cardinal.lean
- \+/\- *lemma* cardinal.finset_card

Modified src/topology/separation.lean




## [2021-05-31 21:08:05](https://github.com/leanprover-community/mathlib/commit/ca740b6)
feat(data/finset/powerset): ssubsets and decidability ([#7543](https://github.com/leanprover-community/mathlib/pull/7543))
A few more little additions to finset-world that I found useful.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.ssubset_iff_subset_ne

Modified src/data/finset/powerset.lean
- \+ *def* finset.decidable_exists_of_decidable_ssubsets'
- \+ *def* finset.decidable_exists_of_decidable_subsets'
- \+ *def* finset.decidable_forall_of_decidable_ssubsets'
- \+ *def* finset.decidable_forall_of_decidable_subsets'
- \+ *lemma* finset.empty_mem_ssubsets
- \+ *lemma* finset.mem_ssubsets
- \+ *def* finset.ssubsets



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
- \+ *lemma* directed_of_chain
- \- *theorem* directed_of_chain
- \+ *lemma* zorn.chain.directed_on
- \- *theorem* zorn.chain.directed_on
- \+ *lemma* zorn.chain.image
- \- *theorem* zorn.chain.image
- \+ *lemma* zorn.chain.mono
- \- *theorem* zorn.chain.mono
- \+ *lemma* zorn.chain.symm
- \- *theorem* zorn.chain.symm
- \+ *lemma* zorn.chain.total
- \- *theorem* zorn.chain.total
- \+ *lemma* zorn.chain.total_of_refl
- \- *theorem* zorn.chain.total_of_refl
- \+ *lemma* zorn.chain_chain_closure
- \- *theorem* zorn.chain_chain_closure
- \+ *lemma* zorn.chain_closure_closure
- \- *theorem* zorn.chain_closure_closure
- \+ *lemma* zorn.chain_closure_empty
- \- *theorem* zorn.chain_closure_empty
- \+ *lemma* zorn.chain_closure_succ_fixpoint
- \- *theorem* zorn.chain_closure_succ_fixpoint
- \+ *lemma* zorn.chain_closure_succ_fixpoint_iff
- \- *theorem* zorn.chain_closure_succ_fixpoint_iff
- \+ *lemma* zorn.chain_closure_total
- \- *theorem* zorn.chain_closure_total
- \+ *lemma* zorn.chain_insert
- \- *theorem* zorn.chain_insert
- \+ *lemma* zorn.chain_succ
- \- *theorem* zorn.chain_succ
- \+ *lemma* zorn.succ_increasing
- \- *theorem* zorn.succ_increasing
- \+ *lemma* zorn.succ_spec
- \- *theorem* zorn.succ_spec
- \+ *lemma* zorn.super_of_not_max
- \- *theorem* zorn.super_of_not_max



## [2021-05-31 15:49:23](https://github.com/leanprover-community/mathlib/commit/d0ebc8e)
feat(ring_theory/laurent_series): Defines Laurent series and their localization map ([#7604](https://github.com/leanprover-community/mathlib/pull/7604))
Defines `laurent_series` as an abbreviation of `hahn_series Z`
Defines `laurent_series.power_series_part`
Shows that the map from power series to Laurent series is a `localization_map`.
#### Estimated changes
Modified src/ring_theory/hahn_series.lean
- \+/\- *def* hahn_series.of_power_series
- \+ *lemma* hahn_series.of_power_series_apply
- \+ *lemma* hahn_series.of_power_series_apply_coeff
- \+ *lemma* hahn_series.of_power_series_injective

Added src/ring_theory/laurent_series.lean
- \+ *lemma* laurent_series.coe_power_series
- \+ *lemma* laurent_series.coeff_coe_power_series
- \+ *lemma* laurent_series.of_power_series_X
- \+ *lemma* laurent_series.of_power_series_X_pow
- \+ *def* laurent_series.of_power_series_localization
- \+ *lemma* laurent_series.of_power_series_power_series_part
- \+ *def* laurent_series.power_series_part
- \+ *lemma* laurent_series.power_series_part_coeff
- \+ *lemma* laurent_series.power_series_part_eq_zero
- \+ *lemma* laurent_series.power_series_part_zero
- \+ *lemma* laurent_series.single_order_mul_power_series_part



## [2021-05-31 14:35:07](https://github.com/leanprover-community/mathlib/commit/4555798)
feat(topology/semicontinuous): semicontinuity of compositions ([#7763](https://github.com/leanprover-community/mathlib/pull/7763))
#### Estimated changes
Modified src/topology/semicontinuous.lean
- \+ *lemma* continuous.comp_lower_semicontinuous
- \+ *lemma* continuous.comp_lower_semicontinuous_antimono
- \+ *lemma* continuous.comp_lower_semicontinuous_on
- \+ *lemma* continuous.comp_lower_semicontinuous_on_antimono
- \+ *lemma* continuous.comp_upper_semicontinuous
- \+ *lemma* continuous.comp_upper_semicontinuous_antimono
- \+ *lemma* continuous.comp_upper_semicontinuous_on
- \+ *lemma* continuous.comp_upper_semicontinuous_on_antimono
- \+ *lemma* continuous_at.comp_lower_semicontinuous_at
- \+ *lemma* continuous_at.comp_lower_semicontinuous_at_antimono
- \+ *lemma* continuous_at.comp_lower_semicontinuous_within_at
- \+ *lemma* continuous_at.comp_lower_semicontinuous_within_at_antimono
- \+ *lemma* continuous_at.comp_upper_semicontinuous_at
- \+ *lemma* continuous_at.comp_upper_semicontinuous_at_antimono
- \+ *lemma* continuous_at.comp_upper_semicontinuous_within_at
- \+ *lemma* continuous_at.comp_upper_semicontinuous_within_at_antimono



## [2021-05-31 13:18:14](https://github.com/leanprover-community/mathlib/commit/2af6912)
feat(linear_algebra): the determinant of an endomorphism ([#7635](https://github.com/leanprover-community/mathlib/pull/7635))
 `linear_map.det` is the determinant of an endomorphism, which is defined independent of a basis. If there is no finite basis, the determinant is defined to be equal to `1`.
This approach is inspired by `linear_map.trace`.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/linear_algebra/determinant.lean
- \+ *lemma* linear_map.coe_det
- \+ *def* linear_map.det_aux
- \+ *lemma* linear_map.det_aux_comp
- \+ *lemma* linear_map.det_aux_def'
- \+ *lemma* linear_map.det_aux_def
- \+ *lemma* linear_map.det_aux_id
- \+ *lemma* linear_map.det_comp
- \+ *lemma* linear_map.det_eq_det_to_matrix_of_finite_set
- \+ *lemma* linear_map.det_id
- \+ *lemma* linear_map.det_to_matrix
- \+ *lemma* linear_map.det_to_matrix_eq_det_to_matrix
- \+ *lemma* linear_map.det_zero



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
Added src/category_theory/preadditive/projective_resolution.lean
- \+ *def* category_theory.ProjectiveResolution.homotopy_equiv
- \+ *lemma* category_theory.ProjectiveResolution.homotopy_equiv_hom_π
- \+ *lemma* category_theory.ProjectiveResolution.homotopy_equiv_inv_π
- \+ *def* category_theory.ProjectiveResolution.lift
- \+ *lemma* category_theory.ProjectiveResolution.lift_commutes
- \+ *def* category_theory.ProjectiveResolution.lift_comp_homotopy
- \+ *def* category_theory.ProjectiveResolution.lift_f_one
- \+ *lemma* category_theory.ProjectiveResolution.lift_f_one_zero_comm
- \+ *def* category_theory.ProjectiveResolution.lift_f_succ
- \+ *def* category_theory.ProjectiveResolution.lift_f_zero
- \+ *def* category_theory.ProjectiveResolution.lift_homotopy
- \+ *def* category_theory.ProjectiveResolution.lift_homotopy_zero
- \+ *def* category_theory.ProjectiveResolution.lift_homotopy_zero_one
- \+ *def* category_theory.ProjectiveResolution.lift_homotopy_zero_succ
- \+ *def* category_theory.ProjectiveResolution.lift_homotopy_zero_zero
- \+ *def* category_theory.ProjectiveResolution.lift_id_homotopy
- \+ *def* category_theory.ProjectiveResolution.self
- \+ *lemma* category_theory.ProjectiveResolution.π_f_succ
- \+ *def* category_theory.projective_resolutions



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
- \+/\- *lemma* path.extend_one
- \+/\- *lemma* path.extend_zero

Modified src/topology/unit_interval.lean
- \+ *lemma* unit_interval.mk_one
- \+ *lemma* unit_interval.mk_zero

Modified test/nontriviality.lean




## [2021-05-30 21:09:58](https://github.com/leanprover-community/mathlib/commit/fd48ac5)
chore(data/list): extract sublists to a separate file ([#7757](https://github.com/leanprover-community/mathlib/pull/7757))
Minor splitting in `data/list/basic`, splitting out `sublists` to its own file, thereby delaying importing `data.nat.choose` in the `list` development.
#### Estimated changes
Modified src/data/list/basic.lean
- \- *lemma* list.length_of_sublists_len
- \- *theorem* list.length_sublists'
- \- *theorem* list.length_sublists
- \- *lemma* list.length_sublists_len
- \- *theorem* list.map_ret_sublist_sublists
- \- *theorem* list.map_sublists'_aux
- \- *theorem* list.mem_sublists'
- \- *theorem* list.mem_sublists
- \- *lemma* list.mem_sublists_len
- \- *lemma* list.mem_sublists_len_self
- \- *theorem* list.sublists'_aux_append
- \- *theorem* list.sublists'_aux_eq_sublists'
- \- *theorem* list.sublists'_cons
- \- *theorem* list.sublists'_eq_sublists
- \- *theorem* list.sublists'_nil
- \- *theorem* list.sublists'_reverse
- \- *theorem* list.sublists'_singleton
- \- *theorem* list.sublists_append
- \- *theorem* list.sublists_aux_cons_append
- \- *theorem* list.sublists_aux_cons_cons
- \- *theorem* list.sublists_aux_cons_eq_sublists_aux₁
- \- *theorem* list.sublists_aux_eq_foldr.aux
- \- *theorem* list.sublists_aux_eq_foldr
- \- *theorem* list.sublists_aux_ne_nil
- \- *theorem* list.sublists_aux₁_append
- \- *theorem* list.sublists_aux₁_bind
- \- *theorem* list.sublists_aux₁_concat
- \- *theorem* list.sublists_aux₁_eq_sublists_aux
- \- *theorem* list.sublists_concat
- \- *theorem* list.sublists_eq_sublists'
- \- *def* list.sublists_len
- \- *def* list.sublists_len_aux
- \- *lemma* list.sublists_len_aux_append
- \- *lemma* list.sublists_len_aux_eq
- \- *lemma* list.sublists_len_aux_zero
- \- *lemma* list.sublists_len_sublist_of_sublist
- \- *lemma* list.sublists_len_sublist_sublists'
- \- *lemma* list.sublists_len_succ_cons
- \- *lemma* list.sublists_len_succ_nil
- \- *lemma* list.sublists_len_zero
- \- *theorem* list.sublists_nil
- \- *theorem* list.sublists_reverse
- \- *theorem* list.sublists_singleton

Modified src/data/list/pairwise.lean


Added src/data/list/sublists.lean
- \+ *lemma* list.length_of_sublists_len
- \+ *theorem* list.length_sublists'
- \+ *theorem* list.length_sublists
- \+ *lemma* list.length_sublists_len
- \+ *theorem* list.map_ret_sublist_sublists
- \+ *theorem* list.map_sublists'_aux
- \+ *theorem* list.mem_sublists'
- \+ *theorem* list.mem_sublists
- \+ *lemma* list.mem_sublists_len
- \+ *lemma* list.mem_sublists_len_self
- \+ *theorem* list.sublists'_aux_append
- \+ *theorem* list.sublists'_aux_eq_sublists'
- \+ *theorem* list.sublists'_cons
- \+ *theorem* list.sublists'_eq_sublists
- \+ *theorem* list.sublists'_nil
- \+ *theorem* list.sublists'_reverse
- \+ *theorem* list.sublists'_singleton
- \+ *theorem* list.sublists_append
- \+ *theorem* list.sublists_aux_cons_append
- \+ *theorem* list.sublists_aux_cons_cons
- \+ *theorem* list.sublists_aux_cons_eq_sublists_aux₁
- \+ *theorem* list.sublists_aux_eq_foldr.aux
- \+ *theorem* list.sublists_aux_eq_foldr
- \+ *theorem* list.sublists_aux_ne_nil
- \+ *theorem* list.sublists_aux₁_append
- \+ *theorem* list.sublists_aux₁_bind
- \+ *theorem* list.sublists_aux₁_concat
- \+ *theorem* list.sublists_aux₁_eq_sublists_aux
- \+ *theorem* list.sublists_concat
- \+ *theorem* list.sublists_eq_sublists'
- \+ *def* list.sublists_len
- \+ *def* list.sublists_len_aux
- \+ *lemma* list.sublists_len_aux_append
- \+ *lemma* list.sublists_len_aux_eq
- \+ *lemma* list.sublists_len_aux_zero
- \+ *lemma* list.sublists_len_sublist_of_sublist
- \+ *lemma* list.sublists_len_sublist_sublists'
- \+ *lemma* list.sublists_len_succ_cons
- \+ *lemma* list.sublists_len_succ_nil
- \+ *lemma* list.sublists_len_zero
- \+ *theorem* list.sublists_nil
- \+ *theorem* list.sublists_reverse
- \+ *theorem* list.sublists_singleton



## [2021-05-30 21:09:57](https://github.com/leanprover-community/mathlib/commit/14b597c)
feat(analysis/normed_space): ∥n • a∥ ≤ n * ∥a∥ ([#7745](https://github.com/leanprover-community/mathlib/pull/7745))
From LTE.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* nnnorm_gsmul_le
- \+ *lemma* nnnorm_nsmul_le
- \+ *lemma* norm_gsmul_le
- \+ *lemma* norm_nsmul_le



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
- \- *def* fintype.fintype_prod_left
- \- *def* fintype.fintype_prod_right
- \+ *def* fintype.prod_left
- \+ *def* fintype.prod_right

Modified src/group_theory/order_of_element.lean




## [2021-05-30 09:54:50](https://github.com/leanprover-community/mathlib/commit/4ea253b)
feat(measure_theory/integration): in a sigma finite space, there exists an integrable positive function ([#7721](https://github.com/leanprover-community/mathlib/pull/7721))
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+ *lemma* measurable.nnreal_tsum

Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.exists_integrable_pos_of_sigma_finite

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* tsum_pos

Modified src/topology/instances/ennreal.lean
- \+ *lemma* nnreal.has_sum_lt
- \+ *lemma* nnreal.has_sum_strict_mono
- \+ *lemma* nnreal.tsum_eq_to_nnreal_tsum
- \+ *lemma* nnreal.tsum_lt_tsum
- \+ *lemma* nnreal.tsum_pos
- \+ *lemma* nnreal.tsum_strict_mono



## [2021-05-30 08:29:40](https://github.com/leanprover-community/mathlib/commit/8e25bb6)
feat(algebra/homology): complexes in functor categories ([#7744](https://github.com/leanprover-community/mathlib/pull/7744))
From LTE.
#### Estimated changes
Added src/algebra/homology/functor.lean
- \+ *def* homological_complex.as_functor
- \+ *def* homological_complex.complex_of_functors_to_functor_to_complex



## [2021-05-30 08:29:39](https://github.com/leanprover-community/mathlib/commit/f4d145e)
feat(algebra/homology): construct isomorphisms of complexes ([#7741](https://github.com/leanprover-community/mathlib/pull/7741))
From LTE.
#### Estimated changes
Modified src/algebra/homology/homological_complex.lean
- \+ *def* homological_complex.hom.iso_app
- \+ *def* homological_complex.hom.iso_of_components
- \+ *lemma* homological_complex.hom.iso_of_components_app



## [2021-05-30 08:29:38](https://github.com/leanprover-community/mathlib/commit/08bb112)
chore(ring_theory/hahn_series): extract lemmas from slow definitions ([#7737](https://github.com/leanprover-community/mathlib/pull/7737))
This doesn't make them much faster, but it makes it easier to tell which bits are slow
#### Estimated changes
Modified src/ring_theory/hahn_series.lean
- \+ *lemma* hahn_series.emb_domain_add
- \+ *lemma* hahn_series.emb_domain_mul
- \+ *lemma* hahn_series.emb_domain_one
- \+ *lemma* hahn_series.emb_domain_smul



## [2021-05-30 04:33:33](https://github.com/leanprover-community/mathlib/commit/e2168e5)
feat(src/ring_theory/derivation): merge duplicates `derivation.comp` and `linear_map.comp_der` ([#7727](https://github.com/leanprover-community/mathlib/pull/7727))
I propose keeping the version introduced in [#7715](https://github.com/leanprover-community/mathlib/pull/7715) since it also contains
the statement that the push forward is linear, but moving it to the `linear_map`
namespace to enable dot notation.
Thanks to @Nicknamen for alerting me to the duplication: https://github.com/leanprover-community/mathlib/pull/7715#issuecomment-849192370
#### Estimated changes
Modified src/ring_theory/derivation.lean
- \- *def* derivation.comp
- \+/\- *def* linear_map.comp_der
- \- *lemma* linear_map.comp_der_apply



## [2021-05-30 04:33:32](https://github.com/leanprover-community/mathlib/commit/9d63c38)
feat(topology/continuous_function/algebra): add `coe_fn_(linear_map|ring_hom|alg_hom)` ([#7720](https://github.com/leanprover-community/mathlib/pull/7720))
#### Estimated changes
Modified src/topology/continuous_function/algebra.lean
- \+ *def* continuous_map.coe_fn_alg_hom
- \+ *def* continuous_map.coe_fn_linear_map
- \+ *def* continuous_map.coe_fn_ring_hom



## [2021-05-30 01:16:52](https://github.com/leanprover-community/mathlib/commit/a3ba4d4)
feat(algebra/homology): eval and forget functors ([#7742](https://github.com/leanprover-community/mathlib/pull/7742))
From LTE.
#### Estimated changes
Modified src/algebra/homology/additive.lean


Modified src/algebra/homology/differential_object.lean


Modified src/algebra/homology/homological_complex.lean
- \+ *def* homological_complex.eval
- \- *def* homological_complex.eval_at
- \+ *def* homological_complex.forget
- \+ *def* homological_complex.forget_eval

Modified src/category_theory/graded_object.lean
- \+ *def* category_theory.graded_object.eval



## [2021-05-29 18:15:17](https://github.com/leanprover-community/mathlib/commit/035aa60)
feat(analysis/normed_space): SemiNormedGroup.has_zero_object ([#7740](https://github.com/leanprover-community/mathlib/pull/7740))
From LTE.
#### Estimated changes
Modified src/analysis/normed_space/SemiNormedGroup.lean
- \+ *lemma* SemiNormedGroup.coe_comp
- \+ *lemma* SemiNormedGroup.zero_apply



## [2021-05-29 02:32:43](https://github.com/leanprover-community/mathlib/commit/1ac49b0)
chore(category_theory): dualize filtered categories to cofiltered categories ([#7731](https://github.com/leanprover-community/mathlib/pull/7731))
Per request on [zulip](https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/status.20update/near/240548989).
I have not attempted to dualize "filtered colimits commute with finite limits", as I've never heard of that being used.
#### Estimated changes
Modified src/category_theory/filtered.lean
- \+ *lemma* category_theory.is_cofiltered.cone_nonempty
- \+ *lemma* category_theory.is_cofiltered.eq_condition
- \+ *def* category_theory.is_cofiltered.inf
- \+ *lemma* category_theory.is_cofiltered.inf_exists
- \+ *lemma* category_theory.is_cofiltered.inf_objs_exists
- \+ *def* category_theory.is_cofiltered.inf_to
- \+ *lemma* category_theory.is_cofiltered.inf_to_commutes
- \+ *lemma* category_theory.is_cofiltered.of_equivalence
- \+ *lemma* category_theory.is_cofiltered.of_is_left_adjoint
- \+ *lemma* category_theory.is_cofiltered.of_left_adjoint



## [2021-05-28 19:12:47](https://github.com/leanprover-community/mathlib/commit/f74a375)
chore(linear_algebra/finsupp): remove useless lemma ([#7734](https://github.com/leanprover-community/mathlib/pull/7734))
The lemma is not used in mathlib, it's mathematically useless (you'd never have a surjective function from an indexing set to a module), and it's badly named, so I propose removing it entirely.
#### Estimated changes
Modified src/linear_algebra/finsupp.lean
- \- *theorem* finsupp.total_range



## [2021-05-28 15:21:27](https://github.com/leanprover-community/mathlib/commit/13746fe)
feat(group_theory/subgroup linear_algebra/prod): add ker_prod_map ([#7729](https://github.com/leanprover-community/mathlib/pull/7729))
The kernel of the product of two `group_hom` is the product of the kernels (and similarly for monoids).
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* monoid_hom.ker_prod_map
- \+ *lemma* monoid_hom.prod_map_comap_prod

Modified src/linear_algebra/prod.lean
- \+ *lemma* linear_map.ker_prod_map
- \+ *lemma* linear_map.prod_map_comap_prod



## [2021-05-28 11:55:01](https://github.com/leanprover-community/mathlib/commit/5fff3b1)
feat(ring_theory/mv_polynomial/basic): add polynomial.basis_monomials ([#7728](https://github.com/leanprover-community/mathlib/pull/7728))
We add `polynomial.basis_monomials` : the monomials form a basis on `polynomial R`.
Because of the structure of the import, it seems to me a little complicated to do it directly, so I use `mv_polynomial.punit_alg_equiv`
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+/\- *def* finsupp.equiv_fun_on_fintype

Modified src/data/polynomial/algebra_map.lean
- \+/\- *lemma* polynomial.C_eq_algebra_map
- \+ *def* polynomial.to_finsupp_iso_alg

Modified src/data/polynomial/basic.lean
- \+/\- *lemma* polynomial.monomial_one_right_eq_X_pow

Modified src/data/polynomial/monomial.lean


Modified src/ring_theory/mv_polynomial/basic.lean
- \+ *lemma* polynomial.coe_basis_monomials



## [2021-05-27 09:01:17](https://github.com/leanprover-community/mathlib/commit/5360e47)
feat(algebra/module/linear_map): `linear_(map|equiv).restrict_scalars` is injective ([#7725](https://github.com/leanprover-community/mathlib/pull/7725))
So as not to repeat them for the lemmas, I moved the typeclasses into a `variables` statement.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+/\- *def* linear_equiv.restrict_scalars
- \+ *lemma* linear_equiv.restrict_scalars_inj
- \+ *lemma* linear_equiv.restrict_scalars_injective
- \+/\- *def* linear_map.restrict_scalars
- \+ *lemma* linear_map.restrict_scalars_inj
- \+ *lemma* linear_map.restrict_scalars_injective



## [2021-05-27 05:47:47](https://github.com/leanprover-community/mathlib/commit/6109558)
chore(category_theory/*): provide aliases quiver.hom.le and has_le.le.hom ([#7677](https://github.com/leanprover-community/mathlib/pull/7677))
#### Estimated changes
Modified src/algebra/category/Module/limits.lean


Modified src/category_theory/category/default.lean
- \+/\- *lemma* category_theory.hom_of_le_le_of_hom
- \+/\- *lemma* category_theory.hom_of_le_refl
- \+/\- *lemma* category_theory.le_of_hom_hom_of_le

Modified src/category_theory/category/pairwise.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/functor.lean


Modified src/category_theory/isomorphism.lean
- \+/\- *lemma* category_theory.iso.to_eq

Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/opposites.lean
- \+/\- *lemma* category_theory.le_of_op_hom
- \+/\- *def* category_theory.op_hom_of_le

Modified src/category_theory/sites/spaces.lean


Modified src/category_theory/skeletal.lean


Modified src/category_theory/subobject/basic.lean


Modified src/category_theory/subobject/lattice.lean


Modified src/category_theory/subobject/types.lean


Modified src/topology/category/Profinite/as_limit.lean


Modified src/topology/category/Top/limits.lean


Modified src/topology/category/Top/open_nhds.lean


Modified src/topology/category/Top/opens.lean
- \+/\- *def* topological_space.opens.bot_le
- \+/\- *def* topological_space.opens.inf_le_left
- \+/\- *def* topological_space.opens.inf_le_right
- \+/\- *def* topological_space.opens.le_supr
- \+/\- *def* topological_space.opens.le_top

Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean


Modified src/topology/sheaves/sheaf_condition/unique_gluing.lean




## [2021-05-27 00:46:29](https://github.com/leanprover-community/mathlib/commit/a85fbda)
feat(algebra/opposites): add units.op_equiv ([#7723](https://github.com/leanprover-community/mathlib/pull/7723))
#### Estimated changes
Modified src/algebra/opposites.lean
- \+ *lemma* units.coe_op_equiv_symm
- \+ *lemma* units.coe_unop_op_equiv
- \+ *def* units.op_equiv



## [2021-05-27 00:46:28](https://github.com/leanprover-community/mathlib/commit/20291d0)
feat(topology/semicontinuous): basics on lower and upper semicontinuous functions ([#7693](https://github.com/leanprover-community/mathlib/pull/7693))
We mimick the interface for continuity, by introducing predicates `lower_semicontinuous_within_at`, `lower_semicontinuous_at`, `lower_semicontinuous_on` and `lower_semicontinuous` (and similarly for upper semicontinuity).
#### Estimated changes
Modified src/algebra/ordered_monoid.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/constructions.lean
- \+ *lemma* mem_nhds_prod_iff'

Added src/topology/semicontinuous.lean
- \+ *lemma* continuous.lower_semicontinuous
- \+ *lemma* continuous.upper_semicontinuous
- \+ *lemma* continuous_at.lower_semicontinuous_at
- \+ *lemma* continuous_at.upper_semicontinuous_at
- \+ *lemma* continuous_at_iff_lower_upper_semicontinuous_at
- \+ *lemma* continuous_iff_lower_upper_semicontinuous
- \+ *lemma* continuous_on.lower_semicontinuous_on
- \+ *lemma* continuous_on.upper_semicontinuous_on
- \+ *lemma* continuous_on_iff_lower_upper_semicontinuous_on
- \+ *lemma* continuous_within_at.lower_semicontinuous_within_at
- \+ *lemma* continuous_within_at.upper_semicontinuous_within_at
- \+ *lemma* continuous_within_at_iff_lower_upper_semicontinuous_within_at
- \+ *lemma* is_closed.lower_semicontinuous_at_indicator
- \+ *lemma* is_closed.lower_semicontinuous_indicator
- \+ *lemma* is_closed.lower_semicontinuous_on_indicator
- \+ *lemma* is_closed.lower_semicontinuous_within_at_indicator
- \+ *lemma* is_closed.upper_semicontinuous_at_indicator
- \+ *lemma* is_closed.upper_semicontinuous_indicator
- \+ *lemma* is_closed.upper_semicontinuous_on_indicator
- \+ *lemma* is_closed.upper_semicontinuous_within_at_indicator
- \+ *lemma* is_open.lower_semicontinuous_at_indicator
- \+ *lemma* is_open.lower_semicontinuous_indicator
- \+ *lemma* is_open.lower_semicontinuous_on_indicator
- \+ *lemma* is_open.lower_semicontinuous_within_at_indicator
- \+ *lemma* is_open.upper_semicontinuous_at_indicator
- \+ *lemma* is_open.upper_semicontinuous_indicator
- \+ *lemma* is_open.upper_semicontinuous_on_indicator
- \+ *lemma* is_open.upper_semicontinuous_within_at_indicator
- \+ *lemma* lower_semicontinuous.add'
- \+ *lemma* lower_semicontinuous.add
- \+ *lemma* lower_semicontinuous.is_open_preimage
- \+ *lemma* lower_semicontinuous.lower_semicontinuous_at
- \+ *lemma* lower_semicontinuous.lower_semicontinuous_on
- \+ *lemma* lower_semicontinuous.lower_semicontinuous_within_at
- \+ *def* lower_semicontinuous
- \+ *lemma* lower_semicontinuous_at.add'
- \+ *lemma* lower_semicontinuous_at.add
- \+ *lemma* lower_semicontinuous_at.lower_semicontinuous_within_at
- \+ *def* lower_semicontinuous_at
- \+ *lemma* lower_semicontinuous_at_bsupr
- \+ *lemma* lower_semicontinuous_at_const
- \+ *lemma* lower_semicontinuous_at_sum
- \+ *lemma* lower_semicontinuous_at_supr
- \+ *lemma* lower_semicontinuous_at_tsum
- \+ *lemma* lower_semicontinuous_bsupr
- \+ *lemma* lower_semicontinuous_const
- \+ *theorem* lower_semicontinuous_iff_is_open
- \+ *lemma* lower_semicontinuous_on.add'
- \+ *lemma* lower_semicontinuous_on.add
- \+ *lemma* lower_semicontinuous_on.lower_semicontinuous_within_at
- \+ *lemma* lower_semicontinuous_on.mono
- \+ *def* lower_semicontinuous_on
- \+ *lemma* lower_semicontinuous_on_bsupr
- \+ *lemma* lower_semicontinuous_on_const
- \+ *lemma* lower_semicontinuous_on_sum
- \+ *lemma* lower_semicontinuous_on_supr
- \+ *lemma* lower_semicontinuous_on_tsum
- \+ *lemma* lower_semicontinuous_on_univ_iff
- \+ *lemma* lower_semicontinuous_sum
- \+ *lemma* lower_semicontinuous_supr
- \+ *lemma* lower_semicontinuous_tsum
- \+ *lemma* lower_semicontinuous_within_at.add'
- \+ *lemma* lower_semicontinuous_within_at.add
- \+ *lemma* lower_semicontinuous_within_at.mono
- \+ *def* lower_semicontinuous_within_at
- \+ *lemma* lower_semicontinuous_within_at_bsupr
- \+ *lemma* lower_semicontinuous_within_at_const
- \+ *lemma* lower_semicontinuous_within_at_sum
- \+ *lemma* lower_semicontinuous_within_at_supr
- \+ *lemma* lower_semicontinuous_within_at_tsum
- \+ *lemma* lower_semicontinuous_within_at_univ_iff
- \+ *lemma* upper_semicontinuous.add'
- \+ *lemma* upper_semicontinuous.add
- \+ *lemma* upper_semicontinuous.is_open_preimage
- \+ *lemma* upper_semicontinuous.upper_semicontinuous_at
- \+ *lemma* upper_semicontinuous.upper_semicontinuous_on
- \+ *lemma* upper_semicontinuous.upper_semicontinuous_within_at
- \+ *def* upper_semicontinuous
- \+ *lemma* upper_semicontinuous_at.add'
- \+ *lemma* upper_semicontinuous_at.add
- \+ *lemma* upper_semicontinuous_at.upper_semicontinuous_within_at
- \+ *def* upper_semicontinuous_at
- \+ *lemma* upper_semicontinuous_at_binfi
- \+ *lemma* upper_semicontinuous_at_const
- \+ *lemma* upper_semicontinuous_at_infi
- \+ *lemma* upper_semicontinuous_at_sum
- \+ *lemma* upper_semicontinuous_binfi
- \+ *lemma* upper_semicontinuous_const
- \+ *theorem* upper_semicontinuous_iff_is_open
- \+ *lemma* upper_semicontinuous_infi
- \+ *lemma* upper_semicontinuous_on.add'
- \+ *lemma* upper_semicontinuous_on.add
- \+ *lemma* upper_semicontinuous_on.mono
- \+ *lemma* upper_semicontinuous_on.upper_semicontinuous_within_at
- \+ *def* upper_semicontinuous_on
- \+ *lemma* upper_semicontinuous_on_binfi
- \+ *lemma* upper_semicontinuous_on_const
- \+ *lemma* upper_semicontinuous_on_infi
- \+ *lemma* upper_semicontinuous_on_sum
- \+ *lemma* upper_semicontinuous_on_univ_iff
- \+ *lemma* upper_semicontinuous_sum
- \+ *lemma* upper_semicontinuous_within_at.add'
- \+ *lemma* upper_semicontinuous_within_at.add
- \+ *lemma* upper_semicontinuous_within_at.mono
- \+ *def* upper_semicontinuous_within_at
- \+ *lemma* upper_semicontinuous_within_at_binfi
- \+ *lemma* upper_semicontinuous_within_at_const
- \+ *lemma* upper_semicontinuous_within_at_infi
- \+ *lemma* upper_semicontinuous_within_at_sum
- \+ *lemma* upper_semicontinuous_within_at_univ_iff



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
- \+ *theorem* ennreal.exists_pos_sum_of_encodable'

Modified src/measure_theory/regular.lean
- \+ *lemma* is_open.exists_lt_is_closed_of_gt
- \+ *lemma* is_open.exists_lt_is_compact
- \+ *lemma* is_open.measure_eq_supr_is_closed
- \+ *lemma* is_open.measure_eq_supr_is_compact
- \+ *lemma* measurable_set.exists_is_open_lt_of_lt'
- \+ *lemma* measurable_set.exists_is_open_lt_of_lt
- \+ *lemma* measurable_set.exists_lt_is_closed_of_lt_top
- \+ *lemma* measurable_set.exists_lt_is_closed_of_lt_top_of_pos
- \+ *lemma* measurable_set.exists_lt_is_compact_of_lt_top
- \+ *lemma* measurable_set.exists_lt_is_compact_of_lt_top_of_pos
- \+ *lemma* measurable_set.measure_eq_infi_is_open'
- \+ *lemma* measurable_set.measure_eq_infi_is_open
- \+ *lemma* measurable_set.measure_eq_supr_is_closed_of_finite_measure
- \+ *lemma* measurable_set.measure_eq_supr_is_closed_of_lt_top
- \+ *lemma* measurable_set.measure_eq_supr_is_compact_of_lt_top
- \- *lemma* measure_theory.measure.regular.inner_regular_eq
- \- *lemma* measure_theory.measure.regular.outer_regular_eq
- \+ *lemma* measure_theory.measure.weakly_regular.exists_closed_subset_self_subset_open_of_pos
- \+ *lemma* measure_theory.measure.weakly_regular.exists_subset_is_open_measure_lt_top
- \+ *lemma* measure_theory.measure.weakly_regular.inner_regular_of_pseudo_emetric_space
- \+ *lemma* measure_theory.measure.weakly_regular.restrict_of_is_open
- \+ *lemma* measure_theory.measure.weakly_regular.restrict_of_measurable_set
- \+ *theorem* measure_theory.measure.weakly_regular.weakly_regular_of_inner_regular_of_finite_measure

Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* is_open.exists_Union_is_closed



## [2021-05-26 21:50:16](https://github.com/leanprover-community/mathlib/commit/a2e8b3c)
feat(special_functions/polynomials): Generalize some polynomial asymptotics to iff statements. ([#7545](https://github.com/leanprover-community/mathlib/pull/7545))
#### Estimated changes
Modified src/analysis/asymptotics/asymptotic_equivalent.lean
- \+ *lemma* asymptotics.is_equivalent_zero_iff_is_O_zero

Modified src/analysis/special_functions/polynomials.lean
- \+ *lemma* polynomial.abs_div_tendsto_at_top_of_degree_gt
- \+ *lemma* polynomial.abs_is_bounded_under_iff
- \+ *lemma* polynomial.abs_tendsto_at_top_iff
- \+ *lemma* polynomial.div_tendsto_zero_iff_degree_lt
- \- *lemma* polynomial.eval_div_tendsto_at_top_of_degree_gt
- \+ *lemma* polynomial.tendsto_at_bot_iff_leading_coeff_nonpos
- \+ *lemma* polynomial.tendsto_at_top_iff_leading_coeff_nonneg
- \+ *lemma* polynomial.tendsto_nhds_iff

Modified src/data/nat/with_bot.lean
- \+ *lemma* nat.with_bot.one_le_iff_zero_lt

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.tendsto_const_mul_pow_at_top_iff
- \+ *lemma* filter.tendsto_neg_const_mul_pow_at_top_iff

Modified src/order/liminf_limsup.lean
- \+ *lemma* filter.not_is_bounded_under_of_tendsto_at_bot
- \+ *lemma* filter.not_is_bounded_under_of_tendsto_at_top

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* mul_tendsto_nhds_one_nhds_one
- \+ *lemma* mul_tendsto_nhds_zero_left
- \+ *lemma* mul_tendsto_nhds_zero_right
- \+/\- *lemma* nhds_basis_Ioo'
- \+/\- *lemma* nhds_basis_Ioo
- \+ *lemma* nhds_basis_Ioo_pos
- \+ *lemma* nhds_basis_Ioo_pos_of_pos
- \+ *lemma* nhds_basis_abs_sub_lt
- \+ *lemma* nhds_basis_zero_abs_sub_lt
- \+ *lemma* nhds_eq_map_mul_left_nhds_one
- \+ *lemma* nhds_eq_map_mul_right_nhds_one
- \+ *lemma* tendsto_const_mul_fpow_at_top_zero
- \+ *lemma* tendsto_const_mul_fpow_at_top_zero_iff
- \+ *lemma* tendsto_const_mul_pow_nhds_iff

Modified src/topology/separation.lean
- \+ *lemma* tendsto_const_nhds_iff



## [2021-05-26 19:17:45](https://github.com/leanprover-community/mathlib/commit/fd43ce0)
feat(linear_algebra/matrix): generalize `basis.to_matrix_mul_to_matrix` ([#7670](https://github.com/leanprover-community/mathlib/pull/7670))
Now the second family of vectors does not have to form a basis.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *lemma* basis.sum_repr_mul_repr

Modified src/linear_algebra/matrix/basis.lean




## [2021-05-26 13:34:28](https://github.com/leanprover-community/mathlib/commit/fa27c0c)
feat(ring_theory/derivation): define push forward of derivations ([#7715](https://github.com/leanprover-community/mathlib/pull/7715))
#### Estimated changes
Modified src/ring_theory/derivation.lean
- \+ *lemma* derivation.coe_comp
- \+ *lemma* derivation.coe_to_linear_map_comp
- \+ *def* derivation.comp
- \+ *lemma* derivation.mk_coe



## [2021-05-26 13:34:27](https://github.com/leanprover-community/mathlib/commit/b059708)
feat(data/nnreal): filling out some lemmas ([#7710](https://github.com/leanprover-community/mathlib/pull/7710))
From LTE.
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.div_le_iff'
- \+ *lemma* nnreal.div_lt_iff'
- \+/\- *lemma* nnreal.div_lt_iff
- \+ *lemma* nnreal.le_div_iff'
- \+ *lemma* nnreal.le_div_iff
- \+ *lemma* nnreal.lt_div_iff'



## [2021-05-26 13:34:26](https://github.com/leanprover-community/mathlib/commit/273546e)
feat(group_theory/sub{group,monoid,semiring,ring}): subobjects inherit the actions of their carrier type ([#7665](https://github.com/leanprover-community/mathlib/pull/7665))
This acts as a generalization of `algebra.of_subsemiring` and `algebra.of_subring`, and transfers the weaker action structures too.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.smul_def

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* submonoid.smul_def

Modified src/ring_theory/subring.lean
- \+ *lemma* subring.smul_def

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* subsemiring.smul_def



## [2021-05-26 13:34:25](https://github.com/leanprover-community/mathlib/commit/66ec15c)
feat(analysis/complex/isometry): add linear_isometry_complex ([#6923](https://github.com/leanprover-community/mathlib/pull/6923))
add proof about the isometries in the complex plane
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* complex.conj_li_apply

Added src/analysis/complex/isometry.lean
- \+ *lemma* linear_isometry.abs_apply_sub_one_eq_abs_sub_one
- \+ *lemma* linear_isometry.im_apply_eq_im
- \+ *lemma* linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re
- \+ *lemma* linear_isometry.re_apply_eq_re
- \+ *lemma* linear_isometry.re_apply_eq_re_of_add_conj_eq
- \+ *lemma* linear_isometry_complex
- \+ *lemma* linear_isometry_complex_aux

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry_equiv.linear_isometry.id_apply
- \+ *lemma* linear_isometry_equiv.linear_isometry.id_to_linear_map

Modified src/data/complex/basic.lean
- \+ *lemma* complex.conj_one
- \+ *lemma* complex.conj_sub



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
- \- *lemma* finset.inf_eq_Inf
- \+ *lemma* finset.inf_eq_Inf_image
- \+ *lemma* finset.inf_id_eq_Inf
- \- *lemma* finset.sup_eq_Sup
- \+ *lemma* finset.sup_eq_Sup_image
- \+ *lemma* finset.sup_id_eq_Sup

Modified src/order/compactly_generated.lean


Modified src/order/complete_lattice.lean
- \+/\- *theorem* infi_true
- \+/\- *theorem* supr_true

Modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* cSup_empty
- \+ *lemma* cinfi_le_of_le
- \+ *lemma* cinfi_pos
- \+ *lemma* csupr_neg
- \+ *lemma* csupr_pos
- \+ *lemma* finset.inf'_eq_cInf_image
- \+ *lemma* finset.inf'_id_eq_cInf
- \+ *lemma* finset.sup'_eq_cSup_image
- \+ *lemma* finset.sup'_id_eq_cSup
- \+ *lemma* le_csupr_of_le
- \+/\- *theorem* with_bot.cSup_empty
- \+ *theorem* with_top.cInf_empty

Modified src/ring_theory/noetherian.lean




## [2021-05-26 08:25:15](https://github.com/leanprover-community/mathlib/commit/00394b7)
feat(tactic/simps): implement prefix names ([#7596](https://github.com/leanprover-community/mathlib/pull/7596))
* You can now write `initialize_simps_projections equiv (to_fun → coe as_prefix)` to add the projection name as a prefix to the simp lemmas: if you then write `@[simps coe] def foo ...` you get a lemma named `coe_foo`.
* Remove the `short_name` option from `simps_cfg`. This was unused and not that useful. 
* Refactor some tuples used in the functions into structures.
* Implements one item of [#5489](https://github.com/leanprover-community/mathlib/pull/5489).
#### Estimated changes
Modified src/data/list/defs.lean
- \+ *def* list.zip_with3
- \+ *def* list.zip_with4
- \+ *def* list.zip_with5

Modified src/meta/expr.lean
- \+ *def* name.append_to_last
- \+ *def* name.update_last

Modified src/tactic/reserved_notation.lean


Modified src/tactic/simps.lean


Modified test/simps.lean
- \+ *def* prefix_projection_names.equiv.simps.symm_apply
- \+ *def* prefix_projection_names.equiv.symm
- \+ *def* prefix_projection_names.foo
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


Modified test/examples.lean


Modified test/traversable.lean




## [2021-05-26 00:55:46](https://github.com/leanprover-community/mathlib/commit/fd1c8e7)
feat(data/list/forall2): add two lemmas about forall₂ and reverse ([#7714](https://github.com/leanprover-community/mathlib/pull/7714))
rel_reverse shows that forall₂ is preserved across reversed lists,
forall₂_iff_reverse uses rel_reverse to show that it is preserved in
both directions.
#### Estimated changes
Modified src/data/list/forall2.lean
- \+ *lemma* list.forall₂_reverse_iff
- \+ *lemma* list.rel_reverse



## [2021-05-25 23:21:27](https://github.com/leanprover-community/mathlib/commit/360ca9c)
feat(analysis/special_functions/integrals): `interval_integrable_log` ([#7713](https://github.com/leanprover-community/mathlib/pull/7713))
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* interval_integral.interval_integrable.log
- \+ *lemma* interval_integral.interval_integrable_log



## [2021-05-25 23:21:26](https://github.com/leanprover-community/mathlib/commit/f1425b6)
feat(measure_theory/interval_integral): `integral_comp_add_left` ([#7712](https://github.com/leanprover-community/mathlib/pull/7712))
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* interval_integral.integral_comp_add_left



## [2021-05-25 19:48:36](https://github.com/leanprover-community/mathlib/commit/82e78ce)
feat(algebra/big_operators/finprod): add lemma `finprod_mem_finset_of_product` ([#7439](https://github.com/leanprover-community/mathlib/pull/7439))
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_curry
- \+ *lemma* finprod_curry₃
- \+ *lemma* finprod_mem_finset_product'
- \+ *lemma* finprod_mem_finset_product
- \+ *lemma* finprod_mem_finset_product₃
- \+ *lemma* finprod_mem_mul_support
- \+ *lemma* finset.mul_support_of_fiberwise_prod_subset_image

Modified src/data/support.lean
- \+ *lemma* function.mul_support_along_fiber_finite_of_finite
- \+ *lemma* function.mul_support_along_fiber_subset



## [2021-05-25 17:19:09](https://github.com/leanprover-community/mathlib/commit/8078eca)
feat(linear_algebra): `det (M ⬝ N ⬝ M') = det N`, where `M'` is an inverse of `M` ([#7633](https://github.com/leanprover-community/mathlib/pull/7633))
This is an important step towards showing the determinant of `linear_map.to_matrix` does not depend on the choice of basis.
    
The main difficulty is allowing the two indexing types of `M` to be (a priori) different. They are in bijection though (using `basis.index_equiv` from [#7631](https://github.com/leanprover-community/mathlib/pull/7631)), so using `reindex_linear_equiv` we can turn everything into square matrices and apply the "usual" proof.
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *def* equiv_of_pi_lequiv_pi
- \+ *lemma* matrix.det_conj
- \+ *def* matrix.index_equiv_of_inv

Modified src/linear_algebra/matrix/reindex.lean
- \+ *lemma* matrix.reindex_alg_equiv_mul
- \+ *lemma* matrix.reindex_linear_equiv_mul

Modified src/linear_algebra/matrix/to_lin.lean
- \+ *lemma* matrix.to_lin'_mul_apply
- \+ *def* matrix.to_lin'_of_inv
- \+ *lemma* matrix.to_lin_mul_apply
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
Added src/algebra/category/Module/projective.lean
- \+ *lemma* Module.projective_of_free
- \+ *theorem* is_projective.iff_projective

Modified src/algebra/module/projective.lean
- \+ *theorem* is_projective.of_lifting_property'
- \+/\- *theorem* is_projective.of_lifting_property



## [2021-05-25 11:18:58](https://github.com/leanprover-community/mathlib/commit/bbf6150)
feat(measure_theory/measurable_space): add instances for subtypes ([#7702](https://github.com/leanprover-community/mathlib/pull/7702))
#### Estimated changes
Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_set.coe_bot
- \+ *lemma* measurable_set.coe_compl
- \+ *lemma* measurable_set.coe_empty
- \+ *lemma* measurable_set.coe_insert
- \+ *lemma* measurable_set.coe_inter
- \+ *lemma* measurable_set.coe_sdiff
- \+ *lemma* measurable_set.coe_top
- \+ *lemma* measurable_set.coe_union
- \+ *lemma* measurable_set.mem_coe



## [2021-05-25 11:18:57](https://github.com/leanprover-community/mathlib/commit/75e07d1)
feat(linear_algebra/matrix/determinant): lemmas about commutativity under det ([#7685](https://github.com/leanprover-community/mathlib/pull/7685))
#### Estimated changes
Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* matrix.det_mul_comm
- \+ *lemma* matrix.det_mul_left_comm
- \+ *lemma* matrix.det_mul_right_comm
- \+ *lemma* matrix.det_units_conj'
- \+ *lemma* matrix.det_units_conj



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
- \+ *def* add_action.to_perm_hom
- \- *def* add_units.vadd_perm_hom
- \+/\- *theorem* is_unit.smul_eq_zero
- \+/\- *lemma* is_unit.smul_left_cancel
- \+/\- *def* mul_action.to_perm
- \+ *def* mul_action.to_perm_hom
- \+ *lemma* smul_eq_iff_eq_inv_smul
- \+ *theorem* smul_eq_zero_iff_eq'
- \+ *theorem* smul_eq_zero_iff_eq
- \+ *theorem* smul_ne_zero_iff_ne'
- \+ *theorem* smul_ne_zero_iff_ne
- \- *lemma* units.inv_smul_smul
- \- *lemma* units.smul_eq_iff_eq_inv_smul
- \- *theorem* units.smul_eq_zero
- \- *lemma* units.smul_inv_smul
- \- *lemma* units.smul_left_cancel
- \- *theorem* units.smul_ne_zero
- \- *def* units.smul_perm
- \- *def* units.smul_perm_hom

Added src/group_theory/group_action/units.lean
- \+ *lemma* units.coe_smul
- \+ *lemma* units.smul_def
- \+ *lemma* units.smul_inv

Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/matrix/determinant.lean


Modified src/linear_algebra/matrix/nonsingular_inverse.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/measure_theory/arithmetic.lean
- \- *lemma* units.ae_measurable_const_smul_iff
- \- *lemma* units.measurable_const_smul_iff

Modified src/topology/algebra/mul_action.lean
- \+/\- *lemma* is_unit.continuous_at_const_smul_iff
- \+/\- *lemma* is_unit.continuous_const_smul_iff
- \+/\- *lemma* is_unit.continuous_on_const_smul_iff
- \+/\- *lemma* is_unit.continuous_within_at_const_smul_iff
- \+/\- *lemma* is_unit.is_closed_map_smul
- \+/\- *lemma* is_unit.is_open_map_smul
- \+/\- *lemma* is_unit.tendsto_const_smul_iff
- \- *lemma* units.tendsto_const_smul_iff



## [2021-05-25 05:41:54](https://github.com/leanprover-community/mathlib/commit/d81fcda)
feat(algebra/group_with_zero): add some equational lemmas ([#7705](https://github.com/leanprover-community/mathlib/pull/7705))
Add some equations for `group_with_zero` that are direct analogues of lemmas for `group`.
Useful for [#6923](https://github.com/leanprover-community/mathlib/pull/6923).
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* eq_inv_iff
- \+ *lemma* eq_inv_mul_iff_mul_eq'
- \+/\- *lemma* eq_inv_of_mul_left_eq_one
- \+/\- *lemma* eq_inv_of_mul_right_eq_one
- \+ *lemma* eq_mul_inv_iff_mul_eq'
- \+/\- *lemma* group_with_zero.mul_left_injective
- \+/\- *lemma* group_with_zero.mul_right_injective
- \+/\- *lemma* inv_eq_iff
- \+/\- *lemma* inv_eq_one'
- \+/\- *lemma* inv_inj'
- \+/\- *lemma* inv_mul_cancel
- \+/\- *lemma* inv_mul_cancel_left'
- \+/\- *lemma* inv_mul_cancel_right'
- \+ *lemma* inv_mul_eq_iff_eq_mul'
- \+ *lemma* inv_mul_eq_one'
- \+/\- *lemma* inv_ne_zero
- \+ *lemma* mul_eq_one_iff_eq_inv'
- \+ *lemma* mul_eq_one_iff_inv_eq'
- \+/\- *lemma* mul_inv_cancel_left'
- \+/\- *lemma* mul_inv_cancel_right'
- \+ *lemma* mul_inv_eq_iff_eq_mul'
- \+ *lemma* mul_inv_eq_one'



## [2021-05-25 00:46:31](https://github.com/leanprover-community/mathlib/commit/a880ea4)
feat(ring_theory/coprime): add some lemmas ([#7650](https://github.com/leanprover-community/mathlib/pull/7650))
#### Estimated changes
Modified src/ring_theory/coprime.lean
- \+ *theorem* is_coprime.is_unit_of_dvd'
- \+ *lemma* is_coprime.neg_left
- \+ *lemma* is_coprime.neg_left_iff
- \+ *lemma* is_coprime.neg_neg
- \+ *lemma* is_coprime.neg_neg_iff
- \+ *lemma* is_coprime.neg_right
- \+ *lemma* is_coprime.neg_right_iff
- \+ *theorem* is_coprime.of_coprime_of_dvd_left
- \+ *theorem* is_coprime.of_coprime_of_dvd_right
- \+ *theorem* is_coprime.pow_iff
- \+ *theorem* is_coprime.pow_left_iff
- \+ *theorem* is_coprime.pow_right_iff
- \+ *lemma* not_coprime_zero_zero



## [2021-05-25 00:46:30](https://github.com/leanprover-community/mathlib/commit/c3dcb7d)
feat(category_theory/limits): comma category colimit construction ([#7535](https://github.com/leanprover-community/mathlib/pull/7535))
As well as the duals. Also adds some autoparams for consistency with `has_limit` and some missing instances which are basically just versions of existing things
#### Estimated changes
Modified src/category_theory/arrow.lean
- \+ *def* category_theory.arrow.left_func
- \+ *def* category_theory.arrow.left_to_right
- \+ *def* category_theory.arrow.right_func

Added src/category_theory/limits/comma.lean
- \+ *def* category_theory.comma.cocone_of_preserves
- \+ *def* category_theory.comma.cocone_of_preserves_is_colimit
- \+ *def* category_theory.comma.colimit_auxiliary_cocone
- \+ *def* category_theory.comma.cone_of_preserves
- \+ *def* category_theory.comma.cone_of_preserves_is_limit
- \+ *def* category_theory.comma.limit_auxiliary_cone

Modified src/category_theory/limits/creates.lean


Modified src/category_theory/limits/kan_extension.lean


Modified src/category_theory/limits/over.lean
- \- *def* category_theory.functor.to_cocone
- \- *def* category_theory.functor.to_cone

Modified src/category_theory/limits/preserves/basic.lean


Modified src/category_theory/limits/punit.lean
- \+ *def* category_theory.limits.punit_cocone
- \+ *def* category_theory.limits.punit_cone

Modified src/category_theory/over.lean


Modified src/category_theory/punit.lean


Modified src/category_theory/structured_arrow.lean
- \+/\- *lemma* category_theory.costructured_arrow.eq_mk
- \+/\- *def* category_theory.costructured_arrow.proj
- \+ *lemma* category_theory.costructured_arrow.w
- \+/\- *def* category_theory.structured_arrow.proj
- \+ *lemma* category_theory.structured_arrow.w



## [2021-05-24 19:29:16](https://github.com/leanprover-community/mathlib/commit/17f3b80)
feat(100-theorems-list/16_abel_ruffini): some simplifications ([#7699](https://github.com/leanprover-community/mathlib/pull/7699))
#### Estimated changes
Modified archive/100-theorems-list/16_abel_ruffini.lean
- \+/\- *lemma* abel_ruffini.irreducible_Phi

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
- \+/\- *lemma* smooth_bump_function.c_mem_support

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
- \+ *lemma* is_open.mem_nhds
- \+ *lemma* mem_nhds_iff
- \- *lemma* mem_nhds_sets
- \- *lemma* mem_nhds_sets_iff
- \+ *lemma* mem_of_mem_nhds
- \- *lemma* mem_of_nhds

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
- \+ *lemma* opposite.op_ne_zero_iff
- \+ *lemma* opposite.unop_ne_zero_iff



## [2021-05-24 14:07:32](https://github.com/leanprover-community/mathlib/commit/a09ddc7)
feat(measure_theory/interval_integral): `interval_integrable.mono` ([#7679](https://github.com/leanprover-community/mathlib/pull/7679))
`interval_integrable f ν a b → interval c d ⊆ interval a b → μ ≤ ν → interval_integrable f μ c d`
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* interval_integrable.def
- \+ *lemma* interval_integrable.mono
- \+ *lemma* interval_integrable.mono_measure
- \+ *lemma* interval_integrable.mono_set
- \+ *lemma* interval_integrable.mono_set_ae
- \+/\- *lemma* interval_integrable.trans
- \+ *lemma* interval_integrable_iff
- \+/\- *lemma* measure_theory.integrable.interval_integrable



## [2021-05-24 11:01:13](https://github.com/leanprover-community/mathlib/commit/0b51a72)
feat(linear_algebra/determinant): specialize `is_basis.iff_det` ([#7668](https://github.com/leanprover-community/mathlib/pull/7668))
After the bundled basis refactor, applying `is_basis.iff_det` in the forward direction is slightly more involved (since defining the `iff` requires an unbundled basis), so I added a lemma that does the necessary translation between "unbundled basis" and "bundled basis" for you.
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* basis.is_unit_det
- \- *lemma* is_basis.iff_det
- \+ *lemma* is_basis_iff_det



## [2021-05-24 11:01:12](https://github.com/leanprover-community/mathlib/commit/8ff2783)
feat(counterexamples/cyclotomic_105): add coeff_cyclotomic_105 ([#7648](https://github.com/leanprover-community/mathlib/pull/7648))
We show that `coeff (cyclotomic 105 ℤ) 7 = -2`, proving that not all coefficients of cyclotomic polynomials are `0`, `-1` or `1`.
#### Estimated changes
Added counterexamples/cyclotomic_105.lean
- \+ *lemma* coeff_cyclotomic_105
- \+ *lemma* cyclotomic_105
- \+ *lemma* cyclotomic_15
- \+ *lemma* cyclotomic_21
- \+ *lemma* cyclotomic_35
- \+ *lemma* cyclotomic_3
- \+ *lemma* cyclotomic_5
- \+ *lemma* cyclotomic_7
- \+ *lemma* not_forall_coeff_cyclotomic_neg_one_zero_one
- \+ *lemma* prime_3
- \+ *lemma* prime_5
- \+ *lemma* prime_7
- \+ *lemma* proper_divisors_105
- \+ *lemma* proper_divisors_15
- \+ *lemma* proper_divisors_21
- \+ *lemma* proper_divisors_35

Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.coeff_bit0_mul
- \+ *lemma* polynomial.coeff_bit1_mul



## [2021-05-24 05:13:08](https://github.com/leanprover-community/mathlib/commit/16733c8)
chore(data/nat/basic): move unique {units/add_units} instances ([#7701](https://github.com/leanprover-community/mathlib/pull/7701))
#### Estimated changes
Modified src/data/nat/basic.lean


Modified src/ring_theory/int/basic.lean




## [2021-05-23 23:25:01](https://github.com/leanprover-community/mathlib/commit/2734d91)
fix(data/nat/factorial): fix factorial_zero ([#7697](https://github.com/leanprover-community/mathlib/pull/7697))
#### Estimated changes
Modified src/data/nat/factorial.lean
- \+/\- *theorem* nat.factorial_zero



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
- \+ *lemma* finset.nonempty.cInf_mem
- \+ *lemma* finset.nonempty.cSup_mem
- \+ *lemma* set.nonempty.cInf_mem
- \+ *lemma* set.nonempty.cSup_mem



## [2021-05-22 12:15:36](https://github.com/leanprover-community/mathlib/commit/418dc04)
feat(100-theorems-list/16_abel_ruffini): The Abel-Ruffini Theorem ([#7562](https://github.com/leanprover-community/mathlib/pull/7562))
It's done!
#### Estimated changes
Added archive/100-theorems-list/16_abel_ruffini.lean
- \+ *lemma* abel_ruffini.coeff_five_Phi
- \+ *lemma* abel_ruffini.coeff_zero_Phi
- \+ *lemma* abel_ruffini.complex_roots_Phi
- \+ *lemma* abel_ruffini.degree_Phi
- \+ *theorem* abel_ruffini.exists_not_solvable_by_rad
- \+ *lemma* abel_ruffini.gal_Phi
- \+ *lemma* abel_ruffini.irreducible_Phi
- \+ *lemma* abel_ruffini.leading_coeff_Phi
- \+ *lemma* abel_ruffini.map_Phi
- \+ *lemma* abel_ruffini.monic_Phi
- \+ *lemma* abel_ruffini.nat_degree_Phi
- \+ *theorem* abel_ruffini.not_solvable_by_rad'
- \+ *theorem* abel_ruffini.not_solvable_by_rad
- \+ *lemma* abel_ruffini.real_roots_Phi_ge
- \+ *lemma* abel_ruffini.real_roots_Phi_ge_aux
- \+ *lemma* abel_ruffini.real_roots_Phi_le

Modified docs/100.yaml


Modified src/field_theory/separable.lean
- \+ *lemma* polynomial.card_root_set_eq_nat_degree



## [2021-05-22 06:50:13](https://github.com/leanprover-community/mathlib/commit/b29d40c)
fix(algebra): change local transparency to semireducible ([#7687](https://github.com/leanprover-community/mathlib/pull/7687))
* When a type is `[irreducible]` it should locally be made `[semireducible]` and (almost) never `[reducible]`. 
* If it is made `[reducible]`, type-class inference will unfold this definition, and will apply instances that would not type-check when the definition is `[irreducible]`
#### Estimated changes
Modified src/algebra/opposites.lean
- \+/\- *lemma* opposite.op_eq_one_iff
- \+/\- *lemma* opposite.op_eq_zero_iff
- \+/\- *lemma* opposite.unop_eq_one_iff
- \+/\- *lemma* opposite.unop_eq_zero_iff

Modified src/algebra/ordered_monoid.lean


Modified src/data/polynomial/ring_division.lean




## [2021-05-21 21:35:13](https://github.com/leanprover-community/mathlib/commit/f8530d5)
feat(ring_theory/ideal/operations): `ideal.span_singleton_pow` ([#7660](https://github.com/leanprover-community/mathlib/pull/7660))
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.span_singleton_pow



## [2021-05-21 16:38:59](https://github.com/leanprover-community/mathlib/commit/f70e160)
chore(order/conditionally_complete_lattice): golf proofs with `order_dual` ([#7684](https://github.com/leanprover-community/mathlib/pull/7684))
Even in the places where this doesn't result in a shorter proof, it makes it obvious that the `inf` lemmas have a matching `sup` lemma.
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean




## [2021-05-21 11:28:01](https://github.com/leanprover-community/mathlib/commit/233eff0)
feat(data/fintype/card_embedding): the birthday problem ([#7363](https://github.com/leanprover-community/mathlib/pull/7363))
#### Estimated changes
Added archive/100-theorems-list/93_birthday_problem.lean
- \+ *theorem* birthday

Modified docs/100.yaml


Modified src/data/equiv/basic.lean
- \+ *def* equiv.subtype_prod_equiv_sigma_subtype

Added src/data/equiv/embedding.lean
- \+ *def* equiv.cod_restrict
- \+ *def* equiv.prod_embedding_disjoint_equiv_sigma_embedding_restricted
- \+ *def* equiv.sum_embedding_equiv_prod_embedding_disjoint
- \+ *def* equiv.sum_embedding_equiv_sigma_embedding_restricted
- \+ *def* equiv.unique_embedding_equiv_result

Modified src/data/fintype/basic.lean
- \+ *lemma* function.embedding.is_empty_of_card_lt

Added src/data/fintype/card_embedding.lean
- \+ *theorem* fintype.card_embedding
- \+ *theorem* fintype.card_embedding_eq_if
- \+ *lemma* fintype.card_embedding_eq_infinite
- \+ *theorem* fintype.card_embedding_eq_zero
- \+ *lemma* fintype.card_embedding_of_unique

Modified src/data/nat/factorial.lean
- \+ *lemma* nat.desc_fac_of_sub

Modified src/logic/embedding.lean
- \+ *def* equiv.embedding_congr
- \+ *lemma* equiv.embedding_congr_apply_trans
- \+ *lemma* equiv.embedding_congr_refl
- \+ *lemma* equiv.embedding_congr_symm
- \+ *lemma* equiv.embedding_congr_trans
- \+ *def* equiv.subtype_injective_equiv_embedding
- \+ *lemma* function.embedding.mk_coe

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
- \+ *lemma* has_ssubset.ssubset.asymm
- \+ *lemma* has_ssubset.ssubset.trans
- \+ *lemma* has_subset.subset.antisymm
- \+ *lemma* has_subset.subset.trans



## [2021-05-21 00:33:52](https://github.com/leanprover-community/mathlib/commit/53e2307)
feat(ring_theory): every left-noetherian ring has invariant basis number ([#7678](https://github.com/leanprover-community/mathlib/pull/7678))
This is a lovely case where we get more for less.
By directly proving that every left-noetherian ring has invariant basis number, we don't need to import `linear_algebra.finite_dimensional` in order to do the `field` case. This means that in a future PR we can instead import `ring_theory.invariant_basis_number` in `linear_algebra.finite_dimensional`, and set up the theory of bases in greater generality.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *lemma* linear_map.map_eq_zero_iff

Modified src/linear_algebra/basic.lean
- \+ *theorem* linear_map.fun_left_injective_of_surjective
- \+ *theorem* linear_map.fun_left_surjective_of_injective

Modified src/linear_algebra/invariant_basis_number.lean
- \- *lemma* invariant_basis_number_field
- \+ *lemma* le_of_fin_injective
- \+ *lemma* le_of_fin_surjective



## [2021-05-21 00:33:51](https://github.com/leanprover-community/mathlib/commit/c63c6d1)
feat(order/closure): make closure operators implementable ([#7608](https://github.com/leanprover-community/mathlib/pull/7608))
introduce `lower_adjoint` as a way to talk about closure operators whose input and output types do not match
#### Estimated changes
Modified src/order/closure.lean
- \+/\- *lemma* closure_operator.closure_bsupr_closure
- \+/\- *lemma* closure_operator.closure_inf_le
- \+/\- *lemma* closure_operator.closure_sup_closure
- \+/\- *lemma* closure_operator.closure_sup_closure_le
- \+/\- *lemma* closure_operator.closure_sup_closure_left
- \+/\- *lemma* closure_operator.closure_sup_closure_right
- \+/\- *lemma* closure_operator.closure_supr_closure
- \+/\- *lemma* closure_operator.closure_top
- \+/\- *def* closure_operator.gi
- \+/\- *def* closure_operator.simps.apply
- \+/\- *lemma* closure_operator.top_mem_closed
- \+/\- *lemma* closure_operator_gi_self
- \+/\- *def* galois_connection.closure_operator
- \+ *def* galois_connection.lower_adjoint
- \+ *def* lower_adjoint.closed
- \+ *lemma* lower_adjoint.closed_eq_range_close
- \+ *lemma* lower_adjoint.closure_Union_closure
- \+ *lemma* lower_adjoint.closure_bUnion_closure
- \+ *lemma* lower_adjoint.closure_bsupr_closure
- \+ *lemma* lower_adjoint.closure_eq_self_of_mem_closed
- \+ *lemma* lower_adjoint.closure_inf_le
- \+ *lemma* lower_adjoint.closure_is_closed
- \+ *lemma* lower_adjoint.closure_le_closed_iff_le
- \+ *def* lower_adjoint.closure_operator
- \+ *lemma* lower_adjoint.closure_sup_closure
- \+ *lemma* lower_adjoint.closure_sup_closure_le
- \+ *lemma* lower_adjoint.closure_sup_closure_left
- \+ *lemma* lower_adjoint.closure_sup_closure_right
- \+ *lemma* lower_adjoint.closure_supr_closure
- \+ *lemma* lower_adjoint.closure_top
- \+ *lemma* lower_adjoint.closure_union_closure
- \+ *lemma* lower_adjoint.closure_union_closure_left
- \+ *lemma* lower_adjoint.closure_union_closure_right
- \+ *lemma* lower_adjoint.closure_union_closure_subset
- \+ *lemma* lower_adjoint.eq_of_le
- \+ *lemma* lower_adjoint.ext
- \+ *lemma* lower_adjoint.gc
- \+ *lemma* lower_adjoint.idempotent
- \+ *lemma* lower_adjoint.le_closure
- \+ *lemma* lower_adjoint.le_closure_iff
- \+ *lemma* lower_adjoint.le_iff_subset
- \+ *lemma* lower_adjoint.mem_closed_iff
- \+ *lemma* lower_adjoint.mem_closed_iff_closure_le
- \+ *lemma* lower_adjoint.mem_iff
- \+ *lemma* lower_adjoint.monotone
- \+ *def* lower_adjoint.simps.apply
- \+ *lemma* lower_adjoint.subset_closure
- \+ *def* lower_adjoint.to_closed



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
- \+ *lemma* exists_open_set_nhds'
- \+ *lemma* exists_open_set_nhds

Modified src/topology/separation.lean
- \+ *lemma* exists_subset_nhd_of_compact
- \+ *lemma* is_topological_basis_clopen
- \+ *lemma* nhds_basis_clopen

Modified src/topology/subset_properties.lean
- \+ *lemma* exists_subset_nhd_of_compact'
- \+ *lemma* exists_subset_nhd_of_compact_space
- \+ *lemma* is_clopen_Union
- \+ *lemma* is_clopen_bUnion



## [2021-05-20 13:34:18](https://github.com/leanprover-community/mathlib/commit/d3ec77c)
feat(category_theory/limits): reflecting limits of isomorphic diagram ([#7674](https://github.com/leanprover-community/mathlib/pull/7674))
#### Estimated changes
Modified src/category_theory/limits/preserves/basic.lean
- \+ *def* category_theory.limits.reflects_colimit_of_iso_diagram
- \+ *def* category_theory.limits.reflects_limit_of_iso_diagram



## [2021-05-20 08:06:42](https://github.com/leanprover-community/mathlib/commit/c5951f3)
feat(ring_theory/noetherian): a surjective endomorphism of a noetherian module is injective ([#7676](https://github.com/leanprover-community/mathlib/pull/7676))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *def* linear_map.iterate_ker
- \+ *def* linear_map.iterate_range

Modified src/ring_theory/noetherian.lean
- \+ *theorem* is_noetherian.bijective_of_surjective_endomorphism
- \+ *theorem* is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot
- \+ *theorem* is_noetherian.injective_of_surjective_endomorphism
- \+ *theorem* monotone_stabilizes_iff_noetherian



## [2021-05-20 08:06:41](https://github.com/leanprover-community/mathlib/commit/ff51159)
feat(algebra/homology/*): add hypotheses to the d_comp_d' axiom ([#7673](https://github.com/leanprover-community/mathlib/pull/7673))
#### Estimated changes
Modified src/algebra/homology/additive.lean


Modified src/algebra/homology/augment.lean


Modified src/algebra/homology/differential_object.lean


Modified src/algebra/homology/flip.lean


Modified src/algebra/homology/homological_complex.lean
- \+ *lemma* homological_complex.d_comp_d



## [2021-05-20 08:06:40](https://github.com/leanprover-community/mathlib/commit/2d414d0)
feat(algebra/homology/homological_complex): add condition to hom.comm' ([#7666](https://github.com/leanprover-community/mathlib/pull/7666))
#### Estimated changes
Modified src/algebra/homology/additive.lean


Modified src/algebra/homology/differential_object.lean


Modified src/algebra/homology/flip.lean


Modified src/algebra/homology/homological_complex.lean
- \+ *lemma* homological_complex.hom.comm

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
- \+/\- *lemma* ennreal.one_sub_inv_two

Modified src/data/real/nnreal.lean


Modified src/dynamics/omega_limit.lean


Modified src/measure_theory/haar_measure.lean


Modified src/measure_theory/hausdorff_measure.lean


Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure_add_measure_compl

Modified src/set_theory/cardinal.lean


Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* cauchy_seq_of_dist_le_of_summable
- \+/\- *lemma* cauchy_seq_of_edist_le_of_summable
- \+/\- *lemma* cauchy_seq_of_summable_dist
- \+/\- *lemma* dist_le_tsum_dist_of_tendsto
- \+/\- *lemma* dist_le_tsum_dist_of_tendsto₀
- \+/\- *lemma* dist_le_tsum_of_dist_le_of_tendsto
- \+/\- *lemma* dist_le_tsum_of_dist_le_of_tendsto₀

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
- \+ *lemma* ennreal.tendsto_nat_tsum

Modified src/topology/locally_constant/basic.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/hausdorff_distance.lean
- \+/\- *def* emetric.Hausdorff_edist
- \+/\- *lemma* emetric.Hausdorff_edist_def
- \- *lemma* emetric.mem_iff_ind_edist_zero_of_closed
- \+ *lemma* emetric.mem_iff_inf_edist_zero_of_closed

Modified src/topology/metric_space/kuratowski.lean


Modified src/topology/paracompact.lean


Modified src/topology/separation.lean


Modified src/topology/sequences.lean


Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean
- \- *lemma* compact_diff
- \- *lemma* compact_empty
- \- *lemma* compact_iff_compact_space
- \- *lemma* compact_iff_compact_univ
- \- *lemma* compact_iff_finite_subcover
- \- *theorem* compact_iff_finite_subfamily_closed
- \- *lemma* compact_iff_ultrafilter_le_nhds
- \- *lemma* compact_of_finite_subcover
- \- *theorem* compact_of_finite_subfamily_closed
- \- *lemma* compact_pi_infinite
- \- *lemma* compact_range
- \- *lemma* compact_singleton
- \- *lemma* compact_univ_pi
- \- *lemma* embedding.compact_iff_compact_image
- \+ *lemma* embedding.is_compact_iff_is_compact_image
- \- *lemma* is_closed.compact
- \+ *lemma* is_closed.is_compact
- \- *theorem* is_closed_proj_of_compact
- \+ *theorem* is_closed_proj_of_is_compact
- \+ *lemma* is_compact.diff
- \+ *lemma* is_compact_empty
- \+ *lemma* is_compact_iff_compact_space
- \+ *lemma* is_compact_iff_finite_subcover
- \+ *theorem* is_compact_iff_finite_subfamily_closed
- \+ *lemma* is_compact_iff_is_compact_univ
- \+ *lemma* is_compact_iff_ultrafilter_le_nhds
- \+ *lemma* is_compact_of_finite_subcover
- \+ *theorem* is_compact_of_finite_subfamily_closed
- \+ *lemma* is_compact_pi_infinite
- \+ *lemma* is_compact_range
- \+ *lemma* is_compact_singleton
- \+ *lemma* is_compact_univ_pi

Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/compact_separated.lean




## [2021-05-20 02:00:37](https://github.com/leanprover-community/mathlib/commit/1016a14)
refactor(linear_algebra/finite_dimensional): generalize finite_dimensional.iff_fg to division rings ([#7644](https://github.com/leanprover-community/mathlib/pull/7644))
Replace `finite_dimensional.iff_fg` (working over a field) with `is_noetherian.iff_fg` (working over a division ring). Also, use the `module.finite` predicate.
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/field_theory/finite/polynomial.lean


Added src/field_theory/finiteness.lean
- \+ *lemma* is_noetherian.coe_finset_basis_index
- \+ *lemma* is_noetherian.dim_lt_omega
- \+ *lemma* is_noetherian.finite_basis_index
- \+ *lemma* is_noetherian.iff_dim_lt_omega
- \+ *lemma* is_noetherian.iff_fg
- \+ *lemma* is_noetherian.range_finset_basis

Modified src/field_theory/fixed.lean


Modified src/field_theory/splitting_field.lean


Modified src/field_theory/tower.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finite_dimensional.lean
- \- *lemma* finite_dimensional.coe_finset_basis_index
- \- *lemma* finite_dimensional.dim_lt_omega
- \- *lemma* finite_dimensional.finite_basis_index
- \- *lemma* finite_dimensional.finite_dimensional_iff_dim_lt_omega
- \- *lemma* finite_dimensional.iff_fg
- \- *lemma* finite_dimensional.range_finset_basis

Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/ring_theory/finiteness.lean
- \+/\- *lemma* module.finite_def

Modified src/ring_theory/noetherian.lean
- \+/\- *lemma* finite_of_linear_independent



## [2021-05-20 02:00:36](https://github.com/leanprover-community/mathlib/commit/641cece)
feat(algebra/homology): the homotopy category ([#7484](https://github.com/leanprover-community/mathlib/pull/7484))
#### Estimated changes
Added src/algebra/homology/homotopy_category.lean
- \+ *def* category_theory.functor.map_homotopy_category
- \+ *def* category_theory.nat_trans.map_homotopy_category
- \+ *lemma* category_theory.nat_trans.map_homotopy_category_comp
- \+ *lemma* category_theory.nat_trans.map_homotopy_category_id
- \+ *def* homotopic
- \+ *lemma* homotopy_category.eq_of_homotopy
- \+ *def* homotopy_category.homology_factors
- \+ *lemma* homotopy_category.homology_factors_hom_app
- \+ *lemma* homotopy_category.homology_factors_inv_app
- \+ *def* homotopy_category.homology_functor
- \+ *lemma* homotopy_category.homology_functor_map_factors
- \+ *def* homotopy_category.homotopy_equiv_of_iso
- \+ *def* homotopy_category.homotopy_of_eq
- \+ *def* homotopy_category.homotopy_out_map
- \+ *def* homotopy_category.iso_of_homotopy_equiv
- \+ *def* homotopy_category.quotient
- \+ *lemma* homotopy_category.quotient_map_out
- \+ *lemma* homotopy_category.quotient_map_out_comp_out
- \+ *lemma* homotopy_category.quotient_obj_as
- \+ *def* homotopy_category



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
- \+/\- *lemma* polynomial.coeff_smul
- \+/\- *lemma* polynomial.support_smul



## [2021-05-19 15:48:58](https://github.com/leanprover-community/mathlib/commit/599712f)
feat(data/int/parity, data/nat/parity): add some lemmas ([#7624](https://github.com/leanprover-community/mathlib/pull/7624))
#### Estimated changes
Modified src/data/int/parity.lean
- \+/\- *theorem* int.even_coe_nat
- \+ *theorem* int.even_pow'
- \+/\- *theorem* int.even_pow
- \+ *theorem* int.nat_abs_even
- \+ *theorem* int.nat_abs_odd
- \+ *theorem* int.odd_coe_nat

Modified src/data/nat/parity.lean
- \+ *theorem* nat.even_pow'
- \+/\- *theorem* nat.even_pow



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
- \+ *lemma* is_closed.inter
- \+ *lemma* is_closed.not
- \+ *lemma* is_closed.union
- \- *lemma* is_closed_inter
- \- *lemma* is_closed_union
- \+ *lemma* is_open.and
- \+ *lemma* is_open.inter
- \+ *lemma* is_open.sdiff
- \+ *lemma* is_open.union
- \- *lemma* is_open_and
- \- *lemma* is_open_diff
- \- *lemma* is_open_inter
- \- *lemma* is_open_neg
- \- *lemma* is_open_union

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
- \+ *theorem* Scott.is_open.inter
- \- *theorem* Scott.is_open_inter

Modified src/topology/opens.lean


Modified src/topology/separation.lean


Modified src/topology/shrinking_lemma.lean


Modified src/topology/subset_properties.lean
- \+ *theorem* is_clopen.compl
- \+ *theorem* is_clopen.diff
- \+ *theorem* is_clopen.inter
- \+ *theorem* is_clopen.union
- \- *theorem* is_clopen_compl
- \- *theorem* is_clopen_diff
- \- *theorem* is_clopen_inter
- \- *theorem* is_clopen_union

Modified src/topology/topological_fiber_bundle.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/compact_separated.lean




## [2021-05-19 09:57:34](https://github.com/leanprover-community/mathlib/commit/c7a5197)
feat(data/polynomial/degree/definitions): `polynomial.degree_C_mul_X_le` ([#7659](https://github.com/leanprover-community/mathlib/pull/7659))
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* polynomial.degree_C_mul_X_le



## [2021-05-19 09:57:33](https://github.com/leanprover-community/mathlib/commit/040ebea)
fix(analysis/normed_space/normed_group_quotient): put lemmas inside namespace  ([#7653](https://github.com/leanprover-community/mathlib/pull/7653))
#### Estimated changes
Modified src/analysis/normed_space/normed_group_quotient.lean
- \- *lemma* add_subgroup.is_quotient.norm_le
- \- *lemma* add_subgroup.is_quotient.norm_lift
- \- *lemma* add_subgroup.is_quotient_quotient
- \- *def* add_subgroup.lift
- \- *lemma* add_subgroup.lift_mk
- \- *lemma* add_subgroup.lift_unique
- \+ *lemma* normed_group_hom.is_quotient.norm_le
- \+ *lemma* normed_group_hom.is_quotient.norm_lift
- \+ *lemma* normed_group_hom.is_quotient_quotient
- \+ *def* normed_group_hom.lift
- \+ *lemma* normed_group_hom.lift_mk
- \+ *lemma* normed_group_hom.lift_unique



## [2021-05-19 08:44:51](https://github.com/leanprover-community/mathlib/commit/c1e9f94)
docs(field_theory/polynomial_galois_group): improve existing docs ([#7586](https://github.com/leanprover-community/mathlib/pull/7586))
#### Estimated changes
Modified src/field_theory/polynomial_galois_group.lean
- \+ *lemma* polynomial.gal.card_complex_roots_eq_card_real_add_card_not_gal_inv
- \- *lemma* polynomial.gal.gal_action_hom_bijective_of_prime_degree_aux



## [2021-05-19 02:36:44](https://github.com/leanprover-community/mathlib/commit/1d4990e)
chore(scripts): update nolints.txt ([#7658](https://github.com/leanprover-community/mathlib/pull/7658))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-05-19 02:36:43](https://github.com/leanprover-community/mathlib/commit/918dcc0)
chore(algebra/homology): further dualization ([#7657](https://github.com/leanprover-community/mathlib/pull/7657))
#### Estimated changes
Modified src/algebra/homology/augment.lean
- \+ *lemma* chain_complex.chain_complex_d_succ_succ_zero
- \- *lemma* chain_complex.cochain_complex_d_succ_succ_zero
- \+ *def* cochain_complex.augment
- \+ *lemma* cochain_complex.augment_X_succ
- \+ *lemma* cochain_complex.augment_X_zero
- \+ *lemma* cochain_complex.augment_d_succ_succ
- \+ *lemma* cochain_complex.augment_d_zero_one
- \+ *def* cochain_complex.augment_truncate
- \+ *lemma* cochain_complex.augment_truncate_hom_f_succ
- \+ *lemma* cochain_complex.augment_truncate_hom_f_zero
- \+ *lemma* cochain_complex.augment_truncate_inv_f_succ
- \+ *lemma* cochain_complex.augment_truncate_inv_f_zero
- \+ *lemma* cochain_complex.cochain_complex_d_succ_succ_zero
- \+ *def* cochain_complex.from_single₀_as_complex
- \+ *def* cochain_complex.to_truncate
- \+ *def* cochain_complex.truncate
- \+ *def* cochain_complex.truncate_augment
- \+ *lemma* cochain_complex.truncate_augment_hom_f
- \+ *lemma* cochain_complex.truncate_augment_inv_f

Modified src/algebra/homology/homological_complex.lean
- \+ *def* cochain_complex.mk'
- \+ *lemma* cochain_complex.mk'_X_0
- \+ *lemma* cochain_complex.mk'_X_1
- \+ *lemma* cochain_complex.mk'_d_1_0
- \+ *def* cochain_complex.mk
- \+ *lemma* cochain_complex.mk_X_0
- \+ *lemma* cochain_complex.mk_X_1
- \+ *lemma* cochain_complex.mk_X_2
- \+ *def* cochain_complex.mk_aux
- \+ *lemma* cochain_complex.mk_d_1_0
- \+ *lemma* cochain_complex.mk_d_2_0
- \+ *def* cochain_complex.mk_hom
- \+ *def* cochain_complex.mk_hom_aux
- \+ *lemma* cochain_complex.mk_hom_f_0
- \+ *lemma* cochain_complex.mk_hom_f_1
- \+ *lemma* cochain_complex.mk_hom_f_succ_succ
- \+ *def* cochain_complex.mk_struct.flat

Modified src/algebra/homology/single.lean
- \+ *def* cochain_complex.from_single₀_equiv
- \+ *def* cochain_complex.homology_functor_0_single₀
- \+ *def* cochain_complex.homology_functor_succ_single₀
- \+ *def* cochain_complex.single₀
- \+ *def* cochain_complex.single₀_iso_single
- \+ *lemma* cochain_complex.single₀_map_f_0
- \+ *lemma* cochain_complex.single₀_map_f_succ
- \+ *lemma* cochain_complex.single₀_obj_X_0
- \+ *lemma* cochain_complex.single₀_obj_X_d
- \+ *lemma* cochain_complex.single₀_obj_X_d_from
- \+ *lemma* cochain_complex.single₀_obj_X_d_to
- \+ *lemma* cochain_complex.single₀_obj_X_succ



## [2021-05-19 02:36:42](https://github.com/leanprover-community/mathlib/commit/aee918b)
feat(algebraic_topology/simplicial_object): Some API for converting between simplicial and cosimplicial ([#7656](https://github.com/leanprover-community/mathlib/pull/7656))
This adds some code which is helpful to convert back and forth between simplicial and cosimplicial object.
For augmented objects, this doesn't follow directly from the existing API in `category_theory/opposite`.
#### Estimated changes
Modified src/algebraic_topology/simplicial_object.lean
- \+ *def* category_theory.cosimplicial_object.augmented.left_op
- \+ *def* category_theory.cosimplicial_object.augmented.left_op_right_op_iso
- \+ *def* category_theory.cosimplicial_to_simplicial_augmented
- \+ *def* category_theory.simplicial_cosimplicial_augmented_equiv
- \+ *def* category_theory.simplicial_cosimplicial_equiv
- \+ *def* category_theory.simplicial_object.augmented.right_op
- \+ *def* category_theory.simplicial_object.augmented.right_op_left_op_iso
- \+ *def* category_theory.simplicial_to_cosimplicial_augmented



## [2021-05-19 01:16:47](https://github.com/leanprover-community/mathlib/commit/24d2713)
feat(algebraic_topology/simplicial_object): Whiskering of simplicial objects. ([#7651](https://github.com/leanprover-community/mathlib/pull/7651))
This adds whiskering constructions for (truncated, augmented) (co)simplicial objects.
#### Estimated changes
Modified src/algebraic_topology/simplicial_object.lean
- \+ *def* category_theory.cosimplicial_object.augmented.whiskering
- \+ *def* category_theory.cosimplicial_object.augmented.whiskering_obj
- \+ *def* category_theory.cosimplicial_object.truncated.whiskering
- \+ *def* category_theory.cosimplicial_object.whiskering
- \+ *def* category_theory.simplicial_object.augmented.whiskering
- \+ *def* category_theory.simplicial_object.augmented.whiskering_obj
- \+ *def* category_theory.simplicial_object.truncated.whiskering
- \+ *def* category_theory.simplicial_object.whiskering



## [2021-05-18 22:27:07](https://github.com/leanprover-community/mathlib/commit/0bcfff9)
feat(linear_algebra/basis) remove several [nontrivial R] ([#7642](https://github.com/leanprover-community/mathlib/pull/7642))
We remove some unnecessary `nontrivial R`.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+/\- *def* basis.reindex_range
- \+/\- *lemma* basis.reindex_range_apply
- \+/\- *lemma* basis.reindex_range_repr'
- \+/\- *lemma* basis.reindex_range_repr
- \+/\- *lemma* basis.reindex_range_repr_self
- \+/\- *lemma* basis.reindex_range_self

Modified src/linear_algebra/finsupp.lean
- \+ *def* module.subsingleton_equiv

Modified src/linear_algebra/matrix/to_lin.lean
- \+/\- *theorem* linear_map.to_matrix_alg_equiv_reindex_range
- \+/\- *theorem* linear_map.to_matrix_reindex_range



## [2021-05-18 16:02:45](https://github.com/leanprover-community/mathlib/commit/a51d1e0)
feat(algebra/homology/homological_complex): Dualizes some constructions ([#7643](https://github.com/leanprover-community/mathlib/pull/7643))
This PR adds `cochain_complex.of` and `cochain_complex.of_hom`. 
Still not done: `cochain_complex.mk`.
#### Estimated changes
Modified src/algebra/homology/homological_complex.lean
- \+ *def* cochain_complex.of
- \+ *lemma* cochain_complex.of_X
- \+ *lemma* cochain_complex.of_d
- \+ *lemma* cochain_complex.of_d_ne
- \+ *def* cochain_complex.of_hom



## [2021-05-18 16:02:44](https://github.com/leanprover-community/mathlib/commit/e275604)
chore(data/set/basic): add `set.compl_eq_compl` ([#7641](https://github.com/leanprover-community/mathlib/pull/7641))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.compl_eq_compl



## [2021-05-18 10:47:24](https://github.com/leanprover-community/mathlib/commit/c2114d4)
refactor(linear_algebra/dimension): generalize definition of `module.rank` ([#7634](https://github.com/leanprover-community/mathlib/pull/7634))
The main change is to generalize the definition of `module.rank`. It used to be the infimum over cardinalities of bases, and is now the supremum over cardinalities of linearly independent sets.
I have not attempted to systematically generalize  theorems about the rank; there is lots more work to be done. For now I've just made a few easy generalizations (either replacing `field` with `division_ring`, or `division_ring` with `ring`+`nontrivial`).
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+/\- *lemma* basis.reindex_range_apply

Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/linear_independent.lean
- \+/\- *lemma* linear_independent_singleton
- \+/\- *lemma* linear_independent_unique_iff

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
- \+ *lemma* opposite.op_smul_eq_mul



## [2021-05-18 04:50:02](https://github.com/leanprover-community/mathlib/commit/1a2781a)
feat(analysis/normed_space): the category of seminormed groups ([#7617](https://github.com/leanprover-community/mathlib/pull/7617))
From LTE, along with adding `SemiNormedGroup₁`, the subcategory of norm non-increasing maps.
#### Estimated changes
Added src/analysis/normed_space/SemiNormedGroup.lean
- \+ *lemma* SemiNormedGroup.coe_id
- \+ *lemma* SemiNormedGroup.coe_of
- \+ *def* SemiNormedGroup.of
- \+ *def* SemiNormedGroup
- \+ *lemma* SemiNormedGroup₁.coe_comp
- \+ *lemma* SemiNormedGroup₁.coe_id
- \+ *lemma* SemiNormedGroup₁.coe_of
- \+ *lemma* SemiNormedGroup₁.hom_ext
- \+ *lemma* SemiNormedGroup₁.iso_isometry
- \+ *def* SemiNormedGroup₁.mk_hom
- \+ *lemma* SemiNormedGroup₁.mk_hom_apply
- \+ *def* SemiNormedGroup₁.mk_iso
- \+ *def* SemiNormedGroup₁.of
- \+ *lemma* SemiNormedGroup₁.zero_apply
- \+ *def* SemiNormedGroup₁

Modified src/analysis/normed_space/normed_group_hom.lean
- \+ *lemma* normed_group_hom.norm_noninc.zero



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
- \- *lemma* finprod_of_empty
- \+ *lemma* finprod_of_is_empty

Modified src/algebra/homology/homological_complex.lean


Modified src/analysis/calculus/inverse.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/combinatorics/hall.lean


Modified src/data/equiv/basic.lean
- \+ *def* equiv.arrow_punit_of_is_empty
- \- *def* equiv.empty_of_not_nonempty
- \+/\- *def* equiv.empty_sum
- \+/\- *lemma* equiv.empty_sum_apply_inr
- \+/\- *def* equiv.equiv_empty
- \+ *def* equiv.equiv_empty_equiv
- \+/\- *def* equiv.fun_unique
- \+ *lemma* equiv.is_empty_congr
- \- *def* equiv.pempty_of_not_nonempty
- \- *def* equiv.pempty_sum
- \- *lemma* equiv.pempty_sum_apply_inr
- \+ *lemma* equiv.subsingleton_congr
- \- *lemma* equiv.subsingleton_iff
- \+/\- *def* equiv.sum_empty
- \+/\- *lemma* equiv.sum_empty_apply_inl
- \- *def* equiv.sum_pempty
- \- *lemma* equiv.sum_pempty_apply_inl
- \+/\- *def* equiv.{u'

Modified src/data/equiv/denumerable.lean


Modified src/data/equiv/fin.lean
- \+/\- *def* fin_one_equiv

Modified src/data/fin.lean


Modified src/data/fintype/basic.lean
- \+ *def* fintype.card_eq_zero_equiv_equiv_empty
- \- *def* fintype.card_eq_zero_equiv_equiv_pempty
- \+/\- *lemma* fintype.card_eq_zero_iff
- \+ *lemma* is_empty_fintype
- \+ *lemma* not_fintype
- \+/\- *lemma* not_nonempty_fintype

Modified src/data/option/basic.lean
- \+/\- *lemma* option.choice_eq_none

Modified src/data/polynomial/ring_division.lean


Modified src/data/set/basic.lean


Modified src/data/zmod/basic.lean


Modified src/field_theory/polynomial_galois_group.lean


Modified src/group_theory/specific_groups/cyclic.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/matrix/block.lean


Added src/logic/is_empty.lean
- \+ *lemma* is_empty.exists_iff
- \+ *lemma* is_empty.forall_iff
- \+ *def* is_empty_elim
- \+ *lemma* is_empty_iff
- \+ *lemma* is_empty_or_nonempty
- \+ *lemma* not_is_empty_iff
- \+ *lemma* not_is_empty_of_nonempty
- \+ *lemma* not_nonempty_iff

Modified src/logic/unique.lean
- \- *def* pi.unique_of_empty

Modified src/ring_theory/jacobson.lean


Modified src/set_theory/cardinal.lean
- \- *lemma* cardinal.eq_one_iff_subsingleton_and_nonempty
- \+ *lemma* cardinal.eq_one_iff_unique
- \+ *lemma* cardinal.eq_zero_iff_is_empty

Modified src/set_theory/ordinal.lean


Modified src/set_theory/pgame.lean




## [2021-05-18 04:49:59](https://github.com/leanprover-community/mathlib/commit/1b864c0)
feat(analysis/normed_group): quotients ([#7603](https://github.com/leanprover-community/mathlib/pull/7603))
From LTE.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* mem_ball_0_iff

Added src/analysis/normed_space/normed_group_quotient.lean
- \+ *lemma* add_subgroup.is_quotient.norm_le
- \+ *lemma* add_subgroup.is_quotient.norm_lift
- \+ *lemma* add_subgroup.is_quotient_quotient
- \+ *lemma* add_subgroup.ker_normed_mk
- \+ *def* add_subgroup.lift
- \+ *lemma* add_subgroup.lift_mk
- \+ *lemma* add_subgroup.lift_unique
- \+ *lemma* add_subgroup.norm_normed_mk
- \+ *lemma* add_subgroup.norm_normed_mk_le
- \+ *lemma* add_subgroup.norm_trivial_quotient_mk
- \+ *lemma* add_subgroup.normed_mk.apply
- \+ *def* add_subgroup.normed_mk
- \+ *lemma* add_subgroup.surjective_normed_mk
- \+ *lemma* bdd_below_image_norm
- \+ *lemma* image_norm_nonempty
- \+ *lemma* norm_mk_lt'
- \+ *lemma* norm_mk_lt
- \+ *lemma* norm_mk_nonneg
- \+ *lemma* norm_mk_zero
- \+ *lemma* norm_zero_eq_zero
- \+ *lemma* quotient_nhd_basis
- \+ *lemma* quotient_norm_add_le
- \+ *lemma* quotient_norm_eq_zero_iff
- \+ *lemma* quotient_norm_mk_eq
- \+ *lemma* quotient_norm_mk_le
- \+ *lemma* quotient_norm_neg
- \+ *lemma* quotient_norm_nonneg
- \+ *lemma* quotient_norm_sub_rev



## [2021-05-18 02:58:27](https://github.com/leanprover-community/mathlib/commit/f900513)
feat(linear_algebra/matrix): slightly generalize `smul_left_mul_matrix` ([#7632](https://github.com/leanprover-community/mathlib/pull/7632))
Two minor changes that make `smul_left_mul_matrix` slightly easier to apply:
 * the bases `b` and `c` can now be indexed by different types
 * replace `(i, k)` on the LHS with `ik.1 ik.2` on the RHS (so you don't have to introduce the constructor with `rw ← prod.mk.eta` somewhere deep in your expression)
#### Estimated changes
Modified src/linear_algebra/matrix/to_lin.lean
- \+/\- *lemma* algebra.smul_left_mul_matrix



## [2021-05-17 23:05:07](https://github.com/leanprover-community/mathlib/commit/b8a6995)
feat(data/polynomial): the `d-1`th coefficient of `polynomial.map` ([#7639](https://github.com/leanprover-community/mathlib/pull/7639))
We prove `polynomial.next_coeff_map` just like `polynomial.leading_coeff_map'`.
#### Estimated changes
Modified src/data/polynomial/degree/lemmas.lean
- \+ *lemma* polynomial.next_coeff_map



## [2021-05-17 23:05:06](https://github.com/leanprover-community/mathlib/commit/ccf5188)
feat(ring_theory/power_basis): the dimension of a power basis is positive ([#7638](https://github.com/leanprover-community/mathlib/pull/7638))
We already have `pb.dim_ne_zero : pb.dim ≠ 0` (assuming nontriviality), but it's also useful to also have it in the form `0 < pb.dim`.
#### Estimated changes
Modified src/ring_theory/power_basis.lean
- \+ *lemma* power_basis.dim_pos



## [2021-05-17 18:10:36](https://github.com/leanprover-community/mathlib/commit/4ab0e35)
feat(data/multiset): the product of inverses is the inverse of the product ([#7637](https://github.com/leanprover-community/mathlib/pull/7637))
Entirely analogous to `prod_map_mul` defined above.
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.prod_map_inv



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
- \+ *lemma* add_monoid_hom.map_nat_module_smul

Modified src/algebra/module/linear_map.lean
- \+ *def* add_monoid_hom.to_nat_linear_map

Modified src/linear_algebra/basic.lean
- \+ *def* add_monoid_hom_lequiv_int
- \+ *def* add_monoid_hom_lequiv_nat



## [2021-05-17 12:38:49](https://github.com/leanprover-community/mathlib/commit/d201a18)
refactor(algebra/homology/homotopy): avoid needing has_zero_object ([#7621](https://github.com/leanprover-community/mathlib/pull/7621))
A refactor of the definition of `homotopy`, so we don't need `has_zero_object`.
#### Estimated changes
Modified src/algebra/homology/homotopy.lean
- \+ *def* d_next
- \+ *lemma* d_next_comp_left
- \+ *lemma* d_next_comp_right
- \+ *lemma* d_next_eq
- \+ *lemma* d_next_eq_d_from_from_next
- \- *def* from_next'
- \- *lemma* from_next'_add
- \- *lemma* from_next'_comp_left
- \- *lemma* from_next'_comp_right
- \- *lemma* from_next'_eq
- \- *lemma* from_next'_neg
- \- *lemma* from_next'_zero
- \+ *def* from_next
- \- *lemma* homotopy.comm
- \+ *lemma* homotopy.d_next_succ_chain_complex
- \+ *lemma* homotopy.d_next_zero_chain_complex
- \- *lemma* homotopy.from_next'_succ_chain_complex
- \- *lemma* homotopy.from_next'_zero_chain_complex
- \- *def* homotopy.from_next
- \+ *lemma* homotopy.prev_d_chain_complex
- \- *lemma* homotopy.to_prev'_chain_complex
- \- *def* homotopy.to_prev
- \+ *def* prev_d
- \+ *lemma* prev_d_comp_left
- \+ *lemma* prev_d_eq
- \+ *lemma* prev_d_eq_to_prev_d_to
- \- *def* to_prev'
- \- *lemma* to_prev'_add
- \- *lemma* to_prev'_comp_left
- \- *lemma* to_prev'_eq
- \- *lemma* to_prev'_neg
- \- *lemma* to_prev'_zero
- \+ *def* to_prev



## [2021-05-17 12:38:49](https://github.com/leanprover-community/mathlib/commit/07fb3d7)
refactor(data/finsupp/antidiagonal): Make antidiagonal a finset ([#7595](https://github.com/leanprover-community/mathlib/pull/7595))
Pursuant to discussion [here](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/antidiagonals.20having.20multiplicity) 
Refactoring so that `finsupp.antidiagonal` and `multiset.antidiagonal` are finsets.
~~Still TO DO: `multiset.antidiagonal`~~
#### Estimated changes
Modified src/data/finsupp/antidiagonal.lean
- \+ *def* finsupp.antidiagonal'
- \+/\- *def* finsupp.antidiagonal
- \+ *lemma* finsupp.antidiagonal_filter_fst_eq
- \+ *lemma* finsupp.antidiagonal_filter_snd_eq
- \- *lemma* finsupp.antidiagonal_support_filter_fst_eq
- \- *lemma* finsupp.antidiagonal_support_filter_snd_eq
- \+/\- *lemma* finsupp.antidiagonal_zero
- \+ *lemma* finsupp.mem_antidiagonal
- \- *lemma* finsupp.mem_antidiagonal_support
- \- *lemma* finsupp.prod_antidiagonal_support_swap
- \+ *lemma* finsupp.prod_antidiagonal_swap
- \+ *lemma* finsupp.swap_mem_antidiagonal
- \- *lemma* finsupp.swap_mem_antidiagonal_support

Modified src/data/mv_polynomial/basic.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/ring_theory/polynomial/homogeneous.lean


Modified src/ring_theory/power_series/basic.lean




## [2021-05-17 08:05:30](https://github.com/leanprover-community/mathlib/commit/8394e59)
feat(data/finset/basic): perm_of_nodup_nodup_to_finset_eq ([#7588](https://github.com/leanprover-community/mathlib/pull/7588))
Also `finset.exists_list_nodup_eq`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.exists_list_nodup_eq
- \+ *lemma* list.perm_of_nodup_nodup_to_finset_eq
- \+ *lemma* multiset.nodup.to_finset_inj



## [2021-05-17 06:01:44](https://github.com/leanprover-community/mathlib/commit/739d93c)
feat(algebra/lie/weights): the zero root subalgebra is self-normalizing ([#7622](https://github.com/leanprover-community/mathlib/pull/7622))
#### Estimated changes
Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* lie_subalgebra.mem_mk_iff

Modified src/algebra/lie/weights.lean
- \+ *lemma* lie_algebra.mem_zero_root_subalgebra
- \+ *lemma* lie_algebra.zero_root_subalgebra_is_cartan_of_eq
- \+ *lemma* lie_algebra.zero_root_subalgebra_normalizer_eq_self
- \+ *lemma* lie_module.coe_weight_space'
- \+ *def* lie_module.weight_space'



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
- \- *lemma* game.quot_add
- \- *lemma* game.quot_neg
- \- *lemma* game.quot_sub
- \+/\- *theorem* pgame.left_distrib_equiv
- \- *lemma* pgame.left_distrib_equiv_aux'
- \- *lemma* pgame.left_distrib_equiv_aux
- \+ *theorem* pgame.mul_assoc_equiv
- \- *def* pgame.mul_comm_relabelling
- \+ *theorem* pgame.mul_one_equiv
- \+ *theorem* pgame.one_mul_equiv
- \+ *lemma* pgame.quot_add
- \+ *theorem* pgame.quot_eq_of_mk_quot_eq
- \+ *theorem* pgame.quot_left_distrib
- \+ *theorem* pgame.quot_left_distrib_sub
- \+ *theorem* pgame.quot_mul_assoc
- \+ *theorem* pgame.quot_mul_comm
- \+ *theorem* pgame.quot_mul_neg
- \+ *theorem* pgame.quot_mul_one
- \+ *theorem* pgame.quot_mul_zero
- \+ *lemma* pgame.quot_neg
- \+ *theorem* pgame.quot_neg_mul
- \+ *theorem* pgame.quot_one_mul
- \+ *theorem* pgame.quot_right_distrib
- \+ *theorem* pgame.quot_right_distrib_sub
- \+ *lemma* pgame.quot_sub
- \+ *theorem* pgame.quot_zero_mul



## [2021-05-16 18:58:53](https://github.com/leanprover-community/mathlib/commit/aedd12d)
refactor(measure_theory/haar_measure): move general material to content.lean, make content a structure  ([#7615](https://github.com/leanprover-community/mathlib/pull/7615))
Several facts that are proved only for the Haar measure (including for instance regularity) are true for any measure constructed from a content. We move these facts to the `content.lean` file (and make `content` a structure for easier management). Also, move the notion of regular measure to its own file, and make it a class.
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \- *lemma* measure_theory.measure.regular.exists_compact_not_null
- \- *lemma* measure_theory.measure.regular.inner_regular_eq
- \- *lemma* measure_theory.measure.regular.outer_regular_eq

Modified src/measure_theory/content.lean
- \+ *lemma* measure_theory.content.apply_eq_coe_to_fun
- \+ *lemma* measure_theory.content.borel_le_caratheodory
- \+ *lemma* measure_theory.content.empty
- \+ *def* measure_theory.content.inner_content
- \+ *lemma* measure_theory.content.inner_content_Sup_nat
- \+ *lemma* measure_theory.content.inner_content_Union_nat
- \+ *lemma* measure_theory.content.inner_content_comap
- \+ *lemma* measure_theory.content.inner_content_empty
- \+ *lemma* measure_theory.content.inner_content_exists_compact
- \+ *lemma* measure_theory.content.inner_content_le
- \+ *lemma* measure_theory.content.inner_content_mono'
- \+ *lemma* measure_theory.content.inner_content_mono
- \+ *lemma* measure_theory.content.inner_content_of_is_compact
- \+ *lemma* measure_theory.content.inner_content_pos_of_is_mul_left_invariant
- \+ *lemma* measure_theory.content.is_mul_left_invariant_inner_content
- \+ *lemma* measure_theory.content.is_mul_left_invariant_outer_measure
- \+ *lemma* measure_theory.content.le_inner_content
- \+ *lemma* measure_theory.content.le_outer_measure_compacts
- \+ *lemma* measure_theory.content.lt_top
- \+ *def* measure_theory.content.measure
- \+ *lemma* measure_theory.content.measure_apply
- \+ *lemma* measure_theory.content.mono
- \+ *lemma* measure_theory.content.outer_measure_caratheodory
- \+ *lemma* measure_theory.content.outer_measure_eq_infi
- \+ *lemma* measure_theory.content.outer_measure_exists_compact
- \+ *lemma* measure_theory.content.outer_measure_exists_open
- \+ *lemma* measure_theory.content.outer_measure_interior_compacts
- \+ *lemma* measure_theory.content.outer_measure_le
- \+ *lemma* measure_theory.content.outer_measure_lt_top_of_is_compact
- \+ *lemma* measure_theory.content.outer_measure_of_is_open
- \+ *lemma* measure_theory.content.outer_measure_opens
- \+ *lemma* measure_theory.content.outer_measure_pos_of_is_mul_left_invariant
- \+ *lemma* measure_theory.content.outer_measure_preimage
- \+ *lemma* measure_theory.content.sup_disjoint
- \+ *lemma* measure_theory.content.sup_le
- \- *def* measure_theory.inner_content
- \- *lemma* measure_theory.inner_content_Sup_nat
- \- *lemma* measure_theory.inner_content_Union_nat
- \- *lemma* measure_theory.inner_content_comap
- \- *lemma* measure_theory.inner_content_empty
- \- *lemma* measure_theory.inner_content_exists_compact
- \- *lemma* measure_theory.inner_content_le
- \- *lemma* measure_theory.inner_content_mono'
- \- *lemma* measure_theory.inner_content_mono
- \- *lemma* measure_theory.inner_content_of_is_compact
- \- *lemma* measure_theory.inner_content_pos_of_is_mul_left_invariant
- \- *lemma* measure_theory.is_mul_left_invariant_inner_content
- \- *lemma* measure_theory.le_inner_content
- \- *lemma* measure_theory.outer_measure.is_mul_left_invariant_of_content
- \- *lemma* measure_theory.outer_measure.le_of_content_compacts
- \- *def* measure_theory.outer_measure.of_content
- \- *lemma* measure_theory.outer_measure.of_content_caratheodory
- \- *lemma* measure_theory.outer_measure.of_content_eq_infi
- \- *lemma* measure_theory.outer_measure.of_content_exists_compact
- \- *lemma* measure_theory.outer_measure.of_content_exists_open
- \- *lemma* measure_theory.outer_measure.of_content_interior_compacts
- \- *lemma* measure_theory.outer_measure.of_content_le
- \- *lemma* measure_theory.outer_measure.of_content_opens
- \- *lemma* measure_theory.outer_measure.of_content_pos_of_is_mul_left_invariant
- \- *lemma* measure_theory.outer_measure.of_content_preimage

Modified src/measure_theory/group.lean
- \+/\- *lemma* measure_theory.is_mul_left_invariant.measure_ne_zero_iff_nonempty
- \+/\- *lemma* measure_theory.is_mul_left_invariant.null_iff
- \+/\- *lemma* measure_theory.is_mul_left_invariant.null_iff_empty
- \+/\- *lemma* measure_theory.lintegral_eq_zero_of_is_mul_left_invariant
- \- *lemma* measure_theory.measure.regular.inv

Modified src/measure_theory/haar_measure.lean
- \- *lemma* measure_theory.measure.echaar_le_haar_outer_measure
- \- *def* measure_theory.measure.haar.echaar
- \- *lemma* measure_theory.measure.haar.echaar_mono
- \- *lemma* measure_theory.measure.haar.echaar_self
- \- *lemma* measure_theory.measure.haar.echaar_sup_le
- \+ *def* measure_theory.measure.haar.haar_content
- \+ *lemma* measure_theory.measure.haar.haar_content_apply
- \+ *lemma* measure_theory.measure.haar.haar_content_outer_measure_self_pos
- \+ *lemma* measure_theory.measure.haar.haar_content_self
- \- *lemma* measure_theory.measure.haar.is_left_invariant_echaar
- \+ *lemma* measure_theory.measure.haar.is_left_invariant_haar_content
- \- *lemma* measure_theory.measure.haar_caratheodory_measurable
- \- *def* measure_theory.measure.haar_outer_measure
- \- *lemma* measure_theory.measure.haar_outer_measure_caratheodory
- \- *lemma* measure_theory.measure.haar_outer_measure_eq_infi
- \- *lemma* measure_theory.measure.haar_outer_measure_exists_compact
- \- *lemma* measure_theory.measure.haar_outer_measure_exists_open
- \- *lemma* measure_theory.measure.haar_outer_measure_le_echaar
- \- *lemma* measure_theory.measure.haar_outer_measure_lt_top_of_is_compact
- \- *lemma* measure_theory.measure.haar_outer_measure_of_is_open
- \- *lemma* measure_theory.measure.haar_outer_measure_pos_of_is_open
- \- *lemma* measure_theory.measure.haar_outer_measure_self_pos
- \- *lemma* measure_theory.measure.one_le_haar_outer_measure_self
- \- *lemma* measure_theory.measure.regular_haar_measure

Modified src/measure_theory/prod_group.lean


Added src/measure_theory/regular.lean
- \+ *lemma* measure_theory.measure.regular.exists_compact_not_null
- \+ *lemma* measure_theory.measure.regular.inner_regular_eq
- \+ *lemma* measure_theory.measure.regular.outer_regular_eq



## [2021-05-16 18:58:52](https://github.com/leanprover-community/mathlib/commit/1b098c0)
feat(algebra/ordered_group, algebra/ordered_ring): add some lemmas about abs ([#7612](https://github.com/leanprover-community/mathlib/pull/7612))
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* abs_choice
- \+ *lemma* abs_eq_abs
- \+ *lemma* eq_or_eq_neg_of_abs_eq

Modified src/algebra/ordered_ring.lean
- \+ *lemma* abs_dvd
- \+ *lemma* abs_dvd_abs
- \+ *lemma* abs_dvd_self
- \+ *lemma* dvd_abs
- \+ *lemma* even_abs
- \+ *lemma* self_dvd_abs



## [2021-05-16 18:58:51](https://github.com/leanprover-community/mathlib/commit/b98d840)
feat(category_theory/category): initialize simps ([#7605](https://github.com/leanprover-community/mathlib/pull/7605))
Initialize `@[simps]` so that it works better for `category`. It just makes the names of the generated lemmas shorter.
Add `@[simps]` to product categories.
#### Estimated changes
Modified src/category_theory/category/default.lean


Modified src/category_theory/products/basic.lean
- \- *lemma* category_theory.prod_comp_fst
- \- *lemma* category_theory.prod_comp_snd
- \- *lemma* category_theory.prod_id_fst
- \- *lemma* category_theory.prod_id_snd

Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean




## [2021-05-16 18:58:50](https://github.com/leanprover-community/mathlib/commit/9084a3c)
chore(order/fixed_point): add docstring for Knaster-Tarski theorem ([#7589](https://github.com/leanprover-community/mathlib/pull/7589))
clarify that the def provided constitutes the Knaster-Tarski theorem
#### Estimated changes
Modified src/order/countable_dense_linear_order.lean


Modified src/order/fixed_points.lean
- \+ *lemma* fixed_points.Sup_le_f_of_fixed_points
- \- *theorem* fixed_points.Sup_le_f_of_fixed_points
- \+ *lemma* fixed_points.f_le_Inf_of_fixed_points
- \- *theorem* fixed_points.f_le_Inf_of_fixed_points
- \+ *lemma* fixed_points.f_le_inf_of_fixed_points
- \- *theorem* fixed_points.f_le_inf_of_fixed_points
- \+ *lemma* fixed_points.le_next
- \+/\- *lemma* fixed_points.next_eq
- \- *theorem* fixed_points.next_le
- \+/\- *lemma* fixed_points.prev_eq
- \+ *lemma* fixed_points.prev_le
- \- *theorem* fixed_points.prev_le
- \+ *lemma* fixed_points.sup_le_f_of_fixed_points
- \- *theorem* fixed_points.sup_le_f_of_fixed_points
- \+ *lemma* gfp_comp
- \- *theorem* gfp_comp
- \- *theorem* gfp_eq
- \+ *lemma* gfp_fixed_point
- \+ *lemma* gfp_gfp
- \- *theorem* gfp_gfp
- \- *theorem* gfp_induct
- \+ *lemma* gfp_induction
- \+ *lemma* gfp_le
- \- *theorem* gfp_le
- \+ *lemma* le_gfp
- \- *theorem* le_gfp
- \+ *lemma* le_lfp
- \- *theorem* le_lfp
- \+ *lemma* lfp_comp
- \- *theorem* lfp_comp
- \- *theorem* lfp_eq
- \+ *lemma* lfp_fixed_point
- \- *theorem* lfp_induct
- \+ *lemma* lfp_induction
- \+ *lemma* lfp_le
- \- *theorem* lfp_le
- \+ *lemma* lfp_lfp
- \- *theorem* lfp_lfp
- \+ *lemma* monotone_gfp
- \- *theorem* monotone_gfp
- \+ *lemma* monotone_lfp
- \- *theorem* monotone_lfp

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


Added test/lift.lean




## [2021-05-16 13:18:11](https://github.com/leanprover-community/mathlib/commit/632783d)
feat(algebra/subalgebra): two equal subalgebras are equivalent ([#7590](https://github.com/leanprover-community/mathlib/pull/7590))
This extends `linear_equiv.of_eq` to an `alg_equiv` between two `subalgebra`s.
[Zulip discussion starts around here](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/towers.20of.20algebras/near/238452076)
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *def* subalgebra.equiv_of_eq
- \+ *lemma* subalgebra.equiv_of_eq_rfl
- \+ *lemma* subalgebra.equiv_of_eq_symm
- \+ *lemma* subalgebra.equiv_of_eq_trans



## [2021-05-16 13:18:10](https://github.com/leanprover-community/mathlib/commit/4d909f4)
feat(analysis/calculus/local_extr): A polynomial's roots are bounded by its derivative ([#7571](https://github.com/leanprover-community/mathlib/pull/7571))
An application of Rolle's theorem to polynomials.
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+ *lemma* ring_hom.char_zero
- \+ *lemma* ring_hom.char_zero_iff

Modified src/analysis/calculus/local_extr.lean
- \+ *lemma* polynomial.card_root_set_le_derivative

Modified src/data/finset/sort.lean
- \+ *lemma* finset.card_le_of_interleaved



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
- \+ *def* category_theory.cosimplicial_object.augmented.drop
- \+ *def* category_theory.cosimplicial_object.augmented.point
- \+ *def* category_theory.cosimplicial_object.augmented
- \+ *def* category_theory.cosimplicial_object.eq_to_iso
- \+ *lemma* category_theory.cosimplicial_object.eq_to_iso_refl
- \+ *def* category_theory.cosimplicial_object.sk
- \+ *def* category_theory.cosimplicial_object.truncated
- \+ *def* category_theory.cosimplicial_object.δ
- \+ *lemma* category_theory.cosimplicial_object.δ_comp_δ
- \+ *lemma* category_theory.cosimplicial_object.δ_comp_δ_self
- \+ *lemma* category_theory.cosimplicial_object.δ_comp_σ_of_gt
- \+ *lemma* category_theory.cosimplicial_object.δ_comp_σ_of_le
- \+ *lemma* category_theory.cosimplicial_object.δ_comp_σ_self
- \+ *lemma* category_theory.cosimplicial_object.δ_comp_σ_succ
- \+ *def* category_theory.cosimplicial_object.σ
- \+ *lemma* category_theory.cosimplicial_object.σ_comp_σ
- \+ *def* category_theory.cosimplicial_object
- \+ *def* category_theory.simplicial_object.augmented.drop
- \+ *def* category_theory.simplicial_object.augmented.point



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
- \+ *lemma* reflexive.ne_imp_iff
- \+ *lemma* reflexive.rel_of_ne_imp
- \+ *lemma* reflexive_ne_imp_iff



## [2021-05-15 21:20:55](https://github.com/leanprover-community/mathlib/commit/82ac80f)
feat(data/set/basic): pairwise_on.imp_on ([#7578](https://github.com/leanprover-community/mathlib/pull/7578))
Provide more helper lemmas for transferring `pairwise_on` between different relations. Provide a rephrase of `pairwise_on.mono'` as `pairwise_on.imp`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.pairwise_on.imp
- \+ *lemma* set.pairwise_on.imp_on
- \+ *lemma* set.pairwise_on_of_forall
- \+ *theorem* set.pairwise_on_top



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
- \+ *theorem* decidable.eq_or_ne
- \+ *theorem* decidable.ne_or_eq
- \+ *theorem* em'
- \+/\- *theorem* em
- \+ *theorem* eq_or_ne
- \+ *theorem* ne_or_eq
- \+/\- *theorem* or_not

Modified src/tactic/lint/type_classes.lean




## [2021-05-15 21:20:52](https://github.com/leanprover-community/mathlib/commit/d338ebd)
feat(counterexamples/*): add counterexamples folder ([#7558](https://github.com/leanprover-community/mathlib/pull/7558))
Several times, there has been a discussion on Zulip about the appropriateness of having counterexamples in mathlib.  This PR introduces a `counterexamples` folder, together with the first couple of counterexamples.
For the most recent discussion, see
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.237553
#### Estimated changes
Added src/counterexamples/canonically_ordered_comm_semiring_two_mul.lean
- \+ *lemma* Nxzmod_2.add_le_add_left
- \+ *lemma* Nxzmod_2.add_left_cancel
- \+ *lemma* Nxzmod_2.le_of_add_le_add_left
- \+ *lemma* Nxzmod_2.lt_def
- \+ *lemma* Nxzmod_2.mul_lt_mul_of_pos_left
- \+ *lemma* Nxzmod_2.mul_lt_mul_of_pos_right
- \+ *lemma* Nxzmod_2.zero_le_one
- \+ *lemma* add_self_zmod_2
- \+ *def* ex_L.L
- \+ *lemma* ex_L.add_L
- \+ *lemma* ex_L.bot_le
- \+ *lemma* ex_L.eq_zero_or_eq_zero_of_mul_eq_zero
- \+ *lemma* ex_L.le_iff_exists_add
- \+ *lemma* ex_L.lt_of_add_lt_add_left
- \+ *lemma* ex_L.mul_L
- \+ *def* from_Bhavik.K
- \+ *lemma* mem_zmod_2

Added src/counterexamples/linear_order_with_pos_mul_pos_eq_zero.lean
- \+ *def* foo.aux1
- \+ *lemma* foo.aux1_inj
- \+ *def* foo.mul
- \+ *lemma* foo.not_mul_pos



## [2021-05-15 21:20:51](https://github.com/leanprover-community/mathlib/commit/56442cf)
feat(data/nnreal): div and pow lemmas ([#7471](https://github.com/leanprover-community/mathlib/pull/7471))
from the liquid tensor experiment
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.div_le_div_left
- \+ *lemma* nnreal.div_le_div_left_of_le
- \+ *lemma* nnreal.pow_mono_decr_exp



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
- \- *def* pi.alg_hom.apply
- \+ *def* pi.eval_alg_hom

Modified src/algebra/big_operators/pi.lean


Modified src/algebra/category/Group/biproducts.lean


Modified src/algebra/char_p/pi.lean


Modified src/algebra/group/pi.lean
- \- *def* monoid_hom.apply
- \- *lemma* monoid_hom.apply_apply
- \+ *def* pi.eval_monoid_hom

Modified src/algebra/ring/pi.lean
- \+ *def* pi.eval_ring_hom
- \- *def* ring_hom.apply
- \- *lemma* ring_hom.apply_apply

Modified src/data/dfinsupp.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/linear_algebra/quadratic_form.lean


Modified src/ring_theory/witt_vector/basic.lean
- \+/\- *def* witt_vector.ghost_component



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
- \+/\- *def* function.injective.ordered_comm_monoid
- \- *lemma* le_mul_iff_one_le_left'
- \- *lemma* le_mul_iff_one_le_right'
- \- *lemma* le_mul_of_le_mul_left
- \- *lemma* le_mul_of_le_mul_right
- \- *lemma* le_mul_of_le_of_one_le
- \- *lemma* le_mul_of_one_le_left'
- \- *lemma* le_mul_of_one_le_of_le
- \- *lemma* le_mul_of_one_le_right'
- \- *lemma* le_of_le_mul_of_le_one_left
- \- *lemma* le_of_le_mul_of_le_one_right
- \- *lemma* le_of_mul_le_mul_left'
- \- *lemma* le_of_mul_le_mul_right'
- \- *lemma* le_of_mul_le_of_one_le_left
- \- *lemma* le_of_mul_le_of_one_le_right
- \- *lemma* lt_mul_iff_one_lt_left'
- \- *lemma* lt_mul_iff_one_lt_right'
- \- *lemma* lt_mul_of_le_of_one_lt
- \- *lemma* lt_mul_of_lt_mul_left
- \- *lemma* lt_mul_of_lt_mul_right
- \- *lemma* lt_mul_of_lt_of_one_le'
- \- *lemma* lt_mul_of_lt_of_one_le
- \- *lemma* lt_mul_of_lt_of_one_lt'
- \- *lemma* lt_mul_of_lt_of_one_lt
- \- *lemma* lt_mul_of_one_le_of_lt'
- \- *lemma* lt_mul_of_one_le_of_lt
- \- *lemma* lt_mul_of_one_lt_left'
- \- *lemma* lt_mul_of_one_lt_of_le
- \- *lemma* lt_mul_of_one_lt_of_lt'
- \- *lemma* lt_mul_of_one_lt_of_lt
- \- *lemma* lt_mul_of_one_lt_right'
- \- *lemma* lt_of_lt_mul_of_le_one_left
- \- *lemma* lt_of_lt_mul_of_le_one_right
- \- *lemma* lt_of_mul_lt_mul_left'
- \- *lemma* lt_of_mul_lt_mul_right'
- \- *lemma* lt_of_mul_lt_of_one_le_left
- \- *lemma* lt_of_mul_lt_of_one_le_right
- \- *lemma* monotone.const_mul'
- \- *lemma* monotone.mul'
- \- *lemma* monotone.mul_const'
- \- *lemma* mul_eq_one_iff'
- \- *lemma* mul_eq_one_iff_eq_one_of_one_le
- \- *lemma* mul_le_iff_le_one_left'
- \- *lemma* mul_le_iff_le_one_right'
- \- *lemma* mul_le_mul'
- \- *lemma* mul_le_mul_iff_left
- \- *lemma* mul_le_mul_iff_right
- \- *lemma* mul_le_mul_left'
- \- *lemma* mul_le_mul_right'
- \- *lemma* mul_le_mul_three
- \- *lemma* mul_le_of_le_of_le_one'
- \- *lemma* mul_le_of_le_of_le_one
- \- *lemma* mul_le_of_le_one_left'
- \- *lemma* mul_le_of_le_one_of_le'
- \- *lemma* mul_le_of_le_one_of_le
- \- *lemma* mul_le_of_le_one_right'
- \- *lemma* mul_le_of_mul_le_left
- \- *lemma* mul_le_of_mul_le_right
- \- *lemma* mul_le_one'
- \- *lemma* mul_lt_iff_lt_one_left'
- \- *lemma* mul_lt_iff_lt_one_right'
- \- *lemma* mul_lt_mul'''
- \- *lemma* mul_lt_mul_iff_left
- \- *lemma* mul_lt_mul_iff_right
- \- *lemma* mul_lt_mul_left'
- \- *lemma* mul_lt_mul_of_le_of_lt
- \- *lemma* mul_lt_mul_of_lt_of_le
- \- *lemma* mul_lt_mul_right'
- \- *lemma* mul_lt_of_le_of_lt_one
- \- *lemma* mul_lt_of_le_one_of_lt'
- \- *lemma* mul_lt_of_le_one_of_lt
- \- *lemma* mul_lt_of_lt_of_le_one'
- \- *lemma* mul_lt_of_lt_of_le_one
- \- *lemma* mul_lt_of_lt_of_lt_one'
- \- *lemma* mul_lt_of_lt_of_lt_one
- \- *lemma* mul_lt_of_lt_one_of_le
- \- *lemma* mul_lt_of_lt_one_of_lt'
- \- *lemma* mul_lt_of_lt_one_of_lt
- \- *lemma* mul_lt_of_mul_lt_left
- \- *lemma* mul_lt_of_mul_lt_right
- \- *lemma* mul_lt_one'
- \- *lemma* mul_lt_one
- \- *lemma* mul_lt_one_of_le_one_of_lt_one'
- \- *lemma* mul_lt_one_of_le_one_of_lt_one
- \- *lemma* mul_lt_one_of_lt_one_of_le_one'
- \- *lemma* mul_lt_one_of_lt_one_of_le_one
- \- *lemma* one_le_mul
- \- *lemma* one_lt_mul'
- \- *lemma* one_lt_mul_of_le_of_lt'
- \- *lemma* one_lt_mul_of_lt_of_le'
- \- *lemma* pos_of_gt
- \+/\- *lemma* with_zero.lt_of_mul_lt_mul_left
- \+/\- *lemma* with_zero.mul_le_mul_left
- \+/\- *lemma* with_zero.zero_lt_coe

Added src/algebra/ordered_monoid_lemmas.lean
- \+ *def* contravariant
- \+ *def* covariant
- \+ *lemma* le_mul_iff_one_le_left'
- \+ *lemma* le_mul_iff_one_le_right'
- \+ *lemma* le_mul_of_le_mul_left
- \+ *lemma* le_mul_of_le_mul_right
- \+ *lemma* le_mul_of_le_of_one_le
- \+ *lemma* le_mul_of_one_le_left'
- \+ *lemma* le_mul_of_one_le_of_le
- \+ *lemma* le_mul_of_one_le_right'
- \+ *lemma* le_of_le_mul_of_le_one_left
- \+ *lemma* le_of_le_mul_of_le_one_right
- \+ *lemma* le_of_mul_le_mul_left'
- \+ *lemma* le_of_mul_le_mul_right'
- \+ *lemma* le_of_mul_le_of_one_le_left
- \+ *lemma* le_of_mul_le_of_one_le_right
- \+ *lemma* lt_mul_iff_one_lt_left'
- \+ *lemma* lt_mul_iff_one_lt_right'
- \+ *lemma* lt_mul_of_le_of_one_lt
- \+ *lemma* lt_mul_of_lt_mul_left
- \+ *lemma* lt_mul_of_lt_mul_right
- \+ *lemma* lt_mul_of_lt_of_one_le'
- \+ *lemma* lt_mul_of_lt_of_one_le
- \+ *lemma* lt_mul_of_lt_of_one_lt'
- \+ *lemma* lt_mul_of_lt_of_one_lt
- \+ *lemma* lt_mul_of_one_le_of_lt'
- \+ *lemma* lt_mul_of_one_le_of_lt
- \+ *lemma* lt_mul_of_one_lt_left'
- \+ *lemma* lt_mul_of_one_lt_of_le
- \+ *lemma* lt_mul_of_one_lt_of_lt'
- \+ *lemma* lt_mul_of_one_lt_of_lt
- \+ *lemma* lt_mul_of_one_lt_right'
- \+ *lemma* lt_of_lt_mul_of_le_one_left
- \+ *lemma* lt_of_lt_mul_of_le_one_right
- \+ *lemma* lt_of_mul_lt_mul_left'
- \+ *lemma* lt_of_mul_lt_mul_right'
- \+ *lemma* lt_of_mul_lt_of_one_le_left
- \+ *lemma* lt_of_mul_lt_of_one_le_right
- \+ *lemma* monotone.const_mul'
- \+ *lemma* monotone.mul'
- \+ *lemma* monotone.mul_const'
- \+ *lemma* mul_eq_one_iff'
- \+ *lemma* mul_eq_one_iff_eq_one_of_one_le
- \+ *lemma* mul_le_iff_le_one_left'
- \+ *lemma* mul_le_iff_le_one_right'
- \+ *lemma* mul_le_mul'
- \+ *lemma* mul_le_mul_iff_left
- \+ *lemma* mul_le_mul_iff_right
- \+ *lemma* mul_le_mul_left'
- \+ *lemma* mul_le_mul_right'
- \+ *lemma* mul_le_mul_three
- \+ *lemma* mul_le_of_le_of_le_one'
- \+ *lemma* mul_le_of_le_of_le_one
- \+ *lemma* mul_le_of_le_one_left'
- \+ *lemma* mul_le_of_le_one_of_le'
- \+ *lemma* mul_le_of_le_one_of_le
- \+ *lemma* mul_le_of_le_one_right'
- \+ *lemma* mul_le_of_mul_le_left
- \+ *lemma* mul_le_of_mul_le_right
- \+ *lemma* mul_le_one'
- \+ *lemma* mul_lt_iff_lt_one_left'
- \+ *lemma* mul_lt_iff_lt_one_right'
- \+ *lemma* mul_lt_mul'''
- \+ *lemma* mul_lt_mul_iff_left
- \+ *lemma* mul_lt_mul_iff_right
- \+ *lemma* mul_lt_mul_left'
- \+ *lemma* mul_lt_mul_of_le_of_lt
- \+ *lemma* mul_lt_mul_of_lt_of_le
- \+ *lemma* mul_lt_mul_right'
- \+ *lemma* mul_lt_of_le_of_lt_one
- \+ *lemma* mul_lt_of_le_one_of_lt'
- \+ *lemma* mul_lt_of_le_one_of_lt
- \+ *lemma* mul_lt_of_lt_of_le_one'
- \+ *lemma* mul_lt_of_lt_of_le_one
- \+ *lemma* mul_lt_of_lt_of_lt_one'
- \+ *lemma* mul_lt_of_lt_of_lt_one
- \+ *lemma* mul_lt_of_lt_one_of_le
- \+ *lemma* mul_lt_of_lt_one_of_lt'
- \+ *lemma* mul_lt_of_lt_one_of_lt
- \+ *lemma* mul_lt_of_mul_lt_left
- \+ *lemma* mul_lt_of_mul_lt_right
- \+ *lemma* mul_lt_one'
- \+ *lemma* mul_lt_one
- \+ *lemma* mul_lt_one_of_le_one_of_lt_one'
- \+ *lemma* mul_lt_one_of_le_one_of_lt_one
- \+ *lemma* mul_lt_one_of_lt_one_of_le_one'
- \+ *lemma* mul_lt_one_of_lt_one_of_le_one
- \+ *lemma* one_le_mul
- \+ *lemma* one_lt_mul'
- \+ *lemma* one_lt_mul_of_le_of_lt'
- \+ *lemma* one_lt_mul_of_lt_of_le'

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
- \+ *def* basis.det
- \+ *lemma* basis.det_apply
- \+ *lemma* basis.det_self
- \+ *lemma* is_basis.iff_det
- \+ *lemma* linear_equiv.is_unit_det
- \+ *def* linear_equiv.of_is_unit_det
- \- *lemma* matrix.alg_hom.map_det
- \- *lemma* matrix.det_apply'
- \- *lemma* matrix.det_apply
- \- *lemma* matrix.det_block_diagonal
- \- *lemma* matrix.det_diagonal
- \- *lemma* matrix.det_eq_elem_of_card_eq_one
- \- *lemma* matrix.det_eq_of_eq_det_one_mul
- \- *lemma* matrix.det_eq_of_eq_mul_det_one
- \- *lemma* matrix.det_eq_of_forall_col_eq_smul_add_pred
- \- *lemma* matrix.det_eq_of_forall_row_eq_smul_add_const
- \- *lemma* matrix.det_eq_of_forall_row_eq_smul_add_const_aux
- \- *lemma* matrix.det_eq_of_forall_row_eq_smul_add_pred
- \- *lemma* matrix.det_eq_of_forall_row_eq_smul_add_pred_aux
- \- *lemma* matrix.det_eq_one_of_card_eq_zero
- \- *lemma* matrix.det_eq_zero_of_column_eq_zero
- \- *lemma* matrix.det_eq_zero_of_row_eq_zero
- \- *lemma* matrix.det_fin_zero
- \- *lemma* matrix.det_minor_equiv_self
- \- *lemma* matrix.det_mul
- \- *lemma* matrix.det_mul_aux
- \- *lemma* matrix.det_mul_column
- \- *lemma* matrix.det_mul_row
- \- *lemma* matrix.det_one
- \- *lemma* matrix.det_permutation
- \- *lemma* matrix.det_permute
- \- *lemma* matrix.det_reindex_self
- \- *def* matrix.det_row_multilinear
- \- *lemma* matrix.det_smul
- \- *lemma* matrix.det_succ_column
- \- *lemma* matrix.det_succ_column_zero
- \- *lemma* matrix.det_succ_row
- \- *lemma* matrix.det_succ_row_zero
- \- *lemma* matrix.det_transpose
- \- *lemma* matrix.det_unique
- \- *lemma* matrix.det_update_column_add
- \- *lemma* matrix.det_update_column_add_self
- \- *lemma* matrix.det_update_column_add_smul_self
- \- *lemma* matrix.det_update_column_smul
- \- *lemma* matrix.det_update_row_add
- \- *lemma* matrix.det_update_row_add_self
- \- *lemma* matrix.det_update_row_add_smul_self
- \- *lemma* matrix.det_update_row_smul
- \- *lemma* matrix.det_zero
- \- *theorem* matrix.det_zero_of_column_eq
- \- *theorem* matrix.det_zero_of_row_eq
- \- *lemma* matrix.ring_hom.map_det
- \- *lemma* matrix.upper_two_block_triangular_det

Modified src/linear_algebra/eigenspace.lean


Deleted src/linear_algebra/matrix.lean
- \- *def* alg_equiv_matrix'
- \- *def* alg_equiv_matrix
- \- *lemma* algebra.left_mul_matrix_apply
- \- *lemma* algebra.left_mul_matrix_eq_repr_mul
- \- *lemma* algebra.left_mul_matrix_injective
- \- *lemma* algebra.left_mul_matrix_mul_vec_repr
- \- *lemma* algebra.smul_left_mul_matrix
- \- *lemma* algebra.smul_left_mul_matrix_algebra_map
- \- *lemma* algebra.smul_left_mul_matrix_algebra_map_eq
- \- *lemma* algebra.smul_left_mul_matrix_algebra_map_ne
- \- *lemma* algebra.to_matrix_lmul'
- \- *lemma* algebra.to_matrix_lmul_eq
- \- *lemma* algebra.to_matrix_lsmul
- \- *def* basis.det
- \- *lemma* basis.det_apply
- \- *lemma* basis.det_self
- \- *lemma* basis.sum_to_matrix_smul_self
- \- *lemma* basis.to_lin_to_matrix
- \- *def* basis.to_matrix
- \- *lemma* basis.to_matrix_apply
- \- *lemma* basis.to_matrix_eq_to_matrix_constr
- \- *def* basis.to_matrix_equiv
- \- *lemma* basis.to_matrix_mul_to_matrix
- \- *lemma* basis.to_matrix_self
- \- *lemma* basis.to_matrix_transpose_apply
- \- *lemma* basis.to_matrix_update
- \- *lemma* basis_to_matrix_mul_linear_map_to_matrix
- \- *lemma* is_basis.iff_det
- \- *def* linear_equiv.alg_conj
- \- *lemma* linear_equiv.is_unit_det
- \- *def* linear_equiv.of_is_unit_det
- \- *lemma* linear_map.finrank_linear_map
- \- *def* linear_map.to_matrix'
- \- *lemma* linear_map.to_matrix'_apply
- \- *lemma* linear_map.to_matrix'_comp
- \- *lemma* linear_map.to_matrix'_id
- \- *lemma* linear_map.to_matrix'_mul
- \- *lemma* linear_map.to_matrix'_symm
- \- *lemma* linear_map.to_matrix'_to_lin'
- \- *def* linear_map.to_matrix
- \- *def* linear_map.to_matrix_alg_equiv'
- \- *lemma* linear_map.to_matrix_alg_equiv'_apply
- \- *lemma* linear_map.to_matrix_alg_equiv'_comp
- \- *lemma* linear_map.to_matrix_alg_equiv'_id
- \- *lemma* linear_map.to_matrix_alg_equiv'_mul
- \- *lemma* linear_map.to_matrix_alg_equiv'_symm
- \- *lemma* linear_map.to_matrix_alg_equiv'_to_lin_alg_equiv'
- \- *def* linear_map.to_matrix_alg_equiv
- \- *lemma* linear_map.to_matrix_alg_equiv_apply'
- \- *lemma* linear_map.to_matrix_alg_equiv_apply
- \- *lemma* linear_map.to_matrix_alg_equiv_comp
- \- *lemma* linear_map.to_matrix_alg_equiv_id
- \- *lemma* linear_map.to_matrix_alg_equiv_mul
- \- *theorem* linear_map.to_matrix_alg_equiv_reindex_range
- \- *lemma* linear_map.to_matrix_alg_equiv_symm
- \- *lemma* linear_map.to_matrix_alg_equiv_to_lin_alg_equiv
- \- *lemma* linear_map.to_matrix_alg_equiv_transpose_apply'
- \- *lemma* linear_map.to_matrix_alg_equiv_transpose_apply
- \- *lemma* linear_map.to_matrix_apply'
- \- *lemma* linear_map.to_matrix_apply
- \- *lemma* linear_map.to_matrix_comp
- \- *lemma* linear_map.to_matrix_id
- \- *lemma* linear_map.to_matrix_id_eq_basis_to_matrix
- \- *lemma* linear_map.to_matrix_mul
- \- *lemma* linear_map.to_matrix_mul_vec_repr
- \- *lemma* linear_map.to_matrix_one
- \- *theorem* linear_map.to_matrix_reindex_range
- \- *lemma* linear_map.to_matrix_symm
- \- *lemma* linear_map.to_matrix_to_lin
- \- *lemma* linear_map.to_matrix_transpose
- \- *lemma* linear_map.to_matrix_transpose_apply'
- \- *lemma* linear_map.to_matrix_transpose_apply
- \- *def* linear_map.trace
- \- *def* linear_map.trace_aux
- \- *lemma* linear_map.trace_aux_def
- \- *theorem* linear_map.trace_aux_eq
- \- *theorem* linear_map.trace_aux_reindex_range
- \- *theorem* linear_map.trace_eq_matrix_trace
- \- *theorem* linear_map.trace_eq_matrix_trace_of_finite_set
- \- *theorem* linear_map.trace_mul_comm
- \- *lemma* linear_map_to_matrix_mul_basis_to_matrix
- \- *def* matrix.block_triangular_matrix'
- \- *def* matrix.block_triangular_matrix
- \- *lemma* matrix.det_of_block_triangular_matrix''
- \- *lemma* matrix.det_of_block_triangular_matrix'
- \- *lemma* matrix.det_of_block_triangular_matrix
- \- *lemma* matrix.det_of_lower_triangular
- \- *lemma* matrix.det_of_upper_triangular
- \- *lemma* matrix.det_reindex_alg_equiv
- \- *lemma* matrix.det_reindex_linear_equiv_self
- \- *lemma* matrix.det_to_block
- \- *lemma* matrix.det_to_square_block'
- \- *lemma* matrix.det_to_square_block
- \- *def* matrix.diag
- \- *lemma* matrix.diag_apply
- \- *lemma* matrix.diag_one
- \- *lemma* matrix.diag_transpose
- \- *lemma* matrix.diagonal_comp_std_basis
- \- *lemma* matrix.diagonal_to_lin'
- \- *lemma* matrix.dot_product_eq
- \- *lemma* matrix.dot_product_eq_iff
- \- *lemma* matrix.dot_product_eq_zero
- \- *lemma* matrix.dot_product_eq_zero_iff
- \- *lemma* matrix.dot_product_std_basis_eq_mul
- \- *lemma* matrix.dot_product_std_basis_one
- \- *lemma* matrix.equiv_block_det
- \- *lemma* matrix.finrank_matrix
- \- *lemma* matrix.ker_diagonal_to_lin'
- \- *lemma* matrix.ker_to_lin_eq_bot
- \- *def* matrix.mul_vec_lin
- \- *lemma* matrix.mul_vec_lin_apply
- \- *lemma* matrix.mul_vec_std_basis
- \- *lemma* matrix.proj_diagonal
- \- *lemma* matrix.range_diagonal
- \- *lemma* matrix.range_to_lin_eq_top
- \- *lemma* matrix.rank_diagonal
- \- *lemma* matrix.rank_vec_mul_vec
- \- *def* matrix.reindex_alg_equiv
- \- *lemma* matrix.reindex_alg_equiv_apply
- \- *lemma* matrix.reindex_alg_equiv_refl
- \- *lemma* matrix.reindex_alg_equiv_symm
- \- *def* matrix.reindex_linear_equiv
- \- *lemma* matrix.reindex_linear_equiv_apply
- \- *lemma* matrix.reindex_linear_equiv_refl_refl
- \- *lemma* matrix.reindex_linear_equiv_symm
- \- *def* matrix.to_lin'
- \- *lemma* matrix.to_lin'_apply
- \- *lemma* matrix.to_lin'_mul
- \- *lemma* matrix.to_lin'_one
- \- *lemma* matrix.to_lin'_symm
- \- *lemma* matrix.to_lin'_to_matrix'
- \- *def* matrix.to_lin
- \- *def* matrix.to_lin_alg_equiv'
- \- *lemma* matrix.to_lin_alg_equiv'_apply
- \- *lemma* matrix.to_lin_alg_equiv'_mul
- \- *lemma* matrix.to_lin_alg_equiv'_one
- \- *lemma* matrix.to_lin_alg_equiv'_symm
- \- *lemma* matrix.to_lin_alg_equiv'_to_matrix_alg_equiv'
- \- *def* matrix.to_lin_alg_equiv
- \- *lemma* matrix.to_lin_alg_equiv_apply
- \- *lemma* matrix.to_lin_alg_equiv_mul
- \- *lemma* matrix.to_lin_alg_equiv_one
- \- *lemma* matrix.to_lin_alg_equiv_self
- \- *lemma* matrix.to_lin_alg_equiv_symm
- \- *lemma* matrix.to_lin_alg_equiv_to_matrix_alg_equiv
- \- *lemma* matrix.to_lin_apply
- \- *lemma* matrix.to_lin_mul
- \- *lemma* matrix.to_lin_one
- \- *lemma* matrix.to_lin_self
- \- *lemma* matrix.to_lin_symm
- \- *lemma* matrix.to_lin_to_matrix
- \- *lemma* matrix.to_lin_transpose
- \- *def* matrix.to_linear_equiv'
- \- *lemma* matrix.to_linear_equiv'_apply
- \- *lemma* matrix.to_linear_equiv'_symm_apply
- \- *def* matrix.to_linear_equiv
- \- *lemma* matrix.to_square_block_det''
- \- *def* matrix.trace
- \- *lemma* matrix.trace_apply
- \- *lemma* matrix.trace_diag
- \- *lemma* matrix.trace_mul_comm
- \- *lemma* matrix.trace_one
- \- *lemma* matrix.trace_transpose
- \- *lemma* matrix.trace_transpose_mul
- \- *lemma* matrix.two_block_triangular_det
- \- *lemma* matrix.upper_two_block_triangular'
- \- *lemma* matrix.upper_two_block_triangular

Added src/linear_algebra/matrix/basis.lean
- \+ *lemma* basis.sum_to_matrix_smul_self
- \+ *lemma* basis.to_lin_to_matrix
- \+ *def* basis.to_matrix
- \+ *lemma* basis.to_matrix_apply
- \+ *lemma* basis.to_matrix_eq_to_matrix_constr
- \+ *def* basis.to_matrix_equiv
- \+ *lemma* basis.to_matrix_mul_to_matrix
- \+ *lemma* basis.to_matrix_self
- \+ *lemma* basis.to_matrix_transpose_apply
- \+ *lemma* basis.to_matrix_update
- \+ *lemma* basis_to_matrix_mul_linear_map_to_matrix
- \+ *lemma* linear_map.to_matrix_id_eq_basis_to_matrix
- \+ *lemma* linear_map_to_matrix_mul_basis_to_matrix

Added src/linear_algebra/matrix/block.lean
- \+ *def* matrix.block_triangular_matrix'
- \+ *def* matrix.block_triangular_matrix
- \+ *lemma* matrix.det_of_block_triangular_matrix''
- \+ *lemma* matrix.det_of_block_triangular_matrix'
- \+ *lemma* matrix.det_of_block_triangular_matrix
- \+ *lemma* matrix.det_of_lower_triangular
- \+ *lemma* matrix.det_of_upper_triangular
- \+ *lemma* matrix.det_to_block
- \+ *lemma* matrix.det_to_square_block'
- \+ *lemma* matrix.det_to_square_block
- \+ *lemma* matrix.equiv_block_det
- \+ *lemma* matrix.to_square_block_det''
- \+ *lemma* matrix.two_block_triangular_det
- \+ *lemma* matrix.upper_two_block_triangular'
- \+ *lemma* matrix.upper_two_block_triangular

Added src/linear_algebra/matrix/default.lean


Added src/linear_algebra/matrix/determinant.lean
- \+ *lemma* matrix.alg_hom.map_det
- \+ *lemma* matrix.det_apply'
- \+ *lemma* matrix.det_apply
- \+ *lemma* matrix.det_block_diagonal
- \+ *lemma* matrix.det_diagonal
- \+ *lemma* matrix.det_eq_elem_of_card_eq_one
- \+ *lemma* matrix.det_eq_of_eq_det_one_mul
- \+ *lemma* matrix.det_eq_of_eq_mul_det_one
- \+ *lemma* matrix.det_eq_of_forall_col_eq_smul_add_pred
- \+ *lemma* matrix.det_eq_of_forall_row_eq_smul_add_const
- \+ *lemma* matrix.det_eq_of_forall_row_eq_smul_add_const_aux
- \+ *lemma* matrix.det_eq_of_forall_row_eq_smul_add_pred
- \+ *lemma* matrix.det_eq_of_forall_row_eq_smul_add_pred_aux
- \+ *lemma* matrix.det_eq_one_of_card_eq_zero
- \+ *lemma* matrix.det_eq_zero_of_column_eq_zero
- \+ *lemma* matrix.det_eq_zero_of_row_eq_zero
- \+ *lemma* matrix.det_fin_zero
- \+ *lemma* matrix.det_minor_equiv_self
- \+ *lemma* matrix.det_mul
- \+ *lemma* matrix.det_mul_aux
- \+ *lemma* matrix.det_mul_column
- \+ *lemma* matrix.det_mul_row
- \+ *lemma* matrix.det_one
- \+ *lemma* matrix.det_permutation
- \+ *lemma* matrix.det_permute
- \+ *lemma* matrix.det_reindex_self
- \+ *def* matrix.det_row_multilinear
- \+ *lemma* matrix.det_smul
- \+ *lemma* matrix.det_succ_column
- \+ *lemma* matrix.det_succ_column_zero
- \+ *lemma* matrix.det_succ_row
- \+ *lemma* matrix.det_succ_row_zero
- \+ *lemma* matrix.det_transpose
- \+ *lemma* matrix.det_unique
- \+ *lemma* matrix.det_update_column_add
- \+ *lemma* matrix.det_update_column_add_self
- \+ *lemma* matrix.det_update_column_add_smul_self
- \+ *lemma* matrix.det_update_column_smul
- \+ *lemma* matrix.det_update_row_add
- \+ *lemma* matrix.det_update_row_add_self
- \+ *lemma* matrix.det_update_row_add_smul_self
- \+ *lemma* matrix.det_update_row_smul
- \+ *lemma* matrix.det_zero
- \+ *theorem* matrix.det_zero_of_column_eq
- \+ *theorem* matrix.det_zero_of_row_eq
- \+ *lemma* matrix.ring_hom.map_det
- \+ *lemma* matrix.upper_two_block_triangular_det

Added src/linear_algebra/matrix/diagonal.lean
- \+ *lemma* matrix.diagonal_comp_std_basis
- \+ *lemma* matrix.diagonal_to_lin'
- \+ *lemma* matrix.ker_diagonal_to_lin'
- \+ *lemma* matrix.proj_diagonal
- \+ *lemma* matrix.range_diagonal
- \+ *lemma* matrix.rank_diagonal

Added src/linear_algebra/matrix/dot_product.lean
- \+ *lemma* matrix.dot_product_eq
- \+ *lemma* matrix.dot_product_eq_iff
- \+ *lemma* matrix.dot_product_eq_zero
- \+ *lemma* matrix.dot_product_eq_zero_iff
- \+ *lemma* matrix.dot_product_std_basis_eq_mul
- \+ *lemma* matrix.dot_product_std_basis_one

Added src/linear_algebra/matrix/dual.lean
- \+ *lemma* linear_map.to_matrix_transpose
- \+ *lemma* matrix.to_lin_transpose

Added src/linear_algebra/matrix/finite_dimensional.lean
- \+ *lemma* matrix.finrank_matrix

Renamed src/linear_algebra/nonsingular_inverse.lean to src/linear_algebra/matrix/nonsingular_inverse.lean


Added src/linear_algebra/matrix/reindex.lean
- \+ *lemma* matrix.det_reindex_alg_equiv
- \+ *lemma* matrix.det_reindex_linear_equiv_self
- \+ *def* matrix.reindex_alg_equiv
- \+ *lemma* matrix.reindex_alg_equiv_apply
- \+ *lemma* matrix.reindex_alg_equiv_refl
- \+ *lemma* matrix.reindex_alg_equiv_symm
- \+ *def* matrix.reindex_linear_equiv
- \+ *lemma* matrix.reindex_linear_equiv_apply
- \+ *lemma* matrix.reindex_linear_equiv_refl_refl
- \+ *lemma* matrix.reindex_linear_equiv_symm

Added src/linear_algebra/matrix/to_lin.lean
- \+ *def* alg_equiv_matrix'
- \+ *def* alg_equiv_matrix
- \+ *lemma* algebra.left_mul_matrix_apply
- \+ *lemma* algebra.left_mul_matrix_eq_repr_mul
- \+ *lemma* algebra.left_mul_matrix_injective
- \+ *lemma* algebra.left_mul_matrix_mul_vec_repr
- \+ *lemma* algebra.smul_left_mul_matrix
- \+ *lemma* algebra.smul_left_mul_matrix_algebra_map
- \+ *lemma* algebra.smul_left_mul_matrix_algebra_map_eq
- \+ *lemma* algebra.smul_left_mul_matrix_algebra_map_ne
- \+ *lemma* algebra.to_matrix_lmul'
- \+ *lemma* algebra.to_matrix_lmul_eq
- \+ *lemma* algebra.to_matrix_lsmul
- \+ *def* linear_equiv.alg_conj
- \+ *lemma* linear_map.finrank_linear_map
- \+ *def* linear_map.to_matrix'
- \+ *lemma* linear_map.to_matrix'_apply
- \+ *lemma* linear_map.to_matrix'_comp
- \+ *lemma* linear_map.to_matrix'_id
- \+ *lemma* linear_map.to_matrix'_mul
- \+ *lemma* linear_map.to_matrix'_symm
- \+ *lemma* linear_map.to_matrix'_to_lin'
- \+ *def* linear_map.to_matrix
- \+ *def* linear_map.to_matrix_alg_equiv'
- \+ *lemma* linear_map.to_matrix_alg_equiv'_apply
- \+ *lemma* linear_map.to_matrix_alg_equiv'_comp
- \+ *lemma* linear_map.to_matrix_alg_equiv'_id
- \+ *lemma* linear_map.to_matrix_alg_equiv'_mul
- \+ *lemma* linear_map.to_matrix_alg_equiv'_symm
- \+ *lemma* linear_map.to_matrix_alg_equiv'_to_lin_alg_equiv'
- \+ *def* linear_map.to_matrix_alg_equiv
- \+ *lemma* linear_map.to_matrix_alg_equiv_apply'
- \+ *lemma* linear_map.to_matrix_alg_equiv_apply
- \+ *lemma* linear_map.to_matrix_alg_equiv_comp
- \+ *lemma* linear_map.to_matrix_alg_equiv_id
- \+ *lemma* linear_map.to_matrix_alg_equiv_mul
- \+ *theorem* linear_map.to_matrix_alg_equiv_reindex_range
- \+ *lemma* linear_map.to_matrix_alg_equiv_symm
- \+ *lemma* linear_map.to_matrix_alg_equiv_to_lin_alg_equiv
- \+ *lemma* linear_map.to_matrix_alg_equiv_transpose_apply'
- \+ *lemma* linear_map.to_matrix_alg_equiv_transpose_apply
- \+ *lemma* linear_map.to_matrix_apply'
- \+ *lemma* linear_map.to_matrix_apply
- \+ *lemma* linear_map.to_matrix_comp
- \+ *lemma* linear_map.to_matrix_id
- \+ *lemma* linear_map.to_matrix_mul
- \+ *lemma* linear_map.to_matrix_mul_vec_repr
- \+ *lemma* linear_map.to_matrix_one
- \+ *theorem* linear_map.to_matrix_reindex_range
- \+ *lemma* linear_map.to_matrix_symm
- \+ *lemma* linear_map.to_matrix_to_lin
- \+ *lemma* linear_map.to_matrix_transpose_apply'
- \+ *lemma* linear_map.to_matrix_transpose_apply
- \+ *def* matrix.mul_vec_lin
- \+ *lemma* matrix.mul_vec_lin_apply
- \+ *lemma* matrix.mul_vec_std_basis
- \+ *lemma* matrix.rank_vec_mul_vec
- \+ *def* matrix.to_lin'
- \+ *lemma* matrix.to_lin'_apply
- \+ *lemma* matrix.to_lin'_mul
- \+ *lemma* matrix.to_lin'_one
- \+ *lemma* matrix.to_lin'_symm
- \+ *lemma* matrix.to_lin'_to_matrix'
- \+ *def* matrix.to_lin
- \+ *def* matrix.to_lin_alg_equiv'
- \+ *lemma* matrix.to_lin_alg_equiv'_apply
- \+ *lemma* matrix.to_lin_alg_equiv'_mul
- \+ *lemma* matrix.to_lin_alg_equiv'_one
- \+ *lemma* matrix.to_lin_alg_equiv'_symm
- \+ *lemma* matrix.to_lin_alg_equiv'_to_matrix_alg_equiv'
- \+ *def* matrix.to_lin_alg_equiv
- \+ *lemma* matrix.to_lin_alg_equiv_apply
- \+ *lemma* matrix.to_lin_alg_equiv_mul
- \+ *lemma* matrix.to_lin_alg_equiv_one
- \+ *lemma* matrix.to_lin_alg_equiv_self
- \+ *lemma* matrix.to_lin_alg_equiv_symm
- \+ *lemma* matrix.to_lin_alg_equiv_to_matrix_alg_equiv
- \+ *lemma* matrix.to_lin_apply
- \+ *lemma* matrix.to_lin_mul
- \+ *lemma* matrix.to_lin_one
- \+ *lemma* matrix.to_lin_self
- \+ *lemma* matrix.to_lin_symm
- \+ *lemma* matrix.to_lin_to_matrix

Added src/linear_algebra/matrix/to_linear_equiv.lean
- \+ *lemma* matrix.ker_to_lin_eq_bot
- \+ *lemma* matrix.range_to_lin_eq_top
- \+ *lemma* matrix.to_linear_equiv'_apply
- \+ *lemma* matrix.to_linear_equiv'_symm_apply

Added src/linear_algebra/matrix/trace.lean
- \+ *def* matrix.diag
- \+ *lemma* matrix.diag_apply
- \+ *lemma* matrix.diag_one
- \+ *lemma* matrix.diag_transpose
- \+ *def* matrix.trace
- \+ *lemma* matrix.trace_apply
- \+ *lemma* matrix.trace_diag
- \+ *lemma* matrix.trace_mul_comm
- \+ *lemma* matrix.trace_one
- \+ *lemma* matrix.trace_transpose
- \+ *lemma* matrix.trace_transpose_mul

Modified src/linear_algebra/quadratic_form.lean


Modified src/linear_algebra/special_linear_group.lean


Added src/linear_algebra/trace.lean
- \+ *def* linear_map.trace
- \+ *def* linear_map.trace_aux
- \+ *lemma* linear_map.trace_aux_def
- \+ *theorem* linear_map.trace_aux_eq
- \+ *theorem* linear_map.trace_aux_reindex_range
- \+ *theorem* linear_map.trace_eq_matrix_trace
- \+ *theorem* linear_map.trace_eq_matrix_trace_of_finite_set
- \+ *theorem* linear_map.trace_mul_comm

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
- \+ *lemma* lie_module_hom.coe_restrict_lie
- \+ *def* lie_module_hom.restrict_lie

Modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_subalgebra.coe_to_lie_submodule
- \+/\- *lemma* lie_subalgebra.exists_lie_ideal_coe_eq_iff
- \+ *lemma* lie_subalgebra.mem_to_lie_submodule
- \+ *def* lie_subalgebra.to_lie_submodule
- \+ *lemma* lie_submodule.coe_add
- \+ *lemma* lie_submodule.coe_bracket
- \+ *lemma* lie_submodule.coe_neg
- \+ *lemma* lie_submodule.coe_smul
- \+ *lemma* lie_submodule.coe_sub
- \+ *lemma* lie_submodule.coe_zero

Modified src/algebra/lie/weights.lean
- \+ *lemma* lie_algebra.coe_root_space_weight_space_product_tmul
- \+ *lemma* lie_algebra.coe_zero_root_subalgebra
- \+ *lemma* lie_algebra.le_zero_root_subalgebra
- \+ *lemma* lie_algebra.lie_mem_weight_space_of_mem_weight_space
- \+ *def* lie_algebra.root_space_product
- \+ *lemma* lie_algebra.root_space_product_def
- \+ *lemma* lie_algebra.root_space_product_tmul
- \+ *def* lie_algebra.root_space_weight_space_product
- \+ *lemma* lie_algebra.to_lie_submodule_le_root_space_zero
- \+ *def* lie_algebra.zero_root_subalgebra



## [2021-05-15 14:21:13](https://github.com/leanprover-community/mathlib/commit/515762a)
feat(category_theory/quotient): congruence relations ([#7501](https://github.com/leanprover-community/mathlib/pull/7501))
Define congruence relations and show that when you quotient a category by a congruence relation, two morphism become equal iff they are related.
#### Estimated changes
Modified src/category_theory/quotient.lean
- \+ *lemma* category_theory.quotient.functor_map_eq_iff
- \+ *def* hom_rel



## [2021-05-15 08:16:35](https://github.com/leanprover-community/mathlib/commit/fc94b47)
feat(counterexamples): a counterexample on the Pettis integral ([#7553](https://github.com/leanprover-community/mathlib/pull/7553))
Phillips (1940) has exhibited under the continuum hypothesis a bounded weakly measurable function which is not Pettis-integrable. We formalize this counterexample.
#### Estimated changes
Added counterexamples/phillips.lean
- \+ *def* continuous_linear_map.to_bounded_additive_measure
- \+ *def* discrete_copy
- \+ *def* measure_theory.measure.extension_to_bounded_functions
- \+ *lemma* phillips_1940.apply_f_eq_continuous_part
- \+ *def* phillips_1940.bounded_additive_measure.C
- \+ *lemma* phillips_1940.bounded_additive_measure.abs_le_bound
- \+ *lemma* phillips_1940.bounded_additive_measure.additive
- \+ *lemma* phillips_1940.bounded_additive_measure.apply_countable
- \+ *def* phillips_1940.bounded_additive_measure.continuous_part
- \+ *lemma* phillips_1940.bounded_additive_measure.continuous_part_apply_diff
- \+ *lemma* phillips_1940.bounded_additive_measure.continuous_part_apply_eq_zero_of_countable
- \+ *lemma* phillips_1940.bounded_additive_measure.countable_discrete_support
- \+ *def* phillips_1940.bounded_additive_measure.discrete_part
- \+ *lemma* phillips_1940.bounded_additive_measure.discrete_part_apply
- \+ *def* phillips_1940.bounded_additive_measure.discrete_support
- \+ *lemma* phillips_1940.bounded_additive_measure.empty
- \+ *lemma* phillips_1940.bounded_additive_measure.eq_add_parts
- \+ *lemma* phillips_1940.bounded_additive_measure.exists_discrete_support
- \+ *lemma* phillips_1940.bounded_additive_measure.exists_discrete_support_nonpos
- \+ *lemma* phillips_1940.bounded_additive_measure.le_bound
- \+ *lemma* phillips_1940.bounded_additive_measure.neg_apply
- \+ *def* phillips_1940.bounded_additive_measure.restrict
- \+ *lemma* phillips_1940.bounded_additive_measure.restrict_apply
- \+ *def* phillips_1940.bounded_integrable_functions
- \+ *def* phillips_1940.bounded_integrable_functions_integral_clm
- \+ *lemma* phillips_1940.comp_ae_eq_const
- \+ *lemma* phillips_1940.continuous_part_eval_clm_eq_zero
- \+ *lemma* phillips_1940.countable_compl_spf
- \+ *lemma* phillips_1940.countable_ne
- \+ *lemma* phillips_1940.countable_spf_mem
- \+ *lemma* phillips_1940.exists_linear_extension_to_bounded_functions
- \+ *lemma* phillips_1940.extension_to_bounded_functions_apply
- \+ *def* phillips_1940.f
- \+ *lemma* phillips_1940.integrable_comp
- \+ *lemma* phillips_1940.integral_comp
- \+ *lemma* phillips_1940.measurable_comp
- \+ *theorem* phillips_1940.no_pettis_integral
- \+ *lemma* phillips_1940.norm_bound
- \+ *lemma* phillips_1940.norm_indicator_le_one
- \+ *theorem* phillips_1940.sierpinski_pathological_family
- \+ *def* phillips_1940.spf
- \+ *lemma* phillips_1940.to_functions_to_measure
- \+ *lemma* phillips_1940.to_functions_to_measure_continuous_part

Modified docs/references.bib


Modified src/data/set/basic.lean
- \+ *lemma* set.diff_union_inter
- \+ *lemma* set.union_eq_diff_union_diff_union_inter
- \- *lemma* set.union_eq_sdiff_union_sdiff_union_inter

Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/lp_space.lean


Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable.measurable_of_countable_ne
- \+ *lemma* set.countable.measurable_set

Modified src/measure_theory/measure_space.lean
- \+ *lemma* finset.measure_zero
- \- *lemma* measure_theory.measure_countable
- \- *lemma* measure_theory.measure_finite
- \- *lemma* measure_theory.measure_finset
- \+ *lemma* set.countable.measure_zero
- \+ *lemma* set.finite.measure_zero

Modified src/set_theory/cardinal_ordinal.lean
- \+ *lemma* cardinal.countable_iff_lt_aleph_one

Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.coe_of_normed_group
- \+ *lemma* bounded_continuous_function.coe_of_normed_group_discrete
- \+/\- *theorem* bounded_continuous_function.continuous_eval
- \+/\- *theorem* bounded_continuous_function.continuous_evalx
- \+ *def* bounded_continuous_function.eval_clm
- \+ *lemma* bounded_continuous_function.eval_clm_apply



## [2021-05-15 08:16:34](https://github.com/leanprover-community/mathlib/commit/b4b38da)
feat(category_theory/*/projective): refactor treatment of projective objects ([#7485](https://github.com/leanprover-community/mathlib/pull/7485))
#### Estimated changes
Modified src/algebra/homology/exact.lean


Modified src/algebra/homology/homological_complex.lean


Modified src/algebra/homology/image_to_kernel.lean


Modified src/category_theory/abelian/non_preadditive.lean


Modified src/category_theory/abelian/projective.lean
- \+ *lemma* category_theory.exact_d_f
- \- *lemma* category_theory.projective.exact_d_f
- \- *def* category_theory.projective.factor_thru
- \- *lemma* category_theory.projective.factor_thru_comp
- \- *lemma* category_theory.projective.iso_iff
- \- *def* category_theory.projective.left
- \- *lemma* category_theory.projective.of_iso
- \- *def* category_theory.projective.over
- \- *def* category_theory.projective.π

Modified src/category_theory/closed/zero.lean


Modified src/category_theory/differential_object.lean


Modified src/category_theory/graded_object.lean


Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/preadditive/additive_functor.lean


Modified src/category_theory/preadditive/default.lean


Added src/category_theory/preadditive/projective.lean
- \+ *def* category_theory.exact.lift
- \+ *lemma* category_theory.exact.lift_comp
- \+ *def* category_theory.projective.factor_thru
- \+ *lemma* category_theory.projective.factor_thru_comp
- \+ *lemma* category_theory.projective.iso_iff
- \+ *lemma* category_theory.projective.of_iso
- \+ *def* category_theory.projective.over
- \+ *def* category_theory.projective.syzygies
- \+ *def* category_theory.projective.π

Modified src/category_theory/simple.lean


Modified src/category_theory/subobject/lattice.lean


Modified src/category_theory/triangulated/basic.lean




## [2021-05-15 08:16:32](https://github.com/leanprover-community/mathlib/commit/c63caeb)
feat(algebra/homology): homotopies between chain maps ([#7483](https://github.com/leanprover-community/mathlib/pull/7483))
#### Estimated changes
Modified src/algebra/homology/additive.lean


Added src/algebra/homology/homotopy.lean
- \+ *def* category_theory.functor.map_homotopy
- \+ *def* category_theory.functor.map_homotopy_equiv
- \+ *def* from_next'
- \+ *lemma* from_next'_add
- \+ *lemma* from_next'_comp_left
- \+ *lemma* from_next'_comp_right
- \+ *lemma* from_next'_eq
- \+ *lemma* from_next'_neg
- \+ *lemma* from_next'_zero
- \+ *theorem* homology_map_eq_of_homotopy
- \+ *def* homology_obj_iso_of_homotopy_equiv
- \+ *lemma* homotopy.comm
- \+ *def* homotopy.comp_left
- \+ *def* homotopy.comp_left_id
- \+ *def* homotopy.comp_right
- \+ *def* homotopy.comp_right_id
- \+ *def* homotopy.equiv_sub_zero
- \+ *lemma* homotopy.from_next'_succ_chain_complex
- \+ *lemma* homotopy.from_next'_zero_chain_complex
- \+ *def* homotopy.from_next
- \+ *def* homotopy.mk_inductive
- \+ *def* homotopy.mk_inductive_aux₁
- \+ *def* homotopy.mk_inductive_aux₂
- \+ *lemma* homotopy.mk_inductive_aux₃
- \+ *def* homotopy.refl
- \+ *def* homotopy.symm
- \+ *lemma* homotopy.to_prev'_chain_complex
- \+ *def* homotopy.to_prev
- \+ *def* homotopy.trans
- \+ *def* homotopy_equiv.refl
- \+ *def* homotopy_equiv.symm
- \+ *def* homotopy_equiv.trans
- \+ *def* to_prev'
- \+ *lemma* to_prev'_add
- \+ *lemma* to_prev'_comp_left
- \+ *lemma* to_prev'_comp_right
- \+ *lemma* to_prev'_eq
- \+ *lemma* to_prev'_neg
- \+ *lemma* to_prev'_zero



## [2021-05-15 08:16:31](https://github.com/leanprover-community/mathlib/commit/cc47aff)
feat(algebra/homology): truncation and augmentation of chain complexes ([#7480](https://github.com/leanprover-community/mathlib/pull/7480))
#### Estimated changes
Added src/algebra/homology/augment.lean
- \+ *def* chain_complex.augment
- \+ *lemma* chain_complex.augment_X_succ
- \+ *lemma* chain_complex.augment_X_zero
- \+ *lemma* chain_complex.augment_d_one_zero
- \+ *lemma* chain_complex.augment_d_succ_succ
- \+ *def* chain_complex.augment_truncate
- \+ *lemma* chain_complex.augment_truncate_hom_f_succ
- \+ *lemma* chain_complex.augment_truncate_hom_f_zero
- \+ *lemma* chain_complex.augment_truncate_inv_f_succ
- \+ *lemma* chain_complex.augment_truncate_inv_f_zero
- \+ *lemma* chain_complex.cochain_complex_d_succ_succ_zero
- \+ *def* chain_complex.to_single₀_as_complex
- \+ *def* chain_complex.truncate
- \+ *def* chain_complex.truncate_augment
- \+ *lemma* chain_complex.truncate_augment_hom_f
- \+ *lemma* chain_complex.truncate_augment_inv_f
- \+ *def* chain_complex.truncate_to



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
- \+ *lemma* chain_complex.of_d_ne
- \+ *def* chain_complex.of_hom

Added src/algebraic_topology/Moore_complex.lean
- \+ *lemma* algebraic_topology.normalized_Moore_complex.d_squared
- \+ *def* algebraic_topology.normalized_Moore_complex.map
- \+ *def* algebraic_topology.normalized_Moore_complex.obj
- \+ *def* algebraic_topology.normalized_Moore_complex.obj_X
- \+ *def* algebraic_topology.normalized_Moore_complex.obj_d
- \+ *def* algebraic_topology.normalized_Moore_complex



## [2021-05-15 03:59:57](https://github.com/leanprover-community/mathlib/commit/94aae73)
feat(data/nat/factorial) : descending factorial ([#7527](https://github.com/leanprover-community/mathlib/pull/7527))
#### Estimated changes
Modified src/data/nat/choose/basic.lean
- \+ *lemma* nat.choose_eq_desc_fac_div_factorial
- \+ *lemma* nat.desc_fac_eq_factorial_mul_choose
- \+ *lemma* nat.factorial_dvd_desc_fac

Modified src/data/nat/factorial.lean
- \+ *def* nat.desc_fac
- \+ *lemma* nat.desc_fac_eq_div
- \+ *lemma* nat.desc_fac_succ
- \+ *lemma* nat.desc_fac_zero
- \+ *theorem* nat.factorial_mul_desc_fac
- \+ *lemma* nat.succ_desc_fac
- \+ *lemma* nat.zero_desc_fac

Modified src/ring_theory/polynomial/bernstein.lean
- \- *lemma* bernstein_polynomial.iterate_derivative_at_0_aux₁
- \- *lemma* bernstein_polynomial.iterate_derivative_at_0_aux₂

Modified src/ring_theory/polynomial/pochhammer.lean
- \- *lemma* choose_eq_pochhammer_eval_div_factorial
- \- *lemma* factorial_mul_pochhammer'
- \- *lemma* pochhammer_eval_eq_choose_mul_factorial
- \- *lemma* pochhammer_eval_eq_factorial_div_factorial
- \- *lemma* pochhammer_eval_one'
- \+ *lemma* pochhammer_eval_succ
- \+ *lemma* pochhammer_nat_eq_desc_fac
- \+ *lemma* pochhammer_nat_eval_succ



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
- \+ *lemma* finsupp.single_nat_sub
- \+ *lemma* finsupp.single_neg
- \+/\- *lemma* finsupp.single_sub

Modified src/data/mv_polynomial/basic.lean


Modified src/data/mv_polynomial/comm_ring.lean
- \+ *lemma* mv_polynomial.monomial_neg
- \+ *lemma* mv_polynomial.monomial_sub



## [2021-05-14 17:28:32](https://github.com/leanprover-community/mathlib/commit/a52f471)
feat(algebra/homology): chain complexes are an additive category ([#7478](https://github.com/leanprover-community/mathlib/pull/7478))
#### Estimated changes
Added src/algebra/homology/additive.lean
- \+ *def* category_theory.functor.map_homological_complex
- \+ *def* category_theory.nat_trans.map_homological_complex
- \+ *lemma* category_theory.nat_trans.map_homological_complex_comp
- \+ *lemma* category_theory.nat_trans.map_homological_complex_id
- \+ *lemma* category_theory.nat_trans.map_homological_complex_naturality
- \+ *def* chain_complex.single₀_map_homological_complex
- \+ *lemma* chain_complex.single₀_map_homological_complex_hom_app_succ
- \+ *lemma* chain_complex.single₀_map_homological_complex_hom_app_zero
- \+ *lemma* chain_complex.single₀_map_homological_complex_inv_app_succ
- \+ *lemma* chain_complex.single₀_map_homological_complex_inv_app_zero
- \+ *lemma* homological_complex.add_f_apply
- \+ *lemma* homological_complex.neg_f_apply
- \+ *def* homological_complex.single_map_homological_complex
- \+ *lemma* homological_complex.single_map_homological_complex_hom_app_ne
- \+ *lemma* homological_complex.single_map_homological_complex_hom_app_self
- \+ *lemma* homological_complex.single_map_homological_complex_inv_app_ne
- \+ *lemma* homological_complex.single_map_homological_complex_inv_app_self
- \+ *lemma* homological_complex.sub_f_apply
- \+ *lemma* homological_complex.zero_f_apply

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
- \- *theorem* Liminf_eq_of_le_nhds
- \- *theorem* Liminf_nhds
- \- *theorem* Limsup_eq_of_le_nhds
- \- *theorem* Limsup_nhds
- \- *lemma* continuous_on_Icc_extend_from_Ioo
- \- *lemma* continuous_on_Ico_extend_from_Ioo
- \- *lemma* continuous_on_Ioc_extend_from_Ioo
- \- *lemma* eq_lim_at_left_extend_from_Ioo
- \- *lemma* eq_lim_at_right_extend_from_Ioo
- \- *lemma* filter.tendsto.is_bounded_under_ge
- \- *lemma* filter.tendsto.is_bounded_under_le
- \- *lemma* filter.tendsto.is_cobounded_under_ge
- \- *lemma* filter.tendsto.is_cobounded_under_le
- \- *theorem* filter.tendsto.liminf_eq
- \- *theorem* filter.tendsto.limsup_eq
- \- *theorem* gt_mem_sets_of_Liminf_gt
- \- *lemma* is_bounded_ge_nhds
- \- *lemma* is_bounded_le_nhds
- \- *lemma* is_cobounded_ge_nhds
- \- *lemma* is_cobounded_le_nhds
- \- *theorem* le_nhds_of_Limsup_eq_Liminf
- \- *theorem* lt_mem_sets_of_Limsup_lt
- \- *theorem* tendsto_of_le_liminf_of_limsup_le
- \- *theorem* tendsto_of_liminf_eq_limsup

Added src/topology/algebra/ordered/extend_from.lean
- \+ *lemma* continuous_on_Icc_extend_from_Ioo
- \+ *lemma* continuous_on_Ico_extend_from_Ioo
- \+ *lemma* continuous_on_Ioc_extend_from_Ioo
- \+ *lemma* eq_lim_at_left_extend_from_Ioo
- \+ *lemma* eq_lim_at_right_extend_from_Ioo

Added src/topology/algebra/ordered/liminf_limsup.lean
- \+ *theorem* Liminf_eq_of_le_nhds
- \+ *theorem* Liminf_nhds
- \+ *theorem* Limsup_eq_of_le_nhds
- \+ *theorem* Limsup_nhds
- \+ *lemma* filter.tendsto.is_bounded_under_ge
- \+ *lemma* filter.tendsto.is_bounded_under_le
- \+ *lemma* filter.tendsto.is_cobounded_under_ge
- \+ *lemma* filter.tendsto.is_cobounded_under_le
- \+ *theorem* filter.tendsto.liminf_eq
- \+ *theorem* filter.tendsto.limsup_eq
- \+ *theorem* gt_mem_sets_of_Liminf_gt
- \+ *lemma* is_bounded_ge_nhds
- \+ *lemma* is_bounded_le_nhds
- \+ *lemma* is_cobounded_ge_nhds
- \+ *lemma* is_cobounded_le_nhds
- \+ *theorem* le_nhds_of_Limsup_eq_Liminf
- \+ *theorem* lt_mem_sets_of_Limsup_lt
- \+ *theorem* tendsto_of_le_liminf_of_limsup_le
- \+ *theorem* tendsto_of_liminf_eq_limsup

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
- \+ *def* pgame.inv'
- \+ *def* pgame.inv_val
- \+ *theorem* pgame.left_distrib_equiv
- \+ *lemma* pgame.left_distrib_equiv_aux'
- \+ *lemma* pgame.left_distrib_equiv_aux
- \+ *def* pgame.left_moves_mul
- \+ *lemma* pgame.mk_mul_move_left_inl
- \+ *lemma* pgame.mk_mul_move_left_inr
- \+ *lemma* pgame.mk_mul_move_right_inl
- \+ *lemma* pgame.mk_mul_move_right_inr
- \+ *def* pgame.mul
- \+ *theorem* pgame.mul_comm_equiv
- \+ *def* pgame.mul_comm_relabelling
- \+ *lemma* pgame.mul_move_left_inl
- \+ *lemma* pgame.mul_move_left_inr
- \+ *lemma* pgame.mul_move_right_inl
- \+ *lemma* pgame.mul_move_right_inr
- \+ *theorem* pgame.mul_zero_equiv
- \+ *def* pgame.mul_zero_relabelling
- \+ *theorem* pgame.right_distrib_equiv
- \+ *def* pgame.right_moves_mul
- \+ *theorem* pgame.zero_mul_equiv
- \+ *def* pgame.zero_mul_relabelling

Modified src/set_theory/surreal.lean
- \- *def* pgame.inv'
- \- *def* pgame.inv_val
- \- *theorem* pgame.left_distrib_equiv
- \- *lemma* pgame.left_distrib_equiv_aux'
- \- *lemma* pgame.left_distrib_equiv_aux
- \- *def* pgame.left_moves_mul
- \- *lemma* pgame.mk_mul_move_left_inl
- \- *lemma* pgame.mk_mul_move_left_inr
- \- *lemma* pgame.mk_mul_move_right_inl
- \- *lemma* pgame.mk_mul_move_right_inr
- \- *def* pgame.mul
- \- *theorem* pgame.mul_comm_equiv
- \- *def* pgame.mul_comm_relabelling
- \- *lemma* pgame.mul_move_left_inl
- \- *lemma* pgame.mul_move_left_inr
- \- *lemma* pgame.mul_move_right_inl
- \- *lemma* pgame.mul_move_right_inr
- \- *theorem* pgame.mul_zero_equiv
- \- *def* pgame.mul_zero_relabelling
- \- *theorem* pgame.right_distrib_equiv
- \- *def* pgame.right_moves_mul
- \- *theorem* pgame.zero_mul_equiv
- \- *def* pgame.zero_mul_relabelling



## [2021-05-14 12:02:31](https://github.com/leanprover-community/mathlib/commit/87adde4)
feat(category_theory/monoidal): the monoidal opposite ([#7602](https://github.com/leanprover-community/mathlib/pull/7602))
#### Estimated changes
Added src/category_theory/monoidal/opposite.lean
- \+ *def* category_theory.iso.mop
- \+ *def* category_theory.monoidal_opposite.mop
- \+ *lemma* category_theory.monoidal_opposite.mop_unmop
- \+ *lemma* category_theory.monoidal_opposite.op_inj_iff
- \+ *lemma* category_theory.monoidal_opposite.op_injective
- \+ *def* category_theory.monoidal_opposite.unmop
- \+ *lemma* category_theory.monoidal_opposite.unmop_mop
- \+ *lemma* category_theory.monoidal_opposite.unop_inj_iff
- \+ *lemma* category_theory.monoidal_opposite.unop_injective
- \+ *def* category_theory.monoidal_opposite
- \+ *lemma* category_theory.mop_comp
- \+ *lemma* category_theory.mop_id
- \+ *lemma* category_theory.mop_id_unmop
- \+ *lemma* category_theory.mop_inj
- \+ *lemma* category_theory.mop_tensor_obj
- \+ *lemma* category_theory.mop_tensor_unit
- \+ *lemma* category_theory.mop_unmop
- \+ *lemma* category_theory.op_tensor_obj
- \+ *lemma* category_theory.op_tensor_unit
- \+ *lemma* category_theory.unmop_comp
- \+ *lemma* category_theory.unmop_id
- \+ *lemma* category_theory.unmop_id_mop
- \+ *lemma* category_theory.unmop_inj
- \+ *lemma* category_theory.unmop_mop
- \+ *def* quiver.hom.mop
- \+ *def* quiver.hom.unmop



## [2021-05-14 12:02:30](https://github.com/leanprover-community/mathlib/commit/cc1690e)
feat(analysis/calculus/parametric_integral): derivative of parametric integrals ([#7437](https://github.com/leanprover-community/mathlib/pull/7437))
from the sphere eversion project
#### Estimated changes
Added src/analysis/calculus/parametric_integral.lean
- \+ *lemma* has_deriv_at_of_dominated_loc_of_deriv_le
- \+ *lemma* has_deriv_at_of_dominated_loc_of_lip
- \+ *lemma* has_fderiv_at_of_dominated_loc_of_lip'
- \+ *lemma* has_fderiv_at_of_dominated_loc_of_lip
- \+ *lemma* has_fderiv_at_of_dominated_of_fderiv_le

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.coe_of_real_le
- \+ *lemma* real.nnabs_of_nonneg



## [2021-05-14 09:48:30](https://github.com/leanprover-community/mathlib/commit/1199a3d)
feat(analysis/special_functions/exp_log): strengthen statement of `continuous_log'` ([#7607](https://github.com/leanprover-community/mathlib/pull/7607))
The proof of `continuous (λ x : {x : ℝ // 0 < x}, log x)` also works for `continuous (λ x : {x : ℝ // x ≠ 0}, log x)`.
I keep the preexisting lemma as well since it is used in a number of places and seems generally useful.
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* real.continuous_log



## [2021-05-14 09:48:29](https://github.com/leanprover-community/mathlib/commit/3c77167)
feat(linear_algebra/dual): generalize from field to ring ([#7599](https://github.com/leanprover-community/mathlib/pull/7599))
#### Estimated changes
Modified src/linear_algebra/dual.lean
- \+/\- *lemma* basis.coe_to_dual_self
- \+/\- *def* basis.dual_basis
- \+/\- *lemma* basis.dual_basis_apply
- \+/\- *lemma* basis.dual_basis_equiv_fun
- \+/\- *lemma* basis.dual_basis_repr
- \+/\- *theorem* basis.dual_dim_eq
- \+ *def* basis.eval_equiv
- \+ *lemma* basis.eval_equiv_to_linear_map
- \+ *theorem* basis.eval_ker
- \+ *lemma* basis.eval_range
- \+/\- *def* basis.to_dual
- \+/\- *lemma* basis.to_dual_apply_left
- \+/\- *lemma* basis.to_dual_apply_right
- \+/\- *lemma* basis.to_dual_eq_equiv_fun
- \+/\- *lemma* basis.to_dual_eq_repr
- \+/\- *def* basis.to_dual_equiv
- \+/\- *def* basis.to_dual_flip
- \+/\- *lemma* basis.to_dual_flip_apply
- \+/\- *lemma* basis.to_dual_inj
- \+/\- *theorem* basis.to_dual_ker
- \+/\- *theorem* basis.to_dual_range
- \+/\- *lemma* basis.to_dual_total_left
- \+/\- *lemma* basis.to_dual_total_right
- \+/\- *lemma* basis.total_coord
- \+/\- *lemma* basis.total_dual_basis
- \+/\- *def* dual_pair.basis
- \+/\- *def* dual_pair.coeffs
- \+/\- *lemma* dual_pair.coeffs_apply
- \+/\- *lemma* dual_pair.coeffs_lc
- \+/\- *lemma* dual_pair.dual_lc
- \+/\- *def* dual_pair.lc
- \+/\- *lemma* dual_pair.lc_coeffs
- \+/\- *lemma* dual_pair.lc_def
- \+/\- *lemma* dual_pair.mem_of_mem_span



## [2021-05-14 04:49:59](https://github.com/leanprover-community/mathlib/commit/840db09)
chore(category_theory/groupoid): remove unnecessary imports ([#7600](https://github.com/leanprover-community/mathlib/pull/7600))
#### Estimated changes
Modified src/category_theory/core.lean


Modified src/category_theory/epi_mono.lean
- \+ *def* category_theory.groupoid.of_trunc_split_mono

Modified src/category_theory/groupoid.lean
- \- *def* category_theory.groupoid.of_trunc_split_mono



## [2021-05-14 04:49:58](https://github.com/leanprover-community/mathlib/commit/3124e1d)
feat(data/finset/lattice): choice-free le_sup_iff and lt_sup_iff ([#7584](https://github.com/leanprover-community/mathlib/pull/7584))
Propagate to `finset` the change to `le_sup_iff [is_total α (≤)]` and `lt_sup_iff [is_total α (≤)]` made in [#7455](https://github.com/leanprover-community/mathlib/pull/7455).
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+/\- *lemma* finset.le_sup_iff
- \+/\- *lemma* finset.lt_sup_iff



## [2021-05-14 04:49:57](https://github.com/leanprover-community/mathlib/commit/bf2750e)
chore(order/atoms): ask for the correct instances ([#7582](https://github.com/leanprover-community/mathlib/pull/7582))
replace bounded_lattice by order_bot/order_top where it can
#### Estimated changes
Modified src/order/atoms.lean
- \+/\- *lemma* is_atom_dual_iff_is_coatom
- \+/\- *theorem* is_atomic_dual_iff_is_coatomic
- \+/\- *theorem* is_atomic_iff_forall_is_atomic_Iic
- \+/\- *lemma* is_coatom_dual_iff_is_atom
- \+/\- *theorem* is_coatomic_dual_iff_is_atomic
- \+/\- *theorem* is_coatomic_iff_forall_is_coatomic_Ici
- \+/\- *lemma* order_iso.is_atom_iff
- \+/\- *lemma* order_iso.is_atomic_iff
- \+/\- *lemma* order_iso.is_coatom_iff
- \+/\- *lemma* order_iso.is_coatomic_iff
- \+/\- *lemma* order_iso.is_simple_lattice
- \+/\- *lemma* order_iso.is_simple_lattice_iff



## [2021-05-14 04:49:56](https://github.com/leanprover-community/mathlib/commit/8829c0d)
feat(algebra/homology): flipping double complexes ([#7482](https://github.com/leanprover-community/mathlib/pull/7482))
#### Estimated changes
Added src/algebra/homology/flip.lean
- \+ *def* homological_complex.flip
- \+ *def* homological_complex.flip_equivalence
- \+ *def* homological_complex.flip_equivalence_counit_iso
- \+ *def* homological_complex.flip_equivalence_unit_iso
- \+ *def* homological_complex.flip_obj



## [2021-05-14 04:49:55](https://github.com/leanprover-community/mathlib/commit/722b5fc)
feat(algebra/homology): homological complexes are the same as differential objects ([#7481](https://github.com/leanprover-community/mathlib/pull/7481))
#### Estimated changes
Added src/algebra/homology/differential_object.lean
- \+ *def* homological_complex.dgo_equiv_homological_complex
- \+ *def* homological_complex.dgo_equiv_homological_complex_counit_iso
- \+ *def* homological_complex.dgo_equiv_homological_complex_unit_iso
- \+ *def* homological_complex.dgo_to_homological_complex
- \+ *def* homological_complex.homological_complex_to_dgo



## [2021-05-14 04:49:54](https://github.com/leanprover-community/mathlib/commit/f5327c9)
feat(algebra/homology): definition of quasi_iso ([#7479](https://github.com/leanprover-community/mathlib/pull/7479))
#### Estimated changes
Added src/algebra/homology/quasi_iso.lean




## [2021-05-14 01:13:30](https://github.com/leanprover-community/mathlib/commit/239908e)
feat(ring_theory/ideal/operations): add apply_coe_mem_map ([#7566](https://github.com/leanprover-community/mathlib/pull/7566))
This is a continuation of [#7459](https://github.com/leanprover-community/mathlib/pull/7459). In this PR:
- We modify `ideal.mem_map_of_mem` in order to be consistent with `submonoid.mem_map_of_mem`.
- We modify `submonoid.apply_coe_mem_map` (and friends) to have the submonoid as an explicit variable. This was the case before [#7459](https://github.com/leanprover-community/mathlib/pull/7459) (but with a different, and not consistent, name). It seems to me that this version makes the code more readable.
- We add `ideal.apply_coe_mem_map` (similar to `submonoid.apply_coe_mem_map`).
Note that `mem_map_of_mem` is used in other places, for example we have `multiset.mem_map_of_mem`, but since a multiset is not a type there is no `apply_coe_mem_map` to add there.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+/\- *lemma* subgroup.apply_coe_mem_map

Modified src/group_theory/submonoid/operations.lean
- \+/\- *lemma* submonoid.apply_coe_mem_map

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.apply_coe_mem_map
- \+/\- *theorem* ideal.mem_map_of_mem

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
- \+/\- *lemma* galois_connection.l_Sup
- \+/\- *lemma* galois_connection.u_Inf
- \+/\- *def* galois_connection
- \+/\- *lemma* galois_insertion.strict_mono_u
- \+/\- *lemma* nat.galois_connection_mul_div



## [2021-05-13 15:18:23](https://github.com/leanprover-community/mathlib/commit/ce45594)
feat(algebra/homology/single): chain complexes supported in a single degree ([#7477](https://github.com/leanprover-community/mathlib/pull/7477))
#### Estimated changes
Modified src/algebra/homology/homological_complex.lean


Added src/algebra/homology/single.lean
- \+ *def* chain_complex.homology_functor_0_single₀
- \+ *def* chain_complex.homology_functor_succ_single₀
- \+ *def* chain_complex.single₀
- \+ *def* chain_complex.single₀_iso_single
- \+ *lemma* chain_complex.single₀_map_f_0
- \+ *lemma* chain_complex.single₀_map_f_succ
- \+ *lemma* chain_complex.single₀_obj_X_0
- \+ *lemma* chain_complex.single₀_obj_X_d
- \+ *lemma* chain_complex.single₀_obj_X_d_from
- \+ *lemma* chain_complex.single₀_obj_X_d_to
- \+ *lemma* chain_complex.single₀_obj_X_succ
- \+ *def* chain_complex.to_single₀_equiv
- \+ *def* homological_complex.single
- \+ *lemma* homological_complex.single_map_f_self
- \+ *def* homological_complex.single_obj_X_self

Modified src/category_theory/fully_faithful.lean
- \+ *def* category_theory.full.of_iso



## [2021-05-13 13:44:39](https://github.com/leanprover-community/mathlib/commit/c5faead)
feat(category_theory/preadditive/functor_category): preadditive instance for C \func D ([#7533](https://github.com/leanprover-community/mathlib/pull/7533))
#### Estimated changes
Modified src/category_theory/preadditive/default.lean
- \+/\- *lemma* category_theory.preadditive.comp_gsmul
- \+ *def* category_theory.preadditive.comp_hom
- \+/\- *lemma* category_theory.preadditive.comp_neg
- \+ *lemma* category_theory.preadditive.comp_nsmul
- \+/\- *lemma* category_theory.preadditive.comp_sub
- \+/\- *lemma* category_theory.preadditive.comp_sum
- \+/\- *lemma* category_theory.preadditive.gsmul_comp
- \+/\- *lemma* category_theory.preadditive.neg_comp
- \+/\- *lemma* category_theory.preadditive.neg_comp_neg
- \+ *lemma* category_theory.preadditive.nsmul_comp
- \+/\- *lemma* category_theory.preadditive.sub_comp
- \+/\- *lemma* category_theory.preadditive.sum_comp

Added src/category_theory/preadditive/functor_category.lean
- \+ *lemma* category_theory.nat_trans.app_add
- \+ *lemma* category_theory.nat_trans.app_gsmul
- \+ *def* category_theory.nat_trans.app_hom
- \+ *lemma* category_theory.nat_trans.app_neg
- \+ *lemma* category_theory.nat_trans.app_nsmul
- \+ *lemma* category_theory.nat_trans.app_sub
- \+ *lemma* category_theory.nat_trans.app_sum
- \+ *lemma* category_theory.nat_trans.app_zero



## [2021-05-12 16:37:46](https://github.com/leanprover-community/mathlib/commit/43bd924)
feat(topology/category/Profinite): iso_equiv_homeo ([#7529](https://github.com/leanprover-community/mathlib/pull/7529))
From LTE
#### Estimated changes
Modified src/topology/category/Profinite/default.lean
- \+/\- *def* Fintype.to_Profinite
- \+ *def* Profinite.homeo_of_iso
- \+/\- *lemma* Profinite.is_closed_map
- \+/\- *lemma* Profinite.is_iso_of_bijective
- \+ *def* Profinite.iso_equiv_homeo
- \+ *def* Profinite.iso_of_homeo



## [2021-05-12 15:10:58](https://github.com/leanprover-community/mathlib/commit/08f4404)
refactor(ring_theory/perfection): remove coercion in the definition of the type ([#7583](https://github.com/leanprover-community/mathlib/pull/7583))
Defining the type `ring.perfection R p` as a plain subtype (but inheriting the semiring or ring instances from a `subsemiring` structure) removes several coercions and helps Lean a lot when elaborating or unifying.
#### Estimated changes
Modified src/ring_theory/perfection.lean
- \+/\- *def* ring.perfection
- \+ *def* ring.perfection_subring
- \+ *def* ring.perfection_subsemiring



## [2021-05-12 10:02:56](https://github.com/leanprover-community/mathlib/commit/6b62b9f)
refactor(algebra/module): rename `smul_injective hx` to `smul_left_injective M hx` ([#7577](https://github.com/leanprover-community/mathlib/pull/7577))
This is a follow-up PR to [#7548](https://github.com/leanprover-community/mathlib/pull/7548).
 * Now that there is also a `smul_right_injective`, we should disambiguate the previous `smul_injective` to `smul_left_injective`.
 * The `M` parameter can't be inferred from arguments before the colon, so we make it explicit in `smul_left_injective` and `smul_right_injective`.
#### Estimated changes
Modified src/algebra/algebra/tower.lean


Modified src/algebra/module/basic.lean
- \- *lemma* smul_injective
- \+ *lemma* smul_left_injective

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


Added src/data/finsupp/antidiagonal.lean
- \+ *def* finsupp.Iic_finset
- \+ *def* finsupp.antidiagonal
- \+ *lemma* finsupp.antidiagonal_support_filter_fst_eq
- \+ *lemma* finsupp.antidiagonal_support_filter_snd_eq
- \+ *lemma* finsupp.antidiagonal_zero
- \+ *lemma* finsupp.coe_Iic_finset
- \+ *lemma* finsupp.finite_le_nat
- \+ *lemma* finsupp.finite_lt_nat
- \+ *lemma* finsupp.mem_Iic_finset
- \+ *lemma* finsupp.mem_antidiagonal_support
- \+ *lemma* finsupp.prod_antidiagonal_support_swap
- \+ *lemma* finsupp.swap_mem_antidiagonal_support

Modified src/data/finsupp/basic.lean
- \- *def* finsupp.Iic_finset
- \- *def* finsupp.antidiagonal
- \- *lemma* finsupp.antidiagonal_support_filter_fst_eq
- \- *lemma* finsupp.antidiagonal_support_filter_snd_eq
- \- *lemma* finsupp.antidiagonal_zero
- \- *lemma* finsupp.coe_Iic_finset
- \- *lemma* finsupp.finite_le_nat
- \- *lemma* finsupp.finite_lt_nat
- \- *lemma* finsupp.mem_Iic_finset
- \- *lemma* finsupp.mem_antidiagonal_support
- \- *lemma* finsupp.prod_antidiagonal_support_swap
- \- *lemma* finsupp.swap_mem_antidiagonal_support

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
- \+ *lemma* localization.local_ring_hom_mk'
- \+ *lemma* localization.local_ring_hom_to_map
- \+ *lemma* localization.local_ring_hom_unique
- \+ *lemma* localization_map.map_unique



## [2021-05-11 14:57:06](https://github.com/leanprover-community/mathlib/commit/b746e82)
feat(linear_algebra/finsupp): adjust apply lemma for `finsupp.dom_lcongr` ([#7549](https://github.com/leanprover-community/mathlib/pull/7549))
This is a split-off dependency from [#7496](https://github.com/leanprover-community/mathlib/pull/7496).
#### Estimated changes
Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/finsupp.lean
- \+/\- *lemma* finsupp.dom_lcongr_apply



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
- \- *def* category_theory.functor.map_homological_complex
- \- *def* category_theory.functor.pushforward_homological_complex
- \- *lemma* homological_complex.comm
- \- *lemma* homological_complex.comm_at
- \- *lemma* homological_complex.d_squared
- \- *lemma* homological_complex.eq_to_hom_d
- \- *lemma* homological_complex.eq_to_hom_f

Added src/algebra/homology/complex_shape.lean
- \+ *def* complex_shape.down'
- \+ *def* complex_shape.down
- \+ *def* complex_shape.next
- \+ *lemma* complex_shape.next_eq_some
- \+ *def* complex_shape.prev
- \+ *lemma* complex_shape.prev_eq_some
- \+ *def* complex_shape.refl
- \+ *def* complex_shape.symm
- \+ *lemma* complex_shape.symm_symm
- \+ *def* complex_shape.trans
- \+ *def* complex_shape.up'
- \+ *def* complex_shape.up

Modified src/algebra/homology/exact.lean
- \+ *lemma* category_theory.comp_eq_zero_of_image_eq_kernel
- \+ *lemma* category_theory.epi_iff_exact_zero_right
- \- *lemma* category_theory.exact_comp_hom_inv_comp
- \+ *lemma* category_theory.exact_comp_iso
- \+ *lemma* category_theory.exact_iso_comp
- \- *lemma* category_theory.exact_kernel
- \+ *lemma* category_theory.exact_kernel_subobject_arrow
- \+ *lemma* category_theory.exact_kernel_ι
- \+ *lemma* category_theory.exact_of_image_eq_kernel
- \- *lemma* category_theory.exact_of_zero
- \+ *lemma* category_theory.image_to_kernel_is_iso_of_image_eq_kernel
- \+ *lemma* category_theory.kernel_subobject_arrow_eq_zero_of_exact_zero_left
- \+/\- *lemma* category_theory.kernel_ι_eq_zero_of_exact_zero_left
- \+ *lemma* category_theory.mono_iff_exact_zero_left
- \+ *lemma* category_theory.preadditive.exact_iff_homology_zero

Added src/algebra/homology/homological_complex.lean
- \+ *def* chain_complex.mk'
- \+ *lemma* chain_complex.mk'_X_0
- \+ *lemma* chain_complex.mk'_X_1
- \+ *lemma* chain_complex.mk'_d_1_0
- \+ *def* chain_complex.mk
- \+ *lemma* chain_complex.mk_X_0
- \+ *lemma* chain_complex.mk_X_1
- \+ *lemma* chain_complex.mk_X_2
- \+ *def* chain_complex.mk_aux
- \+ *lemma* chain_complex.mk_d_1_0
- \+ *lemma* chain_complex.mk_d_2_0
- \+ *def* chain_complex.mk_hom
- \+ *def* chain_complex.mk_hom_aux
- \+ *lemma* chain_complex.mk_hom_f_0
- \+ *lemma* chain_complex.mk_hom_f_1
- \+ *lemma* chain_complex.mk_hom_f_succ_succ
- \+ *def* chain_complex.mk_struct.flat
- \+ *lemma* chain_complex.next
- \+ *lemma* chain_complex.next_nat_succ
- \+ *lemma* chain_complex.next_nat_zero
- \+ *def* chain_complex.of
- \+ *lemma* chain_complex.of_X
- \+ *lemma* chain_complex.of_d
- \+ *lemma* chain_complex.prev
- \+ *lemma* cochain_complex.next
- \+ *lemma* cochain_complex.prev
- \+ *lemma* cochain_complex.prev_nat_succ
- \+ *lemma* cochain_complex.prev_nat_zero
- \+ *def* homological_complex.X_next
- \+ *def* homological_complex.X_next_iso
- \+ *def* homological_complex.X_next_iso_zero
- \+ *def* homological_complex.X_prev
- \+ *def* homological_complex.X_prev_iso
- \+ *lemma* homological_complex.X_prev_iso_comp_d_to
- \+ *def* homological_complex.X_prev_iso_zero
- \+ *lemma* homological_complex.X_prev_iso_zero_comp_d_to
- \+ *def* homological_complex.comp
- \+ *lemma* homological_complex.comp_f
- \+ *lemma* homological_complex.congr_hom
- \+ *lemma* homological_complex.d_comp_eq_to_hom
- \+ *def* homological_complex.d_from
- \+ *lemma* homological_complex.d_from_comp_X_next_iso
- \+ *lemma* homological_complex.d_from_comp_X_next_iso_zero
- \+ *lemma* homological_complex.d_from_eq
- \+ *lemma* homological_complex.d_from_eq_zero
- \+ *def* homological_complex.d_to
- \+ *lemma* homological_complex.d_to_comp_d_from
- \+ *lemma* homological_complex.d_to_eq
- \+ *lemma* homological_complex.d_to_eq_zero
- \+ *lemma* homological_complex.eq_to_hom_comp_d
- \+ *def* homological_complex.eval_at
- \+ *lemma* homological_complex.hom.comm_from
- \+ *lemma* homological_complex.hom.comm_to
- \+ *def* homological_complex.hom.next
- \+ *lemma* homological_complex.hom.next_eq
- \+ *def* homological_complex.hom.prev
- \+ *lemma* homological_complex.hom.prev_eq
- \+ *def* homological_complex.hom.sq_from
- \+ *lemma* homological_complex.hom.sq_from_comp
- \+ *lemma* homological_complex.hom.sq_from_id
- \+ *lemma* homological_complex.hom.sq_from_left
- \+ *lemma* homological_complex.hom.sq_from_right
- \+ *def* homological_complex.hom.sq_to
- \+ *lemma* homological_complex.hom.sq_to_left
- \+ *lemma* homological_complex.hom.sq_to_right
- \+ *lemma* homological_complex.hom_f_injective
- \+ *def* homological_complex.id
- \+ *lemma* homological_complex.id_f
- \+ *lemma* homological_complex.image_eq_image
- \+ *lemma* homological_complex.image_to_eq_image
- \+ *lemma* homological_complex.kernel_eq_kernel
- \+ *lemma* homological_complex.kernel_from_eq_kernel
- \+ *lemma* homological_complex.zero_apply

Modified src/algebra/homology/homology.lean
- \+ *def* boundaries_functor
- \+ *def* boundaries_to_cycles_nat_trans
- \+ *lemma* boundaries_to_cycles_naturality
- \+ *def* cycles_functor
- \+ *lemma* cycles_map_arrow
- \+ *lemma* cycles_map_comp
- \+ *lemma* cycles_map_id
- \+ *def* graded_homology_functor
- \+ *lemma* homological_complex.boundaries_eq_bot
- \+ *lemma* homological_complex.boundaries_eq_image_subobject
- \+ *def* homological_complex.boundaries_iso_image
- \+ *lemma* homological_complex.boundaries_le_cycles
- \+ *lemma* homological_complex.boundaries_to_cycles_arrow
- \+ *def* homological_complex.cycles
- \+ *lemma* homological_complex.cycles_arrow_d_from
- \+ *lemma* homological_complex.cycles_eq_kernel_subobject
- \+ *lemma* homological_complex.cycles_eq_top
- \+ *def* homological_complex.cycles_iso_kernel
- \- *def* homological_complex.graded_homology
- \- *def* homological_complex.homology
- \- *def* homological_complex.homology_group
- \- *def* homological_complex.homology_map
- \- *lemma* homological_complex.homology_map_comp
- \- *lemma* homological_complex.homology_map_condition
- \- *lemma* homological_complex.homology_map_id
- \- *lemma* homological_complex.image_map_ι
- \+ *lemma* homological_complex.image_to_kernel_as_boundaries_to_cycles
- \- *def* homological_complex.image_to_kernel_map
- \- *lemma* homological_complex.image_to_kernel_map_comp_kernel_map
- \- *lemma* homological_complex.image_to_kernel_map_condition
- \- *def* homological_complex.kernel_functor
- \- *def* homological_complex.kernel_map
- \- *lemma* homological_complex.kernel_map_comp
- \- *lemma* homological_complex.kernel_map_condition
- \- *lemma* homological_complex.kernel_map_id
- \+ *def* homology_functor

Added src/algebra/homology/image_to_kernel.lean
- \+ *lemma* factor_thru_image_subobject_comp_image_to_kernel
- \+ *lemma* homology.condition
- \+ *def* homology.congr
- \+ *def* homology.desc
- \+ *lemma* homology.ext
- \+ *def* homology.map
- \+ *lemma* homology.map_desc
- \+ *def* homology.π
- \+ *lemma* homology.π_desc
- \+ *lemma* homology.π_map
- \+ *def* homology
- \+ *def* homology_zero_zero
- \+ *lemma* image_le_kernel
- \+ *lemma* image_subobject_map_comp_image_to_kernel
- \+ *def* image_to_kernel
- \+ *lemma* image_to_kernel_arrow
- \+ *lemma* image_to_kernel_comp_hom_inv_comp
- \+ *lemma* image_to_kernel_comp_left
- \+ *lemma* image_to_kernel_comp_mono
- \+ *lemma* image_to_kernel_comp_right
- \+ *lemma* image_to_kernel_epi_comp
- \+ *lemma* image_to_kernel_zero_left
- \+ *lemma* image_to_kernel_zero_right
- \+ *lemma* subobject_of_le_as_image_to_kernel

Deleted src/algebra/homology/image_to_kernel_map.lean
- \- *lemma* category_theory.image_to_kernel_map_comp_hom_inv_comp
- \- *lemma* category_theory.image_to_kernel_map_comp_iso
- \- *lemma* category_theory.image_to_kernel_map_comp_left
- \- *lemma* category_theory.image_to_kernel_map_comp_right
- \- *lemma* category_theory.image_to_kernel_map_epi_of_epi_of_zero
- \- *lemma* category_theory.image_to_kernel_map_epi_of_zero_of_mono
- \- *lemma* category_theory.image_to_kernel_map_iso_comp
- \- *lemma* category_theory.image_to_kernel_map_zero_left
- \- *lemma* category_theory.image_to_kernel_map_zero_right

Modified src/category_theory/abelian/exact.lean
- \- *lemma* category_theory.abelian.epi_iff_exact_zero_right
- \+ *theorem* category_theory.abelian.exact_iff''
- \+ *theorem* category_theory.abelian.exact_tfae
- \- *lemma* category_theory.abelian.mono_iff_exact_zero_left



## [2021-05-11 07:41:52](https://github.com/leanprover-community/mathlib/commit/12c9ddf)
feat(set_theory/{pgame, surreal}): add `left_distrib_equiv` and `right_distrib_equiv` for pgames ([#7440](https://github.com/leanprover-community/mathlib/pull/7440))
and several other auxiliary lemmas.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Surreal.20numbers)
#### Estimated changes
Modified src/set_theory/game.lean
- \+/\- *theorem* game.le_refl
- \+/\- *theorem* game.le_trans
- \+ *lemma* game.quot_add
- \+ *lemma* game.quot_neg
- \+ *lemma* game.quot_sub
- \- *def* game

Modified src/set_theory/pgame.lean
- \+ *theorem* pgame.add_right_neg_equiv
- \+ *theorem* pgame.equiv_of_mk_equiv
- \+ *theorem* pgame.sub_congr

Modified src/set_theory/surreal.lean
- \- *def* pgame.add_comm_sub_relabelling
- \- *def* pgame.add_sub_relabelling
- \+ *theorem* pgame.left_distrib_equiv
- \+ *lemma* pgame.left_distrib_equiv_aux'
- \+ *lemma* pgame.left_distrib_equiv_aux
- \+/\- *theorem* pgame.mul_comm_equiv
- \+/\- *theorem* pgame.mul_zero_equiv
- \+ *theorem* pgame.right_distrib_equiv
- \+/\- *theorem* pgame.zero_mul_equiv



## [2021-05-11 05:55:39](https://github.com/leanprover-community/mathlib/commit/ca4024b)
feat(algebraic_topology/cech_nerve): Adds a definition of the Cech nerve associated to an arrow. ([#7547](https://github.com/leanprover-community/mathlib/pull/7547))
Also adds a definition of augmented simplicial objects as a comma category.
#### Estimated changes
Added src/algebraic_topology/cech_nerve.lean
- \+ *def* category_theory.arrow.augmented_cech_nerve
- \+ *def* category_theory.arrow.cech_nerve
- \+ *def* simplicial_object.augmented_cech_nerve
- \+ *def* simplicial_object.cech_nerve

Modified src/algebraic_topology/simplicial_object.lean
- \+ *def* category_theory.simplicial_object.augmented

Modified src/category_theory/limits/shapes/wide_pullbacks.lean




## [2021-05-11 04:39:37](https://github.com/leanprover-community/mathlib/commit/8dc848c)
feat(ring_theory/finiteness): add finite_type_iff_group_fg ([#7569](https://github.com/leanprover-community/mathlib/pull/7569))
We add here a simple modification of `monoid_algebra.fg_of_finite_type`: a group algebra is of finite type if and only if the group is finitely generated (as group opposed to as monoid).
#### Estimated changes
Modified src/ring_theory/finiteness.lean
- \+ *lemma* add_monoid_algebra.finite_type_iff_group_fg
- \+ *lemma* monoid_algebra.finite_type_iff_group_fg



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
- \+ *def* hahn_series.emb_domain
- \+ *def* hahn_series.emb_domain_alg_hom
- \+ *lemma* hahn_series.emb_domain_coeff
- \+ *lemma* hahn_series.emb_domain_injective
- \+ *def* hahn_series.emb_domain_linear_map
- \+ *lemma* hahn_series.emb_domain_mk_coeff
- \+ *lemma* hahn_series.emb_domain_notin_image_support
- \+ *lemma* hahn_series.emb_domain_notin_range
- \+ *def* hahn_series.emb_domain_ring_hom
- \+ *lemma* hahn_series.emb_domain_ring_hom_C
- \+ *lemma* hahn_series.emb_domain_single
- \+ *lemma* hahn_series.emb_domain_zero
- \+ *def* hahn_series.of_power_series
- \+ *def* hahn_series.of_power_series_alg
- \+ *lemma* hahn_series.support_emb_domain_subset



## [2021-05-10 22:45:43](https://github.com/leanprover-community/mathlib/commit/81c98d5)
feat(ring_theory/hahn_series): Hahn series form a field ([#7495](https://github.com/leanprover-community/mathlib/pull/7495))
Uses Higman's Lemma to define `summable_family.powers`, a summable family consisting of the powers of a Hahn series of positive valuation
Uses `summable_family.powers` to define inversion on Hahn series over a field and linear-ordered value group, making the type of Hahn series a field.
Shows that a Hahn series over an integral domain and linear-ordered value group  `is_unit` if and only if its lowest coefficient is.
#### Estimated changes
Modified src/order/well_founded_set.lean
- \+ *lemma* set.is_pwo.submonoid_closure
- \- *theorem* set.partially_well_ordered_on.image_of_monotone
- \+ *theorem* set.partially_well_ordered_on.image_of_monotone_on
- \+ *lemma* set.well_founded_on.induction

Modified src/ring_theory/hahn_series.lean
- \+ *lemma* hahn_series.is_pwo_Union_support_powers
- \+ *lemma* hahn_series.is_unit_iff
- \+ *lemma* hahn_series.summable_family.coe_powers
- \+ *lemma* hahn_series.summable_family.emb_domain_succ_smul_powers
- \+ *lemma* hahn_series.summable_family.one_sub_self_mul_hsum_powers
- \+ *def* hahn_series.summable_family.powers
- \+ *lemma* hahn_series.unit_aux



## [2021-05-10 22:45:42](https://github.com/leanprover-community/mathlib/commit/1cbb31d)
feat(analysis/normed_space/normed_group_hom): add lemmas ([#7474](https://github.com/leanprover-community/mathlib/pull/7474))
From LTE.
Written by @PatrickMassot 
- [x] depends on: [#7459](https://github.com/leanprover-community/mathlib/pull/7459)
#### Estimated changes
Modified src/analysis/normed_space/normed_group_hom.lean
- \+ *lemma* normed_group_hom.comp_range
- \+ *lemma* normed_group_hom.incl_range
- \+ *lemma* normed_group_hom.norm_incl
- \+ *lemma* normed_group_hom.range_comp_incl_top



## [2021-05-10 16:44:24](https://github.com/leanprover-community/mathlib/commit/b7ab74a)
feat(algebra/lie/weights): add lemma `root_space_comap_eq_weight_space` ([#7565](https://github.com/leanprover-community/mathlib/pull/7565))
#### Estimated changes
Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* lie_subalgebra.coe_incl'
- \+ *lemma* lie_subalgebra.coe_incl
- \+ *def* lie_subalgebra.incl'
- \+/\- *def* lie_subalgebra.incl

Modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_submodule.mem_comap

Modified src/algebra/lie/weights.lean
- \+ *lemma* lie_algebra.root_space_comap_eq_weight_space
- \+/\- *lemma* lie_module.coe_weight_space_of_top



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
- \+ *theorem* int.sign_pow_bit1



## [2021-05-10 16:44:21](https://github.com/leanprover-community/mathlib/commit/3417ee0)
chore(deprecated/group): relax monoid to mul_one_class ([#7556](https://github.com/leanprover-community/mathlib/pull/7556))
This fixes an annoyance where `monoid_hom.is_monoid_hom` didn't work on non-associative monoids.
#### Estimated changes
Modified src/data/dfinsupp.lean


Modified src/deprecated/group.lean
- \+/\- *lemma* additive.is_add_monoid_hom
- \+/\- *lemma* is_monoid_hom.comp
- \+/\- *theorem* is_monoid_hom.of_mul
- \+/\- *lemma* multiplicative.is_monoid_hom



## [2021-05-10 16:44:20](https://github.com/leanprover-community/mathlib/commit/477af65)
feat(category_theory/limits/shapes/wide_pullbacks): Adds some wrappers around the (co)limit api for wide pullbacks/pushouts ([#7546](https://github.com/leanprover-community/mathlib/pull/7546))
This PR adds some wrappers (mostly abbreviations) around the (co)limit api specifically for wide pullbacks and wide pushouts.
#### Estimated changes
Modified src/category_theory/limits/shapes/wide_pullbacks.lean
- \+ *lemma* category_theory.limits.wide_pullback.eq_lift_of_comp_eq
- \+ *lemma* category_theory.limits.wide_pullback.hom_eq_lift
- \+ *lemma* category_theory.limits.wide_pullback.hom_ext
- \+ *lemma* category_theory.limits.wide_pullback.lift_base
- \+ *lemma* category_theory.limits.wide_pullback.lift_π
- \+ *lemma* category_theory.limits.wide_pullback.π_arrow
- \+ *lemma* category_theory.limits.wide_pushout.arrow_ι
- \+ *lemma* category_theory.limits.wide_pushout.eq_desc_of_comp_eq
- \+ *lemma* category_theory.limits.wide_pushout.head_desc
- \+ *lemma* category_theory.limits.wide_pushout.hom_eq_desc
- \+ *lemma* category_theory.limits.wide_pushout.hom_ext
- \+ *lemma* category_theory.limits.wide_pushout.ι_desc



## [2021-05-10 16:44:19](https://github.com/leanprover-community/mathlib/commit/92395fd)
feat(data/list/rotate): is_rotated ([#7299](https://github.com/leanprover-community/mathlib/pull/7299))
`is_rotated l₁ l₂` or `l₁ ~r l₂` asserts that `l₁` and `l₂` are cyclic permutations
  of each other. This is defined by claiming that `∃ n, l.rotate n = l'`.
#### Estimated changes
Modified src/data/list/rotate.lean
- \+ *lemma* list.is_rotated.eqv
- \+ *lemma* list.is_rotated.mem_iff
- \+ *lemma* list.is_rotated.nodup_iff
- \+ *lemma* list.is_rotated.perm
- \+ *lemma* list.is_rotated.refl
- \+ *lemma* list.is_rotated.reverse
- \+ *def* list.is_rotated.setoid
- \+ *lemma* list.is_rotated.symm
- \+ *lemma* list.is_rotated.trans
- \+ *def* list.is_rotated
- \+ *lemma* list.is_rotated_comm
- \+ *lemma* list.is_rotated_concat
- \+ *lemma* list.is_rotated_iff_mem_map_range
- \+ *lemma* list.is_rotated_iff_mod
- \+ *lemma* list.is_rotated_nil_iff'
- \+ *lemma* list.is_rotated_nil_iff
- \+ *lemma* list.is_rotated_reverse_comm_iff
- \+ *lemma* list.is_rotated_reverse_iff
- \+ *lemma* list.nodup_rotate
- \+ *lemma* list.nth_le_rotate
- \+ *lemma* list.nth_le_rotate_one
- \+ *lemma* list.reverse_rotate
- \+ *lemma* list.rotate'_eq_drop_append_take
- \- *lemma* list.rotate'_eq_take_append_drop
- \+ *lemma* list.rotate_eq_drop_append_take
- \+ *lemma* list.rotate_eq_drop_append_take_mod
- \+ *lemma* list.rotate_eq_iff
- \+ *lemma* list.rotate_eq_nil_iff
- \+ *lemma* list.rotate_eq_rotate
- \- *lemma* list.rotate_eq_take_append_drop
- \+ *lemma* list.rotate_injective
- \+ *lemma* list.rotate_perm
- \+ *lemma* list.rotate_singleton
- \+ *lemma* list.zip_with_rotate_distrib
- \+ *lemma* list.zip_with_rotate_one



## [2021-05-10 13:15:31](https://github.com/leanprover-community/mathlib/commit/41c7b1e)
chore(category_theory/Fintype): remove redundant lemmas ([#7531](https://github.com/leanprover-community/mathlib/pull/7531))
These lemmas exist for arbitrary concrete categories.
- [x] depends on: [#7530](https://github.com/leanprover-community/mathlib/pull/7530)
#### Estimated changes
Modified src/category_theory/Fintype.lean
- \- *lemma* Fintype.coe_comp
- \- *lemma* Fintype.coe_id
- \- *lemma* Fintype.comp_apply
- \- *lemma* Fintype.id_apply



## [2021-05-10 13:15:30](https://github.com/leanprover-community/mathlib/commit/b9f4420)
feat(geometry/euclidean/triangle): add Stewart's Theorem + one similarity lemma ([#7327](https://github.com/leanprover-community/mathlib/pull/7327))
#### Estimated changes
Modified src/geometry/euclidean/triangle.lean
- \+ *lemma* euclidean_geometry.dist_mul_of_eq_angle_of_dist_mul
- \+ *theorem* euclidean_geometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
- \+ *theorem* euclidean_geometry.dist_sq_mul_dist_add_dist_sq_mul_dist



## [2021-05-10 13:15:28](https://github.com/leanprover-community/mathlib/commit/03b88c1)
feat(algebra/category/Module): Free R C, the free R-linear completion of a category ([#7177](https://github.com/leanprover-community/mathlib/pull/7177))
The free R-linear completion of a category.
#### Estimated changes
Modified src/algebra/category/Module/adjunctions.lean
- \+ *def* category_theory.Free.embedding
- \+ *def* category_theory.Free.embedding_lift_iso
- \+ *def* category_theory.Free.ext
- \+ *def* category_theory.Free.lift
- \+ *lemma* category_theory.Free.lift_map_single
- \+ *def* category_theory.Free.lift_unique
- \+ *def* category_theory.Free.of
- \+ *lemma* category_theory.Free.single_comp_single
- \+ *def* category_theory.Free

Modified src/category_theory/preadditive/additive_functor.lean
- \+ *lemma* category_theory.functor.map_gsmul

Modified src/category_theory/preadditive/default.lean
- \+ *lemma* category_theory.preadditive.comp_gsmul
- \+ *lemma* category_theory.preadditive.gsmul_comp

Modified src/linear_algebra/tensor_product.lean




## [2021-05-10 07:36:17](https://github.com/leanprover-community/mathlib/commit/48104c3)
feat(data/set/lattice): (b)Union and (b)Inter lemmas ([#7557](https://github.com/leanprover-community/mathlib/pull/7557))
from LTE
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.Union_prop
- \+ *lemma* set.Union_prop_neg
- \+ *lemma* set.Union_prop_pos
- \+ *lemma* set.bInter_inter
- \+ *lemma* set.inter_bInter
- \+ *lemma* set.mem_bUnion_iff'



## [2021-05-10 07:36:16](https://github.com/leanprover-community/mathlib/commit/b577697)
feat(data/matrix/basic): add missing smul instances, generalize lemmas to work on scalar towers ([#7544](https://github.com/leanprover-community/mathlib/pull/7544))
This also fixes the `add_monoid_hom.map_zero` etc lemmas to not require overly strong typeclasses on `α`
This removes the `matrix.smul_apply` lemma since `pi.smul_apply` and `smul_eq_mul` together replace it.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *def* add_monoid_hom.map_matrix
- \+/\- *lemma* add_monoid_hom.map_matrix_apply
- \+/\- *lemma* matrix.add_equiv_map_zero
- \+/\- *lemma* matrix.add_monoid_hom_map_zero
- \+/\- *lemma* matrix.diagonal_map
- \+/\- *lemma* matrix.dot_product_smul
- \+/\- *lemma* matrix.linear_equiv_map_zero
- \+/\- *lemma* matrix.linear_map_map_zero
- \+/\- *def* matrix.map
- \+/\- *lemma* matrix.map_add
- \+/\- *lemma* matrix.map_apply
- \+/\- *lemma* matrix.map_mul
- \+/\- *lemma* matrix.map_sub
- \+/\- *lemma* matrix.map_zero
- \+/\- *lemma* matrix.mul_smul
- \+/\- *lemma* matrix.one_map
- \+/\- *lemma* matrix.ring_equiv_map_one
- \+/\- *lemma* matrix.ring_equiv_map_zero
- \+/\- *lemma* matrix.ring_hom_map_one
- \+/\- *lemma* matrix.ring_hom_map_zero
- \- *lemma* matrix.smul_apply
- \+/\- *lemma* matrix.smul_dot_product
- \+/\- *lemma* matrix.smul_mul
- \+/\- *lemma* matrix.star_apply
- \+/\- *lemma* matrix.star_mul
- \+/\- *lemma* matrix.transpose_map
- \+/\- *lemma* matrix.zero_hom_map_zero
- \+/\- *def* ring_hom.map_matrix
- \- *lemma* ring_hom.map_matrix_apply

Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/ring_theory/matrix_algebra.lean


Modified src/ring_theory/polynomial_algebra.lean




## [2021-05-10 07:36:15](https://github.com/leanprover-community/mathlib/commit/38bf2ab)
feat(field_theory/abel_ruffini): Version of solvable_by_rad.is_solvable ([#7509](https://github.com/leanprover-community/mathlib/pull/7509))
This is a version of `solvable_by_rad.is_solvable`, which will be the final step of the abel-ruffini theorem.
#### Estimated changes
Modified src/field_theory/abel_ruffini.lean
- \+ *lemma* solvable_by_rad.is_solvable'

Modified src/field_theory/minpoly.lean
- \+ *lemma* minpoly.unique''



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
- \+/\- *theorem* is_projective.of_free

Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* basis.coe_constrL
- \+ *def* basis.constrL
- \+ *lemma* basis.constrL_apply
- \+ *lemma* basis.constrL_basis
- \+ *def* basis.equiv_funL
- \+ *lemma* basis.op_norm_le
- \+ *lemma* basis.sup_norm_le_norm
- \+/\- *lemma* continuous_equiv_fun_basis
- \- *lemma* is_basis.coe_constrL
- \- *def* is_basis.constrL
- \- *lemma* is_basis.constrL_apply
- \- *lemma* is_basis.constrL_basis
- \- *def* is_basis.equiv_funL
- \- *lemma* is_basis.op_norm_le
- \- *lemma* is_basis.sup_norm_le_norm

Modified src/analysis/normed_space/inner_product.lean
- \+ *def* basis.isometry_euclidean_of_orthonormal
- \+ *def* basis_of_orthonormal_of_card_eq_finrank
- \+ *lemma* coe_basis_of_orthonormal_of_card_eq_finrank
- \+ *lemma* coe_orthonormal_basis
- \- *lemma* exists_is_orthonormal_basis'
- \- *lemma* exists_is_orthonormal_basis
- \+ *def* fin_orthonormal_basis
- \+ *lemma* fin_orthonormal_basis_orthonormal
- \- *def* is_basis.isometry_euclidean_of_orthonormal
- \- *lemma* is_basis_of_orthonormal_of_card_eq_finrank
- \+ *lemma* maximal_orthonormal_iff_basis_of_finite_dimensional
- \- *lemma* maximal_orthonormal_iff_is_basis_of_finite_dimensional
- \+ *def* orthonormal_basis
- \+ *def* orthonormal_basis_index
- \+ *lemma* orthonormal_basis_orthonormal

Modified src/data/complex/module.lean
- \+ *def* complex.basis_one_I
- \+ *lemma* complex.coe_basis_one_I
- \+ *lemma* complex.coe_basis_one_I_repr
- \- *lemma* complex.is_basis_one_I

Modified src/field_theory/adjoin.lean
- \- *lemma* intermediate_field.power_basis_is_basis

Modified src/field_theory/mv_polynomial.lean


Modified src/field_theory/normal.lean


Modified src/field_theory/tower.lean


Modified src/linear_algebra/affine_space/independent.lean


Modified src/linear_algebra/basis.lean
- \+ *lemma* basis.apply_eq_iff
- \+ *lemma* basis.basis_singleton_iff
- \+ *lemma* basis.coe_extend
- \+ *lemma* basis.coe_mk
- \+ *lemma* basis.coe_of_equiv_fun
- \+ *lemma* basis.coe_of_repr
- \+ *lemma* basis.coe_of_vector_space
- \+ *lemma* basis.coe_reindex
- \+ *lemma* basis.coe_reindex_repr
- \+ *lemma* basis.coe_repr_symm
- \+ *def* basis.constr
- \+ *theorem* basis.constr_apply
- \+ *theorem* basis.constr_apply_fintype
- \+ *lemma* basis.constr_basis
- \+ *theorem* basis.constr_def
- \+ *lemma* basis.constr_eq
- \+ *lemma* basis.constr_range
- \+ *lemma* basis.constr_self
- \+ *def* basis.coord
- \+ *lemma* basis.empty_unique
- \+ *lemma* basis.eq_of_apply_eq
- \+ *lemma* basis.eq_of_repr_eq_repr
- \+ *def* basis.equiv'
- \+ *lemma* basis.equiv'_apply
- \+ *lemma* basis.equiv'_symm_apply
- \+ *lemma* basis.equiv_apply
- \+ *def* basis.equiv_fun
- \+ *lemma* basis.equiv_fun_apply
- \+ *lemma* basis.equiv_fun_self
- \+ *lemma* basis.equiv_fun_symm_apply
- \+ *lemma* basis.equiv_refl
- \+ *lemma* basis.equiv_symm
- \+ *lemma* basis.equiv_trans
- \+ *lemma* basis.exists_basis
- \+ *theorem* basis.ext'
- \+ *theorem* basis.ext
- \+ *theorem* basis.ext_elem
- \+ *lemma* basis.extend_apply_self
- \+ *lemma* basis.finsupp.single_apply_left
- \+ *lemma* basis.forall_coord_eq_zero_iff
- \+ *lemma* basis.map_apply
- \+ *lemma* basis.mk_apply
- \+ *lemma* basis.mk_repr
- \+ *def* basis.of_equiv_fun
- \+ *lemma* basis.of_equiv_fun_repr_apply
- \+ *lemma* basis.of_vector_space_apply_self
- \+ *lemma* basis.of_vector_space_index.linear_independent
- \+ *lemma* basis.prod_apply
- \+ *lemma* basis.prod_apply_inl_fst
- \+ *lemma* basis.prod_apply_inl_snd
- \+ *lemma* basis.prod_apply_inr_fst
- \+ *lemma* basis.prod_apply_inr_snd
- \+ *lemma* basis.prod_repr_inl
- \+ *lemma* basis.prod_repr_inr
- \+ *lemma* basis.range_extend
- \+ *lemma* basis.range_of_vector_space
- \+ *lemma* basis.range_reindex'
- \+ *lemma* basis.range_reindex
- \+ *def* basis.reindex
- \+ *lemma* basis.reindex_apply
- \+ *def* basis.reindex_range
- \+ *lemma* basis.reindex_range_apply
- \+ *lemma* basis.reindex_range_repr'
- \+ *lemma* basis.reindex_range_repr
- \+ *lemma* basis.reindex_range_repr_self
- \+ *lemma* basis.reindex_range_self
- \+ *lemma* basis.reindex_repr
- \+ *lemma* basis.repr_apply_eq
- \+ *lemma* basis.repr_eq_iff'
- \+ *lemma* basis.repr_eq_iff
- \+ *lemma* basis.repr_range
- \+ *lemma* basis.repr_self
- \+ *lemma* basis.repr_self_apply
- \+ *lemma* basis.repr_symm_apply
- \+ *lemma* basis.repr_symm_single
- \+ *lemma* basis.repr_symm_single_one
- \+ *lemma* basis.repr_total
- \+ *lemma* basis.singleton_apply
- \+ *lemma* basis.singleton_repr
- \+ *lemma* basis.subset_extend
- \+ *lemma* basis.sum_equiv_fun
- \+ *lemma* basis.sum_repr
- \+ *lemma* basis.total_repr
- \- *lemma* constr_add
- \- *lemma* constr_basis
- \- *lemma* constr_eq
- \- *lemma* constr_neg
- \- *lemma* constr_range
- \- *lemma* constr_self
- \- *lemma* constr_smul
- \- *lemma* constr_sub
- \- *lemma* constr_zero
- \- *lemma* exists_is_basis
- \- *lemma* exists_subset_is_basis
- \- *lemma* exists_sum_is_basis
- \- *lemma* is_basis.comp
- \- *def* is_basis.constr
- \- *theorem* is_basis.constr_apply
- \- *theorem* is_basis.constr_apply_fintype
- \- *def* is_basis.equiv_fun
- \- *lemma* is_basis.equiv_fun_apply
- \- *lemma* is_basis.equiv_fun_self
- \- *lemma* is_basis.equiv_fun_symm_apply
- \- *lemma* is_basis.equiv_fun_total
- \- *lemma* is_basis.ext
- \- *lemma* is_basis.ext_elem
- \- *lemma* is_basis.injective
- \- *lemma* is_basis.mem_span
- \- *lemma* is_basis.no_zero_smul_divisors
- \- *lemma* is_basis.range
- \- *lemma* is_basis.range_repr
- \- *lemma* is_basis.range_repr_self
- \- *def* is_basis.repr
- \- *lemma* is_basis.repr_apply_eq
- \- *lemma* is_basis.repr_eq_iff
- \- *lemma* is_basis.repr_eq_single
- \- *lemma* is_basis.repr_eq_zero
- \- *lemma* is_basis.repr_ker
- \- *lemma* is_basis.repr_range
- \- *lemma* is_basis.repr_self_apply
- \- *lemma* is_basis.repr_total
- \- *lemma* is_basis.smul_eq_zero
- \- *lemma* is_basis.total_comp_repr
- \- *lemma* is_basis.total_repr
- \- *def* is_basis
- \- *lemma* is_basis_empty
- \- *lemma* is_basis_inl_union_inr
- \- *lemma* is_basis_singleton_iff
- \- *lemma* is_basis_singleton_one
- \- *lemma* is_basis_span
- \- *def* linear_equiv_of_is_basis'
- \- *def* linear_equiv_of_is_basis
- \- *lemma* linear_equiv_of_is_basis_comp
- \- *lemma* linear_equiv_of_is_basis_refl
- \- *lemma* linear_equiv_of_is_basis_symm_trans
- \- *lemma* linear_equiv_of_is_basis_trans_symm
- \- *def* module_equiv_finsupp
- \- *theorem* module_equiv_finsupp_apply_basis

Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* basis.equiv_fun_symm_std_basis
- \+/\- *lemma* bilin_form.comp_left_injective
- \+/\- *lemma* bilin_form.is_adjoint_pair_unique_of_nondegenerate
- \+/\- *lemma* bilin_form.le_orthogonal_orthogonal
- \+/\- *lemma* bilin_form.restrict_sym
- \+/\- *lemma* bilin_form.to_dual_def
- \+ *lemma* bilin_form.to_matrix_basis_fun
- \- *lemma* bilin_form.to_matrix_is_basis_fun
- \- *lemma* is_basis.equiv_fun_symm_std_basis
- \+ *lemma* matrix.to_bilin_basis_fun
- \- *lemma* matrix.to_bilin_is_basis_fun

Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/dimension.lean
- \+ *lemma* basis.finite_index_of_dim_lt_omega
- \+ *lemma* basis.finite_of_vector_space_index_of_dim_lt_omega
- \+ *theorem* basis.le_span
- \+ *theorem* basis.mk_eq_dim''
- \+ *theorem* basis.mk_eq_dim
- \+ *theorem* basis.mk_range_eq_dim
- \+ *lemma* basis.nonempty_fintype_index_of_dim_lt_omega
- \+ *def* basis.of_dim_eq_zero'
- \+ *lemma* basis.of_dim_eq_zero'_apply
- \+ *def* basis.of_dim_eq_zero
- \+ *lemma* basis.of_dim_eq_zero_apply
- \- *lemma* exists_is_basis_fintype
- \- *theorem* is_basis.le_span
- \- *theorem* is_basis.mk_eq_dim''
- \- *theorem* is_basis.mk_eq_dim
- \- *theorem* is_basis.mk_range_eq_dim
- \- *lemma* is_basis_of_dim_eq_zero'
- \- *lemma* is_basis_of_dim_eq_zero
- \+/\- *theorem* mk_eq_mk_of_basis'
- \+/\- *theorem* mk_eq_mk_of_basis
- \+/\- *theorem* {m}

Modified src/linear_algebra/dual.lean
- \+ *lemma* basis.coe_dual_basis
- \+ *lemma* basis.coe_to_dual_self
- \+ *def* basis.dual_basis
- \+ *lemma* basis.dual_basis_apply
- \+ *lemma* basis.dual_basis_apply_self
- \+ *lemma* basis.dual_basis_equiv_fun
- \+ *lemma* basis.dual_basis_repr
- \+ *theorem* basis.dual_dim_eq
- \+ *def* basis.to_dual
- \+ *lemma* basis.to_dual_apply
- \+ *lemma* basis.to_dual_apply_left
- \+ *lemma* basis.to_dual_apply_right
- \+ *lemma* basis.to_dual_eq_equiv_fun
- \+ *lemma* basis.to_dual_eq_repr
- \+ *def* basis.to_dual_equiv
- \+ *def* basis.to_dual_flip
- \+ *lemma* basis.to_dual_flip_apply
- \+ *lemma* basis.to_dual_inj
- \+ *theorem* basis.to_dual_ker
- \+ *theorem* basis.to_dual_range
- \+ *lemma* basis.to_dual_to_dual
- \+ *lemma* basis.to_dual_total_left
- \+ *lemma* basis.to_dual_total_right
- \+ *lemma* basis.total_coord
- \+ *lemma* basis.total_dual_basis
- \+ *def* dual_pair.basis
- \+ *lemma* dual_pair.coe_basis
- \+ *lemma* dual_pair.coe_dual_basis
- \- *lemma* dual_pair.decomposition
- \- *lemma* dual_pair.eq_dual
- \- *lemma* dual_pair.is_basis
- \+ *lemma* dual_pair.lc_coeffs
- \+ *lemma* dual_pair.lc_def
- \- *def* is_basis.coord_fun
- \- *lemma* is_basis.coord_fun_eq_repr
- \- *def* is_basis.dual_basis
- \- *lemma* is_basis.dual_basis_apply
- \- *lemma* is_basis.dual_basis_apply_self
- \- *lemma* is_basis.dual_basis_equiv_fun
- \- *theorem* is_basis.dual_basis_is_basis
- \- *lemma* is_basis.dual_basis_repr
- \- *theorem* is_basis.dual_dim_eq
- \- *theorem* is_basis.dual_lin_independent
- \- *def* is_basis.to_dual
- \- *lemma* is_basis.to_dual_apply
- \- *lemma* is_basis.to_dual_apply_left
- \- *lemma* is_basis.to_dual_apply_right
- \- *lemma* is_basis.to_dual_eq_equiv_fun
- \- *lemma* is_basis.to_dual_eq_repr
- \- *def* is_basis.to_dual_equiv
- \- *def* is_basis.to_dual_flip
- \- *lemma* is_basis.to_dual_inj
- \- *theorem* is_basis.to_dual_ker
- \- *theorem* is_basis.to_dual_range
- \- *lemma* is_basis.to_dual_swap_eq_to_dual
- \- *lemma* is_basis.to_dual_to_dual
- \- *lemma* is_basis.to_dual_total_left
- \- *lemma* is_basis.to_dual_total_right
- \- *lemma* is_basis.total_dual_basis

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* coe_basis_of_linear_independent_of_card_eq_finrank
- \+ *lemma* coe_basis_of_span_eq_top_of_card_eq_finrank
- \+ *lemma* coe_finset_basis_of_linear_independent_of_card_eq_finrank
- \+ *lemma* coe_set_basis_of_linear_independent_of_card_eq_finrank
- \+ *lemma* finite_dimensional.basis.subset_extend
- \+ *lemma* finite_dimensional.basis_singleton_apply
- \+ *lemma* finite_dimensional.basis_unique.repr_eq_zero_iff
- \+ *lemma* finite_dimensional.coe_finset_basis_index
- \+/\- *lemma* finite_dimensional.dim_eq_card_basis
- \- *lemma* finite_dimensional.equiv_fin
- \- *lemma* finite_dimensional.equiv_fin_of_dim_eq
- \- *lemma* finite_dimensional.exists_is_basis_finite
- \- *lemma* finite_dimensional.exists_is_basis_finset
- \- *lemma* finite_dimensional.exists_is_basis_singleton
- \- *lemma* finite_dimensional.fin_basis
- \+ *lemma* finite_dimensional.finite_basis_index
- \+/\- *lemma* finite_dimensional.finrank_eq_card_basis'
- \+/\- *lemma* finite_dimensional.finrank_eq_card_basis
- \+/\- *lemma* finite_dimensional.finrank_eq_card_finset_basis
- \+/\- *lemma* finite_dimensional.of_finite_basis
- \+/\- *lemma* finite_dimensional.of_finset_basis
- \+/\- *lemma* finite_dimensional.of_fintype_basis
- \+ *lemma* finite_dimensional.range_basis_singleton
- \+ *lemma* finite_dimensional.range_finset_basis
- \+/\- *lemma* finrank_eq_one_iff
- \+ *lemma* finrank_eq_zero_of_basis_imp_false
- \+ *lemma* finrank_eq_zero_of_basis_imp_not_finite
- \+ *lemma* finrank_eq_zero_of_not_exists_basis_finite
- \- *lemma* finset_is_basis_of_linear_independent_of_card_eq_finrank
- \- *lemma* finset_is_basis_of_span_eq_top_of_card_eq_finrank
- \- *lemma* is_basis_of_finrank_zero'
- \- *lemma* is_basis_of_finrank_zero
- \- *lemma* is_basis_of_linear_independent_of_card_eq_finrank
- \- *lemma* is_basis_of_span_eq_top_of_card_eq_finrank
- \- *lemma* set_is_basis_of_linear_independent_of_card_eq_finrank
- \- *lemma* set_is_basis_of_span_eq_top_of_card_eq_finrank
- \- *lemma* singleton_is_basis

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp.dom_lcongr_apply

Modified src/linear_algebra/finsupp_vector_space.lean
- \+ *def* finsupp.basis.tensor_product
- \+ *lemma* finsupp.basis_repr
- \+ *lemma* finsupp.coe_basis
- \+ *lemma* finsupp.coe_basis_single_one
- \- *lemma* finsupp.is_basis.tensor_product
- \- *lemma* finsupp.is_basis_single
- \- *lemma* finsupp.is_basis_single_one

Modified src/linear_algebra/free_algebra.lean
- \- *lemma* free_algebra.is_basis_free_monoid

Modified src/linear_algebra/free_module.lean
- \+ *lemma* basis.card_le_card_of_linear_independent
- \+ *lemma* basis.card_le_card_of_linear_independent_aux
- \+/\- *lemma* eq_bot_of_generator_maximal_map_eq_zero
- \+/\- *lemma* eq_bot_of_rank_eq_zero
- \- *lemma* is_basis.card_le_card_of_linear_independent
- \- *lemma* is_basis.card_le_card_of_linear_independent_aux
- \- *lemma* module.free_of_finite_type_torsion_free'
- \- *lemma* module.free_of_finite_type_torsion_free
- \- *theorem* submodule.exists_is_basis
- \- *lemma* submodule.exists_is_basis_of_le
- \- *lemma* submodule.exists_is_basis_of_le_span
- \+/\- *def* submodule.induction_on_rank
- \+/\- *def* submodule.induction_on_rank_aux

Modified src/linear_algebra/invariant_basis_number.lean


Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent.extend_subset
- \+ *lemma* linear_independent.linear_independent_extend
- \+ *lemma* linear_independent.subset_extend
- \+ *lemma* linear_independent.subset_span_extend

Modified src/linear_algebra/matrix.lean
- \+/\- *lemma* algebra.left_mul_matrix_injective
- \+ *def* basis.det
- \+ *lemma* basis.det_apply
- \+ *lemma* basis.det_self
- \+ *lemma* basis.sum_to_matrix_smul_self
- \+ *lemma* basis.to_lin_to_matrix
- \+ *def* basis.to_matrix
- \+ *lemma* basis.to_matrix_apply
- \+ *lemma* basis.to_matrix_eq_to_matrix_constr
- \+ *def* basis.to_matrix_equiv
- \+ *lemma* basis.to_matrix_mul_to_matrix
- \+ *lemma* basis.to_matrix_self
- \+ *lemma* basis.to_matrix_transpose_apply
- \+ *lemma* basis.to_matrix_update
- \+ *lemma* basis_to_matrix_mul_linear_map_to_matrix
- \- *def* is_basis.det
- \- *lemma* is_basis.det_apply
- \- *lemma* is_basis.det_self
- \+/\- *lemma* is_basis.iff_det
- \- *lemma* is_basis.sum_to_matrix_smul_self
- \- *lemma* is_basis.to_lin_to_matrix
- \- *def* is_basis.to_matrix
- \- *lemma* is_basis.to_matrix_apply
- \- *lemma* is_basis.to_matrix_eq_to_matrix_constr
- \- *def* is_basis.to_matrix_equiv
- \- *lemma* is_basis.to_matrix_mul_to_matrix
- \- *lemma* is_basis.to_matrix_self
- \- *lemma* is_basis.to_matrix_transpose_apply
- \- *lemma* is_basis.to_matrix_update
- \- *lemma* is_basis_to_matrix_mul_linear_map_to_matrix
- \+/\- *lemma* linear_equiv.is_unit_det
- \+/\- *def* linear_equiv.of_is_unit_det
- \+/\- *lemma* linear_map.to_matrix_alg_equiv_id
- \- *theorem* linear_map.to_matrix_alg_equiv_range
- \+ *theorem* linear_map.to_matrix_alg_equiv_reindex_range
- \+/\- *lemma* linear_map.to_matrix_id
- \+/\- *lemma* linear_map.to_matrix_one
- \- *theorem* linear_map.to_matrix_range
- \+ *theorem* linear_map.to_matrix_reindex_range
- \- *lemma* linear_map.to_matrix_symm_transpose
- \+/\- *def* linear_map.trace
- \+/\- *def* linear_map.trace_aux
- \+/\- *lemma* linear_map.trace_aux_def
- \- *theorem* linear_map.trace_aux_eq'
- \+/\- *theorem* linear_map.trace_aux_eq
- \- *theorem* linear_map.trace_aux_range
- \+ *theorem* linear_map.trace_aux_reindex_range
- \+/\- *theorem* linear_map.trace_eq_matrix_trace
- \+ *theorem* linear_map.trace_eq_matrix_trace_of_finite_set
- \+/\- *theorem* linear_map.trace_mul_comm
- \+ *lemma* linear_map_to_matrix_mul_basis_to_matrix
- \- *lemma* linear_map_to_matrix_mul_is_basis_to_matrix
- \+/\- *lemma* matrix.to_lin_alg_equiv_one
- \+/\- *lemma* matrix.to_lin_one
- \+ *lemma* matrix.to_lin_transpose

Modified src/linear_algebra/quadratic_form.lean


Modified src/linear_algebra/std_basis.lean
- \+ *lemma* pi.basis_apply
- \+ *lemma* pi.basis_fun_apply
- \+ *lemma* pi.basis_fun_repr
- \+ *lemma* pi.basis_repr
- \+ *lemma* pi.basis_repr_std_basis
- \- *lemma* pi.is_basis_fun
- \- *lemma* pi.is_basis_fun_repr
- \- *lemma* pi.is_basis_fun₀
- \- *lemma* pi.is_basis_std_basis

Modified src/ring_theory/adjoin/power_basis.lean
- \- *lemma* algebra.power_basis_is_basis

Modified src/ring_theory/adjoin_root.lean
- \+ *def* adjoin_root.power_basis
- \+ *def* adjoin_root.power_basis_aux
- \- *lemma* adjoin_root.power_basis_is_basis

Modified src/ring_theory/algebra_tower.lean
- \+ *theorem* basis.smul_apply
- \+ *theorem* basis.smul_repr
- \+ *theorem* basis.smul_repr_mk
- \- *theorem* is_basis.smul
- \- *theorem* is_basis.smul_repr
- \- *theorem* is_basis.smul_repr_mk

Modified src/ring_theory/mv_polynomial/basic.lean
- \+ *def* mv_polynomial.basis_monomials
- \+ *lemma* mv_polynomial.coe_basis_monomials
- \- *lemma* mv_polynomial.is_basis_monomials

Modified src/ring_theory/power_basis.lean
- \+ *lemma* power_basis.coe_basis

Modified src/ring_theory/trace.lean
- \+/\- *lemma* algebra.trace_eq_matrix_trace



## [2021-05-10 07:36:13](https://github.com/leanprover-community/mathlib/commit/f985e36)
feat(group_theory/subgroup): add mem_map_of_mem ([#7459](https://github.com/leanprover-community/mathlib/pull/7459))
From LTE.
Written by @PatrickMassot
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.apply_coe_mem_map
- \+ *lemma* subgroup.mem_map_of_mem

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* submonoid.apply_coe_mem_map
- \+/\- *lemma* submonoid.mem_map_of_mem

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.apply_coe_mem_map

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
- \- *def* equiv.arrow_arrow_equiv_prod_arrow
- \+ *def* equiv.curry
- \+/\- *def* equiv.prod_punit
- \+/\- *def* equiv.punit_prod

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv.coe_curry
- \+ *lemma* linear_equiv.coe_curry_symm
- \- *lemma* linear_equiv.coe_uncurry
- \- *lemma* linear_equiv.coe_uncurry_symm

Modified src/linear_algebra/matrix.lean


Modified src/set_theory/cardinal.lean
- \+/\- *theorem* cardinal.power_mul

Modified src/set_theory/cardinal_ordinal.lean


Modified src/set_theory/cofinality.lean




## [2021-05-10 06:01:59](https://github.com/leanprover-community/mathlib/commit/7150c90)
refactor(ring_theory/localization): Golf two proofs ([#7520](https://github.com/leanprover-community/mathlib/pull/7520))
Golfing two proofs and changing their order.
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+/\- *lemma* localization.at_prime.comap_maximal_ideal
- \+/\- *lemma* localization.at_prime.map_eq_maximal_ideal



## [2021-05-09 22:18:48](https://github.com/leanprover-community/mathlib/commit/ea0043c)
feat(topology): tiny new lemmas ([#7554](https://github.com/leanprover-community/mathlib/pull/7554))
from LTE
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.eq_of_same_basis

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
- \+ *lemma* quotient_group.coe_mk'
- \+ *lemma* quotient_group.mk'_apply

Modified src/group_theory/subgroup.lean
- \+ *lemma* monoid_hom.eq_iff
- \+ *lemma* subgroup.div_mem_comm_iff

Modified src/topology/algebra/group.lean




## [2021-05-09 12:20:10](https://github.com/leanprover-community/mathlib/commit/581064f)
feat(uniform_space/cauchy): cauchy_seq lemmas ([#7528](https://github.com/leanprover-community/mathlib/pull/7528))
from the Liquid Tensor Experiment
#### Estimated changes
Modified src/analysis/calculus/fderiv_measurable.lean


Modified src/topology/instances/real.lean


Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy_seq.subseq_mem
- \+ *lemma* cauchy_seq.subseq_subseq_mem
- \+ *lemma* cauchy_seq_const
- \+ *lemma* cauchy_seq_iff'
- \+ *lemma* cauchy_seq_iff



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


Added src/algebra/lie/character.lean
- \+ *lemma* lie_algebra.lie_character_apply_lie
- \+ *lemma* lie_algebra.lie_character_apply_of_mem_derived
- \+ *def* lie_algebra.lie_character_equiv_linear_dual

Modified src/algebra/lie/nilpotent.lean
- \- *lemma* lie_algebra.nilpotent_iff_equiv_nilpotent
- \+ *lemma* lie_equiv.nilpotent_iff_equiv_nilpotent

Modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_submodule.mem_mk_iff
- \+ *lemma* lie_submodule.nontrivial_iff
- \+ *lemma* lie_submodule.subsingleton_iff

Added src/algebra/lie/weights.lean
- \+ *lemma* lie_algebra.zero_root_space_eq_top_of_nilpotent
- \+ *lemma* lie_module.coe_weight_space_of_top
- \+ *def* lie_module.is_weight
- \+ *lemma* lie_module.is_weight_zero_of_nilpotent
- \+ *lemma* lie_module.lie_mem_pre_weight_space_of_mem_pre_weight_space
- \+ *lemma* lie_module.mem_pre_weight_space
- \+ *lemma* lie_module.mem_weight_space
- \+ *def* lie_module.pre_weight_space
- \+ *def* lie_module.weight_space
- \+ *lemma* lie_module.zero_weight_space_eq_top_of_nilpotent'
- \+ *lemma* lie_module.zero_weight_space_eq_top_of_nilpotent

Modified src/data/nat/basic.lean
- \+ *lemma* nat.le_or_le_of_add_eq_add_pred

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.commute_pow_left_of_commute
- \+ *lemma* linear_map.pow_map_zero_of_le



## [2021-05-08 08:13:59](https://github.com/leanprover-community/mathlib/commit/4a8a595)
feat(topology/subset_properties, homeomorph): lemmata about embeddings ([#7431](https://github.com/leanprover-community/mathlib/pull/7431))
Two lemmata: (i) embedding to homeomorphism (ii) a closed embedding is proper
Coauthored with @hrmacbeth
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.self_comp_of_injective_symm

Modified src/topology/homeomorph.lean


Modified src/topology/subset_properties.lean
- \+ *lemma* closed_embedding.tendsto_cocompact



## [2021-05-08 05:52:42](https://github.com/leanprover-community/mathlib/commit/583ad82)
feat(algebraic_geometry/structure_sheaf): Structure sheaf on basic opens ([#7405](https://github.com/leanprover-community/mathlib/pull/7405))
Proves that `to_basic_open` is an isomorphism of commutative rings. Also adds Hartshorne as a reference.
#### Estimated changes
Modified docs/references.bib


Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *def* algebraic_geometry.basic_open_iso
- \+ *lemma* algebraic_geometry.locally_const_basic_open
- \+ *lemma* algebraic_geometry.normalize_finite_fraction_representation
- \+ *lemma* algebraic_geometry.to_basic_open_injective
- \+ *lemma* algebraic_geometry.to_basic_open_surjective



## [2021-05-07 22:54:26](https://github.com/leanprover-community/mathlib/commit/dbcd454)
feat(topology/category/*): Add alternative explicit limit cones for `Top`, etc. and shows `X : Profinite` is a limit of finite sets. ([#7448](https://github.com/leanprover-community/mathlib/pull/7448))
This PR redefines `Top.limit_cone`, and defines similar explicit limit cones for `CompHaus` and `Profinite`.
Using the definition with the subspace topology makes the proofs that the limit is compact, t2 and/or totally disconnected much easier.
This also expresses any `X : Profinite` as a limit of its discrete quotients, which are all finite.
#### Estimated changes
Modified src/topology/category/CompHaus.lean
- \+ *def* CompHaus.limit_cone
- \+ *def* CompHaus.limit_cone_is_limit

Added src/topology/category/Profinite/as_limit.lean
- \+ *def* Profinite.as_limit
- \+ *def* Profinite.as_limit_cone
- \+ *def* Profinite.as_limit_cone_iso
- \+ *def* Profinite.fintype_diagram
- \+ *def* Profinite.iso_as_limit_cone_lift
- \+ *def* Profinite.lim

Renamed src/topology/category/Profinite.lean to src/topology/category/Profinite/default.lean
- \+ *def* Profinite.limit_cone
- \+ *def* Profinite.limit_cone_is_limit

Modified src/topology/category/Top/limits.lean




## [2021-05-07 22:54:25](https://github.com/leanprover-community/mathlib/commit/515fb2f)
feat(group_theory/perm/*): lemmas about `extend_domain`, `fin_rotate`, and `fin.cycle_type` ([#7447](https://github.com/leanprover-community/mathlib/pull/7447))
Shows how `disjoint`, `support`, `is_cycle`, and `cycle_type` behave under `extend_domain`
Calculates `support` and `cycle_type` for `fin_rotate` and `fin.cycle_type`
Shows that the normal closure of `fin_rotate 5` in `alternating_group (fin 5)` is the whole alternating group.
#### Estimated changes
Modified src/analysis/normed_space/hahn_banach.lean


Modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* equiv.perm.cycle_type_extend_domain

Modified src/group_theory/perm/cycles.lean
- \+ *lemma* equiv.perm.is_cycle.extend_domain

Modified src/group_theory/perm/fin.lean
- \+ *lemma* cycle_type_fin_rotate
- \+ *lemma* cycle_type_fin_rotate_of_le
- \+ *lemma* fin.cycle_type_cycle_range
- \+ *lemma* fin.is_cycle_cycle_range
- \+ *lemma* fin.is_three_cycle_cycle_range_two
- \+ *lemma* is_cycle_fin_rotate
- \+ *lemma* is_cycle_fin_rotate_of_le
- \+ *lemma* support_fin_rotate
- \+ *lemma* support_fin_rotate_of_le

Modified src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.disjoint.extend_domain

Modified src/group_theory/perm/support.lean
- \+ *lemma* equiv.perm.card_support_extend_domain
- \+ *lemma* equiv.perm.support_extend_domain

Modified src/group_theory/specific_groups/alternating.lean
- \+ *lemma* alternating_group.is_conj_of
- \+ *lemma* alternating_group.is_three_cycle_is_conj
- \+ *lemma* alternating_group.normal_closure_fin_rotate_five
- \+ *lemma* equiv.perm.fin_rotate_bit1_mem_alternating_group
- \+ *lemma* equiv.perm.is_three_cycle.alternating_normal_closure
- \+ *lemma* equiv.perm.is_three_cycle.mem_alternating_group

Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.subtype_range

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
- \+ *lemma* hahn_series.C_injective
- \+ *lemma* hahn_series.C_ne_zero
- \+ *lemma* hahn_series.add_val_le_of_coeff_ne_zero
- \- *lemma* hahn_series.coeff_min_ne_zero
- \+ *lemma* hahn_series.coeff_order_ne_zero
- \+ *lemma* hahn_series.min_order_le_order_add
- \- *lemma* hahn_series.mul_coeff_min_add_min
- \+ *lemma* hahn_series.mul_coeff_order_add_order
- \+ *lemma* hahn_series.ne_zero_of_coeff_ne_zero
- \+ *def* hahn_series.order
- \+ *lemma* hahn_series.order_C
- \+ *lemma* hahn_series.order_le_of_coeff_ne_zero
- \+ *lemma* hahn_series.order_mul
- \+ *lemma* hahn_series.order_of_ne
- \+ *lemma* hahn_series.order_one
- \+ *lemma* hahn_series.order_single
- \+ *lemma* hahn_series.order_zero
- \+ *lemma* hahn_series.single_injective
- \+ *lemma* hahn_series.single_ne_zero
- \+ *def* hahn_series.summable_family.emb_domain
- \+ *lemma* hahn_series.summable_family.emb_domain_apply
- \+ *lemma* hahn_series.summable_family.emb_domain_image
- \+ *lemma* hahn_series.summable_family.emb_domain_notin_range
- \+ *lemma* hahn_series.summable_family.hsum_emb_domain
- \+ *lemma* hahn_series.summable_family.hsum_sub



## [2021-05-07 09:30:47](https://github.com/leanprover-community/mathlib/commit/72e151d)
feat(topology/uniform_space): is_closed_of_spread_out ([#7538](https://github.com/leanprover-community/mathlib/pull/7538))
See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/integers.20are.20closed.20in.20reals)
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+ *lemma* ball_inter_left
- \+ *lemma* ball_inter_right
- \+ *lemma* uniform_space.mem_closure_iff_ball
- \+ *lemma* uniform_space.mem_closure_iff_symm_ball

Modified src/topology/uniform_space/separation.lean
- \+ *lemma* eq_of_forall_symmetric
- \+ *lemma* eq_of_uniformity
- \+ *lemma* eq_of_uniformity_basis
- \+ *lemma* is_closed_of_spaced_out



## [2021-05-07 09:30:46](https://github.com/leanprover-community/mathlib/commit/301542a)
feat(group_theory.quotient_group): add eq_iff_div_mem ([#7523](https://github.com/leanprover-community/mathlib/pull/7523))
From LTE.
Written by @PatrickMassot
#### Estimated changes
Modified src/group_theory/quotient_group.lean
- \+ *lemma* quotient_group.eq_iff_div_mem
- \+ *lemma* quotient_group.eq_one_iff

Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.exists_inv_mem_iff_exists_mem



## [2021-05-07 09:30:45](https://github.com/leanprover-community/mathlib/commit/63a1782)
feat(field_theory/polynomial_galois_group): More flexible version of gal_action_hom_bijective_of_prime_degree ([#7508](https://github.com/leanprover-community/mathlib/pull/7508))
Since the number of non-real roots is even, we can make a more flexible version of `gal_action_hom_bijective_of_prime_degree`. This flexibility will be helpful when working with a specific polynomial.
#### Estimated changes
Modified src/field_theory/polynomial_galois_group.lean
- \+ *lemma* polynomial.gal.gal_action_hom_bijective_of_prime_degree'
- \+/\- *lemma* polynomial.gal.gal_action_hom_bijective_of_prime_degree_aux

Modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* equiv.perm.two_dvd_card_support



## [2021-05-07 09:30:44](https://github.com/leanprover-community/mathlib/commit/565310f)
feat(data/nat/cast): pi.coe_nat and pi.nat_apply ([#7492](https://github.com/leanprover-community/mathlib/pull/7492))
#### Estimated changes
Modified src/data/int/cast.lean
- \+ *lemma* pi.coe_int
- \+ *lemma* pi.int_apply

Modified src/data/nat/cast.lean
- \+ *lemma* pi.coe_nat
- \+ *lemma* pi.nat_apply



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
- \+ *theorem* category_theory.arrow.mk_inj
- \+ *theorem* category_theory.arrow.mk_injective



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
- \- *lemma* decidable.le_iff_le_iff_lt_iff_lt
- \- *lemma* decidable.le_imp_le_iff_lt_imp_lt

Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_monoid.lean


Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* add_le_mul_two_add
- \- *lemma* decidable.mul_le_mul_left
- \- *lemma* decidable.mul_le_mul_right
- \+/\- *lemma* le_mul_of_one_le_left
- \+/\- *lemma* le_mul_of_one_le_right
- \+/\- *lemma* le_of_mul_le_of_one_le
- \+/\- *lemma* lt_mul_of_one_lt_left
- \+/\- *lemma* lt_mul_of_one_lt_right
- \+/\- *lemma* mul_le_mul
- \+/\- *lemma* mul_le_mul_of_nonneg_left
- \+/\- *lemma* mul_le_mul_of_nonneg_right
- \+/\- *lemma* mul_le_mul_of_nonpos_left
- \+/\- *lemma* mul_le_mul_of_nonpos_right
- \+/\- *lemma* mul_le_of_le_one_left
- \+/\- *lemma* mul_le_of_le_one_right
- \+/\- *lemma* mul_le_one
- \+/\- *lemma* mul_lt_mul''
- \+/\- *lemma* mul_lt_mul'
- \+/\- *lemma* mul_lt_mul
- \+/\- *lemma* mul_lt_one_of_nonneg_of_lt_one_left
- \+/\- *lemma* mul_lt_one_of_nonneg_of_lt_one_right
- \+/\- *lemma* mul_nonneg
- \+/\- *theorem* mul_nonneg_iff_right_nonneg_of_pos
- \+/\- *lemma* mul_nonneg_le_one_le
- \+/\- *lemma* mul_nonneg_of_nonpos_of_nonpos
- \+/\- *lemma* mul_nonpos_of_nonneg_of_nonpos
- \+/\- *lemma* mul_nonpos_of_nonpos_of_nonneg
- \+/\- *def* nonneg_ring.to_linear_nonneg_ring
- \+/\- *lemma* one_le_mul_of_one_le_of_one_le
- \+/\- *lemma* one_lt_mul
- \+/\- *lemma* one_lt_mul_of_le_of_lt
- \+/\- *lemma* one_lt_mul_of_lt_of_le
- \+/\- *lemma* ordered_ring.mul_le_mul_of_nonneg_left
- \+/\- *lemma* ordered_ring.mul_le_mul_of_nonneg_right
- \+/\- *lemma* ordered_ring.mul_nonneg

Modified src/computability/halting.lean


Modified src/computability/partrec.lean
- \+ *theorem* decidable.partrec.const'
- \+/\- *theorem* partrec.fix
- \+ *lemma* partrec.fix_aux
- \+/\- *theorem* partrec.sum_cases_left
- \+/\- *theorem* partrec.sum_cases_right

Modified src/data/int/basic.lean
- \+ *def* int.greatest_of_bdd
- \+ *def* int.least_of_bdd

Modified src/data/list/basic.lean
- \+ *theorem* decidable.list.eq_or_ne_mem_of_mem
- \+ *theorem* decidable.list.lex.ne_iff
- \+/\- *theorem* list.eq_or_ne_mem_of_mem
- \+/\- *theorem* list.lex.ne_iff

Modified src/data/list/range.lean


Modified src/data/nat/basic.lean
- \+/\- *lemma* nat.lt_of_div_lt_div

Modified src/data/nat/prime.lean


Modified src/data/nat/sqrt.lean


Modified src/data/set/basic.lean


Modified src/logic/nontrivial.lean


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
- \- *def* equiv.perm.via_embedding
- \- *lemma* equiv.perm.via_embedding_apply_image
- \- *lemma* equiv.perm.via_embedding_apply_mem_range
- \- *lemma* equiv.perm.via_embedding_apply_not_mem_range
- \- *lemma* equiv.perm.via_embedding_sign
- \+ *def* equiv.perm.via_fintype_embedding
- \+ *lemma* equiv.perm.via_fintype_embedding_apply_image
- \+ *lemma* equiv.perm.via_fintype_embedding_apply_mem_range
- \+ *lemma* equiv.perm.via_fintype_embedding_apply_not_mem_range
- \+ *lemma* equiv.perm.via_fintype_embedding_sign

Modified src/group_theory/perm/basic.lean
- \+ *def* equiv.perm.extend_domain_hom
- \+ *lemma* equiv.perm.extend_domain_hom_injective
- \+ *lemma* equiv.perm.of_subtype_apply_coe
- \+ *lemma* equiv.perm.via_embedding_apply
- \+ *lemma* equiv.perm.via_embedding_apply_of_not_mem
- \+ *lemma* equiv.perm.via_embedding_hom_apply
- \+ *lemma* equiv.perm.via_embedding_hom_injective

Modified src/group_theory/perm/fin.lean


Modified src/group_theory/solvable.lean
- \+ *lemma* equiv.perm.fin_5_not_solvable
- \+ *lemma* equiv.perm.not_solvable
- \+ *lemma* general_commutator_containment
- \+ *lemma* not_solvable_of_mem_derived_series



## [2021-05-07 09:30:38](https://github.com/leanprover-community/mathlib/commit/95b91b3)
refactor(group_theory/perm/*): disjoint and support in own file ([#7450](https://github.com/leanprover-community/mathlib/pull/7450))
The group_theory/perm/sign file was getting large and too broad in scope. This refactor pulls out `perm.support`, `perm.is_swap`, and `perm.disjoint` into a separate file.
A simpler version of [#7118](https://github.com/leanprover-community/mathlib/pull/7118).
#### Estimated changes
Modified src/group_theory/perm/cycle_type.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean
- \- *lemma* equiv.perm.apply_mem_support
- \- *lemma* equiv.perm.card_support_eq_two
- \- *lemma* equiv.perm.card_support_eq_zero
- \- *lemma* equiv.perm.card_support_le_one
- \- *lemma* equiv.perm.card_support_ne_one
- \- *lemma* equiv.perm.card_support_prod_list_of_pairwise_disjoint
- \- *lemma* equiv.perm.card_support_swap
- \- *lemma* equiv.perm.card_support_swap_mul
- \- *lemma* equiv.perm.disjoint.card_support_mul
- \- *lemma* equiv.perm.disjoint.disjoint_support
- \- *lemma* equiv.perm.disjoint.gpow_disjoint_gpow
- \- *lemma* equiv.perm.disjoint.mul_apply_eq_iff
- \- *lemma* equiv.perm.disjoint.mul_comm
- \- *lemma* equiv.perm.disjoint.mul_eq_one_iff
- \- *lemma* equiv.perm.disjoint.mul_left
- \- *lemma* equiv.perm.disjoint.mul_right
- \- *lemma* equiv.perm.disjoint.pow_disjoint_pow
- \- *lemma* equiv.perm.disjoint.support_mul
- \- *lemma* equiv.perm.disjoint.symm
- \- *def* equiv.perm.disjoint
- \- *lemma* equiv.perm.disjoint_comm
- \- *lemma* equiv.perm.disjoint_iff_disjoint_support
- \- *lemma* equiv.perm.disjoint_one_left
- \- *lemma* equiv.perm.disjoint_one_right
- \- *lemma* equiv.perm.disjoint_prod_list_of_disjoint
- \- *lemma* equiv.perm.disjoint_prod_perm
- \- *lemma* equiv.perm.disjoint_prod_right
- \- *lemma* equiv.perm.exists_mem_support_of_mem_support_prod
- \- *lemma* equiv.perm.gpow_apply_eq_of_apply_apply_eq_self
- \- *lemma* equiv.perm.gpow_apply_eq_self_of_apply_eq_self
- \- *lemma* equiv.perm.gpow_apply_mem_support
- \- *lemma* equiv.perm.is_swap.of_subtype_is_swap
- \- *def* equiv.perm.is_swap
- \- *lemma* equiv.perm.mem_support
- \- *lemma* equiv.perm.ne_and_ne_of_swap_mul_apply_ne_self
- \- *lemma* equiv.perm.nodup_of_pairwise_disjoint
- \- *lemma* equiv.perm.one_lt_card_support_of_ne_one
- \- *lemma* equiv.perm.pow_apply_eq_of_apply_apply_eq_self
- \- *lemma* equiv.perm.pow_apply_eq_self_of_apply_eq_self
- \- *lemma* equiv.perm.pow_apply_mem_support
- \- *def* equiv.perm.support
- \- *lemma* equiv.perm.support_eq_empty_iff
- \- *lemma* equiv.perm.support_inv
- \- *lemma* equiv.perm.support_mul_le
- \- *lemma* equiv.perm.support_one
- \- *lemma* equiv.perm.support_pow_le
- \- *lemma* equiv.perm.support_swap
- \- *lemma* equiv.perm.support_swap_mul_eq
- \- *lemma* equiv.perm.two_le_card_support_of_ne_one

Added src/group_theory/perm/support.lean
- \+ *lemma* equiv.perm.apply_mem_support
- \+ *lemma* equiv.perm.card_support_eq_two
- \+ *lemma* equiv.perm.card_support_eq_zero
- \+ *lemma* equiv.perm.card_support_le_one
- \+ *lemma* equiv.perm.card_support_ne_one
- \+ *lemma* equiv.perm.card_support_prod_list_of_pairwise_disjoint
- \+ *lemma* equiv.perm.card_support_swap
- \+ *lemma* equiv.perm.card_support_swap_mul
- \+ *lemma* equiv.perm.disjoint.card_support_mul
- \+ *lemma* equiv.perm.disjoint.disjoint_support
- \+ *lemma* equiv.perm.disjoint.gpow_disjoint_gpow
- \+ *lemma* equiv.perm.disjoint.inv_left
- \+ *lemma* equiv.perm.disjoint.inv_right
- \+ *lemma* equiv.perm.disjoint.mul_apply_eq_iff
- \+ *lemma* equiv.perm.disjoint.mul_comm
- \+ *lemma* equiv.perm.disjoint.mul_eq_one_iff
- \+ *lemma* equiv.perm.disjoint.mul_left
- \+ *lemma* equiv.perm.disjoint.mul_right
- \+ *lemma* equiv.perm.disjoint.pow_disjoint_pow
- \+ *lemma* equiv.perm.disjoint.support_mul
- \+ *lemma* equiv.perm.disjoint.symm
- \+ *def* equiv.perm.disjoint
- \+ *lemma* equiv.perm.disjoint_comm
- \+ *lemma* equiv.perm.disjoint_iff_disjoint_support
- \+ *lemma* equiv.perm.disjoint_iff_eq_or_eq
- \+ *lemma* equiv.perm.disjoint_inv_left_iff
- \+ *lemma* equiv.perm.disjoint_inv_right_iff
- \+ *lemma* equiv.perm.disjoint_one_left
- \+ *lemma* equiv.perm.disjoint_one_right
- \+ *lemma* equiv.perm.disjoint_prod_perm
- \+ *lemma* equiv.perm.disjoint_prod_right
- \+ *lemma* equiv.perm.disjoint_refl_iff
- \+ *lemma* equiv.perm.exists_mem_support_of_mem_support_prod
- \+ *lemma* equiv.perm.gpow_apply_eq_of_apply_apply_eq_self
- \+ *lemma* equiv.perm.gpow_apply_eq_self_of_apply_eq_self
- \+ *lemma* equiv.perm.gpow_apply_mem_support
- \+ *lemma* equiv.perm.is_swap.of_subtype_is_swap
- \+ *def* equiv.perm.is_swap
- \+ *lemma* equiv.perm.mem_support
- \+ *lemma* equiv.perm.mem_support_swap_mul_imp_mem_support_ne
- \+ *lemma* equiv.perm.ne_and_ne_of_swap_mul_apply_ne_self
- \+ *lemma* equiv.perm.nodup_of_pairwise_disjoint
- \+ *lemma* equiv.perm.not_mem_support
- \+ *lemma* equiv.perm.one_lt_card_support_of_ne_one
- \+ *lemma* equiv.perm.pow_apply_eq_of_apply_apply_eq_self
- \+ *lemma* equiv.perm.pow_apply_eq_self_of_apply_eq_self
- \+ *lemma* equiv.perm.pow_apply_mem_support
- \+ *def* equiv.perm.support
- \+ *lemma* equiv.perm.support_congr
- \+ *lemma* equiv.perm.support_eq_empty_iff
- \+ *lemma* equiv.perm.support_gpow_le
- \+ *lemma* equiv.perm.support_inv
- \+ *lemma* equiv.perm.support_mul_le
- \+ *lemma* equiv.perm.support_one
- \+ *lemma* equiv.perm.support_pow_le
- \+ *lemma* equiv.perm.support_prod_le
- \+ *lemma* equiv.perm.support_prod_of_pairwise_disjoint
- \+ *lemma* equiv.perm.support_refl
- \+ *lemma* equiv.perm.support_swap
- \+ *lemma* equiv.perm.support_swap_iff
- \+ *lemma* equiv.perm.support_swap_mul_eq
- \+ *lemma* equiv.perm.support_swap_mul_ge_support_diff
- \+ *lemma* equiv.perm.support_swap_mul_swap
- \+ *lemma* equiv.perm.two_le_card_support_of_ne_one



## [2021-05-07 09:30:37](https://github.com/leanprover-community/mathlib/commit/251a42b)
feat(ring_theory/finiteness): add monoid_algebra.ft_iff_fg ([#7445](https://github.com/leanprover-community/mathlib/pull/7445))
We prove here `add monoid_algebra.ft_iff_fg`: the monoid algebra is of finite type if and only if the monoid is finitely generated.
- [x] depends on: [#7409](https://github.com/leanprover-community/mathlib/pull/7409)
#### Estimated changes
Modified src/algebra/monoid_algebra.lean
- \+ *lemma* add_monoid_algebra.of'_eq_of

Modified src/ring_theory/finiteness.lean
- \+ *lemma* add_monoid_algebra.exists_finset_adjoin_eq_top
- \+ *lemma* add_monoid_algebra.fg_of_finite_type
- \+ *lemma* add_monoid_algebra.finite_type_iff_fg
- \+ *lemma* add_monoid_algebra.mem_adjoin_support
- \- *lemma* add_monoid_algebra.mem_adjoint_support
- \+ *lemma* add_monoid_algebra.mem_closure_of_mem_span_closure
- \+ *lemma* add_monoid_algebra.of'_mem_span
- \+ *lemma* monoid_algebra.exists_finset_adjoin_eq_top
- \+ *lemma* monoid_algebra.fg_of_finite_type
- \+ *lemma* monoid_algebra.finite_type_iff_fg
- \+/\- *lemma* monoid_algebra.mem_adjoint_support
- \+ *lemma* monoid_algebra.mem_closure_of_mem_span_closure
- \+ *lemma* monoid_algebra.of_mem_span_of_iff



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
Added src/algebra/monoid_algebra_to_direct_sum.lean
- \+ *def* add_monoid_algebra.to_direct_sum
- \+ *lemma* add_monoid_algebra.to_direct_sum_add
- \+ *lemma* add_monoid_algebra.to_direct_sum_mul
- \+ *lemma* add_monoid_algebra.to_direct_sum_single
- \+ *lemma* add_monoid_algebra.to_direct_sum_to_add_monoid_algebra
- \+ *lemma* add_monoid_algebra.to_direct_sum_zero
- \+ *def* add_monoid_algebra_equiv_direct_sum
- \+ *def* direct_sum.to_add_monoid_algebra
- \+ *lemma* direct_sum.to_add_monoid_algebra_add
- \+ *lemma* direct_sum.to_add_monoid_algebra_mul
- \+ *lemma* direct_sum.to_add_monoid_algebra_of
- \+ *lemma* direct_sum.to_add_monoid_algebra_to_direct_sum
- \+ *lemma* direct_sum.to_add_monoid_algebra_zero



## [2021-05-07 09:30:34](https://github.com/leanprover-community/mathlib/commit/3a5c871)
refactor(polynomial/*): make polynomials irreducible ([#7421](https://github.com/leanprover-community/mathlib/pull/7421))
Polynomials are the most basic objects in field theory. Making them irreducible helps Lean, because it can not try to unfold things too far, and it helps the user because it forces him to use a sane API instead of mixing randomly stuff from finsupp and from polynomials, as used to be the case in mathlib before this PR.
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.monomial_eq_C_mul_X
- \- *lemma* mv_polynomial.single_eq_C_mul_X
- \- *lemma* mv_polynomial.sum_monomial
- \+ *lemma* mv_polynomial.sum_monomial_eq

Modified src/data/mv_polynomial/pderiv.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/basic.lean
- \+/\- *def* polynomial.C
- \+/\- *lemma* polynomial.C_0
- \+ *lemma* polynomial.C_mul_monomial
- \+ *lemma* polynomial.add_to_finsupp
- \+/\- *def* polynomial.coeff
- \+ *lemma* polynomial.coeff_erase
- \- *lemma* polynomial.coeff_mk
- \+/\- *lemma* polynomial.coeff_neg
- \+/\- *lemma* polynomial.coeff_one_zero
- \+/\- *lemma* polynomial.coeff_sub
- \+ *lemma* polynomial.erase_monomial
- \+ *lemma* polynomial.erase_ne
- \+ *lemma* polynomial.erase_same
- \+ *lemma* polynomial.erase_zero
- \+ *lemma* polynomial.exists_iff_exists_finsupp
- \+ *lemma* polynomial.forall_iff_forall_finsupp
- \+ *lemma* polynomial.mem_support_iff
- \+/\- *def* polynomial.monomial
- \+ *lemma* polynomial.monomial_add_erase
- \- *lemma* polynomial.monomial_def
- \+ *lemma* polynomial.monomial_eq_C_mul_X
- \+ *def* polynomial.monomial_fun
- \+ *lemma* polynomial.monomial_mul_C
- \+ *lemma* polynomial.mul_eq_sum_sum
- \+ *lemma* polynomial.mul_to_finsupp
- \+ *lemma* polynomial.neg_to_finsupp
- \+ *lemma* polynomial.not_mem_support_iff
- \+ *lemma* polynomial.one_to_finsupp
- \- *lemma* polynomial.single_eq_C_mul_X
- \+ *lemma* polynomial.smul_to_finsupp
- \+ *def* polynomial.sum
- \+/\- *lemma* polynomial.sum_C_index
- \+ *lemma* polynomial.sum_X_index
- \+ *lemma* polynomial.sum_add'
- \+ *lemma* polynomial.sum_add
- \+ *lemma* polynomial.sum_add_index
- \+ *lemma* polynomial.sum_def
- \+ *lemma* polynomial.sum_eq_of_subset
- \+ *lemma* polynomial.sum_monomial_index
- \+ *lemma* polynomial.sum_smul_index
- \+ *lemma* polynomial.sum_to_finsupp
- \+ *lemma* polynomial.sum_zero_index
- \+/\- *def* polynomial.support
- \+/\- *lemma* polynomial.support_add
- \+ *lemma* polynomial.support_erase
- \+/\- *lemma* polynomial.support_zero
- \+ *def* polynomial.to_finsupp_iso
- \+ *lemma* polynomial.to_finsupp_iso_monomial
- \+ *lemma* polynomial.to_finsupp_iso_symm_single
- \+ *lemma* polynomial.zero_to_finsupp
- \- *def* polynomial

Modified src/data/polynomial/coeff.lean
- \+/\- *lemma* polynomial.coeff_add
- \- *lemma* polynomial.exists_coeff_not_mem_C_inverse
- \- *lemma* polynomial.mem_span_C_coeff
- \- *lemma* polynomial.mem_support_iff
- \- *lemma* polynomial.not_mem_support_iff
- \- *lemma* polynomial.span_le_of_coeff_mem_C_inverse
- \- *lemma* polynomial.sum_def
- \+ *lemma* polynomial.support_smul

Modified src/data/polynomial/degree/definitions.lean
- \+/\- *lemma* polynomial.degree_C_le
- \+ *lemma* polynomial.degree_smul_le
- \+ *lemma* polynomial.nat_degree_add_le
- \+/\- *lemma* polynomial.nat_degree_le_nat_degree
- \+ *lemma* polynomial.nat_degree_smul_le

Modified src/data/polynomial/degree/lemmas.lean
- \- *lemma* polynomial.degree_map_le
- \- *lemma* polynomial.nat_degree_map_le

Modified src/data/polynomial/degree/trailing_degree.lean
- \+ *lemma* polynomial.trailing_coeff_zero

Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/div.lean


Modified src/data/polynomial/erase_lead.lean


Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.degree_map_le
- \+/\- *lemma* polynomial.eval_eq_finset_sum
- \+/\- *lemma* polynomial.eval_eq_sum
- \- *lemma* polynomial.eval₂_eq_lift_nc
- \+ *lemma* polynomial.eval₂_to_finsupp_eq_lift_nc
- \+ *lemma* polynomial.nat_degree_map_le

Modified src/data/polynomial/identities.lean


Modified src/data/polynomial/induction.lean
- \+ *lemma* polynomial.exists_coeff_not_mem_C_inverse
- \+ *lemma* polynomial.mem_span_C_coeff
- \+ *lemma* polynomial.span_le_of_coeff_mem_C_inverse

Modified src/data/polynomial/integral_normalization.lean


Modified src/data/polynomial/iterated_deriv.lean


Modified src/data/polynomial/lifts.lean


Modified src/data/polynomial/mirror.lean
- \+/\- *lemma* polynomial.mirror_zero

Modified src/data/polynomial/monic.lean


Modified src/data/polynomial/monomial.lean
- \- *lemma* polynomial.C_mul_monomial
- \+ *lemma* polynomial.card_support_le_one_iff_monomial
- \- *lemma* polynomial.monomial_mul_C
- \+ *lemma* polynomial.monomial_one_eq_iff

Modified src/data/polynomial/reverse.lean


Modified src/data/polynomial/ring_division.lean


Modified src/field_theory/adjoin.lean


Modified src/field_theory/fixed.lean


Modified src/field_theory/minpoly.lean


Modified src/field_theory/separable.lean
- \+/\- *theorem* polynomial.coeff_contract
- \- *theorem* polynomial.expand_eq_map_domain

Modified src/field_theory/splitting_field.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/ring_theory/eisenstein_criterion.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/localization.lean
- \+ *lemma* localization_map.coeff_integer_normalization_of_not_mem_support

Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* polynomial.coeff_mem_frange
- \+ *lemma* polynomial.coeff_of_subring
- \+/\- *theorem* polynomial.coeff_to_subring'
- \+/\- *theorem* polynomial.coeff_to_subring
- \+/\- *theorem* polynomial.degree_restriction
- \+/\- *theorem* polynomial.degree_to_subring
- \+ *def* polynomial.frange
- \+ *lemma* polynomial.frange_one
- \+ *lemma* polynomial.frange_zero
- \+ *lemma* polynomial.linear_independent_powers_iff_aeval
- \- *lemma* polynomial.linear_independent_powers_iff_eval₂
- \+ *lemma* polynomial.mem_frange_iff
- \+/\- *theorem* polynomial.nat_degree_to_subring
- \+/\- *theorem* polynomial.restriction_zero
- \+ *lemma* polynomial.support_restriction
- \+ *lemma* polynomial.support_to_subring
- \+/\- *theorem* polynomial.to_subring_zero

Modified src/ring_theory/polynomial/content.lean


Modified src/ring_theory/polynomial/scale_roots.lean


Modified src/ring_theory/polynomial_algebra.lean
- \+ *lemma* support_subset_support_mat_poly_equiv

Modified src/ring_theory/power_basis.lean
- \- *lemma* power_basis.polynomial.mem_supported_range

Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/roots_of_unity.lean




## [2021-05-07 09:30:33](https://github.com/leanprover-community/mathlib/commit/322ccc5)
feat(finset/basic): downward induction for finsets ([#7379](https://github.com/leanprover-community/mathlib/pull/7379))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *def* finset.strong_downward_induction
- \+ *lemma* finset.strong_downward_induction_eq
- \+ *def* finset.strong_downward_induction_on
- \+ *lemma* finset.strong_downward_induction_on_eq

Modified src/data/multiset/basic.lean
- \+ *def* multiset.strong_downward_induction
- \+ *lemma* multiset.strong_downward_induction_eq
- \+ *def* multiset.strong_downward_induction_on
- \+ *lemma* multiset.strong_downward_induction_on_eq



## [2021-05-07 09:30:31](https://github.com/leanprover-community/mathlib/commit/11a06de)
feat(order/closure): closure of unions and bUnions ([#7361](https://github.com/leanprover-community/mathlib/pull/7361))
prove closure_closure_union and similar
#### Estimated changes
Modified src/order/closure.lean
- \+ *lemma* closure_operator.closure_bsupr_closure
- \+ *lemma* closure_operator.closure_inf_le
- \- *lemma* closure_operator.closure_inter_le
- \+/\- *lemma* closure_operator.closure_le_closed_iff_le
- \+ *lemma* closure_operator.closure_le_mk₃_iff
- \+ *lemma* closure_operator.closure_mem_mk₃
- \+ *lemma* closure_operator.closure_sup_closure
- \+ *lemma* closure_operator.closure_sup_closure_le
- \+ *lemma* closure_operator.closure_sup_closure_left
- \+ *lemma* closure_operator.closure_sup_closure_right
- \+ *lemma* closure_operator.closure_supr_closure
- \+/\- *lemma* closure_operator.closure_top
- \- *lemma* closure_operator.closure_union_closure_le
- \+ *lemma* closure_operator.eq_mk₃_closed
- \+ *lemma* closure_operator.mem_mk₃_closed
- \+ *def* closure_operator.mk₂
- \+ *def* closure_operator.mk₃

Modified src/order/complete_lattice.lean
- \+ *theorem* Sup_le_Sup_of_subset_insert_bot
- \- *theorem* Sup_le_Sup_of_subset_instert_bot



## [2021-05-07 09:30:30](https://github.com/leanprover-community/mathlib/commit/b20e664)
feat(order/well_founded_set): Higman's Lemma ([#7212](https://github.com/leanprover-community/mathlib/pull/7212))
Proves Higman's Lemma: if `r` is partially well-ordered on `s`, then `list.sublist_forall2` is partially well-ordered on the set of lists whose elements are in `s`.
#### Estimated changes
Modified docs/references.bib


Modified src/order/well_founded_set.lean
- \+/\- *theorem* finset.is_pwo
- \+/\- *theorem* finset.is_wf
- \+/\- *theorem* finset.partially_well_ordered_on
- \+/\- *theorem* finset.well_founded_on
- \+ *lemma* set.partially_well_ordered_on.exists_min_bad_of_exists_bad
- \+ *lemma* set.partially_well_ordered_on.iff_forall_not_is_bad_seq
- \+ *lemma* set.partially_well_ordered_on.iff_not_exists_is_min_bad_seq
- \+ *def* set.partially_well_ordered_on.is_bad_seq
- \+ *def* set.partially_well_ordered_on.is_min_bad_seq
- \+ *lemma* set.partially_well_ordered_on.partially_well_ordered_on_sublist_forall₂



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
- \+/\- *lemma* category_theory.coe_comp
- \+/\- *lemma* category_theory.coe_id
- \+ *lemma* category_theory.comp_apply
- \+ *lemma* category_theory.id_apply

Modified src/tactic/elementwise.lean


Modified src/topology/sheaves/stalks.lean




## [2021-05-07 04:59:59](https://github.com/leanprover-community/mathlib/commit/0ead8ee)
feat(ring_theory/localization): Characterize units in localization at prime ideal ([#7519](https://github.com/leanprover-community/mathlib/pull/7519))
Adds a few lemmas characterizing units and nonunits (elements of the maximal ideal) in the localization at a prime ideal.
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *lemma* localization_map.at_prime.is_unit_mk'_iff
- \+ *lemma* localization_map.at_prime.is_unit_to_map_iff
- \+ *lemma* localization_map.at_prime.mk'_mem_maximal_iff
- \+ *lemma* localization_map.at_prime.to_map_mem_maximal_iff



## [2021-05-07 04:59:57](https://github.com/leanprover-community/mathlib/commit/755cb75)
feat(data/list/basic): non-meta to_chunks ([#7517](https://github.com/leanprover-community/mathlib/pull/7517))
A non-meta definition of the `list.to_chunks` method, plus some basic theorems about it.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.to_chunks_aux_eq
- \+ *theorem* list.to_chunks_aux_join
- \+ *theorem* list.to_chunks_eq_cons'
- \+ *theorem* list.to_chunks_eq_cons
- \+ *theorem* list.to_chunks_join
- \+ *theorem* list.to_chunks_length_le
- \+ *theorem* list.to_chunks_nil

Modified src/data/list/defs.lean
- \+ *def* list.to_chunks
- \+ *def* list.to_chunks_aux



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
- \+ *def* category_theory.functor.left_op_right_op_equiv
- \+ *def* category_theory.functor.left_op_right_op_iso
- \+ *def* category_theory.functor.op_unop_equiv
- \+/\- *def* category_theory.functor.op_unop_iso
- \+ *def* category_theory.functor.right_op_left_op_iso
- \+/\- *def* category_theory.functor.unop_op_iso



## [2021-05-07 04:59:53](https://github.com/leanprover-community/mathlib/commit/efb283c)
feat(data/dfinsupp): add `finset_sum_apply` and `coe_finset_sum` ([#7499](https://github.com/leanprover-community/mathlib/pull/7499))
The names of the new`add_monoid_hom`s parallel the names in my recent `quadratic_form` PR, [#7417](https://github.com/leanprover-community/mathlib/pull/7417).
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* dfinsupp.coe_finset_sum
- \+ *def* dfinsupp.coe_fn_add_monoid_hom
- \+ *def* dfinsupp.eval_add_monoid_hom
- \+ *lemma* dfinsupp.finset_sum_apply



## [2021-05-07 04:59:51](https://github.com/leanprover-community/mathlib/commit/9acbe58)
feat(normed_space/normed_group_hom): add lemmas ([#7468](https://github.com/leanprover-community/mathlib/pull/7468))
From LTE.
Written by @PatrickMassot
#### Estimated changes
Modified src/analysis/normed_space/normed_group_hom.lean
- \+ *lemma* normed_group_hom.coe_ker
- \+ *lemma* normed_group_hom.is_closed_ker
- \+ *lemma* normed_group_hom.ker_zero

Modified src/group_theory/subgroup.lean
- \+ *lemma* monoid_hom.coe_ker
- \+ *lemma* monoid_hom.ker_one



## [2021-05-07 04:59:50](https://github.com/leanprover-community/mathlib/commit/154fda2)
feat(category_theory/subobjects): more about kernel and image subobjects ([#7467](https://github.com/leanprover-community/mathlib/pull/7467))
Lemmas about factoring through kernel subobjects, and functoriality of kernel subobjects.
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean


Modified src/category_theory/subobject/limits.lean
- \+ *def* category_theory.limits.factor_thru_kernel_subobject
- \+ *lemma* category_theory.limits.factor_thru_kernel_subobject_comp_arrow
- \+ *lemma* category_theory.limits.image_subobject_arrow_comp_eq_zero
- \+ *def* category_theory.limits.kernel_subobject_map
- \+ *lemma* category_theory.limits.kernel_subobject_map_arrow
- \+ *lemma* category_theory.limits.kernel_subobject_map_comp
- \+ *lemma* category_theory.limits.kernel_subobject_map_id



## [2021-05-06 22:46:23](https://github.com/leanprover-community/mathlib/commit/bb1fb89)
feat(data/real/basic): add real.Inf_le_iff ([#7524](https://github.com/leanprover-community/mathlib/pull/7524))
From LTE.
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* le_iff_forall_pos_le_add
- \+ *lemma* le_iff_forall_pos_lt_add

Modified src/data/real/basic.lean
- \+ *lemma* real.Inf_le_iff
- \+ *lemma* real.add_pos_lt_Sup
- \+ *lemma* real.le_Sup_iff
- \+ *lemma* real.lt_Inf_add_pos



## [2021-05-06 22:46:22](https://github.com/leanprover-community/mathlib/commit/e00d6e0)
feat(data/polynomial/*): Specific root sets ([#7510](https://github.com/leanprover-community/mathlib/pull/7510))
Adds lemmas for the root sets of a couple specific polynomials.
#### Estimated changes
Modified src/data/polynomial/field_division.lean
- \+ *lemma* polynomial.root_set_C_mul_X_pow
- \+ *lemma* polynomial.root_set_X_pow
- \+ *lemma* polynomial.root_set_monomial

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.root_set_C



## [2021-05-06 22:46:21](https://github.com/leanprover-community/mathlib/commit/6f27ef7)
chore(data/equiv/basic): Show that `Pi_curry` is really just `sigma.curry` ([#7497](https://github.com/leanprover-community/mathlib/pull/7497))
Extracts some proofs to their own lemmas, and replaces definitions with existing ones.
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/data/sigma/basic.lean
- \+ *lemma* sigma.curry_uncurry
- \+ *lemma* sigma.uncurry_curry



## [2021-05-06 22:46:20](https://github.com/leanprover-community/mathlib/commit/9aed6c9)
feat(data/finsupp,linear_algebra): `finsupp.split` is an equivalence ([#7490](https://github.com/leanprover-community/mathlib/pull/7490))
This PR shows that for finite types `η`, `finsupp.split` is an equivalence between `(Σ (j : η), ιs j) →₀ α` and `Π j, (ιs j →₀ α)`.
To be used in the `bundled-basis` refactor
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.sigma_finsupp_add_equiv_pi_finsupp_apply
- \+ *lemma* finsupp.sigma_finsupp_equiv_pi_finsupp_apply

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp.sigma_finsupp_lequiv_pi_finsupp_apply
- \+ *lemma* finsupp.sigma_finsupp_lequiv_pi_finsupp_symm_apply



## [2021-05-06 22:46:19](https://github.com/leanprover-community/mathlib/commit/48bdd1e)
feat(data/equiv,linear_algebra): `Pi_congr_right` for `mul_equiv` and `linear_equiv` ([#7489](https://github.com/leanprover-community/mathlib/pull/7489))
This PR generalizes `equiv.Pi_congr_right` to linear equivs, adding the `mul_equiv`/`add_equiv` version as well.
To be used in the `bundled-basis` refactor
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *def* mul_equiv.Pi_congr_right
- \+ *lemma* mul_equiv.Pi_congr_right_refl
- \+ *lemma* mul_equiv.Pi_congr_right_symm
- \+ *lemma* mul_equiv.Pi_congr_right_trans

Modified src/linear_algebra/basic.lean
- \+ *def* linear_equiv.Pi_congr_right
- \+ *lemma* linear_equiv.Pi_congr_right_refl
- \+ *lemma* linear_equiv.Pi_congr_right_symm
- \+ *lemma* linear_equiv.Pi_congr_right_trans



## [2021-05-06 22:46:18](https://github.com/leanprover-community/mathlib/commit/652357a)
feat(data/nat/choose/sum): alternate forms of the binomial theorem ([#7415](https://github.com/leanprover-community/mathlib/pull/7415))
#### Estimated changes
Modified src/data/nat/choose/sum.lean
- \+ *lemma* commute.add_pow'
- \+/\- *theorem* commute.add_pow



## [2021-05-06 10:56:24](https://github.com/leanprover-community/mathlib/commit/9c86e38)
refactor(ring_theory/ideal/operations.lean): make is_prime.comap an instance ([#7518](https://github.com/leanprover-community/mathlib/pull/7518))
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/ideal/operations.lean
- \- *theorem* ideal.is_prime.comap



## [2021-05-06 10:56:23](https://github.com/leanprover-community/mathlib/commit/13c41e1)
feat(category_theory/linear): linear functors ([#7369](https://github.com/leanprover-community/mathlib/pull/7369))
#### Estimated changes
Modified src/category_theory/linear/default.lean


Added src/category_theory/linear/linear_functor.lean
- \+ *lemma* category_theory.functor.coe_map_linear_map
- \+ *def* category_theory.functor.map_linear_map
- \+ *lemma* category_theory.functor.map_smul



## [2021-05-06 06:18:21](https://github.com/leanprover-community/mathlib/commit/7040c50)
feat(category_theory): the opposite of an abelian category is abelian ([#7514](https://github.com/leanprover-community/mathlib/pull/7514))
#### Estimated changes
Added src/category_theory/abelian/opposite.lean


Modified src/category_theory/fin_category.lean
- \+ *def* category_theory.fin_category_opposite

Modified src/category_theory/limits/opposites.lean
- \+ *lemma* category_theory.limits.has_finite_colimits_opposite
- \+ *lemma* category_theory.limits.has_finite_coproducts_opposite
- \+ *lemma* category_theory.limits.has_finite_limits_opposite
- \+ *lemma* category_theory.limits.has_finite_products_opposite

Modified src/category_theory/limits/shapes/normal_mono.lean
- \+ *def* category_theory.normal_epi_of_normal_mono_unop
- \+ *def* category_theory.normal_mono_of_normal_epi_unop

Modified src/category_theory/limits/shapes/zero.lean


Added src/category_theory/preadditive/opposite.lean
- \+ *lemma* category_theory.unop_add
- \+ *lemma* category_theory.unop_zero



## [2021-05-06 06:18:20](https://github.com/leanprover-community/mathlib/commit/c4c6cd8)
feat(linear_algebra/finsupp): linear equivalence between `α × β →₀ M` and `α →₀ β →₀ M` ([#7472](https://github.com/leanprover-community/mathlib/pull/7472))
This PR extends the equivalence `finsupp.finsupp_prod_equiv` to a linear equivalence (to be used in the `bundled-basis` refactor).
#### Estimated changes
Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp.finsupp_prod_lequiv_apply
- \+ *lemma* finsupp.finsupp_prod_lequiv_symm_apply



## [2021-05-06 06:18:19](https://github.com/leanprover-community/mathlib/commit/9154a83)
feat(algebra/*, ring_theory/valuation/basic): `linear_ordered_add_comm_group_with_top`, `add_valuation.map_sub` ([#7452](https://github.com/leanprover-community/mathlib/pull/7452))
Defines `linear_ordered_add_comm_group_with_top`
Uses that to port a few more facts about `valuation`s to `add_valuation`s.
#### Estimated changes
Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_monoid.lean


Modified src/ring_theory/valuation/basic.lean
- \+ *lemma* add_valuation.map_add_of_distinct_val
- \+ *lemma* add_valuation.map_eq_of_lt_sub
- \+ *lemma* add_valuation.map_inv
- \+ *lemma* add_valuation.map_le_sub
- \+ *lemma* add_valuation.map_neg
- \+ *lemma* add_valuation.map_sub
- \+ *lemma* add_valuation.map_sub_swap
- \+ *lemma* add_valuation.map_units_inv
- \+ *lemma* valuation.map_sub
- \+ *lemma* valuation.map_sub_le
- \- *lemma* valuation.map_sub_le_max



## [2021-05-06 04:31:52](https://github.com/leanprover-community/mathlib/commit/6af5fbd)
feat(category_theory/.../zero): if a zero morphism is a mono, the source is zero ([#7462](https://github.com/leanprover-community/mathlib/pull/7462))
Some simple lemmas about zero morphisms.
#### Estimated changes
Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* category_theory.limits.has_zero_object.functor.zero_map
- \+ *lemma* category_theory.limits.has_zero_object.functor.zero_obj
- \+ *lemma* category_theory.limits.is_iso_of_source_target_iso_zero
- \+ *def* category_theory.limits.iso_zero_of_epi_zero
- \+ *def* category_theory.limits.iso_zero_of_mono_zero



## [2021-05-05 23:47:55](https://github.com/leanprover-community/mathlib/commit/009be86)
feat(measure_theory/set_integral): continuous_on.measurable_at_filter ([#7511](https://github.com/leanprover-community/mathlib/pull/7511))
#### Estimated changes
Modified src/measure_theory/set_integral.lean
- \+ *lemma* continuous_at.measurable_at_filter
- \+ *lemma* continuous_on.measurable_at_filter



## [2021-05-05 23:47:54](https://github.com/leanprover-community/mathlib/commit/709c73b)
feat(category_theory/Fintype): some lemmas and `Fintype_to_Profinite`.  ([#7491](https://github.com/leanprover-community/mathlib/pull/7491))
Adding some lemmas for morphisms on `Fintype` as functions, as well as `Fintype_to_Profinite`.
Part of the LTE.
#### Estimated changes
Modified src/category_theory/Fintype.lean
- \+ *lemma* Fintype.coe_comp
- \+ *lemma* Fintype.coe_id
- \+ *lemma* Fintype.comp_apply
- \+ *lemma* Fintype.id_apply

Modified src/topology/category/Profinite.lean
- \+ *def* Fintype.discrete_topology
- \+ *def* Fintype.to_Profinite
- \+ *def* Profinite.of



## [2021-05-05 23:47:53](https://github.com/leanprover-community/mathlib/commit/1ef04bd)
feat(data/finsupp): prove `f.curry x y = f (x, y)` ([#7475](https://github.com/leanprover-community/mathlib/pull/7475))
This was surprisingly hard to prove actually!
To be used in the `bundled-basis` refactor
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.curry_apply



## [2021-05-05 23:47:52](https://github.com/leanprover-community/mathlib/commit/d3a46a7)
feat(algebra/big_operators): telescopic sums ([#7470](https://github.com/leanprover-community/mathlib/pull/7470))
This is restating things we already have in a form which is
slightly more convenient for the liquid tensor experiment
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.eq_sum_range_sub'
- \+ *lemma* finset.eq_sum_range_sub



## [2021-05-05 23:47:51](https://github.com/leanprover-community/mathlib/commit/18ada66)
feat(order/filter_at_top_bot): extraction lemmas ([#7469](https://github.com/leanprover-community/mathlib/pull/7469))
from the liquid tensor experiment
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.eventually_at_bot_prod_self'
- \+ *lemma* filter.eventually_at_bot_prod_self
- \+ *lemma* filter.eventually_at_top_prod_self'
- \+ *lemma* filter.eventually_at_top_prod_self
- \+ *lemma* filter.extraction_forall_of_eventually'
- \+ *lemma* filter.extraction_forall_of_eventually
- \+ *lemma* filter.extraction_forall_of_frequently
- \+ *lemma* filter.tendsto.prod_at_bot
- \+ *lemma* filter.tendsto.prod_at_top
- \+ *lemma* filter.tendsto.prod_map_prod_at_bot
- \+ *lemma* filter.tendsto.prod_map_prod_at_top
- \+ *lemma* filter.tendsto.subseq_mem
- \+ *lemma* filter.tendsto_at_bot_diagonal
- \+ *lemma* filter.tendsto_at_top_diagonal



## [2021-05-05 23:47:50](https://github.com/leanprover-community/mathlib/commit/7cc367b)
feat(category_theory/subobject): minor tweaks ([#7466](https://github.com/leanprover-community/mathlib/pull/7466))
A few minor tweaks to the `subobject` API that I wanted while working on homology.
#### Estimated changes
Modified src/category_theory/subobject/basic.lean
- \+ *lemma* category_theory.subobject.of_le_mk_le_mk_of_comm

Modified src/category_theory/subobject/factor_thru.lean
- \- *lemma* category_theory.subobject.factor_thru_comp_of_le
- \+ *lemma* category_theory.subobject.factor_thru_of_le

Modified src/category_theory/subobject/lattice.lean
- \- *def* category_theory.subobject.top_coe_iso_self
- \- *lemma* category_theory.subobject.underlying_iso_id_eq_top_coe_iso_self
- \+ *lemma* category_theory.subobject.underlying_iso_top_hom



## [2021-05-05 23:47:49](https://github.com/leanprover-community/mathlib/commit/e25cbe0)
feat(category_theory/quotient): the quotient functor is full and essentially surjective ([#7465](https://github.com/leanprover-community/mathlib/pull/7465))
#### Estimated changes
Modified src/category_theory/quotient.lean
- \+ *lemma* category_theory.quotient.lift_map_functor_map



## [2021-05-05 23:47:48](https://github.com/leanprover-community/mathlib/commit/19b752c)
feat(category_theory/preadditive): reformulation of mono_of_kernel_zero ([#7464](https://github.com/leanprover-community/mathlib/pull/7464))
#### Estimated changes
Modified src/category_theory/preadditive/default.lean
- \+ *lemma* category_theory.preadditive.epi_of_cokernel_iso_zero
- \+/\- *lemma* category_theory.preadditive.epi_of_cokernel_zero
- \+ *lemma* category_theory.preadditive.mono_of_kernel_iso_zero



## [2021-05-05 23:47:47](https://github.com/leanprover-community/mathlib/commit/7794969)
feat(category_theory/.../additive_functor): additive functors preserve zero objects ([#7463](https://github.com/leanprover-community/mathlib/pull/7463))
#### Estimated changes
Modified src/category_theory/preadditive/additive_functor.lean
- \+ *def* category_theory.functor.map_zero_object



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
Added src/algebra/hierarchy_design.lean




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
- \+/\- *def* discrete_quotient.comap
- \+ *lemma* discrete_quotient.comap_comp
- \+ *lemma* discrete_quotient.comap_id
- \+ *lemma* discrete_quotient.comap_mono
- \+ *def* discrete_quotient.le_comap
- \+ *lemma* discrete_quotient.le_comap_comp
- \+ *lemma* discrete_quotient.le_comap_id
- \+ *lemma* discrete_quotient.le_comap_trans
- \+ *def* discrete_quotient.map
- \+ *lemma* discrete_quotient.map_comp
- \+ *lemma* discrete_quotient.map_continuous
- \+ *lemma* discrete_quotient.map_id
- \+ *lemma* discrete_quotient.map_of_le
- \+ *lemma* discrete_quotient.map_of_le_apply
- \+ *lemma* discrete_quotient.map_proj
- \+ *lemma* discrete_quotient.map_proj_apply
- \+ *lemma* discrete_quotient.of_le_comp
- \+ *lemma* discrete_quotient.of_le_comp_apply
- \+ *lemma* discrete_quotient.of_le_map
- \+ *lemma* discrete_quotient.of_le_map_apply
- \+ *lemma* discrete_quotient.of_le_refl
- \+ *lemma* discrete_quotient.of_le_refl_apply



## [2021-05-05 18:50:19](https://github.com/leanprover-community/mathlib/commit/84d27b4)
refactor(group_theory/group_action/defs): generalize smul_mul_assoc and mul_smul_comm ([#7441](https://github.com/leanprover-community/mathlib/pull/7441))
These lemmas did not need a full algebra structure; written this way, it permits usage on `has_scalar (units R) A` given `algebra R A` (in some future PR).
For now, the old algebra lemmas are left behind, to minimize the scope of this patch.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *lemma* algebra.mul_smul_comm
- \- *lemma* algebra.smul_mul_assoc
- \- *lemma* algebra.smul_mul_smul

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
- \+ *def* direct_sum.lift_ring_hom
- \+ *lemma* direct_sum.ring_hom_ext'
- \+ *def* direct_sum.to_semiring
- \+ *lemma* direct_sum.to_semiring_coe_add_monoid_hom
- \+ *lemma* direct_sum.to_semiring_of



## [2021-05-05 18:50:16](https://github.com/leanprover-community/mathlib/commit/93bc7e0)
feat(order): add some missing `pi` and `Prop` instances ([#7268](https://github.com/leanprover-community/mathlib/pull/7268))
#### Estimated changes
Modified src/order/boolean_algebra.lean


Modified src/order/bounded_lattice.lean
- \+ *lemma* inf_Prop_eq
- \+ *lemma* le_Prop_eq
- \- *lemma* le_iff_imp
- \+ *lemma* sup_Prop_eq

Modified src/order/complete_boolean_algebra.lean


Modified src/order/complete_lattice.lean
- \+/\- *lemma* Inf_Prop_eq
- \+/\- *lemma* Sup_Prop_eq
- \+/\- *lemma* infi_Prop_eq
- \+/\- *lemma* infi_apply
- \+/\- *lemma* supr_Prop_eq
- \+/\- *lemma* supr_apply
- \+ *lemma* supr_subtype''

Modified src/topology/omega_complete_partial_order.lean




## [2021-05-05 18:50:15](https://github.com/leanprover-community/mathlib/commit/52268b8)
feat(linear_algebra): Vandermonde matrices and their determinant ([#7116](https://github.com/leanprover-community/mathlib/pull/7116))
This PR defines the `vandermonde` matrix and gives a formula for its determinant.
@paulvanwamelen: if you would like to have `det_vandermonde` in a different form (e.g. swap the order of the variables that are being summed), please let me know!
#### Estimated changes
Added src/linear_algebra/vandermonde.lean
- \+ *lemma* matrix.det_vandermonde
- \+ *def* matrix.vandermonde
- \+ *lemma* matrix.vandermonde_apply
- \+ *lemma* matrix.vandermonde_cons
- \+ *lemma* matrix.vandermonde_succ



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
- \+ *lemma* category_theory.eq_conj_eq_to_hom

Modified src/category_theory/path_category.lean
- \+ *lemma* category_theory.paths.ext_functor



## [2021-05-05 13:56:50](https://github.com/leanprover-community/mathlib/commit/18af6b5)
feat(algebra/module): `linear_equiv.refl.symm = refl` ([#7493](https://github.com/leanprover-community/mathlib/pull/7493))
To be part of the `bundled_basis` refactor
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *lemma* linear_equiv.refl_symm



## [2021-05-05 13:56:49](https://github.com/leanprover-community/mathlib/commit/1823aee)
feat(algebra/module): `S`-linear equivs are also `R`-linear equivs ([#7476](https://github.com/leanprover-community/mathlib/pull/7476))
This PR extends `linear_map.restrict_scalars` to `linear_equiv`s.
To be used in the `bundled-basis` refactor.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *def* linear_equiv.restrict_scalars



## [2021-05-05 13:56:48](https://github.com/leanprover-community/mathlib/commit/9b1b854)
feat(data/fintype/basic): add set.to_finset_range ([#7426](https://github.com/leanprover-community/mathlib/pull/7426))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* set.to_finset_range



## [2021-05-05 13:56:47](https://github.com/leanprover-community/mathlib/commit/bb9216c)
feat(category_theory/opposites): iso.unop ([#7400](https://github.com/leanprover-community/mathlib/pull/7400))
#### Estimated changes
Modified src/category_theory/opposites.lean
- \+ *lemma* category_theory.iso.op_unop
- \+ *def* category_theory.iso.unop
- \+ *lemma* category_theory.iso.unop_op



## [2021-05-05 13:56:45](https://github.com/leanprover-community/mathlib/commit/78e36a7)
feat(analysis/convex/extreme): extreme sets ([#7357](https://github.com/leanprover-community/mathlib/pull/7357))
define extreme sets
#### Estimated changes
Modified docs/references.bib


Modified src/analysis/convex/basic.lean
- \+ *lemma* convex.convex_remove_iff_not_mem_convex_hull_remove
- \+ *lemma* convex.open_segment_subset
- \+/\- *lemma* convex.segment_subset
- \+ *lemma* convex_iff_open_segment_subset
- \+/\- *lemma* convex_iff_segment_subset
- \+ *lemma* left_mem_open_segment_iff
- \+ *lemma* mem_open_segment_of_ne_left_right
- \+ *lemma* mem_open_segment_translate
- \+ *def* open_segment
- \+ *lemma* open_segment_eq_Ioo'
- \+ *lemma* open_segment_eq_Ioo
- \+ *lemma* open_segment_eq_image'
- \+ *lemma* open_segment_eq_image
- \+ *lemma* open_segment_eq_image₂
- \+ *lemma* open_segment_image
- \+ *lemma* open_segment_same
- \+ *lemma* open_segment_subset_segment
- \+ *lemma* open_segment_symm
- \+ *lemma* open_segment_translate_image
- \+ *lemma* open_segment_translate_preimage
- \+ *lemma* right_mem_open_segment_iff
- \+/\- *lemma* segment_eq_image'
- \+/\- *lemma* segment_eq_image
- \+/\- *lemma* segment_translate_image

Added src/analysis/convex/extreme.lean
- \+ *lemma* convex.mem_extreme_points_iff_convex_remove
- \+ *lemma* convex.mem_extreme_points_iff_mem_diff_convex_hull_remove
- \+ *lemma* extreme_points_convex_hull_subset
- \+ *lemma* extreme_points_def
- \+ *lemma* extreme_points_empty
- \+ *lemma* extreme_points_singleton
- \+ *lemma* extreme_points_subset
- \+ *lemma* inter_extreme_points_subset_extreme_points_of_subset
- \+ *lemma* is_extreme.Inter
- \+ *lemma* is_extreme.antisymm
- \+ *lemma* is_extreme.bInter
- \+ *lemma* is_extreme.convex_diff
- \+ *lemma* is_extreme.extreme_points_eq
- \+ *lemma* is_extreme.extreme_points_subset_extreme_points
- \+ *lemma* is_extreme.inter
- \+ *lemma* is_extreme.mono
- \+ *lemma* is_extreme.refl
- \+ *lemma* is_extreme.sInter
- \+ *lemma* is_extreme.trans
- \+ *def* is_extreme
- \+ *lemma* mem_extreme_points_iff_extreme_singleton
- \+ *lemma* mem_extreme_points_iff_forall_segment
- \+ *def* set.extreme_points

Modified src/data/set/intervals/image_preimage.lean
- \+ *lemma* set.image_mul_left_Ioo
- \+ *lemma* set.image_mul_right_Ioo



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
- \+ *theorem* finset.fold_image_idem

Modified src/data/finset/lattice.lean
- \+ *lemma* finset.inf_image
- \+ *lemma* finset.inf_map
- \- *lemma* finset.map_inf
- \- *lemma* finset.map_sup
- \+ *lemma* finset.sup_image
- \+ *lemma* finset.sup_map



## [2021-05-03 21:31:42](https://github.com/leanprover-community/mathlib/commit/3773525)
feat(ring_theory/finiteness): add lemmas ([#7409](https://github.com/leanprover-community/mathlib/pull/7409))
I add here some preliminary lemmas to prove that a monoid is finitely generated iff the monoid algebra is.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean
- \+ *lemma* add_monoid_algebra.mem_span_support'
- \+/\- *lemma* add_monoid_algebra.mem_span_support
- \+ *def* add_monoid_algebra.of'
- \+ *lemma* add_monoid_algebra.of'_apply

Modified src/ring_theory/finiteness.lean
- \+ *lemma* add_monoid_algebra.mem_adjoint_support
- \+ *lemma* add_monoid_algebra.support_gen_of_gen'
- \+ *lemma* add_monoid_algebra.support_gen_of_gen
- \+ *lemma* monoid_algebra.mem_adjoint_support
- \+ *lemma* monoid_algebra.support_gen_of_gen'
- \+ *lemma* monoid_algebra.support_gen_of_gen



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
- \- *def* fintype.equiv_fin
- \- *theorem* fintype.exists_equiv_fin
- \- *lemma* fintype.nonempty_equiv_of_card_eq
- \+ *def* fintype.trunc_equiv_fin
- \+ *def* fintype.trunc_equiv_fin_of_card_eq
- \+ *def* fintype.trunc_equiv_of_card_eq

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
- \+ *lemma* round_one
- \+ *lemma* round_zero

Modified src/algebra/order.lean
- \- *lemma* le_imp_le_of_lt_imp_lt
- \- *lemma* le_of_not_lt
- \- *lemma* le_or_lt
- \- *lemma* lt_or_le

Modified src/algebra/ring/basic.lean
- \+ *lemma* ring_hom.to_monoid_with_zero_hom_eq_coe

Modified src/analysis/analytic/inverse.lean


Modified src/category_theory/equivalence.lean
- \+ *def* category_theory.equivalence.pow_nat

Modified src/computability/partrec.lean


Modified src/computability/partrec_code.lean


Modified src/computability/primrec.lean


Modified src/computability/turing_machine.lean


Modified src/data/complex/module.lean


Modified src/data/equiv/fin.lean


Modified src/data/equiv/list.lean
- \+/\- *theorem* denumerable.list_of_nat_zero
- \+/\- *theorem* encodable.decode_list_zero

Modified src/data/fin.lean
- \+ *lemma* fin.coe_bit0
- \+ *lemma* fin.coe_bit1
- \+ *lemma* fin.succ_one_eq_two
- \+ *lemma* fin.zero_succ_above

Modified src/data/int/basic.lean
- \+/\- *theorem* int.zero_mod

Modified src/data/int/parity.lean


Modified src/data/list/rotate.lean
- \+/\- *lemma* list.rotate_nil

Modified src/data/list/sort.lean


Modified src/data/matrix/notation.lean


Modified src/data/nat/basic.lean
- \+/\- *theorem* nat.size_one
- \+/\- *theorem* nat.size_zero

Modified src/data/nat/bitwise.lean
- \+/\- *lemma* nat.land_zero
- \+/\- *lemma* nat.lor_zero
- \+/\- *lemma* nat.lxor_zero
- \+/\- *lemma* nat.zero_land
- \+/\- *lemma* nat.zero_lor
- \+/\- *lemma* nat.zero_lxor

Modified src/data/nat/digits.lean
- \+/\- *lemma* nat.digits_aux_zero

Modified src/data/nat/log.lean


Modified src/data/nat/modeq.lean
- \+/\- *lemma* nat.odd_mul_odd
- \+/\- *lemma* nat.odd_of_mod_four_eq_one
- \+/\- *lemma* nat.odd_of_mod_four_eq_three

Modified src/data/nat/pairing.lean
- \+ *lemma* nat.unpair_zero

Modified src/data/nat/parity.lean


Modified src/data/nat/prime.lean
- \+/\- *lemma* nat.factors_one
- \+/\- *lemma* nat.factors_zero
- \+/\- *theorem* nat.not_prime_one
- \+/\- *theorem* nat.not_prime_zero
- \+/\- *theorem* nat.prime_three

Modified src/data/nat/sqrt.lean
- \+ *lemma* nat.sqrt_zero

Modified src/data/nat/totient.lean


Modified src/data/num/lemmas.lean
- \+/\- *theorem* num.of_nat'_eq
- \+ *theorem* num.of_nat'_zero

Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean
- \+/\- *lemma* padic.coe_one

Modified src/data/pnat/factors.lean
- \+/\- *theorem* pnat.factor_multiset_one

Modified src/data/rat/basic.lean
- \+ *lemma* rat.mk_neg_one_one
- \+ *lemma* rat.mk_one_one
- \+ *lemma* rat.mk_zero_one

Modified src/data/rat/cast.lean


Modified src/data/rat/order.lean


Modified src/data/vector2.lean


Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.int_coe_eq_int_coe_iff'
- \+/\- *lemma* zmod.neg_eq_self_mod_two
- \+ *lemma* zmod.val_mul'
- \+ *lemma* zmod.val_neg'
- \+ *lemma* zmod.val_one'

Modified src/data/zmod/parity.lean


Modified src/data/zsqrtd/gaussian_int.lean


Modified src/field_theory/finite/basic.lean


Modified src/group_theory/perm/fin.lean


Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* finset.univ_fin2

Modified src/linear_algebra/affine_space/independent.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/linear_algebra/matrix.lean


Modified src/number_theory/ADE_inequality.lean


Modified src/number_theory/arithmetic_function.lean
- \+/\- *lemma* nat.arithmetic_function.card_distinct_factors_zero
- \+/\- *lemma* nat.arithmetic_function.card_factors_one

Modified src/number_theory/bernoulli.lean
- \+/\- *lemma* bernoulli'_zero
- \+/\- *lemma* bernoulli_zero

Modified src/number_theory/primorial.lean


Modified src/number_theory/pythagorean_triples.lean
- \+ *lemma* int.sq_ne_two_mod_four
- \+ *lemma* sq_ne_two_fin_zmod_four

Modified src/ring_theory/int/basic.lean


Modified src/ring_theory/power_series/well_known.lean
- \+/\- *lemma* power_series.constant_coeff_exp

Modified src/set_theory/game/domineering.lean


Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/short.lean


Modified src/set_theory/game/winner.lean


Modified src/set_theory/pgame.lean
- \+/\- *theorem* pgame.equiv_refl

Modified src/tactic/norm_fin.lean
- \+/\- *theorem* tactic.norm_fin.normalize_fin.zero

Modified src/topology/continuous_function/stone_weierstrass.lean




## [2021-05-03 14:11:12](https://github.com/leanprover-community/mathlib/commit/7da8303)
feat(category_theory/preadditive): Schur's lemma ([#7366](https://github.com/leanprover-community/mathlib/pull/7366))
We prove Schur's lemma for `𝕜`-linear categories with finite dimensional hom spaces,
over an algebraically closed field `𝕜`:
the hom space `X ⟶ Y` between simple objects `X` and `Y` is at most one dimensional,
and is 1-dimensional iff `X` and `Y` are isomorphic.
#### Estimated changes
Modified src/category_theory/endomorphism.lean
- \+ *def* category_theory.End.as_hom
- \+ *def* category_theory.End.of
- \+ *lemma* category_theory.is_unit_iff_is_iso

Modified src/category_theory/linear/default.lean


Modified src/category_theory/preadditive/default.lean


Modified src/category_theory/preadditive/schur.lean
- \+ *lemma* category_theory.endomorphism_simple_eq_smul_id
- \+ *lemma* category_theory.finrank_endomorphism_eq_one
- \+ *lemma* category_theory.finrank_endomorphism_simple_eq_one
- \+ *lemma* category_theory.finrank_hom_simple_simple_eq_one_iff
- \+ *lemma* category_theory.finrank_hom_simple_simple_eq_zero_iff
- \+ *lemma* category_theory.finrank_hom_simple_simple_eq_zero_of_not_iso
- \+ *lemma* category_theory.finrank_hom_simple_simple_le_one
- \- *def* category_theory.is_iso_equiv_nonzero
- \+ *lemma* category_theory.is_iso_iff_nonzero
- \+/\- *lemma* category_theory.is_iso_of_hom_simple

Modified src/category_theory/simple.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finrank_eq_one_iff_of_nonzero'



## [2021-05-03 07:41:58](https://github.com/leanprover-community/mathlib/commit/62c06a5)
feat(data/finset/basic): a finset has card at most one iff it is contained in a singleton ([#7404](https://github.com/leanprover-community/mathlib/pull/7404))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* finset.card_le_one_iff
- \+ *lemma* finset.card_le_one_iff_subset_singleton
- \+ *lemma* finset.card_le_one_of_subsingleton
- \+ *lemma* finset.one_lt_card_iff

Modified src/data/fintype/basic.lean
- \- *lemma* finset.card_le_one_iff
- \- *lemma* finset.card_le_one_of_subsingleton
- \- *lemma* finset.one_lt_card_iff



## [2021-05-02 18:59:48](https://github.com/leanprover-community/mathlib/commit/0cc3cd5)
feat(topology/category): Profinite has colimits ([#7434](https://github.com/leanprover-community/mathlib/pull/7434))
Show that a reflective subcategory of a cocomplete category is cocomplete, and derive that `CompHaus` and `Profinite` have colimits.
#### Estimated changes
Modified src/category_theory/monad/limits.lean
- \+ *lemma* category_theory.has_colimits_of_reflective
- \+ *lemma* category_theory.has_colimits_of_shape_of_reflective

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
- \+ *lemma* alg_hom.map_list_prod
- \+ *lemma* alg_hom.map_multiset_prod

Modified src/algebra/group/units.lean
- \+ *lemma* is_unit.mul_iff

Modified src/data/list/basic.lean
- \+ *lemma* list.prod_is_unit

Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.prod_to_list

Modified src/field_theory/algebraic_closure.lean
- \+ *lemma* exists_spectrum_of_is_alg_closed_of_finite_dimensional

Modified src/field_theory/splitting_field.lean
- \+ *lemma* polynomial.eq_prod_roots_of_monic_of_splits_id
- \+ *lemma* polynomial.eq_prod_roots_of_splits_id

Modified src/linear_algebra/eigenspace.lean
- \+ *lemma* module.End.has_eigenvalue_of_has_eigenvector



## [2021-05-02 10:42:35](https://github.com/leanprover-community/mathlib/commit/58e990d)
chore(dynamics/periodic_pts): remove duplicate of nat.dvd_right_iff_eq ([#7435](https://github.com/leanprover-community/mathlib/pull/7435))
#### Estimated changes
Modified src/dynamics/periodic_pts.lean
- \- *lemma* function.nat_dvd_iff_right



## [2021-05-02 09:28:57](https://github.com/leanprover-community/mathlib/commit/4bd1c83)
feat(topology/category/Profinite): Any continuous bijection of profinite spaces is an isomorphism. ([#7430](https://github.com/leanprover-community/mathlib/pull/7430))
#### Estimated changes
Modified src/topology/category/CompHaus.lean
- \+ *lemma* CompHaus.is_closed_map
- \+ *lemma* CompHaus.is_iso_of_bijective
- \+ *def* CompHaus.iso_of_bijective

Modified src/topology/category/Profinite.lean
- \+ *lemma* Profinite.is_closed_map
- \+ *lemma* Profinite.is_iso_of_bijective
- \+/\- *def* Profinite.to_Profinite_adj_to_CompHaus



## [2021-05-02 04:27:19](https://github.com/leanprover-community/mathlib/commit/30f3788)
feat(topology/discrete_quotient): Discrete quotients of topological spaces ([#7425](https://github.com/leanprover-community/mathlib/pull/7425))
This PR defines the type of discrete quotients of a topological space and provides a basic API.
In a subsequent PR, this will be used to show that a profinite space is the limit of its finite quotients, which will be needed for the liquid tensor experiment.
#### Estimated changes
Added src/topology/discrete_quotient.lean
- \+ *def* discrete_quotient.comap
- \+ *lemma* discrete_quotient.eq_of_proj_eq
- \+ *lemma* discrete_quotient.exists_of_compat
- \+ *lemma* discrete_quotient.fiber_clopen
- \+ *lemma* discrete_quotient.fiber_closed
- \+ *lemma* discrete_quotient.fiber_eq
- \+ *lemma* discrete_quotient.fiber_le_of_le
- \+ *lemma* discrete_quotient.fiber_open
- \+ *def* discrete_quotient.of_clopen
- \+ *def* discrete_quotient.of_le
- \+ *lemma* discrete_quotient.of_le_continuous
- \+ *lemma* discrete_quotient.of_le_proj
- \+ *lemma* discrete_quotient.of_le_proj_apply
- \+ *def* discrete_quotient.proj
- \+ *lemma* discrete_quotient.proj_continuous
- \+ *lemma* discrete_quotient.proj_is_locally_constant
- \+ *lemma* discrete_quotient.proj_surjective
- \+ *lemma* discrete_quotient.refl
- \+ *def* discrete_quotient.setoid
- \+ *lemma* discrete_quotient.symm
- \+ *lemma* discrete_quotient.trans



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
- \+ *lemma* complex.eq_conj_iff_im

Modified src/data/complex/module.lean
- \+ *def* complex.conj_alg_equiv

Modified src/data/fintype/basic.lean
- \+/\- *lemma* set.to_finset_empty

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.root_set_finite

Modified src/field_theory/polynomial_galois_group.lean
- \+ *lemma* polynomial.gal.gal_action_hom_bijective_of_prime_degree
- \+ *lemma* polynomial.gal.gal_action_hom_bijective_of_prime_degree_aux
- \+ *lemma* polynomial.gal.gal_action_hom_restrict
- \+ *lemma* polynomial.gal.splits_ℚ_ℂ

Modified src/group_theory/subgroup.lean
- \+ *lemma* monoid_hom.of_injective_apply
- \+ *def* monoid_hom.of_left_inverse
- \+ *lemma* monoid_hom.of_left_inverse_apply
- \+ *lemma* monoid_hom.of_left_inverse_symm_apply



## [2021-05-02 00:17:41](https://github.com/leanprover-community/mathlib/commit/6624bbe)
feat(category_theory/limits): dualizing some results ([#7391](https://github.com/leanprover-community/mathlib/pull/7391))
Requested on [zulip](https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/LocallyConstant.20preserves.20colimits/near/236442281).
#### Estimated changes
Renamed src/category_theory/limits/shapes/constructions/finite_products_of_binary_products.lean to src/category_theory/limits/constructions/finite_products_of_binary_products.lean
- \+ *def* category_theory.extend_cofan
- \+ *def* category_theory.extend_cofan_is_colimit
- \+ *lemma* category_theory.has_finite_coproducts_of_has_binary_and_terminal
- \+ *def* category_theory.preserves_finite_coproducts_of_preserves_binary_and_initial
- \+ *def* category_theory.preserves_ulift_fin_of_preserves_binary_and_initial

Modified src/category_theory/limits/constructions/limits_of_products_and_equalizers.lean
- \+ *lemma* category_theory.limits.colimits_from_coequalizers_and_coproducts
- \+ *lemma* category_theory.limits.finite_colimits_from_coequalizers_and_finite_coproducts
- \+ *lemma* category_theory.limits.has_colimit_of_coequalizer_and_coproduct
- \+ *def* category_theory.limits.has_colimit_of_has_coproducts_of_has_coequalizers.build_colimit
- \+ *def* category_theory.limits.has_colimit_of_has_coproducts_of_has_coequalizers.build_is_colimit
- \+ *def* category_theory.limits.preserves_colimit_of_preserves_coequalizers_and_coproduct
- \+ *def* category_theory.limits.preserves_colimits_of_preserves_coequalizers_and_coproducts
- \+ *def* category_theory.limits.preserves_finite_colimits_of_preserves_coequalizers_and_finite_coproducts

Modified src/category_theory/limits/preserves/shapes/binary_products.lean
- \+ *def* category_theory.limits.is_colimit_map_cocone_binary_cofan_equiv
- \+ *def* category_theory.limits.is_colimit_of_has_binary_coproduct_of_preserves_colimit
- \+ *def* category_theory.limits.is_colimit_of_reflects_of_map_is_colimit
- \+ *def* category_theory.limits.map_is_colimit_of_preserves_of_is_colimit
- \+ *def* category_theory.limits.preserves_colimit_pair.iso
- \+ *lemma* category_theory.limits.preserves_colimit_pair.iso_hom
- \+ *def* category_theory.limits.preserves_colimit_pair.of_iso_coprod_comparison
- \+ *def* category_theory.limits.preserves_limit_pair.iso
- \+ *lemma* category_theory.limits.preserves_limit_pair.iso_hom
- \+ *def* category_theory.limits.preserves_limit_pair.of_iso_prod_comparison
- \- *def* category_theory.limits.preserves_pair.iso
- \- *lemma* category_theory.limits.preserves_pair.iso_hom
- \- *def* category_theory.limits.preserves_pair.of_iso_comparison

Modified src/category_theory/limits/preserves/shapes/products.lean
- \+ *def* category_theory.limits.is_colimit_cofan_mk_obj_of_is_colimit
- \+ *def* category_theory.limits.is_colimit_map_cocone_cofan_mk_equiv
- \+ *def* category_theory.limits.is_colimit_of_has_coproduct_of_preserves_colimit
- \+ *def* category_theory.limits.is_colimit_of_is_colimit_cofan_mk_obj
- \+ *lemma* category_theory.limits.preserves_coproduct.inv_hom
- \+ *def* category_theory.limits.preserves_coproduct.iso
- \+ *def* category_theory.limits.preserves_coproduct.of_iso_comparison

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *def* category_theory.limits.coprod_comparison
- \+ *lemma* category_theory.limits.coprod_comparison_inl
- \+ *lemma* category_theory.limits.coprod_comparison_inr
- \+ *lemma* category_theory.limits.coprod_comparison_inv_natural
- \+ *def* category_theory.limits.coprod_comparison_nat_iso
- \+ *def* category_theory.limits.coprod_comparison_nat_trans
- \+ *lemma* category_theory.limits.coprod_comparison_natural
- \+/\- *def* category_theory.limits.coprod_is_coprod
- \+ *lemma* category_theory.limits.map_inl_inv_coprod_comparison
- \+ *lemma* category_theory.limits.map_inr_inv_coprod_comparison

Modified src/category_theory/limits/shapes/products.lean
- \+ *def* category_theory.limits.coproduct_is_coproduct



## [2021-05-02 00:17:39](https://github.com/leanprover-community/mathlib/commit/6e836c4)
feat(group_theory/perm/{cycles, cycle_type}): permutations are conjugate iff they have the same cycle type ([#7335](https://github.com/leanprover-community/mathlib/pull/7335))
Slightly strengthens the induction principle `equiv.perm.cycle_induction_on`
Proves that two permutations are conjugate iff they have the same cycle type: `equiv.perm.is_conj_iff_cycle_type_eq`
#### Estimated changes
Modified src/algebra/group/conj.lean
- \+ *lemma* conj_gpow
- \+ *lemma* conj_pow

Modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* equiv.perm.cycle_type_conj
- \+ *lemma* equiv.perm.filter_parts_partition_eq_cycle_type
- \+ *theorem* equiv.perm.is_conj_iff_cycle_type_eq
- \+ *theorem* equiv.perm.is_conj_of_cycle_type_eq
- \+ *lemma* equiv.perm.partition_eq_of_is_conj
- \+ *lemma* equiv.perm.parts_partition

Modified src/group_theory/perm/cycles.lean
- \+ *lemma* equiv.perm.card_support_conj
- \+ *theorem* equiv.perm.disjoint.is_conj_mul
- \+ *lemma* equiv.perm.is_cycle.is_cycle_conj
- \+ *lemma* equiv.perm.support_conj



## [2021-05-02 00:17:38](https://github.com/leanprover-community/mathlib/commit/106ac8e)
feat(category_theory): definition of R-linear category ([#7321](https://github.com/leanprover-community/mathlib/pull/7321))
#### Estimated changes
Modified src/algebra/category/Module/basic.lean


Added src/category_theory/linear/default.lean
- \+ *def* category_theory.linear.comp
- \+ *def* category_theory.linear.left_comp
- \+ *def* category_theory.linear.right_comp



## [2021-05-02 00:17:37](https://github.com/leanprover-community/mathlib/commit/decb556)
feat(geometry/euclidean/basic): lemmas about angles and distances ([#7140](https://github.com/leanprover-community/mathlib/pull/7140))
#### Estimated changes
Modified src/geometry/euclidean/basic.lean
- \+ *lemma* euclidean_geometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi
- \+ *lemma* euclidean_geometry.angle_left_midpoint_eq_pi_div_two_of_dist_eq
- \+ *lemma* euclidean_geometry.angle_midpoint_eq_pi
- \+ *lemma* euclidean_geometry.angle_right_midpoint_eq_pi_div_two_of_dist_eq
- \+ *lemma* euclidean_geometry.dist_eq_abs_sub_dist_iff_angle_eq_zero
- \+ *lemma* euclidean_geometry.dist_eq_abs_sub_dist_of_angle_eq_zero
- \+ *lemma* euclidean_geometry.dist_eq_add_dist_iff_angle_eq_pi
- \+ *lemma* euclidean_geometry.dist_eq_add_dist_of_angle_eq_pi
- \+ *lemma* euclidean_geometry.dist_left_midpoint_eq_dist_right_midpoint
- \+ *lemma* euclidean_geometry.left_dist_ne_zero_of_angle_eq_pi
- \+ *lemma* euclidean_geometry.right_dist_ne_zero_of_angle_eq_pi
- \+ *lemma* inner_product_geometry.inner_eq_mul_norm_iff_angle_eq_zero
- \+ *lemma* inner_product_geometry.inner_eq_mul_norm_of_angle_eq_zero
- \+ *lemma* inner_product_geometry.inner_eq_neg_mul_norm_iff_angle_eq_pi
- \+ *lemma* inner_product_geometry.inner_eq_neg_mul_norm_of_angle_eq_pi
- \+ *lemma* inner_product_geometry.norm_add_eq_add_norm_iff_angle_eq_zero
- \+ *lemma* inner_product_geometry.norm_add_eq_add_norm_of_angle_eq_zero
- \+ *lemma* inner_product_geometry.norm_add_eq_norm_sub_iff_angle_eq_pi_div_two
- \+ *lemma* inner_product_geometry.norm_sub_eq_abs_sub_norm_iff_angle_eq_zero
- \+ *lemma* inner_product_geometry.norm_sub_eq_abs_sub_norm_of_angle_eq_zero
- \+ *lemma* inner_product_geometry.norm_sub_eq_add_norm_iff_angle_eq_pi
- \+ *lemma* inner_product_geometry.norm_sub_eq_add_norm_of_angle_eq_pi



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
- \+ *lemma* finset.inf'_const
- \+ *lemma* finset.sup'_const

Modified src/order/filter/basic.lean
- \+ *lemma* filter.tendsto.frequently_map

Modified src/topology/algebra/algebra.lean
- \+ *lemma* subalgebra.subalgebra_topological_closure
- \- *lemma* subalgebra.subring_topological_closure

Modified src/topology/algebra/module.lean
- \+ *lemma* submodule.topological_closure_coe

Modified src/topology/algebra/ring.lean
- \+ *lemma* subsemiring.topological_closure_coe

Modified src/topology/continuous_function/basic.lean
- \+ *lemma* continuous_map.continuous_set_coe

Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.algebra_map_apply

Modified src/topology/continuous_function/compact.lean
- \+ *lemma* continuous_map.apply_le_norm
- \+ *lemma* continuous_map.neg_norm_le_apply

Added src/topology/continuous_function/stone_weierstrass.lean
- \+ *theorem* continuous_map.abs_mem_subalgebra_closure
- \+ *def* continuous_map.attach_bound
- \+ *lemma* continuous_map.attach_bound_apply_coe
- \+ *theorem* continuous_map.comp_attach_bound_mem_closure
- \+ *theorem* continuous_map.continuous_map_mem_subalgebra_closure_of_separates_points
- \+ *theorem* continuous_map.exists_mem_subalgebra_near_continuous_map_of_separates_points
- \+ *theorem* continuous_map.exists_mem_subalgebra_near_continuous_of_separates_points
- \+ *theorem* continuous_map.inf_mem_closed_subalgebra
- \+ *theorem* continuous_map.inf_mem_subalgebra_closure
- \+ *lemma* continuous_map.polynomial_comp_attach_bound
- \+ *lemma* continuous_map.polynomial_comp_attach_bound_mem
- \+ *theorem* continuous_map.subalgebra_topological_closure_eq_top_of_separates_points
- \+ *theorem* continuous_map.sublattice_closure_eq_top
- \+ *theorem* continuous_map.sup_mem_closed_subalgebra
- \+ *theorem* continuous_map.sup_mem_subalgebra_closure



## [2021-05-01 18:03:22](https://github.com/leanprover-community/mathlib/commit/d3c565d)
feat(category_theory/monoidal): the monoidal coherence theorem ([#7324](https://github.com/leanprover-community/mathlib/pull/7324))
This PR contains a proof of the monoidal coherence theorem, stated in the following way: if `C` is any type, then the free monoidal category over `C` is a preorder.
This should immediately imply the statement needed in the `coherence` branch.
#### Estimated changes
Modified docs/references.bib


Modified src/category_theory/monoidal/category.lean
- \+/\- *lemma* category_theory.monoidal_category.triangle_assoc_comp_left_inv
- \+/\- *lemma* category_theory.monoidal_category.triangle_assoc_comp_right
- \+/\- *lemma* category_theory.monoidal_category.triangle_assoc_comp_right_inv

Added src/category_theory/monoidal/free/basic.lean
- \+ *lemma* category_theory.free_monoidal_category.mk_comp
- \+ *lemma* category_theory.free_monoidal_category.mk_id
- \+ *lemma* category_theory.free_monoidal_category.mk_l_hom
- \+ *lemma* category_theory.free_monoidal_category.mk_l_inv
- \+ *lemma* category_theory.free_monoidal_category.mk_tensor
- \+ *lemma* category_theory.free_monoidal_category.mk_α_hom
- \+ *lemma* category_theory.free_monoidal_category.mk_α_inv
- \+ *lemma* category_theory.free_monoidal_category.mk_ρ_hom
- \+ *lemma* category_theory.free_monoidal_category.mk_ρ_inv
- \+ *def* category_theory.free_monoidal_category.project
- \+ *def* category_theory.free_monoidal_category.project_map
- \+ *def* category_theory.free_monoidal_category.project_map_aux
- \+ *def* category_theory.free_monoidal_category.project_obj
- \+ *def* category_theory.free_monoidal_category.setoid_hom
- \+ *lemma* category_theory.free_monoidal_category.tensor_eq_tensor
- \+ *lemma* category_theory.free_monoidal_category.unit_eq_unit

Added src/category_theory/monoidal/free/coherence.lean
- \+ *def* category_theory.free_monoidal_category.full_normalize
- \+ *def* category_theory.free_monoidal_category.full_normalize_iso
- \+ *def* category_theory.free_monoidal_category.inclusion
- \+ *def* category_theory.free_monoidal_category.inclusion_obj
- \+ *def* category_theory.free_monoidal_category.inverse_aux
- \+ *def* category_theory.free_monoidal_category.normalize'
- \+ *def* category_theory.free_monoidal_category.normalize
- \+ *def* category_theory.free_monoidal_category.normalize_iso
- \+ *def* category_theory.free_monoidal_category.normalize_iso_app
- \+ *lemma* category_theory.free_monoidal_category.normalize_iso_app_tensor
- \+ *lemma* category_theory.free_monoidal_category.normalize_iso_app_unitor
- \+ *def* category_theory.free_monoidal_category.normalize_iso_aux
- \+ *def* category_theory.free_monoidal_category.normalize_map_aux
- \+ *def* category_theory.free_monoidal_category.normalize_obj
- \+ *lemma* category_theory.free_monoidal_category.normalize_obj_tensor
- \+ *lemma* category_theory.free_monoidal_category.normalize_obj_unitor
- \+ *def* category_theory.free_monoidal_category.tensor_func
- \+ *lemma* category_theory.free_monoidal_category.tensor_func_map_app
- \+ *lemma* category_theory.free_monoidal_category.tensor_func_obj_map



## [2021-05-01 15:16:03](https://github.com/leanprover-community/mathlib/commit/790ec6b)
feat(algebra/archimedean): rat.cast_round for non-archimedean fields ([#7424](https://github.com/leanprover-community/mathlib/pull/7424))
The theorem still applies to the non-canonical archimedean instance (at least if you use simp).  I've also added `rat.cast_ceil` because it seems to fit here.
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+/\- *lemma* abs_sub_round
- \+ *theorem* rat.cast_ceil
- \+/\- *theorem* rat.cast_floor
- \+/\- *theorem* rat.cast_round
- \+/\- *def* round

Modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean
- \+/\- *theorem* generalized_continued_fraction.terminates_iff_rat



## [2021-05-01 15:16:02](https://github.com/leanprover-community/mathlib/commit/92b9048)
chore(topology/continuous_function/algebra): put `coe_fn_monoid_hom `into the `continuous_map` namespace ([#7423](https://github.com/leanprover-community/mathlib/pull/7423))
Rather than adding `continuous_map.` to the definition, this wraps everything in a namespace to make this type of mistake unlikely to happen again.
This also adds `comp_monoid_hom'` to golf a proof.
#### Estimated changes
Modified src/topology/continuous_function/algebra.lean
- \- *def* coe_fn_monoid_hom
- \+ *def* continuous_map.coe_fn_monoid_hom
- \+/\- *lemma* continuous_map.coe_prod
- \+ *def* continuous_map.comp_monoid_hom'
- \+/\- *lemma* continuous_map.div_coe
- \+/\- *lemma* continuous_map.div_comp
- \+/\- *lemma* continuous_map.inv_coe
- \+/\- *lemma* continuous_map.inv_comp
- \+ *lemma* continuous_map.one_comp
- \+/\- *lemma* continuous_map.pow_coe
- \+/\- *lemma* continuous_map.pow_comp
- \+/\- *lemma* continuous_map.prod_apply
- \+/\- *lemma* continuous_map.smul_apply
- \+/\- *lemma* continuous_map.smul_coe
- \+/\- *lemma* continuous_map.smul_comp



## [2021-05-01 09:09:54](https://github.com/leanprover-community/mathlib/commit/5511275)
chore(measure_theory/ae_eq_fun_metric): remove useless file ([#7419](https://github.com/leanprover-community/mathlib/pull/7419))
The file `measure_theory/ae_eq_fun_metric.lean` used to contain an edistance on the space of equivalence classes of functions. It has been replaced by the use of the `L^1` space in [#5510](https://github.com/leanprover-community/mathlib/pull/5510), so this file is now useless and should be removed.
#### Estimated changes
Deleted src/measure_theory/ae_eq_fun_metric.lean
- \- *lemma* measure_theory.ae_eq_fun.coe_fn_edist
- \- *lemma* measure_theory.ae_eq_fun.edist_add_right
- \- *lemma* measure_theory.ae_eq_fun.edist_eq_coe'
- \- *lemma* measure_theory.ae_eq_fun.edist_eq_coe
- \- *lemma* measure_theory.ae_eq_fun.edist_mk_mk'
- \- *lemma* measure_theory.ae_eq_fun.edist_mk_mk
- \- *lemma* measure_theory.ae_eq_fun.edist_smul
- \- *lemma* measure_theory.ae_eq_fun.edist_zero_eq_coe



## [2021-05-01 09:09:53](https://github.com/leanprover-community/mathlib/commit/d04af20)
feat(linear_algebra/quadratic_form): add lemmas about sums of quadratic forms ([#7417](https://github.com/leanprover-community/mathlib/pull/7417))
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean
- \+ *def* quadratic_form.coe_fn_add_monoid_hom
- \+ *lemma* quadratic_form.coe_fn_sum
- \+ *lemma* quadratic_form.coe_fn_zero
- \+ *def* quadratic_form.eval_add_monoid_hom
- \+ *lemma* quadratic_form.sum_apply



## [2021-05-01 09:09:52](https://github.com/leanprover-community/mathlib/commit/bf0f15a)
chore(algebra/algebra/basic): add missing lemmas ([#7412](https://github.com/leanprover-community/mathlib/pull/7412))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+/\- *lemma* alg_equiv.coe_refl
- \+ *lemma* alg_equiv.coe_trans
- \+ *theorem* alg_equiv.left_inverse_symm
- \+ *lemma* alg_equiv.refl_to_alg_hom
- \+ *theorem* alg_equiv.right_inverse_symm
- \+/\- *lemma* alg_equiv.trans_apply
- \+ *lemma* alg_hom.coe_comp
- \+ *lemma* alg_hom.coe_id
- \+/\- *lemma* alg_hom.comp_apply
- \+ *lemma* alg_hom.comp_to_ring_hom
- \+/\- *lemma* alg_hom.id_apply
- \+ *lemma* alg_hom.id_to_ring_hom



## [2021-05-01 06:41:10](https://github.com/leanprover-community/mathlib/commit/e3de4e3)
fix(algebra/direct_sum_graded): replace badly-stated and slow `simps` lemmas with manual ones  ([#7403](https://github.com/leanprover-community/mathlib/pull/7403))
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/simps.20is.20very.20slow/near/236636962). The `simps mul` attribute on `direct_sum.ghas_mul.of_add_subgroups` was taking 44s, only to produce a lemma that wasn't very useful anyway.
#### Estimated changes
Modified src/algebra/direct_sum_graded.lean
- \+ *lemma* direct_sum.ghas_mul.of_add_subgroups_mul
- \+ *lemma* direct_sum.ghas_mul.of_add_submonoids_mul
- \+ *lemma* direct_sum.ghas_mul.of_submodules_mul



## [2021-05-01 06:41:09](https://github.com/leanprover-community/mathlib/commit/aa37eee)
feat(analysis/special_functions/integrals): integral of `cos x ^ n` ([#7402](https://github.com/leanprover-community/mathlib/pull/7402))
The reduction of `∫ x in a..b, cos x ^ n`, ∀ n ∈ ℕ, 2 ≤ n, as well as the integral of `cos x ^ 2` as a special case.
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* integral_cos_pow
- \+ *lemma* integral_cos_pow_aux
- \+ *lemma* integral_cos_sq

Modified test/integration.lean




## [2021-05-01 06:41:08](https://github.com/leanprover-community/mathlib/commit/2cc8128)
feat(algebra/polynomial): generalize to `multiset` products ([#7399](https://github.com/leanprover-community/mathlib/pull/7399))
This PR generalizes the results in `algebra.polynomial.big_operators` to sums and products of multisets.
The new multiset results are stated for `multiset.prod t`, not `(multiset.map t f).prod`. To get the latter, you can simply rewrite with `multiset.map_map`.
#### Estimated changes
Modified src/algebra/polynomial/big_operators.lean
- \+ *lemma* polynomial.coeff_zero_multiset_prod
- \+ *lemma* polynomial.degree_multiset_prod
- \+ *lemma* polynomial.leading_coeff_multiset_prod'
- \+ *lemma* polynomial.leading_coeff_multiset_prod
- \+ *lemma* polynomial.multiset_prod_X_sub_C_coeff_card_pred
- \+ *lemma* polynomial.multiset_prod_X_sub_C_next_coeff
- \+ *lemma* polynomial.nat_degree_multiset_prod'
- \+ *lemma* polynomial.nat_degree_multiset_prod_le
- \+ *lemma* polynomial.nat_degree_multiset_prod_of_monic

Modified src/data/polynomial/monic.lean
- \+ *lemma* polynomial.monic.next_coeff_multiset_prod
- \+ *lemma* polynomial.monic_multiset_prod_of_monic



## [2021-05-01 00:19:22](https://github.com/leanprover-community/mathlib/commit/d5d22c5)
feat(algebra/squarefree): add sq_mul_squarefree lemmas ([#7282](https://github.com/leanprover-community/mathlib/pull/7282))
Every positive natural number can be expressed as m^2 * n where n is square free. Used in [#7274](https://github.com/leanprover-community/mathlib/pull/7274)
#### Estimated changes
Modified src/algebra/squarefree.lean
- \+ *lemma* nat.sq_mul_squarefree
- \+ *lemma* nat.sq_mul_squarefree_of_pos'
- \+ *lemma* nat.sq_mul_squarefree_of_pos



## [2021-05-01 00:19:21](https://github.com/leanprover-community/mathlib/commit/b51cee2)
feat(data/polynomial/coeff): Add smul_eq_C_mul ([#7240](https://github.com/leanprover-community/mathlib/pull/7240))
Adding a lemma `polynomial.smul_eq_C_mul` for single variate polynomials analogous to `mv_polynomial.smul_eq_C_mul` for multivariate.
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *def* polynomial.C
- \+ *lemma* polynomial.C_0
- \+ *lemma* polynomial.C_1
- \+ *lemma* polynomial.C_add
- \+ *lemma* polynomial.C_bit0
- \+ *lemma* polynomial.C_bit1
- \+ *lemma* polynomial.C_eq_nat_cast
- \+ *lemma* polynomial.C_eq_zero
- \+ *lemma* polynomial.C_inj
- \+ *lemma* polynomial.C_mul
- \+ *lemma* polynomial.C_pow
- \+ *lemma* polynomial.coeff_C
- \+ *lemma* polynomial.coeff_C_ne_zero
- \+ *lemma* polynomial.coeff_C_zero
- \+ *lemma* polynomial.monomial_eq_smul_X
- \+ *lemma* polynomial.monomial_zero_left
- \+ *theorem* polynomial.nontrivial.of_polynomial_ne
- \+ *lemma* polynomial.single_eq_C_mul_X
- \+ *lemma* polynomial.sum_C_index

Modified src/data/polynomial/coeff.lean


Modified src/data/polynomial/degree/definitions.lean


Modified src/data/polynomial/monomial.lean
- \- *def* polynomial.C
- \- *lemma* polynomial.C_0
- \- *lemma* polynomial.C_1
- \- *lemma* polynomial.C_add
- \- *lemma* polynomial.C_bit0
- \- *lemma* polynomial.C_bit1
- \- *lemma* polynomial.C_eq_nat_cast
- \- *lemma* polynomial.C_eq_zero
- \- *lemma* polynomial.C_inj
- \- *lemma* polynomial.C_mul
- \- *lemma* polynomial.C_pow
- \- *lemma* polynomial.coeff_C
- \- *lemma* polynomial.coeff_C_ne_zero
- \- *lemma* polynomial.coeff_C_zero
- \- *lemma* polynomial.monomial_eq_smul_X
- \- *lemma* polynomial.monomial_zero_left
- \- *theorem* polynomial.nontrivial.of_polynomial_ne
- \- *lemma* polynomial.single_eq_C_mul_X
- \+ *lemma* polynomial.smul_eq_C_mul
- \- *lemma* polynomial.sum_C_index



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


Added src/category_theory/enriched/basic.lean
- \+ *def* category_theory.category_of_enriched_category_Type
- \+ *lemma* category_theory.e_assoc
- \+ *def* category_theory.e_comp
- \+ *lemma* category_theory.e_comp_id
- \+ *def* category_theory.e_id
- \+ *lemma* category_theory.e_id_comp
- \+ *def* category_theory.enriched_category_Type_equiv_category
- \+ *def* category_theory.enriched_category_Type_of_category
- \+ *def* category_theory.enriched_functor.comp
- \+ *def* category_theory.enriched_functor.forget
- \+ *def* category_theory.enriched_functor.id
- \+ *def* category_theory.enriched_functor_Type_equiv_functor
- \+ *def* category_theory.enriched_nat_trans_yoneda
- \+ *def* category_theory.enriched_nat_trans_yoneda_Type_iso_yoneda_nat_trans
- \+ *def* category_theory.forget_enrichment.hom_of
- \+ *lemma* category_theory.forget_enrichment.hom_of_hom_to
- \+ *def* category_theory.forget_enrichment.hom_to
- \+ *lemma* category_theory.forget_enrichment.hom_to_hom_of
- \+ *def* category_theory.forget_enrichment.of
- \+ *lemma* category_theory.forget_enrichment.of_to
- \+ *def* category_theory.forget_enrichment.to
- \+ *lemma* category_theory.forget_enrichment.to_of
- \+ *def* category_theory.forget_enrichment
- \+ *lemma* category_theory.forget_enrichment_comp
- \+ *lemma* category_theory.forget_enrichment_id'
- \+ *lemma* category_theory.forget_enrichment_id
- \+ *def* category_theory.transport_enrichment

Modified src/category_theory/monoidal/braided.lean


Modified src/category_theory/monoidal/category.lean
- \+ *lemma* category_theory.monoidal_category.unitors_inv_equal

Modified src/category_theory/monoidal/center.lean
- \+ *lemma* category_theory.center.ext
- \+ *def* category_theory.center.of_braided
- \+ *def* category_theory.center.of_braided_obj
- \+ *lemma* category_theory.center.tensor_unit_β

Modified src/category_theory/monoidal/functor.lean
- \+ *lemma* category_theory.lax_monoidal_functor.associativity_inv
- \+ *lemma* category_theory.lax_monoidal_functor.left_unitality_inv
- \+ *lemma* category_theory.lax_monoidal_functor.right_unitality_inv

Modified src/category_theory/monoidal/internal/types.lean


Modified src/category_theory/monoidal/types.lean
- \+ *lemma* category_theory.associator_hom_apply
- \+ *lemma* category_theory.associator_inv_apply
- \+ *lemma* category_theory.braiding_hom_apply
- \+ *lemma* category_theory.braiding_inv_apply
- \+ *def* category_theory.coyoneda_tensor_unit
- \+ *lemma* category_theory.left_unitor_hom_apply
- \+ *lemma* category_theory.left_unitor_inv_apply
- \- *lemma* category_theory.monoidal.associator_hom_apply
- \- *lemma* category_theory.monoidal.associator_inv_apply
- \- *lemma* category_theory.monoidal.braiding_hom_apply
- \- *lemma* category_theory.monoidal.braiding_inv_apply
- \- *lemma* category_theory.monoidal.left_unitor_hom_apply
- \- *lemma* category_theory.monoidal.left_unitor_inv_apply
- \- *lemma* category_theory.monoidal.right_unitor_hom_apply
- \- *lemma* category_theory.monoidal.right_unitor_inv_apply
- \- *lemma* category_theory.monoidal.tensor_apply
- \+ *lemma* category_theory.right_unitor_hom_apply
- \+ *lemma* category_theory.right_unitor_inv_apply
- \+ *lemma* category_theory.tensor_apply



## [2021-05-01 00:19:19](https://github.com/leanprover-community/mathlib/commit/802c5b5)
feat(linear_algebra/determinant): various operations preserve the determinant ([#7115](https://github.com/leanprover-community/mathlib/pull/7115))
These are a couple of helper lemmas for computing the determinant of a Vandermonde matrix.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.update_column_eq_self
- \+ *lemma* matrix.update_row_eq_self

Modified src/linear_algebra/determinant.lean
- \+ *lemma* matrix.det_eq_of_eq_det_one_mul
- \+ *lemma* matrix.det_eq_of_eq_mul_det_one
- \+ *lemma* matrix.det_eq_of_forall_col_eq_smul_add_pred
- \+ *lemma* matrix.det_eq_of_forall_row_eq_smul_add_const
- \+ *lemma* matrix.det_eq_of_forall_row_eq_smul_add_const_aux
- \+ *lemma* matrix.det_eq_of_forall_row_eq_smul_add_pred
- \+ *lemma* matrix.det_eq_of_forall_row_eq_smul_add_pred_aux
- \+ *lemma* matrix.det_mul_column
- \+ *lemma* matrix.det_mul_row
- \+ *lemma* matrix.det_update_column_add_self
- \+ *lemma* matrix.det_update_column_add_smul_self
- \+ *lemma* matrix.det_update_row_add_self
- \+ *lemma* matrix.det_update_row_add_smul_self
- \+ *theorem* matrix.det_zero_of_column_eq



## [2021-05-01 00:19:18](https://github.com/leanprover-community/mathlib/commit/6c61779)
refactor(group_theory/order_of_element): use minimal_period for the definition ([#7082](https://github.com/leanprover-community/mathlib/pull/7082))
This PR redefines `order_of_element` in terms of `function.minimal_period`. It furthermore introduces a predicate on elements of a finite group to be of finite order.
Co-authored by: Damiano Testa adomani@gmail.com
#### Estimated changes
Modified src/algebra/char_p/basic.lean


Modified src/algebra/group/basic.lean
- \+ *lemma* mul_one_eq_id
- \+ *lemma* one_mul_eq_id

Modified src/algebra/iterate_hom.lean
- \+/\- *lemma* add_left_iterate
- \+/\- *lemma* add_right_iterate
- \+ *lemma* add_right_iterate_apply_zero
- \+ *lemma* commute.function_commute_mul_left
- \+ *lemma* commute.function_commute_mul_right
- \+/\- *lemma* mul_left_iterate
- \+/\- *lemma* mul_right_iterate
- \+ *lemma* mul_right_iterate_apply_one
- \+ *lemma* semiconj_by.function_semiconj_mul_left
- \+ *lemma* semiconj_by.function_semiconj_mul_right_swap

Modified src/algebra/regular.lean


Modified src/dynamics/periodic_pts.lean
- \+ *lemma* function.commute.minimal_period_of_comp_dvd_lcm
- \+ *lemma* function.is_fixed_point_iff_minimal_period_eq_one
- \+ *lemma* function.iterate_eq_mod_minimal_period
- \+ *lemma* function.minimal_period_eq_minimal_period_iff
- \+ *lemma* function.minimal_period_eq_prime
- \+ *lemma* function.minimal_period_eq_prime_pow
- \+ *lemma* function.minimal_period_id
- \+ *lemma* function.minimal_period_iterate_eq_div_gcd'
- \+ *lemma* function.minimal_period_iterate_eq_div_gcd
- \+ *lemma* function.nat_dvd_iff_right
- \+ *lemma* function.not_is_periodic_pt_of_pos_of_lt_minimal_period

Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* add_order_eq_card_gmultiples
- \+/\- *lemma* add_order_of_dvd_card_univ
- \+/\- *lemma* add_order_of_dvd_iff_nsmul_eq_zero
- \+/\- *lemma* add_order_of_dvd_of_nsmul_eq_zero
- \+/\- *lemma* add_order_of_eq_add_order_of_iff
- \+/\- *lemma* add_order_of_eq_card_multiples
- \+/\- *lemma* add_order_of_eq_one_iff
- \+/\- *lemma* add_order_of_eq_prime
- \+/\- *lemma* add_order_of_eq_prime_pow
- \- *lemma* add_order_of_eq_zero
- \+/\- *lemma* add_order_of_injective
- \+/\- *lemma* add_order_of_le_card_univ
- \- *lemma* add_order_of_le_of_nsmul_eq_zero'
- \+/\- *lemma* add_order_of_le_of_nsmul_eq_zero
- \+/\- *lemma* add_order_of_nsmul''
- \+/\- *lemma* add_order_of_nsmul
- \+/\- *lemma* add_order_of_nsmul_eq_zero
- \+/\- *lemma* add_order_of_of_mul_eq_order_of
- \- *lemma* add_order_of_pos'
- \+/\- *lemma* add_order_of_pos
- \+/\- *lemma* add_order_of_zero
- \+/\- *lemma* card_nsmul_eq_zero
- \+/\- *lemma* commute.order_of_mul_dvd_lcm
- \+/\- *lemma* exists_gpow_eq_one
- \+/\- *lemma* exists_gsmul_eq_zero
- \+/\- *lemma* exists_nsmul_eq_self_of_coprime
- \+/\- *lemma* exists_nsmul_eq_zero
- \+/\- *lemma* exists_pow_eq_one
- \+/\- *lemma* exists_pow_eq_self_of_coprime
- \+/\- *lemma* fin_equiv_gmultiples_apply
- \+/\- *lemma* fin_equiv_gmultiples_symm_apply
- \+/\- *lemma* fin_equiv_gpowers_apply
- \+/\- *lemma* fin_equiv_gpowers_symm_apply
- \+/\- *lemma* fin_equiv_multiples_apply
- \+/\- *lemma* fin_equiv_multiples_symm_apply
- \+/\- *lemma* fin_equiv_powers_apply
- \+/\- *lemma* fin_equiv_powers_symm_apply
- \+/\- *lemma* gcd_nsmul_card_eq_zero_iff
- \+/\- *lemma* gmultiples_equiv_gmultiples_apply
- \+/\- *lemma* gpow_eq_mod_order_of
- \+/\- *lemma* gpowers_equiv_gpowers_apply
- \+/\- *lemma* gsmul_eq_mod_add_order_of
- \+/\- *lemma* image_range_add_order_of
- \+/\- *lemma* image_range_order_of
- \+ *def* is_of_fin_add_order
- \+ *lemma* is_of_fin_add_order_iff_nsmul_eq_zero
- \+ *lemma* is_of_fin_add_order_of_mul_iff
- \+ *def* is_of_fin_order
- \+ *lemma* is_of_fin_order_iff_pow_eq_one
- \+ *lemma* is_of_fin_order_of_add_iff
- \+ *lemma* is_periodic_pt_add_iff_nsmul_eq_zero
- \+ *lemma* is_periodic_pt_mul_iff_pow_eq_one
- \+/\- *lemma* mem_gmultiples_iff_mem_range_add_order_of
- \+/\- *lemma* mem_gpowers_iff_mem_range_order_of
- \+/\- *lemma* mem_multiples_iff_mem_gmultiples
- \+/\- *lemma* mem_multiples_iff_mem_range_add_order_of
- \+/\- *lemma* mem_powers_iff_mem_gpowers
- \+/\- *lemma* mem_powers_iff_mem_range_order_of
- \+/\- *lemma* multiples_eq_gmultiples
- \+/\- *lemma* multiples_equiv_multiples_apply
- \+/\- *lemma* nsmul_eq_mod_add_order_of
- \+ *lemma* nsmul_ne_zero_of_lt_add_order_of'
- \+/\- *lemma* order_eq_card_gpowers
- \+/\- *lemma* order_eq_card_powers
- \+/\- *lemma* order_of_dvd_card_univ
- \+/\- *lemma* order_of_dvd_iff_pow_eq_one
- \+/\- *lemma* order_of_dvd_of_pow_eq_one
- \+/\- *lemma* order_of_eq_one_iff
- \+/\- *lemma* order_of_eq_order_of_iff
- \+/\- *lemma* order_of_eq_prime
- \+/\- *lemma* order_of_eq_prime_pow
- \+/\- *lemma* order_of_eq_zero
- \+/\- *lemma* order_of_injective
- \+/\- *lemma* order_of_le_card_univ
- \- *lemma* order_of_le_of_pow_eq_one'
- \+/\- *lemma* order_of_le_of_pow_eq_one
- \+/\- *lemma* order_of_of_add_eq_add_order_of
- \+/\- *lemma* order_of_one
- \+/\- *lemma* order_of_pos'
- \+/\- *lemma* order_of_pos
- \+/\- *lemma* order_of_pow''
- \+/\- *lemma* order_of_pow
- \+/\- *lemma* order_of_subgroup
- \+/\- *lemma* order_of_submonoid
- \+/\- *lemma* pow_card_eq_one
- \+/\- *lemma* pow_eq_mod_order_of
- \+ *lemma* pow_eq_one_of_lt_order_of'
- \+/\- *lemma* pow_gcd_card_eq_one_iff
- \+/\- *lemma* pow_injective_aux
- \+/\- *lemma* pow_injective_of_lt_order_of
- \+/\- *lemma* pow_order_of_eq_one
- \+/\- *lemma* powers_eq_gpowers
- \+/\- *lemma* powers_equiv_powers_apply
- \+/\- *lemma* sum_card_add_order_of_eq_card_nsmul_eq_zero
- \+/\- *lemma* sum_card_order_of_eq_card_pow_eq_one

Modified src/group_theory/specific_groups/dihedral.lean


Modified src/group_theory/specific_groups/quaternion.lean


Modified src/group_theory/sylow.lean


Modified src/topology/algebra/ordered.lean


