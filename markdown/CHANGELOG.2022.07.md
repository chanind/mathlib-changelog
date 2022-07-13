## [2022-07-13 09:50:47](https://github.com/leanprover-community/mathlib/commit/83092fb)
feat(data/matrix/notation): add `!![1, 2; 3, 4]` notation ([#14991](https://github.com/leanprover-community/mathlib/pull/14991))
This adds `!![1, 2; 3, 4]` as a matlab-like shorthand for `matrix.of ![![1, 2], ![3, 4]]`. This has special support for empty arrays, where `!![,,,]` is a matrix with 0 rows and 3 columns, and `![;;;]` is a matrix with 3 rows and zero columns.
#### Estimated changes
Modified src/data/fin/vec_notation.lean


Modified src/data/matrix/notation.lean
- \+/\- *lemma* one_fin_two
- \+/\- *lemma* one_fin_three

Modified src/tactic/core.lean


Modified src/tactic/reserved_notation.lean


Modified test/matrix.lean




## [2022-07-13 09:50:45](https://github.com/leanprover-community/mathlib/commit/01a1824)
feat(data/polynomial/unit_trinomial): An irreducibility criterion for unit trinomials ([#14914](https://github.com/leanprover-community/mathlib/pull/14914))
This PR adds an irreducibility criterion for unit trinomials. This is building up to irreducibility of $x^n-x-1$.
#### Estimated changes
Created src/data/polynomial/unit_trinomial.lean
- \+ *lemma* trinomial_def
- \+ *lemma* trinomial_leading_coeff'
- \+ *lemma* trinomial_middle_coeff
- \+ *lemma* trinomial_trailing_coeff'
- \+ *lemma* trinomial_nat_degree
- \+ *lemma* trinomial_nat_trailing_degree
- \+ *lemma* trinomial_leading_coeff
- \+ *lemma* trinomial_trailing_coeff
- \+ *lemma* trinomial_mirror
- \+ *lemma* trinomial_support
- \+ *lemma* not_is_unit
- \+ *lemma* card_support_eq_three
- \+ *lemma* ne_zero
- \+ *lemma* coeff_is_unit
- \+ *lemma* leading_coeff_is_unit
- \+ *lemma* trailing_coeff_is_unit
- \+ *lemma* is_unit_trinomial_iff
- \+ *lemma* is_unit_trinomial_iff'
- \+ *lemma* is_unit_trinomial_iff''
- \+ *lemma* irreducible_aux1
- \+ *lemma* irreducible_aux2
- \+ *lemma* irreducible_aux3
- \+ *lemma* irreducible_of_coprime
- \+ *lemma* irreducible_of_is_coprime
- \+ *def* is_unit_trinomial



## [2022-07-13 09:50:44](https://github.com/leanprover-community/mathlib/commit/581b694)
feat(data/polynomial/erase_lead): Characterization of polynomials of fixed support ([#14741](https://github.com/leanprover-community/mathlib/pull/14741))
This PR adds a lemma characterizing polynomials of fixed support.
#### Estimated changes
Modified src/data/polynomial/erase_lead.lean
- \+ *lemma* card_support_eq'
- \+ *lemma* card_support_eq



## [2022-07-13 09:09:29](https://github.com/leanprover-community/mathlib/commit/7340203)
feat(information_theory/hamming): add Hamming distance and norm ([#14739](https://github.com/leanprover-community/mathlib/pull/14739))
Add the Hamming distance, Hamming norm, and a `hamming` type synonym equipped with a normed group instance using the Hamming norm.
#### Estimated changes
Created src/information_theory/hamming.lean
- \+ *lemma* hamming_dist_self
- \+ *lemma* hamming_dist_nonneg
- \+ *lemma* hamming_dist_comm
- \+ *lemma* hamming_dist_triangle
- \+ *lemma* hamming_dist_triangle_left
- \+ *lemma* hamming_dist_triangle_right
- \+ *lemma* eq_of_hamming_dist_eq_zero
- \+ *lemma* hamming_dist_eq_zero
- \+ *lemma* hamming_zero_eq_dist
- \+ *lemma* hamming_dist_ne_zero
- \+ *lemma* hamming_dist_pos
- \+ *lemma* hamming_dist_lt_one
- \+ *lemma* hamming_dist_le_card_fintype
- \+ *lemma* hamming_dist_comp_le_hamming_dist
- \+ *lemma* hamming_dist_comp
- \+ *lemma* hamming_dist_smul_le_hamming_dist
- \+ *lemma* hamming_dist_smul
- \+ *lemma* hamming_dist_zero_right
- \+ *lemma* hamming_dist_zero_left
- \+ *lemma* hamming_norm_nonneg
- \+ *lemma* hamming_norm_zero
- \+ *lemma* hamming_norm_eq_zero
- \+ *lemma* hamming_norm_ne_zero_iff
- \+ *lemma* hamming_norm_pos_iff
- \+ *lemma* hamming_norm_lt_one
- \+ *lemma* hamming_norm_le_card_fintype
- \+ *lemma* hamming_norm_comp_le_hamming_norm
- \+ *lemma* hamming_norm_comp
- \+ *lemma* hamming_norm_smul_le_hamming_norm
- \+ *lemma* hamming_norm_smul
- \+ *lemma* hamming_dist_eq_hamming_norm
- \+ *lemma* to_hamming_symm_eq
- \+ *lemma* of_hamming_symm_eq
- \+ *lemma* to_hamming_of_hamming
- \+ *lemma* of_hamming_to_hamming
- \+ *lemma* to_hamming_inj
- \+ *lemma* of_hamming_inj
- \+ *lemma* to_hamming_zero
- \+ *lemma* of_hamming_zero
- \+ *lemma* to_hamming_neg
- \+ *lemma* of_hamming_neg
- \+ *lemma* to_hamming_add
- \+ *lemma* of_hamming_add
- \+ *lemma* to_hamming_sub
- \+ *lemma* of_hamming_sub
- \+ *lemma* to_hamming_smul
- \+ *lemma* of_hamming_smul
- \+ *lemma* dist_eq_hamming_dist
- \+ *lemma* nndist_eq_hamming_dist
- \+ *lemma* norm_eq_hamming_norm
- \+ *lemma* nnnorm_eq_hamming_norm
- \+ *theorem* swap_hamming_dist
- \+ *def* hamming_dist
- \+ *def* hamming_norm
- \+ *def* hamming
- \+ *def* to_hamming
- \+ *def* of_hamming



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
- \- *lemma* forall_false_left
- \- *theorem* forall_pempty
- \- *theorem* exists_pempty

Modified src/logic/is_empty.lean
- \+/\- *lemma* forall_iff
- \+/\- *lemma* exists_iff

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
- \+/\- *lemma* is_clopen_bUnion
- \+ *lemma* is_clopen_bUnion_finset
- \+/\- *lemma* is_clopen_bInter
- \+ *lemma* is_clopen_bInter_finset



## [2022-07-13 02:40:32](https://github.com/leanprover-community/mathlib/commit/2a32596)
feat(data/finsupp/basic): graph of a finitely supported function ([#15197](https://github.com/leanprover-community/mathlib/pull/15197))
We define the graph of a finitely supported function, i.e. the finset of input/output pairs, and prove basic results.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* mk_mem_graph_iff
- \+ *lemma* mem_graph_iff
- \+ *lemma* mk_mem_graph
- \+ *lemma* apply_eq_of_mem_graph
- \+ *lemma* not_mem_graph_snd_zero
- \+ *lemma* image_fst_graph
- \+ *lemma* graph_injective
- \+ *lemma* graph_inj
- \+ *lemma* graph_zero
- \+ *lemma* graph_eq_empty
- \+ *def* graph



## [2022-07-13 02:40:31](https://github.com/leanprover-community/mathlib/commit/c6014bd)
feat(algebra/parity): more general odd.pos ([#15186](https://github.com/leanprover-community/mathlib/pull/15186))
The old version of this lemma (added in [#13040](https://github.com/leanprover-community/mathlib/pull/13040)) was only for ℕ and didn't allow dot notation. We remove this and add a version for `canonically_ordered_comm_semiring`s, and if the definition of `odd` changes, this will also work for `canononically_ordered_add_monoid`s.
#### Estimated changes
Modified archive/imo/imo1998_q2.lean


Modified src/algebra/parity.lean
- \+ *lemma* odd.pos

Modified src/data/nat/parity.lean
- \- *lemma* pos_of_odd



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
- \+ *lemma* topological_group.t3_space
- \- *lemma* topological_group.regular_space

Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* has_sum.sigma
- \+/\- *lemma* has_sum.prod_fiberwise
- \+/\- *lemma* summable.sigma'
- \+/\- *lemma* has_sum.sigma_of_has_sum
- \+/\- *lemma* tsum_sigma'
- \+/\- *lemma* tsum_prod'
- \+/\- *lemma* tsum_comm'

Modified src/topology/algebra/module/basic.lean


Modified src/topology/algebra/order/basic.lean


Modified src/topology/algebra/order/extend_from.lean


Modified src/topology/algebra/uniform_field.lean


Modified src/topology/algebra/valued_field.lean


Modified src/topology/algebra/with_zero_topology.lean


Modified src/topology/dense_embedding.lean
- \+/\- *lemma* continuous_at_extend
- \+/\- *lemma* continuous_extend

Modified src/topology/extend_from.lean
- \+/\- *lemma* continuous_on_extend_from
- \+/\- *lemma* continuous_extend_from

Modified src/topology/homeomorph.lean


Modified src/topology/metric_space/metrizable.lean
- \+ *lemma* metrizable_space_of_t3_second_countable
- \- *lemma* metrizable_space_of_regular_second_countable

Modified src/topology/separation.lean
- \+/\- *lemma* nhds_is_closed
- \+/\- *lemma* closed_nhds_basis
- \+/\- *lemma* topological_space.is_topological_basis.exists_closure_subset
- \+/\- *lemma* topological_space.is_topological_basis.nhds_basis_closure
- \+/\- *lemma* disjoint_nested_nhds
- \+/\- *lemma* exists_compact_between
- \+/\- *lemma* exists_open_between_and_is_compact_closure
- \+ *lemma* normal_space_of_t3_second_countable
- \- *lemma* normal_space_of_regular_second_countable

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
- \+ *lemma* of_apply
- \+ *lemma* of_symm_apply
- \+ *lemma* of_zero
- \+ *lemma* of_add_of
- \+ *lemma* of_sub_of
- \+ *lemma* neg_of
- \+ *lemma* smul_of
- \+ *def* of
- \+/\- *def* map

Modified src/data/matrix/block.lean


Modified src/data/matrix/notation.lean
- \+/\- *lemma* cons_val'
- \+/\- *lemma* head_val'
- \+/\- *lemma* tail_val'
- \+/\- *lemma* transpose_empty_rows
- \+/\- *lemma* transpose_empty_cols
- \+/\- *lemma* head_transpose
- \+/\- *lemma* tail_transpose
- \+/\- *lemma* cons_mul
- \+/\- *lemma* cons_vec_mul
- \+/\- *lemma* vec_mul_cons
- \+/\- *lemma* smul_mat_cons

Modified src/linear_algebra/matrix/basis.lean


Modified src/linear_algebra/matrix/bilinear_form.lean
- \+ *lemma* bilin_form.to_matrix_aux_apply

Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* det_fin_two_of
- \- *lemma* det_fin_two_mk

Modified src/linear_algebra/matrix/to_lin.lean


Modified src/linear_algebra/matrix/transvection.lean


Modified src/linear_algebra/vandermonde.lean


Modified src/logic/equiv/basic.lean
- \+/\- *theorem* perm.coe_subsingleton

Modified src/ring_theory/matrix_algebra.lean


Modified src/ring_theory/trace.lean
- \+/\- *lemma* trace_matrix_def

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
- \+ *lemma* open_embedding_iff_embedding_open
- \+ *lemma* open_embedding_iff_continuous_injective_open
- \+ *lemma* open_embedding.is_open_map_iff
- \+ *lemma* open_embedding.of_comp_iff
- \+ *lemma* open_embedding.of_comp
- \- *lemma* open_embedding_of_open_embedding_compose
- \- *lemma* open_embedding_iff_open_embedding_compose



## [2022-07-12 21:43:24](https://github.com/leanprover-community/mathlib/commit/7bd4755)
feat(analysis/special_functions/pow): drop an assumption in `is_o_log_rpow_rpow_at_top` ([#15164](https://github.com/leanprover-community/mathlib/pull/15164))
Drop an unneeded assumption in `is_o_log_rpow_rpow_at_top`, add a few variants.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* is_o_log_rpow_rpow_at_top
- \+ *lemma* is_o_abs_log_rpow_rpow_nhds_zero
- \+ *lemma* is_o_log_rpow_nhds_zero
- \+ *lemma* tendsto_log_div_rpow_nhds_zero
- \+ *lemma* tensdto_log_mul_rpow_nhds_zero



## [2022-07-12 21:43:23](https://github.com/leanprover-community/mathlib/commit/3543262)
feat(ring_theory/bezout): Define Bézout rings. ([#15091](https://github.com/leanprover-community/mathlib/pull/15091))
#### Estimated changes
Created src/ring_theory/bezout.lean
- \+ *lemma* iff_span_pair_is_principal
- \+ *lemma* span_gcd
- \+ *lemma* gcd_dvd_left
- \+ *lemma* gcd_dvd_right
- \+ *lemma* dvd_gcd
- \+ *lemma* gcd_eq_sum
- \+ *lemma* _root_.function.surjective.is_bezout
- \+ *lemma* tfae
- \+ *def* gcd
- \+ *def* to_gcd_domain

Modified src/ring_theory/noetherian.lean
- \+ *lemma* fg_induction
- \+ *lemma* is_noetherian_iff_fg_well_founded



## [2022-07-12 21:43:22](https://github.com/leanprover-community/mathlib/commit/ece3044)
feat(algebra/ring/{pi, prod, opposite}): add basic defs for non_unital_ring_hom ([#13958](https://github.com/leanprover-community/mathlib/pull/13958))
The defs added mimic the corresponding ones for `ring_hom`, wherever possible.
- [x] depends on: [#13956](https://github.com/leanprover-community/mathlib/pull/13956)
#### Estimated changes
Modified src/algebra/ring/opposite.lean
- \+ *def* non_unital_ring_hom.to_opposite
- \+ *def* non_unital_ring_hom.from_opposite
- \+ *def* non_unital_ring_hom.op
- \+ *def* non_unital_ring_hom.unop

Modified src/algebra/ring/pi.lean
- \+ *lemma* non_unital_ring_hom_injective
- \+ *def* pi.eval_non_unital_ring_hom
- \+ *def* pi.const_non_unital_ring_hom

Modified src/algebra/ring/prod.lean
- \+ *lemma* coe_fst
- \+ *lemma* coe_snd
- \+ *lemma* prod_apply
- \+ *lemma* fst_comp_prod
- \+ *lemma* snd_comp_prod
- \+ *lemma* prod_unique
- \+ *lemma* prod_map_def
- \+ *lemma* coe_prod_map
- \+ *lemma* prod_comp_prod_map
- \+ *def* fst
- \+ *def* snd
- \+ *def* prod_map



## [2022-07-12 19:18:58](https://github.com/leanprover-community/mathlib/commit/55db072)
chore(data/set/finite): golf some proofs ([#15273](https://github.com/leanprover-community/mathlib/pull/15273))
#### Estimated changes
Modified src/data/set/finite.lean


Modified src/data/set/lattice.lean
- \+ *theorem* Union_eq_range_psigma



## [2022-07-12 19:18:57](https://github.com/leanprover-community/mathlib/commit/7251bbf)
feat(analysis/special_functions/trigonometric/angle): equality of twice angles ([#14988](https://github.com/leanprover-community/mathlib/pull/14988))
Add lemmas about equality of twice `real.angle` values (i.e. equality
as angles modulo π).
#### Estimated changes
Created src/algebra/char_zero/quotient.lean
- \+ *lemma* zsmul_mem_zmultiples_iff_exists_sub_div
- \+ *lemma* nsmul_mem_zmultiples_iff_exists_sub_div
- \+ *lemma* zmultiples_zsmul_eq_zsmul_iff
- \+ *lemma* zmultiples_nsmul_eq_nsmul_iff

Modified src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* zsmul_eq_iff
- \+ *lemma* nsmul_eq_iff
- \+ *lemma* two_zsmul_eq_iff
- \+ *lemma* two_nsmul_eq_iff
- \+ *lemma* two_nsmul_eq_zero_iff
- \+ *lemma* two_zsmul_eq_zero_iff



## [2022-07-12 16:39:10](https://github.com/leanprover-community/mathlib/commit/89a80e6)
feat(data/nat/parity): `nat.bit1_div_bit0` ([#15268](https://github.com/leanprover-community/mathlib/pull/15268))
This PR adds `nat.bit1_div_bit0` and related lemmas. This came up when working with the power series of sin.
#### Estimated changes
Modified src/data/nat/parity.lean
- \+ *lemma* bit0_div_two
- \+ *lemma* bit1_div_two
- \+ *lemma* bit0_div_bit0
- \+ *lemma* bit1_div_bit0



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
- \+/\- *lemma* mem_diagonal
- \+ *lemma* mem_diagonal_iff
- \+/\- *lemma* prod_subset_compl_diagonal_iff_disjoint

Modified src/data/sum/basic.lean
- \+/\- *lemma* map_inl
- \+/\- *lemma* map_inr
- \+/\- *lemma* map_map
- \+/\- *lemma* map_comp_map
- \+/\- *lemma* map_id_id
- \+ *lemma* swap_inl
- \+ *lemma* swap_inr
- \+/\- *def* swap

Modified src/data/sum/order.lean


Modified src/logic/equiv/basic.lean
- \+ *theorem* sum_prod_distrib_symm_apply_left
- \+ *theorem* sum_prod_distrib_symm_apply_right
- \+ *theorem* prod_sum_distrib_symm_apply_left
- \+ *theorem* prod_sum_distrib_symm_apply_right

Modified src/order/filter/bases.lean
- \+ *lemma* compl_diagonal_mem_prod

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
- \+ *def* strong_sub_recursion
- \+ *def* pincer_recursion



## [2022-07-12 14:37:15](https://github.com/leanprover-community/mathlib/commit/13f04ec)
feat(set_theory/game/pgame): strengthen `lf_or_equiv_of_le` to `lt_or_equiv_of_le` ([#15255](https://github.com/leanprover-community/mathlib/pull/15255))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *theorem* lt_or_equiv_of_le
- \- *theorem* lf_or_equiv_of_le



## [2022-07-12 14:37:14](https://github.com/leanprover-community/mathlib/commit/0d659de)
feat(algebra/module/torsion): `R/I`-module structure on `M/IM`. ([#15092](https://github.com/leanprover-community/mathlib/pull/15092))
#### Estimated changes
Modified src/algebra/module/torsion.lean




## [2022-07-12 14:37:13](https://github.com/leanprover-community/mathlib/commit/fef5124)
feat(order/order_iso_nat): generalize `well_founded.monotone_chain_condition` to preorders ([#15073](https://github.com/leanprover-community/mathlib/pull/15073))
We also clean up the spacing throughout the file.
#### Estimated changes
Modified src/order/order_iso_nat.lean
- \+/\- *lemma* nat_lt_apply
- \+/\- *lemma* subtype.order_iso_of_nat_apply
- \+ *lemma* well_founded.monotone_chain_condition'
- \+/\- *lemma* well_founded.monotone_chain_condition
- \+/\- *lemma* well_founded.supr_eq_monotonic_sequence_limit
- \+/\- *theorem* exists_subseq_of_forall_mem_union
- \+/\- *theorem* exists_increasing_or_nonincreasing_subseq'
- \+/\- *theorem* exists_increasing_or_nonincreasing_subseq
- \+/\- *def* nat_gt

Modified src/order/well_founded_set.lean


Modified src/ring_theory/artinian.lean




## [2022-07-12 13:45:52](https://github.com/leanprover-community/mathlib/commit/119e166)
feat(representation_theory/character): formula for the dimension of the invariants in terms of the character ([#15084](https://github.com/leanprover-community/mathlib/pull/15084))
#### Estimated changes
Modified src/representation_theory/character.lean
- \+ *theorem* average_char_eq_finrank_invariants

Modified src/representation_theory/invariants.lean
- \- *lemma* average_def



## [2022-07-12 12:46:38](https://github.com/leanprover-community/mathlib/commit/aadba9b)
feat(order/well_founded_set): any relation is well-founded on `Ø` ([#15266](https://github.com/leanprover-community/mathlib/pull/15266))
#### Estimated changes
Modified src/order/well_founded_set.lean
- \+ *lemma* well_founded_on_empty
- \+ *lemma* is_wf_empty
- \+ *theorem* partially_well_ordered_on_empty
- \+/\- *theorem* is_pwo_empty



## [2022-07-12 12:46:37](https://github.com/leanprover-community/mathlib/commit/6c5e9fe)
feat(set_theory/game/pgame): `is_option (-x) (-y) ↔ is_option x y` ([#15256](https://github.com/leanprover-community/mathlib/pull/15256))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *theorem* is_option_neg
- \+ *theorem* is_option_neg_neg



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
- \+/\- *def* CNF



## [2022-07-12 12:05:18](https://github.com/leanprover-community/mathlib/commit/8284c00)
feat(algebra/order/monoid_lemmas_zero_lt): add missing lemmas ([#14770](https://github.com/leanprover-community/mathlib/pull/14770))
#### Estimated changes
Modified src/algebra/order/monoid_lemmas_zero_lt.lean
- \+ *lemma* mul_lt_of_lt_one_right
- \+ *lemma* lt_mul_of_one_lt_right
- \+ *lemma* mul_lt_of_lt_one_left
- \+ *lemma* lt_mul_of_one_lt_left



## [2022-07-12 09:40:23](https://github.com/leanprover-community/mathlib/commit/30daa3c)
chore(logic/is_empty): add lemmas for subtype, sigma, and psigma ([#15134](https://github.com/leanprover-community/mathlib/pull/15134))
This reorders the nonempty lemmas to put `sigma` next to `psigma`. The resulting `is_empty` and `nonempty` lemmas are now in the same order.
#### Estimated changes
Modified src/logic/is_empty.lean
- \+ *lemma* is_empty_Prop
- \+ *lemma* is_empty_sigma
- \+ *lemma* is_empty_psigma
- \+ *lemma* is_empty_subtype
- \+ *lemma* is_empty_ulift
- \+ *lemma* is_empty_plift

Modified src/logic/nonempty.lean
- \+/\- *lemma* nonempty_psigma



## [2022-07-12 08:44:51](https://github.com/leanprover-community/mathlib/commit/a8fdd99)
feat(probability/moments): Chernoff bound on the upper/lower tail of a real random variable ([#15129](https://github.com/leanprover-community/mathlib/pull/15129))
For `t` nonnegative such that the cgf exists, `ℙ(ε ≤ X) ≤ exp(-t*ε + cgf X ℙ t)`. We prove a similar result for the lower tail, as well as two corresponding versions using mgf instead of cgf.
#### Estimated changes
Modified src/analysis/special_functions/log/basic.lean
- \+ *lemma* le_exp_log

Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* mul_meas_ge_le_integral_of_nonneg

Modified src/probability/moments.lean
- \+/\- *lemma* cgf_zero_fun
- \+/\- *lemma* mgf_const'
- \+/\- *lemma* mgf_const
- \+/\- *lemma* cgf_zero'
- \+/\- *lemma* mgf_undef
- \+/\- *lemma* cgf_undef
- \+/\- *lemma* mgf_pos'
- \+/\- *lemma* mgf_pos
- \+ *lemma* mgf_neg
- \+ *lemma* cgf_neg
- \+ *lemma* measure_ge_le_exp_mul_mgf
- \+ *lemma* measure_le_le_exp_mul_mgf
- \+ *lemma* measure_ge_le_exp_cgf
- \+ *lemma* measure_le_le_exp_cgf
- \+/\- *def* mgf
- \+/\- *def* cgf



## [2022-07-12 07:50:38](https://github.com/leanprover-community/mathlib/commit/0039a19)
feat(probability/independence): two tuples indexed by disjoint subsets of an independent family of r.v. are independent ([#15131](https://github.com/leanprover-community/mathlib/pull/15131))
If `f` is a family of independent random variables and `S,T` are two disjoint finsets, then we have `indep_fun (λ a (i : S), f i a) (λ a (i : T), f i a) μ`.
Also golf `indep_fun_iff_measure_inter_preimage_eq_mul` and add its `Indep` version: `Indep_fun_iff_measure_inter_preimage_eq_mul`.
#### Estimated changes
Modified src/measure_theory/pi_system.lean
- \+ *lemma* is_pi_system.comap

Modified src/probability/independence.lean
- \+ *lemma* Indep_fun.indep_fun
- \+ *lemma* Indep_fun_iff_measure_inter_preimage_eq_mul
- \+ *lemma* Indep_fun.indep_fun_finset



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


Created scripts/polyrith_sage.py
- \+ *def* type_str(type):
- \+ *def* create_query(type:
- \+ *def* evaluate_in_sage(query:
- \+ *def* main():

Created scripts/polyrith_sage_helper.py
- \+ *def* mk_app(*args:
- \+ *def* const_to_string(coeff:
- \+ *def* power_to_string(var:
- \+ *def* sum_to_string(terms:
- \+ *def* monomial_to_string(etuple:
- \+ *def* polynomial_to_string(p)

Modified src/data/buffer/parser/numeral.lean


Modified src/tactic/default.lean


Created src/tactic/polyrith.lean


Created test/polyrith.lean




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
- \+ *lemma* partial_prod_zero
- \+ *lemma* partial_prod_succ
- \+ *lemma* partial_prod_succ'
- \+/\- *lemma* prod_take_of_fn
- \+/\- *lemma* prod_of_fn
- \+ *def* partial_prod

Modified src/representation_theory/basic.lean
- \+ *lemma* of_mul_action_def
- \+ *lemma* of_mul_action_apply

Created src/representation_theory/group_cohomology_resolution.lean
- \+ *lemma* to_tensor_aux_single
- \+ *lemma* to_tensor_aux_of_mul_action
- \+ *lemma* of_tensor_aux_single
- \+ *lemma* of_tensor_aux_comm_of_mul_action
- \+ *lemma* to_tensor_single
- \+ *lemma* of_tensor_single
- \+ *lemma* of_tensor_single'
- \+ *def* to_tensor_aux
- \+ *def* of_tensor_aux
- \+ *def* to_tensor
- \+ *def* of_tensor



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
- \+/\- *lemma* coe_inj
- \+/\- *lemma* dom_coe
- \+/\- *lemma* le_def
- \+/\- *lemma* top_add
- \+/\- *lemma* add_top
- \+/\- *lemma* coe_get
- \+/\- *lemma* get_coe'
- \+/\- *lemma* get_coe
- \+/\- *lemma* coe_add_get
- \+/\- *lemma* get_add
- \+/\- *lemma* get_zero
- \+/\- *lemma* get_one
- \+/\- *lemma* get_eq_iff_eq_some
- \+/\- *lemma* get_eq_iff_eq_coe
- \+/\- *lemma* dom_of_le_of_dom
- \+/\- *lemma* dom_of_le_some
- \+/\- *lemma* dom_of_le_coe
- \+/\- *lemma* lt_def
- \+/\- *lemma* coe_le_coe
- \+/\- *lemma* coe_lt_coe
- \+/\- *lemma* get_le_get
- \+/\- *lemma* le_coe_iff
- \+/\- *lemma* lt_coe_iff
- \+/\- *lemma* coe_le_iff
- \+/\- *lemma* coe_lt_iff
- \+/\- *lemma* eq_zero_iff
- \+/\- *lemma* ne_zero_iff
- \+/\- *lemma* dom_of_lt
- \+/\- *lemma* top_eq_none
- \+/\- *lemma* coe_lt_top
- \+/\- *lemma* coe_ne_top
- \+/\- *lemma* not_is_max_coe
- \+/\- *lemma* ne_top_iff
- \+/\- *lemma* ne_top_iff_dom
- \+/\- *lemma* not_dom_iff_eq_top
- \+/\- *lemma* ne_top_of_lt
- \+/\- *lemma* eq_top_iff_forall_lt
- \+/\- *lemma* eq_top_iff_forall_le
- \+/\- *lemma* pos_iff_one_le
- \+/\- *lemma* lt_add_one
- \+/\- *lemma* le_of_lt_add_one
- \+/\- *lemma* add_one_le_of_lt
- \+/\- *lemma* add_one_le_iff_lt
- \+/\- *lemma* lt_add_one_iff_lt
- \+/\- *lemma* add_eq_top_iff
- \+/\- *lemma* to_with_top_top'
- \+/\- *lemma* to_with_top_zero'
- \+/\- *lemma* to_with_top_coe
- \+/\- *lemma* to_with_top_coe'
- \+/\- *lemma* to_with_top_le
- \+/\- *lemma* to_with_top_lt
- \+/\- *lemma* to_with_top_add
- \+/\- *lemma* with_top_equiv_le
- \+/\- *lemma* with_top_equiv_lt
- \+/\- *lemma* lt_wf
- \+/\- *lemma* lt_find
- \+/\- *lemma* lt_find_iff
- \+ *def* part_enat
- \+/\- *def* some
- \+/\- *def* coe_hom
- \+/\- *def* to_with_top
- \+/\- *def* find
- \- *def* enat

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
- \+/\- *lemma* pow_dvd_of_le_multiplicity
- \+/\- *lemma* dvd_of_multiplicity_pos
- \+/\- *lemma* dvd_iff_multiplicity_pos
- \+/\- *def* multiplicity

Modified src/ring_theory/power_series/basic.lean
- \+/\- *lemma* le_order
- \+/\- *lemma* order_eq
- \+/\- *def* order

Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/set_theory/cardinal/basic.lean
- \+ *lemma* to_part_enat_apply_of_lt_aleph_0
- \+ *lemma* to_part_enat_apply_of_aleph_0_le
- \+ *lemma* to_part_enat_cast
- \+ *lemma* mk_to_part_enat_of_infinite
- \+ *lemma* to_part_enat_surjective
- \+ *lemma* mk_to_part_enat_eq_coe_card
- \- *lemma* to_enat_apply_of_lt_aleph_0
- \- *lemma* to_enat_apply_of_aleph_0_le
- \- *lemma* to_enat_cast
- \- *lemma* mk_to_enat_of_infinite
- \- *lemma* to_enat_surjective
- \- *lemma* mk_to_enat_eq_coe_card
- \+ *theorem* aleph_0_to_part_enat
- \- *theorem* aleph_0_to_enat
- \+ *def* to_part_enat
- \- *def* to_enat

Modified src/set_theory/cardinal/continuum.lean
- \+ *theorem* continuum_to_part_enat
- \- *theorem* continuum_to_enat

Modified src/set_theory/cardinal/finite.lean
- \+/\- *lemma* card_eq_coe_fintype_card
- \+/\- *lemma* card_eq_top_of_infinite
- \+/\- *def* card

Modified src/set_theory/cardinal/ordinal.lean
- \+ *theorem* aleph_to_part_enat
- \- *theorem* aleph_to_enat



## [2022-07-11 16:51:23](https://github.com/leanprover-community/mathlib/commit/44905df)
feat(order/hom/basic): `order_iso` to `rel_iso (<) (<)` ([#15182](https://github.com/leanprover-community/mathlib/pull/15182))
Couldn't find this in the library. Asked on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/rel_iso.20.28.3C.29.20.28.3C.29.20from.20order_iso/near/288891638) in case anyone knew of this already.
#### Estimated changes
Modified src/order/hom/basic.lean
- \+ *def* to_rel_iso_lt



## [2022-07-11 16:51:22](https://github.com/leanprover-community/mathlib/commit/0f56b2d)
feat(combinatorics/simple_graph/connectivity): simp confluence ([#15153](https://github.com/leanprover-community/mathlib/pull/15153))
From branch `walks_and_trees`. Adds data/list/basic lemma to help simp prove `d ∈ p.reverse.darts ↔ d.symm ∈ p.darts`.
#### Estimated changes
Modified src/combinatorics/simple_graph/connectivity.lean
- \+ *lemma* mem_darts_reverse
- \+/\- *lemma* dart_snd_mem_support_of_mem_darts
- \+ *lemma* fst_mem_support_of_mem_edges
- \+ *lemma* snd_mem_support_of_mem_edges
- \+ *lemma* is_cycle.not_of_nil
- \- *lemma* mem_support_of_mem_edges

Modified src/data/list/basic.lean
- \+ *lemma* _root_.function.involutive.exists_mem_and_apply_eq_iff
- \+ *theorem* mem_map_of_involutive



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
- \+ *def* order_embedding_coe

Modified src/algebra/order/nonneg.lean


Modified src/algebra/order/ring.lean


Modified src/algebra/order/with_zero.lean


Modified src/data/fin/basic.lean


Modified src/data/ulift.lean


Modified src/field_theory/subfield.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/group_theory/submonoid/operations.lean


Modified src/order/basic.lean
- \+ *lemma* min_rec
- \+ *lemma* max_rec
- \+ *lemma* min_rec'
- \+ *lemma* max_rec'
- \+/\- *def* linear_order.lift
- \+ *def* linear_order.lift'

Modified src/order/category/NonemptyFinLinOrd.lean


Modified src/order/lattice.lean


Modified src/order/min_max.lean
- \- *lemma* min_rec
- \- *lemma* max_rec
- \- *lemma* min_rec'
- \- *lemma* max_rec'

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
- \+ *def* preserves_limits_of_shape_pempty_of_preserves_terminal
- \+ *def* preserves_colimits_of_shape_pempty_of_preserves_initial

Modified src/category_theory/limits/preserves/shapes/zero.lean
- \+ *def* preserves_terminal_object_of_preserves_zero_morphisms
- \+ *def* preserves_initial_object_of_preserves_zero_morphisms

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* binary_fan.mk_fst
- \+ *lemma* binary_fan.mk_snd
- \+ *lemma* binary_cofan.mk_inl
- \+ *lemma* binary_cofan.mk_inr
- \- *lemma* binary_fan.mk_π_app_left
- \- *lemma* binary_fan.mk_π_app_right
- \- *lemma* binary_cofan.mk_ι_app_left
- \- *lemma* binary_cofan.mk_ι_app_right
- \+ *def* iso_binary_fan_mk
- \+ *def* iso_binary_cofan_mk

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *lemma* binary_bicone.fst_kernel_fork_ι
- \+ *lemma* binary_bicone.snd_kernel_fork_ι
- \+ *lemma* binary_bicone.inl_cokernel_cofork_π
- \+ *lemma* binary_bicone.inr_cokernel_cofork_π
- \+ *lemma* biprod.inl_cokernel_cofork_π
- \+ *lemma* biprod.inr_cokernel_cofork_π
- \- *lemma* biprod.inl_cokernel_fork_π
- \- *lemma* biprod.inr_cokernel_fork_π
- \+ *def* binary_bicone.fst_kernel_fork
- \+ *def* binary_bicone.snd_kernel_fork
- \+ *def* binary_bicone.inl_cokernel_cofork
- \+ *def* binary_bicone.inr_cokernel_cofork
- \+ *def* binary_bicone.is_limit_fst_kernel_fork
- \+ *def* binary_bicone.is_limit_snd_kernel_fork
- \+ *def* binary_bicone.is_colimit_inl_cokernel_cofork
- \+ *def* binary_bicone.is_colimit_inr_cokernel_cofork
- \+ *def* biprod.inl_cokernel_cofork
- \+/\- *def* biprod.is_cokernel_inl_cokernel_fork
- \+ *def* biprod.inr_cokernel_cofork
- \+/\- *def* biprod.is_cokernel_inr_cokernel_fork
- \- *def* biprod.inl_cokernel_fork
- \- *def* biprod.inr_cokernel_fork

Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* fork.ι_postcompose
- \+ *lemma* cofork.π_precompose
- \+ *def* parallel_pair.eq_of_hom_eq
- \+ *def* fork.iso_fork_of_ι
- \+ *def* cofork.iso_cofork_of_π

Modified src/category_theory/limits/shapes/images.lean


Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* kernel_fork.is_limit.of_ι
- \+ *def* cokernel_cofork.is_colimit.of_π
- \- *def* is_limit.of_ι
- \- *def* is_colimit.of_π

Modified src/category_theory/limits/shapes/normal_mono/basic.lean


Modified src/category_theory/preadditive/additive_functor.lean


Modified src/category_theory/preadditive/default.lean
- \+ *lemma* fork_of_kernel_fork_ι
- \+ *lemma* cofork_of_cokernel_cofork_π

Created src/category_theory/preadditive/left_exact.lean
- \+ *def* is_limit_map_cone_binary_fan_of_preserves_kernels
- \+ *def* preserves_binary_product_of_preserves_kernels
- \+ *def* preserves_binary_products_of_preserves_kernels
- \+ *def* preserves_equalizer_of_preserves_kernels
- \+ *def* preserves_equalizers_of_preserves_kernels
- \+ *def* preserves_finite_limits_of_preserves_kernels
- \+ *def* is_colimit_map_cocone_binary_cofan_of_preserves_cokernels
- \+ *def* preserves_coproduct_of_preserves_cokernels
- \+ *def* preserves_binary_coproducts_of_preserves_cokernels
- \+ *def* preserves_coequalizer_of_preserves_cokernels
- \+ *def* preserves_coequalizers_of_preserves_cokernels
- \+ *def* preserves_finite_colimits_of_preserves_cokernels



## [2022-07-11 16:51:18](https://github.com/leanprover-community/mathlib/commit/d3f5adb)
feat(combinatorics/simple_graph/regularity/equitabilise): Equitabilising a partition ([#13222](https://github.com/leanprover-community/mathlib/pull/13222))
Define the equitabilisation of a partition and a way to find an arbitrary equipartition of any size.
#### Estimated changes
Created src/combinatorics/simple_graph/regularity/equitabilise.lean
- \+ *lemma* equitabilise_aux
- \+ *lemma* card_eq_of_mem_parts_equitabilise
- \+ *lemma* equitabilise_is_equipartition
- \+ *lemma* card_filter_equitabilise_big
- \+ *lemma* card_filter_equitabilise_small
- \+ *lemma* card_parts_equitabilise
- \+ *lemma* card_parts_equitabilise_subset_le
- \+ *lemma* exists_equipartition_card_eq

Modified src/order/partition/finpartition.lean
- \+ *lemma* mem_avoid



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
- \+ *lemma* covby_sup_of_inf_covby_of_inf_covby_left
- \+ *lemma* covby_sup_of_inf_covby_of_inf_covby_right
- \+ *lemma* inf_covby_of_covby_sup_of_covby_sup_left
- \+ *lemma* inf_covby_of_covby_sup_of_covby_sup_right
- \+ *lemma* covby_sup_of_inf_covby_left
- \+ *lemma* covby_sup_of_inf_covby_right
- \+ *lemma* inf_covby_of_covby_sup_left
- \+ *lemma* inf_covby_of_covby_sup_right



## [2022-07-11 14:26:39](https://github.com/leanprover-community/mathlib/commit/dfcbe85)
refactor(data/finite): move definition to a new file ([#15204](https://github.com/leanprover-community/mathlib/pull/15204))
The new file imports nothing but `logic.equiv.basic`.
#### Estimated changes
Modified src/data/finite/basic.lean
- \- *lemma* finite_iff_exists_equiv_fin
- \- *lemma* finite.exists_equiv_fin
- \- *lemma* finite.of_equiv
- \- *lemma* equiv.finite_iff
- \- *lemma* finite.of_fintype
- \- *lemma* of_bijective

Created src/data/finite/defs.lean
- \+ *lemma* finite_iff_exists_equiv_fin
- \+ *lemma* finite.exists_equiv_fin
- \+ *lemma* finite.of_equiv
- \+ *lemma* equiv.finite_iff
- \+ *lemma* function.bijective.finite_iff
- \+ *lemma* of_bijective



## [2022-07-11 14:26:38](https://github.com/leanprover-community/mathlib/commit/aae01cd)
data/multiset/range): add multiset.coe_range ([#15201](https://github.com/leanprover-community/mathlib/pull/15201))
#### Estimated changes
Modified src/data/multiset/range.lean
- \+ *theorem* coe_range



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
- \+/\- *lemma* finite_to_set
- \+/\- *lemma* finite_to_set_to_finset
- \+ *lemma* list.finite_to_set
- \- *lemma* range_find_greatest_subset

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
- \+/\- *theorem* prod_univ_two

Modified src/linear_algebra/basis.lean
- \+ *lemma* fin_two_prod_zero
- \+ *lemma* fin_two_prod_one
- \+ *lemma* coe_fin_two_prod_repr

Modified src/linear_algebra/determinant.lean
- \+ *lemma* det_to_lin

Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* det_fin_one_mk
- \+ *lemma* det_fin_two_mk

Modified src/linear_algebra/matrix/to_lin.lean
- \+ *lemma* matrix.to_lin_fin_two_prod_apply
- \+ *lemma* matrix.to_lin_fin_two_prod

Modified src/topology/algebra/module/finite_dimension.lean
- \+ *lemma* det_to_continuous_linear_map
- \+ *lemma* _root_.matrix.to_lin_fin_two_prod_to_continuous_linear_map



## [2022-07-11 14:26:33](https://github.com/leanprover-community/mathlib/commit/611dcca)
feat(analysis/inner_product_space): the Hellinger-Toeplitz theorem ([#15055](https://github.com/leanprover-community/mathlib/pull/15055))
Prove the Hellinger-Toeplitz theorem as a corollary of the closed graph theorem.
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* is_self_adjoint.continuous
- \+ *lemma* is_self_adjoint.clm_apply
- \+ *def* is_self_adjoint.clm



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
- \+ *lemma* is_generic_point_iff_specializes
- \+ *lemma* specializes_iff_mem
- \+ *lemma* specializes
- \+ *lemma* mem
- \+ *lemma* mem_open_set_iff
- \+ *lemma* disjoint_iff
- \+ *lemma* mem_closed_set_iff
- \+/\- *lemma* is_generic_point_iff_forall_closed
- \- *lemma* is_generic_point.specializes
- \- *lemma* is_generic_point.mem
- \- *lemma* is_generic_point.is_closed
- \- *lemma* is_generic_point.is_irreducible
- \- *lemma* is_generic_point.eq
- \- *lemma* is_generic_point.mem_open_set_iff
- \- *lemma* is_generic_point.disjoint_iff
- \- *lemma* is_generic_point.mem_closed_set_iff
- \- *lemma* is_generic_point.image



## [2022-07-11 14:26:30](https://github.com/leanprover-community/mathlib/commit/902e351)
feat(data/set/pointwise): `list` and `multiset` versions of n-ary lemmas ([#14928](https://github.com/leanprover-community/mathlib/pull/14928))
These lemmas are generalizations of the existing lemmas about `finset.prod` and `finset.sum`, but for the `list` and `multiset` versions.
The finset ones can now be proved in terms of the multiset ones.
#### Estimated changes
Modified src/data/set/pointwise.lean
- \+ *lemma* list_prod_mem_list_prod
- \+ *lemma* list_prod_subset_list_prod
- \+ *lemma* list_prod_singleton
- \+ *lemma* multiset_prod_mem_multiset_prod
- \+ *lemma* multiset_prod_subset_multiset_prod
- \+ *lemma* multiset_prod_singleton



## [2022-07-11 14:26:29](https://github.com/leanprover-community/mathlib/commit/b762695)
feat(algebraic_geometry/projective_spectrum): forward direction of homeomorphism between top_space of Proj and top_space of Spec ([#13397](https://github.com/leanprover-community/mathlib/pull/13397))
This pr is the start of showing that Proj is a scheme. In this pr, it will be shown that the locally on basic open set, there is a continuous function from the underlying topological space of Proj restricted to this open set to Spec of degree zero part of some localised ring. In the near future, it will be shown that this function is a homeomorphism.
#### Estimated changes
Modified src/algebraic_geometry/projective_spectrum/scheme.lean
- \+/\- *lemma* degree_zero_part.num_mem
- \+/\- *lemma* degree_zero_part.eq
- \+ *lemma* degree_zero_part.coe_mul
- \+ *lemma* mem_carrier_iff
- \+ *lemma* mem_carrier.clear_denominator
- \+ *lemma* disjoint
- \+ *lemma* carrier_ne_top
- \+ *lemma* preimage_eq
- \- *lemma* degree_zero_part.mul_val
- \+/\- *def* degree_zero_part.deg
- \+/\- *def* degree_zero_part.num
- \+ *def* carrier
- \+ *def* to_fun
- \+ *def* to_Spec

Modified src/algebraic_geometry/projective_spectrum/structure_sheaf.lean




## [2022-07-11 09:33:58](https://github.com/leanprover-community/mathlib/commit/cea2769)
chore(category_theory/adjunction/*): making arguments implicit in adjuction.comp and two small lemmas about mates ([#15062](https://github.com/leanprover-community/mathlib/pull/15062))
Working on adjunctions between monads and comonads, I noticed that adjunction.comp was defined with having the functors of one of the adjunctions explicit as well as the adjunction. However in the library, only `adjunction.comp _ _` ever appears. Thus I found it natural to make these two arguments implicit, so that composition of adjunctions can now be written as `adj1.comp adj2` instead of `adj1.comp _ _ adj2`. 
Furthermore, I provide two lemmas about mates of natural transformations to and from the identity functor. The application I have in mind is to the unit/counit of a monad/comonad in case of an adjunction of monads and comonads, as studied already by Eilenberg and Moore.
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/mates.lean
- \+ *lemma* transfer_nat_trans_self_adjunction_id
- \+ *lemma* transfer_nat_trans_self_adjunction_id_symm

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
- \+/\- *lemma* pos_of_mul_pos_right
- \+/\- *lemma* pos_of_mul_pos_left
- \+/\- *lemma* neg_of_mul_pos_right
- \+/\- *lemma* neg_of_mul_pos_left

Modified src/algebra/order/ring.lean
- \+/\- *lemma* pos_of_mul_pos_left
- \+/\- *lemma* pos_of_mul_pos_right
- \+/\- *lemma* pos_iff_pos_of_mul_pos
- \+/\- *lemma* neg_of_mul_pos_left
- \+/\- *lemma* neg_of_mul_pos_right
- \+/\- *lemma* nonneg_of_mul_nonneg_left
- \+/\- *lemma* nonneg_of_mul_nonneg_right
- \+/\- *lemma* neg_of_mul_neg_left
- \+/\- *lemma* neg_of_mul_neg_right
- \+/\- *lemma* nonpos_of_mul_nonpos_left
- \+/\- *lemma* nonpos_of_mul_nonpos_right

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
- \+ *lemma* id_eq_id
- \+ *lemma* id_f
- \+ *lemma* comp_eq_comp
- \+ *lemma* comp_f
- \+ *lemma* iso_of_iso
- \+ *lemma* algebra.hom_equiv_naturality_str
- \+ *lemma* coalgebra.hom_equiv_naturality_str_symm
- \+ *def* id
- \+ *def* comp
- \+ *def* iso_mk
- \+ *def* forget
- \+ *def* functor_of_nat_trans
- \+ *def* functor_of_nat_trans_id
- \+ *def* functor_of_nat_trans_comp
- \+ *def* functor_of_nat_trans_eq
- \+ *def* equiv_of_nat_iso
- \+ *def* algebra.to_coalgebra_of
- \+ *def* coalgebra.to_algebra_of
- \+ *def* alg_coalg_equiv.unit_iso
- \+ *def* alg_coalg_equiv.counit_iso
- \+ *def* algebra_coalgebra_equiv



## [2022-07-11 09:33:55](https://github.com/leanprover-community/mathlib/commit/f7baecb)
feat(category_theory/functor): preserving/reflecting monos/epis ([#14829](https://github.com/leanprover-community/mathlib/pull/14829))
#### Estimated changes
Modified src/algebra/category/Group/abelian.lean


Modified src/algebra/category/Group/adjunctions.lean


Modified src/algebraic_geometry/open_immersion.lean


Modified src/category_theory/adjunction/evaluation.lean


Modified src/category_theory/concrete_category/basic.lean


Modified src/category_theory/epi_mono.lean
- \- *lemma* left_adjoint_preserves_epi
- \- *lemma* right_adjoint_preserves_mono
- \- *lemma* faithful_reflects_epi
- \- *lemma* faithful_reflects_mono

Created src/category_theory/functor/epi_mono.lean
- \+ *lemma* mono_of_mono_map
- \+ *lemma* epi_of_epi_map
- \+ *lemma* preserves_monomorphisms.of_iso
- \+ *lemma* preserves_monomorphisms.iso_iff
- \+ *lemma* preserves_epimorphisms.of_iso
- \+ *lemma* preserves_epimorphisms.iso_iff
- \+ *lemma* reflects_monomorphisms.of_iso
- \+ *lemma* reflects_monomorphisms.iso_iff
- \+ *lemma* reflects_epimorphisms.of_iso
- \+ *lemma* reflects_epimorphisms.iso_iff
- \+ *lemma* preserves_epimorphsisms_of_adjunction
- \+ *lemma* preserves_monomorphisms_of_adjunction

Modified src/category_theory/glue_data.lean


Modified src/category_theory/limits/constructions/epi_mono.lean
- \+ *lemma* preserves_mono_of_preserves_limit
- \+ *lemma* reflects_mono_of_reflects_limit
- \+ *lemma* preserves_epi_of_preserves_colimit
- \+ *lemma* reflects_epi_of_reflects_colimit
- \- *lemma* reflects_mono
- \- *lemma* reflects_epi

Modified src/category_theory/over.lean


Modified src/topology/category/CompHaus/default.lean


Modified src/topology/category/Profinite/default.lean


Modified src/topology/category/Top/adjunctions.lean


Modified src/topology/category/Top/epi_mono.lean




## [2022-07-11 09:33:54](https://github.com/leanprover-community/mathlib/commit/3536347)
feat(combinatorics/set_family/harris_kleitman): The Harris-Kleitman inequality ([#14497](https://github.com/leanprover-community/mathlib/pull/14497))
Lower/upper sets in `finset α` are (anti)correlated.
#### Estimated changes
Created src/combinatorics/set_family/harris_kleitman.lean
- \+ *lemma* mem_non_member_subfamily
- \+ *lemma* mem_member_subfamily
- \+ *lemma* non_member_subfamily_inter
- \+ *lemma* member_subfamily_inter
- \+ *lemma* card_member_subfamily_add_card_non_member_subfamily
- \+ *lemma* is_lower_set.non_member_subfamily
- \+ *lemma* is_lower_set.member_subfamily
- \+ *lemma* is_lower_set.member_subfamily_subset_non_member_subfamily
- \+ *lemma* is_lower_set.le_card_inter_finset'
- \+ *lemma* is_lower_set.le_card_inter_finset
- \+ *lemma* is_upper_set.card_inter_le_finset
- \+ *lemma* is_lower_set.card_inter_le_finset
- \+ *lemma* is_upper_set.le_card_inter_finset
- \+ *def* non_member_subfamily
- \+ *def* member_subfamily

Modified src/order/upper_lower.lean
- \+ *lemma* is_upper_set_compl
- \+ *lemma* is_lower_set_compl



## [2022-07-11 09:33:53](https://github.com/leanprover-community/mathlib/commit/f5170fc)
feat(order/bounded_order): Codisjointness ([#14195](https://github.com/leanprover-community/mathlib/pull/14195))
Define `codisjoint`, the dual notion of `disjoint`. This is already used without a name in `is_compl`, and will soon be used for Heyting algebras.
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/sesquilinear_form.lean


Modified src/order/bounded_order.lean
- \+ *lemma* codisjoint_iff
- \+ *lemma* codisjoint.eq_top
- \+ *lemma* codisjoint.comm
- \+ *lemma* codisjoint.symm
- \+ *lemma* symmetric_codisjoint
- \+ *lemma* codisjoint_assoc
- \+ *lemma* codisjoint_top_left
- \+ *lemma* codisjoint_top_right
- \+ *lemma* codisjoint.mono
- \+ *lemma* codisjoint.mono_left
- \+ *lemma* codisjoint.mono_right
- \+ *lemma* codisjoint.sup_left
- \+ *lemma* codisjoint.sup_left'
- \+ *lemma* codisjoint.sup_right
- \+ *lemma* codisjoint.sup_right'
- \+ *lemma* codisjoint_self
- \+ *lemma* codisjoint.ne
- \+ *lemma* codisjoint.eq_top_of_ge
- \+ *lemma* codisjoint.eq_top_of_le
- \+ *lemma* codisjoint.of_codisjoint_sup_of_le
- \+ *lemma* codisjoint.of_codisjoint_sup_of_le'
- \+ *lemma* codisjoint_bot
- \+ *lemma* bot_codisjoint
- \+ *lemma* codisjoint_inf_left
- \+ *lemma* codisjoint_inf_right
- \+ *lemma* codisjoint.inf_left
- \+ *lemma* codisjoint.inf_right
- \+ *lemma* codisjoint.left_le_of_le_inf_right
- \+ *lemma* codisjoint.left_le_of_le_inf_left
- \+ *lemma* disjoint.dual
- \+ *lemma* codisjoint.dual
- \+ *lemma* disjoint_to_dual_iff
- \+ *lemma* disjoint_of_dual_iff
- \+ *lemma* codisjoint_to_dual_iff
- \+ *lemma* codisjoint_of_dual_iff
- \+/\- *lemma* of_eq
- \+/\- *lemma* sup_eq_top
- \+ *def* codisjoint

Modified src/order/compactly_generated.lean


Modified src/order/filter/basic.lean


Modified src/order/hom/basic.lean
- \+/\- *lemma* order_embedding.map_inf_le
- \+/\- *lemma* order_embedding.le_map_sup
- \+/\- *lemma* order_iso.map_inf
- \+/\- *lemma* order_iso.map_sup
- \+ *lemma* codisjoint.map_order_iso
- \+ *lemma* codisjoint_map_order_iso_iff

Modified src/order/hom/lattice.lean
- \+ *lemma* codisjoint.map
- \+/\- *lemma* is_compl.map



## [2022-07-11 08:26:44](https://github.com/leanprover-community/mathlib/commit/b7148c4)
feat(analysis/special_functions/pow): Rational powers are dense ([#15002](https://github.com/leanprover-community/mathlib/pull/15002))
There is a rational square between any two positive elements of an archimedean ordered field.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* exists_rat_pow_btwn_rat_aux
- \+ *lemma* exists_rat_pow_btwn_rat
- \+ *lemma* exists_rat_pow_btwn

Modified src/data/real/sqrt.lean
- \+ *lemma* lt_sq_of_sqrt_lt



## [2022-07-11 02:42:30](https://github.com/leanprover-community/mathlib/commit/e3e4cc6)
feat(data/nat/basic): split `exists_lt_and_lt_iff_not_dvd` into `if` and `iff` lemmas ([#15099](https://github.com/leanprover-community/mathlib/pull/15099))
Pull out from `exists_lt_and_lt_iff_not_dvd` ("`n` is not divisible by `a` iff it is between `a * k` and `a * (k + 1)` for some `k`") a separate lemma proving the forward direction (which doesn't need the `0 < a` assumption) and use this to golf the `iff` lemma.
Also renames the lemma to the more descriptive `not_dvd_{of,iff}_between_consec_multiples`.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* not_dvd_of_between_consec_multiples
- \+ *lemma* not_dvd_iff_between_consec_multiples
- \- *lemma* exists_lt_and_lt_iff_not_dvd

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
- \+ *lemma* unop_fst
- \+ *lemma* unop_snd
- \+ *lemma* op_fst
- \+ *lemma* op_snd
- \+ *lemma* unop_inl
- \+ *lemma* unop_inr
- \+ *lemma* op_inl
- \+ *lemma* op_inr
- \+ *def* span_op
- \+ *def* op_cospan
- \+ *def* cospan_op
- \+ *def* op_span
- \+ *def* unop
- \+ *def* op
- \+ *def* op_unop
- \+ *def* unop_op
- \+ *def* is_colimit_equiv_is_limit_op
- \+ *def* is_colimit_equiv_is_limit_unop
- \+ *def* is_limit_equiv_is_colimit_op
- \+ *def* is_limit_equiv_is_colimit_unop

Modified src/category_theory/limits/shapes/pullbacks.lean




## [2022-07-10 17:43:04](https://github.com/leanprover-community/mathlib/commit/f4f0f67)
feat(set_theory/zfc): simp lemmas for `arity` and `const` ([#15214](https://github.com/leanprover-community/mathlib/pull/15214))
#### Estimated changes
Modified src/set_theory/zfc.lean
- \+ *theorem* arity_zero
- \+ *theorem* arity_succ
- \+ *theorem* const_zero
- \+ *theorem* const_succ
- \+ *theorem* const_succ_apply



## [2022-07-10 17:43:03](https://github.com/leanprover-community/mathlib/commit/cf4783f)
feat(set_theory/zfc): basic lemmas on `pSet.equiv` ([#15211](https://github.com/leanprover-community/mathlib/pull/15211))
We unfold the complex definition into something easier to use.
#### Estimated changes
Modified src/set_theory/zfc.lean
- \+ *theorem* exists_equiv_left
- \+ *theorem* exists_equiv_right



## [2022-07-10 17:43:01](https://github.com/leanprover-community/mathlib/commit/4b6ec60)
lint(topology/algebra/order/basic): use `finite` instead of `fintype` ([#15203](https://github.com/leanprover-community/mathlib/pull/15203))
#### Estimated changes
Modified src/topology/algebra/order/basic.lean




## [2022-07-10 15:28:36](https://github.com/leanprover-community/mathlib/commit/f51aaab)
feat(algebra/order/monoid) Add zero_le_three and zero_le_four ([#15219](https://github.com/leanprover-community/mathlib/pull/15219))
#### Estimated changes
Modified src/algebra/order/monoid.lean
- \+ *lemma* zero_le_three
- \+ *lemma* zero_le_four



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
- \+ *lemma* coe_le_max_of_mem
- \+ *lemma* max_mono
- \+ *lemma* max_le
- \+ *lemma* min_le_coe_of_mem
- \+ *lemma* min_mono
- \+ *lemma* le_min



## [2022-07-10 15:28:34](https://github.com/leanprover-community/mathlib/commit/5305d39)
feat(data/pnat/basic): `succ` as an order isomorphism between `ℕ` and `ℕ+` ([#15183](https://github.com/leanprover-community/mathlib/pull/15183))
Couldn't find this in the library. Asked on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/order.20isomorphism.20between.20.E2.84.95.20and.20.E2.84.95.2B/near/288891689) in case anyone knew of this already.
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *def* succ_order_iso



## [2022-07-10 14:02:39](https://github.com/leanprover-community/mathlib/commit/37c2777)
feat(order/filter/ultrafilter): `pure`, `map`, and `comap` lemmas ([#15187](https://github.com/leanprover-community/mathlib/pull/15187))
A handful of simple lemmas.
#### Estimated changes
Modified src/order/filter/ultrafilter.lean
- \+ *lemma* map_id
- \+ *lemma* map_id'
- \+ *lemma* map_map
- \+/\- *lemma* coe_comap
- \+ *lemma* comap_id
- \+ *lemma* comap_comap
- \+ *lemma* coe_pure
- \+ *lemma* map_pure
- \+ *lemma* comap_pure
- \+ *lemma* pure_injective
- \+ *lemma* eq_pure_of_finite_mem
- \+ *lemma* eq_pure_of_fintype
- \- *lemma* eq_principal_of_finite_mem



## [2022-07-09 19:44:03](https://github.com/leanprover-community/mathlib/commit/861589f)
feat(linear_algebra/unitary_group): better constructor ([#15209](https://github.com/leanprover-community/mathlib/pull/15209))
`A ∈ matrix.unitary_group n α` means by definition (for reasons of agreement with something more general) that `A * star A = 1` and `star A * A = 1`.  But either condition implies the other, so we provide a lemma to reduce to the first.
#### Estimated changes
Modified src/linear_algebra/unitary_group.lean
- \+ *lemma* mem_unitary_group_iff
- \+ *lemma* mem_orthogonal_group_iff



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
- \+/\- *theorem* nat_cast_succ
- \+/\- *theorem* add_le_add_iff_right
- \+/\- *theorem* nat_cast_mul
- \+/\- *theorem* nat_cast_opow
- \+/\- *theorem* nat_cast_le
- \+/\- *theorem* nat_cast_lt
- \+/\- *theorem* nat_cast_inj
- \+/\- *theorem* nat_cast_eq_zero
- \+/\- *theorem* nat_cast_pos
- \+/\- *theorem* nat_cast_sub
- \+/\- *theorem* nat_cast_div
- \+/\- *theorem* nat_cast_mod
- \+/\- *theorem* lift_nat_cast
- \- *theorem* lift_type_fin

Modified src/set_theory/ordinal/notation.lean




## [2022-07-09 14:09:58](https://github.com/leanprover-community/mathlib/commit/6d245b2)
feat(set_theory/ordinal/basic): order type of naturals is `ω` ([#15178](https://github.com/leanprover-community/mathlib/pull/15178))
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean
- \+ *theorem* type_nat_lt



## [2022-07-09 13:17:49](https://github.com/leanprover-community/mathlib/commit/7cf0ae6)
feat(combinatorics/simple_graph/subgraph): add `subgraph.comap` and subgraph of subgraph coercion ([#14877](https://github.com/leanprover-community/mathlib/pull/14877))
#### Estimated changes
Modified src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* comap_monotone
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* restrict_coe_subgraph
- \+ *lemma* coe_subgraph_injective



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
- \+/\- *lemma* absorbs_Union_finset
- \+/\- *lemma* set.finite.absorbs_Union
- \+ *lemma* balanced_empty
- \+/\- *lemma* balanced_univ
- \+ *lemma* balanced_Union
- \+ *lemma* balanced_Union₂
- \+ *lemma* balanced_Inter
- \+ *lemma* balanced_Inter₂
- \+/\- *lemma* balanced.smul
- \+ *lemma* absorbs.neg
- \+ *lemma* balanced.neg
- \+/\- *lemma* absorbs.add
- \+/\- *lemma* balanced.add
- \+ *lemma* absorbs.sub
- \+ *lemma* balanced.sub
- \+/\- *lemma* balanced_zero
- \+ *lemma* balanced.mem_smul_iff
- \+ *lemma* balanced.neg_mem_iff



## [2022-07-08 22:50:34](https://github.com/leanprover-community/mathlib/commit/fefd449)
feat(set_theory/ordinal/arithmetic): tweak `type_add` and `type_mul` ([#15193](https://github.com/leanprover-community/mathlib/pull/15193))
This renames `type_mul` to the more accurate `type_prod_lex`, and renames `type_add` to `type_sum_lex` and reverses the order of the equality so that the two lemmas match.
#### Estimated changes
Modified src/set_theory/ordinal/arithmetic.lean
- \+ *theorem* type_prod_lex
- \- *theorem* type_mul

Modified src/set_theory/ordinal/basic.lean
- \+ *theorem* type_sum_lex
- \- *theorem* type_add



## [2022-07-08 20:54:25](https://github.com/leanprover-community/mathlib/commit/f39bd5f)
feat(analysis/normed_space/star/basic): make starₗᵢ apply to normed star groups ([#15173](https://github.com/leanprover-community/mathlib/pull/15173))
#### Estimated changes
Modified src/analysis/normed_space/star/basic.lean




## [2022-07-08 20:54:25](https://github.com/leanprover-community/mathlib/commit/8a38a69)
feat(combinatorics/simple_graph/hasse): The Hasse diagram of `α × β` ([#14978](https://github.com/leanprover-community/mathlib/pull/14978))
... is the box product of the Hasse diagrams of `α` and `β`.
#### Estimated changes
Modified src/combinatorics/simple_graph/hasse.lean
- \+ *lemma* hasse_prod

Modified src/combinatorics/simple_graph/prod.lean
- \+/\- *lemma* box_prod_adj



## [2022-07-08 20:54:24](https://github.com/leanprover-community/mathlib/commit/1a54e4d)
feat(combinatorics/additive/ruzsa_covering): The Ruzsa covering lemma ([#14697](https://github.com/leanprover-community/mathlib/pull/14697))
Prove the Ruzsa covering lemma, which says that a finset `s` can be covered using at most $\frac{|s + t|}{|t|}$ copies of `t - t`.
#### Estimated changes
Created src/combinatorics/additive/ruzsa_covering.lean
- \+ *lemma* exists_subset_mul_div



## [2022-07-08 18:50:17](https://github.com/leanprover-community/mathlib/commit/2d5b45c)
chore(data/zmod/defs): shuffle files around ([#15142](https://github.com/leanprover-community/mathlib/pull/15142))
This is to prepare to fix `char_p` related diamonds. No new lemmas were added, stuff was just moved around.
#### Estimated changes
Modified src/algebra/char_p/basic.lean


Modified src/algebra/ne_zero.lean


Modified src/data/zmod/basic.lean
- \- *lemma* card
- \- *def* zmod

Created src/data/zmod/defs.lean
- \+ *lemma* card
- \+ *def* zmod

Modified src/data/zmod/quotient.lean


Modified src/ring_theory/roots_of_unity.lean




## [2022-07-08 18:50:16](https://github.com/leanprover-community/mathlib/commit/11cdccb)
feat(data/rat/defs): add denominator as pnat ([#15101](https://github.com/leanprover-community/mathlib/pull/15101))
Option to bundle `x.denom` and `x.pos` into a pnat, which can be useful in defining functions using the denominator.
#### Estimated changes
Modified src/data/rat/defs.lean
- \+ *lemma* coe_pnat_denom
- \+ *lemma* mk_pnat_pnat_denom_eq
- \+ *lemma* pnat_denom_eq_iff_denom_eq
- \+ *def* pnat_denom



## [2022-07-08 17:45:40](https://github.com/leanprover-community/mathlib/commit/feb34df)
chore(data/nat/squarefree): fix a tactic doc typo for norm num extension ([#15189](https://github.com/leanprover-community/mathlib/pull/15189))
#### Estimated changes
Modified src/data/nat/squarefree.lean




## [2022-07-08 14:49:24](https://github.com/leanprover-community/mathlib/commit/5a5d290)
fix(data/fintype/basic): move card_subtype_mono into the fintype namespace ([#15185](https://github.com/leanprover-community/mathlib/pull/15185))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *theorem* fintype.card_subtype_mono
- \- *theorem* card_subtype_mono



## [2022-07-08 13:36:19](https://github.com/leanprover-community/mathlib/commit/1937dff)
feat(analysis/normed_space/lp_space): normed_algebra structure ([#15086](https://github.com/leanprover-community/mathlib/pull/15086))
This also golfs the `normed_ring` instance to go via `subring.to_ring`, as this saves us from having to build the power, nat_cast, and int_cast structures manually.
We also rename `lp.lp_submodule` to `lp_submodule` to avoid unhelpful repetition.
#### Estimated changes
Modified src/analysis/normed_space/lp_space.lean
- \+/\- *lemma* _root_.mem_ℓp.infty_pow
- \+/\- *lemma* _root_.nat_cast_mem_ℓp_infty
- \+/\- *lemma* _root_.int_cast_mem_ℓp_infty
- \+/\- *lemma* infty_coe_fn_one
- \+/\- *lemma* infty_coe_fn_pow
- \+/\- *lemma* infty_coe_fn_nat_cast
- \+ *lemma* _root_.algebra_map_mem_ℓp_infty
- \+ *def* _root_.lp_submodule
- \+ *def* _root_.lp_infty_subring
- \+ *def* _root_.lp_infty_subalgebra
- \- *def* lp_submodule



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
- \+ *lemma* _root_.is_compact.exists_thickening_subset_open
- \+ *lemma* _root_.is_compact.exists_cthickening_subset_open



## [2022-07-08 11:29:25](https://github.com/leanprover-community/mathlib/commit/93be74b)
feat(combinatorics/simple_graph/prod): Box product ([#14867](https://github.com/leanprover-community/mathlib/pull/14867))
Define `simple_graph.box_prod`, the box product of simple graphs. Show that it's commutative and associative, and prove its connectivity properties.
#### Estimated changes
Modified src/combinatorics/simple_graph/connectivity.lean


Created src/combinatorics/simple_graph/prod.lean
- \+ *lemma* box_prod_adj
- \+ *lemma* box_prod_adj_left
- \+ *lemma* box_prod_adj_right
- \+ *lemma* of_box_prod_left_box_prod_left
- \+ *lemma* of_box_prod_left_box_prod_right
- \+ *lemma* box_prod_connected
- \+ *def* box_prod
- \+ *def* box_prod_comm
- \+ *def* box_prod_assoc
- \+ *def* box_prod_left
- \+ *def* box_prod_right
- \+ *def* of_box_prod_left
- \+ *def* of_box_prod_right



## [2022-07-08 09:53:26](https://github.com/leanprover-community/mathlib/commit/7c070c4)
feat(data/finset/basic): Coercion of a product of finsets ([#15011](https://github.com/leanprover-community/mathlib/pull/15011))
`↑(∏ i in s, f i) : set α) = ∏ i in s, ↑(f i)` for `f : ι → finset α`.
#### Estimated changes
Modified src/data/finset/pointwise.lean
- \+ *lemma* coe_coe_monoid_hom
- \+ *lemma* coe_monoid_hom_apply
- \+/\- *lemma* coe_pow
- \+ *lemma* coe_prod
- \+ *def* coe_monoid_hom

Modified src/data/polynomial/ring_division.lean




## [2022-07-08 05:24:53](https://github.com/leanprover-community/mathlib/commit/d34b330)
feat(data/set/basic,order/filter/basic): add semiconj lemmas about images and maps ([#14970](https://github.com/leanprover-community/mathlib/pull/14970))
This adds `function.commute` and `function.semiconj` lemmas, and replaces all the uses of `_comm` lemmas with the `semiconj` version as it turns out that only this generality is needed.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* _root_.function.semiconj.finset_map
- \+ *lemma* _root_.function.commute.finset_map
- \+ *lemma* _root_.function.semiconj.finset_image
- \+ *lemma* _root_.function.commute.finset_image

Modified src/data/finset/pointwise.lean


Modified src/data/set/basic.lean
- \+ *lemma* _root_.function.semiconj.set_image
- \+ *lemma* _root_.function.commute.set_image

Modified src/data/set/pointwise.lean
- \+/\- *lemma* image_op_inv

Modified src/order/filter/basic.lean
- \+ *lemma* _root_.function.semiconj.filter_map
- \+ *lemma* _root_.commute.filter_map
- \+ *lemma* _root_.function.semiconj.filter_comap
- \+ *lemma* _root_.commute.filter_comap

Modified src/order/filter/pointwise.lean
- \+/\- *lemma* map_inv'

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
- \+ *lemma* uniform_group_infi
- \+ *lemma* uniform_group_inf
- \+ *lemma* uniform_group_comap

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
- \+ *lemma* cardinal_mk_le_max_aleph_0_of_finite
- \- *lemma* cardinal_mk_le_max_aleph_0_of_fintype

Modified src/data/finite/basic.lean
- \+ *lemma* finite_iff_exists_equiv_fin

Modified src/data/mv_polynomial/cardinal.lean


Modified src/data/polynomial/cardinal.lean


Modified src/field_theory/finiteness.lean


Modified src/field_theory/is_alg_closed/classification.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/set_theory/cardinal/basic.lean
- \+ *theorem* mk_eq_nat_iff
- \+/\- *theorem* lt_aleph_0_iff_finite
- \+ *theorem* lt_aleph_0_of_finite
- \+ *theorem* lt_aleph_0_iff_set_finite
- \- *theorem* lt_aleph_0_of_fintype

Modified src/set_theory/game/short.lean




## [2022-07-08 02:55:32](https://github.com/leanprover-community/mathlib/commit/a3c647b)
feat(set_theory/ordinal/arithmetic): tweak theorems about `0` and `1` ([#15174](https://github.com/leanprover-community/mathlib/pull/15174))
We add a few basic theorems on the `0` and `1` ordinals. We rename `one_eq_type_unit` to `type_unit`, and remove `one_eq_lift_type_unit` by virtue of being a trivial consequence of `type_unit` and `lift_one`.
#### Estimated changes
Modified src/set_theory/ordinal/arithmetic.lean


Modified src/set_theory/ordinal/basic.lean
- \+ *theorem* type_pempty
- \+ *theorem* type_empty
- \+ *theorem* type_eq_one_of_unique
- \+ *theorem* type_eq_one_iff_unique
- \+ *theorem* type_punit
- \+ *theorem* type_unit
- \+/\- *theorem* lift_zero
- \+/\- *theorem* lift_one
- \- *theorem* one_eq_type_unit
- \- *theorem* one_eq_lift_type_unit



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
- \+ *lemma* forall_fin_zero_pi
- \+ *lemma* exists_fin_zero_pi
- \+ *lemma* forall_fin_succ_pi
- \+ *lemma* exists_fin_succ_pi



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


Created src/combinatorics/set_family/intersecting.lean
- \+ *lemma* intersecting.mono
- \+ *lemma* intersecting.not_bot_mem
- \+ *lemma* intersecting.ne_bot
- \+ *lemma* intersecting_empty
- \+ *lemma* intersecting_singleton
- \+ *lemma* intersecting.insert
- \+ *lemma* intersecting_insert
- \+ *lemma* intersecting_iff_pairwise_not_disjoint
- \+ *lemma* intersecting_iff_eq_empty_of_subsingleton
- \+ *lemma* intersecting.is_upper_set'
- \+ *lemma* intersecting.exists_mem_set
- \+ *lemma* intersecting.exists_mem_finset
- \+ *lemma* intersecting.not_compl_mem
- \+ *lemma* intersecting.not_mem
- \+ *lemma* intersecting.card_le
- \+ *lemma* intersecting.is_max_iff_card_eq
- \+ *lemma* intersecting.exists_card_eq
- \+ *def* intersecting

Modified src/order/upper_lower.lean
- \+ *lemma* is_lower_set.top_mem
- \+ *lemma* is_upper_set.top_mem
- \+ *lemma* is_upper_set.not_top_mem
- \+ *lemma* is_upper_set.bot_mem
- \+ *lemma* is_lower_set.bot_mem
- \+ *lemma* is_lower_set.not_bot_mem



## [2022-07-08 02:55:26](https://github.com/leanprover-community/mathlib/commit/70a2708)
feat(topology/continuous_function): Any T0 space embeds in a product of copies of the Sierpinski space ([#14036](https://github.com/leanprover-community/mathlib/pull/14036))
Any T0 space embeds in a product of copies of the Sierpinski space
#### Estimated changes
Created src/topology/continuous_function/t0_sierpinski.lean
- \+ *lemma* eq_induced_by_maps_to_sierpinski
- \+ *lemma* product_of_mem_opens_inducing
- \+ *lemma* product_of_mem_opens_injective
- \+ *theorem* product_of_mem_opens_embedding
- \+ *def* product_of_mem_opens

Modified src/topology/sets/opens.lean
- \+ *lemma* mem_mk



## [2022-07-08 00:21:19](https://github.com/leanprover-community/mathlib/commit/646028a)
refactor(data/finset/lattice): finset.{min,max} away from option ([#15163](https://github.com/leanprover-community/mathlib/pull/15163))
Switch to a `with_top`/`with_bot` based API. This avoids exposing `option`
as implementation detail.
Redefines `polynomial.degree` to use `coe` instead of `some`
#### Estimated changes
Modified archive/100-theorems-list/73_ascending_descending_sequences.lean


Modified src/combinatorics/simple_graph/basic.lean


Modified src/data/finset/lattice.lean
- \+/\- *theorem* max_empty
- \+/\- *theorem* max_singleton
- \+/\- *theorem* max_of_mem
- \+/\- *theorem* max_of_nonempty
- \+ *theorem* max_eq_bot
- \+/\- *theorem* mem_of_max
- \+/\- *theorem* le_max_of_mem
- \+/\- *theorem* min_empty
- \+/\- *theorem* min_singleton
- \+/\- *theorem* min_of_mem
- \+/\- *theorem* min_of_nonempty
- \+ *theorem* min_eq_top
- \+/\- *theorem* mem_of_min
- \+/\- *theorem* min_le_of_mem
- \+/\- *theorem* min'_le
- \+/\- *theorem* le_max'
- \- *theorem* max_eq_none
- \- *theorem* min_eq_none

Modified src/data/mv_polynomial/equiv.lean


Modified src/data/polynomial/degree/definitions.lean
- \+/\- *def* degree

Modified src/data/polynomial/degree/trailing_degree.lean


Modified src/order/bounded_order.lean
- \+ *lemma* rec_bot_coe_bot
- \+ *lemma* rec_bot_coe_coe
- \+ *lemma* unbot'_bot
- \+ *lemma* unbot'_coe
- \+ *lemma* rec_top_coe_top
- \+ *lemma* rec_top_coe_coe
- \+ *lemma* untop'_top
- \+ *lemma* untop'_coe
- \+ *def* unbot'
- \+ *def* untop'

Modified src/ring_theory/polynomial/basic.lean




## [2022-07-07 22:47:30](https://github.com/leanprover-community/mathlib/commit/8a80759)
feat(order/filter/basic): add `map_le_map` and `map_injective` ([#15128](https://github.com/leanprover-community/mathlib/pull/15128))
* Add `filter.map_le_map`, an `iff` version of `filter.map_mono`.
* Add `filter.map_injective`, a `function.injective` version of `filter.map_inj`.
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* map_le_map_iff_of_inj_on
- \+ *lemma* map_le_map_iff
- \+ *lemma* map_eq_map_iff_of_inj_on
- \+/\- *lemma* map_inj
- \+ *lemma* map_injective
- \- *lemma* le_of_map_le_map_inj'
- \- *lemma* le_of_map_le_map_inj_iff
- \- *lemma* eq_of_map_eq_map_inj'



## [2022-07-07 19:22:46](https://github.com/leanprover-community/mathlib/commit/b4979cb)
chore(data/rat): split `field ℚ` instance from definition of `ℚ` ([#14893](https://github.com/leanprover-community/mathlib/pull/14893))
I want to refer to the rational numbers in the definition of a field, meaning we can't define the field structure on `ℚ` in the same file as `ℚ` itself.
This PR moves everything in `data/rat/basic.lean` that does not depend on `algebra/field/basic.lean` into a new file `data/rat/defs.lean`: definition of the type `ℚ`, the operations giving its algebraic structure, and the coercions from integers and natural numbers. Basically, everything except the actual `field ℚ` instance.
It turns out our basic lemmas on rational numbers only require a `comm_ring`, `comm_group_with_zero` and `is_domain` instance, so I defined those instances in `defs.lean` could leave all lemmas intact.
As a consequence, the transitive imports provided by `data.rat.basic` are somewhat smaller: no `linear_ordered_field` is needed until `data.rat.order`. I see this as a bonus but can also re-import `algebra.order.field` in `data.rat.basic` if desired.
#### Estimated changes
Modified counterexamples/pseudoelement.lean


Modified src/algebra/field/basic.lean


Created src/data/rat/basic.lean


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
- \+ *lemma* nonempty_fintype
- \+/\- *def* fintype.of_finite

Modified src/data/finite/set.lean
- \+/\- *lemma* finite.of_injective_finite_range
- \- *lemma* set.finite_iff_finite
- \- *lemma* finite_bUnion
- \- *lemma* set.finite_univ_iff
- \- *lemma* finite.of_finite_univ
- \- *theorem* set.finite_of_finite

Modified src/data/polynomial/ring_division.lean


Modified src/data/set/finite.lean
- \+ *lemma* finite_coe_iff
- \+ *lemma* finite_bUnion
- \+/\- *lemma* finite.of_subsingleton
- \+/\- *lemma* finite_lt_nat
- \+/\- *lemma* finite_le_nat
- \+/\- *lemma* finite_to_set
- \+ *theorem* to_finite
- \+/\- *theorem* finite_univ
- \+ *theorem* finite_univ_iff
- \+/\- *theorem* finite_Union
- \+/\- *theorem* finite_empty
- \+/\- *theorem* finite_singleton
- \+/\- *theorem* finite_pure
- \+/\- *theorem* finite_range
- \+/\- *theorem* finite_mem_finset
- \- *theorem* finite_of_fintype
- \- *theorem* finite.of_fintype

Modified src/data/set/function.lean
- \+/\- *lemma* coe_cod_restrict_apply
- \+/\- *lemma* restrict_comp_cod_restrict
- \+/\- *lemma* injective_cod_restrict
- \+/\- *def* cod_restrict

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
- \+/\- *lemma* finite_Icc
- \+/\- *lemma* finite_Ico
- \+/\- *lemma* finite_Ioc
- \+/\- *lemma* finite_Ioo
- \+/\- *lemma* finite_Ici
- \+/\- *lemma* finite_Ioi
- \+/\- *lemma* finite_Iic
- \+/\- *lemma* finite_Iio

Modified src/order/well_founded_set.lean
- \+/\- *theorem* fintype.is_pwo

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
- \+ *lemma* not_rel_of_subsingleton
- \+ *lemma* rel_of_subsingleton
- \- *lemma* not_rel

Modified src/order/rel_iso.lean
- \+ *def* rel_iso_of_unique_of_irrefl
- \+ *def* rel_iso_of_unique_of_refl



## [2022-07-07 14:49:11](https://github.com/leanprover-community/mathlib/commit/6df59d6)
feat(data/list/basic): nth_le_enum ([#15139](https://github.com/leanprover-community/mathlib/pull/15139))
Fill out some of the `enum` and `enum_from` API
Link the two via `map_fst_add_enum_eq_enum_from`.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* enum_nil
- \+ *lemma* enum_from_nil
- \+ *lemma* enum_from_cons
- \+ *lemma* enum_cons
- \+ *lemma* enum_from_singleton
- \+ *lemma* enum_singleton
- \+ *lemma* enum_from_append
- \+ *lemma* enum_append
- \+ *lemma* map_fst_add_enum_from_eq_enum_from
- \+ *lemma* map_fst_add_enum_eq_enum_from
- \+ *lemma* nth_le_enum_from
- \+ *lemma* nth_le_enum



## [2022-07-07 13:45:33](https://github.com/leanprover-community/mathlib/commit/5852568)
feat(combinatorics/simple_graph/{basic,subgraph,clique,coloring}): add induced graphs, characterization of cliques, and bounds for colorings ([#14034](https://github.com/leanprover-community/mathlib/pull/14034))
This adds `simple_graph.map`, `simple_graph.comap`, and induced graphs and subgraphs. There are renamings: `simple_graph.subgraph.map` to `simple_graph.subgraph.inclusion`, `simple_graph.subgraph.map_top` to `simple_graph.subgraph.hom`, and `simple_graph.subgraph.map_spanning_top` to `simple_graph.subgraph.spanning_hom`. These changes originated to be able to express that a clique is a set of vertices whose induced subgraph is complete, which gives some clique-based bounds for chromatic numbers.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* map_adj
- \+ *lemma* map_monotone
- \+ *lemma* comap_monotone
- \+ *lemma* comap_map_eq
- \+ *lemma* left_inverse_comap_map
- \+ *lemma* map_injective
- \+ *lemma* comap_surjective
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* map_comap_le
- \+ *lemma* induce_spanning_coe
- \+ *lemma* spanning_coe_induce_le
- \+ *lemma* injective_of_top_hom
- \+ *lemma* to_embedding_complete_graph
- \+ *def* induce
- \+ *def* spanning_coe

Modified src/combinatorics/simple_graph/clique.lean
- \+ *lemma* is_clique_iff_induce_eq
- \+ *lemma* not_clique_free_of_top_embedding
- \+ *lemma* not_clique_free_iff
- \+ *lemma* clique_free_iff
- \+ *lemma* not_clique_free_card_of_top_embedding
- \+ *lemma* clique_free_of_card_lt
- \+ *def* top_embedding_of_not_clique_free

Modified src/combinatorics/simple_graph/coloring.lean
- \+ *lemma* is_clique.card_le_of_coloring
- \+ *lemma* is_clique.card_le_of_colorable
- \+ *lemma* is_clique.card_le_chromatic_number
- \+ *lemma* colorable.clique_free
- \+ *lemma* clique_free_of_chromatic_number_lt

Modified src/combinatorics/simple_graph/subgraph.lean
- \+ *lemma* map_monotone
- \+ *lemma* inclusion.injective
- \+ *lemma* hom.injective
- \+ *lemma* spanning_hom.injective
- \+ *lemma* _root_.simple_graph.induce_eq_coe_induce_top
- \+ *lemma* induce_mono
- \+ *lemma* induce_mono_left
- \+ *lemma* induce_mono_right
- \+ *lemma* induce_empty
- \- *lemma* map.injective
- \- *lemma* map_top.injective
- \- *lemma* map_top_to_fun
- \- *lemma* map_spanning_top.injective
- \+ *def* inclusion
- \+ *def* spanning_hom
- \+ *def* induce
- \- *def* map
- \- *def* map_top
- \- *def* map_spanning_top



## [2022-07-07 08:40:00](https://github.com/leanprover-community/mathlib/commit/1422d38)
feat(order/succ_pred): expand API on `with_bot` and `with_top` ([#15016](https://github.com/leanprover-community/mathlib/pull/15016))
We add a bunch of `simp` lemmas for successor and predecessors on `with_bot` and `with_top`, and golf some proofs.
#### Estimated changes
Modified src/order/succ_pred/basic.lean
- \+ *lemma* succ_coe_top
- \+ *lemma* succ_coe_of_ne_top
- \+ *lemma* pred_top
- \+ *lemma* pred_coe
- \+ *lemma* succ_coe
- \+ *lemma* succ_bot
- \+ *lemma* pred_coe_bot
- \+ *lemma* pred_coe_of_ne_bot



## [2022-07-07 06:45:03](https://github.com/leanprover-community/mathlib/commit/0d18630)
chore(ring_theory/norm): generalise a couple of lemmas ([#15160](https://github.com/leanprover-community/mathlib/pull/15160))
Using the generalisation linter
#### Estimated changes
Modified src/ring_theory/norm.lean
- \+/\- *lemma* norm_eq_zero_iff
- \+/\- *lemma* norm_eq_zero_iff'
- \+/\- *lemma* norm_eq_prod_embeddings_gen
- \+/\- *lemma* prod_embeddings_eq_finrank_pow



## [2022-07-07 05:04:33](https://github.com/leanprover-community/mathlib/commit/bf735cd)
chore(set_theory/ordinal/basic): remove `rel_iso_out` ([#15145](https://github.com/leanprover-community/mathlib/pull/15145))
This is just a specific application of `rel_iso.cast`. Moreover, it's unused.
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean
- \- *def* rel_iso_out



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
- \+ *lemma* pos_of_odd
- \- *lemma* odd_gt_zero



## [2022-07-07 02:38:11](https://github.com/leanprover-community/mathlib/commit/6d02dac)
feat(order/lattice, order/lattice_intervals): coe inf/sup lemmas ([#15136](https://github.com/leanprover-community/mathlib/pull/15136))
This PR adds simp lemmas for coercions of inf/sup in order instances on intervals. We also change the order of some arguments in instances/lemmas, by removing `variables` commands, so that typeclass arguments precede others.
#### Estimated changes
Modified src/order/lattice.lean
- \+ *lemma* coe_sup
- \+ *lemma* coe_inf
- \+ *lemma* mk_sup_mk
- \+ *lemma* mk_inf_mk

Modified src/order/lattice_intervals.lean




## [2022-07-07 00:12:50](https://github.com/leanprover-community/mathlib/commit/418373e)
feat(combinatorics/simple_graph/basic): `dart.to_prod` is injective ([#15150](https://github.com/leanprover-community/mathlib/pull/15150))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* dart.to_prod_injective



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
- \+/\- *lemma* tensor_id
- \+/\- *def* associator

Modified src/group_theory/congruence.lean


Modified src/group_theory/quotient_group.lean




## [2022-07-07 00:12:45](https://github.com/leanprover-community/mathlib/commit/fdfc222)
feat(measure_theory/integral): Circle integral transform ([#13885](https://github.com/leanprover-community/mathlib/pull/13885))
Some basic definitions and results related to circle integrals of a function. These form part of [#13500](https://github.com/leanprover-community/mathlib/pull/13500)
#### Estimated changes
Modified src/measure_theory/integral/circle_integral.lean
- \+ *lemma* continuous_circle_map_inv

Created src/measure_theory/integral/circle_integral_transform.lean
- \+ *lemma* circle_transform_deriv_periodic
- \+ *lemma* circle_transform_deriv_eq
- \+ *lemma* integral_circle_transform
- \+ *lemma* continuous_circle_transform
- \+ *lemma* continuous_circle_transform_deriv
- \+ *lemma* continuous_on_prod_circle_transform_function
- \+ *lemma* continuous_on_abs_circle_transform_bounding_function
- \+ *lemma* abs_circle_transform_bounding_function_le
- \+ *lemma* circle_transform_deriv_bound
- \+ *def* circle_transform
- \+ *def* circle_transform_deriv
- \+ *def* circle_transform_bounding_function



## [2022-07-06 21:58:37](https://github.com/leanprover-community/mathlib/commit/0a89f18)
chore(set_theory/ordinal/basic): clean up `ordinal.card` API ([#15147](https://github.com/leanprover-community/mathlib/pull/15147))
We tweak some spacing throughout this section of the file, and golf a few theorems/definitions.
Conflicts and is inspired by [#15137](https://github.com/leanprover-community/mathlib/pull/15137).
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean
- \+ *lemma* ne_zero_of_out_nonempty
- \+/\- *theorem* card_type
- \+/\- *theorem* type_ne_zero_iff_nonempty
- \+/\- *theorem* out_empty_iff_eq_zero
- \+/\- *def* card



## [2022-07-06 21:58:36](https://github.com/leanprover-community/mathlib/commit/a54e63d)
feat(set_theory/ordinal/basic): basic lemmas on `ordinal.lift`  ([#15146](https://github.com/leanprover-community/mathlib/pull/15146))
We add some missing instances for preimages, and missing theorems for `ordinal.lift`. We remove `ordinal.lift_type`, as it was just a worse way of stating `ordinal.type_ulift`.
We also tweak some spacing and golf a few theorems.
This conflicts with (and is inspired by) some of the changes of [#15137](https://github.com/leanprover-community/mathlib/pull/15137).
#### Estimated changes
Modified src/order/rel_iso.lean


Modified src/set_theory/cardinal/cofinality.lean


Modified src/set_theory/ordinal/basic.lean
- \+ *theorem* type_preimage
- \+ *theorem* type_ulift
- \+ *theorem* _root_.rel_iso.ordinal_lift_type_eq
- \+ *theorem* type_lift_preimage
- \+/\- *theorem* lift_zero
- \- *theorem* lift_type



## [2022-07-06 19:18:30](https://github.com/leanprover-community/mathlib/commit/b758104)
feat(order/basic): a symmetric relation implies equality when it implies less-equal ([#15149](https://github.com/leanprover-community/mathlib/pull/15149))
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* rel_imp_eq_of_rel_imp_le



## [2022-07-06 15:08:32](https://github.com/leanprover-community/mathlib/commit/d45a8ac)
refactor(topology/separation): redefine `t0_space` ([#15046](https://github.com/leanprover-community/mathlib/pull/15046))
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+ *def* nhds_order_embedding

Modified src/topology/alexandroff.lean
- \+ *lemma* specializes_coe
- \+ *lemma* inseparable_coe
- \+ *lemma* not_specializes_infty_coe
- \+ *lemma* not_inseparable_infty_coe
- \+ *lemma* not_inseparable_coe_infty
- \+ *lemma* inseparable_iff

Modified src/topology/separation.lean
- \+/\- *lemma* t0_space_iff_inseparable
- \+ *lemma* t0_space_iff_exists_is_open_xor_mem
- \+/\- *lemma* exists_is_open_xor_mem
- \+ *lemma* t1_space_iff_specializes_imp_eq
- \+/\- *lemma* specializes.eq
- \+/\- *lemma* specializes_iff_eq
- \- *lemma* t0_space_def

Modified src/topology/uniform_space/separation.lean




## [2022-07-06 13:12:54](https://github.com/leanprover-community/mathlib/commit/71b1be6)
feat(analysis/inner_product_space): add simple lemmas for the orthogonal complement ([#15020](https://github.com/leanprover-community/mathlib/pull/15020))
We show that the orthogonal complement of a dense subspace is trivial.
#### Estimated changes
Modified src/analysis/inner_product_space/projection.lean
- \+ *lemma* submodule.triorthogonal_eq_orthogonal
- \+ *lemma* submodule.topological_closure_eq_top_iff

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
- \+ *lemma* cont_diff_within_at_prop_mono
- \+ *lemma* cont_diff_within_at_prop_id
- \+ *lemma* cont_mdiff_at_iff
- \+/\- *lemma* cont_mdiff_within_at_iff'
- \+ *lemma* cont_mdiff_within_at_iff_of_mem_source
- \+ *lemma* cont_mdiff_within_at_iff_of_mem_source'
- \+ *lemma* cont_mdiff_at_iff_of_mem_source
- \+/\- *lemma* cont_mdiff_at_ext_chart_at
- \- *lemma* cont_diff_within_at_local_invariant_prop_mono
- \- *lemma* cont_diff_within_at_local_invariant_prop_id
- \- *lemma* cont_mdiff_within_at_iff''
- \+/\- *def* cont_diff_within_at_prop

Modified src/geometry/manifold/diffeomorph.lean


Modified src/geometry/manifold/local_invariant_properties.lean
- \+ *lemma* congr_set
- \+ *lemma* is_local_nhds
- \+ *lemma* left_invariance
- \+ *lemma* congr_iff_nhds_within
- \+ *lemma* congr_nhds_within
- \+ *lemma* congr_nhds_within'
- \+ *lemma* congr_iff
- \+ *lemma* congr
- \+ *lemma* congr'
- \+ *lemma* lift_prop_at_iff
- \+ *lemma* lift_prop_iff
- \+/\- *lemma* lift_prop_within_at_univ
- \+/\- *lemma* lift_prop_on_univ
- \+ *lemma* lift_prop_within_at_iff
- \+/\- *lemma* lift_prop_of_locally_lift_prop_on
- \+/\- *lemma* lift_prop_within_at_congr_iff_of_eventually_eq
- \+/\- *lemma* lift_prop_within_at_congr_iff
- \+/\- *lemma* lift_prop_within_at_congr
- \+/\- *lemma* lift_prop_at_congr_of_eventually_eq
- \+ *def* lift_prop_within_at
- \+ *def* lift_prop_on
- \+ *def* lift_prop_at
- \+ *def* lift_prop
- \- *def* charted_space.lift_prop_within_at
- \- *def* charted_space.lift_prop_on
- \- *def* charted_space.lift_prop_at
- \- *def* charted_space.lift_prop

Modified src/topology/continuous_on.lean
- \+ *lemma* mem_nhds_within_iff_eventually
- \+ *lemma* mem_nhds_within_iff_eventually_eq
- \+ *lemma* nhds_within_eq_iff_eventually_eq

Modified src/topology/local_homeomorph.lean
- \+ *lemma* eventually_nhds
- \+ *lemma* eventually_nhds'
- \+ *lemma* eventually_nhds_within
- \+ *lemma* eventually_nhds_within'
- \+ *lemma* preimage_eventually_eq_target_inter_preimage_inter



## [2022-07-06 08:41:41](https://github.com/leanprover-community/mathlib/commit/8ff5e11)
feat(analysis/special_functions/complex/arg): add complex.abs_eq_one_iff ([#15125](https://github.com/leanprover-community/mathlib/pull/15125))
This is a simpler formulation of `complex.range_exp_mul_I` below.
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* abs_eq_one_iff
- \+/\- *lemma* range_exp_mul_I



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
- \+ *lemma* set_integral_ge_of_const_le

Modified src/measure_theory/lattice.lean
- \+ *lemma* finset.measurable_sup'
- \+ *lemma* finset.measurable_range_sup'
- \+ *lemma* finset.measurable_range_sup''

Modified src/probability/hitting_time.lean
- \+ *lemma* stopped_value_hitting_mem

Modified src/probability/martingale.lean
- \+ *lemma* smul_le_stopped_value_hitting
- \+ *lemma* maximal_ineq



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
- \+ *lemma* concave_on.right_le_of_le_left'
- \+ *lemma* concave_on.right_le_of_le_left
- \+ *lemma* convex_on.le_right_of_left_le''
- \+ *lemma* convex_on.le_left_of_right_le''
- \+ *lemma* concave_on.right_le_of_le_left''
- \+ *lemma* concave_on.left_le_of_le_right''
- \- *lemma* concave_on.le_right_of_left_le'
- \- *lemma* concave_on.le_right_of_left_le



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
- \+ *theorem* is_O_with_abs_right
- \+ *theorem* is_O_abs_right
- \+ *theorem* is_o_abs_right
- \+ *theorem* is_O_with_abs_left
- \+ *theorem* is_O_abs_left
- \+ *theorem* is_o_abs_left
- \+ *theorem* is_O_with_abs_abs
- \+ *theorem* is_O_abs_abs
- \+ *theorem* is_o_abs_abs

Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/complex/basic.lean
- \+/\- *def* re_clm
- \+/\- *def* im_clm

Modified src/analysis/normed/group/basic.lean
- \+/\- *lemma* real.norm_eq_abs

Modified src/analysis/normed_space/basic.lean


Modified src/analysis/special_functions/log/deriv.lean


Modified src/geometry/euclidean/basic.lean
- \+ *lemma* angle_smul_smul
- \+ *lemma* _root_.linear_isometry.angle_map

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
- \+ *lemma* ae_le_of_forall_set_integral_le

Modified src/order/filter/basic.lean
- \+ *lemma* eventually_le.sup
- \+ *lemma* eventually_le.sup_le
- \+ *lemma* eventually_le.le_sup_of_le_left
- \+ *lemma* eventually_le.le_sup_of_le_right

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
- \- *theorem* range_sigma_mk

Modified src/data/set/sigma.lean
- \+ *lemma* image_sigma_mk_preimage_sigma_map_subset
- \+ *lemma* image_sigma_mk_preimage_sigma_map
- \+ *theorem* range_sigma_mk
- \+ *theorem* preimage_image_sigma_mk_of_ne

Modified src/data/sigma/basic.lean
- \+ *lemma* function.injective.of_sigma_map
- \+ *lemma* function.injective.sigma_map_iff
- \+/\- *lemma* prod.fst_to_sigma
- \+/\- *lemma* prod.snd_to_sigma
- \+ *lemma* prod.to_sigma_mk
- \+/\- *def* prod.to_sigma

Modified src/order/filter/bases.lean
- \+ *lemma* map_sigma_mk_comap



## [2022-07-05 16:26:49](https://github.com/leanprover-community/mathlib/commit/527afb3)
feat(topology/sets/compacts): prod constructions ([#15118](https://github.com/leanprover-community/mathlib/pull/15118))
#### Estimated changes
Modified src/topology/sets/compacts.lean
- \+ *lemma* carrier_eq_coe
- \+ *lemma* coe_prod



## [2022-07-05 15:04:58](https://github.com/leanprover-community/mathlib/commit/db9cb46)
feat(analysis/complex): equiv_real_prod_symm_apply ([#15122](https://github.com/leanprover-community/mathlib/pull/15122))
Plus some minor lemmas for [#15106](https://github.com/leanprover-community/mathlib/pull/15106).
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* arg_lt_pi_iff

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* continuous_at_rpow_const

Modified src/data/complex/basic.lean
- \+ *lemma* equiv_real_prod_symm_apply
- \+/\- *def* equiv_real_prod

Modified src/topology/separation.lean
- \+ *lemma* is_open_ne_fun



## [2022-07-05 15:04:57](https://github.com/leanprover-community/mathlib/commit/68ae182)
feat(measure_theory/group/measure): a product of Haar measures is a Haar measure ([#15120](https://github.com/leanprover-community/mathlib/pull/15120))
#### Estimated changes
Modified src/measure_theory/constructions/prod.lean
- \+ *lemma* integrable_prod_mul
- \+ *lemma* integral_prod_mul
- \+ *lemma* set_integral_prod_mul

Modified src/measure_theory/function/jacobian.lean
- \+ *theorem* integral_target_eq_integral_abs_det_fderiv_smul

Modified src/measure_theory/group/measure.lean


Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* integrable_on_Ici_iff_integrable_on_Ioi'
- \+ *lemma* integrable_on_Ici_iff_integrable_on_Ioi

Modified src/measure_theory/measure/haar.lean
- \+ *lemma* measure_preserving_inv



## [2022-07-05 12:32:49](https://github.com/leanprover-community/mathlib/commit/365e30d)
chore(data/set/*,order/*): add missing lemmas about `monotone_on` etc ([#14943](https://github.com/leanprover-community/mathlib/pull/14943))
* Add `monotone_on`/`antitone`/`antitone_on` versions of existing `monotone` lemmas for `id`/`const`, `inf`/`sup`/`min`/`max`, `inter`/`union`, and intervals.
* Drop `set.monotone_prod`, leave `monotone.set_prod` only.
* Golf some proofs that were broken by removal of `set.monotone_prod`.
#### Estimated changes
Modified src/data/set/intervals/monotone.lean


Modified src/data/set/lattice.lean
- \+ *theorem* _root_.monotone_on.inter
- \+ *theorem* _root_.antitone_on.inter
- \+ *theorem* _root_.monotone_on.union
- \+ *theorem* _root_.antitone_on.union
- \- *theorem* monotone_prod

Modified src/data/set/prod.lean
- \+ *theorem* _root_.monotone.set_prod
- \+ *theorem* _root_.antitone.set_prod
- \+ *theorem* _root_.monotone_on.set_prod
- \+ *theorem* _root_.antitone_on.set_prod

Modified src/order/filter/lift.lean


Modified src/order/lattice.lean


Modified src/order/monotone.lean
- \+ *lemma* monotone_on_id
- \+ *lemma* strict_mono_on_id
- \+ *lemma* strict_anti_of_le_iff_le
- \+ *theorem* monotone_on_const
- \+ *theorem* antitone_on_const

Modified src/tactic/monotonicity/lemmas.lean


Modified src/topology/uniform_space/basic.lean
- \+ *lemma* nhds_eq_uniformity'



## [2022-07-05 10:10:27](https://github.com/leanprover-community/mathlib/commit/dba3dce)
feat(measure_theory/function/conditional_expectation): monotonicity of the conditional expectation ([#15024](https://github.com/leanprover-community/mathlib/pull/15024))
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean
- \+ *lemma* set_integral_condexp_L2_indicator
- \+ *lemma* condexp_L2_indicator_nonneg
- \+ *lemma* condexp_ind_smul_nonneg
- \+ *lemma* condexp_ind_nonneg
- \+ *lemma* condexp_L1_mono
- \+ *lemma* condexp_mono



## [2022-07-05 10:10:26](https://github.com/leanprover-community/mathlib/commit/676e772)
refactor(analysis/convex/specific_functions): Remove hypothesis from `deriv_sqrt_mul_log` ([#15015](https://github.com/leanprover-community/mathlib/pull/15015))
This PR removes the `hx : 0 < x` hypothesis from `deriv_sqrt_mul_log`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_within_at.congr_of_mem
- \+ *theorem* has_deriv_within_at.deriv_eq_zero

Modified src/analysis/convex/specific_functions.lean
- \+ *lemma* has_deriv_at_sqrt_mul_log
- \+/\- *lemma* deriv_sqrt_mul_log
- \+ *lemma* deriv_sqrt_mul_log'
- \+/\- *lemma* deriv2_sqrt_mul_log

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
- \+ *lemma* bit0_strict_mono
- \+ *lemma* bit0_injective
- \+ *lemma* bit0_lt_bit0
- \+ *lemma* bit0_le_bit0
- \+/\- *lemma* bit0_inj
- \+/\- *lemma* bit0_eq_zero_iff
- \+ *lemma* bit0_top
- \+/\- *lemma* bit0_eq_top_iff
- \+ *lemma* bit1_strict_mono
- \+ *lemma* bit1_injective
- \+ *lemma* bit1_lt_bit1
- \+ *lemma* bit1_le_bit1
- \+/\- *lemma* bit1_inj
- \+/\- *lemma* bit1_ne_zero
- \+ *lemma* bit1_top
- \+/\- *lemma* bit1_eq_top_iff
- \+/\- *lemma* bit1_eq_one_iff
- \+ *lemma* div_eq_inv_mul
- \+/\- *lemma* coe_inv
- \+/\- *lemma* mul_inv_cancel
- \+/\- *lemma* inv_mul_cancel
- \+ *lemma* div_mul_cancel
- \+/\- *lemma* mul_div_cancel'
- \+ *lemma* inv_strict_anti
- \+/\- *lemma* inv_lt_inv
- \+/\- *lemma* inv_le_inv
- \+/\- *lemma* _root_.order_iso.inv_ennreal_symm_apply
- \+/\- *lemma* inv_le_iff_le_mul
- \+/\- *lemma* mul_div_le
- \+ *lemma* of_real_mul'
- \+/\- *lemma* to_nnreal_mul_top
- \+/\- *lemma* to_nnreal_top_mul
- \+/\- *lemma* to_nnreal_mul
- \+/\- *lemma* to_nnreal_pow
- \+/\- *lemma* to_nnreal_prod
- \+/\- *lemma* to_real_mul
- \+/\- *lemma* to_real_pow
- \+/\- *lemma* to_real_prod
- \+/\- *lemma* to_real_of_real_mul
- \+/\- *lemma* to_real_mul_top
- \+/\- *lemma* to_real_top_mul
- \+/\- *lemma* of_real_bit0
- \- *lemma* mul_div_cancel
- \+/\- *def* to_nnreal_hom
- \+/\- *def* to_real_hom

Modified src/data/real/nnreal.lean
- \+/\- *lemma* to_nnreal_bit0

Modified src/number_theory/liouville/measure.lean


Modified src/topology/algebra/order/basic.lean


Modified src/topology/constructions.lean
- \+ *lemma* prod_mem_nhds
- \+ *lemma* filter.eventually.prod_nhds
- \- *lemma* prod_is_open.mem_nhds

Modified src/topology/instances/ennreal.lean


Modified src/topology/uniform_space/compact_separated.lean




## [2022-07-04 23:23:06](https://github.com/leanprover-community/mathlib/commit/1886093)
chore(analysis/calculus/deriv): make the exponent explicit in pow lemmas ([#15117](https://github.com/leanprover-community/mathlib/pull/15117))
This is useful to build derivatives for explicit functions using dot notation.
#### Estimated changes
Modified archive/100-theorems-list/9_area_of_a_circle.lean


Modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* deriv_pow
- \+/\- *lemma* deriv_pow'

Modified src/analysis/complex/phragmen_lindelof.lean


Modified src/analysis/convex/specific_functions.lean


Modified src/analysis/special_functions/integrals.lean




## [2022-07-04 21:37:31](https://github.com/leanprover-community/mathlib/commit/73d15d7)
feat(number_theory/wilson): add Wilson's Theorem ([#14717](https://github.com/leanprover-community/mathlib/pull/14717))
The previous "Wilson's lemma" (zmod.wilsons_lemma) was a single direction of the iff for Wilson's Theorem. This finishes the proof by adding the (admittedly, much simpler) direction where, if the congruence is satisfied for `n`, then `n` is prime.
#### Estimated changes
Created src/number_theory/wilson.lean
- \+ *lemma* prime_of_fac_equiv_neg_one
- \+ *theorem* prime_iff_fac_equiv_neg_one



## [2022-07-04 20:40:33](https://github.com/leanprover-community/mathlib/commit/06ac34b)
feat(analysis/special_functions/complex/arg): `continuous_at_arg_coe_angle` ([#14980](https://github.com/leanprover-community/mathlib/pull/14980))
Add the lemma that `complex.arg`, coerced to `real.angle`, is
continuous except at 0.
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* continuous_at_arg_coe_angle



## [2022-07-04 19:58:37](https://github.com/leanprover-community/mathlib/commit/8f391f5)
feat(geometry/euclidean/basic): `continuous_at_angle` ([#15021](https://github.com/leanprover-community/mathlib/pull/15021))
Add lemmas that (unoriented) angles are continuous, as a function of a
pair of vectors or a triple of points, except where one of the vectors
is zero or one of the end points equals the middle point.
#### Estimated changes
Modified src/geometry/euclidean/basic.lean
- \+ *lemma* continuous_at_angle



## [2022-07-04 17:12:28](https://github.com/leanprover-community/mathlib/commit/407f39b)
chore(ring_theory/matrix_algebra): golf using `matrix.map` ([#15040](https://github.com/leanprover-community/mathlib/pull/15040))
This replaces terms of the form `λ i j, a * algebra_map R A (m i j)` with the defeq `a • m.map (algebra_map R A)`, as then we get access to the API about `map`.
This also leverages existing bundled maps to avoid reproving linearity in the auxiliary constructions, removing `to_fun` and `to_fun_right_linear` as we can construct `to_fun_bilinear` directly with ease.
#### Estimated changes
Modified src/ring_theory/matrix_algebra.lean
- \+ *lemma* to_fun_bilinear_apply
- \- *def* to_fun
- \- *def* to_fun_right_linear



## [2022-07-04 01:38:58](https://github.com/leanprover-community/mathlib/commit/051dffa)
refactor(data/nat/parity): `nat.even_succ` -> `nat.even_add_one` ([#14917](https://github.com/leanprover-community/mathlib/pull/14917))
Change `nat.even_succ` to be analogous to `int.even_add_one`.
#### Estimated changes
Modified archive/100-theorems-list/70_perfect_numbers.lean


Modified src/algebra/geom_sum.lean


Modified src/analysis/special_functions/log/deriv.lean


Modified src/data/nat/parity.lean
- \+ *theorem* even_add_one
- \- *theorem* even_succ



## [2022-07-03 17:11:19](https://github.com/leanprover-community/mathlib/commit/46344b4)
feat(category_theory/limits): bilimit from kernel ([#14452](https://github.com/leanprover-community/mathlib/pull/14452))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *def* binary_fan.is_limit.mk
- \+ *def* binary_cofan.is_colimit.mk

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* binary_bicone.is_bilimit_of_kernel_inl
- \+ *def* binary_bicone.is_bilimit_of_kernel_inr
- \+ *def* binary_bicone.is_bilimit_of_cokernel_fst
- \+ *def* binary_bicone.is_bilimit_of_cokernel_snd



## [2022-07-03 11:47:31](https://github.com/leanprover-community/mathlib/commit/024a423)
refactor(category_theory): generalise universe levels in preservation statements ([#15067](https://github.com/leanprover-community/mathlib/pull/15067))
This big refactoring of universe levels in the category theory library allows to express limit preservation statements like exactness of functors which are between categories that are not necessarily in the same universe level. For this change to make sense for fixed diagrams (like coequalizers or binary products), the corresponding index categories, the universe of which so far was pinned to the category they were used for, is now fixed to `Type`.
#### Estimated changes
Modified src/algebra/category/FinVect/limits.lean


Modified src/algebra/category/Group/biproducts.lean
- \+/\- *lemma* biproduct_iso_pi_inv_comp_π
- \+/\- *def* biproduct_iso_pi

Modified src/algebra/category/Module/biproducts.lean


Modified src/algebra/category/Ring/constructions.lean


Modified src/algebraic_geometry/Spec.lean
- \+/\- *def* Spec.to_PresheafedSpace

Modified src/algebraic_geometry/locally_ringed_space/has_colimits.lean


Modified src/algebraic_geometry/open_immersion.lean
- \+/\- *lemma* SheafedSpace_to_SheafedSpace

Modified src/algebraic_geometry/presheafed_space.lean
- \+/\- *lemma* as_coe
- \+/\- *lemma* id_base
- \+/\- *lemma* id_c
- \+/\- *lemma* id_c_app
- \+/\- *lemma* comp_base
- \+/\- *lemma* coe_to_fun_eq
- \+/\- *lemma* comp_c_app
- \+/\- *lemma* congr_app
- \+/\- *lemma* Γ_map_op
- \+/\- *lemma* map_presheaf_map_f
- \+/\- *lemma* map_presheaf_map_c
- \+/\- *def* id
- \+/\- *def* forget
- \+/\- *def* restrict
- \+/\- *def* of_restrict
- \+/\- *def* Γ
- \+/\- *def* map_presheaf

Modified src/algebraic_geometry/presheafed_space/gluing.lean


Modified src/algebraic_geometry/presheafed_space/has_colimits.lean
- \+/\- *lemma* map_id_c_app
- \+/\- *lemma* map_comp_c_app
- \+/\- *lemma* colimit_carrier
- \+/\- *lemma* colimit_presheaf
- \+/\- *lemma* desc_c_naturality
- \+/\- *lemma* desc_fac
- \+/\- *lemma* colimit_presheaf_obj_iso_componentwise_limit_inv_ι_app
- \+/\- *lemma* colimit_presheaf_obj_iso_componentwise_limit_hom_π
- \+/\- *def* componentwise_diagram
- \+/\- *def* pushforward_diagram_to_colimit
- \+/\- *def* colimit
- \+/\- *def* colimit_cocone
- \+/\- *def* desc_c_app
- \+/\- *def* desc
- \+/\- *def* colimit_cocone_is_colimit
- \+/\- *def* colimit_presheaf_obj_iso_componentwise_limit

Modified src/algebraic_geometry/sheafed_space.lean
- \+/\- *lemma* as_coe
- \+ *def* unit
- \+/\- *def* forget_to_PresheafedSpace
- \- *def* punit

Modified src/algebraic_geometry/stalks.lean
- \+/\- *lemma* stalk_map_germ
- \+/\- *lemma* restrict_stalk_iso_hom_eq_germ
- \+/\- *lemma* restrict_stalk_iso_inv_eq_germ
- \+/\- *lemma* restrict_stalk_iso_inv_eq_of_restrict
- \+/\- *lemma* id
- \+/\- *lemma* comp
- \+/\- *lemma* congr
- \+/\- *lemma* congr_hom
- \+/\- *lemma* congr_point
- \+/\- *lemma* stalk_specializes_stalk_map
- \+/\- *def* stalk_map
- \+/\- *def* restrict_stalk_iso
- \+/\- *def* stalk_iso

Modified src/algebraic_topology/cech_nerve.lean


Modified src/category_theory/abelian/right_derived.lean


Modified src/category_theory/closed/functor.lean


Modified src/category_theory/closed/ideal.lean


Modified src/category_theory/closed/types.lean


Modified src/category_theory/discrete_category.lean
- \+ *def* functor_comp

Modified src/category_theory/filtered.lean


Modified src/category_theory/fin_category.lean


Modified src/category_theory/functor/flat.lean


Modified src/category_theory/functor/left_derived.lean


Modified src/category_theory/graded_object.lean


Modified src/category_theory/idempotents/biproducts.lean
- \+/\- *def* bicone

Modified src/category_theory/is_connected.lean


Modified src/category_theory/limits/colimit_limit.lean


Modified src/category_theory/limits/comma.lean


Modified src/category_theory/limits/concrete_category.lean
- \+/\- *lemma* concrete.wide_pullback_ext
- \+/\- *lemma* concrete.wide_pullback_ext'
- \+/\- *lemma* concrete.multiequalizer_ext
- \+/\- *lemma* concrete.multiequalizer_equiv_apply
- \+/\- *def* concrete.multiequalizer_equiv

Modified src/category_theory/limits/cone_category.lean


Modified src/category_theory/limits/constructions/finite_products_of_binary_products.lean
- \+/\- *def* extend_fan
- \+/\- *def* extend_fan_is_limit
- \+ *def* preserves_shape_fin_of_preserves_binary_and_terminal
- \+/\- *def* extend_cofan
- \+/\- *def* extend_cofan_is_colimit
- \+ *def* preserves_shape_fin_of_preserves_binary_and_initial
- \- *def* preserves_ulift_fin_of_preserves_binary_and_terminal
- \- *def* preserves_ulift_fin_of_preserves_binary_and_initial

Modified src/category_theory/limits/constructions/limits_of_products_and_equalizers.lean
- \+/\- *def* limit_subobject_product
- \+/\- *def* colimit_quotient_coproduct

Modified src/category_theory/limits/constructions/over/default.lean


Modified src/category_theory/limits/constructions/over/products.lean
- \+/\- *lemma* over_products_of_wide_pullbacks
- \+/\- *def* wide_pullback_diagram_of_diagram_over
- \+/\- *def* cones_equiv_inverse_obj
- \+/\- *def* cones_equiv_inverse
- \+/\- *def* cones_equiv_functor

Modified src/category_theory/limits/constructions/weakly_initial.lean
- \+/\- *lemma* has_weakly_initial_of_weakly_initial_set_and_has_products
- \+/\- *lemma* has_initial_of_weakly_initial_and_has_wide_equalizers

Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean


Modified src/category_theory/limits/has_limits.lean
- \- *lemma* has_smallest_limits_of_has_limits
- \- *lemma* has_smallest_colimits_of_has_colimits

Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/limits/opposites.lean
- \+/\- *lemma* has_finite_coproducts_opposite
- \+/\- *lemma* has_finite_products_opposite

Modified src/category_theory/limits/preserves/basic.lean
- \+ *def* preserves_limits_of_size_shrink
- \+ *def* preserves_smallest_limits_of_preserves_limits
- \+ *def* preserves_colimits_of_size_shrink
- \+ *def* preserves_smallest_colimits_of_preserves_colimits
- \+ *def* reflects_limits_of_shape_of_equiv
- \+ *def* reflects_limits_of_size_shrink
- \+ *def* reflects_smallest_limits_of_reflects_limits
- \+ *def* reflects_colimits_of_shape_of_equiv
- \+ *def* reflects_colimits_of_size_shrink
- \+ *def* reflects_smallest_colimits_of_reflects_colimits

Modified src/category_theory/limits/preserves/finite.lean
- \+ *def* preserves_finite_limits_of_preserves_finite_limits_of_size
- \+ *def* preserves_finite_colimits_of_preserves_finite_colimits_of_size

Modified src/category_theory/limits/preserves/shapes/binary_products.lean


Modified src/category_theory/limits/preserves/shapes/biproducts.lean
- \+ *lemma* map_bicone_whisker
- \+ *def* preserves_biproducts_shrink

Modified src/category_theory/limits/preserves/shapes/equalizers.lean


Modified src/category_theory/limits/preserves/shapes/kernels.lean


Modified src/category_theory/limits/preserves/shapes/products.lean


Modified src/category_theory/limits/preserves/shapes/pullbacks.lean


Modified src/category_theory/limits/preserves/shapes/terminal.lean
- \+/\- *lemma* has_terminal_of_has_terminal_of_preserves_limit
- \+/\- *lemma* has_initial_of_has_initial_of_preserves_colimit
- \+/\- *def* is_terminal.is_terminal_obj
- \+/\- *def* is_terminal.is_terminal_of_obj
- \+/\- *def* is_limit_of_has_terminal_of_preserves_limit
- \+/\- *def* is_initial.is_initial_obj
- \+/\- *def* is_initial.is_initial_of_obj
- \+/\- *def* is_colimit_of_has_initial_of_preserves_colimit

Modified src/category_theory/limits/preserves/shapes/zero.lean


Modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *lemma* prod.diag_map_fst_snd_comp
- \+/\- *lemma* coprod.map_comp_inl_inr_codiag
- \+/\- *def* pair

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* whisker
- \+ *def* whisker_to_cone
- \+ *def* whisker_to_cocone
- \+ *def* whisker_is_bilimit_iff
- \+/\- *def* biproduct.reindex

Modified src/category_theory/limits/shapes/comm_sq.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+/\- *def* walking_parallel_pair_op
- \+/\- *def* walking_parallel_pair_op_equiv
- \+/\- *def* parallel_pair
- \+/\- *def* parallel_pair.ext

Modified src/category_theory/limits/shapes/finite_limits.lean
- \+ *lemma* has_finite_limits_of_has_finite_limits_of_size
- \+ *lemma* has_finite_colimits_of_has_finite_colimits_of_size

Modified src/category_theory/limits/shapes/finite_products.lean
- \+/\- *lemma* has_finite_products_of_has_products
- \+/\- *lemma* has_finite_coproducts_of_has_coproducts

Modified src/category_theory/limits/shapes/functor_category.lean


Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/limits/shapes/multiequalizer.lean


Modified src/category_theory/limits/shapes/products.lean
- \+ *lemma* has_smallest_products_of_has_products
- \+ *lemma* has_smallest_coproducts_of_has_coproducts
- \+/\- *lemma* has_products_of_limit_fans

Modified src/category_theory/limits/shapes/pullbacks.lean
- \- *lemma* walking_cospan_functor_one
- \- *lemma* walking_cospan_functor_left
- \- *lemma* walking_cospan_functor_right
- \- *lemma* walking_cospan_functor_id
- \- *lemma* walking_cospan_functor_inl
- \- *lemma* walking_cospan_functor_inr
- \- *lemma* walking_span_functor_zero
- \- *lemma* walking_span_functor_left
- \- *lemma* walking_span_functor_right
- \- *lemma* walking_span_functor_id
- \- *lemma* walking_span_functor_fst
- \- *lemma* walking_span_functor_snd
- \- *def* walking_cospan_functor
- \- *def* walking_cospan_equiv
- \- *def* walking_span_functor
- \- *def* walking_span_equiv

Modified src/category_theory/limits/shapes/split_coequalizer.lean


Modified src/category_theory/limits/shapes/terminal.lean
- \+/\- *def* as_empty_cone
- \+/\- *def* as_empty_cocone
- \+/\- *def* is_terminal_equiv_unique
- \+/\- *def* is_initial_equiv_unique

Modified src/category_theory/limits/shapes/types.lean


Modified src/category_theory/limits/shapes/wide_equalizers.lean


Modified src/category_theory/limits/shapes/wide_pullbacks.lean
- \+ *lemma* has_wide_pullbacks_shrink
- \+ *def* equivalence_of_equiv
- \+ *def* ulift_equivalence

Modified src/category_theory/limits/shapes/zero_morphisms.lean


Modified src/category_theory/limits/small_complete.lean


Renamed src/category_theory/limits/punit.lean to src/category_theory/limits/unit.lean


Modified src/category_theory/limits/yoneda.lean
- \+/\- *def* yoneda_jointly_reflects_limits
- \+/\- *def* coyoneda_jointly_reflects_limits

Modified src/category_theory/monoidal/preadditive.lean
- \+/\- *lemma* left_distributor_hom
- \+/\- *lemma* left_distributor_inv
- \+/\- *lemma* left_distributor_assoc
- \+/\- *lemma* right_distributor_hom
- \+/\- *lemma* right_distributor_inv
- \+/\- *lemma* right_distributor_assoc
- \+/\- *def* left_distributor
- \+/\- *def* right_distributor

Modified src/category_theory/preadditive/Mat.lean


Modified src/category_theory/preadditive/biproducts.lean


Modified src/category_theory/preadditive/hom_orthogonal.lean


Modified src/category_theory/sites/left_exact.lean


Modified src/category_theory/sites/sheaf.lean


Modified src/category_theory/subobject/lattice.lean


Modified src/order/category/omega_complete_partial_order.lean


Modified src/topology/category/Top/limits.lean
- \+/\- *lemma* coequalizer_is_open_iff

Modified src/topology/sheaves/forget.lean


Modified src/topology/sheaves/functors.lean


Modified src/topology/sheaves/limits.lean
- \+/\- *lemma* is_sheaf_of_is_limit
- \+/\- *lemma* limit_is_sheaf

Modified src/topology/sheaves/presheaf.lean
- \+/\- *lemma* pushforward_obj_obj
- \+/\- *lemma* pushforward_obj_map
- \+/\- *lemma* pushforward_eq'
- \+/\- *lemma* pushforward_eq_rfl
- \+/\- *lemma* pushforward_eq_eq
- \+/\- *lemma* comp_eq
- \+/\- *lemma* comp_hom_app
- \+/\- *lemma* comp_inv_app
- \+/\- *lemma* pullback_obj_eq_pullback_obj
- \+/\- *def* presheaf
- \+/\- *def* pushforward_obj
- \+/\- *def* pushforward_eq
- \+/\- *def* comp
- \+/\- *def* pushforward_map

Modified src/topology/sheaves/sheaf.lean
- \+ *lemma* is_sheaf_unit
- \- *lemma* is_sheaf_punit
- \+/\- *def* is_sheaf
- \+/\- *def* sheaf

Modified src/topology/sheaves/sheaf_condition/equalizer_products.lean
- \+/\- *def* diagram

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
- \+ *lemma* of_bijective_apply_symm_apply

Modified src/data/nat/enat.lean
- \+ *lemma* not_dom_iff_eq_top

Modified src/ring_theory/chain_of_divisors.lean
- \+ *lemma* factor_order_iso_map_one_eq_bot
- \+ *lemma* coe_factor_order_iso_map_eq_one_iff
- \+/\- *lemma* pow_image_of_prime_by_factor_order_iso_dvd
- \+ *lemma* map_prime_of_factor_order_iso
- \+ *lemma* mem_normalized_factors_factor_order_iso_of_mem_normalized_factors
- \+/\- *lemma* multiplicity_prime_le_multiplicity_image_by_factor_order_iso
- \+ *lemma* multiplicity_prime_eq_multiplicity_image_by_factor_order_iso
- \+ *lemma* mem_normalized_factors_factor_dvd_iso_of_mem_normalized_factors
- \+ *lemma* multiplicity_eq_multiplicity_factor_dvd_iso_of_mem_normalized_factor
- \+ *def* mk_factor_order_iso_of_factor_dvd_equiv

Modified src/ring_theory/dedekind_domain/ideal.lean
- \+ *lemma* ideal_factors_fun_of_quot_hom_id
- \+ *lemma* ideal_factors_fun_of_quot_hom_comp
- \+ *def* ideal_factors_fun_of_quot_hom
- \+ *def* ideal_factors_equiv_of_quot_equiv

Modified src/ring_theory/multiplicity.lean
- \+ *lemma* multiplicity_mk_eq_multiplicity



## [2022-07-02 12:02:23](https://github.com/leanprover-community/mathlib/commit/4823da2)
feat(data/nat/basic): add `mul_div_mul_comm_of_dvd_dvd` ([#15031](https://github.com/leanprover-community/mathlib/pull/15031))
Add lemma `mul_div_mul_comm_of_dvd_dvd (hac : c ∣ a) (hbd : d ∣ b) : (a * b) / (c * d) = (a / c) * (b / d)`
(Compare with `mul_div_mul_comm`, which holds for a `division_comm_monoid`)
Also adds the same lemma for a `euclidean_domain`.
#### Estimated changes
Modified src/algebra/euclidean_domain.lean
- \+ *lemma* mul_div_mul_comm_of_dvd_dvd

Modified src/data/nat/basic.lean
- \+ *lemma* mul_div_mul_comm_of_dvd_dvd



## [2022-07-02 10:12:17](https://github.com/leanprover-community/mathlib/commit/2d76f56)
chore(algebra/associated): make `irreducible` not a class ([#14713](https://github.com/leanprover-community/mathlib/pull/14713))
This functionality was rarely used and doesn't align with how `irreducible` is used in practice.
In a future PR, we can remove some `unfreezingI`s caused by this.
#### Estimated changes
Modified src/algebra/associated.lean
- \- *lemma* not_unit

Modified src/algebra/module/pid.lean


Modified src/field_theory/adjoin.lean


Modified src/field_theory/normal.lean


Modified src/field_theory/separable_degree.lean
- \+ *lemma* _root_.irreducible.has_separable_contraction
- \- *lemma* irreducible_has_separable_contraction

Modified src/field_theory/splitting_field.lean
- \+ *lemma* irreducible_factor
- \+ *lemma* fact_irreducible_factor

Modified src/number_theory/number_field.lean


Modified src/ring_theory/adjoin_root.lean
- \+/\- *lemma* coe_injective
- \+ *lemma* coe_injective'
- \+/\- *lemma* mul_div_root_cancel



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
- \+ *lemma* uniform_continuous_inf_rng
- \+ *lemma* uniform_continuous_inf_dom_left
- \+ *lemma* uniform_continuous_inf_dom_right
- \+ *lemma* uniform_continuous_Inf_dom
- \+ *lemma* uniform_continuous_Inf_rng
- \+ *lemma* uniform_continuous_infi_dom
- \+ *lemma* uniform_continuous_infi_rng
- \+ *lemma* uniform_continuous_inf_dom_left₂
- \+ *lemma* uniform_continuous_inf_dom_right₂
- \+ *lemma* uniform_continuous_Inf_dom₂



## [2022-07-01 18:31:15](https://github.com/leanprover-community/mathlib/commit/ff5e97a)
feat(order/lattice, data/set): some helper lemmas ([#14789](https://github.com/leanprover-community/mathlib/pull/14789))
This PR provides lemmas describing when `s ∪ a = t ∪ a`, in both necessary and iff forms, as well as intersection and lattice versions.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* union_eq_union_of_subset_of_subset
- \+ *lemma* union_eq_union_iff_subset_subset
- \+ *lemma* inter_eq_inter_of_subset_of_subset
- \+ *lemma* inter_eq_inter_iff_subset_subset

Modified src/order/lattice.lean
- \+ *lemma* sup_eq_sup_of_le_of_le
- \+ *lemma* sup_eq_sup_iff_le_le
- \+ *lemma* inf_eq_inf_of_le_of_le
- \+ *lemma* inf_eq_inf_iff_le_le



## [2022-07-01 18:31:14](https://github.com/leanprover-community/mathlib/commit/7f95e22)
feat(linear_algebra/*): add lemma `linear_independent.finite_of_is_noetherian` ([#14714](https://github.com/leanprover-community/mathlib/pull/14714))
This replaces `fintype_of_is_noetherian_linear_independent` which gave the same
conclusion except demanded `strong_rank_condition R` instead of just `nontrivial R`.
Also some other minor gaps filled.
#### Estimated changes
Modified src/algebra/module/torsion.lean
- \+ *lemma* torsion_of_zero
- \+ *lemma* torsion_of_eq_top_iff
- \+ *lemma* torsion_of_eq_bot_iff_of_no_zero_smul_divisors
- \+ *lemma* complete_lattice.independent.linear_independent'

Modified src/analysis/box_integral/partition/measure.lean


Modified src/data/finite/set.lean
- \+ *lemma* finite.of_injective_finite_range

Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/dfinsupp.lean
- \+ *lemma* independent_iff_linear_independent_of_ne_zero

Modified src/linear_algebra/dimension.lean
- \+ *lemma* linear_independent.finite_of_is_noetherian
- \+ *lemma* linear_independent.set_finite_of_is_noetherian
- \- *lemma* finite_of_is_noetherian_linear_independent

Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent.independent_span_singleton

Modified src/linear_algebra/matrix/diagonal.lean


Modified src/linear_algebra/span.lean
- \+/\- *lemma* span_eq_supr_of_singleton_spans
- \+ *lemma* span_range_eq_supr
- \+/\- *lemma* to_span_singleton_one
- \+ *lemma* to_span_singleton_zero

Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/integral/divergence_theorem.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/order/compactly_generated.lean
- \+ *lemma* well_founded.finite_of_independent

Modified src/order/sup_indep.lean
- \+/\- *lemma* independent.mono
- \+/\- *lemma* independent.comp
- \+ *lemma* independent.comp'
- \+ *lemma* independent.set_independent_range
- \+ *lemma* independent.injective
- \+/\- *theorem* independent_def'
- \+/\- *theorem* independent_def''



## [2022-07-01 14:39:25](https://github.com/leanprover-community/mathlib/commit/2ae2065)
chore(data/set,topology): fix 2 lemma names ([#15079](https://github.com/leanprover-community/mathlib/pull/15079))
* rename `set.quot_mk_range_eq` to `set.range_quotient_mk`;
* rename `is_closed_infi_iff` to `is_closed_supr_iff`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* range_quotient_mk
- \- *theorem* quot_mk_range_eq

Modified src/topology/order.lean
- \+ *lemma* is_closed_supr_iff
- \- *lemma* is_closed_infi_iff



## [2022-07-01 14:39:24](https://github.com/leanprover-community/mathlib/commit/8b69a4b)
feat(ring_theory): Some missing lemmas ([#15064](https://github.com/leanprover-community/mathlib/pull/15064))
#### Estimated changes
Modified src/algebra/algebra/subalgebra/basic.lean


Modified src/linear_algebra/span.lean
- \+ *lemma* closure_subset_span
- \+ *lemma* closure_le_to_add_submonoid_span
- \+ *lemma* span_closure

Modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* adjoin_span

Modified src/ring_theory/finiteness.lean
- \+ *lemma* is_noetherian_ring
- \+ *lemma* _root_.subalgebra.fg_iff_finite_type

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* smul_inf_le

Modified src/ring_theory/noetherian.lean
- \+ *lemma* fg_finset_sup
- \+ *lemma* fg_bsupr
- \+ *lemma* fg_supr



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
- \+ *lemma* eq_zero_iff
- \+ *lemma* ne_zero_iff
- \+ *lemma* not_is_max_coe



## [2022-07-01 12:26:32](https://github.com/leanprover-community/mathlib/commit/6e362f6)
chore(algebra/order/monoid): golf proofs, fix docs ([#14728](https://github.com/leanprover-community/mathlib/pull/14728))
#### Estimated changes
Modified src/algebra/order/monoid.lean




## [2022-07-01 10:20:04](https://github.com/leanprover-community/mathlib/commit/9e97baa)
feat(data/list/basic): add filter_map_join ([#14777](https://github.com/leanprover-community/mathlib/pull/14777))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* filter_map_join



## [2022-07-01 10:20:03](https://github.com/leanprover-community/mathlib/commit/e73ac94)
feat (analysis/normed_space/lp_space):add l_infinity ring instances ([#14104](https://github.com/leanprover-community/mathlib/pull/14104))
We define pointwise multiplication on `lp E ∞` and give it has_mul, non_unital_ring, non_unital_normed_ring, ring, normed_ring, comm_ring and normed_comm_ring instances under the appropriate assumptions.
#### Estimated changes
Modified src/analysis/normed_space/lp_space.lean
- \+ *lemma* _root_.mem_ℓp.infty_mul
- \+ *lemma* infty_coe_fn_mul
- \+ *lemma* _root_.one_mem_ℓp_infty
- \+ *lemma* infty_coe_fn_one
- \+ *lemma* _root_.mem_ℓp.infty_pow
- \+ *lemma* infty_coe_fn_pow
- \+ *lemma* _root_.nat_cast_mem_ℓp_infty
- \+ *lemma* infty_coe_fn_nat_cast
- \+ *lemma* _root_.int_cast_mem_ℓp_infty
- \+ *lemma* infty_coe_fn_int_cast



## [2022-07-01 08:11:22](https://github.com/leanprover-community/mathlib/commit/ce332c1)
refactor(algebra/group_power): split ring lemmas into a separate file ([#15032](https://github.com/leanprover-community/mathlib/pull/15032))
This doesn't actually stop `algebra.ring.basic` being imported into `group_power.basic` yet, but it makes it easier to make that change in future. Two ~300 line files are also slightly easier to manage than one ~600 line file, and ring/add_group feels like a natural place to draw the line
All lemmas have just been moved, and none have been renamed. Some lemmas have had their `R` variables renamed to `M` to better reflect that they apply to monoids with zero.
By grouping together the `monoid_with_zero` lemmas from separate files, it become apparent that there's some overlap.
This PR does not attempt to clean this up, in the interest of limiting the the scope of this change to just moves.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \- *lemma* zero_pow
- \- *lemma* zero_pow_eq
- \- *lemma* pow_eq_zero_of_le
- \- *lemma* coe_pow_monoid_with_zero_hom
- \- *lemma* pow_monoid_with_zero_hom_apply
- \- *lemma* pow_eq_zero_iff
- \- *lemma* pow_eq_zero_iff'
- \- *lemma* pow_ne_zero_iff
- \- *lemma* pow_dvd_pow_iff
- \- *lemma* min_pow_dvd_add
- \- *lemma* add_sq
- \- *lemma* add_sq'
- \- *lemma* neg_sq
- \- *lemma* neg_one_sq
- \- *lemma* neg_one_pow_mul_eq_zero_iff
- \- *lemma* mul_neg_one_pow_eq_zero_iff
- \- *lemma* sq_eq_one_iff
- \- *lemma* sq_ne_one_iff
- \- *lemma* sq_sub_sq
- \- *lemma* sub_sq
- \- *lemma* sub_sq'
- \- *lemma* sq_eq_sq_iff_eq_or_eq_neg
- \- *lemma* eq_or_eq_neg_of_sq_eq_sq
- \- *theorem* pow_eq_zero
- \- *theorem* pow_ne_zero
- \- *theorem* sq_eq_zero_iff
- \- *theorem* neg_one_pow_eq_or
- \- *theorem* neg_pow
- \- *theorem* neg_pow_bit0
- \- *theorem* neg_pow_bit1
- \- *def* pow_monoid_with_zero_hom

Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/group_power/order.lean


Created src/algebra/group_power/ring.lean
- \+ *lemma* zero_pow
- \+ *lemma* zero_pow'
- \+ *lemma* zero_pow_eq
- \+ *lemma* pow_eq_zero_of_le
- \+ *lemma* pow_eq_zero_iff
- \+ *lemma* pow_eq_zero_iff'
- \+ *lemma* pow_ne_zero_iff
- \+ *lemma* ne_zero_pow
- \+ *lemma* zero_pow_eq_zero
- \+ *lemma* ring.inverse_pow
- \+ *lemma* coe_pow_monoid_with_zero_hom
- \+ *lemma* pow_monoid_with_zero_hom_apply
- \+ *lemma* pow_dvd_pow_iff
- \+ *lemma* min_pow_dvd_add
- \+ *lemma* add_sq
- \+ *lemma* add_sq'
- \+ *lemma* neg_sq
- \+ *lemma* neg_one_sq
- \+ *lemma* neg_one_pow_mul_eq_zero_iff
- \+ *lemma* mul_neg_one_pow_eq_zero_iff
- \+ *lemma* sq_eq_one_iff
- \+ *lemma* sq_ne_one_iff
- \+ *lemma* sq_sub_sq
- \+ *lemma* sub_sq
- \+ *lemma* sub_sq'
- \+ *lemma* sq_eq_sq_iff_eq_or_eq_neg
- \+ *lemma* eq_or_eq_neg_of_sq_eq_sq
- \+ *theorem* pow_eq_zero
- \+ *theorem* pow_ne_zero
- \+ *theorem* sq_eq_zero_iff
- \+ *theorem* neg_one_pow_eq_or
- \+ *theorem* neg_pow
- \+ *theorem* neg_pow_bit0
- \+ *theorem* neg_pow_bit1
- \+ *def* pow_monoid_with_zero_hom

Modified src/algebra/group_with_zero/power.lean
- \- *lemma* zero_pow'
- \- *lemma* ne_zero_pow
- \- *lemma* zero_pow_eq_zero
- \- *lemma* ring.inverse_pow



## [2022-07-01 04:21:43](https://github.com/leanprover-community/mathlib/commit/7e244d8)
feat(algebra/category/Module): upgrade `free : Type ⥤ Module R` to a monoidal functor ([#14328](https://github.com/leanprover-community/mathlib/pull/14328))
#### Estimated changes
Modified src/algebra/category/Module/adjunctions.lean
- \+ *lemma* ε_apply
- \+/\- *def* μ
- \+ *def* monoidal_free

