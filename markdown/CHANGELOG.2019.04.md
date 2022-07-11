## [2019-04-30 20:17:17](https://github.com/leanprover-community/mathlib/commit/c8a2aa9)
chore(category_theory): move small_category_of_preorder to preorder namespace ([#932](https://github.com/leanprover-community/mathlib/pull/932))
#### Estimated changes
Modified src/category_theory/category.lean




## [2019-04-30 18:22:31+02:00](https://github.com/leanprover-community/mathlib/commit/7c86814)
fix(scripts/remote-install-update-mathlib): try again [ci skip]
The previous attempt to install setuptools seems to fails for timing
reasons (PyGithub need setuptools after it's downloaded but before
it is installed, this is probably also a packaging issue in PyGithub).
#### Estimated changes
Modified scripts/remote-install-update-mathlib.sh




## [2019-04-30 15:20:36](https://github.com/leanprover-community/mathlib/commit/a15fca5)
fix(scripts/remote-install-update-mathlib): missing dependency ([#964](https://github.com/leanprover-community/mathlib/pull/964))
Also add a `--upgrade` option to `pip install` in case something is
already there but outdated
#### Estimated changes
Modified scripts/remote-install-update-mathlib.sh




## [2019-04-30 12:53:25+01:00](https://github.com/leanprover-community/mathlib/commit/8dcce05)
feat(analysis/normed_space): open mapping ([#900](https://github.com/leanprover-community/mathlib/pull/900))
* The Banach open mapping theorem
* improve comments
* feat(analysis/normed_space): rebase, fix build
#### Estimated changes
Created src/analysis/normed_space/banach.lean
- \+ *theorem* exists_preimage_norm_le
- \+ *theorem* open_mapping
- \+ *theorem* linear_equiv.is_bounded_inv

Modified src/analysis/specific_limits.lean
- \+ *lemma* summable_geometric
- \+ *lemma* tsum_geometric
- \+/\- *lemma* has_sum_geometric_two
- \+ *lemma* summable_geometric_two
- \+ *lemma* tsum_geometric_two
- \+ *lemma* has_sum_geometric_two'



## [2019-04-29 20:12:03](https://github.com/leanprover-community/mathlib/commit/00aaf05)
refactor(tactic/interactive): remove dependencies of ([#878](https://github.com/leanprover-community/mathlib/pull/878))
`tactic/interactive` on many theories
#### Estimated changes
Modified .travis.yml


Modified src/algebra/associated.lean


Modified src/algebra/big_operators.lean


Modified src/algebra/char_p.lean


Modified src/algebra/field_power.lean


Modified src/algebra/free.lean


Modified src/algebra/group_power.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/pointwise.lean


Modified src/algebra/punit_instances.lean


Modified src/algebra/ring.lean


Modified src/analysis/normed_space/basic.lean


Modified src/category/bitraversable/basic.lean


Modified src/category/monad/cont.lean


Modified src/category/traversable/equiv.lean


Modified src/category_theory/adjunction.lean


Modified src/category_theory/category.lean


Modified src/category_theory/comma.lean


Modified src/category_theory/core.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/instances/CommRing/basic.lean


Modified src/category_theory/instances/Top/basic.lean


Modified src/category_theory/instances/Top/open_nhds.lean


Modified src/category_theory/instances/Top/opens.lean


Modified src/category_theory/instances/groups.lean


Modified src/category_theory/instances/measurable_space.lean


Modified src/category_theory/instances/monoids.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/category_theory/opposites.lean


Modified src/category_theory/types.lean


Modified src/data/analysis/filter.lean


Modified src/data/equiv/basic.lean


Modified src/data/equiv/list.lean


Modified src/data/erased.lean


Modified src/data/finset.lean


Modified src/data/fintype.lean


Modified src/data/hash_map.lean


Modified src/data/list/basic.lean


Modified src/data/list/defs.lean


Modified src/data/list/perm.lean
- \+/\- *theorem* nil_subperm

Modified src/data/list/sigma.lean


Modified src/data/nat/prime.lean


Modified src/data/nat/sqrt.lean


Modified src/data/num/basic.lean


Modified src/data/option/basic.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/pfun.lean


Modified src/data/rat.lean


Modified src/data/real/basic.lean


Modified src/data/seq/computation.lean


Modified src/data/seq/seq.lean


Modified src/data/set/basic.lean


Modified src/data/set/enumerate.lean


Modified src/data/set/intervals.lean


Modified src/data/vector2.lean


Modified src/data/zsqrtd/gaussian_int.lean


Modified src/field_theory/finite.lean


Modified src/field_theory/splitting_field.lean


Modified src/group_theory/eckmann_hilton.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/determinant.lean


Modified src/logic/basic.lean
- \+/\- *lemma* iff_iff_not_or_and_or_not

Modified src/logic/relator.lean


Modified src/logic/unique.lean


Modified src/measure_theory/giry_monad.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean


Modified src/number_theory/dioph.lean


Modified src/number_theory/pell.lean


Modified src/order/basic.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/filter/default.lean


Modified src/order/lexicographic.lean


Modified src/order/zorn.lean


Modified src/ring_theory/algebra_operations.lean


Modified src/ring_theory/polynomial.lean


Modified src/set_theory/lists.lean


Modified src/tactic/basic.lean


Modified src/tactic/chain.lean


Modified src/tactic/default.lean


Modified src/tactic/interactive.lean


Modified src/tactic/omega/nat/dnf.lean


Modified src/tactic/omega/nat/main.lean


Modified src/tactic/rcases.lean


Modified src/tactic/tfae.lean


Modified src/tactic/tidy.lean


Modified src/tactic/wlog.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean


Modified src/topology/bounded_continuous_function.lean


Modified src/topology/instances/polynomial.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/isometry.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/completion.lean




## [2019-04-29 12:46:38+02:00](https://github.com/leanprover-community/mathlib/commit/9b3e91b)
Update elan.md
#### Estimated changes
Modified docs/elan.md




## [2019-04-26 20:52:03](https://github.com/leanprover-community/mathlib/commit/53f9878)
refactor(analysis/normed_space): use bundled type for `fderiv` ([#956](https://github.com/leanprover-community/mathlib/pull/956))
* feat(analysis/normed_space): refactor fderiv to use bounded_linear_map
- uniqueness remains sorry'd
- more simp lemmas about bounded_linear_map
* refactor uniqueness proof
* fix(analysis/normed_space/operator_norm): rename `bound_le_op_norm` to `op_norm_le_bound`
- so that the inequality goes the correct way.
#### Estimated changes
Modified src/analysis/normed_space/deriv.lean
- \+/\- *lemma* fderiv_at_filter_unique
- \+/\- *theorem* has_fderiv_at_filter_iff_tendsto
- \+/\- *theorem* has_fderiv_at_within_iff_tendsto
- \+/\- *theorem* has_fderiv_at_iff_tendsto
- \+/\- *theorem* has_fderiv_at_filter.mono
- \+/\- *theorem* has_fderiv_at_within.mono
- \+/\- *theorem* has_fderiv_at_filter_of_has_fderiv_at
- \+/\- *theorem* has_fderiv_at_within_of_has_fderiv_at
- \+/\- *theorem* has_fderiv_at_filter_congr'
- \+/\- *theorem* has_fderiv_at_filter_congr
- \+/\- *theorem* has_fderiv_at_filter.congr
- \+/\- *theorem* has_fderiv_at_within_congr
- \+/\- *theorem* has_fderiv_at_within.congr
- \+/\- *theorem* has_fderiv_at_congr
- \+/\- *theorem* has_fderiv_at.congr
- \+/\- *theorem* has_fderiv_at_filter_id
- \+/\- *theorem* has_fderiv_at_within_id
- \+/\- *theorem* has_fderiv_at_id
- \+/\- *theorem* has_fderiv_at_filter_smul
- \+/\- *theorem* has_fderiv_at_within_smul
- \+/\- *theorem* has_fderiv_at_smul
- \+/\- *theorem* has_fderiv_at_filter_add
- \+/\- *theorem* has_fderiv_at_within_add
- \+/\- *theorem* has_fderiv_at_add
- \+/\- *theorem* has_fderiv_at_filter_neg
- \+/\- *theorem* has_fderiv_at_within_neg
- \+/\- *theorem* has_fderiv_at_neg
- \+/\- *theorem* has_fderiv_at_filter_sub
- \+/\- *theorem* has_fderiv_at_within_sub
- \+/\- *theorem* has_fderiv_at_sub
- \+/\- *theorem* has_fderiv_at_filter.is_O_sub
- \+/\- *theorem* has_fderiv_at_filter.tendsto_nhds
- \+/\- *theorem* has_fderiv_at_within.continuous_at_within
- \+/\- *theorem* has_fderiv_at.continuous_at
- \+/\- *theorem* has_fderiv_at_filter.comp
- \+/\- *theorem* has_fderiv_at_within.comp
- \+/\- *theorem* has_fderiv_at.comp
- \+/\- *theorem* fderiv_at_unique
- \+/\- *theorem* fderiv_at_within_open_unique
- \+/\- *theorem* has_fderiv_at_filter_real_equiv
- \- *theorem* has_fderiv_at_filter.is_o
- \- *theorem* has_fderiv_at.is_o
- \+/\- *def* has_fderiv_at_filter
- \+/\- *def* has_fderiv_at_within
- \+/\- *def* has_fderiv_at

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* op_norm_le_bound
- \- *lemma* bound_le_op_norm



## [2019-04-26 22:27:05+02:00](https://github.com/leanprover-community/mathlib/commit/b49bf61)
fix(README): update maintainer list
#### Estimated changes
Modified README.md




## [2019-04-26 10:52:46+01:00](https://github.com/leanprover-community/mathlib/commit/0444f9c)
feat(data/equiv/basic): sum_compl_apply and others ([#961](https://github.com/leanprover-community/mathlib/pull/961))
* feat(data/equiv/basic): sum_congr_apply and others
* Update basic.lean
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* univ_apply
- \+ *lemma* univ_symm_apply
- \+ *lemma* union_apply_left
- \+ *lemma* union_apply_right
- \+ *lemma* of_eq_apply
- \+ *lemma* of_eq_symm_apply
- \+ *lemma* sum_compl_apply_inl
- \+ *lemma* sum_compl_apply_inr
- \+ *lemma* sum_compl_symm_apply_of_mem
- \+ *lemma* sum_compl_symm_apply_of_not_mem
- \+ *theorem* symm_symm_apply



## [2019-04-25 18:58:02](https://github.com/leanprover-community/mathlib/commit/038f809)
refactor(analysis/normed_space/operator_norm): replace subspace with … ([#955](https://github.com/leanprover-community/mathlib/pull/955))
* refactor(analysis/normed_space/operator_norm): replace subspace with structure
* refactor(analysis/normed_space/operator_norm): add coercions
#### Estimated changes
Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* bounded_linear_map.is_bounded_linear_map
- \- *lemma* mul_inv_eq'
- \+ *def* to_bounded_linear_map

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* exists_pos_bound_of_bound
- \+ *lemma* coe_coe
- \+/\- *lemma* coe_zero
- \+ *lemma* coe_zero'
- \+ *lemma* id_apply
- \+ *lemma* coe_id
- \+ *lemma* coe_id'
- \+ *lemma* add_apply
- \+ *lemma* coe_add
- \+ *lemma* coe_add'
- \+/\- *lemma* smul_apply
- \+ *lemma* coe_apply
- \+ *lemma* coe_apply'
- \+/\- *lemma* neg_apply
- \+ *lemma* coe_neg
- \+ *lemma* coe_neg'
- \+ *lemma* sub_apply
- \+ *lemma* coe_sub
- \+ *lemma* coe_sub'
- \+ *lemma* coe_comp
- \+ *lemma* coe_comp'
- \- *lemma* zero_smul
- \- *lemma* one_smul
- \+/\- *theorem* is_O_sub
- \+ *theorem* continuous
- \- *theorem* tendsto
- \+ *def* zero
- \+ *def* id
- \- *def* bounded_linear_map_subspace
- \- *def* bounded_linear_map
- \- *def* is_bounded_linear_map.to_bounded_linear_map
- \- *def* to_linear_map



## [2019-04-23 20:15:47](https://github.com/leanprover-community/mathlib/commit/1d9ff68)
feat(function/embedding): ext and ext_iff ([#962](https://github.com/leanprover-community/mathlib/pull/962))
#### Estimated changes
Modified src/logic/embedding.lean
- \+ *lemma* ext
- \+ *lemma* ext_iff



## [2019-04-23 07:22:05](https://github.com/leanprover-community/mathlib/commit/0d7b419)
fix(ring_theory/adjoin_root): move adjoin_root out of adjoin_root namespace ([#960](https://github.com/leanprover-community/mathlib/pull/960))
#### Estimated changes
Modified src/ring_theory/adjoin_root.lean
- \+/\- *def* adjoin_root



## [2019-04-22 23:48:35](https://github.com/leanprover-community/mathlib/commit/45456cf)
refactor(data/equiv/basic): simplify definition of equiv.set.range ([#959](https://github.com/leanprover-community/mathlib/pull/959))
* refactor(data/equiv/basic): simplify definition of equiv.set.range
* delete duplicate
#### Estimated changes
Modified src/data/equiv/basic.lean




## [2019-04-22 15:00:53](https://github.com/leanprover-community/mathlib/commit/63bbd1c)
feat(data/list/basic): index_of_inj ([#954](https://github.com/leanprover-community/mathlib/pull/954))
* feat(data/list/basic): index_of_inj
* make it an iff
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* index_of_inj



## [2019-04-21 06:07:43-04:00](https://github.com/leanprover-community/mathlib/commit/3478f1f)
fix(tactic/interactive): allow `convert e using 0`
#### Estimated changes
Modified src/tactic/interactive.lean




## [2019-04-20 18:42:45-04:00](https://github.com/leanprover-community/mathlib/commit/9daa1a5)
feat(tactic/clear_except): clear most of the assumptions in context ([#957](https://github.com/leanprover-community/mathlib/pull/957))
#### Estimated changes
Modified src/tactic/interactive.lean




## [2019-04-20 20:07:03](https://github.com/leanprover-community/mathlib/commit/4b9d94d)
feat(data/[fin]set): add some more basic properties of (finite) sets ([#948](https://github.com/leanprover-community/mathlib/pull/948))
* feat(data/[fin]set): add some more basic properties of (finite) sets
* update after reviews
* fix error, move pairwise_disjoint to lattice as well
* fix error
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/data/finset.lean
- \+ *lemma* to_set_injective
- \+ *lemma* nonempty_iff_ne_empty
- \+ *lemma* to_set_sdiff
- \+ *lemma* subset_union_elim
- \+ *lemma* subset_image_iff
- \+ *theorem* filter_union_right

Modified src/data/set/basic.lean
- \+ *lemma* subset_union_of_subset_left
- \+ *lemma* subset_union_of_subset_right
- \+ *lemma* nmem_singleton_empty
- \+ *lemma* compl_empty_iff
- \+ *lemma* compl_univ_iff
- \+ *lemma* nonempty_compl
- \+ *lemma* subset_insert_diff
- \+ *lemma* diff_singleton_subset_iff
- \+ *lemma* subset_insert_diff_singleton
- \+ *lemma* mem_diff_singleton
- \+ *lemma* mem_diff_singleton_empty
- \+ *lemma* image_congr'
- \+ *lemma* image_image
- \+ *lemma* image_id'
- \+ *lemma* nonempty_image
- \+ *lemma* preimage_subset_preimage_iff
- \+ *lemma* preimage_eq_preimage'
- \+ *lemma* image_eq_range
- \+ *lemma* range_val
- \+ *lemma* exists_set_subtype

Modified src/data/set/finite.lean
- \+ *lemma* finite.coe_to_finset
- \+ *lemma* exists_finset_of_finite
- \+ *theorem* finite_bUnion'

Modified src/data/set/function.lean
- \+ *lemma* inj_on_comp_of_injective_left
- \+ *lemma* inj_on_preimage
- \+/\- *theorem* inj_on_comp

Modified src/data/set/lattice.lean
- \+ *lemma* subset_sUnion_of_subset
- \+ *lemma* Union_of_singleton
- \+ *lemma* Union_range_eq_sUnion
- \+ *lemma* Union_range_eq_Union
- \+ *lemma* disjoint_self
- \+ *lemma* ne_of_disjoint
- \+ *lemma* pairwise_disjoint_subset
- \+ *lemma* pairwise_disjoint_range
- \+ *lemma* pairwise_disjoint_elim
- \+ *def* pairwise_disjoint



## [2019-04-20 15:39:59+02:00](https://github.com/leanprover-community/mathlib/commit/7370cbf)
feat(tactic/linarith): treat expr atoms up to defeq ([#950](https://github.com/leanprover-community/mathlib/pull/950))
#### Estimated changes
Modified src/tactic/linarith.lean


Modified test/linarith.lean




## [2019-04-20 09:47:15](https://github.com/leanprover-community/mathlib/commit/784a68c)
fix(topology/order): Missing Prop annotation ([#952](https://github.com/leanprover-community/mathlib/pull/952))
#### Estimated changes
Modified src/topology/order.lean




## [2019-04-20 00:49:21](https://github.com/leanprover-community/mathlib/commit/e4fc5af)
feat(tactic/ring): treat expr atoms up to defeq ([#949](https://github.com/leanprover-community/mathlib/pull/949))
#### Estimated changes
Modified src/tactic/ring.lean


Modified test/ring.lean




## [2019-04-18 22:33:17-04:00](https://github.com/leanprover-community/mathlib/commit/c1aff1b)
style(tactic/omega): whitespace and minor tweaks
missed the PR review cycle
#### Estimated changes
Modified src/data/list/basic.lean
- \+/\- *lemma* get_nil
- \+/\- *lemma* get_map
- \+/\- *lemma* get_map'
- \+/\- *lemma* forall_val_of_forall_mem
- \+/\- *lemma* equiv_symm
- \+/\- *lemma* equiv_of_eq
- \+/\- *lemma* get_neg
- \+/\- *lemma* length_neg
- \+/\- *lemma* nil_pointwise
- \+/\- *lemma* pointwise_nil
- \+/\- *lemma* get_pointwise
- \+/\- *lemma* length_pointwise
- \+/\- *lemma* length_add
- \+/\- *lemma* nil_add
- \+/\- *lemma* add_nil
- \+/\- *lemma* get_sub
- \+/\- *lemma* length_sub
- \+/\- *lemma* nil_sub
- \+/\- *lemma* sub_nil

Modified src/tactic/omega/coeffs.lean
- \+/\- *lemma* val_except_update_set
- \+/\- *lemma* val_between_map_div

Modified src/tactic/omega/eq_elim.lean


Modified src/tactic/omega/find_ees.lean


Modified src/tactic/omega/int/dnf.lean


Modified src/tactic/omega/int/form.lean


Modified src/tactic/omega/int/main.lean


Modified src/tactic/omega/int/preterm.lean


Modified src/tactic/omega/misc.lean


Modified src/tactic/omega/nat/dnf.lean


Modified src/tactic/omega/nat/form.lean
- \+/\- *lemma* univ_close_of_valid
- \+/\- *lemma* valid_of_unsat_not
- \+/\- *def* holds
- \+/\- *def* univ_close
- \+/\- *def* neg_free
- \+/\- *def* sub_free
- \+/\- *def* fresh_index
- \+/\- *def* valid
- \+/\- *def* sat
- \+/\- *def* implies
- \+/\- *def* equiv
- \+/\- *def* repr

Modified src/tactic/omega/nat/main.lean


Modified src/tactic/omega/nat/neg_elim.lean
- \+/\- *lemma* push_neg_equiv
- \+/\- *lemma* is_nnf_nnf
- \+/\- *lemma* neg_free_neg_elim_core
- \+/\- *lemma* le_and_le_iff_eq
- \+/\- *lemma* implies_neg_elim_core
- \+/\- *lemma* neg_free_neg_elim
- \+/\- *def* push_neg
- \+/\- *def* nnf
- \+/\- *def* is_nnf
- \+/\- *def* neg_elim_core

Modified src/tactic/omega/nat/preterm.lean
- \+/\- *lemma* val_add
- \+/\- *lemma* val_sub
- \+/\- *lemma* val_canonize
- \+/\- *def* val
- \+/\- *def* fresh_index
- \+/\- *def* repr
- \+/\- *def* sub_free
- \+/\- *def* canonize

Modified src/tactic/omega/nat/sub_elim.lean


Modified src/tactic/omega/term.lean
- \+ *def* to_string

Modified test/omega.lean




## [2019-04-18 20:15:55](https://github.com/leanprover-community/mathlib/commit/d0140dd)
feat(group_theory/subgroup): additive version of inj_iff_trivial_ker ([#947](https://github.com/leanprover-community/mathlib/pull/947))
#### Estimated changes
Modified src/group_theory/subgroup.lean




## [2019-04-17 15:33:51](https://github.com/leanprover-community/mathlib/commit/032400b)
feat(analysis/normed_space): more facts about operator norm ([#927](https://github.com/leanprover-community/mathlib/pull/927))
* refactor(analysis/normed_space): refactor and additional lemmas
- rename `bounded_linear_maps` to `bounded_linear_map`, `operator_norm` to `op_norm`.
- refactor operator norm with an equivalent definition.
- change some names and notation to be more consistent with conventions elsewhere
  in mathlib: replace `bounded_by_*` with `le_*`, `operator_norm_homogeneous` with
  `op_norm_smul`.
- more simp lemmas for bounded_linear_map.
- additional results: lipschitz continuity of the operator norm, also
  that it is submultiplicative.
* chore(analysis/normed_space/operator_norm): add attribution
* style(analysis/normed_space/operator_norm): use namespace `real`
- open `real` instead of `lattice` and omit spurious prefixes.
* feat(analysis/normed_space/operator_norm): coercion to linear_map
* style(analysis/normed_space/bounded_linear_maps): minor edits
- extract variables for brevity of theorem statements.
- more consistent naming of variables.
* feat(analysis/normed_space/operator_norm): add constructor of bounded_linear_map from is_bounded_linear_map
* fix(analysis/normed_space/operator_norm): remove spurious explicit argument
* fix(analysis/normed_space): type of bounded linear maps
- change the definition of bounded_linear_map to be a type rather than
  the corresponding subspace, and mark it for unfolding.
- rename `bounded_linear_map.from_is_bounded_linear_map` to `is_bounded_linear_map.to_bounded_linear_map`.
* feat(analysis/normed_space): analysis results for bounded_linear_maps
#### Estimated changes
Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+/\- *lemma* smul
- \+/\- *lemma* neg
- \+/\- *lemma* add
- \+/\- *lemma* sub
- \+/\- *lemma* comp
- \+/\- *lemma* tendsto
- \+/\- *lemma* continuous
- \+/\- *lemma* lim_zero_bounded_linear_map
- \+/\- *theorem* is_O_id
- \+/\- *theorem* is_O_comp
- \+/\- *theorem* is_O_sub

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* map_zero
- \+ *lemma* map_add
- \+ *lemma* map_sub
- \+ *lemma* map_smul
- \+ *lemma* map_neg
- \+ *lemma* coe_zero
- \+ *lemma* zero_apply
- \+ *lemma* smul_apply
- \+ *lemma* neg_apply
- \+ *lemma* zero_smul
- \+ *lemma* one_smul
- \+ *lemma* bounds_nonempty
- \+ *lemma* bounds_bdd_below
- \+ *lemma* op_norm_nonneg
- \+ *lemma* ratio_le_op_norm
- \+ *lemma* unit_le_op_norm
- \+ *lemma* bound_le_op_norm
- \+ *lemma* op_norm_smul
- \+ *lemma* op_norm_comp_le
- \- *lemma* bounded_linear_maps.map_zero
- \- *lemma* bounded_linear_maps.coe_zero
- \- *lemma* bounded_linear_maps.smul_coe
- \- *lemma* bounded_linear_maps.zero_smul
- \- *lemma* bounded_linear_maps.one_smul
- \- *lemma* exists_bound
- \- *lemma* bdd_above_range_norm_image_div_norm
- \- *lemma* operator_norm_nonneg
- \- *lemma* operator_norm_bounded_by
- \- *lemma* operator_norm_homogeneous_le
- \+/\- *theorem* ext
- \+ *theorem* ext_iff
- \+ *theorem* tendsto
- \+ *theorem* is_O_id
- \+ *theorem* is_O_comp
- \+ *theorem* is_O_sub
- \+ *theorem* le_op_norm
- \+ *theorem* op_norm_triangle
- \+ *theorem* op_norm_zero_iff
- \+ *theorem* lipschitz
- \- *theorem* bounded_by_operator_norm
- \- *theorem* operator_norm_triangle
- \- *theorem* operator_norm_zero_iff
- \- *theorem* operator_norm_homogeneous
- \+ *def* bounded_linear_map_subspace
- \+ *def* bounded_linear_map
- \+ *def* is_bounded_linear_map.to_bounded_linear_map
- \+/\- *def* to_linear_map
- \+ *def* comp
- \+ *def* op_norm
- \- *def* bounded_linear_maps



## [2019-04-17 09:53:00-04:00](https://github.com/leanprover-community/mathlib/commit/8b23dad)
feat(scripts): use apt-get on ubuntu and support older Python versions ([#945](https://github.com/leanprover-community/mathlib/pull/945))
#### Estimated changes
Modified .travis.yml


Modified scripts/setup-dev-scripts.sh


Modified scripts/update-mathlib.py




## [2019-04-17 11:03:45+02:00](https://github.com/leanprover-community/mathlib/commit/3f4b154)
feat(tactic/omega): tactic for linear integer & natural number arithmetic ([#827](https://github.com/leanprover-community/mathlib/pull/827))
* feat(tactic/omega): tactic for discharging linear integer and natural number arithmetic goals
* refactor(tactic/omega): clean up namespace and notations
* Update src/data/list/func.lean
Co-Authored-By: skbaek <seulkeebaek@gmail.com>
* Add changed files
* Refactor val_between_map_div
* Use default inhabitants for list.func
#### Estimated changes
Modified docs/tactics.md


Modified src/data/int/basic.lean
- \+ *lemma* default_eq_zero
- \+ *lemma* add_div_of_dvd

Modified src/data/list/basic.lean
- \+/\- *lemma* filter_ge
- \+ *lemma* length_set
- \+ *lemma* get_nil
- \+ *lemma* get_eq_default_of_le
- \+ *lemma* get_set
- \+ *lemma* eq_get_of_mem
- \+ *lemma* mem_get_of_le
- \+ *lemma* mem_get_of_ne_zero
- \+ *lemma* get_set_eq_of_ne
- \+ *lemma* get_map
- \+ *lemma* get_map'
- \+ *lemma* forall_val_of_forall_mem
- \+ *lemma* equiv_refl
- \+ *lemma* equiv_symm
- \+ *lemma* equiv_trans
- \+ *lemma* equiv_of_eq
- \+ *lemma* eq_of_equiv
- \+ *lemma* get_neg
- \+ *lemma* length_neg
- \+ *lemma* nil_pointwise
- \+ *lemma* pointwise_nil
- \+ *lemma* get_pointwise
- \+ *lemma* length_pointwise
- \+ *lemma* get_add
- \+ *lemma* length_add
- \+ *lemma* nil_add
- \+ *lemma* add_nil
- \+ *lemma* map_add_map
- \+ *lemma* get_sub
- \+ *lemma* length_sub
- \+ *lemma* nil_sub
- \+ *lemma* sub_nil

Modified src/data/list/defs.lean
- \+ *def* map_with_index_core
- \+ *def* map_with_index
- \+ *def* set
- \+ *def* get
- \+ *def* equiv
- \+ *def* neg
- \+ *def* pointwise
- \+ *def* add
- \+ *def* sub

Modified src/data/nat/basic.lean
- \+ *lemma* zero_max
- \+ *lemma* lt_iff_add_one_le
- \+ *theorem* max_succ_succ

Modified src/logic/basic.lean
- \+ *lemma* iff_iff_not_or_and_or_not

Created src/tactic/omega/clause.lean
- \+ *lemma* clauses.unsat_nil
- \+ *lemma* clauses.unsat_cons
- \+ *def* clause
- \+ *def* holds
- \+ *def* sat
- \+ *def* unsat
- \+ *def* append
- \+ *def* holds_append
- \+ *def* clauses.sat
- \+ *def* clauses.unsat

Created src/tactic/omega/coeffs.lean
- \+ *lemma* val_between_nil
- \+ *lemma* val_nil
- \+ *lemma* val_between_eq_of_le
- \+ *lemma* val_eq_of_le
- \+ *lemma* val_between_eq_val_between
- \+ *lemma* val_between_neg
- \+ *lemma* val_neg
- \+ *lemma* val_between_add
- \+ *lemma* val_add
- \+ *lemma* val_between_sub
- \+ *lemma* val_sub
- \+ *lemma* val_except_eq_val_except
- \+ *lemma* val_except_update_set
- \+ *lemma* val_between_add_val_between
- \+ *lemma* val_between_map_mul
- \+ *lemma* forall_val_dvd_of_forall_mem_dvd
- \+ *lemma* dvd_val_between
- \+ *lemma* dvd_val
- \+ *lemma* val_between_map_div
- \+ *lemma* val_map_div
- \+ *lemma* val_between_eq_zero
- \+ *lemma* val_eq_zero
- \+ *def* val_between
- \+ *def* val
- \+ *def* val_between_set
- \+ *def* val_set
- \+ *def* val_except
- \+ *def* val_except_add_eq

Created src/tactic/omega/default.lean


Created src/tactic/omega/eq_elim.lean
- \+ *lemma* symmod_add_one_self
- \+ *lemma* mul_symdiv_eq
- \+ *lemma* symmod_eq
- \+ *lemma* rhs_correct_aux
- \+ *lemma* rhs_correct
- \+ *lemma* coeffs_reduce_correct
- \+ *lemma* subst_correct
- \+ *lemma* sat_empty
- \+ *lemma* sat_eq_elim
- \+ *lemma* unsat_of_unsat_eq_elim
- \+ *def* symdiv
- \+ *def* symmod
- \+ *def* sgm
- \+ *def* rhs
- \+ *def* sym_sym
- \+ *def* coeffs_reduce
- \+ *def* cancel
- \+ *def* subst
- \+ *def* repr
- \+ *def* eq_elim

Created src/tactic/omega/find_ees.lean
- \+ *def* gcd

Created src/tactic/omega/find_scalars.lean


Created src/tactic/omega/int/dnf.lean
- \+ *lemma* push_neg_equiv
- \+ *lemma* is_nnf_push_neg
- \+ *lemma* is_nnf_nnf
- \+ *lemma* nnf_equiv
- \+ *lemma* neg_free_neg_elim
- \+ *lemma* le_and_le_iff_eq
- \+ *lemma* implies_neg_elim
- \+ *lemma* exists_clause_holds
- \+ *lemma* clauses_sat_dnf_core
- \+ *lemma* unsat_of_clauses_unsat
- \+ *def* push_neg
- \+ *def* nnf
- \+ *def* is_nnf
- \+ *def* neg_free
- \+ *def* neg_elim
- \+ *def* dnf_core
- \+ *def* dnf

Created src/tactic/omega/int/form.lean
- \+ *lemma* sat_of_implies_of_sat
- \+ *lemma* sat_or
- \+ *lemma* univ_close_of_valid
- \+ *lemma* valid_of_unsat_not
- \+ *def* holds
- \+ *def* univ_close
- \+ *def* fresh_index
- \+ *def* valid
- \+ *def* sat
- \+ *def* implies
- \+ *def* equiv
- \+ *def* unsat
- \+ *def* repr

Created src/tactic/omega/int/main.lean
- \+ *lemma* univ_close_of_unsat_clausify

Created src/tactic/omega/int/preterm.lean
- \+ *lemma* val_canonize
- \+ *def* val
- \+ *def* fresh_index
- \+ *def* add_one
- \+ *def* repr
- \+ *def* canonize

Created src/tactic/omega/lin_comb.lean
- \+ *lemma* lin_comb_holds
- \+ *lemma* unsat_lin_comb_of
- \+ *lemma* unsat_of_unsat_lin_comb
- \+ *def* lin_comb
- \+ *def* unsat_lin_comb

Created src/tactic/omega/main.lean


Created src/tactic/omega/misc.lean
- \+ *lemma* fun_mono_2
- \+ *lemma* pred_mono_2
- \+ *lemma* pred_mono_2'
- \+ *lemma* update_eq
- \+ *lemma* update_eq_of_ne
- \+ *def* update
- \+ *def* update_zero

Created src/tactic/omega/nat/dnf.lean
- \+ *lemma* exists_clause_holds_core
- \+ *lemma* holds_nonneg_consts_core
- \+ *lemma* holds_nonneg_consts
- \+ *lemma* exists_clause_holds
- \+ *lemma* exists_clause_sat
- \+ *lemma* unsat_of_unsat_dnf
- \+ *def* dnf_core
- \+ *def* term.vars_core
- \+ *def* term.vars
- \+ *def* bools.or
- \+ *def* terms.vars
- \+ *def* nonneg_consts_core
- \+ *def* nonneg_consts
- \+ *def* nonnegate
- \+ *def* dnf

Created src/tactic/omega/nat/form.lean
- \+ *lemma* sat_of_implies_of_sat
- \+ *lemma* sat_or
- \+ *lemma* univ_close_of_valid
- \+ *lemma* valid_of_unsat_not
- \+ *def* holds
- \+ *def* univ_close
- \+ *def* neg_free
- \+ *def* sub_free
- \+ *def* fresh_index
- \+ *def* holds_constant
- \+ *def* valid
- \+ *def* sat
- \+ *def* implies
- \+ *def* equiv
- \+ *def* unsat
- \+ *def* repr

Created src/tactic/omega/nat/main.lean
- \+ *lemma* univ_close_of_unsat_neg_elim_not

Created src/tactic/omega/nat/neg_elim.lean
- \+ *lemma* push_neg_equiv
- \+ *lemma* is_nnf_push_neg
- \+ *lemma* is_nnf_nnf
- \+ *lemma* nnf_equiv
- \+ *lemma* neg_free_neg_elim_core
- \+ *lemma* le_and_le_iff_eq
- \+ *lemma* implies_neg_elim_core
- \+ *lemma* neg_free_neg_elim
- \+ *lemma* implies_neg_elim
- \+ *def* push_neg
- \+ *def* nnf
- \+ *def* is_nnf
- \+ *def* neg_elim_core
- \+ *def* neg_elim

Created src/tactic/omega/nat/preterm.lean
- \+ *lemma* val_const
- \+ *lemma* val_var
- \+ *lemma* val_add
- \+ *lemma* val_sub
- \+ *lemma* val_canonize
- \+ *def* val
- \+ *def* fresh_index
- \+ *def* val_constant
- \+ *def* repr
- \+ *def* add_one
- \+ *def* sub_free
- \+ *def* canonize

Created src/tactic/omega/nat/sub_elim.lean
- \+ *lemma* val_sub_subst
- \+ *lemma* holds_is_diff
- \+ *lemma* sub_subst_equiv
- \+ *lemma* sat_sub_elim
- \+ *lemma* unsat_of_unsat_sub_elim
- \+ *def* sub_terms
- \+ *def* sub_subst
- \+ *def* is_diff
- \+ *def* sub_elim_core
- \+ *def* sub_fresh_index
- \+ *def* sub_elim

Created src/tactic/omega/prove_unsats.lean
- \+ *lemma* forall_mem_repeat_zero_eq_zero

Created src/tactic/omega/term.lean
- \+ *lemma* val_neg
- \+ *lemma* val_sub
- \+ *lemma* val_add
- \+ *lemma* val_mul
- \+ *lemma* val_div
- \+ *def* term
- \+ *def* val
- \+ *def* neg
- \+ *def* add
- \+ *def* sub
- \+ *def* mul
- \+ *def* div
- \+ *def* fresh_index
- \+ *def* terms.fresh_index

Created test/omega.lean




## [2019-04-16 21:38:18](https://github.com/leanprover-community/mathlib/commit/4b8106b)
fix(test/local_cache): make the trace text explicit and quiet ([#941](https://github.com/leanprover-community/mathlib/pull/941))
(by default)
#### Estimated changes
Modified test/local_cache.lean
- \+ *def* do_trace



## [2019-04-16 20:12:19](https://github.com/leanprover-community/mathlib/commit/7bbbee1)
feat(*): various additions to low-level files ([#904](https://github.com/leanprover-community/mathlib/pull/904))
* feat(*): various additions to low-level files
* fix(data/fin): add missing universe
#### Estimated changes
Modified src/algebra/order.lean
- \+ *def* lt_by_cases

Modified src/data/equiv/basic.lean
- \+ *lemma* subtype_congr_right_mk
- \+ *def* subtype_congr_right

Modified src/data/fin.lean
- \+ *def* {u}

Modified src/data/nat/basic.lean
- \+ *lemma* add_sub_cancel_right

Modified src/data/subtype.lean
- \+ *lemma* restrict_apply
- \+ *lemma* restrict_def
- \+ *lemma* restrict_injective
- \+ *lemma* map_injective
- \+/\- *theorem* val_injective
- \+ *theorem* coind_injective
- \+ *def* restrict
- \+ *def* coind

Modified src/logic/basic.lean
- \+ *lemma* congr_arg2

Modified src/logic/embedding.lean


Modified src/order/basic.lean
- \+ *lemma* trans_trichotomous_left
- \+ *lemma* trans_trichotomous_right
- \+ *def* unbounded
- \+ *def* bounded

Modified src/order/order_iso.lean
- \+ *lemma* injective_of_increasing

Modified src/set_theory/cofinality.lean




## [2019-04-16 18:10:16](https://github.com/leanprover-community/mathlib/commit/2294876)
feat(data/finset): powerset_len (subsets of a given size) ([#899](https://github.com/leanprover-community/mathlib/pull/899))
* feat(data/finset): powerset_len (subsets of a given size)
* fix build
#### Estimated changes
Modified src/algebra/char_p.lean


Modified src/data/complex/exponential.lean


Modified src/data/finset.lean
- \+ *theorem* mem_powerset_len
- \+ *theorem* powerset_len_mono
- \+ *theorem* card_powerset_len
- \+ *def* powerset_len

Modified src/data/list/basic.lean
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
- \+ *lemma* nodup_sublists_len
- \+ *theorem* append_sublist_append
- \+ *def* sublists_len_aux
- \+ *def* sublists_len

Modified src/data/multiset.lean
- \+ *theorem* powerset_len_aux_eq_map_coe
- \+ *theorem* mem_powerset_len_aux
- \+ *theorem* powerset_len_aux_zero
- \+ *theorem* powerset_len_aux_nil
- \+ *theorem* powerset_len_aux_cons
- \+ *theorem* powerset_len_aux_perm
- \+ *theorem* powerset_len_coe'
- \+ *theorem* powerset_len_coe
- \+ *theorem* powerset_len_zero_left
- \+ *theorem* powerset_len_zero_right
- \+ *theorem* powerset_len_cons
- \+ *theorem* mem_powerset_len
- \+ *theorem* card_powerset_len
- \+ *theorem* powerset_len_le_powerset
- \+ *theorem* powerset_len_mono
- \+ *theorem* nodup_powerset_len
- \+ *def* powerset_len_aux
- \+ *def* powerset_len

Modified src/data/nat/basic.lean
- \+ *lemma* choose_zero_right
- \+ *lemma* choose_zero_succ
- \+ *lemma* choose_succ_succ
- \+ *lemma* choose_eq_zero_of_lt
- \+ *lemma* choose_self
- \+ *lemma* choose_succ_self
- \+ *lemma* choose_one_right
- \+ *lemma* choose_pos
- \+ *lemma* succ_mul_choose_eq
- \+ *lemma* choose_mul_fact_mul_fact
- \+ *theorem* choose_eq_fact_div_fact
- \+ *theorem* fact_mul_fact_dvd_fact
- \+ *def* choose

Modified src/data/nat/choose.lean
- \- *lemma* choose_zero_right
- \- *lemma* choose_zero_succ
- \- *lemma* choose_succ_succ
- \- *lemma* choose_eq_zero_of_lt
- \- *lemma* choose_self
- \- *lemma* choose_succ_self
- \- *lemma* choose_one_right
- \- *lemma* choose_pos
- \- *lemma* succ_mul_choose_eq
- \- *lemma* choose_mul_fact_mul_fact
- \- *theorem* choose_eq_fact_div_fact
- \- *theorem* fact_mul_fact_dvd_fact
- \- *def* choose

Modified src/ring_theory/ideal_operations.lean




## [2019-04-16 16:32:52](https://github.com/leanprover-community/mathlib/commit/8985a43)
feat(data/set/intervals): some interval lemmas ([#942](https://github.com/leanprover-community/mathlib/pull/942))
* feat(data/set/intervals): a few more lemmas
* one-liners
#### Estimated changes
Modified src/data/set/intervals.lean
- \+ *lemma* left_mem_Ioo
- \+ *lemma* left_mem_Ico
- \+ *lemma* left_mem_Icc
- \+ *lemma* left_mem_Ioc
- \+ *lemma* right_mem_Ioo
- \+ *lemma* right_mem_Ico
- \+ *lemma* right_mem_Icc
- \+ *lemma* right_mem_Ioc
- \+ *lemma* Ioc_self
- \+ *lemma* Ioc_subset_Ioc
- \+ *lemma* Ioc_subset_Ioc_left
- \+ *lemma* Ioc_subset_Ioc_right



## [2019-04-16 07:19:32](https://github.com/leanprover-community/mathlib/commit/361e216)
feature(category_theory/instances/Top/open[_nhds]): category of open sets, and open neighbourhoods of a point (merge [#920](https://github.com/leanprover-community/mathlib/pull/920) first) ([#922](https://github.com/leanprover-community/mathlib/pull/922))
* rearrange Top
* oops, import from the future
* the categories of open sets and of open_nhds
* missing import
* restoring opens, adding headers
* Update src/category_theory/instances/Top/open_nhds.lean
Co-Authored-By: semorrison <scott@tqft.net>
* use full_subcategory_inclusion
#### Estimated changes
Created src/category_theory/instances/Top/adjunctions.lean
- \+ *def* adj₁
- \+ *def* adj₂

Created src/category_theory/instances/Top/basic.lean
- \+ *def* Top
- \+ *def* discrete
- \+ *def* trivial

Created src/category_theory/instances/Top/default.lean


Created src/category_theory/instances/Top/limits.lean
- \+ *def* limit
- \+ *def* limit_is_limit
- \+ *def* colimit
- \+ *def* colimit_is_colimit

Created src/category_theory/instances/Top/open_nhds.lean
- \+ *lemma* inclusion_obj
- \+ *lemma* map_id_obj'
- \+ *lemma* map_id_obj
- \+ *lemma* map_id_obj_unop
- \+ *lemma* op_map_id_obj
- \+ *lemma* inclusion_map_iso_hom
- \+ *lemma* inclusion_map_iso_inv
- \+ *def* open_nhds
- \+ *def* inclusion
- \+ *def* map
- \+ *def* inclusion_map_iso

Created src/category_theory/instances/Top/opens.lean
- \+ *lemma* map_id_obj'
- \+ *lemma* map_id_obj
- \+ *lemma* map_id_obj_unop
- \+ *lemma* op_map_id_obj
- \+ *lemma* map_id_hom_app
- \+ *lemma* map_id_inv_app
- \+ *lemma* map_comp_obj'
- \+ *lemma* map_comp_obj
- \+ *lemma* map_comp_obj_unop
- \+ *lemma* op_map_comp_obj
- \+ *lemma* map_comp_hom_app
- \+ *lemma* map_comp_inv_app
- \+ *lemma* map_iso_refl
- \+ *lemma* map_iso_hom_app
- \+ *lemma* map_iso_inv_app
- \+ *def* map
- \+ *def* map_id
- \+ *def* map_comp
- \+ *def* map_iso

Modified src/category_theory/instances/measurable_space.lean


Deleted src/category_theory/instances/topological_spaces.lean
- \- *lemma* map_id_obj
- \- *def* Top
- \- *def* limit
- \- *def* limit_is_limit
- \- *def* colimit
- \- *def* colimit_is_colimit
- \- *def* discrete
- \- *def* trivial
- \- *def* adj₁
- \- *def* adj₂
- \- *def* nbhd
- \- *def* nbhds
- \- *def* map
- \- *def* map_id
- \- *def* map_iso
- \- *def* map_iso_id



## [2019-04-15 19:41:40](https://github.com/leanprover-community/mathlib/commit/5f04e76)
feat(nat/basic): add some basic nat inequality lemmas ([#937](https://github.com/leanprover-community/mathlib/pull/937))
* feat(nat/basic): add some basic nat inequality lemmas, useful as specific cases of existing ring cases since uses less hypothesis
* feat(nat/basic): add some basic nat inequality lemmas, with convention fixes
* feat(nat/basic): add some basic nat inequality lemmas, with convention fixes
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* le_mul_of_pos_left
- \+ *lemma* le_mul_of_pos_right
- \+ *lemma* lt_of_div_lt_div



## [2019-04-15 19:09:47](https://github.com/leanprover-community/mathlib/commit/d06eb85)
feat(topology/algebra/continuous_functions): the ring of continuous functions ([#923](https://github.com/leanprover-community/mathlib/pull/923))
* feat(topology/algebra/continuous_functions): the ring of continuous functions
* filling in the hierarchy
* use to_additive
#### Estimated changes
Created src/topology/algebra/continuous_functions.lean




## [2019-04-14 19:26:36-04:00](https://github.com/leanprover-community/mathlib/commit/ca5d4c1)
feat(scripts): disable testing the install scripts in external PRs ([#936](https://github.com/leanprover-community/mathlib/pull/936))
#### Estimated changes
Modified .travis.yml




## [2019-04-14 15:16:28+01:00](https://github.com/leanprover-community/mathlib/commit/a1b7dcd)
fix(algebra/big_operators): change variables in finset.prod_map to remove spurious [comm_monoid β] ([#934](https://github.com/leanprover-community/mathlib/pull/934))
The old version involved maps α → β → γ and an instance [comm_monoid γ], but there was also a section variable [comm_monoid β].  In applications of this lemma it is not necessary, and not usually true, that β is a monoid.  Change the statement to involve maps α → γ → β so that we already have a monoid structure on the last variable and we do not make spurious assumptions about the second one.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* prod_map



## [2019-04-13 21:56:41+02:00](https://github.com/leanprover-community/mathlib/commit/f01934c)
docs(elan): remove reference to nightly Lean ([#928](https://github.com/leanprover-community/mathlib/pull/928))
* docs(elan): Remove reference to nightly Lean.
#### Estimated changes
Modified docs/elan.md




## [2019-04-13 19:13:56+01:00](https://github.com/leanprover-community/mathlib/commit/49c3a04)
fix(algebra.field): introduce division_ring_has_div' ([#852](https://github.com/leanprover-community/mathlib/pull/852))
* fix division_ring_has_div
* priority default
* comment
#### Estimated changes
Modified src/algebra/field.lean




## [2019-04-12 12:59:14+02:00](https://github.com/leanprover-community/mathlib/commit/3fe449e)
feat(algebra/free): free magma, semigroup, monoid ([#735](https://github.com/leanprover-community/mathlib/pull/735))
#### Estimated changes
Created src/algebra/free.lean
- \+ *lemma* lift_of
- \+ *lemma* lift_mul
- \+ *lemma* map_of
- \+ *lemma* map_mul
- \+ *lemma* map_pure
- \+ *lemma* map_mul'
- \+ *lemma* pure_bind
- \+ *lemma* mul_bind
- \+ *lemma* pure_seq
- \+ *lemma* mul_seq
- \+ *lemma* traverse_pure
- \+ *lemma* traverse_pure'
- \+ *lemma* traverse_mul
- \+ *lemma* traverse_mul'
- \+ *lemma* traverse_eq
- \+ *lemma* mul_map_seq
- \+ *lemma* lift_of_mul
- \+ *lemma* of_mul
- \+ *lemma* lift_one
- \+ *lemma* free_semigroup_free_magma_mul
- \+ *theorem* lift_unique
- \+ *theorem* of_mul_assoc
- \+ *theorem* of_mul_assoc_left
- \+ *theorem* of_mul_assoc_right
- \+ *theorem* of_mul
- \+ *def* lift
- \+ *def* map
- \+ *def* repr'
- \+ *def* length
- \+ *def* free_semigroup
- \+ *def* of
- \+ *def* lift'
- \+ *def* traverse'
- \+ *def* free_monoid
- \+ *def* free_semigroup_free_magma



## [2019-04-11 19:08:59](https://github.com/leanprover-community/mathlib/commit/be79f25)
refactor(data/int/basic): weaken hypotheses for int.induction_on ([#887](https://github.com/leanprover-community/mathlib/pull/887))
* refactor(data/int/basic): weaken hypotheses for int.induction_on
* fix build
* fix build
#### Estimated changes
Modified src/algebra/group_power.lean


Modified src/data/int/basic.lean




## [2019-04-11 14:11:00](https://github.com/leanprover-community/mathlib/commit/36f0c22)
feat(submonoid, subgroup, subring): is_ring_hom instances for set.inclusion ([#917](https://github.com/leanprover-community/mathlib/pull/917))
#### Estimated changes
Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid.lean


Modified src/ring_theory/subring.lean




## [2019-04-11 04:11:18-04:00](https://github.com/leanprover-community/mathlib/commit/c1e07a2)
fix(tactic/explode): more accurate may_be_proof ([#924](https://github.com/leanprover-community/mathlib/pull/924))
#### Estimated changes
Modified src/meta/expr.lean


Modified src/tactic/explode.lean




## [2019-04-11 00:50:17](https://github.com/leanprover-community/mathlib/commit/22fcb4e)
minor changes ([#921](https://github.com/leanprover-community/mathlib/pull/921))
#### Estimated changes
Modified src/category_theory/concrete_category.lean
- \+ *lemma* coe_id

Modified src/category_theory/eq_to_hom.lean
- \+ *lemma* eq_to_hom_op

Modified src/category_theory/equivalence.lean


Modified src/category_theory/functor_category.lean


Modified src/category_theory/natural_isomorphism.lean
- \+ *lemma* hom_inv_id_app
- \+ *lemma* inv_hom_id_app

Modified src/category_theory/opposites.lean
- \+ *lemma* unop_id_op
- \+ *lemma* op_id_unop



## [2019-04-10 17:49:27](https://github.com/leanprover-community/mathlib/commit/f5d43a9)
feat(analysis/normed_space/deriv): show that the differential is unique (2) ([#916](https://github.com/leanprover-community/mathlib/pull/916))
* Remove wrong simp attribute
* fix typo
* characterize convergence at_top in normed spaces
* copy some changes from [#829](https://github.com/leanprover-community/mathlib/pull/829)
* small elements in normed fields go to zero
* derivatives are unique
* remove unnecessary lemma
* update according to review
* remove another empty line
#### Estimated changes
Modified src/analysis/normed_space/deriv.lean
- \+ *lemma* fderiv_at_filter_unique
- \+ *theorem* fderiv_at_unique
- \+ *theorem* fderiv_at_within_open_unique

Modified src/analysis/specific_limits.lean
- \+ *lemma* tendsto_pow_at_top_nhds_0_of_lt_1_normed_field

Modified src/topology/basic.lean
- \+ *theorem* nhds_within_eq_of_open
- \- *theorem* nhs_within_eq_of_open

Modified src/topology/sequences.lean
- \+/\- *lemma* topological_space.seq_tendsto_iff



## [2019-04-10 17:14:40](https://github.com/leanprover-community/mathlib/commit/41014e5)
rename has_sum and is_sum to summable and has_sum ([#912](https://github.com/leanprover-community/mathlib/pull/912))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* summable_iff_vanishing_norm
- \+ *lemma* summable_of_norm_bounded
- \+ *lemma* summable_of_summable_norm
- \+/\- *lemma* norm_tsum_le_tsum_norm
- \- *lemma* has_sum_iff_vanishing_norm
- \- *lemma* has_sum_of_norm_bounded
- \- *lemma* has_sum_of_has_sum_norm

Modified src/analysis/specific_limits.lean
- \+ *lemma* summable_of_absolute_convergence_real
- \+ *lemma* has_sum_geometric
- \+ *lemma* has_sum_geometric_two
- \- *lemma* has_sum_of_absolute_convergence_real
- \- *lemma* is_sum_geometric
- \- *lemma* is_sum_geometric_two

Modified src/measure_theory/probability_mass_function.lean
- \+ *lemma* has_sum_coe_one
- \+ *lemma* summable_coe
- \+/\- *lemma* tsum_coe
- \- *lemma* is_sum_coe_one
- \- *lemma* has_sum_coe
- \+/\- *def* {u}
- \+/\- *def* pure

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum_tsum
- \+ *lemma* summable_spec
- \+/\- *lemma* has_sum_zero
- \+ *lemma* summable_zero
- \+/\- *lemma* has_sum_add
- \+ *lemma* summable_add
- \+/\- *lemma* has_sum_sum
- \+ *lemma* summable_sum
- \+/\- *lemma* has_sum_sum_of_ne_finset_zero
- \+ *lemma* summable_sum_of_ne_finset_zero
- \+ *lemma* has_sum_ite_eq
- \+ *lemma* has_sum_of_iso
- \+ *lemma* has_sum_iff_has_sum_of_iso
- \+ *lemma* has_sum_hom
- \+ *lemma* tendsto_sum_nat_of_has_sum
- \+/\- *lemma* has_sum_sigma
- \+ *lemma* summable_sigma
- \+ *lemma* has_sum_of_has_sum
- \+ *lemma* has_sum_iff_has_sum
- \+ *lemma* has_sum_of_has_sum_ne_zero
- \+ *lemma* has_sum_iff_has_sum_of_ne_zero
- \+ *lemma* summable_iff_summable_ne_zero
- \+ *lemma* has_sum_iff_has_sum_of_ne_zero_bij
- \+ *lemma* summable_iff_summable_ne_zero_bij
- \+ *lemma* has_sum_unique
- \+ *lemma* tsum_eq_has_sum
- \+ *lemma* has_sum_iff_of_summable
- \+/\- *lemma* tsum_zero
- \+/\- *lemma* tsum_add
- \+/\- *lemma* tsum_sum
- \+ *lemma* tsum_eq_tsum_of_has_sum_iff_has_sum
- \+/\- *lemma* has_sum_neg
- \+ *lemma* summable_neg
- \+/\- *lemma* has_sum_sub
- \+ *lemma* summable_sub
- \+/\- *lemma* tsum_neg
- \+/\- *lemma* tsum_sub
- \+/\- *lemma* has_sum_mul_left
- \+/\- *lemma* has_sum_mul_right
- \+ *lemma* summable_mul_left
- \+ *lemma* summable_mul_right
- \+/\- *lemma* tsum_mul_left
- \+/\- *lemma* tsum_mul_right
- \+ *lemma* has_sum_le
- \+ *lemma* has_sum_le_inj
- \+/\- *lemma* tsum_le_tsum
- \+ *lemma* summable_iff_cauchy
- \+ *lemma* summable_iff_vanishing
- \+ *lemma* summable_of_summable_of_sub
- \+ *lemma* summable_comp_of_summable_of_injective
- \+ *lemma* cauchy_seq_of_summable_dist
- \- *lemma* is_sum_tsum
- \- *lemma* has_sum_spec
- \- *lemma* is_sum_zero
- \- *lemma* is_sum_add
- \- *lemma* is_sum_sum
- \- *lemma* is_sum_sum_of_ne_finset_zero
- \- *lemma* is_sum_ite_eq
- \- *lemma* is_sum_of_iso
- \- *lemma* is_sum_iff_is_sum_of_iso
- \- *lemma* is_sum_hom
- \- *lemma* tendsto_sum_nat_of_is_sum
- \- *lemma* is_sum_sigma
- \- *lemma* is_sum_of_is_sum
- \- *lemma* is_sum_iff_is_sum
- \- *lemma* is_sum_of_is_sum_ne_zero
- \- *lemma* is_sum_iff_is_sum_of_ne_zero
- \- *lemma* has_sum_iff_has_sum_ne_zero
- \- *lemma* is_sum_iff_is_sum_of_ne_zero_bij
- \- *lemma* has_sum_iff_has_sum_ne_zero_bij
- \- *lemma* is_sum_unique
- \- *lemma* tsum_eq_is_sum
- \- *lemma* is_sum_iff_of_has_sum
- \- *lemma* tsum_eq_tsum_of_is_sum_iff_is_sum
- \- *lemma* is_sum_neg
- \- *lemma* is_sum_sub
- \- *lemma* is_sum_mul_left
- \- *lemma* is_sum_mul_right
- \- *lemma* is_sum_le
- \- *lemma* is_sum_le_inj
- \- *lemma* has_sum_iff_cauchy
- \- *lemma* has_sum_iff_vanishing
- \- *lemma* has_sum_of_has_sum_of_sub
- \- *lemma* has_sum_comp_of_has_sum_of_injective
- \- *lemma* cauchy_seq_of_has_sum_dist
- \+/\- *def* has_sum
- \+ *def* summable
- \+/\- *def* tsum
- \- *def* is_sum

Modified src/topology/instances/ennreal.lean
- \+ *lemma* has_sum_iff_tendsto_nat
- \+ *lemma* exists_le_has_sum_of_le
- \+ *lemma* summable_of_le
- \+ *lemma* summable_of_nonneg_of_le
- \+ *lemma* has_sum_iff_tendsto_nat_of_nonneg
- \- *lemma* is_sum_iff_tendsto_nat
- \- *lemma* exists_le_is_sum_of_le
- \- *lemma* has_sum_of_le
- \- *lemma* has_sum_of_nonneg_of_le
- \- *lemma* is_sum_iff_tendsto_nat_of_nonneg

Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* has_sum_coe
- \+ *lemma* summable_coe
- \+/\- *lemma* tsum_coe
- \- *lemma* is_sum_coe



## [2019-04-10 16:24:03+01:00](https://github.com/leanprover-community/mathlib/commit/c4b65da)
fix(mergify): merge if either push or pr build passes. ([#918](https://github.com/leanprover-community/mathlib/pull/918))
* fix(mergify): merge if either push or pr build passes.
* Update .mergify.yml
* Update .mergify.yml
#### Estimated changes
Modified .mergify.yml




## [2019-04-10 09:45:01+01:00](https://github.com/leanprover-community/mathlib/commit/49ccc9f)
refactor(order/lexicographic): use prod.lex and psigma.lex ([#914](https://github.com/leanprover-community/mathlib/pull/914))
* refactor(order/lexicographic): use prod.lex and psigma.lex
* update
#### Estimated changes
Modified src/order/lexicographic.lean




## [2019-04-10 07:17:03](https://github.com/leanprover-community/mathlib/commit/8992472)
fix(category_theory): make the `nat_trans` arrow `⟹` a synonym for the `hom` arrow ([#907](https://github.com/leanprover-community/mathlib/pull/907))
* removing the nat_trans and vcomp notations; use \hom and \gg
* a simpler proposal
* getting rid of vcomp
* fix
* update notations in documentation
* typo in docs
#### Estimated changes
Modified docs/theories/category_theory.md


Modified src/category_theory/adjunction.lean


Modified src/category_theory/comma.lean
- \+/\- *def* nat_trans
- \+/\- *def* map_left
- \+/\- *def* map_left_comp
- \+/\- *def* map_right
- \+/\- *def* map_right_comp

Modified src/category_theory/discrete_category.lean


Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/functor_category.lean
- \+/\- *lemma* id_app
- \+/\- *lemma* app_naturality
- \+/\- *lemma* naturality_app

Modified src/category_theory/limits/cones.lean
- \+/\- *lemma* cocones_obj

Modified src/category_theory/limits/limits.lean
- \+/\- *def* hom_iso

Modified src/category_theory/limits/types.lean
- \+/\- *lemma* types_limit_map
- \+/\- *lemma* types_colimit_map

Modified src/category_theory/natural_isomorphism.lean
- \- *lemma* hom_vcomp_inv
- \- *lemma* inv_vcomp_hom

Modified src/category_theory/natural_transformation.lean
- \+/\- *lemma* ext
- \+/\- *lemma* congr_app
- \+/\- *lemma* vcomp_app
- \+/\- *lemma* vcomp_assoc
- \+/\- *lemma* hcomp_app
- \+/\- *lemma* exchange
- \+/\- *def* vcomp
- \+/\- *def* hcomp

Modified src/category_theory/products.lean
- \+/\- *lemma* prod_app
- \+/\- *def* prod

Modified src/category_theory/types.lean
- \+ *lemma* comp
- \- *lemma* vcomp

Modified src/category_theory/whiskering.lean
- \+/\- *lemma* whiskering_left_obj_map
- \+/\- *lemma* whiskering_left_map_app_app
- \+/\- *lemma* whisker_left.app
- \+/\- *lemma* whiskering_right_obj_map
- \+/\- *lemma* whiskering_right_map_app_app
- \+/\- *lemma* whisker_right.app
- \+ *lemma* whisker_left_comp
- \+ *lemma* whisker_right_comp
- \+/\- *lemma* whisker_left_twice
- \+/\- *lemma* whisker_right_twice
- \+/\- *lemma* whisker_right_left
- \- *lemma* whisker_left_vcomp
- \- *lemma* whisker_right_vcomp
- \+/\- *def* whisker_left
- \+/\- *def* whisker_right

Modified src/category_theory/yoneda.lean
- \+/\- *def* yoneda_sections
- \+/\- *def* yoneda_sections_small



## [2019-04-10 06:48:16](https://github.com/leanprover-community/mathlib/commit/f04535d)
feat(category_theory): iso_whisker_(left|right) ([#908](https://github.com/leanprover-community/mathlib/pull/908))
* feat(category_theory): iso_whisker_(left|right)
* oops, use old notation for now
* update after merge
#### Estimated changes
Modified src/category_theory/whiskering.lean
- \+ *lemma* iso_whisker_left_hom
- \+ *lemma* iso_whisker_left_inv
- \+ *lemma* iso_whisker_right_hom
- \+ *lemma* iso_whisker_right_inv
- \+ *def* iso_whisker_left
- \+ *def* iso_whisker_right



## [2019-04-10 02:08:58](https://github.com/leanprover-community/mathlib/commit/86bd577)
refactor(algebra/group): is_monoid_hom extends is_mul_hom  ([#915](https://github.com/leanprover-community/mathlib/pull/915))
* refactor(algebra/group): is_monoid_hom extends is_mul_hom
* Fix build
#### Estimated changes
Modified src/algebra/group.lean
- \+ *lemma* map_mul
- \+ *lemma* map_add

Modified src/algebra/group_power.lean


Modified src/algebra/module.lean


Modified src/algebra/pi_instances.lean


Modified src/algebra/punit_instances.lean


Modified src/analysis/normed_space/basic.lean


Modified src/category/fold.lean


Modified src/data/dfinsupp.lean


Modified src/data/finsupp.lean


Modified src/data/matrix.lean


Modified src/data/multiset.lean


Modified src/data/nat/cast.lean


Modified src/data/polynomial.lean




## [2019-04-10 00:40:05](https://github.com/leanprover-community/mathlib/commit/f1683a9)
feat(data/set/basic): inclusion map ([#906](https://github.com/leanprover-community/mathlib/pull/906))
* feat(data/set/basic): inclusion map
* add continuous_inclusion
* minor style change
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* inclusion_self
- \+ *lemma* inclusion_inclusion
- \+ *lemma* inclusion_injective
- \+ *def* inclusion

Modified src/topology/constructions.lean
- \+ *lemma* continuous_inclusion



## [2019-04-10 00:12:57](https://github.com/leanprover-community/mathlib/commit/96d748e)
refactor(category_theory): rename `functor.on_iso` to `functor.map_iso` ([#893](https://github.com/leanprover-community/mathlib/pull/893))
* feat(category_theory): functor.map_nat_iso
* define `functor.map_nat_iso`, and relate to whiskering
* rename `functor.on_iso` to `functor.map_iso`
* add some missing lemmas about whiskering
* some more missing whiskering lemmas, while we're at it
* removing map_nat_iso
#### Estimated changes
Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/isomorphism.lean
- \+ *lemma* symm_mk
- \+ *lemma* trans_mk
- \+ *lemma* map_iso_hom
- \+ *lemma* map_iso_inv
- \- *lemma* on_iso_hom
- \- *lemma* on_iso_inv
- \+ *def* map_iso
- \- *def* on_iso

Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/category_theory/whiskering.lean
- \+ *lemma* whiskering_left_obj_obj
- \+ *lemma* whiskering_left_obj_map
- \+ *lemma* whiskering_left_map_app_app
- \+ *lemma* whiskering_right_obj_obj
- \+ *lemma* whiskering_right_obj_map
- \+ *lemma* whiskering_right_map_app_app
- \+ *lemma* whisker_left_id'
- \+ *lemma* whisker_right_id'



## [2019-04-09 22:44:04](https://github.com/leanprover-community/mathlib/commit/d692499)
reorganising category_theory/instances/rings.lean ([#909](https://github.com/leanprover-community/mathlib/pull/909))
#### Estimated changes
Created src/category_theory/instances/CommRing/adjunctions.lean
- \+ *lemma* polynomial_ring_obj_α
- \+ *lemma* polynomial_ring_map_val

Renamed src/category_theory/instances/rings.lean to src/category_theory/instances/CommRing/basic.lean
- \- *lemma* polynomial_obj_α
- \- *lemma* polynomial_map_val

Created src/category_theory/instances/CommRing/default.lean




## [2019-04-09 19:46:08](https://github.com/leanprover-community/mathlib/commit/4494001)
feat(field_theory/subfield): subfields are fields ([#888](https://github.com/leanprover-community/mathlib/pull/888))
* feat(field_theory/subfield): subfield are fields
* Update subfield.lean
#### Estimated changes
Modified src/field_theory/subfield.lean




## [2019-04-09 13:38:26-04:00](https://github.com/leanprover-community/mathlib/commit/5c4f5f2)
chore(build): allow PRs from separate repos to test deployment scripts
#### Estimated changes
Modified .travis.yml


Modified appveyor.yml




## [2019-04-09 10:16:41-04:00](https://github.com/leanprover-community/mathlib/commit/c2d79f8)
fix(mergify): require travis "push" check to push ([#913](https://github.com/leanprover-community/mathlib/pull/913))
This hopefully fixes an error where mergify does not merge a PR is the "pr" build succeeds before the "push" build. In these situations mergify does not merge, because the branch protection settings require both builds to pass.
Unfortunately, there doesn't seem to be an option to change the branch protection settings to only require the "pr" build to pass
#### Estimated changes
Modified .mergify.yml




## [2019-04-09 13:50:54+01:00](https://github.com/leanprover-community/mathlib/commit/66a86ff)
refactor(*): rename is_group_hom.mul to map_mul ([#911](https://github.com/leanprover-community/mathlib/pull/911))
* refactor(*): rename is_group_hom.mul to map_mul
* Fix splits_mul
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* is_group_hom.map_multiset_prod
- \- *lemma* is_group_hom.multiset_prod
- \+ *theorem* is_group_hom.map_prod
- \+ *theorem* is_group_anti_hom.map_prod
- \- *theorem* is_group_hom.prod
- \- *theorem* is_group_anti_hom.prod

Modified src/algebra/direct_sum.lean


Modified src/algebra/group.lean
- \+ *lemma* is_group_hom.mul
- \+ *lemma* is_group_hom.inv
- \+ *lemma* map_sub
- \+ *lemma* is_add_group_hom.sub
- \- *lemma* is_group_hom_mul
- \- *lemma* is_group_hom_inv
- \- *lemma* sub
- \- *lemma* is_add_group_hom_sub
- \+ *theorem* map_one
- \+ *theorem* map_inv
- \- *theorem* one
- \- *theorem* inv

Modified src/algebra/group_power.lean
- \+ *theorem* map_pow
- \+ *theorem* map_gpow
- \+ *theorem* map_smul
- \+ *theorem* map_gsmul
- \+ *theorem* is_add_group_hom.gsmul
- \- *theorem* pow
- \- *theorem* gpow
- \- *theorem* smul
- \- *theorem* gsmul
- \- *theorem* is_add_group_hom_gsmul

Modified src/analysis/complex/exponential.lean
- \+/\- *lemma* coe_gsmul

Modified src/field_theory/splitting_field.lean


Modified src/group_theory/abelianization.lean


Modified src/group_theory/free_abelian_group.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/group_action.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/quotient_group.lean


Modified src/group_theory/subgroup.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/ring_theory/localization.lean


Modified src/topology/algebra/group_completion.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/algebra/uniform_ring.lean




## [2019-04-09 04:27:55](https://github.com/leanprover-community/mathlib/commit/eb024dc)
feat(order/lexicographic): lexicographic pre/partial/linear orders ([#820](https://github.com/leanprover-community/mathlib/pull/820))
* remove prod.(*)order instances
* feat(order/lexicographic): lexicographic pre/partial/linear orders
* add lex_decidable_linear_order
* identical constructions for dependent pairs
* cleaning up
* Update lexicographic.lean
forgotten `instance`
* restore product instances, and add lex type synonym for lexicographic instances
* proofs in progress
* * define lt
* prove lt_iff_le_not_le
* refactoring
#### Estimated changes
Modified src/order/basic.lean


Created src/order/lexicographic.lean
- \+ *def* lex



## [2019-04-08 22:25:36+01:00](https://github.com/leanprover-community/mathlib/commit/29507a4)
feat(group_theory/subgroup): subtype.add_comm_group ([#903](https://github.com/leanprover-community/mathlib/pull/903))
#### Estimated changes
Modified src/group_theory/subgroup.lean




## [2019-04-08 17:11:21](https://github.com/leanprover-community/mathlib/commit/ec51b6e)
feat(category_theory/colimits): missing simp lemmas ([#894](https://github.com/leanprover-community/mathlib/pull/894))
#### Estimated changes
Modified src/category_theory/limits/limits.lean
- \+ *lemma* colimit.ι_desc_assoc
- \+ *lemma* colimit.ι_pre_assoc
- \+ *lemma* colimit.ι_post_assoc
- \+ *lemma* colim.ι_map_assoc



## [2019-04-08 17:49:51+02:00](https://github.com/leanprover-community/mathlib/commit/6d2cf4a)
fix(doc/extra/tactic_writing): rename mul_left ([#902](https://github.com/leanprover-community/mathlib/pull/902)) [ci skip]
*  fix(doc/extra/tactic_writing): rename mul_left
* one more fix
#### Estimated changes
Modified docs/extras/tactic_writing.md




## [2019-04-08 12:50:22+02:00](https://github.com/leanprover-community/mathlib/commit/5f1329a)
feat(linear_algebra/dual): add dual vector spaces ([#881](https://github.com/leanprover-community/mathlib/pull/881))
* feat(linear_algebra/dual): add dual vector spaces
Define dual modules and vector spaces and prove the basic theorems: the dual basis isomorphism and
evaluation isomorphism in the finite dimensional case, and the corresponding (injectivity)
statements in the general case. A variant of `linear_map.ker_eq_bot` and the "inverse" of
`is_basis.repr_total` are included.
Universe issues make an adaptation of `linear_equiv.dim_eq` necessary.
* style(linear_algebra/dual): adapt to remarks from PR dsicussion
* style(linear_algebra/dual): reformat proof of `ker_eq_bot'`
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *theorem* ker_eq_bot'

Modified src/linear_algebra/basis.lean
- \+ *lemma* is_basis.repr_total

Modified src/linear_algebra/dimension.lean
- \+ *lemma* exists_is_basis_fintype
- \+ *theorem* linear_equiv.dim_eq_lift

Created src/linear_algebra/dual.lean
- \+ *lemma* eval_apply
- \+ *lemma* to_dual_apply
- \+ *lemma* coord_fun_eq_repr
- \+ *lemma* to_dual_swap_eq_to_dual
- \+ *lemma* to_dual_eq_repr
- \+ *lemma* to_dual_inj
- \+ *lemma* to_dual_to_dual
- \+ *lemma* eval_range
- \+ *theorem* to_dual_ker
- \+ *theorem* to_dual_range
- \+ *theorem* dual_lin_independent
- \+ *theorem* dual_basis_is_basis
- \+ *theorem* dual_dim_eq
- \+ *theorem* eval_ker
- \+ *def* dual
- \+ *def* eval
- \+ *def* to_dual
- \+ *def* to_dual_flip
- \+ *def* eval_lc_at
- \+ *def* coord_fun
- \+ *def* dual_basis
- \+ *def* to_dual_equiv
- \+ *def* eval_equiv



## [2019-04-08 05:21:27](https://github.com/leanprover-community/mathlib/commit/10490ea)
feat(analysis/complex/polynomial): fundamental theorem of algebra ([#851](https://github.com/leanprover-community/mathlib/pull/851))
* feat(data/complex/polynomia): fundamental theorem of algebra
* fix build
* add docstring
* add comment giving link to proof used.
* spag
* move to analysis/complex
* fix data/real/pi
* Update src/analysis/complex/polynomial.lean
Co-Authored-By: ChrisHughes24 <33847686+ChrisHughes24@users.noreply.github.com>
* make Reid's suggested changes
* make Reid's suggested changes
#### Estimated changes
Renamed src/analysis/exponential.lean to src/analysis/complex/exponential.lean


Created src/analysis/complex/polynomial.lean
- \+ *lemma* exists_forall_abs_polynomial_eval_le
- \+ *lemma* exists_root

Modified src/data/real/pi.lean


Modified src/topology/instances/polynomial.lean
- \+ *lemma* polynomial.tendsto_infinity



## [2019-04-07 23:05:06-04:00](https://github.com/leanprover-community/mathlib/commit/4fecb10)
feat(topology/gromov_hausdorff): the Gromov-Hausdorff space ([#883](https://github.com/leanprover-community/mathlib/pull/883))
#### Estimated changes
Created src/topology/metric_space/gromov_hausdorff.lean
- \+ *lemma* eq_to_GH_space_iff
- \+ *lemma* eq_to_GH_space
- \+ *lemma* GH_space.to_GH_space_rep
- \+ *lemma* to_GH_space_eq_to_GH_space_iff_isometric
- \+ *lemma* dist_GH_dist
- \+ *lemma* Hausdorff_dist_optimal
- \+ *lemma* to_GH_space_lipschitz
- \+ *lemma* to_GH_space_continuous
- \+ *lemma* second_countable
- \+ *lemma* totally_bounded
- \+ *theorem* GH_dist_le_Hausdorff_dist
- \+ *theorem* GH_dist_eq_Hausdorff_dist
- \+ *theorem* GH_dist_le_nonempty_compacts_dist
- \+ *theorem* GH_dist_le_of_approx_subsets
- \+ *def* GH_dist
- \+ *def* aux_gluing

Created src/topology/metric_space/gromov_hausdorff_realized.lean
- \+ *lemma* candidates_b_of_candidates_mem
- \+ *lemma* candidates_b_dist_mem_candidates_b
- \+ *lemma* HD_below_aux1
- \+ *lemma* HD_below_aux2
- \+ *lemma* HD_candidates_b_dist_le
- \+ *lemma* isometry_optimal_GH_injl
- \+ *lemma* isometry_optimal_GH_injr
- \+ *lemma* Hausdorff_dist_optimal_le_HD
- \+ *def* candidates
- \+ *def* candidates_b_of_candidates
- \+ *def* candidates_b_dist
- \+ *def* HD
- \+ *def* premetric_optimal_GH_dist
- \+ *def* optimal_GH_injl
- \+ *def* optimal_GH_injr

Modified src/topology/metric_space/isometry.lean
- \+ *lemma* embedding_of_subset_coe
- \+ *lemma* embedding_of_subset_dist_le
- \+ *lemma* embedding_of_subset_isometry
- \+ *lemma* Kuratowski_embedding_isometry
- \+ *theorem* exists_isometric_embedding
- \+ *def* ℓ_infty_ℝ
- \+ *def* embedding_of_subset
- \+ *def* Kuratowski_embedding
- \+ *def* nonempty_compacts.Kuratowski_embedding



## [2019-04-08 02:41:50](https://github.com/leanprover-community/mathlib/commit/5d81ab1)
trying to work out what was wrong with catching signals ([#898](https://github.com/leanprover-community/mathlib/pull/898))
#### Estimated changes
Modified scripts/cache-olean.py


Modified scripts/setup-dev-scripts.sh


Modified scripts/update-mathlib.py




## [2019-04-08 01:59:38](https://github.com/leanprover-community/mathlib/commit/0a49030)
fix(category_theory): turn `has_limits` classes into structures ([#896](https://github.com/leanprover-community/mathlib/pull/896))
* fix(category_theory): turn `has_limits` classes into structures
* fixing all the other pi-type typclasses
* oops
#### Estimated changes
Modified src/category_theory/adjunction.lean


Modified src/category_theory/instances/topological_spaces.lean


Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/limits.lean
- \- *def* has_limits_of_shape
- \- *def* has_limits
- \- *def* has_colimits_of_shape
- \- *def* has_colimits

Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/preserves.lean
- \- *def* preserves_limits_of_shape
- \- *def* preserves_colimits_of_shape
- \- *def* preserves_limits
- \- *def* preserves_colimits
- \- *def* reflects_limits_of_shape
- \- *def* reflects_colimits_of_shape
- \- *def* reflects_limits
- \- *def* reflects_colimits

Modified src/category_theory/limits/types.lean




## [2019-04-07 19:36:21+02:00](https://github.com/leanprover-community/mathlib/commit/483a6c2)
feat(data/list/min_max): add minimum ([#892](https://github.com/leanprover-community/mathlib/pull/892))
#### Estimated changes
Modified src/data/list/min_max.lean
- \+ *theorem* le_of_foldr_min
- \+ *theorem* le_of_foldl_min
- \+ *theorem* mem_foldr_min
- \+ *theorem* mem_foldl_min
- \+ *theorem* mem_minimum_aux
- \+ *theorem* mem_minimum
- \+ *theorem* le_minimum_aux_of_mem
- \+ *theorem* le_minimum_of_mem
- \+ *def* minimum
- \+ *def* minimum_aux
- \+ *def* minimum_singleton
- \+ *def* minimum_aux_cons
- \+ *def* minimum_cons



## [2019-04-07 16:29:19](https://github.com/leanprover-community/mathlib/commit/891c050)
feat(subgroup, subring, subfield): directed Unions of subrings are subrings ([#889](https://github.com/leanprover-community/mathlib/pull/889))
#### Estimated changes
Modified src/field_theory/subfield.lean
- \+ *lemma* is_subfield_Union_of_directed

Modified src/group_theory/subgroup.lean
- \+ *lemma* is_subgroup_Union_of_directed

Modified src/group_theory/submonoid.lean
- \+ *lemma* is_submonoid_Union_of_directed
- \+ *lemma* is_add_submonoid_Union_of_directed

Modified src/ring_theory/subring.lean
- \+ *lemma* is_subring_Union_of_directed



## [2019-04-07 10:29:26+01:00](https://github.com/leanprover-community/mathlib/commit/bd524fc)
feat(field_theory/subfield): is_subfield instances ([#891](https://github.com/leanprover-community/mathlib/pull/891))
#### Estimated changes
Modified src/field_theory/subfield.lean


Modified src/group_theory/submonoid.lean
- \+ *lemma* image.is_submonoid

Modified src/ring_theory/subring.lean




## [2019-04-07 01:34:16](https://github.com/leanprover-community/mathlib/commit/7e70ebd)
feat(data/nat/basic): b = c if b - a = c - a ([#862](https://github.com/leanprover-community/mathlib/pull/862))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *theorem* sub_cancel



## [2019-04-06 21:04:01-04:00](https://github.com/leanprover-community/mathlib/commit/3000f32)
fix(build): external PRs can't use GitHub credentials
#### Estimated changes
Modified .travis.yml




## [2019-04-07 00:21:11+01:00](https://github.com/leanprover-community/mathlib/commit/e4d3ca3)
fix(analysis/normed_space/bounded_linear_maps): fix build ([#895](https://github.com/leanprover-community/mathlib/pull/895))
#### Estimated changes
Modified src/analysis/normed_space/bounded_linear_maps.lean




## [2019-04-06 16:44:31-04:00](https://github.com/leanprover-community/mathlib/commit/31ff5c5)
refactor(analysis/normed_space/bounded_linear_maps): nondiscrete normed field
#### Estimated changes
Modified src/algebra/module.lean
- \+ *lemma* map_zero
- \+ *lemma* map_add
- \+ *lemma* map_neg
- \+ *lemma* map_sub

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_pos_iff
- \+ *lemma* norm_fpow
- \+ *lemma* exists_one_lt_norm
- \+ *lemma* exists_norm_lt_one
- \+ *lemma* rescale_to_shell

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \- *lemma* bounded_continuous_linear_map
- \+ *theorem* is_linear_map.bounded_of_continuous_at

Modified src/data/padics/padic_numbers.lean




## [2019-04-06 16:20:01-04:00](https://github.com/leanprover-community/mathlib/commit/53e7d72)
fix(appveyor): build every commit
#### Estimated changes
Modified appveyor.yml




## [2019-04-06 16:14:28-04:00](https://github.com/leanprover-community/mathlib/commit/ae8a1fb)
refactor(analysis/normed_space/bounded_linear_maps): nondiscrete normed field
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* bounded_linear_maps.map_zero
- \+ *lemma* bounded_linear_maps.coe_zero
- \+ *lemma* bounded_linear_maps.smul_coe
- \+ *lemma* bounded_linear_maps.zero_smul
- \+ *lemma* bounded_linear_maps.one_smul
- \+/\- *lemma* exists_bound
- \+ *lemma* bdd_above_range_norm_image_div_norm
- \+/\- *lemma* operator_norm_bounded_by
- \+ *lemma* operator_norm_homogeneous_le
- \- *lemma* exists_bound'
- \- *lemma* norm_of_unit_ball_bdd_above
- \- *lemma* zero_in_im_ball
- \- *lemma* bounded_by_operator_norm_on_unit_vector
- \- *lemma* bounded_by_operator_norm_on_unit_ball
- \+/\- *theorem* operator_norm_triangle
- \+/\- *theorem* operator_norm_homogeneous
- \+ *def* to_linear_map



## [2019-04-06 15:56:00-04:00](https://github.com/leanprover-community/mathlib/commit/8831e0a)
chore(mergify): require the AppVeyor build to succeed
#### Estimated changes
Modified .mergify.yml




## [2019-04-06 15:08:22-04:00](https://github.com/leanprover-community/mathlib/commit/8fa071f)
fix(scripts): not all files were deployed through the curl command ([#879](https://github.com/leanprover-community/mathlib/pull/879))
#### Estimated changes
Modified .travis.yml


Modified README.md


Created appveyor.yml


Modified scripts/remote-install-update-mathlib.sh


Modified scripts/setup-dev-scripts.sh


Modified scripts/update-mathlib.py




## [2019-04-06 18:45:57](https://github.com/leanprover-community/mathlib/commit/8d45ccb)
feat(category_theory/bifunctor): simp lemmas ([#867](https://github.com/leanprover-community/mathlib/pull/867))
* feat(category_theory/bifunctor): simp lemmas
* remove need for @, thanks Kenny and Chris!
#### Estimated changes
Created src/category_theory/bifunctor.lean
- \+ *lemma* map_id
- \+ *lemma* map_id_comp
- \+ *lemma* map_comp_id
- \+ *lemma* diagonal
- \+ *lemma* diagonal'



## [2019-04-06 16:52:11](https://github.com/leanprover-community/mathlib/commit/3360f98)
more general hypotheses for integer induction ([#885](https://github.com/leanprover-community/mathlib/pull/885))
#### Estimated changes
Modified src/data/int/basic.lean




## [2019-04-06 10:59:07-04:00](https://github.com/leanprover-community/mathlib/commit/d8a2bc5)
feat(algebra/opposites): opposites of operators ([#538](https://github.com/leanprover-community/mathlib/pull/538))
#### Estimated changes
Created src/algebra/opposites.lean
- \+ *theorem* op_inj
- \+ *theorem* unop_inj
- \+ *theorem* op_unop
- \+ *theorem* unop_op
- \+ *def* opposite
- \+ *def* op
- \+ *def* unop



## [2019-04-05 14:05:35-04:00](https://github.com/leanprover-community/mathlib/commit/e0e231d)
fix(build): match build names
#### Estimated changes
Modified .travis.yml




## [2019-04-05 13:44:34-04:00](https://github.com/leanprover-community/mathlib/commit/d0f8607)
fix(scripts): protect `leanpkg test` against timeouts
#### Estimated changes
Modified .travis.yml




## [2019-04-05 11:21:07-04:00](https://github.com/leanprover-community/mathlib/commit/e809df6)
fix(scripts): Mac Python's test support doesn't work on Travis
#### Estimated changes
Modified .travis.yml




## [2019-04-05 11:07:11-04:00](https://github.com/leanprover-community/mathlib/commit/d9ec8a8)
fix(scripts): not all files were deployed through the curl command
#### Estimated changes
Modified .travis.yml


Modified README.md


Modified scripts/cache-olean.py


Created scripts/leanpkg-example.toml


Modified scripts/remote-install-update-mathlib.sh


Modified scripts/setup-dev-scripts.sh


Modified scripts/update-mathlib.py




## [2019-04-05 14:37:35](https://github.com/leanprover-community/mathlib/commit/78a08eb)
feat(data/mllist): monadic lazy lists ([#865](https://github.com/leanprover-community/mathlib/pull/865))
* feat(data/mllist): monadic lazy lists
* oops, fix header
* shove into tactic namespace
* make mllist into a monad ([#880](https://github.com/leanprover-community/mathlib/pull/880))
* make mllist into a monad
* looks good. add `take`, and some tests
* update authors
* cleanup test
#### Estimated changes
Created src/data/mllist.lean


Created test/mllist.lean
- \+ *def* S
- \+ *def* append
- \+ *def* F



## [2019-04-05 06:30:13](https://github.com/leanprover-community/mathlib/commit/44d1c7a)
feat(list.split_on): [1,1,2,3,2,4,4].split_on 2 = [[1,1],[3],[4,4]] ([#866](https://github.com/leanprover-community/mathlib/pull/866))
#### Estimated changes
Modified src/data/list/defs.lean
- \+ *def* split_on_p_aux
- \+ *def* split_on_p
- \+ *def* split_on



## [2019-04-05 06:11:40](https://github.com/leanprover-community/mathlib/commit/901bdbf)
feat(data/list/min_max): minimum and maximum over list ([#884](https://github.com/leanprover-community/mathlib/pull/884))
* feat(data/list/min_max): minimum and maximum over list
* Update min_max.lean
* replace semicolons
#### Estimated changes
Created src/data/list/min_max.lean
- \+ *theorem* le_of_foldr_max
- \+ *theorem* le_of_foldl_max
- \+ *theorem* mem_foldr_max
- \+ *theorem* mem_foldl_max
- \+ *theorem* mem_maximum_aux
- \+ *theorem* mem_maximum
- \+ *theorem* le_maximum_aux_of_mem
- \+ *theorem* le_maximum_of_mem
- \+ *def* maximum
- \+ *def* maximum_aux
- \+ *def* maximum_singleton
- \+ *def* maximum_aux_cons
- \+ *def* maximum_cons



## [2019-04-05 04:01:15](https://github.com/leanprover-community/mathlib/commit/858d111)
feat(data/matrix): more basic matrix lemmas ([#873](https://github.com/leanprover-community/mathlib/pull/873))
* feat(data/matrix): more basic matrix lemmas
* feat(data/matrix): transpose_add
#### Estimated changes
Modified src/data/matrix.lean
- \+ *lemma* mul_smul
- \+ *lemma* smul_mul
- \+ *lemma* transpose_transpose
- \+ *lemma* transpose_zero
- \+ *lemma* transpose_add
- \+ *lemma* transpose_mul
- \+ *lemma* transpose_neg
- \+/\- *theorem* mul_zero
- \+/\- *theorem* zero_mul
- \+/\- *theorem* mul_add
- \+/\- *theorem* add_mul
- \+ *theorem* neg_mul
- \+ *theorem* mul_neg



## [2019-04-05 03:14:12](https://github.com/leanprover-community/mathlib/commit/0b7ee1b)
feat(category_theory): introduce the core of a category ([#832](https://github.com/leanprover-community/mathlib/pull/832))
#### Estimated changes
Created src/category_theory/core.lean
- \+ *lemma* id_hom
- \+ *lemma* comp_hom
- \+ *def* core
- \+ *def* inclusion
- \+ *def* functor_to_core
- \+ *def* forget_functor_to_core

Modified src/category_theory/isomorphism.lean
- \+ *lemma* map_hom_inv
- \+ *lemma* map_inv_hom



## [2019-04-04 20:42:02-04:00](https://github.com/leanprover-community/mathlib/commit/b6c2be4)
chore(mergify): delete head branch when merging
#### Estimated changes
Modified .mergify.yml




## [2019-04-04 23:27:46](https://github.com/leanprover-community/mathlib/commit/7aaccae)
feat(algebra/char_p,field_theory/finite_card): cardinality of finite fields ([#819](https://github.com/leanprover-community/mathlib/pull/819))
* First lemma's added
* fixed lemmas by switching arguments
* vector_space card_fin
* char p implies zmod p module
* Finite field card
* renaming
* .
* bug fix
* move to_module to is_ring_hom.to_module
* fix bug
* remove unnecessary open
* instance instead of thm and remove unnecessary variables
* moved cast_is_ring_hom and zmod.to_module to char_p
* removed redundent nat.prime
* some char_p stuff inside namespace char_p
* fix
* Moved finite field card to a different file
* Removed unnecessary import
* Remove unnecessary lemmas
* Update src/algebra/char_p.lean
Co-Authored-By: CPutz <casper.putz@gmail.com>
* rename char_p lemmas
* Minor changes
#### Estimated changes
Modified src/algebra/char_p.lean
- \+ *lemma* char_p_to_char_zero
- \+ *lemma* cast_eq_mod
- \+ *theorem* char_ne_zero_of_fintype
- \+ *theorem* char_ne_one
- \+ *theorem* char_is_prime_of_ge_two
- \+ *theorem* char_is_prime_or_zero
- \+ *theorem* char_is_prime

Modified src/algebra/module.lean
- \+ *def* is_ring_hom.to_module

Modified src/data/zmod/basic.lean
- \+ *def* cast

Created src/field_theory/finite_card.lean
- \+ *theorem* card
- \+ *theorem* card'

Modified src/linear_algebra/basis.lean
- \+ *theorem* vector_space.card_fintype
- \+ *theorem* vector_space.card_fintype'



## [2019-04-04 16:28:11-04:00](https://github.com/leanprover-community/mathlib/commit/3abfda0)
chore(github/pr): enable code owners
#### Estimated changes
Created CODEOWNERS




## [2019-04-04 19:04:48](https://github.com/leanprover-community/mathlib/commit/8183a5a)
feat(data/list/perm): nil_subperm ([#882](https://github.com/leanprover-community/mathlib/pull/882))
#### Estimated changes
Modified src/data/list/perm.lean
- \+ *theorem* nil_subperm



## [2019-04-04 17:16:18](https://github.com/leanprover-community/mathlib/commit/384c9be)
feat (analysis/normed_space/basic.lean): implement reverse triangle inequality ([#831](https://github.com/leanprover-community/mathlib/pull/831))
* implement reverse triangle inequality
* make parameters explicit
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_reverse_triangle'
- \+ *lemma* norm_reverse_triangle



## [2019-04-04 08:21:57-04:00](https://github.com/leanprover-community/mathlib/commit/07aa1e3)
fix(build): fix Lean version
#### Estimated changes
Modified .travis.yml




## [2019-04-03 17:19:10-04:00](https://github.com/leanprover-community/mathlib/commit/1c69b60)
chore(mergify): fix config
#### Estimated changes
Modified .mergify.yml




## [2019-04-03 16:22:27-04:00](https://github.com/leanprover-community/mathlib/commit/7762bc4)
chore(mergify): fix config file
#### Estimated changes
Modified .mergify.yml




## [2019-04-03 16:06:06-04:00](https://github.com/leanprover-community/mathlib/commit/d4fd4b2)
chore(mergify): use team names instead of user names
#### Estimated changes
Modified .mergify.yml




## [2019-04-03 14:56:14-04:00](https://github.com/leanprover-community/mathlib/commit/2230934)
chore(mergify): disable `delete_head_branch`
#### Estimated changes
Modified .mergify.yml




## [2019-04-03 16:30:14+01:00](https://github.com/leanprover-community/mathlib/commit/840ddeb)
fix(README): fix mergify icon
#### Estimated changes
Modified README.md




## [2019-04-03 08:38:06-04:00](https://github.com/leanprover-community/mathlib/commit/542d179)
chore(github/pr): mergify configuration ([#871](https://github.com/leanprover-community/mathlib/pull/871))
#### Estimated changes
Created .mergify.yml


Modified README.md




## [2019-04-03 08:10:21-04:00](https://github.com/leanprover-community/mathlib/commit/a0cbe3b)
feat(data/fin): add `fin.clamp` ([#874](https://github.com/leanprover-community/mathlib/pull/874))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* cast_val
- \+ *lemma* clamp_val
- \+/\- *def* cast
- \+ *def* clamp



## [2019-04-03 05:37:35-04:00](https://github.com/leanprover-community/mathlib/commit/2c735dc)
feat(ring_theory/algebra_operations): submodules form a semiring ([#856](https://github.com/leanprover-community/mathlib/pull/856))
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* pointwise_mul_finite

Modified src/ring_theory/algebra_operations.lean
- \+ *theorem* one_eq_map_top
- \+ *theorem* one_eq_span
- \+ *theorem* one_le
- \+/\- *theorem* span_mul_span
- \- *theorem* fg_mul

Modified src/ring_theory/ideal_operations.lean
- \+/\- *lemma* one_eq_top
- \+/\- *theorem* smul_bot
- \+/\- *theorem* bot_smul
- \+/\- *theorem* top_smul

Modified src/ring_theory/noetherian.lean
- \+ *theorem* fg_mul



## [2019-04-03 05:35:05-04:00](https://github.com/leanprover-community/mathlib/commit/b9e9328)
feat(topology/metric_space/completion): completion of metric spaces ([#743](https://github.com/leanprover-community/mathlib/pull/743))
#### Estimated changes
Created src/topology/metric_space/completion.lean
- \+ *lemma* completion.coe_isometry



## [2019-04-03 09:38:15+02:00](https://github.com/leanprover-community/mathlib/commit/c3aba26)
feat(topology/uniform_space/pi): indexed products of uniform spaces ([#845](https://github.com/leanprover-community/mathlib/pull/845))
* feat(topology/uniform_space/pi): indexed products of uniform spaces
* fix(topology/uniform_space/pi): defeq topology
* fix(src/topology/uniform_space/pi): typo
Co-Authored-By: PatrickMassot <patrickmassot@free.fr>
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+/\- *theorem* uniformity_prod

Created src/topology/uniform_space/pi.lean
- \+ *lemma* Pi.uniformity
- \+ *lemma* Pi.uniform_continuous_proj
- \+ *lemma* Pi.uniform_space_topology



## [2019-04-03 02:27:59-04:00](https://github.com/leanprover-community/mathlib/commit/7043a4a)
feat(algebra/pointwise): pointwise addition and multiplication of sets ([#854](https://github.com/leanprover-community/mathlib/pull/854))
#### Estimated changes
Created src/algebra/pointwise.lean
- \+ *lemma* mem_pointwise_one
- \+ *lemma* mem_pointwise_mul
- \+ *lemma* mul_mem_pointwise_mul
- \+ *lemma* pointwise_mul_eq_image
- \+ *lemma* pointwise_mul_empty
- \+ *lemma* empty_pointwise_mul
- \+ *lemma* pointwise_mul_subset_mul
- \+ *lemma* pointwise_mul_union
- \+ *lemma* union_pointwise_mul
- \+ *def* pointwise_one
- \+ *def* pointwise_mul
- \+ *def* pointwise_mul_semigroup
- \+ *def* pointwise_add_add_semigroup
- \+ *def* pointwise_mul_monoid
- \+ *def* pointwise_add_add_monoid
- \+ *def* singleton.is_mul_hom
- \+ *def* singleton.is_monoid_hom
- \+ *def* pointwise_inv
- \+ *def* pointwise_mul_semiring
- \+ *def* pointwise_mul_comm_semiring



## [2019-04-02 21:14:02-04:00](https://github.com/leanprover-community/mathlib/commit/f112076)
feat(tactic/basic): add `tactic.get_goal` ([#876](https://github.com/leanprover-community/mathlib/pull/876))
#### Estimated changes
Modified src/tactic/basic.lean




## [2019-04-02 20:45:14-04:00](https://github.com/leanprover-community/mathlib/commit/e96d6b7)
fix(int/basic): change order of instances to int.cast ([#877](https://github.com/leanprover-community/mathlib/pull/877))
As discussed at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Problem.20with.20type.20class.20search/near/161848744
Changing the order of arguments lets type class inference fail quickly for `int -> nat` coercions, rather than repeatedly looking for `has_neg` on `nat`.
#### Estimated changes
Modified src/data/int/basic.lean




## [2019-04-02 18:34:18-04:00](https://github.com/leanprover-community/mathlib/commit/ce92e8a)
chore(.travis.yml): use Lean to determine the Lean version ([#714](https://github.com/leanprover-community/mathlib/pull/714))
#### Estimated changes
Modified .travis.yml


Created scripts/lean_version.lean
- \+ *def* lean_version_string_core
- \+ *def* main

Deleted scripts/lean_version.py




## [2019-04-02 18:33:34-04:00](https://github.com/leanprover-community/mathlib/commit/6c55989)
build(travis): interrupt the build at the first error message ([#708](https://github.com/leanprover-community/mathlib/pull/708))
Also make travis_long.sh print its progress messages to stderr.
This sidesteps a mysterious issue where piping the output of
travis_long.sh to another program caused that output to be lost
(probably buffered somewhere?) so Travis would kill the build
after 10 minutes.
#### Estimated changes
Modified .travis.yml


Created scripts/detect_errors.py


Modified travis_long.sh




## [2019-04-02 11:22:44-04:00](https://github.com/leanprover-community/mathlib/commit/13034ba)
feat(tactic/local_cache): add tactic-block-local caching mechanism ([#837](https://github.com/leanprover-community/mathlib/pull/837))
#### Estimated changes
Modified src/meta/expr.lean
- \+ *def* from_components

Modified src/tactic/basic.lean


Created src/tactic/local_cache.lean
- \+ *def* FNV_OFFSET_BASIS
- \+ *def* FNV_PRIME
- \+ *def* RADIX
- \+ *def* hash_byte
- \+ *def* hash_string

Created test/local_cache.lean
- \+ *lemma* my_lemma
- \+ *lemma* my_lemma'
- \+ *lemma* my_test_ps
- \+ *lemma* my_test_ns
- \+ *lemma* my_lemma_1
- \+ *lemma* my_lemma_2
- \+ *lemma* my_lemma_3
- \+ *lemma* my_lemma_4
- \+ *def* TEST_NS_1
- \+ *def* TEST_NS_2
- \+ *def* my_definition
- \+ *def* my_definition'
- \+ *def* my_def_1
- \+ *def* my_def_2
- \+ *def* TEST_NS



## [2019-04-02 10:44:43-04:00](https://github.com/leanprover-community/mathlib/commit/7eac178)
fix(scripts/update-mathlib): protect file operations from interrupts ([#864](https://github.com/leanprover-community/mathlib/pull/864))
#### Estimated changes
Modified .gitignore


Created scripts/auth_github.py
- \+ *def* auth_github():

Modified scripts/cache-olean.py
- \- *def* auth_github():

Created scripts/delayed_interrupt.py


Modified scripts/setup-dev-scripts.sh


Modified scripts/update-mathlib.py
- \- *def* auth_github():



## [2019-04-02 08:23:50-05:00](https://github.com/leanprover-community/mathlib/commit/f385ad6)
Inductive limit of metric spaces ([#732](https://github.com/leanprover-community/mathlib/pull/732))
#### Estimated changes
Modified src/topology/metric_space/gluing.lean
- \+ *lemma* inductive_limit_dist_eq_dist
- \+ *lemma* to_inductive_limit_isometry
- \+ *lemma* to_inductive_limit_commute
- \+ *def* inductive_limit_dist
- \+ *def* inductive_premetric
- \+ *def* inductive_limit
- \+ *def* to_inductive_limit



## [2019-04-02 07:57:52-04:00](https://github.com/leanprover-community/mathlib/commit/727120c)
fix(build): improve compatibility of caching scripts with Sourcetree ([#863](https://github.com/leanprover-community/mathlib/pull/863))
#### Estimated changes
Modified scripts/post-checkout


Modified scripts/post-commit




## [2019-04-01 20:04:58-05:00](https://github.com/leanprover-community/mathlib/commit/5694d15)
feat(data/nat/basic): nat.le_rec_on ([#585](https://github.com/leanprover-community/mathlib/pull/585))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *theorem* of_le_succ
- \+ *theorem* le_rec_on_self
- \+ *theorem* le_rec_on_succ
- \+ *theorem* le_rec_on_succ'
- \+ *theorem* le_rec_on_trans
- \+ *theorem* le_rec_on_injective
- \+ *theorem* le_rec_on_surjective
- \+ *def* le_rec_on



## [2019-04-01 18:55:36-04:00](https://github.com/leanprover-community/mathlib/commit/8e4542d)
Merge branch 'congr-2'
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/interactive.lean


Created src/tactic/push_neg.lean
- \+ *theorem* not_not_eq
- \+ *theorem* not_and_eq
- \+ *theorem* not_or_eq
- \+ *theorem* not_forall_eq
- \+ *theorem* not_exists_eq
- \+ *theorem* not_implies_eq
- \+ *theorem* classical.implies_iff_not_or
- \+ *theorem* not_eq
- \+ *theorem* not_le_eq
- \+ *theorem* not_lt_eq

Created test/push_neg.lean




## [2019-04-01 18:52:21-04:00](https://github.com/leanprover-community/mathlib/commit/ec0a4ea)
fix(tactic/congr'): some `\iff` goals were erroneously rejected
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/interactive.lean


Deleted src/tactic/push_neg.lean
- \- *theorem* not_not_eq
- \- *theorem* not_and_eq
- \- *theorem* not_or_eq
- \- *theorem* not_forall_eq
- \- *theorem* not_exists_eq
- \- *theorem* not_implies_eq
- \- *theorem* classical.implies_iff_not_or
- \- *theorem* not_eq
- \- *theorem* not_le_eq
- \- *theorem* not_lt_eq

Deleted test/push_neg.lean




## [2019-04-01 16:48:53-04:00](https://github.com/leanprover-community/mathlib/commit/5fe470b)
feat(tactic/push_neg): a tactic pushing negations ([#853](https://github.com/leanprover-community/mathlib/pull/853))
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/interactive.lean


Created src/tactic/push_neg.lean
- \+ *theorem* not_not_eq
- \+ *theorem* not_and_eq
- \+ *theorem* not_or_eq
- \+ *theorem* not_forall_eq
- \+ *theorem* not_exists_eq
- \+ *theorem* not_implies_eq
- \+ *theorem* classical.implies_iff_not_or
- \+ *theorem* not_eq
- \+ *theorem* not_le_eq
- \+ *theorem* not_lt_eq

Created test/push_neg.lean




## [2019-04-01 16:21:09-04:00](https://github.com/leanprover-community/mathlib/commit/5995d46)
fix(build): prevent leanchecker from timing out
#### Estimated changes
Modified .travis.yml




## [2019-04-01 16:13:58-04:00](https://github.com/leanprover-community/mathlib/commit/2f088fc)
feat(category_theory): working in Sort rather than Type ([#824](https://github.com/leanprover-community/mathlib/pull/824))
#### Estimated changes
Modified src/category_theory/adjunction.lean


Modified src/category_theory/category.lean
- \+/\- *lemma* End.one_def
- \+/\- *lemma* End.mul_def

Modified src/category_theory/comma.lean
- \+/\- *def* over
- \+/\- *def* under

Modified src/category_theory/concrete_category.lean
- \+/\- *def* mk_ob
- \+/\- *def* forget

Modified src/category_theory/const.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/full_subcategory.lean
- \+/\- *def* induced_category

Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/functor.lean


Modified src/category_theory/functor_category.lean


Modified src/category_theory/groupoid.lean


Modified src/category_theory/instances/monoids.lean


Created src/category_theory/instances/rel.lean
- \+ *def* rel

Modified src/category_theory/isomorphism.lean


Modified src/category_theory/limits/cones.lean
- \+ *lemma* extend_π
- \+ *lemma* extend_ι

Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* limit.pre_post
- \+/\- *lemma* limit.map_post
- \+/\- *lemma* colimit.pre_post
- \+/\- *lemma* colimit.map_post
- \+/\- *def* of_faithful

Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/category_theory/natural_transformation.lean


Modified src/category_theory/opposites.lean
- \+/\- *lemma* hom_obj
- \+/\- *lemma* hom_pairing_map
- \+/\- *lemma* opposite.unop_one
- \+/\- *lemma* opposite.unop_mul
- \+/\- *lemma* opposite.op_one
- \+/\- *lemma* opposite.op_mul
- \+/\- *def* opposite

Modified src/category_theory/pempty.lean


Modified src/category_theory/products.lean


Modified src/category_theory/punit.lean


Modified src/category_theory/types.lean
- \+/\- *lemma* types_hom
- \+/\- *lemma* types_id
- \+/\- *lemma* types_comp

Modified src/category_theory/whiskering.lean


Modified src/category_theory/yoneda.lean
- \+/\- *def* yoneda
- \+/\- *def* coyoneda



## [2019-04-01 22:07:28+02:00](https://github.com/leanprover-community/mathlib/commit/404e2c9)
add tutorial about zmod37 ([#767](https://github.com/leanprover-community/mathlib/pull/767))
Reference to a mathlib file which no longer exists has been fixed, and a more user-friendly example of an equivalence relation has been added in a tutorial.
#### Estimated changes
Modified docs/theories/relations.md


Created docs/tutorial/Zmod37.lean
- \+ *lemma* congr_add
- \+ *lemma* congr_neg
- \+ *lemma* coe_add
- \+ *lemma* coe_neg
- \+ *lemma* coe_mul
- \+ *theorem* cong_mod_refl
- \+ *theorem* cong_mod_symm
- \+ *theorem* cong_mod_trans
- \+ *theorem* cong_mod_equiv
- \+ *theorem* of_int_zero
- \+ *theorem* of_int_one



## [2019-04-01 21:58:17+02:00](https://github.com/leanprover-community/mathlib/commit/867661e)
docs(tactics): add introduction to the instance cache tactic section
#### Estimated changes
Modified docs/tactics.md
- \+ *def* my_id



## [2019-04-01 21:55:31+02:00](https://github.com/leanprover-community/mathlib/commit/59e0593)
docs(tactics): minor rewrite of exactI, resetI etc
I always found these tactics confusing, but I finally figured out what they do and so I rewrote the docs so that I understand them better.
#### Estimated changes
Modified docs/tactics.md




## [2019-04-01 15:08:22-04:00](https://github.com/leanprover-community/mathlib/commit/a1fe39b)
refactor(analysis/convex): make instance local ([#869](https://github.com/leanprover-community/mathlib/pull/869))
#### Estimated changes
Modified src/analysis/convex.lean




## [2019-04-01 14:48:06-04:00](https://github.com/leanprover-community/mathlib/commit/3bc0f00)
fix(scripts/cache-olean): only run the post-checkout hook if we actually changed branches ([#857](https://github.com/leanprover-community/mathlib/pull/857))
#### Estimated changes
Modified scripts/post-checkout




## [2019-04-01 03:01:21-04:00](https://github.com/leanprover-community/mathlib/commit/2851236)
feat(data/real/pi): Compute the first three digits of pi ([#822](https://github.com/leanprover-community/mathlib/pull/822))
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *lemma* pow_lt_pow

Modified src/analysis/exponential.lean
- \+ *lemma* sin_lt
- \+ *lemma* sin_gt_sub_cube

Modified src/data/complex/basic.lean
- \+ *lemma* div_re
- \+ *lemma* div_im

Modified src/data/complex/exponential.lean
- \+ *lemma* cos_square
- \+ *lemma* sin_square

Modified src/data/real/basic.lean
- \+ *lemma* sqrt_le_sqrt
- \+ *lemma* sqrt_le_left
- \+ *lemma* le_sqrt
- \+ *lemma* le_sqrt'
- \+ *lemma* le_sqrt_of_sqr_le
- \+/\- *theorem* le_mk_of_forall_le
- \+/\- *theorem* sqrt_eq_zero_of_nonpos
- \+/\- *theorem* mul_self_sqrt
- \+/\- *theorem* sqrt_mul_self
- \+/\- *theorem* sqrt_eq_iff_mul_self_eq
- \+/\- *theorem* sqr_sqrt
- \+/\- *theorem* sqrt_sqr
- \+/\- *theorem* sqrt_eq_iff_sqr_eq
- \+/\- *theorem* sqrt_le
- \+/\- *theorem* sqrt_lt
- \+/\- *theorem* sqrt_inj
- \+/\- *theorem* sqrt_eq_zero
- \+/\- *theorem* sqrt_eq_zero'
- \+/\- *theorem* sqrt_pos
- \+/\- *theorem* sqrt_mul
- \+/\- *theorem* sqrt_div

Created src/data/real/pi.lean
- \+ *lemma* sqrt_two_add_series_zero
- \+ *lemma* sqrt_two_add_series_one
- \+ *lemma* sqrt_two_add_series_two
- \+ *lemma* sqrt_two_add_series_zero_nonneg
- \+ *lemma* sqrt_two_add_series_nonneg
- \+ *lemma* sqrt_two_add_series_lt_two
- \+ *lemma* sqrt_two_add_series_succ
- \+ *lemma* sqrt_two_add_series_monotone_left
- \+ *lemma* sqrt_two_add_series_step_up
- \+ *lemma* sqrt_two_add_series_step_down
- \+ *lemma* cos_pi_over_two_pow
- \+ *lemma* sin_square_pi_over_two_pow
- \+ *lemma* sin_square_pi_over_two_pow_succ
- \+ *lemma* sin_pi_over_two_pow_succ
- \+ *lemma* cos_pi_div_four
- \+ *lemma* sin_pi_div_four
- \+ *lemma* cos_pi_div_eight
- \+ *lemma* sin_pi_div_eight
- \+ *lemma* cos_pi_div_sixteen
- \+ *lemma* sin_pi_div_sixteen
- \+ *lemma* cos_pi_div_thirty_two
- \+ *lemma* sin_pi_div_thirty_two
- \+ *lemma* pi_gt_sqrt_two_add_series
- \+ *lemma* pi_lt_sqrt_two_add_series
- \+ *lemma* pi_gt_three
- \+ *lemma* pi_gt_314
- \+ *lemma* pi_lt_315

