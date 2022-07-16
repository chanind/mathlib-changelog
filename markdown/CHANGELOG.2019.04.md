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
Added src/analysis/normed_space/banach.lean
- \+ *theorem* exists_preimage_norm_le
- \+ *theorem* linear_equiv.is_bounded_inv
- \+ *theorem* open_mapping

Modified src/analysis/specific_limits.lean
- \+ *lemma* has_sum_geometric_two'
- \+/\- *lemma* has_sum_geometric_two
- \+ *lemma* summable_geometric
- \+ *lemma* summable_geometric_two
- \+ *lemma* tsum_geometric
- \+ *lemma* tsum_geometric_two



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
- \+/\- *theorem* list.nil_subperm

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
- \+/\- *lemma* classical.iff_iff_not_or_and_or_not

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
- \+/\- *theorem* fderiv_at_unique
- \+/\- *theorem* fderiv_at_within_open_unique
- \+/\- *theorem* has_fderiv_at.comp
- \+/\- *theorem* has_fderiv_at.congr
- \+/\- *theorem* has_fderiv_at.continuous_at
- \- *theorem* has_fderiv_at.is_o
- \+/\- *def* has_fderiv_at
- \+/\- *theorem* has_fderiv_at_add
- \+/\- *theorem* has_fderiv_at_congr
- \+/\- *theorem* has_fderiv_at_filter.comp
- \+/\- *theorem* has_fderiv_at_filter.congr
- \+/\- *theorem* has_fderiv_at_filter.is_O_sub
- \- *theorem* has_fderiv_at_filter.is_o
- \+/\- *theorem* has_fderiv_at_filter.mono
- \+/\- *theorem* has_fderiv_at_filter.tendsto_nhds
- \+/\- *def* has_fderiv_at_filter
- \+/\- *theorem* has_fderiv_at_filter_add
- \+/\- *theorem* has_fderiv_at_filter_congr'
- \+/\- *theorem* has_fderiv_at_filter_congr
- \+/\- *theorem* has_fderiv_at_filter_id
- \+/\- *theorem* has_fderiv_at_filter_iff_tendsto
- \+/\- *theorem* has_fderiv_at_filter_neg
- \+/\- *theorem* has_fderiv_at_filter_of_has_fderiv_at
- \+/\- *theorem* has_fderiv_at_filter_real_equiv
- \+/\- *theorem* has_fderiv_at_filter_smul
- \+/\- *theorem* has_fderiv_at_filter_sub
- \+/\- *theorem* has_fderiv_at_id
- \+/\- *theorem* has_fderiv_at_iff_tendsto
- \+/\- *theorem* has_fderiv_at_neg
- \+/\- *theorem* has_fderiv_at_smul
- \+/\- *theorem* has_fderiv_at_sub
- \+/\- *theorem* has_fderiv_at_within.comp
- \+/\- *theorem* has_fderiv_at_within.congr
- \+/\- *theorem* has_fderiv_at_within.continuous_at_within
- \+/\- *theorem* has_fderiv_at_within.mono
- \+/\- *def* has_fderiv_at_within
- \+/\- *theorem* has_fderiv_at_within_add
- \+/\- *theorem* has_fderiv_at_within_congr
- \+/\- *theorem* has_fderiv_at_within_id
- \+/\- *theorem* has_fderiv_at_within_iff_tendsto
- \+/\- *theorem* has_fderiv_at_within_neg
- \+/\- *theorem* has_fderiv_at_within_of_has_fderiv_at
- \+/\- *theorem* has_fderiv_at_within_smul
- \+/\- *theorem* has_fderiv_at_within_sub

Modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* bounded_linear_map.bound_le_op_norm
- \+ *lemma* bounded_linear_map.op_norm_le_bound



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
- \+ *lemma* equiv.set.of_eq_apply
- \+ *lemma* equiv.set.of_eq_symm_apply
- \+ *lemma* equiv.set.sum_compl_apply_inl
- \+ *lemma* equiv.set.sum_compl_apply_inr
- \+ *lemma* equiv.set.sum_compl_symm_apply_of_mem
- \+ *lemma* equiv.set.sum_compl_symm_apply_of_not_mem
- \+ *lemma* equiv.set.union_apply_left
- \+ *lemma* equiv.set.union_apply_right
- \+ *lemma* equiv.set.univ_apply
- \+ *lemma* equiv.set.univ_symm_apply
- \+ *theorem* equiv.symm_symm_apply



## [2019-04-25 18:58:02](https://github.com/leanprover-community/mathlib/commit/038f809)
refactor(analysis/normed_space/operator_norm): replace subspace with … ([#955](https://github.com/leanprover-community/mathlib/pull/955))
* refactor(analysis/normed_space/operator_norm): replace subspace with structure
* refactor(analysis/normed_space/operator_norm): add coercions
#### Estimated changes
Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* bounded_linear_map.is_bounded_linear_map
- \+ *def* is_bounded_linear_map.to_bounded_linear_map
- \- *lemma* mul_inv_eq'

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* bounded_linear_map.add_apply
- \+ *lemma* bounded_linear_map.coe_add'
- \+ *lemma* bounded_linear_map.coe_add
- \+ *lemma* bounded_linear_map.coe_apply'
- \+ *lemma* bounded_linear_map.coe_apply
- \+ *lemma* bounded_linear_map.coe_coe
- \+ *lemma* bounded_linear_map.coe_comp'
- \+ *lemma* bounded_linear_map.coe_comp
- \+ *lemma* bounded_linear_map.coe_id'
- \+ *lemma* bounded_linear_map.coe_id
- \+ *lemma* bounded_linear_map.coe_neg'
- \+ *lemma* bounded_linear_map.coe_neg
- \+ *lemma* bounded_linear_map.coe_sub'
- \+ *lemma* bounded_linear_map.coe_sub
- \+ *lemma* bounded_linear_map.coe_zero'
- \+/\- *lemma* bounded_linear_map.coe_zero
- \+ *theorem* bounded_linear_map.continuous
- \+ *def* bounded_linear_map.id
- \+ *lemma* bounded_linear_map.id_apply
- \+/\- *theorem* bounded_linear_map.is_O_sub
- \+/\- *lemma* bounded_linear_map.neg_apply
- \- *lemma* bounded_linear_map.one_smul
- \+ *lemma* bounded_linear_map.sub_apply
- \- *theorem* bounded_linear_map.tendsto
- \- *def* bounded_linear_map.to_linear_map
- \+ *def* bounded_linear_map.zero
- \- *lemma* bounded_linear_map.zero_smul
- \+ *structure* bounded_linear_map
- \- *def* bounded_linear_map
- \- *def* bounded_linear_map_subspace
- \+ *lemma* exists_pos_bound_of_bound
- \- *def* is_bounded_linear_map.to_bounded_linear_map



## [2019-04-23 20:15:47](https://github.com/leanprover-community/mathlib/commit/1d9ff68)
feat(function/embedding): ext and ext_iff ([#962](https://github.com/leanprover-community/mathlib/pull/962))
#### Estimated changes
Modified src/logic/embedding.lean
- \+ *lemma* function.embedding.ext
- \+ *lemma* function.embedding.ext_iff



## [2019-04-23 07:22:05](https://github.com/leanprover-community/mathlib/commit/0d7b419)
fix(ring_theory/adjoin_root): move adjoin_root out of adjoin_root namespace ([#960](https://github.com/leanprover-community/mathlib/pull/960))
#### Estimated changes
Modified src/ring_theory/adjoin_root.lean
- \- *def* adjoin_root.adjoin_root
- \+ *def* adjoin_root



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
- \+ *lemma* list.index_of_inj



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
- \+ *theorem* finset.filter_union_right
- \+ *lemma* finset.nonempty_iff_ne_empty
- \+ *lemma* finset.subset_image_iff
- \+ *lemma* finset.subset_union_elim
- \+ *lemma* finset.to_set_injective
- \+ *lemma* finset.to_set_sdiff

Modified src/data/set/basic.lean
- \+ *lemma* set.compl_empty_iff
- \+ *lemma* set.compl_univ_iff
- \+ *lemma* set.diff_singleton_subset_iff
- \+ *lemma* set.image_congr'
- \+ *lemma* set.image_eq_range
- \+ *lemma* set.image_id'
- \+ *lemma* set.image_image
- \+ *lemma* set.mem_diff_singleton
- \+ *lemma* set.mem_diff_singleton_empty
- \+ *lemma* set.nmem_singleton_empty
- \+ *lemma* set.nonempty_compl
- \+ *lemma* set.nonempty_image
- \+ *lemma* set.preimage_eq_preimage'
- \+ *lemma* set.preimage_subset_preimage_iff
- \+ *lemma* set.subset_insert_diff
- \+ *lemma* set.subset_insert_diff_singleton
- \+ *lemma* set.subset_union_of_subset_left
- \+ *lemma* set.subset_union_of_subset_right
- \+ *lemma* subtype.exists_set_subtype
- \+ *lemma* subtype.range_val

Modified src/data/set/finite.lean
- \+ *lemma* set.exists_finset_of_finite
- \+ *lemma* set.finite.coe_to_finset
- \+ *theorem* set.finite_bUnion'

Modified src/data/set/function.lean
- \+ *lemma* set.inj_on_comp_of_injective_left
- \+ *lemma* set.inj_on_preimage

Modified src/data/set/lattice.lean
- \+ *lemma* disjoint_self
- \+ *lemma* ne_of_disjoint
- \+ *lemma* set.Union_of_singleton
- \+ *lemma* set.Union_range_eq_Union
- \+ *lemma* set.Union_range_eq_sUnion
- \+ *def* set.pairwise_disjoint
- \+ *lemma* set.pairwise_disjoint_elim
- \+ *lemma* set.pairwise_disjoint_range
- \+ *lemma* set.pairwise_disjoint_subset
- \+ *lemma* set.subset_sUnion_of_subset



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
- \+/\- *lemma* list.func.add_nil
- \+/\- *lemma* list.func.equiv_of_eq
- \+/\- *lemma* list.func.equiv_symm
- \+/\- *lemma* list.func.forall_val_of_forall_mem
- \+/\- *lemma* list.func.get_map'
- \+/\- *lemma* list.func.get_map
- \+/\- *lemma* list.func.get_neg
- \+/\- *lemma* list.func.get_nil
- \+/\- *lemma* list.func.get_pointwise
- \+/\- *lemma* list.func.get_sub
- \+/\- *lemma* list.func.length_add
- \+/\- *lemma* list.func.length_neg
- \+/\- *lemma* list.func.length_pointwise
- \+/\- *lemma* list.func.length_sub
- \+/\- *lemma* list.func.nil_add
- \+/\- *lemma* list.func.nil_pointwise
- \+/\- *lemma* list.func.nil_sub
- \+/\- *lemma* list.func.pointwise_nil
- \+/\- *lemma* list.func.sub_nil

Modified src/tactic/omega/coeffs.lean
- \+/\- *lemma* omega.coeffs.val_between_map_div
- \+/\- *lemma* omega.coeffs.val_except_update_set

Modified src/tactic/omega/eq_elim.lean


Modified src/tactic/omega/find_ees.lean
- \+ *structure* omega.ee_state

Modified src/tactic/omega/int/dnf.lean


Modified src/tactic/omega/int/form.lean


Modified src/tactic/omega/int/main.lean


Modified src/tactic/omega/int/preterm.lean


Modified src/tactic/omega/misc.lean


Modified src/tactic/omega/nat/dnf.lean


Modified src/tactic/omega/nat/form.lean
- \+/\- *def* omega.nat.form.equiv
- \+/\- *def* omega.nat.form.fresh_index
- \+/\- *def* omega.nat.form.holds
- \+/\- *def* omega.nat.form.implies
- \+/\- *def* omega.nat.form.neg_free
- \+/\- *def* omega.nat.form.repr
- \+/\- *def* omega.nat.form.sat
- \+/\- *def* omega.nat.form.sub_free
- \+/\- *def* omega.nat.form.valid
- \+/\- *inductive* omega.nat.form
- \+/\- *def* omega.nat.univ_close
- \+/\- *lemma* omega.nat.univ_close_of_valid
- \+/\- *lemma* omega.nat.valid_of_unsat_not

Modified src/tactic/omega/nat/main.lean


Modified src/tactic/omega/nat/neg_elim.lean
- \+/\- *lemma* omega.nat.implies_neg_elim_core
- \+/\- *def* omega.nat.is_nnf
- \+/\- *lemma* omega.nat.is_nnf_nnf
- \+/\- *lemma* omega.nat.le_and_le_iff_eq
- \+/\- *def* omega.nat.neg_elim_core
- \+/\- *lemma* omega.nat.neg_free_neg_elim
- \+/\- *lemma* omega.nat.neg_free_neg_elim_core
- \+/\- *def* omega.nat.nnf
- \+/\- *def* omega.nat.push_neg
- \+/\- *lemma* omega.nat.push_neg_equiv

Modified src/tactic/omega/nat/preterm.lean
- \+/\- *def* omega.nat.canonize
- \+/\- *def* omega.nat.preterm.fresh_index
- \+/\- *def* omega.nat.preterm.repr
- \+/\- *def* omega.nat.preterm.sub_free
- \+/\- *def* omega.nat.preterm.val
- \+/\- *lemma* omega.nat.preterm.val_add
- \+/\- *lemma* omega.nat.preterm.val_sub
- \+/\- *lemma* omega.nat.val_canonize

Modified src/tactic/omega/nat/sub_elim.lean


Modified src/tactic/omega/term.lean
- \+ *def* omega.term.to_string

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
- \+/\- *lemma* is_bounded_linear_map.add
- \+/\- *lemma* is_bounded_linear_map.comp
- \+/\- *lemma* is_bounded_linear_map.continuous
- \+/\- *theorem* is_bounded_linear_map.is_O_comp
- \+/\- *theorem* is_bounded_linear_map.is_O_id
- \+/\- *theorem* is_bounded_linear_map.is_O_sub
- \+/\- *lemma* is_bounded_linear_map.lim_zero_bounded_linear_map
- \+/\- *lemma* is_bounded_linear_map.neg
- \+/\- *lemma* is_bounded_linear_map.smul
- \+/\- *lemma* is_bounded_linear_map.sub
- \+/\- *lemma* is_bounded_linear_map.tendsto
- \+/\- *structure* is_bounded_linear_map

Modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* bdd_above_range_norm_image_div_norm
- \- *theorem* bounded_by_operator_norm
- \+ *lemma* bounded_linear_map.bound_le_op_norm
- \+ *lemma* bounded_linear_map.bounds_bdd_below
- \+ *lemma* bounded_linear_map.bounds_nonempty
- \+ *lemma* bounded_linear_map.coe_zero
- \+ *def* bounded_linear_map.comp
- \+ *theorem* bounded_linear_map.ext
- \+ *theorem* bounded_linear_map.ext_iff
- \+ *theorem* bounded_linear_map.is_O_comp
- \+ *theorem* bounded_linear_map.is_O_id
- \+ *theorem* bounded_linear_map.is_O_sub
- \+ *theorem* bounded_linear_map.le_op_norm
- \+ *theorem* bounded_linear_map.lipschitz
- \+ *lemma* bounded_linear_map.map_add
- \+ *lemma* bounded_linear_map.map_neg
- \+ *lemma* bounded_linear_map.map_smul
- \+ *lemma* bounded_linear_map.map_sub
- \+ *lemma* bounded_linear_map.map_zero
- \+ *lemma* bounded_linear_map.neg_apply
- \+ *lemma* bounded_linear_map.one_smul
- \+ *def* bounded_linear_map.op_norm
- \+ *lemma* bounded_linear_map.op_norm_comp_le
- \+ *lemma* bounded_linear_map.op_norm_nonneg
- \+ *lemma* bounded_linear_map.op_norm_smul
- \+ *theorem* bounded_linear_map.op_norm_triangle
- \+ *theorem* bounded_linear_map.op_norm_zero_iff
- \+ *lemma* bounded_linear_map.ratio_le_op_norm
- \+ *lemma* bounded_linear_map.smul_apply
- \+ *theorem* bounded_linear_map.tendsto
- \+ *def* bounded_linear_map.to_linear_map
- \+ *lemma* bounded_linear_map.unit_le_op_norm
- \+ *lemma* bounded_linear_map.zero_apply
- \+ *lemma* bounded_linear_map.zero_smul
- \+ *def* bounded_linear_map
- \+ *def* bounded_linear_map_subspace
- \- *lemma* bounded_linear_maps.coe_zero
- \- *lemma* bounded_linear_maps.map_zero
- \- *lemma* bounded_linear_maps.one_smul
- \- *lemma* bounded_linear_maps.smul_coe
- \- *lemma* bounded_linear_maps.zero_smul
- \- *def* bounded_linear_maps
- \- *lemma* exists_bound
- \- *theorem* ext
- \+ *def* is_bounded_linear_map.to_bounded_linear_map
- \- *lemma* operator_norm_bounded_by
- \- *theorem* operator_norm_homogeneous
- \- *lemma* operator_norm_homogeneous_le
- \- *lemma* operator_norm_nonneg
- \- *theorem* operator_norm_triangle
- \- *theorem* operator_norm_zero_iff
- \- *def* to_linear_map



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
- \+ *lemma* int.add_div_of_dvd
- \+ *lemma* int.default_eq_zero

Modified src/data/list/basic.lean
- \+/\- *lemma* list.Ico.filter_ge
- \+ *lemma* list.func.add_nil
- \+ *lemma* list.func.eq_get_of_mem
- \+ *lemma* list.func.eq_of_equiv
- \+ *lemma* list.func.equiv_of_eq
- \+ *lemma* list.func.equiv_refl
- \+ *lemma* list.func.equiv_symm
- \+ *lemma* list.func.equiv_trans
- \+ *lemma* list.func.forall_val_of_forall_mem
- \+ *lemma* list.func.get_add
- \+ *lemma* list.func.get_eq_default_of_le
- \+ *lemma* list.func.get_map'
- \+ *lemma* list.func.get_map
- \+ *lemma* list.func.get_neg
- \+ *lemma* list.func.get_nil
- \+ *lemma* list.func.get_pointwise
- \+ *lemma* list.func.get_set
- \+ *lemma* list.func.get_set_eq_of_ne
- \+ *lemma* list.func.get_sub
- \+ *lemma* list.func.length_add
- \+ *lemma* list.func.length_neg
- \+ *lemma* list.func.length_pointwise
- \+ *lemma* list.func.length_set
- \+ *lemma* list.func.length_sub
- \+ *lemma* list.func.map_add_map
- \+ *lemma* list.func.mem_get_of_le
- \+ *lemma* list.func.mem_get_of_ne_zero
- \+ *lemma* list.func.nil_add
- \+ *lemma* list.func.nil_pointwise
- \+ *lemma* list.func.nil_sub
- \+ *lemma* list.func.pointwise_nil
- \+ *lemma* list.func.sub_nil

Modified src/data/list/defs.lean
- \+ *def* list.func.add
- \+ *def* list.func.equiv
- \+ *def* list.func.get
- \+ *def* list.func.neg
- \+ *def* list.func.pointwise
- \+ *def* list.func.set
- \+ *def* list.func.sub
- \+ *def* list.map_with_index
- \+ *def* list.map_with_index_core

Modified src/data/nat/basic.lean
- \+ *lemma* nat.lt_iff_add_one_le
- \+ *theorem* nat.max_succ_succ
- \+ *lemma* nat.zero_max

Modified src/logic/basic.lean
- \+ *lemma* classical.iff_iff_not_or_and_or_not

Added src/tactic/omega/clause.lean
- \+ *def* omega.clause.append
- \+ *def* omega.clause.holds
- \+ *def* omega.clause.holds_append
- \+ *def* omega.clause.sat
- \+ *def* omega.clause.unsat
- \+ *def* omega.clause
- \+ *def* omega.clauses.sat
- \+ *def* omega.clauses.unsat
- \+ *lemma* omega.clauses.unsat_cons
- \+ *lemma* omega.clauses.unsat_nil

Added src/tactic/omega/coeffs.lean
- \+ *lemma* omega.coeffs.dvd_val
- \+ *lemma* omega.coeffs.dvd_val_between
- \+ *lemma* omega.coeffs.forall_val_dvd_of_forall_mem_dvd
- \+ *def* omega.coeffs.val
- \+ *lemma* omega.coeffs.val_add
- \+ *def* omega.coeffs.val_between
- \+ *lemma* omega.coeffs.val_between_add
- \+ *lemma* omega.coeffs.val_between_add_val_between
- \+ *lemma* omega.coeffs.val_between_eq_of_le
- \+ *lemma* omega.coeffs.val_between_eq_val_between
- \+ *lemma* omega.coeffs.val_between_eq_zero
- \+ *lemma* omega.coeffs.val_between_map_div
- \+ *lemma* omega.coeffs.val_between_map_mul
- \+ *lemma* omega.coeffs.val_between_neg
- \+ *lemma* omega.coeffs.val_between_nil
- \+ *def* omega.coeffs.val_between_set
- \+ *lemma* omega.coeffs.val_between_sub
- \+ *lemma* omega.coeffs.val_eq_of_le
- \+ *lemma* omega.coeffs.val_eq_zero
- \+ *def* omega.coeffs.val_except
- \+ *def* omega.coeffs.val_except_add_eq
- \+ *lemma* omega.coeffs.val_except_eq_val_except
- \+ *lemma* omega.coeffs.val_except_update_set
- \+ *lemma* omega.coeffs.val_map_div
- \+ *lemma* omega.coeffs.val_neg
- \+ *lemma* omega.coeffs.val_nil
- \+ *def* omega.coeffs.val_set
- \+ *lemma* omega.coeffs.val_sub

Added src/tactic/omega/default.lean


Added src/tactic/omega/eq_elim.lean
- \+ *def* omega.cancel
- \+ *def* omega.coeffs_reduce
- \+ *lemma* omega.coeffs_reduce_correct
- \+ *def* omega.ee.repr
- \+ *inductive* omega.ee
- \+ *def* omega.eq_elim
- \+ *lemma* omega.mul_symdiv_eq
- \+ *def* omega.rhs
- \+ *lemma* omega.rhs_correct
- \+ *lemma* omega.rhs_correct_aux
- \+ *lemma* omega.sat_empty
- \+ *lemma* omega.sat_eq_elim
- \+ *def* omega.sgm
- \+ *def* omega.subst
- \+ *lemma* omega.subst_correct
- \+ *def* omega.sym_sym
- \+ *def* omega.symdiv
- \+ *def* omega.symmod
- \+ *lemma* omega.symmod_add_one_self
- \+ *lemma* omega.symmod_eq
- \+ *lemma* omega.unsat_of_unsat_eq_elim

Added src/tactic/omega/find_ees.lean
- \+ *def* omega.gcd

Added src/tactic/omega/find_scalars.lean


Added src/tactic/omega/int/dnf.lean
- \+ *lemma* omega.int.clauses_sat_dnf_core
- \+ *def* omega.int.dnf
- \+ *def* omega.int.dnf_core
- \+ *lemma* omega.int.exists_clause_holds
- \+ *lemma* omega.int.implies_neg_elim
- \+ *def* omega.int.is_nnf
- \+ *lemma* omega.int.is_nnf_nnf
- \+ *lemma* omega.int.is_nnf_push_neg
- \+ *lemma* omega.int.le_and_le_iff_eq
- \+ *def* omega.int.neg_elim
- \+ *def* omega.int.neg_free
- \+ *lemma* omega.int.neg_free_neg_elim
- \+ *def* omega.int.nnf
- \+ *lemma* omega.int.nnf_equiv
- \+ *def* omega.int.push_neg
- \+ *lemma* omega.int.push_neg_equiv
- \+ *lemma* omega.int.unsat_of_clauses_unsat

Added src/tactic/omega/int/form.lean
- \+ *def* omega.int.form.equiv
- \+ *def* omega.int.form.fresh_index
- \+ *def* omega.int.form.holds
- \+ *def* omega.int.form.implies
- \+ *def* omega.int.form.repr
- \+ *def* omega.int.form.sat
- \+ *lemma* omega.int.form.sat_of_implies_of_sat
- \+ *lemma* omega.int.form.sat_or
- \+ *def* omega.int.form.unsat
- \+ *def* omega.int.form.valid
- \+ *inductive* omega.int.form
- \+ *def* omega.int.univ_close
- \+ *lemma* omega.int.univ_close_of_valid
- \+ *lemma* omega.int.valid_of_unsat_not

Added src/tactic/omega/int/main.lean
- \+ *lemma* omega.int.univ_close_of_unsat_clausify

Added src/tactic/omega/int/preterm.lean
- \+ *def* omega.int.canonize
- \+ *def* omega.int.preterm.add_one
- \+ *def* omega.int.preterm.fresh_index
- \+ *def* omega.int.preterm.repr
- \+ *def* omega.int.preterm.val
- \+ *inductive* omega.int.preterm
- \+ *lemma* omega.int.val_canonize

Added src/tactic/omega/lin_comb.lean
- \+ *def* omega.lin_comb
- \+ *lemma* omega.lin_comb_holds
- \+ *def* omega.unsat_lin_comb
- \+ *lemma* omega.unsat_lin_comb_of
- \+ *lemma* omega.unsat_of_unsat_lin_comb

Added src/tactic/omega/main.lean


Added src/tactic/omega/misc.lean
- \+ *lemma* omega.fun_mono_2
- \+ *lemma* omega.pred_mono_2'
- \+ *lemma* omega.pred_mono_2
- \+ *def* omega.update
- \+ *lemma* omega.update_eq
- \+ *lemma* omega.update_eq_of_ne
- \+ *def* omega.update_zero

Added src/tactic/omega/nat/dnf.lean
- \+ *def* omega.nat.bools.or
- \+ *def* omega.nat.dnf
- \+ *def* omega.nat.dnf_core
- \+ *lemma* omega.nat.exists_clause_holds
- \+ *lemma* omega.nat.exists_clause_holds_core
- \+ *lemma* omega.nat.exists_clause_sat
- \+ *lemma* omega.nat.holds_nonneg_consts
- \+ *lemma* omega.nat.holds_nonneg_consts_core
- \+ *def* omega.nat.nonneg_consts
- \+ *def* omega.nat.nonneg_consts_core
- \+ *def* omega.nat.nonnegate
- \+ *def* omega.nat.term.vars
- \+ *def* omega.nat.term.vars_core
- \+ *def* omega.nat.terms.vars
- \+ *lemma* omega.nat.unsat_of_unsat_dnf

Added src/tactic/omega/nat/form.lean
- \+ *def* omega.nat.form.equiv
- \+ *def* omega.nat.form.fresh_index
- \+ *def* omega.nat.form.holds
- \+ *def* omega.nat.form.holds_constant
- \+ *def* omega.nat.form.implies
- \+ *def* omega.nat.form.neg_free
- \+ *def* omega.nat.form.repr
- \+ *def* omega.nat.form.sat
- \+ *lemma* omega.nat.form.sat_of_implies_of_sat
- \+ *lemma* omega.nat.form.sat_or
- \+ *def* omega.nat.form.sub_free
- \+ *def* omega.nat.form.unsat
- \+ *def* omega.nat.form.valid
- \+ *inductive* omega.nat.form
- \+ *def* omega.nat.univ_close
- \+ *lemma* omega.nat.univ_close_of_valid
- \+ *lemma* omega.nat.valid_of_unsat_not

Added src/tactic/omega/nat/main.lean
- \+ *lemma* omega.nat.univ_close_of_unsat_neg_elim_not

Added src/tactic/omega/nat/neg_elim.lean
- \+ *lemma* omega.nat.implies_neg_elim
- \+ *lemma* omega.nat.implies_neg_elim_core
- \+ *def* omega.nat.is_nnf
- \+ *lemma* omega.nat.is_nnf_nnf
- \+ *lemma* omega.nat.is_nnf_push_neg
- \+ *lemma* omega.nat.le_and_le_iff_eq
- \+ *def* omega.nat.neg_elim
- \+ *def* omega.nat.neg_elim_core
- \+ *lemma* omega.nat.neg_free_neg_elim
- \+ *lemma* omega.nat.neg_free_neg_elim_core
- \+ *def* omega.nat.nnf
- \+ *lemma* omega.nat.nnf_equiv
- \+ *def* omega.nat.push_neg
- \+ *lemma* omega.nat.push_neg_equiv

Added src/tactic/omega/nat/preterm.lean
- \+ *def* omega.nat.canonize
- \+ *def* omega.nat.preterm.add_one
- \+ *def* omega.nat.preterm.fresh_index
- \+ *def* omega.nat.preterm.repr
- \+ *def* omega.nat.preterm.sub_free
- \+ *def* omega.nat.preterm.val
- \+ *lemma* omega.nat.preterm.val_add
- \+ *lemma* omega.nat.preterm.val_const
- \+ *def* omega.nat.preterm.val_constant
- \+ *lemma* omega.nat.preterm.val_sub
- \+ *lemma* omega.nat.preterm.val_var
- \+ *inductive* omega.nat.preterm
- \+ *lemma* omega.nat.val_canonize

Added src/tactic/omega/nat/sub_elim.lean
- \+ *def* omega.nat.form.sub_subst
- \+ *def* omega.nat.form.sub_terms
- \+ *lemma* omega.nat.holds_is_diff
- \+ *def* omega.nat.is_diff
- \+ *def* omega.nat.preterm.sub_subst
- \+ *def* omega.nat.preterm.sub_terms
- \+ *lemma* omega.nat.preterm.val_sub_subst
- \+ *lemma* omega.nat.sat_sub_elim
- \+ *def* omega.nat.sub_elim
- \+ *def* omega.nat.sub_elim_core
- \+ *def* omega.nat.sub_fresh_index
- \+ *lemma* omega.nat.sub_subst_equiv
- \+ *lemma* omega.nat.unsat_of_unsat_sub_elim

Added src/tactic/omega/prove_unsats.lean
- \+ *lemma* omega.forall_mem_repeat_zero_eq_zero

Added src/tactic/omega/term.lean
- \+ *def* omega.term.add
- \+ *def* omega.term.div
- \+ *def* omega.term.fresh_index
- \+ *def* omega.term.mul
- \+ *def* omega.term.neg
- \+ *def* omega.term.sub
- \+ *def* omega.term.val
- \+ *lemma* omega.term.val_add
- \+ *lemma* omega.term.val_div
- \+ *lemma* omega.term.val_mul
- \+ *lemma* omega.term.val_neg
- \+ *lemma* omega.term.val_sub
- \+ *def* omega.term
- \+ *def* omega.terms.fresh_index

Added test/omega.lean




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
- \+ *def* decidable.lt_by_cases

Modified src/data/equiv/basic.lean
- \+ *def* equiv.subtype_congr_right
- \+ *lemma* equiv.subtype_congr_right_mk

Modified src/data/fin.lean
- \+ *def* {u}

Modified src/data/nat/basic.lean
- \+ *lemma* nat.add_sub_cancel_right

Modified src/data/subtype.lean
- \+ *def* subtype.coind
- \+ *theorem* subtype.coind_injective
- \+ *lemma* subtype.map_injective
- \+ *def* subtype.restrict
- \+ *lemma* subtype.restrict_apply
- \+ *lemma* subtype.restrict_def
- \+ *lemma* subtype.restrict_injective
- \+/\- *theorem* subtype.val_injective

Modified src/logic/basic.lean
- \+ *lemma* congr_arg2

Modified src/logic/embedding.lean


Modified src/order/basic.lean
- \+ *def* bounded
- \+ *lemma* trans_trichotomous_left
- \+ *lemma* trans_trichotomous_right
- \+ *def* unbounded

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
- \+ *theorem* finset.card_powerset_len
- \+ *theorem* finset.mem_powerset_len
- \+ *def* finset.powerset_len
- \+ *theorem* finset.powerset_len_mono

Modified src/data/list/basic.lean
- \+ *theorem* list.append_sublist_append
- \+ *lemma* list.length_of_sublists_len
- \+ *lemma* list.length_sublists_len
- \+ *lemma* list.mem_sublists_len
- \+ *lemma* list.mem_sublists_len_self
- \+ *lemma* list.nodup_sublists_len
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

Modified src/data/multiset.lean
- \+ *theorem* multiset.card_powerset_len
- \+ *theorem* multiset.mem_powerset_len
- \+ *theorem* multiset.mem_powerset_len_aux
- \+ *theorem* multiset.nodup_powerset_len
- \+ *def* multiset.powerset_len
- \+ *def* multiset.powerset_len_aux
- \+ *theorem* multiset.powerset_len_aux_cons
- \+ *theorem* multiset.powerset_len_aux_eq_map_coe
- \+ *theorem* multiset.powerset_len_aux_nil
- \+ *theorem* multiset.powerset_len_aux_perm
- \+ *theorem* multiset.powerset_len_aux_zero
- \+ *theorem* multiset.powerset_len_coe'
- \+ *theorem* multiset.powerset_len_coe
- \+ *theorem* multiset.powerset_len_cons
- \+ *theorem* multiset.powerset_len_le_powerset
- \+ *theorem* multiset.powerset_len_mono
- \+ *theorem* multiset.powerset_len_zero_left
- \+ *theorem* multiset.powerset_len_zero_right

Modified src/data/nat/basic.lean
- \+ *def* nat.choose
- \+ *theorem* nat.choose_eq_fact_div_fact
- \+ *lemma* nat.choose_eq_zero_of_lt
- \+ *lemma* nat.choose_mul_fact_mul_fact
- \+ *lemma* nat.choose_one_right
- \+ *lemma* nat.choose_pos
- \+ *lemma* nat.choose_self
- \+ *lemma* nat.choose_succ_self
- \+ *lemma* nat.choose_succ_succ
- \+ *lemma* nat.choose_zero_right
- \+ *lemma* nat.choose_zero_succ
- \+ *theorem* nat.fact_mul_fact_dvd_fact
- \+ *lemma* nat.succ_mul_choose_eq

Modified src/data/nat/choose.lean
- \- *def* choose
- \- *theorem* choose_eq_fact_div_fact
- \- *lemma* choose_eq_zero_of_lt
- \- *lemma* choose_mul_fact_mul_fact
- \- *lemma* choose_one_right
- \- *lemma* choose_pos
- \- *lemma* choose_self
- \- *lemma* choose_succ_self
- \- *lemma* choose_succ_succ
- \- *lemma* choose_zero_right
- \- *lemma* choose_zero_succ
- \- *theorem* fact_mul_fact_dvd_fact
- \- *lemma* succ_mul_choose_eq

Modified src/ring_theory/ideal_operations.lean




## [2019-04-16 16:32:52](https://github.com/leanprover-community/mathlib/commit/8985a43)
feat(data/set/intervals): some interval lemmas ([#942](https://github.com/leanprover-community/mathlib/pull/942))
* feat(data/set/intervals): a few more lemmas
* one-liners
#### Estimated changes
Modified src/data/set/intervals.lean
- \+ *lemma* set.Ioc_self
- \+ *lemma* set.Ioc_subset_Ioc
- \+ *lemma* set.Ioc_subset_Ioc_left
- \+ *lemma* set.Ioc_subset_Ioc_right
- \+ *lemma* set.left_mem_Icc
- \+ *lemma* set.left_mem_Ico
- \+ *lemma* set.left_mem_Ioc
- \+ *lemma* set.left_mem_Ioo
- \+ *lemma* set.right_mem_Icc
- \+ *lemma* set.right_mem_Ico
- \+ *lemma* set.right_mem_Ioc
- \+ *lemma* set.right_mem_Ioo



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
Added src/category_theory/instances/Top/adjunctions.lean
- \+ *def* category_theory.instances.Top.adj₁
- \+ *def* category_theory.instances.Top.adj₂

Added src/category_theory/instances/Top/basic.lean
- \+ *def* category_theory.instances.Top.discrete
- \+ *def* category_theory.instances.Top.trivial
- \+ *def* category_theory.instances.Top

Added src/category_theory/instances/Top/default.lean


Added src/category_theory/instances/Top/limits.lean
- \+ *def* category_theory.instances.Top.colimit
- \+ *def* category_theory.instances.Top.colimit_is_colimit
- \+ *def* category_theory.instances.Top.limit
- \+ *def* category_theory.instances.Top.limit_is_limit

Added src/category_theory/instances/Top/open_nhds.lean
- \+ *def* topological_space.open_nhds.inclusion
- \+ *def* topological_space.open_nhds.inclusion_map_iso
- \+ *lemma* topological_space.open_nhds.inclusion_map_iso_hom
- \+ *lemma* topological_space.open_nhds.inclusion_map_iso_inv
- \+ *lemma* topological_space.open_nhds.inclusion_obj
- \+ *def* topological_space.open_nhds.map
- \+ *lemma* topological_space.open_nhds.map_id_obj'
- \+ *lemma* topological_space.open_nhds.map_id_obj
- \+ *lemma* topological_space.open_nhds.map_id_obj_unop
- \+ *lemma* topological_space.open_nhds.op_map_id_obj
- \+ *def* topological_space.open_nhds.open_nhds

Added src/category_theory/instances/Top/opens.lean
- \+ *def* topological_space.opens.map
- \+ *def* topological_space.opens.map_comp
- \+ *lemma* topological_space.opens.map_comp_hom_app
- \+ *lemma* topological_space.opens.map_comp_inv_app
- \+ *lemma* topological_space.opens.map_comp_obj'
- \+ *lemma* topological_space.opens.map_comp_obj
- \+ *lemma* topological_space.opens.map_comp_obj_unop
- \+ *def* topological_space.opens.map_id
- \+ *lemma* topological_space.opens.map_id_hom_app
- \+ *lemma* topological_space.opens.map_id_inv_app
- \+ *lemma* topological_space.opens.map_id_obj'
- \+ *lemma* topological_space.opens.map_id_obj
- \+ *lemma* topological_space.opens.map_id_obj_unop
- \+ *def* topological_space.opens.map_iso
- \+ *lemma* topological_space.opens.map_iso_hom_app
- \+ *lemma* topological_space.opens.map_iso_inv_app
- \+ *lemma* topological_space.opens.map_iso_refl
- \+ *lemma* topological_space.opens.op_map_comp_obj
- \+ *lemma* topological_space.opens.op_map_id_obj

Modified src/category_theory/instances/measurable_space.lean


Deleted src/category_theory/instances/topological_spaces.lean
- \- *def* category_theory.instances.Top.adj₁
- \- *def* category_theory.instances.Top.adj₂
- \- *def* category_theory.instances.Top.colimit
- \- *def* category_theory.instances.Top.colimit_is_colimit
- \- *def* category_theory.instances.Top.discrete
- \- *def* category_theory.instances.Top.limit
- \- *def* category_theory.instances.Top.limit_is_limit
- \- *def* category_theory.instances.Top.trivial
- \- *def* category_theory.instances.Top
- \- *def* category_theory.instances.nbhd
- \- *def* category_theory.instances.nbhds
- \- *def* topological_space.opens.map
- \- *def* topological_space.opens.map_id
- \- *lemma* topological_space.opens.map_id_obj
- \- *def* topological_space.opens.map_iso
- \- *def* topological_space.opens.map_iso_id



## [2019-04-15 19:41:40](https://github.com/leanprover-community/mathlib/commit/5f04e76)
feat(nat/basic): add some basic nat inequality lemmas ([#937](https://github.com/leanprover-community/mathlib/pull/937))
* feat(nat/basic): add some basic nat inequality lemmas, useful as specific cases of existing ring cases since uses less hypothesis
* feat(nat/basic): add some basic nat inequality lemmas, with convention fixes
* feat(nat/basic): add some basic nat inequality lemmas, with convention fixes
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.le_mul_of_pos_left
- \+ *lemma* nat.le_mul_of_pos_right
- \+ *lemma* nat.lt_of_div_lt_div



## [2019-04-15 19:09:47](https://github.com/leanprover-community/mathlib/commit/d06eb85)
feat(topology/algebra/continuous_functions): the ring of continuous functions ([#923](https://github.com/leanprover-community/mathlib/pull/923))
* feat(topology/algebra/continuous_functions): the ring of continuous functions
* filling in the hierarchy
* use to_additive
#### Estimated changes
Added src/topology/algebra/continuous_functions.lean




## [2019-04-14 19:26:36-04:00](https://github.com/leanprover-community/mathlib/commit/ca5d4c1)
feat(scripts): disable testing the install scripts in external PRs ([#936](https://github.com/leanprover-community/mathlib/pull/936))
#### Estimated changes
Modified .travis.yml




## [2019-04-14 15:16:28+01:00](https://github.com/leanprover-community/mathlib/commit/a1b7dcd)
fix(algebra/big_operators): change variables in finset.prod_map to remove spurious [comm_monoid β] ([#934](https://github.com/leanprover-community/mathlib/pull/934))
The old version involved maps α → β → γ and an instance [comm_monoid γ], but there was also a section variable [comm_monoid β].  In applications of this lemma it is not necessary, and not usually true, that β is a monoid.  Change the statement to involve maps α → γ → β so that we already have a monoid structure on the last variable and we do not make spurious assumptions about the second one.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* finset.prod_map



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
Added src/algebra/free.lean
- \+ *def* free_magma.length
- \+ *def* free_magma.lift
- \+ *lemma* free_magma.lift_mul
- \+ *lemma* free_magma.lift_of
- \+ *theorem* free_magma.lift_unique
- \+ *def* free_magma.map
- \+ *lemma* free_magma.map_mul'
- \+ *lemma* free_magma.map_mul
- \+ *lemma* free_magma.map_of
- \+ *lemma* free_magma.map_pure
- \+ *lemma* free_magma.mul_bind
- \+ *lemma* free_magma.mul_map_seq
- \+ *lemma* free_magma.mul_seq
- \+ *lemma* free_magma.pure_bind
- \+ *lemma* free_magma.pure_seq
- \+ *def* free_magma.repr'
- \+ *lemma* free_magma.traverse_eq
- \+ *lemma* free_magma.traverse_mul'
- \+ *lemma* free_magma.traverse_mul
- \+ *lemma* free_magma.traverse_pure'
- \+ *lemma* free_magma.traverse_pure
- \+ *inductive* free_magma
- \+ *def* free_semigroup.lift'
- \+ *def* free_semigroup.lift
- \+ *lemma* free_semigroup.lift_mul
- \+ *lemma* free_semigroup.lift_of
- \+ *lemma* free_semigroup.lift_of_mul
- \+ *theorem* free_semigroup.lift_unique
- \+ *def* free_semigroup.map
- \+ *lemma* free_semigroup.map_mul'
- \+ *lemma* free_semigroup.map_mul
- \+ *lemma* free_semigroup.map_of
- \+ *lemma* free_semigroup.map_pure
- \+ *lemma* free_semigroup.mul_bind
- \+ *lemma* free_semigroup.mul_map_seq
- \+ *lemma* free_semigroup.mul_seq
- \+ *def* free_semigroup.of
- \+ *lemma* free_semigroup.pure_bind
- \+ *lemma* free_semigroup.pure_seq
- \+ *def* free_semigroup.traverse'
- \+ *lemma* free_semigroup.traverse_eq
- \+ *lemma* free_semigroup.traverse_mul'
- \+ *lemma* free_semigroup.traverse_mul
- \+ *lemma* free_semigroup.traverse_pure'
- \+ *lemma* free_semigroup.traverse_pure
- \+ *def* free_semigroup
- \+ *def* free_semigroup_free_magma
- \+ *lemma* free_semigroup_free_magma_mul
- \+ *def* magma.free_semigroup.lift
- \+ *lemma* magma.free_semigroup.lift_mul
- \+ *lemma* magma.free_semigroup.lift_of
- \+ *theorem* magma.free_semigroup.lift_unique
- \+ *def* magma.free_semigroup.map
- \+ *lemma* magma.free_semigroup.map_mul
- \+ *lemma* magma.free_semigroup.map_of
- \+ *def* magma.free_semigroup.of
- \+ *theorem* magma.free_semigroup.of_mul
- \+ *theorem* magma.free_semigroup.of_mul_assoc
- \+ *theorem* magma.free_semigroup.of_mul_assoc_left
- \+ *theorem* magma.free_semigroup.of_mul_assoc_right
- \+ *inductive* magma.free_semigroup.r
- \+ *def* magma.free_semigroup
- \+ *def* semigroup.free_monoid.lift
- \+ *lemma* semigroup.free_monoid.lift_mul
- \+ *lemma* semigroup.free_monoid.lift_of
- \+ *lemma* semigroup.free_monoid.lift_one
- \+ *theorem* semigroup.free_monoid.lift_unique
- \+ *def* semigroup.free_monoid.map
- \+ *lemma* semigroup.free_monoid.map_mul
- \+ *lemma* semigroup.free_monoid.map_of
- \+ *def* semigroup.free_monoid.of
- \+ *lemma* semigroup.free_monoid.of_mul
- \+ *def* semigroup.free_monoid



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
- \+ *lemma* category_theory.bundled.coe_id

Modified src/category_theory/eq_to_hom.lean
- \+ *lemma* category_theory.eq_to_hom_op

Modified src/category_theory/equivalence.lean


Modified src/category_theory/functor_category.lean


Modified src/category_theory/natural_isomorphism.lean
- \+ *lemma* category_theory.nat_iso.hom_inv_id_app
- \+ *lemma* category_theory.nat_iso.inv_hom_id_app

Modified src/category_theory/opposites.lean
- \+ *lemma* category_theory.op_id_unop
- \+ *lemma* category_theory.unop_id_op



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
- \- *lemma* has_sum_iff_vanishing_norm
- \- *lemma* has_sum_of_has_sum_norm
- \- *lemma* has_sum_of_norm_bounded
- \+/\- *lemma* norm_tsum_le_tsum_norm
- \+ *lemma* summable_iff_vanishing_norm
- \+ *lemma* summable_of_norm_bounded
- \+ *lemma* summable_of_summable_norm

Modified src/analysis/specific_limits.lean
- \+ *lemma* has_sum_geometric
- \+ *lemma* has_sum_geometric_two
- \- *lemma* has_sum_of_absolute_convergence_real
- \- *lemma* is_sum_geometric
- \- *lemma* is_sum_geometric_two
- \+ *lemma* summable_of_absolute_convergence_real

Modified src/measure_theory/probability_mass_function.lean
- \- *lemma* pmf.has_sum_coe
- \+ *lemma* pmf.has_sum_coe_one
- \- *lemma* pmf.is_sum_coe_one
- \+/\- *def* pmf.pure
- \+ *lemma* pmf.summable_coe
- \+/\- *lemma* pmf.tsum_coe
- \+/\- *def* {u}

Modified src/topology/algebra/infinite_sum.lean
- \- *lemma* cauchy_seq_of_has_sum_dist
- \+ *lemma* cauchy_seq_of_summable_dist
- \+/\- *def* has_sum
- \+/\- *lemma* has_sum_add
- \- *lemma* has_sum_comp_of_has_sum_of_injective
- \+ *lemma* has_sum_hom
- \- *lemma* has_sum_iff_cauchy
- \+ *lemma* has_sum_iff_has_sum
- \- *lemma* has_sum_iff_has_sum_ne_zero
- \- *lemma* has_sum_iff_has_sum_ne_zero_bij
- \+ *lemma* has_sum_iff_has_sum_of_iso
- \+ *lemma* has_sum_iff_has_sum_of_ne_zero
- \+ *lemma* has_sum_iff_has_sum_of_ne_zero_bij
- \+ *lemma* has_sum_iff_of_summable
- \- *lemma* has_sum_iff_vanishing
- \+ *lemma* has_sum_ite_eq
- \+ *lemma* has_sum_le
- \+ *lemma* has_sum_le_inj
- \+/\- *lemma* has_sum_mul_left
- \+/\- *lemma* has_sum_mul_right
- \+/\- *lemma* has_sum_neg
- \+ *lemma* has_sum_of_has_sum
- \+ *lemma* has_sum_of_has_sum_ne_zero
- \- *lemma* has_sum_of_has_sum_of_sub
- \+ *lemma* has_sum_of_iso
- \+/\- *lemma* has_sum_sigma
- \- *lemma* has_sum_spec
- \+/\- *lemma* has_sum_sub
- \+/\- *lemma* has_sum_sum
- \+/\- *lemma* has_sum_sum_of_ne_finset_zero
- \+ *lemma* has_sum_tsum
- \+ *lemma* has_sum_unique
- \+/\- *lemma* has_sum_zero
- \- *def* is_sum
- \- *lemma* is_sum_add
- \- *lemma* is_sum_hom
- \- *lemma* is_sum_iff_is_sum
- \- *lemma* is_sum_iff_is_sum_of_iso
- \- *lemma* is_sum_iff_is_sum_of_ne_zero
- \- *lemma* is_sum_iff_is_sum_of_ne_zero_bij
- \- *lemma* is_sum_iff_of_has_sum
- \- *lemma* is_sum_ite_eq
- \- *lemma* is_sum_le
- \- *lemma* is_sum_le_inj
- \- *lemma* is_sum_mul_left
- \- *lemma* is_sum_mul_right
- \- *lemma* is_sum_neg
- \- *lemma* is_sum_of_is_sum
- \- *lemma* is_sum_of_is_sum_ne_zero
- \- *lemma* is_sum_of_iso
- \- *lemma* is_sum_sigma
- \- *lemma* is_sum_sub
- \- *lemma* is_sum_sum
- \- *lemma* is_sum_sum_of_ne_finset_zero
- \- *lemma* is_sum_tsum
- \- *lemma* is_sum_unique
- \- *lemma* is_sum_zero
- \+ *def* summable
- \+ *lemma* summable_add
- \+ *lemma* summable_comp_of_summable_of_injective
- \+ *lemma* summable_iff_cauchy
- \+ *lemma* summable_iff_summable_ne_zero
- \+ *lemma* summable_iff_summable_ne_zero_bij
- \+ *lemma* summable_iff_vanishing
- \+ *lemma* summable_mul_left
- \+ *lemma* summable_mul_right
- \+ *lemma* summable_neg
- \+ *lemma* summable_of_summable_of_sub
- \+ *lemma* summable_sigma
- \+ *lemma* summable_spec
- \+ *lemma* summable_sub
- \+ *lemma* summable_sum
- \+ *lemma* summable_sum_of_ne_finset_zero
- \+ *lemma* summable_zero
- \+ *lemma* tendsto_sum_nat_of_has_sum
- \- *lemma* tendsto_sum_nat_of_is_sum
- \+/\- *def* tsum
- \+/\- *lemma* tsum_add
- \+ *lemma* tsum_eq_has_sum
- \- *lemma* tsum_eq_is_sum
- \+ *lemma* tsum_eq_tsum_of_has_sum_iff_has_sum
- \- *lemma* tsum_eq_tsum_of_is_sum_iff_is_sum
- \+/\- *lemma* tsum_le_tsum
- \+/\- *lemma* tsum_mul_left
- \+/\- *lemma* tsum_mul_right
- \+/\- *lemma* tsum_neg
- \+/\- *lemma* tsum_sub
- \+/\- *lemma* tsum_sum
- \+/\- *lemma* tsum_zero

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.has_sum_iff_tendsto_nat
- \- *lemma* ennreal.is_sum_iff_tendsto_nat
- \+ *lemma* has_sum_iff_tendsto_nat_of_nonneg
- \- *lemma* has_sum_of_nonneg_of_le
- \- *lemma* is_sum_iff_tendsto_nat_of_nonneg
- \+ *lemma* nnreal.exists_le_has_sum_of_le
- \- *lemma* nnreal.exists_le_is_sum_of_le
- \+ *lemma* nnreal.has_sum_iff_tendsto_nat
- \- *lemma* nnreal.has_sum_of_le
- \- *lemma* nnreal.is_sum_iff_tendsto_nat
- \+ *lemma* nnreal.summable_of_le
- \+ *lemma* summable_of_nonneg_of_le

Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* nnreal.has_sum_coe
- \- *lemma* nnreal.is_sum_coe
- \+ *lemma* nnreal.summable_coe
- \+/\- *lemma* nnreal.tsum_coe



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
- \+/\- *def* category_theory.comma.map_left
- \+/\- *def* category_theory.comma.map_left_comp
- \+/\- *def* category_theory.comma.map_right
- \+/\- *def* category_theory.comma.map_right_comp
- \+/\- *def* category_theory.comma.nat_trans

Modified src/category_theory/discrete_category.lean


Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/functor_category.lean
- \+/\- *lemma* category_theory.functor.category.id_app
- \+/\- *lemma* category_theory.functor.category.nat_trans.app_naturality
- \+/\- *lemma* category_theory.functor.category.nat_trans.naturality_app

Modified src/category_theory/limits/cones.lean
- \+/\- *lemma* category_theory.functor.cocones_obj

Modified src/category_theory/limits/limits.lean
- \+/\- *def* category_theory.limits.is_colimit.hom_iso
- \+/\- *def* category_theory.limits.is_limit.hom_iso

Modified src/category_theory/limits/types.lean
- \+/\- *lemma* category_theory.limits.types.types_colimit_map
- \+/\- *lemma* category_theory.limits.types.types_limit_map

Modified src/category_theory/natural_isomorphism.lean
- \- *lemma* category_theory.nat_iso.hom_vcomp_inv
- \- *lemma* category_theory.nat_iso.inv_vcomp_hom

Modified src/category_theory/natural_transformation.lean
- \+/\- *lemma* category_theory.nat_trans.congr_app
- \+/\- *lemma* category_theory.nat_trans.exchange
- \+/\- *lemma* category_theory.nat_trans.ext
- \+/\- *def* category_theory.nat_trans.hcomp
- \+/\- *lemma* category_theory.nat_trans.hcomp_app
- \+/\- *def* category_theory.nat_trans.vcomp
- \+/\- *lemma* category_theory.nat_trans.vcomp_app
- \+/\- *lemma* category_theory.nat_trans.vcomp_assoc

Modified src/category_theory/products.lean
- \+/\- *def* category_theory.nat_trans.prod
- \+/\- *lemma* category_theory.nat_trans.prod_app

Modified src/category_theory/types.lean
- \+ *lemma* category_theory.functor_to_types.comp
- \- *lemma* category_theory.functor_to_types.vcomp

Modified src/category_theory/whiskering.lean
- \+/\- *lemma* category_theory.whisker_left.app
- \+/\- *def* category_theory.whisker_left
- \+ *lemma* category_theory.whisker_left_comp
- \+/\- *lemma* category_theory.whisker_left_twice
- \- *lemma* category_theory.whisker_left_vcomp
- \+/\- *lemma* category_theory.whisker_right.app
- \+/\- *def* category_theory.whisker_right
- \+ *lemma* category_theory.whisker_right_comp
- \+/\- *lemma* category_theory.whisker_right_left
- \+/\- *lemma* category_theory.whisker_right_twice
- \- *lemma* category_theory.whisker_right_vcomp
- \+/\- *lemma* category_theory.whiskering_left_map_app_app
- \+/\- *lemma* category_theory.whiskering_left_obj_map
- \+/\- *lemma* category_theory.whiskering_right_map_app_app
- \+/\- *lemma* category_theory.whiskering_right_obj_map

Modified src/category_theory/yoneda.lean
- \+/\- *def* category_theory.yoneda_sections
- \+/\- *def* category_theory.yoneda_sections_small



## [2019-04-10 06:48:16](https://github.com/leanprover-community/mathlib/commit/f04535d)
feat(category_theory): iso_whisker_(left|right) ([#908](https://github.com/leanprover-community/mathlib/pull/908))
* feat(category_theory): iso_whisker_(left|right)
* oops, use old notation for now
* update after merge
#### Estimated changes
Modified src/category_theory/whiskering.lean
- \+ *def* category_theory.iso_whisker_left
- \+ *lemma* category_theory.iso_whisker_left_hom
- \+ *lemma* category_theory.iso_whisker_left_inv
- \+ *def* category_theory.iso_whisker_right
- \+ *lemma* category_theory.iso_whisker_right_hom
- \+ *lemma* category_theory.iso_whisker_right_inv



## [2019-04-10 02:08:58](https://github.com/leanprover-community/mathlib/commit/86bd577)
refactor(algebra/group): is_monoid_hom extends is_mul_hom  ([#915](https://github.com/leanprover-community/mathlib/pull/915))
* refactor(algebra/group): is_monoid_hom extends is_mul_hom
* Fix build
#### Estimated changes
Modified src/algebra/group.lean
- \+ *lemma* is_add_monoid_hom.map_add
- \+ *lemma* is_monoid_hom.map_mul

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
- \+ *def* set.inclusion
- \+ *lemma* set.inclusion_inclusion
- \+ *lemma* set.inclusion_injective
- \+ *lemma* set.inclusion_self

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
- \+ *def* category_theory.functor.map_iso
- \+ *lemma* category_theory.functor.map_iso_hom
- \+ *lemma* category_theory.functor.map_iso_inv
- \- *def* category_theory.functor.on_iso
- \- *lemma* category_theory.functor.on_iso_hom
- \- *lemma* category_theory.functor.on_iso_inv
- \+ *lemma* category_theory.iso.symm_mk
- \+ *lemma* category_theory.iso.trans_mk

Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/category_theory/whiskering.lean
- \+ *lemma* category_theory.whisker_left_id'
- \+ *lemma* category_theory.whisker_right_id'
- \+ *lemma* category_theory.whiskering_left_map_app_app
- \+ *lemma* category_theory.whiskering_left_obj_map
- \+ *lemma* category_theory.whiskering_left_obj_obj
- \+ *lemma* category_theory.whiskering_right_map_app_app
- \+ *lemma* category_theory.whiskering_right_obj_map
- \+ *lemma* category_theory.whiskering_right_obj_obj



## [2019-04-09 22:44:04](https://github.com/leanprover-community/mathlib/commit/d692499)
reorganising category_theory/instances/rings.lean ([#909](https://github.com/leanprover-community/mathlib/pull/909))
#### Estimated changes
Added src/category_theory/instances/CommRing/adjunctions.lean
- \+ *lemma* category_theory.instances.CommRing.polynomial_ring_map_val
- \+ *lemma* category_theory.instances.CommRing.polynomial_ring_obj_α

Renamed src/category_theory/instances/rings.lean to src/category_theory/instances/CommRing/basic.lean
- \- *lemma* category_theory.instances.CommRing.polynomial_map_val
- \- *lemma* category_theory.instances.CommRing.polynomial_obj_α

Added src/category_theory/instances/CommRing/default.lean




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
- \+ *theorem* is_group_anti_hom.map_prod
- \- *theorem* is_group_anti_hom.prod
- \+ *lemma* is_group_hom.map_multiset_prod
- \+ *theorem* is_group_hom.map_prod
- \- *lemma* is_group_hom.multiset_prod
- \- *theorem* is_group_hom.prod

Modified src/algebra/direct_sum.lean


Modified src/algebra/group.lean
- \+ *lemma* is_add_group_hom.map_sub
- \+/\- *lemma* is_add_group_hom.sub
- \- *lemma* is_add_group_hom_sub
- \- *theorem* is_group_anti_hom.inv
- \+ *theorem* is_group_anti_hom.map_inv
- \+ *theorem* is_group_anti_hom.map_one
- \- *theorem* is_group_anti_hom.one
- \+ *lemma* is_group_hom.inv
- \- *theorem* is_group_hom.inv
- \+ *theorem* is_group_hom.map_inv
- \+ *theorem* is_group_hom.map_one
- \+ *lemma* is_group_hom.mul
- \- *theorem* is_group_hom.one
- \- *lemma* is_group_hom_inv
- \- *lemma* is_group_hom_mul

Modified src/algebra/group_power.lean
- \+/\- *theorem* is_add_group_hom.gsmul
- \+ *theorem* is_add_group_hom.map_gsmul
- \+ *theorem* is_add_group_hom.map_smul
- \- *theorem* is_add_group_hom.smul
- \- *theorem* is_add_group_hom_gsmul
- \- *theorem* is_group_hom.gpow
- \+ *theorem* is_group_hom.map_gpow
- \+ *theorem* is_group_hom.map_pow
- \- *theorem* is_group_hom.pow

Modified src/analysis/complex/exponential.lean
- \+/\- *lemma* real.angle.coe_gsmul

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


Added src/order/lexicographic.lean
- \+ *def* lex



## [2019-04-08 22:25:36+01:00](https://github.com/leanprover-community/mathlib/commit/29507a4)
feat(group_theory/subgroup): subtype.add_comm_group ([#903](https://github.com/leanprover-community/mathlib/pull/903))
#### Estimated changes
Modified src/group_theory/subgroup.lean




## [2019-04-08 17:11:21](https://github.com/leanprover-community/mathlib/commit/ec51b6e)
feat(category_theory/colimits): missing simp lemmas ([#894](https://github.com/leanprover-community/mathlib/pull/894))
#### Estimated changes
Modified src/category_theory/limits/limits.lean
- \+ *lemma* category_theory.limits.colim.ι_map_assoc
- \+ *lemma* category_theory.limits.colimit.ι_desc_assoc
- \+ *lemma* category_theory.limits.colimit.ι_post_assoc
- \+ *lemma* category_theory.limits.colimit.ι_pre_assoc



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
- \+ *theorem* linear_map.ker_eq_bot'

Modified src/linear_algebra/basis.lean
- \+ *lemma* is_basis.repr_total

Modified src/linear_algebra/dimension.lean
- \+ *lemma* exists_is_basis_fintype
- \+ *theorem* linear_equiv.dim_eq_lift

Added src/linear_algebra/dual.lean
- \+ *def* is_basis.coord_fun
- \+ *lemma* is_basis.coord_fun_eq_repr
- \+ *def* is_basis.dual_basis
- \+ *theorem* is_basis.dual_basis_is_basis
- \+ *theorem* is_basis.dual_dim_eq
- \+ *theorem* is_basis.dual_lin_independent
- \+ *def* is_basis.eval_lc_at
- \+ *def* is_basis.to_dual
- \+ *lemma* is_basis.to_dual_apply
- \+ *lemma* is_basis.to_dual_eq_repr
- \+ *def* is_basis.to_dual_equiv
- \+ *def* is_basis.to_dual_flip
- \+ *lemma* is_basis.to_dual_inj
- \+ *theorem* is_basis.to_dual_ker
- \+ *theorem* is_basis.to_dual_range
- \+ *lemma* is_basis.to_dual_swap_eq_to_dual
- \+ *lemma* is_basis.to_dual_to_dual
- \+ *def* module.dual.eval
- \+ *lemma* module.dual.eval_apply
- \+ *def* module.dual
- \+ *theorem* vector_space.dual_dim_eq
- \+ *def* vector_space.eval_equiv
- \+ *theorem* vector_space.eval_ker
- \+ *lemma* vector_space.eval_range



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


Added src/analysis/complex/polynomial.lean
- \+ *lemma* complex.exists_forall_abs_polynomial_eval_le
- \+ *lemma* complex.exists_root

Modified src/data/real/pi.lean


Modified src/topology/instances/polynomial.lean
- \+ *lemma* polynomial.tendsto_infinity



## [2019-04-07 23:05:06-04:00](https://github.com/leanprover-community/mathlib/commit/4fecb10)
feat(topology/gromov_hausdorff): the Gromov-Hausdorff space ([#883](https://github.com/leanprover-community/mathlib/pull/883))
#### Estimated changes
Added src/topology/metric_space/gromov_hausdorff.lean
- \+ *def* Gromov_Hausdorff.GH_dist
- \+ *theorem* Gromov_Hausdorff.GH_dist_eq_Hausdorff_dist
- \+ *theorem* Gromov_Hausdorff.GH_dist_le_Hausdorff_dist
- \+ *theorem* Gromov_Hausdorff.GH_dist_le_nonempty_compacts_dist
- \+ *theorem* Gromov_Hausdorff.GH_dist_le_of_approx_subsets
- \+ *lemma* Gromov_Hausdorff.GH_space.to_GH_space_rep
- \+ *lemma* Gromov_Hausdorff.Hausdorff_dist_optimal
- \+ *def* Gromov_Hausdorff.aux_gluing
- \+ *structure* Gromov_Hausdorff.aux_gluing_struct
- \+ *lemma* Gromov_Hausdorff.dist_GH_dist
- \+ *lemma* Gromov_Hausdorff.eq_to_GH_space
- \+ *lemma* Gromov_Hausdorff.eq_to_GH_space_iff
- \+ *lemma* Gromov_Hausdorff.second_countable
- \+ *lemma* Gromov_Hausdorff.to_GH_space_continuous
- \+ *lemma* Gromov_Hausdorff.to_GH_space_eq_to_GH_space_iff_isometric
- \+ *lemma* Gromov_Hausdorff.to_GH_space_lipschitz
- \+ *lemma* Gromov_Hausdorff.totally_bounded

Added src/topology/metric_space/gromov_hausdorff_realized.lean
- \+ *def* Gromov_Hausdorff.HD
- \+ *lemma* Gromov_Hausdorff.HD_below_aux1
- \+ *lemma* Gromov_Hausdorff.HD_below_aux2
- \+ *lemma* Gromov_Hausdorff.HD_candidates_b_dist_le
- \+ *lemma* Gromov_Hausdorff.Hausdorff_dist_optimal_le_HD
- \+ *def* Gromov_Hausdorff.candidates
- \+ *def* Gromov_Hausdorff.candidates_b_dist
- \+ *lemma* Gromov_Hausdorff.candidates_b_dist_mem_candidates_b
- \+ *def* Gromov_Hausdorff.candidates_b_of_candidates
- \+ *lemma* Gromov_Hausdorff.candidates_b_of_candidates_mem
- \+ *lemma* Gromov_Hausdorff.isometry_optimal_GH_injl
- \+ *lemma* Gromov_Hausdorff.isometry_optimal_GH_injr
- \+ *def* Gromov_Hausdorff.optimal_GH_injl
- \+ *def* Gromov_Hausdorff.optimal_GH_injr
- \+ *def* Gromov_Hausdorff.premetric_optimal_GH_dist

Modified src/topology/metric_space/isometry.lean
- \+ *def* Kuratowski_embedding.Kuratowski_embedding
- \+ *lemma* Kuratowski_embedding.Kuratowski_embedding_isometry
- \+ *def* Kuratowski_embedding.embedding_of_subset
- \+ *lemma* Kuratowski_embedding.embedding_of_subset_coe
- \+ *lemma* Kuratowski_embedding.embedding_of_subset_dist_le
- \+ *lemma* Kuratowski_embedding.embedding_of_subset_isometry
- \+ *theorem* Kuratowski_embedding.exists_isometric_embedding
- \+ *def* Kuratowski_embedding.nonempty_compacts.Kuratowski_embedding
- \+ *def* Kuratowski_embedding.ℓ_infty_ℝ



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
- \- *def* category_theory.limits.has_colimits
- \- *def* category_theory.limits.has_colimits_of_shape
- \- *def* category_theory.limits.has_limits
- \- *def* category_theory.limits.has_limits_of_shape

Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/preserves.lean
- \- *def* category_theory.limits.preserves_colimits
- \- *def* category_theory.limits.preserves_colimits_of_shape
- \- *def* category_theory.limits.preserves_limits
- \- *def* category_theory.limits.preserves_limits_of_shape
- \- *def* category_theory.limits.reflects_colimits
- \- *def* category_theory.limits.reflects_colimits_of_shape
- \- *def* category_theory.limits.reflects_limits
- \- *def* category_theory.limits.reflects_limits_of_shape

Modified src/category_theory/limits/types.lean




## [2019-04-07 19:36:21+02:00](https://github.com/leanprover-community/mathlib/commit/483a6c2)
feat(data/list/min_max): add minimum ([#892](https://github.com/leanprover-community/mathlib/pull/892))
#### Estimated changes
Modified src/data/list/min_max.lean
- \+ *theorem* list.le_minimum_aux_of_mem
- \+ *theorem* list.le_minimum_of_mem
- \+ *theorem* list.le_of_foldl_min
- \+ *theorem* list.le_of_foldr_min
- \+ *theorem* list.mem_foldl_min
- \+ *theorem* list.mem_foldr_min
- \+ *theorem* list.mem_minimum
- \+ *theorem* list.mem_minimum_aux
- \+ *def* list.minimum
- \+ *def* list.minimum_aux
- \+ *def* list.minimum_aux_cons
- \+ *def* list.minimum_cons
- \+ *def* list.minimum_singleton



## [2019-04-07 16:29:19](https://github.com/leanprover-community/mathlib/commit/891c050)
feat(subgroup, subring, subfield): directed Unions of subrings are subrings ([#889](https://github.com/leanprover-community/mathlib/pull/889))
#### Estimated changes
Modified src/field_theory/subfield.lean
- \+ *lemma* is_subfield_Union_of_directed

Modified src/group_theory/subgroup.lean
- \+ *lemma* is_subgroup_Union_of_directed

Modified src/group_theory/submonoid.lean
- \+ *lemma* is_add_submonoid_Union_of_directed
- \+ *lemma* is_submonoid_Union_of_directed

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
- \+ *theorem* nat.sub_cancel



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
- \+ *lemma* is_linear_map.map_add
- \+ *lemma* is_linear_map.map_neg
- \+ *lemma* is_linear_map.map_sub
- \+ *lemma* is_linear_map.map_zero

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* exists_norm_lt_one
- \+ *lemma* exists_one_lt_norm
- \+ *lemma* norm_fpow
- \+/\- *lemma* norm_pos_iff
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
- \+ *lemma* bdd_above_range_norm_image_div_norm
- \- *lemma* bounded_by_operator_norm_on_unit_ball
- \- *lemma* bounded_by_operator_norm_on_unit_vector
- \+ *lemma* bounded_linear_maps.coe_zero
- \+ *lemma* bounded_linear_maps.map_zero
- \+ *lemma* bounded_linear_maps.one_smul
- \+ *lemma* bounded_linear_maps.smul_coe
- \+ *lemma* bounded_linear_maps.zero_smul
- \- *lemma* exists_bound'
- \+/\- *lemma* exists_bound
- \- *lemma* norm_of_unit_ball_bdd_above
- \+/\- *lemma* operator_norm_bounded_by
- \+/\- *theorem* operator_norm_homogeneous
- \+ *lemma* operator_norm_homogeneous_le
- \+/\- *theorem* operator_norm_triangle
- \+ *def* to_linear_map
- \- *lemma* zero_in_im_ball



## [2019-04-06 15:56:00-04:00](https://github.com/leanprover-community/mathlib/commit/8831e0a)
chore(mergify): require the AppVeyor build to succeed
#### Estimated changes
Modified .mergify.yml




## [2019-04-06 15:08:22-04:00](https://github.com/leanprover-community/mathlib/commit/8fa071f)
fix(scripts): not all files were deployed through the curl command ([#879](https://github.com/leanprover-community/mathlib/pull/879))
#### Estimated changes
Modified .travis.yml


Modified README.md


Added appveyor.yml


Modified scripts/remote-install-update-mathlib.sh


Modified scripts/setup-dev-scripts.sh


Modified scripts/update-mathlib.py




## [2019-04-06 18:45:57](https://github.com/leanprover-community/mathlib/commit/8d45ccb)
feat(category_theory/bifunctor): simp lemmas ([#867](https://github.com/leanprover-community/mathlib/pull/867))
* feat(category_theory/bifunctor): simp lemmas
* remove need for @, thanks Kenny and Chris!
#### Estimated changes
Added src/category_theory/bifunctor.lean
- \+ *lemma* category_theory.bifunctor.diagonal'
- \+ *lemma* category_theory.bifunctor.diagonal
- \+ *lemma* category_theory.bifunctor.map_comp_id
- \+ *lemma* category_theory.bifunctor.map_id
- \+ *lemma* category_theory.bifunctor.map_id_comp



## [2019-04-06 16:52:11](https://github.com/leanprover-community/mathlib/commit/3360f98)
more general hypotheses for integer induction ([#885](https://github.com/leanprover-community/mathlib/pull/885))
#### Estimated changes
Modified src/data/int/basic.lean




## [2019-04-06 10:59:07-04:00](https://github.com/leanprover-community/mathlib/commit/d8a2bc5)
feat(algebra/opposites): opposites of operators ([#538](https://github.com/leanprover-community/mathlib/pull/538))
#### Estimated changes
Added src/algebra/opposites.lean
- \+ *def* opposite.op
- \+ *theorem* opposite.op_inj
- \+ *theorem* opposite.op_unop
- \+ *def* opposite.unop
- \+ *theorem* opposite.unop_inj
- \+ *theorem* opposite.unop_op
- \+ *def* opposite



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


Added scripts/leanpkg-example.toml


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
Added src/data/mllist.lean


Added test/mllist.lean
- \+ *def* F
- \+ *def* S
- \+ *def* append



## [2019-04-05 06:30:13](https://github.com/leanprover-community/mathlib/commit/44d1c7a)
feat(list.split_on): [1,1,2,3,2,4,4].split_on 2 = [[1,1],[3],[4,4]] ([#866](https://github.com/leanprover-community/mathlib/pull/866))
#### Estimated changes
Modified src/data/list/defs.lean
- \+ *def* list.split_on
- \+ *def* list.split_on_p
- \+ *def* list.split_on_p_aux



## [2019-04-05 06:11:40](https://github.com/leanprover-community/mathlib/commit/901bdbf)
feat(data/list/min_max): minimum and maximum over list ([#884](https://github.com/leanprover-community/mathlib/pull/884))
* feat(data/list/min_max): minimum and maximum over list
* Update min_max.lean
* replace semicolons
#### Estimated changes
Added src/data/list/min_max.lean
- \+ *theorem* list.le_maximum_aux_of_mem
- \+ *theorem* list.le_maximum_of_mem
- \+ *theorem* list.le_of_foldl_max
- \+ *theorem* list.le_of_foldr_max
- \+ *def* list.maximum
- \+ *def* list.maximum_aux
- \+ *def* list.maximum_aux_cons
- \+ *def* list.maximum_cons
- \+ *def* list.maximum_singleton
- \+ *theorem* list.mem_foldl_max
- \+ *theorem* list.mem_foldr_max
- \+ *theorem* list.mem_maximum
- \+ *theorem* list.mem_maximum_aux



## [2019-04-05 04:01:15](https://github.com/leanprover-community/mathlib/commit/858d111)
feat(data/matrix): more basic matrix lemmas ([#873](https://github.com/leanprover-community/mathlib/pull/873))
* feat(data/matrix): more basic matrix lemmas
* feat(data/matrix): transpose_add
#### Estimated changes
Modified src/data/matrix.lean
- \+/\- *theorem* matrix.add_mul
- \+/\- *theorem* matrix.mul_add
- \+ *theorem* matrix.mul_neg
- \+ *lemma* matrix.mul_smul
- \+/\- *theorem* matrix.mul_zero
- \+ *theorem* matrix.neg_mul
- \+ *lemma* matrix.smul_mul
- \+ *lemma* matrix.transpose_add
- \+ *lemma* matrix.transpose_mul
- \+ *lemma* matrix.transpose_neg
- \+ *lemma* matrix.transpose_transpose
- \+ *lemma* matrix.transpose_zero
- \+/\- *theorem* matrix.zero_mul



## [2019-04-05 03:14:12](https://github.com/leanprover-community/mathlib/commit/0b7ee1b)
feat(category_theory): introduce the core of a category ([#832](https://github.com/leanprover-community/mathlib/pull/832))
#### Estimated changes
Added src/category_theory/core.lean
- \+ *lemma* category_theory.core.comp_hom
- \+ *def* category_theory.core.forget_functor_to_core
- \+ *def* category_theory.core.functor_to_core
- \+ *lemma* category_theory.core.id_hom
- \+ *def* category_theory.core.inclusion
- \+ *def* category_theory.core

Modified src/category_theory/isomorphism.lean
- \+ *lemma* category_theory.functor.map_hom_inv
- \+ *lemma* category_theory.functor.map_inv_hom



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
- \+ *lemma* char_p.cast_eq_mod
- \+ *theorem* char_p.char_is_prime
- \+ *theorem* char_p.char_is_prime_of_ge_two
- \+ *theorem* char_p.char_is_prime_or_zero
- \+ *theorem* char_p.char_ne_one
- \+ *theorem* char_p.char_ne_zero_of_fintype
- \+ *lemma* char_p.char_p_to_char_zero

Modified src/algebra/module.lean
- \+ *def* is_ring_hom.to_module

Modified src/data/zmod/basic.lean
- \+ *def* zmod.cast

Added src/field_theory/finite_card.lean
- \+ *theorem* finite_field.card'
- \+ *theorem* finite_field.card

Modified src/linear_algebra/basis.lean
- \+ *theorem* vector_space.card_fintype'
- \+ *theorem* vector_space.card_fintype



## [2019-04-04 16:28:11-04:00](https://github.com/leanprover-community/mathlib/commit/3abfda0)
chore(github/pr): enable code owners
#### Estimated changes
Added CODEOWNERS




## [2019-04-04 19:04:48](https://github.com/leanprover-community/mathlib/commit/8183a5a)
feat(data/list/perm): nil_subperm ([#882](https://github.com/leanprover-community/mathlib/pull/882))
#### Estimated changes
Modified src/data/list/perm.lean
- \+ *theorem* list.nil_subperm



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
Added .mergify.yml


Modified README.md




## [2019-04-03 08:10:21-04:00](https://github.com/leanprover-community/mathlib/commit/a0cbe3b)
feat(data/fin): add `fin.clamp` ([#874](https://github.com/leanprover-community/mathlib/pull/874))
#### Estimated changes
Modified src/data/fin.lean
- \+/\- *def* fin.cast
- \+ *lemma* fin.cast_val
- \+ *def* fin.clamp
- \+ *lemma* fin.clamp_val



## [2019-04-03 05:37:35-04:00](https://github.com/leanprover-community/mathlib/commit/2c735dc)
feat(ring_theory/algebra_operations): submodules form a semiring ([#856](https://github.com/leanprover-community/mathlib/pull/856))
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* set.pointwise_mul_finite

Modified src/ring_theory/algebra_operations.lean
- \- *theorem* algebra.bot_mul
- \- *theorem* algebra.fg_mul
- \- *theorem* algebra.mul_bot
- \- *theorem* algebra.mul_le
- \- *theorem* algebra.mul_le_mul
- \- *theorem* algebra.mul_le_mul_left
- \- *theorem* algebra.mul_le_mul_right
- \- *theorem* algebra.mul_mem_mul
- \- *theorem* algebra.mul_mem_mul_rev
- \- *theorem* algebra.mul_sup
- \- *theorem* algebra.span_mul_span
- \- *theorem* algebra.sup_mul
- \+ *theorem* submodule.bot_mul
- \+ *theorem* submodule.mul_bot
- \+ *theorem* submodule.mul_le
- \+ *theorem* submodule.mul_le_mul
- \+ *theorem* submodule.mul_le_mul_left
- \+ *theorem* submodule.mul_le_mul_right
- \+ *theorem* submodule.mul_mem_mul
- \+ *theorem* submodule.mul_mem_mul_rev
- \+ *theorem* submodule.mul_sup
- \+ *theorem* submodule.one_eq_map_top
- \+ *theorem* submodule.one_eq_span
- \+ *theorem* submodule.one_le
- \+ *theorem* submodule.span_mul_span
- \+ *theorem* submodule.sup_mul

Modified src/ring_theory/ideal_operations.lean
- \+/\- *lemma* ideal.one_eq_top
- \+/\- *theorem* submodule.bot_smul
- \+/\- *theorem* submodule.smul_bot
- \+/\- *theorem* submodule.top_smul

Modified src/ring_theory/noetherian.lean
- \+ *theorem* submodule.fg_mul



## [2019-04-03 05:35:05-04:00](https://github.com/leanprover-community/mathlib/commit/b9e9328)
feat(topology/metric_space/completion): completion of metric spaces ([#743](https://github.com/leanprover-community/mathlib/pull/743))
#### Estimated changes
Added src/topology/metric_space/completion.lean
- \+ *lemma* metric.completion.coe_isometry



## [2019-04-03 09:38:15+02:00](https://github.com/leanprover-community/mathlib/commit/c3aba26)
feat(topology/uniform_space/pi): indexed products of uniform spaces ([#845](https://github.com/leanprover-community/mathlib/pull/845))
* feat(topology/uniform_space/pi): indexed products of uniform spaces
* fix(topology/uniform_space/pi): defeq topology
* fix(src/topology/uniform_space/pi): typo
Co-Authored-By: PatrickMassot <patrickmassot@free.fr>
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+/\- *theorem* uniformity_prod

Added src/topology/uniform_space/pi.lean
- \+ *lemma* Pi.uniform_continuous_proj
- \+ *lemma* Pi.uniform_space_topology
- \+ *lemma* Pi.uniformity



## [2019-04-03 02:27:59-04:00](https://github.com/leanprover-community/mathlib/commit/7043a4a)
feat(algebra/pointwise): pointwise addition and multiplication of sets ([#854](https://github.com/leanprover-community/mathlib/pull/854))
#### Estimated changes
Added src/algebra/pointwise.lean
- \+ *lemma* set.empty_pointwise_mul
- \+ *lemma* set.mem_pointwise_mul
- \+ *lemma* set.mem_pointwise_one
- \+ *lemma* set.mul_mem_pointwise_mul
- \+ *def* set.pointwise_add_add_monoid
- \+ *def* set.pointwise_add_add_semigroup
- \+ *def* set.pointwise_inv
- \+ *def* set.pointwise_mul
- \+ *def* set.pointwise_mul_comm_semiring
- \+ *lemma* set.pointwise_mul_empty
- \+ *lemma* set.pointwise_mul_eq_image
- \+ *def* set.pointwise_mul_monoid
- \+ *def* set.pointwise_mul_semigroup
- \+ *def* set.pointwise_mul_semiring
- \+ *lemma* set.pointwise_mul_subset_mul
- \+ *lemma* set.pointwise_mul_union
- \+ *def* set.pointwise_one
- \+ *def* set.singleton.is_monoid_hom
- \+ *def* set.singleton.is_mul_hom
- \+ *lemma* set.union_pointwise_mul



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


Added scripts/lean_version.lean
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


Added scripts/detect_errors.py


Modified travis_long.sh




## [2019-04-02 11:22:44-04:00](https://github.com/leanprover-community/mathlib/commit/13034ba)
feat(tactic/local_cache): add tactic-block-local caching mechanism ([#837](https://github.com/leanprover-community/mathlib/pull/837))
#### Estimated changes
Modified src/meta/expr.lean
- \+ *def* name.from_components

Modified src/tactic/basic.lean


Added src/tactic/local_cache.lean
- \+ *def* tactic.local_cache.internal.def_local.FNV_OFFSET_BASIS
- \+ *def* tactic.local_cache.internal.def_local.FNV_PRIME
- \+ *def* tactic.local_cache.internal.def_local.RADIX
- \+ *def* tactic.local_cache.internal.def_local.hash_byte
- \+ *def* tactic.local_cache.internal.def_local.hash_string

Added test/local_cache.lean
- \+ *def* block_local.TEST_NS_1
- \+ *def* block_local.TEST_NS_2
- \+ *structure* block_local.dummy
- \+ *def* block_local.my_def_1
- \+ *def* block_local.my_def_2
- \+ *def* block_local.my_definition'
- \+ *def* block_local.my_definition
- \+ *lemma* block_local.my_lemma'
- \+ *lemma* block_local.my_lemma
- \+ *lemma* block_local.my_lemma_1
- \+ *lemma* block_local.my_lemma_2
- \+ *lemma* block_local.my_lemma_3
- \+ *lemma* block_local.my_test_ns
- \+ *lemma* block_local.my_test_ps
- \+ *def* collision.TEST_NS
- \+ *lemma* collision.my_lemma_1
- \+ *lemma* collision.my_lemma_2
- \+ *lemma* collision.my_lemma_3
- \+ *lemma* collision.my_lemma_4
- \+ *def* def_local.TEST_NS_1
- \+ *def* def_local.TEST_NS_2
- \+ *structure* def_local.dummy
- \+ *def* def_local.my_def_1
- \+ *def* def_local.my_def_2
- \+ *def* def_local.my_definition'
- \+ *def* def_local.my_definition
- \+ *lemma* def_local.my_lemma'
- \+ *lemma* def_local.my_lemma
- \+ *lemma* def_local.my_lemma_1
- \+ *lemma* def_local.my_lemma_2
- \+ *lemma* def_local.my_lemma_3
- \+ *lemma* def_local.my_test_ns
- \+ *lemma* def_local.my_test_ps



## [2019-04-02 10:44:43-04:00](https://github.com/leanprover-community/mathlib/commit/7eac178)
fix(scripts/update-mathlib): protect file operations from interrupts ([#864](https://github.com/leanprover-community/mathlib/pull/864))
#### Estimated changes
Modified .gitignore


Added scripts/auth_github.py


Modified scripts/cache-olean.py


Added scripts/delayed_interrupt.py


Modified scripts/setup-dev-scripts.sh


Modified scripts/update-mathlib.py




## [2019-04-02 08:23:50-05:00](https://github.com/leanprover-community/mathlib/commit/f385ad6)
Inductive limit of metric spaces ([#732](https://github.com/leanprover-community/mathlib/pull/732))
#### Estimated changes
Modified src/topology/metric_space/gluing.lean
- \+ *def* metric.inductive_limit
- \+ *def* metric.inductive_limit_dist
- \+ *lemma* metric.inductive_limit_dist_eq_dist
- \+ *def* metric.inductive_premetric
- \+ *def* metric.to_inductive_limit
- \+ *lemma* metric.to_inductive_limit_commute
- \+ *lemma* metric.to_inductive_limit_isometry



## [2019-04-02 07:57:52-04:00](https://github.com/leanprover-community/mathlib/commit/727120c)
fix(build): improve compatibility of caching scripts with Sourcetree ([#863](https://github.com/leanprover-community/mathlib/pull/863))
#### Estimated changes
Modified scripts/post-checkout


Modified scripts/post-commit




## [2019-04-01 20:04:58-05:00](https://github.com/leanprover-community/mathlib/commit/5694d15)
feat(data/nat/basic): nat.le_rec_on ([#585](https://github.com/leanprover-community/mathlib/pull/585))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *def* nat.le_rec_on
- \+ *theorem* nat.le_rec_on_injective
- \+ *theorem* nat.le_rec_on_self
- \+ *theorem* nat.le_rec_on_succ'
- \+ *theorem* nat.le_rec_on_succ
- \+ *theorem* nat.le_rec_on_surjective
- \+ *theorem* nat.le_rec_on_trans
- \+ *theorem* nat.of_le_succ



## [2019-04-01 18:55:36-04:00](https://github.com/leanprover-community/mathlib/commit/8e4542d)
Merge branch 'congr-2'
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/interactive.lean


Added src/tactic/push_neg.lean
- \+ *theorem* push_neg.classical.implies_iff_not_or
- \+ *theorem* push_neg.not_and_eq
- \+ *theorem* push_neg.not_eq
- \+ *theorem* push_neg.not_exists_eq
- \+ *theorem* push_neg.not_forall_eq
- \+ *theorem* push_neg.not_implies_eq
- \+ *theorem* push_neg.not_le_eq
- \+ *theorem* push_neg.not_lt_eq
- \+ *theorem* push_neg.not_not_eq
- \+ *theorem* push_neg.not_or_eq

Added test/push_neg.lean




## [2019-04-01 18:52:21-04:00](https://github.com/leanprover-community/mathlib/commit/ec0a4ea)
fix(tactic/congr'): some `\iff` goals were erroneously rejected
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/interactive.lean


Deleted src/tactic/push_neg.lean
- \- *theorem* push_neg.classical.implies_iff_not_or
- \- *theorem* push_neg.not_and_eq
- \- *theorem* push_neg.not_eq
- \- *theorem* push_neg.not_exists_eq
- \- *theorem* push_neg.not_forall_eq
- \- *theorem* push_neg.not_implies_eq
- \- *theorem* push_neg.not_le_eq
- \- *theorem* push_neg.not_lt_eq
- \- *theorem* push_neg.not_not_eq
- \- *theorem* push_neg.not_or_eq

Deleted test/push_neg.lean




## [2019-04-01 16:48:53-04:00](https://github.com/leanprover-community/mathlib/commit/5fe470b)
feat(tactic/push_neg): a tactic pushing negations ([#853](https://github.com/leanprover-community/mathlib/pull/853))
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/interactive.lean


Added src/tactic/push_neg.lean
- \+ *theorem* push_neg.classical.implies_iff_not_or
- \+ *theorem* push_neg.not_and_eq
- \+ *theorem* push_neg.not_eq
- \+ *theorem* push_neg.not_exists_eq
- \+ *theorem* push_neg.not_forall_eq
- \+ *theorem* push_neg.not_implies_eq
- \+ *theorem* push_neg.not_le_eq
- \+ *theorem* push_neg.not_lt_eq
- \+ *theorem* push_neg.not_not_eq
- \+ *theorem* push_neg.not_or_eq

Added test/push_neg.lean




## [2019-04-01 16:21:09-04:00](https://github.com/leanprover-community/mathlib/commit/5995d46)
fix(build): prevent leanchecker from timing out
#### Estimated changes
Modified .travis.yml




## [2019-04-01 16:13:58-04:00](https://github.com/leanprover-community/mathlib/commit/2f088fc)
feat(category_theory): working in Sort rather than Type ([#824](https://github.com/leanprover-community/mathlib/pull/824))
#### Estimated changes
Modified src/category_theory/adjunction.lean


Modified src/category_theory/category.lean
- \+/\- *lemma* category_theory.End.mul_def
- \+/\- *lemma* category_theory.End.one_def
- \+/\- *abbreviation* category_theory.large_category
- \+/\- *abbreviation* category_theory.small_category

Modified src/category_theory/comma.lean
- \+/\- *def* category_theory.over
- \+/\- *def* category_theory.under

Modified src/category_theory/concrete_category.lean
- \+/\- *structure* category_theory.bundled
- \+/\- *def* category_theory.forget
- \+/\- *def* category_theory.mk_ob

Modified src/category_theory/const.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/equivalence.lean
- \+/\- *structure* category_theory.equivalence

Modified src/category_theory/full_subcategory.lean
- \+/\- *def* category_theory.induced_category

Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/functor.lean
- \+/\- *structure* category_theory.functor

Modified src/category_theory/functor_category.lean


Modified src/category_theory/groupoid.lean
- \+/\- *abbreviation* category_theory.large_groupoid
- \+/\- *abbreviation* category_theory.small_groupoid

Modified src/category_theory/instances/monoids.lean


Added src/category_theory/instances/rel.lean
- \+ *def* category_theory.rel

Modified src/category_theory/isomorphism.lean
- \+/\- *structure* category_theory.iso

Modified src/category_theory/limits/cones.lean
- \+ *lemma* category_theory.limits.cocone.extend_ι
- \+ *lemma* category_theory.limits.cone.extend_π

Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* category_theory.limits.colimit.map_post
- \+/\- *lemma* category_theory.limits.colimit.pre_post
- \+/\- *def* category_theory.limits.is_colimit.of_faithful
- \+/\- *def* category_theory.limits.is_limit.of_faithful
- \+/\- *lemma* category_theory.limits.limit.map_post
- \+/\- *lemma* category_theory.limits.limit.pre_post

Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/category_theory/natural_transformation.lean
- \+/\- *structure* category_theory.nat_trans

Modified src/category_theory/opposites.lean
- \+/\- *lemma* category_theory.functor.hom_obj
- \+/\- *lemma* category_theory.functor.hom_pairing_map
- \+/\- *lemma* category_theory.opposite.op_mul
- \+/\- *lemma* category_theory.opposite.op_one
- \+/\- *lemma* category_theory.opposite.unop_mul
- \+/\- *lemma* category_theory.opposite.unop_one
- \+/\- *def* category_theory.opposite

Modified src/category_theory/pempty.lean


Modified src/category_theory/products.lean


Modified src/category_theory/punit.lean


Modified src/category_theory/types.lean
- \+/\- *lemma* category_theory.types_comp
- \+/\- *lemma* category_theory.types_hom
- \+/\- *lemma* category_theory.types_id

Modified src/category_theory/whiskering.lean


Modified src/category_theory/yoneda.lean
- \+/\- *def* category_theory.coyoneda
- \+/\- *def* category_theory.yoneda



## [2019-04-01 22:07:28+02:00](https://github.com/leanprover-community/mathlib/commit/404e2c9)
add tutorial about zmod37 ([#767](https://github.com/leanprover-community/mathlib/pull/767))
Reference to a mathlib file which no longer exists has been fixed, and a more user-friendly example of an equivalence relation has been added in a tutorial.
#### Estimated changes
Modified docs/theories/relations.md


Added docs/tutorial/Zmod37.lean
- \+ *lemma* Zmod37.coe_add
- \+ *lemma* Zmod37.coe_mul
- \+ *lemma* Zmod37.coe_neg
- \+ *lemma* Zmod37.congr_add
- \+ *lemma* Zmod37.congr_neg
- \+ *theorem* Zmod37.of_int_one
- \+ *theorem* Zmod37.of_int_zero
- \+ *theorem* cong_mod_equiv
- \+ *theorem* cong_mod_refl
- \+ *theorem* cong_mod_symm
- \+ *theorem* cong_mod_trans



## [2019-04-01 21:58:17+02:00](https://github.com/leanprover-community/mathlib/commit/867661e)
docs(tactics): add introduction to the instance cache tactic section
#### Estimated changes
Modified docs/tactics.md




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
- \+ *lemma* real.sin_gt_sub_cube
- \+ *lemma* real.sin_lt

Modified src/data/complex/basic.lean
- \+ *lemma* complex.div_im
- \+ *lemma* complex.div_re

Modified src/data/complex/exponential.lean
- \+ *lemma* complex.cos_square
- \+ *lemma* complex.sin_square
- \+ *lemma* real.cos_square
- \+ *lemma* real.sin_square

Modified src/data/real/basic.lean
- \+/\- *theorem* real.le_mk_of_forall_le
- \+ *lemma* real.le_sqrt'
- \+ *lemma* real.le_sqrt
- \+ *lemma* real.le_sqrt_of_sqr_le
- \+/\- *theorem* real.mul_self_sqrt
- \+/\- *theorem* real.sqr_sqrt
- \+/\- *theorem* real.sqrt_div
- \+/\- *theorem* real.sqrt_eq_iff_mul_self_eq
- \+/\- *theorem* real.sqrt_eq_iff_sqr_eq
- \+/\- *theorem* real.sqrt_eq_zero'
- \+/\- *theorem* real.sqrt_eq_zero
- \+/\- *theorem* real.sqrt_eq_zero_of_nonpos
- \+/\- *theorem* real.sqrt_inj
- \+/\- *theorem* real.sqrt_le
- \+ *lemma* real.sqrt_le_left
- \+ *lemma* real.sqrt_le_sqrt
- \+/\- *theorem* real.sqrt_lt
- \+/\- *theorem* real.sqrt_mul
- \+/\- *theorem* real.sqrt_mul_self
- \+/\- *theorem* real.sqrt_pos
- \+/\- *theorem* real.sqrt_sqr

Added src/data/real/pi.lean
- \+ *lemma* real.cos_pi_div_eight
- \+ *lemma* real.cos_pi_div_four
- \+ *lemma* real.cos_pi_div_sixteen
- \+ *lemma* real.cos_pi_div_thirty_two
- \+ *lemma* real.cos_pi_over_two_pow
- \+ *lemma* real.pi_gt_314
- \+ *lemma* real.pi_gt_sqrt_two_add_series
- \+ *lemma* real.pi_gt_three
- \+ *lemma* real.pi_lt_315
- \+ *lemma* real.pi_lt_sqrt_two_add_series
- \+ *lemma* real.sin_pi_div_eight
- \+ *lemma* real.sin_pi_div_four
- \+ *lemma* real.sin_pi_div_sixteen
- \+ *lemma* real.sin_pi_div_thirty_two
- \+ *lemma* real.sin_pi_over_two_pow_succ
- \+ *lemma* real.sin_square_pi_over_two_pow
- \+ *lemma* real.sin_square_pi_over_two_pow_succ
- \+ *lemma* real.sqrt_two_add_series_lt_two
- \+ *lemma* real.sqrt_two_add_series_monotone_left
- \+ *lemma* real.sqrt_two_add_series_nonneg
- \+ *lemma* real.sqrt_two_add_series_one
- \+ *lemma* real.sqrt_two_add_series_step_down
- \+ *lemma* real.sqrt_two_add_series_step_up
- \+ *lemma* real.sqrt_two_add_series_succ
- \+ *lemma* real.sqrt_two_add_series_two
- \+ *lemma* real.sqrt_two_add_series_zero
- \+ *lemma* real.sqrt_two_add_series_zero_nonneg

