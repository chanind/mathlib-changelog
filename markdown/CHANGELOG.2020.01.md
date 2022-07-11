## [2020-01-31 17:07:56](https://github.com/leanprover-community/mathlib/commit/5ce0c0a)
feat(linear_algebra/matrix): Add proof that trace AB = trace BA, for matrices. ([#1913](https://github.com/leanprover-community/mathlib/pull/1913))
* feat(linear_algebra/matrix): trace AB = trace BA
* Remove now-redundant matrix.smul_sum
In a striking coincidence,
  https://github.com/leanprover-community/mathlib/pull/1910
was merged almost immediately before
  https://github.com/leanprover-community/mathlib/pull/1883
thus rendering matrix.smul_sum redundant.
* Make arguments explicit for matrix.trace, matrix.diag
* Tidy up whitespace
* Remove now-redundant type ascriptions
* Update src/linear_algebra/matrix.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Feedback from code review
* Generalize diag_transpose, trace_transpose.
With apologies to the CI for triggering another build :-/
* Explicit arguments trace, diag defs but not lemmas
#### Estimated changes
Modified src/linear_algebra/matrix.lean
- \+ *lemma* diag_transpose
- \+ *lemma* trace_transpose
- \+ *lemma* trace_transpose_mul
- \+ *lemma* trace_mul_comm
- \+/\- *def* diag
- \+/\- *def* trace



## [2020-01-31 14:13:56+01:00](https://github.com/leanprover-community/mathlib/commit/ddba2ae)
chore(scripts/nolints): regenerate
#### Estimated changes
Modified scripts/nolints.txt




## [2020-01-31 12:11:16](https://github.com/leanprover-community/mathlib/commit/a8ba81b)
feat(analysis/convex): define convex hull ([#1915](https://github.com/leanprover-community/mathlib/pull/1915))
* feat(analysis/convex): define convex hull
fixes [#1851](https://github.com/leanprover-community/mathlib/pull/1851)
* Fix compile
* Drop an unused argument
* Split line
* Rename some `_iff`s, drop others
* Mention `std_simplex` in the docs
* More docs
* Rename `α` to `ι`, other small fixes
* Use `range` instead of `f '' univ`
* More docs
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_sum_elim

Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/convex/basic.lean
- \+/\- *lemma* segment_symm
- \+/\- *lemma* left_mem_segment
- \+/\- *lemma* right_mem_segment
- \+ *lemma* segment_same
- \+ *lemma* segment_eq_image
- \+ *lemma* segment_eq_image'
- \+ *lemma* segment_eq_image₂
- \+/\- *lemma* segment_eq_Icc
- \+/\- *lemma* segment_eq_Icc'
- \+ *lemma* mem_segment_translate
- \+/\- *lemma* segment_translate_preimage
- \+/\- *lemma* segment_translate_image
- \+ *lemma* convex_iff_segment_subset
- \+ *lemma* convex.segment_subset
- \+ *lemma* convex_iff_pointwise_add_subset:
- \+/\- *lemma* convex_empty
- \+/\- *lemma* convex_singleton
- \+/\- *lemma* convex_univ
- \+/\- *lemma* convex.inter
- \+/\- *lemma* convex_sInter
- \+/\- *lemma* convex_Inter
- \+/\- *lemma* convex.prod
- \+/\- *lemma* convex.is_linear_image
- \+/\- *lemma* convex.linear_image
- \+/\- *lemma* convex.is_linear_preimage
- \+/\- *lemma* convex.linear_preimage
- \+/\- *lemma* convex.neg
- \+/\- *lemma* convex.neg_preimage
- \+/\- *lemma* convex.smul
- \+/\- *lemma* convex.smul_preimage
- \+/\- *lemma* convex.add
- \+/\- *lemma* convex.sub
- \+/\- *lemma* convex.translate
- \+/\- *lemma* convex.affinity
- \+/\- *lemma* convex_real_iff
- \+/\- *lemma* convex_segment
- \+/\- *lemma* convex_halfspace_lt
- \+/\- *lemma* convex_halfspace_le
- \+/\- *lemma* convex_halfspace_gt
- \+/\- *lemma* convex_halfspace_ge
- \+/\- *lemma* convex_hyperplane
- \+/\- *lemma* submodule.convex
- \+/\- *lemma* subspace.convex
- \+/\- *lemma* linear_order.convex_on_of_lt
- \+/\- *lemma* convex_on_real_of_slope_mono_adjacent
- \+/\- *lemma* convex_on.subset
- \+/\- *lemma* convex_on.add
- \+/\- *lemma* convex_on.smul
- \+ *lemma* convex_on.le_on_segment'
- \+ *lemma* convex_on.le_on_segment
- \+/\- *lemma* convex_on.convex_le
- \+/\- *lemma* convex_on.convex_lt
- \+/\- *lemma* convex_on.convex_epigraph
- \+/\- *lemma* convex_on_iff_convex_epigraph
- \+/\- *lemma* finset.center_mass_empty
- \+/\- *lemma* finset.center_mass_pair
- \+/\- *lemma* finset.center_mass_insert
- \+/\- *lemma* finset.center_mass_singleton
- \+ *lemma* finset.center_mass_eq_of_sum_1
- \+ *lemma* finset.center_mass_smul
- \+ *lemma* finset.center_mass_segment'
- \+ *lemma* finset.center_mass_segment
- \+ *lemma* finset.center_mass_ite_eq
- \+ *lemma* finset.center_mass_subset
- \+ *lemma* finset.center_mass_filter_ne_zero
- \+/\- *lemma* convex.center_mass_mem
- \+/\- *lemma* convex.sum_mem
- \+/\- *lemma* convex_on.map_center_mass_le
- \+/\- *lemma* convex_on.map_sum_le
- \+ *lemma* convex_on.exists_ge_of_center_mass
- \+ *lemma* subset_convex_hull
- \+ *lemma* convex_convex_hull
- \+ *lemma* convex_hull_min
- \+ *lemma* convex_hull_mono
- \+ *lemma* convex.convex_hull_eq
- \+ *lemma* is_linear_map.image_convex_hull
- \+ *lemma* linear_map.image_convex_hull
- \+ *lemma* finset.center_mass_mem_convex_hull
- \+ *lemma* convex_hull_eq
- \+ *lemma* convex_on.exists_ge_of_mem_convex_hull
- \+ *lemma* set.finite.convex_hull_eq
- \+ *lemma* is_linear_map.convex_hull_image
- \+ *lemma* linear_map.convex_hull_image
- \+ *lemma* std_simplex_eq_inter
- \+ *lemma* convex_std_simplex
- \+ *lemma* ite_eq_mem_std_simplex
- \+ *lemma* convex_hull_basis_eq_std_simplex
- \+ *lemma* set.finite.convex_hull_eq_image
- \+ *lemma* mem_Icc_of_mem_std_simplex
- \- *lemma* convex_iff:
- \- *lemma* convex_iff₂:
- \- *lemma* convex_iff₃:
- \- *lemma* mem_segment_iff
- \- *lemma* segment_eq_image_Icc_zero_one
- \- *lemma* mem_segment_iff'
- \- *lemma* segment_eq_image_Icc_zero_one'
- \- *lemma* segment_translate
- \- *lemma* convex_segment_iff
- \- *lemma* convex_on_iff
- \- *lemma* convex_on.le_on_interval
- \- *lemma* convex.interior
- \- *lemma* convex.closure
- \- *lemma* convex_on_dist
- \- *lemma* convex_ball
- \- *lemma* convex_closed_ball
- \+/\- *def* segment
- \+/\- *def* convex
- \+/\- *def* convex_on
- \+ *def* convex_hull
- \+ *def* std_simplex

Created src/analysis/convex/topology.lean
- \+ *lemma* std_simplex_subset_closed_ball
- \+ *lemma* bounded_std_simplex
- \+ *lemma* is_closed_std_simplex
- \+ *lemma* compact_std_simplex
- \+ *lemma* convex.interior
- \+ *lemma* convex.closure
- \+ *lemma* set.finite.compact_convex_hull
- \+ *lemma* set.finite.is_closed_convex_hull
- \+ *lemma* convex_on_dist
- \+ *lemma* convex_ball
- \+ *lemma* convex_closed_ball
- \+ *lemma* convex_hull_exists_dist_ge
- \+ *lemma* convex_hull_exists_dist_ge2
- \+ *lemma* convex_hull_ediam
- \+ *lemma* convex_hull_diam
- \+ *lemma* bounded_convex_hull

Modified src/analysis/normed_space/finite_dimension.lean
- \+/\- *theorem* linear_map.continuous_of_finite_dimensional
- \+/\- *def* linear_map.to_continuous_linear_map

Modified src/analysis/normed_space/real_inner_product.lean


Modified src/data/finset.lean
- \+ *lemma* filter_mem_eq_inter
- \+ *theorem* union_inter_cancel_left
- \+ *theorem* union_inter_cancel_right

Modified src/data/real/nnreal.lean
- \+ *lemma* div_one
- \+ *lemma* div_self

Modified src/geometry/manifold/real_instances.lean


Modified src/group_theory/group_action.lean
- \+ *lemma* ite_smul
- \+ *lemma* smul_ite

Modified src/measure_theory/outer_measure.lean


Modified src/topology/algebra/monoid.lean




## [2020-01-30 15:28:23-08:00](https://github.com/leanprover-community/mathlib/commit/cae9cc9)
chore(ci): remove unused olean-rs setup from build ([#1932](https://github.com/leanprover-community/mathlib/pull/1932))
#### Estimated changes
Modified .github/workflows/build.yml




## [2020-01-30 18:49:20](https://github.com/leanprover-community/mathlib/commit/80f5bd5)
feat(ci): build and push html documentation ([#1927](https://github.com/leanprover-community/mathlib/pull/1927))
* feat(ci): build and push html doc generation
* fix(scripts/deploy_docs): change from temporary doc repo
* chore(ci): re-enable check for deployment
* fix git add
* Update scripts/deploy_docs.sh
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* Update .github/workflows/build.yml
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* Update scripts/deploy_docs.sh
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* Update scripts/deploy_docs.sh
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* remove chmod line
* revert additional check for testing purposes
* is this the error?
Try a test build before I get to the office
* rmeove _test
* reapply author attribution change
* revert change for testing
* missing --
* revert email and name config
#### Estimated changes
Modified .github/workflows/build.yml


Created scripts/deploy_docs.sh




## [2020-01-30 17:24:56](https://github.com/leanprover-community/mathlib/commit/4c2d678)
fix(data/set/finite): finite.fintype is a def ([#1931](https://github.com/leanprover-community/mathlib/pull/1931))
#### Estimated changes
Modified src/data/set/finite.lean




## [2020-01-30 15:16:25](https://github.com/leanprover-community/mathlib/commit/b7e5f75)
fix(tactic/scc): detect Props ([#1930](https://github.com/leanprover-community/mathlib/pull/1930))
* fix(tactic/scc): detect Props
* test(test/tactics): add test
#### Estimated changes
Modified src/tactic/scc.lean


Modified test/tactics.lean




## [2020-01-30 13:41:06](https://github.com/leanprover-community/mathlib/commit/1bd23bf)
feat(tactic/use): apply exists_prop after use ([#1882](https://github.com/leanprover-community/mathlib/pull/1882))
* feat(tactic/use): apply exists_prop after use
* change implementation
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/interactive.lean




## [2020-01-30 11:13:26](https://github.com/leanprover-community/mathlib/commit/dcbc719)
fix(tactic/squeeze): compatibility with `simp [<-...]` ([#1923](https://github.com/leanprover-community/mathlib/pull/1923))
* Add polyfills to `squeeze_simp` which should ensure compatibility with Lean 3.4 and 3.5
* Use `decode_simp_arg_list` so `squeeze_simp` doesn't have to pattern-match
(Except of course for the polyfill `has_to_tactic_format simp_arg_type` instance...)
* Reword comment for `erase_simp_args`
#### Estimated changes
Modified src/tactic/squeeze.lean




## [2020-01-30 08:20:49](https://github.com/leanprover-community/mathlib/commit/9bc0178)
fix(tactic/finish): fix one classical leak, document another ([#1929](https://github.com/leanprover-community/mathlib/pull/1929))
* fix(tactic/finish): fix one classical leak, document another
* fix(src/tactic): deprecate intuitionistic versions in docstrings. Closes [#1927](https://github.com/leanprover-community/mathlib/pull/1927).
#### Estimated changes
Modified src/tactic/finish.lean




## [2020-01-30 00:09:21](https://github.com/leanprover-community/mathlib/commit/868333b)
feat(data/W): show finitely branching W types are encodable ([#1817](https://github.com/leanprover-community/mathlib/pull/1817))
* feat(data/equiv,data/fintype): an encodable fintype is equiv to a fin
* feat(data/W): finitely branching W types are encodable
* feat(archive/examples/prop_encodable): show a type of propositional formulas is encodable
* fix(data/W): remove unused type class argument
* fix(data/equiv): add two docstrings
* fix(*): multiple fixes from code review
#### Estimated changes
Created archive/examples/prop_encodable.lean
- \+ *def* mk_fn0
- \+ *def* mk_fn1
- \+ *def* mk_fn2

Created src/data/W.lean
- \+ *lemma* depth_pos
- \+ *lemma* depth_lt_depth_mk
- \+ *def* depth

Modified src/data/equiv/encodable.lean
- \+ *def* encode'

Modified src/data/equiv/list.lean
- \+ *theorem* mem_sorted_univ
- \+ *theorem* length_sorted_univ
- \+ *theorem* sorted_univ_nodup
- \+ *def* sorted_univ
- \+ *def* fintype_equiv_fin

Modified src/data/fintype.lean
- \+ *def* equiv_fin_of_forall_mem_list

Modified src/order/basic.lean




## [2020-01-29 18:36:33](https://github.com/leanprover-community/mathlib/commit/4ac87ab)
chore(category_theory): use the new @[ext] attribute on structures ([#1663](https://github.com/leanprover-community/mathlib/pull/1663))
* chore(category_theory): use the new @[ext] attribute on structures
* fixes
* unnecessary repeated exts
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean


Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/fully_faithful.lean


Modified src/category_theory/comma.lean
- \- *lemma* ext

Modified src/category_theory/limits/cones.lean
- \- *lemma* cone_morphism.ext
- \- *lemma* cocone_morphism.ext

Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/monad/algebra.lean
- \- *lemma* ext

Modified src/category_theory/natural_transformation.lean
- \- *lemma* ext

Modified src/category_theory/whiskering.lean


Modified src/category_theory/yoneda.lean




## [2020-01-29 17:00:12](https://github.com/leanprover-community/mathlib/commit/4aa3eee)
chore(*): add inhabited instances ([#1898](https://github.com/leanprover-community/mathlib/pull/1898))
* chore(*): add inhabited instances
* Fix linting errors.
#### Estimated changes
Modified scripts/nolints.txt


Modified src/algebra/associated.lean


Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/Group.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/continued_fractions/basic.lean
- \+ *def* of_integer

Modified src/algebra/direct_sum.lean


Modified src/algebra/free.lean


Modified src/algebra/group/free_monoid.lean
- \+/\- *lemma* free_monoid.one_def
- \+/\- *lemma* free_monoid.mul_def
- \- *lemma* free_add_monoid.zero_def
- \- *lemma* free_add_monoid.add_def
- \- *def* free_add_monoid

Modified src/algebra/group/hom.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/type_tags.lean


Modified src/algebra/group/units.lean


Modified src/algebra/group/with_one.lean


Modified src/algebra/module.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/normed_space/basic.lean


Modified src/category/fold.lean


Modified src/category_theory/category/Groupoid.lean


Modified src/category_theory/category/Rel.lean


Modified src/category_theory/discrete_category.lean


Modified src/computability/partrec_code.lean


Modified src/computability/turing_machine.lean


Modified src/data/buffer/basic.lean


Modified src/data/dlist/instances.lean


Modified src/data/equiv/algebra.lean


Modified src/data/finmap.lean


Modified src/data/fp/basic.lean


Modified src/data/hash_map.lean


Modified src/data/lazy_list2.lean
- \+ *def* mk
- \- *def* thunk.mk

Modified src/data/list/alist.lean
- \+ *lemma* ext_iff

Modified src/data/matrix/basic.lean


Modified src/data/mv_polynomial.lean


Modified src/data/nat/enat.lean


Modified src/data/nat/prime.lean


Modified src/data/num/basic.lean


Modified src/data/opposite.lean


Modified src/data/padics/padic_integers.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/pfun.lean


Modified src/data/pnat/basic.lean


Modified src/data/pnat/factors.lean


Modified src/data/pnat/xgcd.lean


Modified src/data/polynomial.lean


Modified src/data/quot.lean


Modified src/data/real/cau_seq.lean


Modified src/data/rel.lean


Modified src/data/semiquot.lean


Modified src/data/seq/computation.lean


Modified src/data/seq/seq.lean


Modified src/data/seq/wseq.lean


Modified src/data/stream/basic.lean


Modified src/data/tree.lean


Modified src/data/zmod/basic.lean


Modified src/data/zsqrtd/basic.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/field_theory/perfect_closure.lean


Modified src/group_theory/abelianization.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/free_abelian_group.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/monoid_localization.lean


Modified src/group_theory/submonoid.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/multilinear.lean


Modified src/linear_algebra/sesquilinear_form.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/logic/basic.lean


Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/measurable_space.lean


Modified src/meta/expr.lean


Modified src/meta/rb_map.lean


Modified src/order/bounded_lattice.lean


Modified src/order/filter/basic.lean


Modified src/order/filter/filter_product.lean


Modified src/order/lexicographic.lean


Modified src/order/pilex.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/free_ring.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/maps.lean


Modified src/ring_theory/power_series.lean


Modified src/set_theory/game.lean


Modified src/set_theory/lists.lean


Modified src/set_theory/ordinal.lean


Modified src/set_theory/ordinal_notation.lean


Modified src/set_theory/pgame.lean


Modified src/set_theory/surreal.lean


Modified src/set_theory/zfc.lean
- \+ *lemma* arity.equiv_const
- \+ *def* const

Modified src/tactic/abel.lean


Modified src/tactic/core.lean


Created src/tactic/derive_inhabited.lean


Modified src/tactic/explode.lean


Modified src/tactic/finish.lean


Modified src/tactic/linarith.lean


Modified src/tactic/lint.lean


Modified src/tactic/monotonicity/basic.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/omega/eq_elim.lean


Modified src/tactic/omega/find_ees.lean


Modified src/tactic/omega/int/form.lean


Modified src/tactic/omega/int/preterm.lean


Modified src/tactic/omega/nat/form.lean


Modified src/tactic/omega/nat/preterm.lean


Modified src/tactic/omega/term.lean


Modified src/tactic/rewrite_all/basic.lean


Modified src/tactic/ring.lean


Modified src/tactic/ring2.lean


Modified src/tactic/ring_exp.lean


Modified src/tactic/suggest.lean


Modified src/tactic/tfae.lean


Modified src/topology/algebra/module.lean


Modified src/topology/compact_open.lean


Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/opens.lean


Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/compare_reals.lean
- \+/\- *def* Q

Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/separation.lean




## [2020-01-28 21:32:29+01:00](https://github.com/leanprover-community/mathlib/commit/b368312)
fix(ci): set GITHUB_TOKEN environment variable for gothub ([#1920](https://github.com/leanprover-community/mathlib/pull/1920))
#### Estimated changes
Modified scripts/deploy_nightly.sh




## [2020-01-28 20:04:21+01:00](https://github.com/leanprover-community/mathlib/commit/99962ad)
fix(ci): unshallow repo before pushing nightly tags ([#1919](https://github.com/leanprover-community/mathlib/pull/1919))
#### Estimated changes
Modified scripts/deploy_nightly.sh




## [2020-01-28 18:53:21](https://github.com/leanprover-community/mathlib/commit/a948e31)
chore(analysis/convex): move to `analysis/convex/basic` ([#1918](https://github.com/leanprover-community/mathlib/pull/1918))
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean


Renamed src/analysis/convex.lean to src/analysis/convex/basic.lean


Modified src/analysis/normed_space/real_inner_product.lean




## [2020-01-28 18:27:54+01:00](https://github.com/leanprover-community/mathlib/commit/e36d7ec)
fix(ci): work around github hack
#### Estimated changes
Modified scripts/deploy_nightly.sh




## [2020-01-28 16:36:42+01:00](https://github.com/leanprover-community/mathlib/commit/8e0d47a)
fix(ci): try again to fix authentication
#### Estimated changes
Modified .github/workflows/build.yml


Modified scripts/deploy_nightly.sh




## [2020-01-28 14:09:28+01:00](https://github.com/leanprover-community/mathlib/commit/75743ac)
fix(scripts/deploy_nightly.sh): try to fix CI ([#1917](https://github.com/leanprover-community/mathlib/pull/1917))
#### Estimated changes
Modified scripts/deploy_nightly.sh




## [2020-01-28 11:49:19](https://github.com/leanprover-community/mathlib/commit/cafd193)
chore(*): use filter.eventually ([#1897](https://github.com/leanprover-community/mathlib/pull/1897))
* chore(*): use filter.eventually
* Update src/measure_theory/integration.lean
Co-Authored-By: Yury G. Kudryashov <urkud@ya.ru>
* Fix closeds.complete_space.
* Fix tendsto_integral_of_dominated_convergence
* Fix tendsto_exp_at_top
* Fix exists_norm_eq_infi_of_complete_convex
* Use obtain.
* Use filter.eventually_of_forall
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+/\- *theorem* is_O_zero_right_iff

Modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* deriv_congr_of_mem_nhds

Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* fderiv_congr_of_mem_nhds

Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/data/real/hyperreal.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/mfderiv.lean
- \+/\- *lemma* mfderiv_congr_of_mem_nhds

Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/integration.lean
- \+/\- *lemma* integral_congr

Modified src/measure_theory/measure_space.lean
- \+/\- *def* all_ae

Modified src/order/filter/basic.lean
- \+ *lemma* eventually_bot
- \+ *lemma* eventually_top
- \+ *lemma* eventually_sup
- \+ *lemma* eventually_Sup
- \+ *lemma* eventually_supr
- \+ *lemma* eventually_principal
- \+ *lemma* not_eventually
- \+ *lemma* not_frequently
- \+ *lemma* frequently_true_iff_ne_bot
- \+ *lemma* frequently_false
- \+ *lemma* frequently_bot
- \+ *lemma* frequently_top
- \+ *lemma* frequently_principal
- \+ *lemma* frequently_sup
- \+ *lemma* frequently_Sup
- \+ *lemma* frequently_supr
- \+/\- *lemma* tendsto_principal
- \+ *lemma* eventually_at_top
- \+ *lemma* eventually.exists_forall_of_at_top
- \+ *lemma* frequently_at_top
- \+ *lemma* frequently.forall_exists_of_at_top

Modified src/order/filter/extr.lean
- \+/\- *def* is_min_filter
- \+/\- *def* is_max_filter

Modified src/order/filter/filter_product.lean
- \+/\- *theorem* of_seq_fun
- \+/\- *theorem* of_seq_fun₂

Modified src/order/liminf_limsup.lean
- \+/\- *lemma* is_cobounded.mk
- \+/\- *theorem* limsup_eq
- \+/\- *theorem* liminf_eq
- \+/\- *theorem* Limsup_eq_infi_Sup
- \+/\- *theorem* limsup_eq_infi_supr
- \+/\- *theorem* Liminf_eq_supr_Inf
- \+/\- *theorem* liminf_eq_supr_infi
- \+/\- *def* is_bounded
- \+/\- *def* is_cobounded
- \+/\- *def* Limsup
- \+/\- *def* Liminf

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* lt_mem_nhds
- \+/\- *lemma* le_mem_nhds
- \+/\- *lemma* gt_mem_nhds
- \+/\- *lemma* ge_mem_nhds

Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/sequences.lean




## [2020-01-27 20:50:19](https://github.com/leanprover-community/mathlib/commit/bba8473)
feat(linear_algebra): Matrix inverses for square nonsingular matrices ([#1816](https://github.com/leanprover-community/mathlib/pull/1816))
* Prove that some matrices have inverses
* Finish the proof: show that the determinant is 0 if a column is repeated
* Show that nonsingular_inv is also a right inverse
* Cleanup and code movement
* Small lemmata on transpose
* WIP: some work on inverse matrices
* Code cleanup and documentation
* More cleanup and documentation
* Generalize det_zero_of_column_eq to remove the linear order assumption
* Fix linting issues.
* Unneeded import can be removed
* A little bit more cleanup
* Generalize nonsing_inv to any ring with inverse
* Improve comments for `nonsingular_inverse`
* Remove the less general `det_zero_of_column_eq_of_char_ne_two` proof
* Rename `cramer_map_val` -> `cramer_map_def`
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* whitespace
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* whitespace: indent tactic proofs
* More renaming `cramer_map_val` -> `cramer_map_def`
* `swap_mul_self_mul` can be a `simp` lemma
* Make parameter σ to `swap_mul_eq_iff` implicit
* Update usage of `function.update_same` and `function.update_noteq`
* Replace `det_permute` with `det_permutation`
Although the statement now gives the determinant of a permutation matrix,
the proof is easier if we write it as a permuted identity matrix.
Thus the proof is basically the same, except a different line showing that the
entries are the same.
* Re-introduce `matrix.det_permute` (now based on `matrix.det_permutation`)
* Delete `cramer_at` and clean up the proofs depending on it
* Replace `cramer_map` with `cramer` after defining `cramer`
* Apply suggestions from code review
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Clean up imports
* Formatting: move } to previous lines
* Move assumptions of `det_zero_of_repeated_column` from variable to argument
* whitespace
Insert space between `finset.filter` and the filter condition.
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Improve docstrings
* Make argument to `prod_cancels_of_partition_cancels` explicit
* Rename `replace_column` and `replace_row` to `update_column` and `update_row`
* Replace `update_column_eq` with `update_column_self` + rewriting step
* whitespace
Newlines between all lemmas
* whitespace
Newline before 'begin'
* Fix conflicts with latest mathlib
* Remove unnecessary explicitification of arguments
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* prod_ite_eq
- \+ *lemma* prod_ite_eq'
- \+ *lemma* prod_cancels_of_partition_cancels

Modified src/data/finset.lean
- \+ *lemma* filter_eq'

Modified src/data/matrix/basic.lean
- \+ *lemma* transpose_val
- \+ *lemma* transpose_one
- \+/\- *lemma* transpose_add
- \+ *lemma* transpose_smul

Modified src/data/matrix/pequiv.lean
- \+ *lemma* to_pequiv_mul_matrix
- \+ *lemma* equiv_to_pequiv_to_matrix

Modified src/data/pequiv.lean
- \+ *lemma* to_pequiv_apply

Modified src/group_theory/perm/sign.lean
- \+ *lemma* swap_mul_self_mul
- \+ *lemma* swap_mul_eq_iff

Modified src/linear_algebra/determinant.lean
- \+ *lemma* det_transpose
- \+ *lemma* det_permutation
- \+ *lemma* det_permute
- \+ *theorem* det_zero_of_column_eq
- \+ *def* mod_swap

Created src/linear_algebra/nonsingular_inverse.lean
- \+ *lemma* update_column_self
- \+ *lemma* update_row_self
- \+ *lemma* update_column_ne
- \+ *lemma* update_row_ne
- \+ *lemma* update_column_val
- \+ *lemma* update_row_val
- \+ *lemma* update_column_transpose
- \+ *lemma* cramer_map_is_linear
- \+ *lemma* cramer_is_linear
- \+ *lemma* cramer_apply
- \+ *lemma* cramer_column_self
- \+ *lemma* sum_cramer
- \+ *lemma* sum_cramer_apply
- \+ *lemma* adjugate_def
- \+ *lemma* adjugate_val
- \+ *lemma* adjugate_transpose
- \+ *lemma* mul_adjugate_val
- \+ *lemma* mul_adjugate
- \+ *lemma* adjugate_mul
- \+ *lemma* nonsing_inv_val
- \+ *lemma* transpose_nonsing_inv
- \+ *theorem* mul_nonsing_inv
- \+ *theorem* nonsing_inv_mul
- \+ *def* update_column
- \+ *def* update_row
- \+ *def* cramer_map
- \+ *def* cramer
- \+ *def* adjugate
- \+ *def* nonsing_inv



## [2020-01-27 16:29:02](https://github.com/leanprover-community/mathlib/commit/5f01591)
fix(.github/workflows/build): set pipefail ([#1911](https://github.com/leanprover-community/mathlib/pull/1911))
Without `pipefail`, the shell command `false | cat` terminates
successfully.
#### Estimated changes
Modified .github/workflows/build.yml




## [2020-01-27 14:52:05](https://github.com/leanprover-community/mathlib/commit/898cd70)
fix(archive/cubing_a_cube): roof broken by [#1903](https://github.com/leanprover-community/mathlib/pull/1903) ([#1912](https://github.com/leanprover-community/mathlib/pull/1912))
#### Estimated changes
Modified archive/cubing_a_cube.lean
- \+/\- *lemma* nonempty_bcubes



## [2020-01-26 21:08:12](https://github.com/leanprover-community/mathlib/commit/497e692)
feat(linear_algebra/matrix): define the trace of a square matrix ([#1883](https://github.com/leanprover-community/mathlib/pull/1883))
* feat(linear_algebra/matrix): define the trace of a square matrix
* Move ring carrier to correct universe
* Add lemma trace_one, and define diag as linear map
* Define diag and trace solely as linear functions
* Diag and trace for module-valued matrices
* Fix cyclic import
* Rename matrix.mul_sum' --> matrix.smul_sum
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Trigger CI
#### Estimated changes
Modified src/data/matrix/basic.lean


Modified src/linear_algebra/matrix.lean
- \+ *lemma* diag_one
- \+ *lemma* trace_one
- \+ *def* diag
- \+ *def* trace

Modified src/ring_theory/algebra.lean




## [2020-01-26 19:37:06](https://github.com/leanprover-community/mathlib/commit/587b312)
refactor(order/filter/basic): redefine `filter.pure` ([#1889](https://github.com/leanprover-community/mathlib/pull/1889))
* refactor(order/filter/basic): redefine `filter.pure`
New definition has `s ∈ pure a` definitionally equal to `a ∈ s`.
* Update src/order/filter/basic.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* Minor fixes suggested by @gebner
* Fix compile
* Update src/order/filter/basic.lean
#### Estimated changes
Modified src/measure_theory/indicator_function.lean


Modified src/order/filter/basic.lean
- \+ *lemma* pure_sets
- \+/\- *lemma* mem_pure_sets
- \+ *lemma* pure_eq_principal
- \+/\- *lemma* map_pure
- \+ *lemma* join_pure
- \+ *lemma* pure_bind
- \+ *lemma* pure_inj
- \+ *lemma* le_pure_iff
- \+ *lemma* tendsto_pure
- \+/\- *lemma* tendsto_const_pure
- \- *lemma* pure_def
- \- *lemma* mem_pure
- \- *lemma* mem_pure_iff

Modified src/topology/list.lean


Modified src/topology/order.lean


Modified src/topology/stone_cech.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/completion.lean




## [2020-01-26 15:54:48](https://github.com/leanprover-community/mathlib/commit/ce2e7a8)
feat(linear_algebra/multilinear): image of sum ([#1908](https://github.com/leanprover-community/mathlib/pull/1908))
* staging
* fix build
* linting
* staging
* docstring
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_powerset_insert
- \+ *lemma* prod_piecewise

Modified src/data/finset.lean
- \+ *lemma* ne_insert_of_not_mem
- \+ *lemma* empty_sdiff
- \+ *lemma* insert_sdiff_of_not_mem
- \+ *lemma* insert_sdiff_of_mem
- \+ *lemma* piecewise_insert_self
- \+ *lemma* piecewise_empty
- \+ *lemma* piecewise_coe
- \+ *lemma* piecewise_eq_of_mem
- \+ *lemma* piecewise_eq_of_not_mem
- \+ *lemma* piecewise_insert_of_ne
- \+ *lemma* piecewise_insert
- \+ *lemma* powerset_empty
- \+ *lemma* not_mem_of_mem_powerset_of_not_mem
- \+ *lemma* powerset_insert
- \+/\- *theorem* lt_wf
- \+ *def* piecewise

Modified src/data/fintype.lean
- \+ *lemma* piecewise_univ

Modified src/data/set/basic.lean
- \+ *lemma* ne_insert_of_not_mem
- \+ *theorem* insert_diff_of_mem
- \+ *theorem* insert_diff_of_not_mem
- \- *theorem* insert_diff

Modified src/data/set/function.lean
- \+ *lemma* piecewise_empty
- \+ *lemma* piecewise_univ
- \+ *lemma* piecewise_insert_self
- \+ *lemma* piecewise_insert
- \+ *lemma* piecewise_eq_of_mem
- \+ *lemma* piecewise_eq_of_not_mem
- \+ *lemma* piecewise_insert_of_ne

Modified src/linear_algebra/multilinear.lean
- \+ *lemma* map_sub
- \+ *lemma* map_piecewise_smul
- \+ *lemma* map_smul_univ
- \+ *lemma* map_piecewise_add
- \+ *lemma* map_add_univ

Modified src/logic/function.lean
- \+ *def* set.piecewise



## [2020-01-26 13:49:29](https://github.com/leanprover-community/mathlib/commit/ab155ef)
refactor(*): refactor `sum_smul`/`smul_sum` ([#1910](https://github.com/leanprover-community/mathlib/pull/1910))
* refactor(*): refactor `sum_smul`/`smul_sum`
API changes:
* Define both versions for `list, `multiset`, and `finset`;
* new `finset.smul_sum` is the old `finset.smul_sum` or `_root_.sum_smul.symm``
* new `finset.sum_smul` is the old `finset.smul_sum'`
* new `smul_smul` doesn't need a `Type` argument
* some lemmas are generalized to a `semimodule` or a `distrib_mul_action`
* Fix compile
#### Estimated changes
Modified src/algebra/module.lean
- \+ *lemma* list.sum_smul
- \+ *lemma* multiset.sum_smul
- \+/\- *lemma* finset.sum_smul
- \+ *lemma* nat.smul_def
- \- *lemma* smul_smul

Modified src/group_theory/group_action.lean
- \+ *lemma* smul_smul
- \+ *lemma* list.smul_sum
- \+ *lemma* multiset.smul_sum
- \+ *lemma* finset.smul_sum

Modified src/linear_algebra/basic.lean
- \- *lemma* smul_sum
- \- *lemma* smul_sum'

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/ring_theory/ideal_operations.lean




## [2020-01-26 03:58:09](https://github.com/leanprover-community/mathlib/commit/2297d20)
feat(tactic/clear): add clear' tactic ([#1899](https://github.com/leanprover-community/mathlib/pull/1899))
* feat(tactic/clear): add clear' tactic
We add an improved version of the `clear` tactic. When clearing multiple
hypotheses, `clear` can fail even though all hypotheses could be
cleared. This happens when the hypotheses depend on each other and are
given in the wrong order:
```lean
example : ∀ {α : Type} {β : α → Type} (a : α) (b : β a), unit :=
  begin
    intros α β a b,
    clear a b, -- fails
    exact ()
  end
```
When `clear` tries to clear `a`, `b`, which depends on `a`, is still in the
context, so the operation fails. We give a tactic `clear'` which
recognises this and clears `b` before `a`.
* refactor(tactic/clear): better implementation of clear'
We refactor `clear'`, replacing the old implementation with one that is
more concise and should be faster. The new implementation strategy also
gives us a new variant of `clear`, `clear_dependent`, almost for free.
`clear_dependent` works like `clear'`, but in addition to the given
hypotheses, it also clears any other hypotheses which depend on them.
* style(test/tactics, docs/tactics): less indentation
* test(test/tactics): better tests for clear' and clear_dependent
We make the tests for `clear'` and `clear_dependent` more meaningful:
They now permit less illegal behaviours.
* refactor(tactic/clear): simplify error message formatting
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/basic.lean


Created src/tactic/clear.lean


Modified test/tactics.lean




## [2020-01-26 01:12:21](https://github.com/leanprover-community/mathlib/commit/9decec2)
feat(*): some simple lemmas about sets and finite sets ([#1903](https://github.com/leanprover-community/mathlib/pull/1903))
* feat(*): some simple lemmas about sets and finite sets
* More lemmas, simplify proofs
* Introduce `finsup.nonempty` and use it.
* Update src/algebra/big_operators.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* Revert "Update src/algebra/big_operators.lean"
This reverts commit 17c89a808545203dc5a80a4f11df4f62e949df8d. It
breaks compile if we rewrite right to left.
* simp, to_additive
* Add a missing docstring
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_filter_ne_one
- \+ *lemma* nonempty_of_prod_ne_one
- \+/\- *lemma* exists_ne_one_of_prod_ne_one
- \+/\- *lemma* prod_Ico_id_eq_fact
- \+ *theorem* sum_lt_sum
- \+ *theorem* exists_le_of_sum_le

Modified src/algebra/module.lean
- \+ *lemma* sum_const'
- \- *lemma* finset.sum_const'
- \+ *theorem* exists_card_smul_le_sum
- \+ *theorem* exists_card_smul_ge_sum

Modified src/data/finset.lean
- \+ *lemma* coe_nonempty
- \+ *lemma* nonempty.bex
- \+ *lemma* nonempty.mono
- \+/\- *lemma* coe_empty
- \+ *lemma* nonempty.image
- \+/\- *lemma* image_const
- \+/\- *lemma* exists_min
- \- *lemma* nonempty_iff_ne_empty
- \+ *theorem* nonempty_of_ne_empty
- \+ *theorem* nonempty_iff_ne_empty
- \+ *theorem* eq_empty_or_nonempty
- \+/\- *theorem* card_pos
- \+ *theorem* max_of_nonempty
- \+ *theorem* min_of_nonempty
- \- *theorem* exists_mem_of_ne_empty
- \- *theorem* exists_mem_iff_ne_empty
- \- *theorem* max_of_ne_empty
- \- *theorem* min_of_ne_empty
- \+/\- *def* min'
- \+/\- *def* max'

Modified src/data/finsupp.lean
- \+/\- *def* split_support

Modified src/data/fintype.lean
- \+ *lemma* fin.univ_succ
- \+ *theorem* fin.prod_univ_succ
- \+ *theorem* fin.prod_univ_zero
- \+ *theorem* fin.sum_univ_succ

Modified src/data/nat/totient.lean


Modified src/data/set/finite.lean
- \+/\- *lemma* exists_min

Modified src/data/set/lattice.lean
- \+ *lemma* Inter_subset_of_subset
- \+ *lemma* Inter_subset_Inter
- \+ *lemma* Inter_subset_Inter2
- \+/\- *theorem* Union_subset_iff
- \+/\- *theorem* mem_Inter_of_mem
- \+/\- *theorem* subset_Inter

Modified src/group_theory/order_of_element.lean




## [2020-01-25 23:45:34](https://github.com/leanprover-community/mathlib/commit/d3e5621)
feat(data/real/ereal): add `ereal` := [-oo,oo] ([#1703](https://github.com/leanprover-community/mathlib/pull/1703))
* feat(data/real/ereal): add `ereal` := [-oo,oo]
* some updates
* some cleanup in ereal
* move pattern attribute
* works
* more docstring
* don't understand why this file was broken
* more tidyup
* deducing complete lattice from type class inference
* another neg theorem
* adding some module doc
* tinkering
* deriving addition
#### Estimated changes
Created src/data/real/ereal.lean
- \+ *theorem* neg_inj
- \+ *theorem* neg_eq_iff_neg_eq
- \+ *theorem* le_neg_of_le_neg
- \+ *def* ereal

Modified src/order/bounded_lattice.lean




## [2020-01-25 21:18:30](https://github.com/leanprover-community/mathlib/commit/d4aa088)
fix(scripts/deploy_nightly): fill in blank env vars ([#1909](https://github.com/leanprover-community/mathlib/pull/1909))
* fix(scripts/deploy_nightly): fill in blank env vars
* fix: LEAN_VERSION="lean-3.4.2"
#### Estimated changes
Modified scripts/deploy_nightly.sh




## [2020-01-25 14:01:56](https://github.com/leanprover-community/mathlib/commit/7077242)
doc (analysis/normed_space/operator_norm): cleanup ([#1906](https://github.com/leanprover-community/mathlib/pull/1906))
* doc (analysis/normed_space/operator_norm): cleanup
* typo
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean




## [2020-01-25 12:31:17](https://github.com/leanprover-community/mathlib/commit/8c9a15e)
feat(topology/instances/ennreal): continuity of multiplication by const ([#1905](https://github.com/leanprover-community/mathlib/pull/1905))
* feat(topology/instances/ennreal): continuity of multiplication by const
* Fix compile
#### Estimated changes
Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/closeds.lean




## [2020-01-25 10:51:17](https://github.com/leanprover-community/mathlib/commit/20f153a)
fix(scripts/deploy_nightly): token is now just the PAT, need to add user ([#1907](https://github.com/leanprover-community/mathlib/pull/1907))
#### Estimated changes
Modified scripts/deploy_nightly.sh




## [2020-01-25 08:42:04](https://github.com/leanprover-community/mathlib/commit/3bbf8eb)
feat(data/real/nnreal): a few lemmas about subtraction ([#1904](https://github.com/leanprover-community/mathlib/pull/1904))
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+/\- *lemma* sub_eq_zero
- \+ *lemma* sub_self
- \+ *lemma* sub_zero
- \+ *lemma* sub_le_self
- \+ *lemma* sub_sub_cancel_of_le



## [2020-01-24 23:34:43](https://github.com/leanprover-community/mathlib/commit/3b9ee8e)
doc(geometry/manifold): fix markdown ([#1901](https://github.com/leanprover-community/mathlib/pull/1901))
* doc(geometry/manifold): fix markdown
* Update src/geometry/manifold/manifold.lean
* Update src/geometry/manifold/manifold.lean
* Update src/geometry/manifold/manifold.lean
* Update src/geometry/manifold/manifold.lean
#### Estimated changes
Modified src/geometry/manifold/manifold.lean




## [2020-01-24 21:56:45+01:00](https://github.com/leanprover-community/mathlib/commit/d075695)
fix(build): typo in deploy_nightly script name ([#1902](https://github.com/leanprover-community/mathlib/pull/1902))
#### Estimated changes
Modified .github/workflows/build.yml




## [2020-01-24 20:01:58+01:00](https://github.com/leanprover-community/mathlib/commit/2db02b8)
feat(.github): switch to github actions for ci ([#1893](https://github.com/leanprover-community/mathlib/pull/1893))
#### Estimated changes
Created .github/workflows/build.yml


Modified .mergify.yml


Deleted .travis.yml


Modified README.md


Deleted purge_olean.sh


Modified scripts/deploy_nightly.sh


Deleted travis_long.sh




## [2020-01-24 12:07:12](https://github.com/leanprover-community/mathlib/commit/601d5b1)
feat(tactic/simp_rw): add `simp_rw` tactic, a mix of `simp` and `rw` ([#1900](https://github.com/leanprover-community/mathlib/pull/1900))
* add `simp_rw` tactic that is a mix of `simp` and `rw`
* Style fixes
* Module documentation for the file `tactic/simp_rw.lean`
* Apply suggestions to improve documentation of `simp_rw`
* Documentation and tests for `simp_rw [...] at ...`
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/default.lean


Created src/tactic/simp_rw.lean


Created test/simp_rw.lean


Modified test/tactics.lean




## [2020-01-24 09:09:29](https://github.com/leanprover-community/mathlib/commit/69099f0)
feat(order/filter/bases): define `filter.has_basis` ([#1896](https://github.com/leanprover-community/mathlib/pull/1896))
* feat(*): assorted simple lemmas, simplify some proofs
* feat(order/filter/bases): define `filter.has_basis`
* Add `@[nolint]`
* +1 lemma, +1 simplified proof
* Remove whitespaces
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Ref. note nolint_ge
#### Estimated changes
Created src/order/filter/bases.lean
- \+ *lemma* has_basis.mem_iff
- \+ *lemma* has_basis.mem_of_superset
- \+ *lemma* has_basis.mem_of_mem
- \+ *lemma* has_basis.forall_nonempty_iff_ne_bot
- \+ *lemma* basis_sets
- \+ *lemma* at_top_basis
- \+ *lemma* at_top_basis'
- \+ *lemma* has_basis.inf
- \+ *lemma* has_basis.inf_principal
- \+ *lemma* has_basis.eq_binfi
- \+ *lemma* has_basis.eq_infi
- \+ *lemma* has_basis_infi_principal
- \+ *lemma* has_basis_binfi_principal
- \+ *lemma* has_basis.map
- \+ *lemma* has_basis.comap
- \+ *lemma* has_basis.prod_self
- \+ *lemma* has_basis.tendsto_left_iff
- \+ *lemma* has_basis.tendsto_right_iff
- \+ *lemma* has_basis.tendsto_iff
- \+ *lemma* tendsto.basis_left
- \+ *lemma* tendsto.basis_right
- \+ *lemma* tendsto.basis_both
- \+ *lemma* has_basis.prod
- \+ *theorem* has_basis.ge_iff
- \+ *theorem* has_basis.le_iff
- \+ *theorem* has_basis.le_basis_iff



## [2020-01-24 00:47:07](https://github.com/leanprover-community/mathlib/commit/aad853b)
docs(data/mv_polynomial): add module docstring [ci skip] ([#1892](https://github.com/leanprover-community/mathlib/pull/1892))
* adding docstring
* fix markdown
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* fix markdown
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* variables have type sigma
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* don't tell the reader about the interface
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* consistent conventions for monomial
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* variables are terms of type sigma
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* Update src/data/mv_polynomial.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* Update src/data/mv_polynomial.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* version 2
* one last tinker
* removing $ signs
* next attempt
* Update src/data/mv_polynomial.lean
* Update src/data/mv_polynomial.lean
* Update src/data/mv_polynomial.lean
#### Estimated changes
Modified src/data/mv_polynomial.lean




## [2020-01-22 20:10:27](https://github.com/leanprover-community/mathlib/commit/b686bc2)
feat(algebra/lie_algebra): define Lie subalgebras, morphisms, modules, submodules, quotients ([#1835](https://github.com/leanprover-community/mathlib/pull/1835))
* feat(algebra/lie_algebra): define Lie subalgebras, morphisms, modules, submodules, quotients
* Code review: colons at end of line
* Update src/algebra/lie_algebra.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebra/lie_algebra.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebra/lie_algebra.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Catch up after GH commits from code review
* Remove accidentally-included '#lint'
* Rename: lie_subalgebra.bracket --> lie_subalgebra.lie_mem
* Lie ideals are subalgebras
* Add missing doc string
* Update src/algebra/lie_algebra.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Allow quotients of lie_modules by lie_submodules (part 1)
The missing piece is the construction of a lie_module structure on
the quotient by a lie_submodule, i.e.,:
`instance lie_quotient_lie_module : lie_module R L N.quotient := ...`
I will add this in due course.
* Code review: minor fixes
* New lie_module approach based on add_action, linear_action
* Remove add_action by merging into linear_action.
I would prefer to keep add_action, and especially like to keep the feature
that linear_action extends has_scalar, but unfortunately this is not
possible with the current typeclass resolution algorithm since we should
never extend a class with fewer carrier types.
* Add missing doc string
* Simplify Lie algebra adjoing action definitions
* whitespace tweaks
* Remove redundant explicit type
* Update src/algebra/lie_algebra.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebra/lie_algebra.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebra/lie_algebra.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebra/lie_algebra.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Catch up after rename bracket --> map_lie in morphism
* Update src/linear_algebra/linear_action.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/linear_algebra/linear_action.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/linear_algebra/linear_action.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/linear_algebra/linear_action.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/linear_algebra/linear_action.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/linear_algebra/linear_action.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/linear_algebra/linear_action.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/linear_algebra/linear_action.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/linear_algebra/linear_action.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/algebra/lie_algebra.lean
- \+ *lemma* map_lie
- \+ *lemma* endo_algebra_bracket
- \+ *lemma* lie_act
- \+ *lemma* lie_mem_right
- \+ *lemma* lie_mem_left
- \+ *lemma* is_quotient_mk
- \+ *lemma* mk_bracket
- \+/\- *def* Ad
- \+ *def* lie_module.of_endo_morphism
- \+ *def* lie_ideal_subalgebra
- \- *def* bil_lie
- \- *def* of_endomorphism_algebra

Created src/linear_algebra/linear_action.lean
- \+ *lemma* zero_linear_action
- \+ *lemma* linear_action_zero
- \+ *lemma* linear_action_add_act
- \+ *lemma* linear_action_act_add
- \+ *lemma* linear_action_act_smul
- \+ *lemma* linear_action_smul_act
- \+ *def* of_endo_map
- \+ *def* to_endo_map



## [2020-01-22 00:57:34](https://github.com/leanprover-community/mathlib/commit/96ee2a6)
feat(order/filter/basic): prove `@cofinite ℕ = at_top` ([#1888](https://github.com/leanprover-community/mathlib/pull/1888))
* feat(order/filter/basic): prove `@cofinite ℕ = at_top`
Also generalize `not_injective_(nat/int)_fintype`, and use `[infinite
α]` instead of `set.infinite (@univ α)` as an argument.
* Update src/data/equiv/basic.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* Drop a duplicate definition, thanks @ChrisHughes24
#### Estimated changes
Modified src/algebra/char_p.lean


Modified src/data/fintype.lean
- \+ *lemma* not_injective_infinite_fintype
- \+ *lemma* not_surjective_fintype_infinite

Modified src/data/real/hyperreal.lean


Modified src/data/set/finite.lean
- \- *lemma* infinite_univ_nat
- \- *lemma* not_injective_nat_fintype
- \- *lemma* not_injective_int_fintype
- \+ *theorem* infinite_univ_iff
- \+ *theorem* infinite_univ

Modified src/group_theory/order_of_element.lean


Modified src/order/filter/basic.lean
- \+ *lemma* mem_cofinite
- \+/\- *lemma* cofinite_ne_bot
- \+ *lemma* frequently_cofinite_iff_infinite
- \+/\- *lemma* hyperfilter_le_cofinite
- \+/\- *lemma* is_ultrafilter_hyperfilter
- \+ *lemma* set.infinite_iff_frequently_cofinite
- \+ *lemma* nat.cofinite_eq_at_top
- \+/\- *theorem* nmem_hyperfilter_of_finite
- \+/\- *theorem* compl_mem_hyperfilter_of_finite
- \+/\- *theorem* mem_hyperfilter_of_finite_compl



## [2020-01-21 21:29:04](https://github.com/leanprover-community/mathlib/commit/aa6cc06)
feat(measure_theory/set_integral): integrals over subsets ([#1875](https://github.com/leanprover-community/mathlib/pull/1875))
* feat(measure_theory/set_integral): integral on a set
* mismached variables
* move if_preimage
* Update src/measure_theory/l1_space.lean
Co-Authored-By: Yury G. Kudryashov <urkud@ya.ru>
* Small fixes
* Put indicator_function into data folder
* Use antimono as names
* Change name to antimono
* Fix everything
* Use binder notation for integrals
* delete an extra space
* Update set_integral.lean
* adjust implicit and explicit variables
* measurable_on_singleton
* prove integral_on_Union
* Update indicator_function.lean
* Update set_integral.lean
* lint
* Update bochner_integration.lean
* reviewer's comment
* use Yury's proof
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* bUnion_union
- \+ *lemma* bUnion_insert
- \+ *theorem* bUnion_singleton
- \+ *theorem* supr_union

Created src/data/indicator_function.lean
- \+ *lemma* indicator_of_mem
- \+ *lemma* indicator_of_not_mem
- \+ *lemma* indicator_congr
- \+ *lemma* indicator_univ
- \+ *lemma* indicator_empty
- \+ *lemma* indicator_zero
- \+ *lemma* indicator_indicator
- \+ *lemma* indicator_preimage
- \+ *lemma* indicator_union_of_not_mem_inter
- \+ *lemma* indicator_union_of_disjoint
- \+ *lemma* indicator_add
- \+ *lemma* indicator_smul
- \+ *lemma* indicator_neg
- \+ *lemma* indicator_sub
- \+ *lemma* indicator_compl
- \+ *lemma* indicator_finset_sum
- \+ *lemma* indicator_finset_bUnion
- \+ *lemma* indicator_le_indicator
- \+ *lemma* indicator_le_indicator_of_subset
- \+ *def* indicator

Modified src/data/set/basic.lean
- \+ *lemma* if_preimage

Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* of_simple_func_zero
- \+/\- *lemma* integral_undef
- \+/\- *lemma* integral_non_integrable
- \+/\- *lemma* integral_non_measurable
- \+/\- *lemma* integral_zero
- \+/\- *lemma* integral_neg
- \+/\- *lemma* integral_smul
- \+ *lemma* integral_mul_left
- \+ *lemma* integral_mul_right
- \+ *lemma* integral_div
- \+/\- *lemma* integral_nonneg_of_nonneg_ae
- \+/\- *lemma* integral_nonpos_of_nonpos_ae
- \+ *lemma* integral_le_integral_ae
- \+ *lemma* integral_le_integral
- \+/\- *lemma* norm_integral_le_integral_norm
- \+ *lemma* integral_finset_sum
- \- *lemma* integral_le_integral_of_le_ae

Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_measurable_Ioi
- \+ *lemma* is_measurable_Ici
- \+ *lemma* is_measurable_Iic
- \+/\- *lemma* is_measurable_Ioo
- \+ *lemma* is_measurable_Ioc
- \+/\- *lemma* is_measurable_Ico
- \+ *lemma* is_measurable_Icc

Created src/measure_theory/indicator_function.lean
- \+ *lemma* indicator_congr_ae
- \+ *lemma* indicator_congr_of_set
- \+ *lemma* indicator_union_ae
- \+ *lemma* norm_indicator_le_of_subset
- \+ *lemma* norm_indicator_le_norm_self
- \+ *lemma* norm_indicator_eq_indicator_norm
- \+ *lemma* indicator_norm_le_norm_self
- \+ *lemma* indicator_le_indicator_ae
- \+ *lemma* tendsto_indicator_of_monotone
- \+ *lemma* tendsto_indicator_of_antimono
- \+ *lemma* tendsto_indicator_bUnion_finset

Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable_congr_ae
- \+ *lemma* integrable_of_le
- \+/\- *lemma* integrable_zero
- \+/\- *lemma* integrable.add
- \+ *lemma* integrable_finset_sum
- \+/\- *lemma* integrable.neg
- \+/\- *lemma* integrable_neg_iff
- \+/\- *lemma* integrable.sub
- \+/\- *lemma* integrable.smul
- \+/\- *lemma* integrable_smul_iff
- \+/\- *lemma* of_fun_zero
- \- *lemma* integrable_iff_of_ae_eq

Created src/measure_theory/set_integral.lean
- \+ *lemma* measurable_on_empty
- \+ *lemma* measurable_on_univ
- \+ *lemma* measurable.measurable_on
- \+ *lemma* is_measurable.inter_preimage
- \+ *lemma* measurable_on.subset
- \+ *lemma* measurable_on.union
- \+ *lemma* measurable_on_singleton
- \+ *lemma* integrable_on_congr
- \+ *lemma* integrable_on_congr_ae
- \+ *lemma* integrable_on_empty
- \+ *lemma* integrable_on_of_integrable
- \+ *lemma* integrable_on.subset
- \+ *lemma* integrable_on.smul
- \+ *lemma* integrable_on.mul_left
- \+ *lemma* integrable_on.mul_right
- \+ *lemma* integrable_on.divide
- \+ *lemma* integrable_on.add
- \+ *lemma* integrable_on.neg
- \+ *lemma* integrable_on.sub
- \+ *lemma* integrable_on.union
- \+ *lemma* integrable_on_norm_iff
- \+ *lemma* integral_on_zero
- \+ *lemma* integral_on_congr
- \+ *lemma* integral_on_congr_of_ae_eq
- \+ *lemma* integral_on_congr_of_set
- \+ *lemma* integral_on_smul
- \+ *lemma* integral_on_mul_left
- \+ *lemma* integral_on_mul_right
- \+ *lemma* integral_on_div
- \+ *lemma* integral_on_neg
- \+ *lemma* integral_on_add
- \+ *lemma* integral_on_sub
- \+ *lemma* integral_on_le_integral_on_ae
- \+ *lemma* integral_on_le_integral_on
- \+ *lemma* integral_on_union
- \+ *lemma* integral_on_union_ae
- \+ *lemma* tendsto_integral_on_of_monotone
- \+ *lemma* tendsto_integral_on_of_antimono
- \+ *lemma* integral_on_Union
- \+ *def* measurable_on
- \+ *def* integrable_on

Modified src/topology/bases.lean
- \+ *lemma* has_countable_basis_at_top_finset_nat



## [2020-01-21 18:58:28](https://github.com/leanprover-community/mathlib/commit/217b5e7)
refactor(algebra/char_zero): use `function.injective` ([#1894](https://github.com/leanprover-community/mathlib/pull/1894))
No need to require `↔` in the definition.
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+/\- *theorem* cast_injective
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_eq_zero
- \+/\- *theorem* cast_ne_zero

Modified src/data/padics/padic_numbers.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* coe_nat_lt_coe_nat
- \+ *lemma* coe_nat_mono
- \+ *lemma* coe_nat_le_coe_nat

Modified src/data/zsqrtd/basic.lean




## [2020-01-21 09:56:58](https://github.com/leanprover-community/mathlib/commit/f3835fa)
feat(*): assorted simple lemmas, simplify some proofs ([#1895](https://github.com/leanprover-community/mathlib/pull/1895))
* feat(*): assorted simple lemmas, simplify some proofs
* +1 lemma, +1 simplified proof
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* of_real_lt_of_real_iff_of_nonneg

Modified src/data/real/nnreal.lean
- \+ *lemma* of_real_lt_of_real_iff_of_nonneg

Modified src/data/set/basic.lean
- \+ *lemma* inter_singleton_nonempty

Modified src/data/set/intervals/basic.lean
- \+ *lemma* nonempty_Ioi
- \+ *lemma* nonempty_Iio

Modified src/order/basic.lean
- \+ *theorem* directed.mono_comp

Modified src/order/bounded_lattice.lean
- \+ *lemma* dense_coe

Modified src/order/filter/basic.lean
- \+ *lemma* forall_sets_nonempty_iff_ne_bot

Modified src/topology/basic.lean


Modified src/topology/continuous_on.lean


Modified src/topology/sequences.lean




## [2020-01-18 08:16:09](https://github.com/leanprover-community/mathlib/commit/d32c797)
feat(data/bool): coe_bool_iff ([#1891](https://github.com/leanprover-community/mathlib/pull/1891))
#### Estimated changes
Modified src/data/bool.lean
- \+ *theorem* coe_bool_iff



## [2020-01-18 05:20:13](https://github.com/leanprover-community/mathlib/commit/d548d92)
chore(ring_theory/polynomial): remove decidable_eq assumptions ([#1890](https://github.com/leanprover-community/mathlib/pull/1890))
#### Estimated changes
Modified src/ring_theory/polynomial.lean
- \+/\- *theorem* is_noetherian_ring_mv_polynomial_of_fintype



## [2020-01-17 18:46:09](https://github.com/leanprover-community/mathlib/commit/c8ae79d)
feat(measure_theory/bochner_integration): dominated convergence theorem for filters ([#1884](https://github.com/leanprover-community/mathlib/pull/1884))
* Dominated convergence theorem for filters
* Update bases.lean
* Update bochner_integration.lean
* reviewer's comments
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* tendsto_integral_filter_of_dominated_convergence
- \+/\- *theorem* tendsto_integral_of_dominated_convergence

Modified src/measure_theory/integration.lean
- \+ *lemma* tendsto_lintegral_filter_of_dominated_convergence

Modified src/measure_theory/l1_space.lean


Modified src/topology/bases.lean
- \+ *lemma* has_countable_basis.tendsto_iff_seq_tendsto
- \+ *lemma* has_countable_basis.tendsto_of_seq_tendsto



## [2020-01-17 03:02:01](https://github.com/leanprover-community/mathlib/commit/9ac26cb)
feat(geometry/manifold/mfderiv): derivative of functions between smooth manifolds ([#1872](https://github.com/leanprover-community/mathlib/pull/1872))
* feat(geometry/manifold/mfderiv): derivative of functions between smooth manifolds
* Update src/geometry/manifold/mfderiv.lean
Co-Authored-By: Yury G. Kudryashov <urkud@ya.ru>
* more details in docstrings [ci skip]
* fix docstrings [ci skip]
* reviewer's comments
#### Estimated changes
Modified src/geometry/manifold/basic_smooth_bundle.lean


Created src/geometry/manifold/mfderiv.lean
- \+ *lemma* unique_mdiff_within_at_univ
- \+ *lemma* unique_mdiff_within_at_iff
- \+ *lemma* unique_mdiff_within_at.mono
- \+ *lemma* unique_mdiff_within_at.inter'
- \+ *lemma* unique_mdiff_within_at.inter
- \+ *lemma* is_open.unique_mdiff_within_at
- \+ *lemma* unique_mdiff_on.inter
- \+ *lemma* is_open.unique_mdiff_on
- \+ *lemma* mdifferentiable_within_at_iff
- \+ *lemma* mfderiv_within_zero_of_not_mdifferentiable_within_at
- \+ *lemma* mfderiv_zero_of_not_mdifferentiable_at
- \+ *lemma* has_mfderiv_within_at.mdifferentiable_within_at
- \+ *lemma* has_mfderiv_at.mdifferentiable_at
- \+ *lemma* has_mfderiv_within_at_univ
- \+ *lemma* has_mfderiv_within_at_inter'
- \+ *lemma* has_mfderiv_within_at_inter
- \+ *lemma* has_mfderiv_within_at.union
- \+ *lemma* has_mfderiv_within_at.nhds_within
- \+ *lemma* has_mfderiv_within_at.has_mfderiv_at
- \+ *lemma* mdifferentiable_within_at.has_mfderiv_within_at
- \+ *lemma* mdifferentiable_within_at.mfderiv_within
- \+ *lemma* mdifferentiable_at.has_mfderiv_at
- \+ *lemma* mdifferentiable_at.mfderiv
- \+ *lemma* has_mfderiv_at.mfderiv
- \+ *lemma* has_mfderiv_within_at.mfderiv_within
- \+ *lemma* mdifferentiable.mfderiv_within
- \+ *lemma* mfderiv_within_subset
- \+ *lemma* mdifferentiable_within_at.mono
- \+ *lemma* mdifferentiable_within_at_univ
- \+ *lemma* mdifferentiable_within_at_inter
- \+ *lemma* mdifferentiable_within_at_inter'
- \+ *lemma* mdifferentiable_at.mdifferentiable_within_at
- \+ *lemma* mdifferentiable_within_at.mdifferentiable_at
- \+ *lemma* mdifferentiable_on.mono
- \+ *lemma* mdifferentiable_on_univ
- \+ *lemma* mdifferentiable.mdifferentiable_on
- \+ *lemma* mdifferentiable_on_of_locally_mdifferentiable_on
- \+ *lemma* mfderiv_within_univ
- \+ *lemma* mfderiv_within_inter
- \+ *lemma* mdifferentiable_within_at.continuous_within_at
- \+ *lemma* mdifferentiable_at.continuous_at
- \+ *lemma* mdifferentiable_on.continuous_on
- \+ *lemma* mdifferentiable.continuous
- \+ *lemma* bundle_mfderiv_within_subset
- \+ *lemma* bundle_mfderiv_within_univ
- \+ *lemma* bundle_mfderiv_within_eq_bundle_mfderiv
- \+ *lemma* bundle_mfderiv_within_tangent_bundle_proj
- \+ *lemma* bundle_mfderiv_within_proj
- \+ *lemma* bundle_mfderiv_tangent_bundle_proj
- \+ *lemma* bundle_mfderiv_proj
- \+ *lemma* has_mfderiv_within_at.congr_of_mem_nhds_within
- \+ *lemma* has_mfderiv_within_at.congr_mono
- \+ *lemma* has_mfderiv_at.congr_of_mem_nhds
- \+ *lemma* mdifferentiable_within_at.congr_of_mem_nhds_within
- \+ *lemma* mdifferentiable_within_at_congr_of_mem_nhds_within
- \+ *lemma* mdifferentiable_within_at.congr_mono
- \+ *lemma* mdifferentiable_within_at.congr
- \+ *lemma* mdifferentiable_on.congr_mono
- \+ *lemma* mdifferentiable_at.congr_of_mem_nhds
- \+ *lemma* mdifferentiable_within_at.mfderiv_within_congr_mono
- \+ *lemma* mfderiv_within_congr_of_mem_nhds_within
- \+ *lemma* mfderiv_congr_of_mem_nhds
- \+ *lemma* written_in_ext_chart_comp
- \+ *lemma* mdifferentiable_within_at.comp
- \+ *lemma* mdifferentiable_at.comp
- \+ *lemma* mfderiv_within_comp
- \+ *lemma* mfderiv_comp
- \+ *lemma* mdifferentiable_on.comp
- \+ *lemma* mdifferentiable.comp
- \+ *lemma* bundle_mfderiv_within_comp_at
- \+ *lemma* bundle_mfderiv_comp_at
- \+ *lemma* bundle_mfderiv_comp
- \+ *lemma* has_mfderiv_at_id
- \+ *lemma* mdifferentiable_at_id
- \+ *lemma* mdifferentiable_within_at_id
- \+ *lemma* mdifferentiable_id
- \+ *lemma* mdifferentiable_on_id
- \+ *lemma* mfderiv_id
- \+ *lemma* mfderiv_within_id
- \+ *lemma* has_mfderiv_at_const
- \+ *lemma* mdifferentiable_at_const
- \+ *lemma* mdifferentiable_within_at_const
- \+ *lemma* mdifferentiable_const
- \+ *lemma* mdifferentiable_on_const
- \+ *lemma* mfderiv_const
- \+ *lemma* mfderiv_within_const
- \+ *lemma* model_with_corners_mdifferentiable_on_to_fun
- \+ *lemma* model_with_corners_mdifferentiable_on_inv_fun
- \+ *lemma* mdifferentiable_at_atlas_to_fun
- \+ *lemma* mdifferentiable_on_atlas_to_fun
- \+ *lemma* mdifferentiable_at_atlas_inv_fun
- \+ *lemma* mdifferentiable_on_atlas_inv_fun
- \+ *lemma* mdifferentiable_of_mem_atlas
- \+ *lemma* mdifferentiable_chart
- \+ *lemma* bundle_mfderiv_chart_to_fun
- \+ *lemma* bundle_mfderiv_chart_inv_fun
- \+ *lemma* unique_mdiff_within_at_iff_unique_diff_within_at
- \+ *lemma* unique_mdiff_on_iff_unique_diff_on
- \+ *lemma* written_in_ext_chart_model_space
- \+ *lemma* symm
- \+ *lemma* mdifferentiable_at_to_fun
- \+ *lemma* mdifferentiable_at_inv_fun
- \+ *lemma* inv_fun_to_fun_deriv
- \+ *lemma* to_fun_inv_fun_deriv
- \+ *lemma* range_mfderiv_eq_univ
- \+ *lemma* trans
- \+ *lemma* unique_mdiff_on.unique_mdiff_on_preimage
- \+ *lemma* unique_mdiff_on.unique_diff_on
- \+ *lemma* unique_mdiff_on.unique_diff_on_inter_preimage
- \+ *lemma* unique_mdiff_on.smooth_bundle_preimage
- \+ *lemma* unique_mdiff_on.tangent_bundle_proj_preimage
- \+ *theorem* unique_mdiff_within_at.eq
- \+ *theorem* unique_mdiff_on.eq
- \+ *theorem* has_mfderiv_within_at.mono
- \+ *theorem* has_mfderiv_at.has_mfderiv_within_at
- \+ *theorem* has_mfderiv_at_unique
- \+ *theorem* has_mfderiv_within_at.continuous_within_at
- \+ *theorem* has_mfderiv_at.continuous_at
- \+ *theorem* has_mfderiv_within_at.comp
- \+ *theorem* has_mfderiv_at.comp
- \+ *theorem* has_mfderiv_at.comp_has_mfderiv_within_at
- \+ *theorem* has_mfderiv_within_at_id
- \+ *theorem* has_mfderiv_within_at_const
- \+ *theorem* mdifferentiable_within_at_iff_differentiable_within_at
- \+ *theorem* mdifferentiable_at_iff_differentiable_at
- \+ *theorem* mdifferentiable_on_iff_differentiable_on
- \+ *theorem* mdifferentiable_iff_differentiable
- \+ *theorem* mfderiv_within_eq_fderiv_within
- \+ *theorem* mfderiv_eq_fderiv
- \+ *def* unique_mdiff_within_at
- \+ *def* unique_mdiff_on
- \+ *def* written_in_ext_chart_at
- \+ *def* mdifferentiable_within_at
- \+ *def* mdifferentiable_at
- \+ *def* mdifferentiable_on
- \+ *def* mdifferentiable
- \+ *def* local_homeomorph.mdifferentiable
- \+ *def* has_mfderiv_within_at
- \+ *def* has_mfderiv_at
- \+ *def* mfderiv_within
- \+ *def* mfderiv
- \+ *def* bundle_mfderiv_within
- \+ *def* bundle_mfderiv

Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* ext_chart_at_source
- \+ *lemma* ext_chart_at_open_source
- \+ *lemma* mem_ext_chart_source
- \+ *lemma* ext_chart_at_to_inv
- \+ *lemma* ext_chart_at_source_mem_nhds
- \+ *lemma* ext_chart_at_continuous_on_to_fun
- \+ *lemma* ext_chart_at_continuous_at_to_fun
- \+ *lemma* ext_chart_at_continuous_on_inv_fun
- \+ *lemma* ext_chart_at_target_mem_nhds_within
- \+ *lemma* nhds_within_ext_chart_target_eq
- \+ *lemma* ext_chart_continuous_at_inv_fun'
- \+ *lemma* ext_chart_continuous_at_inv_fun
- \+ *lemma* ext_chart_preimage_mem_nhds_within'
- \+ *lemma* ext_chart_preimage_mem_nhds_within
- \+ *lemma* ext_chart_preimage_mem_nhds
- \+ *lemma* ext_chart_preimage_inter_eq
- \+ *lemma* ext_chart_model_space_eq_id
- \+ *def* ext_chart_at

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_within_at.union



## [2020-01-16 11:40:38](https://github.com/leanprover-community/mathlib/commit/4f81942)
feat(logic/basic): forall_or_distrib ([#1887](https://github.com/leanprover-community/mathlib/pull/1887))
#### Estimated changes
Modified src/logic/basic.lean
- \+ *theorem* forall_or_distrib_right



## [2020-01-16 10:23:06](https://github.com/leanprover-community/mathlib/commit/58610ff)
chore(order/filter/*): use `s ∈ f` instead of `s ∈ f.sets` ([#1885](https://github.com/leanprover-community/mathlib/pull/1885))
Other changes:
* compose old `mem_infi` and `mem_binfi` with `mem_Union` and
  `mem_bUnion_iff` to avoid `.sets` and simplify usage (it was
  `rw [mem_infi, mem_Union]` every time)
* drop `lift_sets_eq` and `mem_lift_iff` in favor of `mem_lift_sets`
#### Estimated changes
Modified src/order/filter/basic.lean


Modified src/order/filter/lift.lean
- \+/\- *lemma* mem_lift_sets
- \+/\- *lemma* mem_lift
- \+/\- *lemma* lift_mono'
- \+/\- *lemma* mem_lift'
- \+/\- *lemma* mem_lift'_sets
- \+/\- *lemma* lift'_mono'
- \+/\- *lemma* lift'_cong
- \+/\- *lemma* principal_le_lift'
- \- *lemma* lift_sets_eq
- \- *lemma* mem_lift_iff

Modified src/order/filter/pointwise.lean


Modified src/topology/algebra/ordered.lean




## [2020-01-16 08:11:17](https://github.com/leanprover-community/mathlib/commit/05457fd)
feat(analysis/calculus/tangent_cone): define and use `tangent_cone_congr` ([#1886](https://github.com/leanprover-community/mathlib/pull/1886))
* feat(analysis/calculus/tangent_cone): define and use `tangent_cone_congr`
This way some proofs become shorter and hopefully more readable.
* Add a docstring
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean
- \+ *lemma* tangent_cone_mono_nhds
- \+ *lemma* tangent_cone_congr
- \+/\- *lemma* tangent_cone_inter_nhds
- \+ *lemma* unique_diff_within_at.mono_nhds
- \+/\- *lemma* unique_diff_within_at.mono
- \+ *lemma* unique_diff_within_at_congr



## [2020-01-15 15:04:46](https://github.com/leanprover-community/mathlib/commit/b3ed6e6)
chore(*): use `ne_` instead of `neq_` in lemma names ([#1878](https://github.com/leanprover-community/mathlib/pull/1878))
One exception: `mem_sets_of_neq_bot` is now `mem_sets_of_eq_bot`
because it has an equality as an assumption.
Also add `filter.infi_ne_bot_(iff_?)of_directed'` with a different
`nonempty` assumption, and use it to simplify the proof of
`lift_ne_bot_iff`.
#### Estimated changes
Modified scripts/nolints.txt


Modified src/order/bounded_lattice.lean
- \+ *theorem* ne_bot_of_le_ne_bot
- \- *theorem* neq_bot_of_le_neq_bot

Modified src/order/filter/basic.lean
- \+ *lemma* forall_sets_ne_empty_iff_ne_bot
- \+ *lemma* mem_sets_of_eq_bot
- \+ *lemma* comap_ne_bot
- \+ *lemma* comap_ne_bot_of_surj
- \+ *lemma* pure_ne_bot
- \+ *lemma* infi_ne_bot_of_directed'
- \+ *lemma* infi_ne_bot_of_directed
- \+ *lemma* infi_ne_bot_iff_of_directed'
- \+ *lemma* infi_ne_bot_iff_of_directed
- \+ *lemma* prod_ne_bot
- \- *lemma* forall_sets_neq_empty_iff_neq_bot
- \- *lemma* mem_sets_of_neq_bot
- \- *lemma* comap_neq_bot
- \- *lemma* comap_neq_bot_of_surj
- \- *lemma* pure_neq_bot
- \- *lemma* infi_neq_bot_of_directed
- \- *lemma* infi_neq_bot_iff_of_directed
- \- *lemma* prod_neq_bot

Modified src/order/filter/lift.lean
- \+ *lemma* lift_ne_bot_iff
- \+ *lemma* lift'_ne_bot_iff
- \- *lemma* lift_neq_bot_iff
- \- *lemma* lift'_neq_bot_iff

Modified src/order/filter/pointwise.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean
- \+ *lemma* nhds_ne_bot
- \- *lemma* nhds_neq_bot

Modified src/topology/constructions.lean


Modified src/topology/continuous_on.lean


Modified src/topology/dense_embedding.lean
- \+ *lemma* comap_nhds_ne_bot
- \- *lemma* comap_nhds_neq_bot

Modified src/topology/order.lean


Modified src/topology/separation.lean
- \+ *lemma* eq_of_nhds_ne_bot
- \- *lemma* eq_of_nhds_neq_bot

Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-01-15 10:13:40](https://github.com/leanprover-community/mathlib/commit/8e70388)
docs(README): add new maintainers ([#1881](https://github.com/leanprover-community/mathlib/pull/1881))
#### Estimated changes
Modified README.md




## [2020-01-15 09:15:30](https://github.com/leanprover-community/mathlib/commit/d614736)
feat(linear_algebra/tensor_product): tensor product right identity ([#1880](https://github.com/leanprover-community/mathlib/pull/1880))
* feat(linear_algebra/tensor_product): tensor product right identity
* Golf proof of tensor_product.rid
* Add missing docstrings
#### Estimated changes
Modified scripts/nolints.txt


Modified src/linear_algebra/tensor_product.lean




## [2020-01-15 07:24:37](https://github.com/leanprover-community/mathlib/commit/819939f)
refactor(order/lattice): generalize `directed_of_mono` ([#1879](https://github.com/leanprover-community/mathlib/pull/1879))
It suffices to have `semilattice_sup`, not `decidable_linear_order`.
Also add `directed_of_antimono`.
#### Estimated changes
Modified src/order/basic.lean
- \- *lemma* directed_of_mono

Modified src/order/lattice.lean
- \+ *lemma* directed_of_mono
- \+ *lemma* directed_of_antimono

Modified src/topology/bases.lean


Modified src/topology/sequences.lean




## [2020-01-14 16:00:47](https://github.com/leanprover-community/mathlib/commit/9f7ae9a)
chore(data/set/lattice): use `∃ x ∈ s` instead of `∃ x, x ∈ s ∧` in `mem_bUnion_iff` ([#1877](https://github.com/leanprover-community/mathlib/pull/1877))
This seems to be more in line with the rest of the library
#### Estimated changes
Modified src/data/semiquot.lean
- \+/\- *def* get

Modified src/data/set/lattice.lean


Modified src/group_theory/subgroup.lean
- \+/\- *lemma* mem_conjugates_of_set_iff

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/gromov_hausdorff.lean




## [2020-01-14 14:20:21](https://github.com/leanprover-community/mathlib/commit/416b7d8)
fix doc strings ([#1876](https://github.com/leanprover-community/mathlib/pull/1876))
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean




## [2020-01-14 06:33:00](https://github.com/leanprover-community/mathlib/commit/e095e30)
feat(analysis/ODE/gronwall): A version of Grönwall's inequality ([#1846](https://github.com/leanprover-community/mathlib/pull/1846))
* feat(analysis/ODE/gronwall): A version of Gronwall's inequality
+ uniqueness of solutions of an ODE with a Lipschitz continuous RHS
* Consistently use ö in Grönwall
* Fix a typo
* Fix docs, drop assumption `0 < K`, add a version for functions `ℝ → ℝ`.
* Fix docs
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Fix docs
#### Estimated changes
Modified docs/references.bib


Created src/analysis/ODE/gronwall.lean
- \+ *lemma* gronwall_bound_K0
- \+ *lemma* gronwall_bound_of_K_ne_0
- \+ *lemma* has_deriv_at_gronwall_bound
- \+ *lemma* has_deriv_at_gronwall_bound_shift
- \+ *lemma* gronwall_bound_x0
- \+ *lemma* gronwall_bound_ε0
- \+ *lemma* gronwall_bound_ε0_δ0
- \+ *lemma* gronwall_bound_continuous_ε
- \+ *theorem* le_gronwall_bound_of_liminf_deriv_right_le
- \+ *theorem* norm_le_gronwall_bound_of_norm_deriv_right_le
- \+ *theorem* dist_le_of_approx_trajectories_ODE_of_mem_set
- \+ *theorem* dist_le_of_approx_trajectories_ODE
- \+ *theorem* dist_le_of_trajectories_ODE_of_mem_set
- \+ *theorem* dist_le_of_trajectories_ODE
- \+ *theorem* ODE_solution_unique_of_mem_set
- \+ *theorem* ODE_solution_unique

Modified src/analysis/calculus/mean_value.lean
- \+ *lemma* image_le_of_liminf_slope_right_lt_deriv_boundary'
- \+/\- *lemma* image_le_of_liminf_slope_right_lt_deriv_boundary



## [2020-01-12 06:48:46](https://github.com/leanprover-community/mathlib/commit/c5d91bc)
feat(topology/algebra/ordered): add order topology for partial orders… ([#1276](https://github.com/leanprover-community/mathlib/pull/1276))
* feat(topology/algebra/ordered): doc, add convergence in ordered groups criterion
* docstring
* reviewer's comments
#### Estimated changes
Modified scripts/nolints.txt


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/specific_limits.lean


Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/integration.lean
- \+/\- *lemma* approx_apply
- \+/\- *lemma* approx_comp
- \+/\- *lemma* supr_approx_apply

Modified src/tactic/lint.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* nhds_eq_order
- \+ *lemma* tendsto_order
- \+ *lemma* nhds_order_unbounded
- \+ *lemma* tendsto_order_unbounded
- \+ *lemma* nhds_top_order
- \+ *lemma* nhds_bot_order
- \+ *lemma* order_topology.t2_space
- \+/\- *lemma* Sup_mem_closure
- \+/\- *lemma* Inf_mem_closure
- \+/\- *lemma* Sup_mem_of_is_closed
- \+/\- *lemma* Inf_mem_of_is_closed
- \+/\- *lemma* cSup_mem_closure
- \+/\- *lemma* cInf_mem_closure
- \+/\- *lemma* cSup_mem_of_is_closed
- \+/\- *lemma* cInf_mem_of_is_closed
- \+ *lemma* order_topology_of_nhds_abs
- \+/\- *lemma* tendsto_at_top_supr_nat
- \+/\- *lemma* tendsto_at_top_infi_nat
- \+/\- *lemma* supr_eq_of_tendsto
- \+/\- *lemma* infi_eq_of_tendsto
- \+ *lemma* decidable_linear_ordered_comm_group.tendsto_nhds
- \- *lemma* nhds_eq_orderable
- \- *lemma* tendsto_orderable
- \- *lemma* nhds_orderable_unbounded
- \- *lemma* tendsto_orderable_unbounded
- \- *lemma* nhds_top_orderable
- \- *lemma* nhds_bot_orderable
- \- *lemma* orderable_topology.t2_space
- \- *lemma* orderable_topology_of_nhds_abs
- \+ *theorem* induced_order_topology'
- \+ *theorem* induced_order_topology
- \- *theorem* induced_orderable_topology'
- \- *theorem* induced_orderable_topology
- \+ *def* preorder.topology

Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/gromov_hausdorff.lean




## [2020-01-11 14:51:07](https://github.com/leanprover-community/mathlib/commit/25dded2)
chore(measure_theory/bochner_integration): make proofs shorter ([#1871](https://github.com/leanprover-community/mathlib/pull/1871))
* More consistent use of the dot notation
* Revert "More consistent use of the dot notation"
This reverts commit 854a499a9be105b42ca486eb25593a2379b07404.
* Revert "Revert "More consistent use of the dot notation""
This reverts commit 57aaf22695c031fc8dcc581110cc9d1ac397f695.
* fix things
#### Estimated changes
Modified src/measure_theory/ae_eq_fun.lean
- \+/\- *lemma* smul_mk
- \+/\- *def* comp_edist

Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* integral_eq
- \+ *lemma* integral_undef
- \+ *lemma* integral_non_integrable
- \+ *lemma* integral_non_measurable
- \+/\- *lemma* integral_add
- \+/\- *lemma* integral_sub
- \+/\- *lemma* integral_smul
- \- *lemma* integral_eq_zero_of_non_measurable
- \- *lemma* integral_eq_zero_of_non_integrable
- \+/\- *def* simple_func

Modified src/measure_theory/borel_space.lean
- \+ *lemma* measurable.smul'
- \+ *lemma* measurable.smul
- \+/\- *lemma* measurable_dist
- \+ *lemma* measurable.dist
- \+/\- *lemma* measurable_nndist
- \+ *lemma* measurable.nndist
- \+/\- *lemma* measurable_edist
- \+ *lemma* measurable.edist
- \+/\- *lemma* measurable_norm
- \+ *lemma* measurable.norm
- \+/\- *lemma* measurable_nnnorm
- \+ *lemma* measurable.nnnorm
- \+ *lemma* measurable.coe_nnnorm
- \- *lemma* measurable_smul'
- \- *lemma* measurable_smul
- \- *lemma* measurable_dist'
- \- *lemma* measurable_nndist'
- \- *lemma* measurable_edist'
- \- *lemma* measurable_norm'
- \- *lemma* measurable_nnnorm'
- \- *lemma* measurable_coe_nnnorm

Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable_smul_iff
- \- *lemma* integrable.smul_iff
- \+/\- *def* l1

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_zero

Modified src/measure_theory/simple_func_dense.lean




## [2020-01-11 00:42:53](https://github.com/leanprover-community/mathlib/commit/f67df78)
chore(algebra/module): add some missing `*_cast` tags ([#1863](https://github.com/leanprover-community/mathlib/pull/1863))
#### Estimated changes
Modified src/algebra/module.lean
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_sub



## [2020-01-10 01:05:49](https://github.com/leanprover-community/mathlib/commit/ff2a41e)
refactor(docs): additions, modifications, reorganization ([#1815](https://github.com/leanprover-community/mathlib/pull/1815))
* move cc.md to tactics.md
* change h3 to h2
* remove h3
* update simp.md headers
* updates to casts.md
* update holes.md
* update docstrings
* add commands.md
* hole commands in emacs
* reference library_search from find
* delete casts.md
* minor updates
* minor fixes
* more minor fixes
* fix header level
* updating mathlib-overview and removing a bunch of useless  files
#### Estimated changes
Created docs/commands.md
- \+ *lemma* some_class.bar_assoc
- \+ *theorem* alias1
- \+ *theorem* alias2
- \+ *def* f

Deleted docs/extras/casts.md
- \- *def* from_R_to_C

Deleted docs/extras/cc.md


Modified docs/extras/conv.md


Modified docs/extras/simp.md


Modified docs/extras/tactic_writing.md


Modified docs/extras/well_founded_recursion.md


Modified docs/holes.md
- \+ *def* foo

Modified docs/mathlib-overview.md


Modified docs/tactics.md
- \- *lemma* some_class.bar_assoc
- \- *def* f

Deleted docs/theories/functions.md


Deleted docs/theories/groups.md


Deleted docs/theories/integers.md


Deleted docs/theories/linear_algebra.md


Deleted docs/theories/measure.md


Modified docs/theories/naturals.md


Deleted docs/theories/number_theory.md


Deleted docs/theories/orders.md


Deleted docs/theories/polynomials.md


Deleted docs/theories/relations.md


Deleted docs/theories/rings_fields.md


Modified src/tactic/alias.lean


Modified src/tactic/core.lean


Modified src/tactic/where.lean




## [2020-01-09 22:58:55](https://github.com/leanprover-community/mathlib/commit/baa3aa7)
refactor(data/set/basic): change def of `⊂` to match `<` ([#1862](https://github.com/leanprover-community/mathlib/pull/1862))
#### Estimated changes
Modified src/data/finset.lean


Modified src/data/set/basic.lean
- \+ *lemma* ssubset_iff_subset_ne
- \- *lemma* ssubset_iff_subset_not_subset
- \+/\- *theorem* not_subset
- \+/\- *theorem* ssubset_def
- \+ *theorem* eq_or_ssubset_of_subset
- \+ *theorem* nonempty_diff
- \+/\- *def* strict_subset

Modified src/data/set/finite.lean


Modified src/data/set/lattice.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* le_def
- \+/\- *lemma* le_def'
- \+ *lemma* lt_def
- \+ *lemma* not_le_iff_exists
- \+ *lemma* exists_of_lt
- \+ *lemma* lt_iff_le_and_exists
- \+/\- *theorem* of_le_apply
- \+/\- *def* of_le

Modified src/order/zorn.lean




## [2020-01-09 21:23:09](https://github.com/leanprover-community/mathlib/commit/d7cebcf)
feat(linear_algebra/multilinear): basics of multilinear maps ([#1814](https://github.com/leanprover-community/mathlib/pull/1814))
* multilinear maps
* progress
* isomorphisms
* Update src/logic/function.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* better docstring
* variable module
* dep cons
* make everything dependent
* remove print statement
* fix build
* Update src/linear_algebra/multilinear.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* Update src/linear_algebra/multilinear.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* fixes
* docstrings
* reviewer's comments
* cleanup
#### Estimated changes
Modified archive/cubing_a_cube.lean


Modified src/data/fin.lean
- \+ *lemma* succ_inj
- \+ *lemma* injective_succ
- \+ *lemma* cast_succ_ne_last
- \+ *lemma* injective_cast_succ
- \+/\- *lemma* tail_cons
- \+/\- *lemma* cons_succ
- \+/\- *lemma* cons_zero
- \+ *lemma* cons_update
- \+ *lemma* update_cons_zero
- \+ *lemma* cons_self_tail
- \+ *lemma* tail_update_zero
- \+ *lemma* tail_update_succ
- \+ *def* fin_zero_elim'
- \+/\- *def* tail
- \+/\- *def* cons
- \- *def* {u}

Created src/linear_algebra/multilinear.lean
- \+ *lemma* map_add
- \+ *lemma* map_smul
- \+ *lemma* map_coord_zero
- \+ *lemma* map_zero
- \+ *lemma* add_apply
- \+ *lemma* neg_apply
- \+ *lemma* zero_apply
- \+ *lemma* cons_add
- \+ *lemma* cons_smul
- \+ *lemma* smul_apply
- \+ *theorem* ext
- \+ *def* to_linear_map
- \+ *def* linear_to_multilinear_equiv_multilinear
- \+ *def* multilinear_to_linear_equiv_multilinear

Modified src/logic/function.lean
- \+/\- *lemma* update_same
- \+/\- *lemma* update_noteq
- \+ *lemma* update_eq_self
- \+ *lemma* update_comp

Modified src/order/filter/basic.lean




## [2020-01-09 04:14:44](https://github.com/leanprover-community/mathlib/commit/39c10cd)
docs(tactic/tauto): elaborate tauto docs [ci skip] ([#1869](https://github.com/leanprover-community/mathlib/pull/1869))
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/tauto.lean




## [2020-01-09 02:47:17](https://github.com/leanprover-community/mathlib/commit/5289994)
feat(analysis/calculus/mean_value): add generalized "fencing" inequality ([#1838](https://github.com/leanprover-community/mathlib/pull/1838))
* feat(analysis/calculus/mean_value): add generalized "fencing" inequality
This version can be used to deduce, e.g., Gronwall inequality as well
as its generalized version that deals with approximate solutions.
* Adjust to merged branches, use `liminf` instead of `limsup`, add more variations
* Go through dim-1 liminf estimates
* Fix: use `b ∈ Ioc a c` as a hypothesis for `I??_mem_nhds_within_Iio`
* Update src/analysis/calculus/mean_value.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Drop `Prop`-valued `variables`, add some docs
* More docstrings
* Drop `Prop`-valued `variables`, drop assumption `x ∉ s`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_within_at_iff_tendsto_slope'
- \+ *lemma* has_deriv_within_at.limsup_slope_le
- \+ *lemma* has_deriv_within_at.limsup_slope_le'
- \+ *lemma* has_deriv_within_at.liminf_right_slope_le
- \+ *lemma* has_deriv_within_at.limsup_norm_slope_le
- \+ *lemma* has_deriv_within_at.limsup_slope_norm_le
- \+ *lemma* has_deriv_within_at.liminf_right_norm_slope_le
- \+ *lemma* has_deriv_within_at.liminf_right_slope_norm_le

Modified src/analysis/calculus/mean_value.lean
- \+ *lemma* image_le_of_liminf_slope_right_lt_deriv_boundary
- \+ *lemma* image_le_of_liminf_slope_right_le_deriv_boundary
- \+ *lemma* image_le_of_deriv_right_lt_deriv_boundary'
- \+ *lemma* image_le_of_deriv_right_lt_deriv_boundary
- \+ *lemma* image_le_of_deriv_right_le_deriv_boundary
- \+ *lemma* image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary
- \+ *lemma* image_norm_le_of_norm_deriv_right_lt_deriv_boundary'
- \+ *lemma* image_norm_le_of_norm_deriv_right_lt_deriv_boundary
- \+ *lemma* image_norm_le_of_norm_deriv_right_le_deriv_boundary'
- \+ *lemma* image_norm_le_of_norm_deriv_right_le_deriv_boundary
- \+ *theorem* norm_image_sub_le_of_norm_deriv_right_le_segment
- \+ *theorem* norm_image_sub_le_of_norm_deriv_le_segment'
- \+/\- *theorem* norm_image_sub_le_of_norm_deriv_le_segment
- \+ *theorem* norm_image_sub_le_of_norm_deriv_le_segment_01'
- \+ *theorem* norm_image_sub_le_of_norm_deriv_le_segment_01

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* filter.tendsto.norm
- \+ *lemma* filter.tendsto.nnnorm

Modified src/topology/algebra/ordered.lean
- \+ *lemma* Ioo_mem_nhds_within_Iio
- \+ *lemma* Ioc_mem_nhds_within_Iio
- \+ *lemma* Ico_mem_nhds_within_Iio
- \+ *lemma* Icc_mem_nhds_within_Iio



## [2020-01-08 20:16:58](https://github.com/leanprover-community/mathlib/commit/9afc6f2)
docs(tactics): tautology ([#1860](https://github.com/leanprover-community/mathlib/pull/1860))
* added a short description of the tautology tactic
* added a short description of the tautology tactic
* Update docs/tactics.md
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified docs/tactics.md




## [2020-01-08 13:16:54](https://github.com/leanprover-community/mathlib/commit/92841c2)
refactor(analysis/asymptotics): introduce `is_O_with` ([#1857](https://github.com/leanprover-community/mathlib/pull/1857))
* refactor(analysis/asymptotics): introduce `is_O_with`
I use it to factor out common parts of the proofs of facts about
`is_O` and `is_o`. It can also be used with `principal s` filter to
operate with `∀ x ∈ s, ∥f x∥ ≤ C * ∥g x∥` is a manner similar to `is_O`.
* lint
* Fix compile
* Drop `(s)mul_same` lemmas.
It's easy to use `(s)mul_is_O (is_O_refl _ _)` or `(is_O_refl _
_).mul_is_o _` instead
* docs: say explicitly that `is_O` is better than `is_O_with`
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *lemma* is_O_with_fst_prod
- \+ *lemma* is_O_with_snd_prod
- \+ *lemma* is_O_fst_prod
- \+ *lemma* is_O_snd_prod
- \+ *lemma* is_O_with.prod_rightl
- \+/\- *lemma* is_O.prod_rightl
- \+/\- *lemma* is_o.prod_rightl
- \+ *lemma* is_O_with.prod_rightr
- \+/\- *lemma* is_O.prod_rightr
- \+/\- *lemma* is_o.prod_rightr
- \+ *lemma* is_O_with.prod_left_same
- \+ *lemma* is_O_with.prod_left
- \+ *lemma* is_O_with.prod_left_fst
- \+ *lemma* is_O_with.prod_left_snd
- \+ *lemma* is_O_with_prod_left
- \+ *lemma* is_O.prod_left
- \+ *lemma* is_O.prod_left_fst
- \+ *lemma* is_O.prod_left_snd
- \+ *lemma* is_O_prod_left
- \+ *lemma* is_o.prod_left
- \+ *lemma* is_o.prod_left_fst
- \+ *lemma* is_o.prod_left_snd
- \+ *lemma* is_o_prod_left
- \+ *theorem* is_O_with.is_O
- \+ *theorem* is_o.is_O_with
- \+ *theorem* is_o.is_O
- \+ *theorem* is_O_with.weaken
- \+ *theorem* is_O_with.exists_pos
- \+ *theorem* is_O.exists_pos
- \+ *theorem* is_O_with.exists_nonneg
- \+ *theorem* is_O.exists_nonneg
- \+ *theorem* is_O_with_congr
- \+ *theorem* is_O_with.congr'
- \+ *theorem* is_O_with.congr
- \+ *theorem* is_O_with.congr_left
- \+ *theorem* is_O_with.congr_right
- \+ *theorem* is_O_with.congr_const
- \+/\- *theorem* is_O_congr
- \+ *theorem* is_O.congr'
- \+/\- *theorem* is_O.congr
- \+/\- *theorem* is_O.congr_left
- \+/\- *theorem* is_O.congr_right
- \+/\- *theorem* is_o_congr
- \+ *theorem* is_o.congr'
- \+/\- *theorem* is_o.congr
- \+/\- *theorem* is_o.congr_left
- \+/\- *theorem* is_o.congr_right
- \+ *theorem* is_O_with.comp_tendsto
- \+ *theorem* is_O.comp_tendsto
- \+ *theorem* is_o.comp_tendsto
- \+ *theorem* is_O_with.mono
- \+/\- *theorem* is_O.mono
- \+/\- *theorem* is_o.mono
- \+ *theorem* is_O_with.trans
- \+/\- *theorem* is_O.trans
- \+ *theorem* is_o.trans_is_O_with
- \+/\- *theorem* is_o.trans_is_O
- \+ *theorem* is_O_with.trans_is_o
- \+/\- *theorem* is_O.trans_is_o
- \+/\- *theorem* is_o.trans
- \+ *theorem* is_o.trans'
- \+ *theorem* is_O_with_of_le'
- \+ *theorem* is_O_with_of_le
- \+ *theorem* is_O_of_le'
- \+ *theorem* is_O_of_le
- \+ *theorem* is_O_with_refl
- \+/\- *theorem* is_O_refl
- \+ *theorem* is_O_with.trans_le
- \+ *theorem* is_O.trans_le
- \+ *theorem* is_O_with_bot
- \+ *theorem* is_O_bot
- \+ *theorem* is_o_bot
- \+ *theorem* is_O_with.join
- \+ *theorem* is_O_with.join'
- \+ *theorem* is_O.join
- \+ *theorem* is_o.join
- \+ *theorem* is_O_with_norm_right
- \+/\- *theorem* is_O_norm_right
- \+/\- *theorem* is_o_norm_right
- \+ *theorem* is_O_with_norm_left
- \+/\- *theorem* is_O_norm_left
- \+/\- *theorem* is_o_norm_left
- \+ *theorem* is_O_with_norm_norm
- \+ *theorem* is_O_norm_norm
- \+ *theorem* is_o_norm_norm
- \+ *theorem* is_O_with_neg_right
- \+/\- *theorem* is_O_neg_right
- \+/\- *theorem* is_o_neg_right
- \+ *theorem* is_O_with_neg_left
- \+/\- *theorem* is_O_neg_left
- \+/\- *theorem* is_o_neg_left
- \+ *theorem* is_O_with.add
- \+/\- *theorem* is_O.add
- \+/\- *theorem* is_o.add
- \+ *theorem* is_O.add_is_o
- \+ *theorem* is_o.add_is_O
- \+ *theorem* is_O_with.add_is_o
- \+ *theorem* is_o.add_is_O_with
- \+ *theorem* is_O_with.sub
- \+ *theorem* is_O_with.sub_is_o
- \+/\- *theorem* is_O.sub
- \+/\- *theorem* is_o.sub
- \+ *theorem* is_O_with.symm
- \+ *theorem* is_O_with_comm
- \+/\- *theorem* is_O.symm
- \+/\- *theorem* is_O_comm
- \+/\- *theorem* is_o.symm
- \+/\- *theorem* is_o_comm
- \+ *theorem* is_O_with.triangle
- \+ *theorem* is_O.triangle
- \+ *theorem* is_o.triangle
- \+/\- *theorem* is_O.congr_of_sub
- \+/\- *theorem* is_o.congr_of_sub
- \+/\- *theorem* is_o_zero
- \+ *theorem* is_O_with_zero
- \+/\- *theorem* is_O_zero
- \+/\- *theorem* is_O_refl_left
- \+/\- *theorem* is_o_refl_left
- \+ *theorem* is_O_with_zero_right_iff
- \+/\- *theorem* is_O_zero_right_iff
- \+/\- *theorem* is_o_zero_right_iff
- \+ *theorem* is_O_with_const_const
- \+ *theorem* is_O_const_const
- \+ *theorem* is_O_with_const_one
- \+/\- *theorem* is_O_const_one
- \+ *theorem* is_o_const_iff_is_o_one
- \+ *theorem* is_o_const_iff
- \+ *theorem* is_O_const_of_tendsto
- \+/\- *theorem* is_o_one_iff
- \+/\- *theorem* is_O_one_of_tendsto
- \+ *theorem* is_O.trans_tendsto_nhds
- \+/\- *theorem* is_O.trans_tendsto
- \+/\- *theorem* is_o.trans_tendsto
- \+ *theorem* is_O_with_const_mul_self
- \+ *theorem* is_O_const_mul_self
- \+ *theorem* is_O_with.const_mul_left
- \+ *theorem* is_O.const_mul_left
- \+ *theorem* is_O_with_self_const_mul'
- \+ *theorem* is_O_with_self_const_mul
- \+ *theorem* is_O_self_const_mul'
- \+ *theorem* is_O_self_const_mul
- \+ *theorem* is_O_const_mul_left_iff'
- \+/\- *theorem* is_O_const_mul_left_iff
- \+ *theorem* is_o.const_mul_left
- \+ *theorem* is_o_const_mul_left_iff'
- \+/\- *theorem* is_o_const_mul_left_iff
- \+ *theorem* is_O_with.of_const_mul_right
- \+ *theorem* is_O.of_const_mul_right
- \+ *theorem* is_O_with.const_mul_right'
- \+ *theorem* is_O_with.const_mul_right
- \+ *theorem* is_O.const_mul_right'
- \+ *theorem* is_O.const_mul_right
- \+ *theorem* is_O_const_mul_right_iff'
- \+/\- *theorem* is_O_const_mul_right_iff
- \+ *theorem* is_o.of_const_mul_right
- \+ *theorem* is_o.const_mul_right'
- \+ *theorem* is_o.const_mul_right
- \+ *theorem* is_o_const_mul_right_iff'
- \+ *theorem* is_o_const_mul_right_iff
- \+ *theorem* is_O_with.mul
- \+ *theorem* is_O.mul
- \+ *theorem* is_O.mul_is_o
- \+ *theorem* is_o.mul_is_O
- \+ *theorem* is_o.mul
- \+ *theorem* is_O_with.const_smul_left
- \+/\- *theorem* is_O_const_smul_left_iff
- \+/\- *theorem* is_o_const_smul_left
- \+/\- *theorem* is_o_const_smul_left_iff
- \+/\- *theorem* is_O_const_smul_right
- \+/\- *theorem* is_o_const_smul_right
- \+ *theorem* is_O_with.smul
- \+ *theorem* is_O.smul
- \+ *theorem* is_O.smul_is_o
- \+ *theorem* is_o.smul_is_O
- \+ *theorem* is_o.smul
- \+ *theorem* is_o.tendsto_0
- \+ *theorem* is_O_with.right_le_sub_of_lt_1
- \+ *theorem* is_O_with.right_le_add_of_lt_1
- \- *theorem* is_O.comp
- \- *theorem* is_o.comp
- \- *theorem* is_o.to_is_O
- \- *theorem* is_o_join
- \- *theorem* is_O_congr_left
- \- *theorem* is_o_congr_left
- \- *theorem* is_O_congr_right
- \- *theorem* is_o_congr_right
- \- *theorem* is_O_iff
- \- *theorem* is_O_join
- \- *theorem* is_O.tri
- \- *theorem* is_o.tri
- \- *theorem* is_O_prod_left
- \- *theorem* is_o_prod_left
- \- *theorem* is_O_const_mul_left
- \- *theorem* is_o_const_mul_left
- \- *theorem* is_O_of_is_O_const_mul_right
- \- *theorem* is_o_of_is_o_const_mul_right
- \- *theorem* is_o_const_mul_right
- \- *theorem* is_O_mul
- \- *theorem* is_o_mul_left
- \- *theorem* is_o_mul_right
- \- *theorem* is_o_mul
- \- *theorem* is_O_const_smul_left
- \- *theorem* is_O_smul
- \- *theorem* is_o_smul
- \- *theorem* tendsto_nhds_zero_of_is_o
- \+ *def* is_O_with
- \+/\- *def* is_O
- \+/\- *def* is_o

Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/operator_norm.lean




## [2020-01-07 00:44:17](https://github.com/leanprover-community/mathlib/commit/69e07e2)
chore(order/zorn): add docstrings, drop `chain.directed` ([#1861](https://github.com/leanprover-community/mathlib/pull/1861))
`chain.directed_on` is almost the same and uses a named predicate.
#### Estimated changes
Modified src/order/zorn.lean
- \- *theorem* chain.directed
- \+/\- *def* super_chain
- \+/\- *def* succ_chain



## [2020-01-06 23:48:35](https://github.com/leanprover-community/mathlib/commit/a1b7312)
feat(topology/maps): a few lemmas about `is_open_map` ([#1855](https://github.com/leanprover-community/mathlib/pull/1855))
* feat(topology/maps): a few lemmas about `is_open_map`
Also fix arguments order in all `*.comp` in this file.
* Use restricted version of `continuous_of_left_inverse` to prove non-restricted
* Fix compile by reverting a name change
#### Estimated changes
Modified src/topology/constructions.lean
- \+ *lemma* is_open.open_embedding_subtype_val
- \+ *lemma* is_open.is_open_map_subtype_val
- \+ *lemma* is_open_map.restrict
- \+ *lemma* is_closed.closed_embedding_subtype_val
- \- *lemma* subtype_val.open_embedding
- \- *lemma* subtype_val.closed_embedding

Modified src/topology/continuous_on.lean
- \+ *theorem* is_open_map.continuous_on_image_of_left_inv_on
- \+ *theorem* is_open_map.continuous_on_range_of_left_inverse

Modified src/topology/maps.lean
- \+/\- *lemma* embedding.comp
- \+/\- *lemma* is_open_map_iff_nhds_le
- \+ *lemma* is_open_range
- \+ *lemma* nhds_le
- \+/\- *lemma* open_embedding.comp
- \+/\- *lemma* closed_embedding.comp
- \- *lemma* inducing.comp
- \+/\- *def* quotient_map



## [2020-01-06 03:49:33](https://github.com/leanprover-community/mathlib/commit/15c434a)
chore(*): various simple lemmas about `*_equiv`, add missing attrs ([#1854](https://github.com/leanprover-community/mathlib/pull/1854))
* chore(*): various simple lemmas about `*_equiv`, add missing attrs
* Fix compile of `ring_theory/localization`
#### Estimated changes
Modified src/data/equiv/algebra.lean
- \+/\- *lemma* map_eq_one_iff
- \+/\- *lemma* map_ne_one_iff
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_one
- \+/\- *lemma* map_add
- \+/\- *lemma* map_zero
- \+ *lemma* map_eq_zero_iff
- \+ *lemma* map_ne_zero_iff
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_neg_one

Modified src/data/set/function.lean
- \+ *lemma* inj_on.to_bij_on

Modified src/linear_algebra/basic.lean
- \+ *theorem* map_add
- \+ *theorem* map_zero
- \+ *theorem* map_neg
- \+ *theorem* map_sub
- \+ *theorem* map_smul
- \+ *theorem* map_eq_zero_iff
- \+ *theorem* map_ne_zero_iff
- \+/\- *def* refl
- \+/\- *def* symm
- \+/\- *def* trans
- \+ *def* to_add_equiv

Modified src/ring_theory/localization.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* map_eq_zero_iff
- \+ *theorem* coe_comp_coe_symm
- \+ *theorem* coe_symm_comp_coe



## [2020-01-05 21:25:17](https://github.com/leanprover-community/mathlib/commit/63670b5)
feat(data/real/nnreal): add a few simple lemmas ([#1856](https://github.com/leanprover-community/mathlib/pull/1856))
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* div_pos
- \+ *lemma* div_mul_cancel
- \+ *lemma* mul_div_cancel
- \+ *lemma* mul_div_cancel'
- \+ *lemma* half_pos



## [2020-01-04 15:28:27](https://github.com/leanprover-community/mathlib/commit/585e107)
feat(topology/algebra/module): continuous linear equiv ([#1839](https://github.com/leanprover-community/mathlib/pull/1839))
* feat(topology/algebra/module): continuous linear equiv
* linting
* reviewer's comments
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_within_at.unique_diff_within_at_of_continuous_linear_equiv

Modified src/analysis/normed_space/banach.lean
- \+/\- *theorem* linear_equiv.is_bounded_inv
- \+ *def* linear_equiv.to_continuous_linear_equiv_of_continuous

Modified src/analysis/normed_space/finite_dimension.lean
- \+ *def* linear_map.to_continuous_linear_map
- \+ *def* linear_equiv.to_continuous_linear_equiv

Modified src/analysis/normed_space/operator_norm.lean


Modified src/topology/algebra/module.lean
- \+/\- *lemma* continuous_smul
- \+/\- *lemma* continuous.smul
- \+/\- *lemma* is_open_map_smul_of_unit
- \+/\- *lemma* is_closed_map_smul_of_unit
- \+/\- *lemma* is_open_map_smul_of_ne_zero
- \+/\- *lemma* is_closed_map_smul_of_ne_zero
- \+/\- *lemma* map_zero
- \+/\- *lemma* coe_coe
- \+/\- *lemma* zero_apply
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_zero'
- \+/\- *lemma* id_apply
- \+/\- *lemma* coe_id
- \+/\- *lemma* coe_id'
- \+/\- *lemma* one_apply
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_add'
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_neg'
- \+/\- *lemma* sub_apply
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_sub'
- \+/\- *lemma* coe_comp
- \+/\- *lemma* coe_comp'
- \+/\- *lemma* comp_add
- \+/\- *lemma* add_comp
- \+/\- *lemma* coe_apply
- \+/\- *lemma* coe_apply'
- \+/\- *lemma* smul_right_apply
- \+/\- *lemma* smul_right_one_one
- \+/\- *lemma* smul_right_one_eq_iff
- \+ *lemma* ext
- \+ *lemma* map_add
- \+ *lemma* map_sub
- \+ *lemma* map_smul
- \+ *lemma* map_neg
- \+ *lemma* symm_to_linear_equiv
- \+ *lemma* trans_to_linear_equiv
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+/\- *theorem* comp_zero
- \+/\- *theorem* zero_comp
- \+ *theorem* coe_apply
- \+ *theorem* apply_symm_apply
- \+ *theorem* symm_apply_apply
- \+/\- *def* zero
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* prod
- \+/\- *def* smul_right
- \+ *def* to_continuous_linear_map
- \+ *def* to_homeomorph



## [2020-01-02 22:16:08](https://github.com/leanprover-community/mathlib/commit/5c3606d)
feat(order/filter/basic): define `filter.eventually` and `filter.frequently` ([#1845](https://github.com/leanprover-community/mathlib/pull/1845))
* feat(order/filter/basic): define `filter.eventually` and `filter.frequently`
As suggested in [#119](https://github.com/leanprover-community/mathlib/pull/119)
* More lemmas, use notation
* Fix a typo
* Update src/order/filter/basic.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/order/filter/basic.lean
* Add a short file docstring
* Update src/order/filter/basic.lean
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* eventually_true
- \+ *lemma* eventually_of_forall
- \+ *lemma* eventually_false_iff_eq_bot
- \+ *lemma* eventually.mp
- \+ *lemma* eventually.mono
- \+ *lemma* eventually.frequently
- \+ *lemma* frequently.mp
- \+ *lemma* frequently.mono
- \+ *lemma* frequently.and_eventually
- \+ *lemma* frequently.exists
- \+ *lemma* eventually.exists
- \+ *lemma* frequently_iff_forall_eventually_exists_and



## [2020-01-02 19:10:24](https://github.com/leanprover-community/mathlib/commit/840bd1f)
feat(analysis/calculus/deriv): add aliases for `const op f` and `f op const` ([#1843](https://github.com/leanprover-community/mathlib/pull/1843))
* feat(analysis/calculus/deriv): add aliases for `const op f` and `f op const`
Often this leads to simpler answers.
* Docs
* Fix compile of `mean_value.lean`
* Drop comments, use `open_locale classical`
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_within_add_const
- \+ *lemma* deriv_add_const
- \+ *lemma* deriv_within_const_add
- \+ *lemma* deriv_const_add
- \+ *lemma* deriv_within_smul
- \+ *lemma* deriv_smul
- \+ *lemma* deriv_within_smul_const
- \+ *lemma* deriv_smul_const
- \+ *lemma* deriv_within_const_smul
- \+ *lemma* deriv_const_smul
- \+ *lemma* deriv_within_sub_const
- \+ *lemma* deriv_sub_const
- \+ *lemma* deriv_within_const_sub
- \+ *lemma* deriv_const_sub
- \+ *lemma* deriv_within_mul_const
- \+ *lemma* deriv_mul_const
- \+ *lemma* deriv_within_const_mul
- \+ *lemma* deriv_const_mul
- \- *lemma* deriv_within_smul'
- \- *lemma* deriv_smul'
- \+ *theorem* has_deriv_at_filter.add_const
- \+ *theorem* has_deriv_within_at.add_const
- \+ *theorem* has_deriv_at.add_const
- \+ *theorem* has_deriv_at_filter.const_add
- \+ *theorem* has_deriv_within_at.const_add
- \+ *theorem* has_deriv_at.const_add
- \+ *theorem* has_deriv_within_at.smul
- \+ *theorem* has_deriv_at.smul
- \+ *theorem* has_deriv_within_at.smul_const
- \+ *theorem* has_deriv_at.smul_const
- \+ *theorem* has_deriv_within_at.const_smul
- \+ *theorem* has_deriv_at.const_smul
- \+ *theorem* has_deriv_at_filter.sub_const
- \+ *theorem* has_deriv_within_at.sub_const
- \+ *theorem* has_deriv_at.sub_const
- \+ *theorem* has_deriv_at_filter.const_sub
- \+ *theorem* has_deriv_within_at.const_sub
- \+ *theorem* has_deriv_at.const_sub
- \+ *theorem* has_deriv_within_at.mul_const
- \+ *theorem* has_deriv_at.mul_const
- \+ *theorem* has_deriv_within_at.const_mul
- \+ *theorem* has_deriv_at.const_mul
- \- *theorem* has_deriv_within_at.smul'
- \- *theorem* has_deriv_at.smul'

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable_within_at.const_smul
- \+ *lemma* differentiable_at.const_smul
- \+ *lemma* differentiable_on.const_smul
- \+ *lemma* differentiable.const_smul
- \+ *lemma* fderiv_within_const_smul
- \+ *lemma* fderiv_const_smul
- \+ *lemma* differentiable_within_at.add_const
- \+ *lemma* differentiable_at.add_const
- \+ *lemma* differentiable_on.add_const
- \+ *lemma* differentiable.add_const
- \+ *lemma* fderiv_within_add_const
- \+ *lemma* fderiv_add_const
- \+ *lemma* differentiable_within_at.const_add
- \+ *lemma* differentiable_at.const_add
- \+ *lemma* differentiable_on.const_add
- \+ *lemma* differentiable.const_add
- \+ *lemma* fderiv_within_const_add
- \+ *lemma* fderiv_const_add
- \+ *lemma* differentiable_within_at.sub_const
- \+ *lemma* differentiable_at.sub_const
- \+ *lemma* differentiable_on.sub_const
- \+ *lemma* differentiable.sub_const
- \+ *lemma* fderiv_within_sub_const
- \+ *lemma* fderiv_sub_const
- \+ *lemma* differentiable_within_at.const_sub
- \+ *lemma* differentiable_at.const_sub
- \+ *lemma* differentiable_on.const_sub
- \+ *lemma* differentiable.const_sub
- \+ *lemma* fderiv_within_const_sub
- \+ *lemma* fderiv_const_sub
- \+/\- *lemma* differentiable_within_at.smul
- \+/\- *lemma* differentiable_at.smul
- \+/\- *lemma* differentiable_on.smul
- \+/\- *lemma* differentiable.smul
- \+/\- *lemma* fderiv_within_smul
- \+/\- *lemma* fderiv_smul
- \+ *lemma* differentiable_within_at.smul_const
- \+ *lemma* differentiable_at.smul_const
- \+ *lemma* differentiable_on.smul_const
- \+ *lemma* differentiable.smul_const
- \+ *lemma* fderiv_within_smul_const
- \+ *lemma* fderiv_smul_const
- \+ *lemma* differentiable_within_at.mul_const
- \+ *lemma* differentiable_at.mul_const
- \+ *lemma* differentiable_on.mul_const
- \+ *lemma* differentiable.mul_const
- \+ *lemma* fderiv_within_mul_const
- \+ *lemma* fderiv_mul_const
- \+ *lemma* differentiable_within_at.const_mul
- \+ *lemma* differentiable_at.const_mul
- \+ *lemma* differentiable_on.const_mul
- \+ *lemma* differentiable.const_mul
- \+ *lemma* fderiv_within_const_mul
- \+ *lemma* fderiv_const_mul
- \- *lemma* differentiable_within_at.smul'
- \- *lemma* differentiable_at.smul'
- \- *lemma* differentiable_on.smul'
- \- *lemma* differentiable.smul'
- \- *lemma* fderiv_within_smul'
- \- *lemma* fderiv_smul'
- \+ *theorem* has_fderiv_at_filter.const_smul
- \+ *theorem* has_fderiv_within_at.const_smul
- \+ *theorem* has_fderiv_at.const_smul
- \+ *theorem* has_fderiv_at_filter.add_const
- \+ *theorem* has_fderiv_within_at.add_const
- \+ *theorem* has_fderiv_at.add_const
- \+ *theorem* has_fderiv_at_filter.const_add
- \+ *theorem* has_fderiv_within_at.const_add
- \+ *theorem* has_fderiv_at.const_add
- \+ *theorem* has_fderiv_at_filter.sub_const
- \+ *theorem* has_fderiv_within_at.sub_const
- \+ *theorem* has_fderiv_at.sub_const
- \+ *theorem* has_fderiv_at_filter.const_sub
- \+ *theorem* has_fderiv_within_at.const_sub
- \+ *theorem* has_fderiv_at.const_sub
- \+/\- *theorem* has_fderiv_within_at.smul
- \+/\- *theorem* has_fderiv_at.smul
- \+ *theorem* has_fderiv_within_at.smul_const
- \+ *theorem* has_fderiv_at.smul_const
- \+ *theorem* has_fderiv_within_at.mul_const
- \+ *theorem* has_fderiv_at.mul_const
- \+ *theorem* has_fderiv_within_at.const_mul
- \+ *theorem* has_fderiv_at.const_mul
- \- *theorem* has_fderiv_at_filter.smul
- \- *theorem* has_fderiv_within_at.smul'
- \- *theorem* has_fderiv_at.smul'

Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/complex/exponential.lean
- \+ *lemma* has_deriv_at.cexp
- \+ *lemma* has_deriv_within_at.cexp
- \+ *lemma* has_deriv_at.rexp
- \+ *lemma* has_deriv_within_at.rexp



## [2020-01-02 18:35:24](https://github.com/leanprover-community/mathlib/commit/7b18bbf)
feat(topology/algebra/ordered): add `*_mem_nhds_within_Ioi`, reorder args of `is_closed.Icc_subset_of_forall_exists_gt` ([#1844](https://github.com/leanprover-community/mathlib/pull/1844))
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+ *lemma* mem_nhds_within_Ioi_iff_exists_mem_Ioc_Ioo_subset
- \+ *lemma* Ioo_mem_nhds_within_Ioi
- \+ *lemma* Ioc_mem_nhds_within_Ioi
- \+ *lemma* Ico_mem_nhds_within_Ioi
- \+ *lemma* Icc_mem_nhds_within_Ioi
- \+ *lemma* mem_nhds_within_Iio_iff_exists_mem_Ico_Ioo_subset



## [2020-01-02 10:40:36](https://github.com/leanprover-community/mathlib/commit/033ecbf)
chore(topology/*): add a few more trivial `continuous_(within_)at` lemmas ([#1842](https://github.com/leanprover-community/mathlib/pull/1842))
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *lemma* continuous_at.inv
- \+ *lemma* continuous_within_at.inv

Modified src/topology/algebra/monoid.lean
- \+ *lemma* continuous_at.mul
- \+ *lemma* continuous_within_at.mul

Modified src/topology/basic.lean
- \+ *lemma* continuous_at_const
- \+ *lemma* continuous_at_id

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_within_at_const
- \+ *lemma* continuous_on_id
- \+ *lemma* continuous_within_at_id



## [2020-01-02 09:04:12](https://github.com/leanprover-community/mathlib/commit/ffa9785)
feat(topology/algebra/ordered): prove that `nhds_within (Ioi a) b ≠ ⊥` if `a ≤ b` ([#1841](https://github.com/leanprover-community/mathlib/pull/1841))
+ few similar statements
Also drop decidability assumption in `closure_Ioo` etc. We don't care
about using classical reasoning anyway, and usage of `classical.DLO`
here doesn't lead to any `noncomputable` defs.
#### Estimated changes
Modified src/order/bounds.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* nhds_within_Ioi_ne_bot'
- \+ *lemma* nhds_within_Ioi_ne_bot
- \+ *lemma* nhds_within_Ioi_self_ne_bot'
- \+ *lemma* nhds_within_Ioi_self_ne_bot
- \+ *lemma* nhds_within_Iio_ne_bot'
- \+ *lemma* nhds_within_Iio_ne_bot
- \+ *lemma* nhds_within_Iio_self_ne_bot'
- \+ *lemma* nhds_within_Iio_self_ne_bot



## [2020-01-01 22:13:19](https://github.com/leanprover-community/mathlib/commit/d08d509)
fix(metric_space/gromo_hausdorff): lemma should be instance + linting ([#1840](https://github.com/leanprover-community/mathlib/pull/1840))
#### Estimated changes
Modified src/topology/metric_space/gromov_hausdorff.lean
- \- *lemma* second_countable
- \+/\- *theorem* GH_dist_le_of_approx_subsets

