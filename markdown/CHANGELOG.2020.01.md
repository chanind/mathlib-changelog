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
- \+/\- *def* matrix.diag
- \+ *lemma* matrix.diag_transpose
- \+/\- *def* matrix.trace
- \+ *lemma* matrix.trace_mul_comm
- \+ *lemma* matrix.trace_transpose
- \+ *lemma* matrix.trace_transpose_mul



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
- \+ *lemma* finset.prod_sum_elim

Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex.add
- \+/\- *lemma* convex.affinity
- \+/\- *lemma* convex.center_mass_mem
- \- *lemma* convex.closure
- \+ *lemma* convex.convex_hull_eq
- \+/\- *lemma* convex.inter
- \- *lemma* convex.interior
- \+/\- *lemma* convex.is_linear_image
- \+/\- *lemma* convex.is_linear_preimage
- \+/\- *lemma* convex.linear_image
- \+/\- *lemma* convex.linear_preimage
- \+/\- *lemma* convex.neg
- \+/\- *lemma* convex.neg_preimage
- \+/\- *lemma* convex.prod
- \+ *lemma* convex.segment_subset
- \+/\- *lemma* convex.smul
- \+/\- *lemma* convex.smul_preimage
- \+/\- *lemma* convex.sub
- \+/\- *lemma* convex.sum_mem
- \+/\- *lemma* convex.translate
- \+/\- *def* convex
- \+/\- *lemma* convex_Inter
- \- *lemma* convex_ball
- \- *lemma* convex_closed_ball
- \+ *lemma* convex_convex_hull
- \+/\- *lemma* convex_empty
- \+/\- *lemma* convex_halfspace_ge
- \+/\- *lemma* convex_halfspace_gt
- \+/\- *lemma* convex_halfspace_le
- \+/\- *lemma* convex_halfspace_lt
- \+ *def* convex_hull
- \+ *lemma* convex_hull_basis_eq_std_simplex
- \+ *lemma* convex_hull_eq
- \+ *lemma* convex_hull_min
- \+ *lemma* convex_hull_mono
- \+/\- *lemma* convex_hyperplane
- \- *lemma* convex_iff:
- \+ *lemma* convex_iff_pointwise_add_subset:
- \+ *lemma* convex_iff_segment_subset
- \- *lemma* convex_iff₂:
- \- *lemma* convex_iff₃:
- \+/\- *lemma* convex_on.add
- \+/\- *lemma* convex_on.convex_epigraph
- \+/\- *lemma* convex_on.convex_le
- \+/\- *lemma* convex_on.convex_lt
- \+ *lemma* convex_on.exists_ge_of_center_mass
- \+ *lemma* convex_on.exists_ge_of_mem_convex_hull
- \- *lemma* convex_on.le_on_interval
- \+ *lemma* convex_on.le_on_segment'
- \+ *lemma* convex_on.le_on_segment
- \+/\- *lemma* convex_on.map_center_mass_le
- \+/\- *lemma* convex_on.map_sum_le
- \+/\- *lemma* convex_on.smul
- \+/\- *lemma* convex_on.subset
- \+/\- *def* convex_on
- \- *lemma* convex_on_dist
- \- *lemma* convex_on_iff
- \+/\- *lemma* convex_on_iff_convex_epigraph
- \+/\- *lemma* convex_on_real_of_slope_mono_adjacent
- \+/\- *lemma* convex_real_iff
- \+/\- *lemma* convex_sInter
- \+/\- *lemma* convex_segment
- \- *lemma* convex_segment_iff
- \+/\- *lemma* convex_singleton
- \+ *lemma* convex_std_simplex
- \+/\- *lemma* convex_univ
- \+/\- *lemma* finset.center_mass_empty
- \+ *lemma* finset.center_mass_eq_of_sum_1
- \+ *lemma* finset.center_mass_filter_ne_zero
- \+/\- *lemma* finset.center_mass_insert
- \+ *lemma* finset.center_mass_ite_eq
- \+ *lemma* finset.center_mass_mem_convex_hull
- \+/\- *lemma* finset.center_mass_pair
- \+ *lemma* finset.center_mass_segment'
- \+ *lemma* finset.center_mass_segment
- \+/\- *lemma* finset.center_mass_singleton
- \+ *lemma* finset.center_mass_smul
- \+ *lemma* finset.center_mass_subset
- \+ *lemma* is_linear_map.convex_hull_image
- \+ *lemma* is_linear_map.image_convex_hull
- \+ *lemma* ite_eq_mem_std_simplex
- \+/\- *lemma* left_mem_segment
- \+ *lemma* linear_map.convex_hull_image
- \+ *lemma* linear_map.image_convex_hull
- \+/\- *lemma* linear_order.convex_on_of_lt
- \+ *lemma* mem_Icc_of_mem_std_simplex
- \- *lemma* mem_segment_iff'
- \- *lemma* mem_segment_iff
- \+ *lemma* mem_segment_translate
- \+/\- *lemma* right_mem_segment
- \+/\- *def* segment
- \+/\- *lemma* segment_eq_Icc'
- \+ *lemma* segment_eq_image'
- \+ *lemma* segment_eq_image
- \- *lemma* segment_eq_image_Icc_zero_one'
- \- *lemma* segment_eq_image_Icc_zero_one
- \+ *lemma* segment_eq_image₂
- \+ *lemma* segment_same
- \+/\- *lemma* segment_symm
- \- *lemma* segment_translate
- \+/\- *lemma* segment_translate_image
- \+/\- *lemma* segment_translate_preimage
- \+ *lemma* set.finite.convex_hull_eq
- \+ *lemma* set.finite.convex_hull_eq_image
- \+ *def* std_simplex
- \+ *lemma* std_simplex_eq_inter
- \+/\- *lemma* submodule.convex
- \+ *lemma* subset_convex_hull
- \+/\- *lemma* subspace.convex

Added src/analysis/convex/topology.lean
- \+ *lemma* bounded_convex_hull
- \+ *lemma* bounded_std_simplex
- \+ *lemma* compact_std_simplex
- \+ *lemma* convex.closure
- \+ *lemma* convex.interior
- \+ *lemma* convex_ball
- \+ *lemma* convex_closed_ball
- \+ *lemma* convex_hull_diam
- \+ *lemma* convex_hull_ediam
- \+ *lemma* convex_hull_exists_dist_ge2
- \+ *lemma* convex_hull_exists_dist_ge
- \+ *lemma* convex_on_dist
- \+ *lemma* is_closed_std_simplex
- \+ *lemma* set.finite.compact_convex_hull
- \+ *lemma* set.finite.is_closed_convex_hull
- \+ *lemma* std_simplex_subset_closed_ball

Modified src/analysis/normed_space/finite_dimension.lean
- \+/\- *theorem* linear_map.continuous_of_finite_dimensional
- \+/\- *def* linear_map.to_continuous_linear_map

Modified src/analysis/normed_space/real_inner_product.lean


Modified src/data/finset.lean
- \+ *lemma* finset.filter_mem_eq_inter
- \+ *theorem* finset.union_inter_cancel_left
- \+ *theorem* finset.union_inter_cancel_right

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.div_one
- \+ *lemma* nnreal.div_self

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


Added scripts/deploy_docs.sh




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
Added archive/examples/prop_encodable.lean
- \+ *def* mk_fn0
- \+ *def* mk_fn1
- \+ *def* mk_fn2
- \+ *inductive* prop_form

Added src/data/W.lean
- \+ *def* W.depth
- \+ *lemma* W.depth_lt_depth_mk
- \+ *lemma* W.depth_pos
- \+ *inductive* W

Modified src/data/equiv/encodable.lean
- \+ *def* encodable.encode'

Modified src/data/equiv/list.lean
- \+ *def* encodable.fintype_equiv_fin
- \+ *theorem* encodable.length_sorted_univ
- \+ *theorem* encodable.mem_sorted_univ
- \+ *def* encodable.sorted_univ
- \+ *theorem* encodable.sorted_univ_nodup

Modified src/data/fintype.lean
- \+ *def* fintype.equiv_fin_of_forall_mem_list

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
- \- *lemma* category_theory.comma_morphism.ext
- \+/\- *structure* category_theory.comma_morphism

Modified src/category_theory/limits/cones.lean
- \- *lemma* category_theory.limits.cocone_morphism.ext
- \+/\- *structure* category_theory.limits.cocone_morphism
- \- *lemma* category_theory.limits.cone_morphism.ext
- \+/\- *structure* category_theory.limits.cone_morphism

Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/monad/algebra.lean
- \- *lemma* category_theory.monad.algebra.hom.ext
- \+/\- *structure* category_theory.monad.algebra.hom

Modified src/category_theory/natural_transformation.lean
- \- *lemma* category_theory.nat_trans.ext
- \+/\- *structure* category_theory.nat_trans

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
- \+ *def* continued_fraction.of_integer
- \+ *def* generalized_continued_fraction.of_integer
- \+ *def* simple_continued_fraction.of_integer

Modified src/algebra/direct_sum.lean


Modified src/algebra/free.lean


Modified src/algebra/group/free_monoid.lean
- \- *lemma* free_add_monoid.add_def
- \- *lemma* free_add_monoid.zero_def
- \- *def* free_add_monoid
- \+/\- *lemma* free_monoid.mul_def
- \+/\- *lemma* free_monoid.one_def

Modified src/algebra/group/hom.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/type_tags.lean


Modified src/algebra/group/units.lean


Modified src/algebra/group/with_one.lean


Modified src/algebra/module.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *structure* normed_group.core

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
- \- *def* lazy_list.thunk.mk
- \+ *def* thunk.mk

Modified src/data/list/alist.lean
- \+ *lemma* alist.ext_iff

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
- \+ *def* arity.const
- \+ *lemma* pSet.arity.equiv_const

Modified src/tactic/abel.lean


Modified src/tactic/core.lean


Added src/tactic/derive_inhabited.lean


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
- \+/\- *inductive* tactic.tfae.arrow

Modified src/topology/algebra/module.lean


Modified src/topology/compact_open.lean


Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/opens.lean


Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/compare_reals.lean
- \+/\- *def* compare_reals.Q

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
- \+/\- *theorem* asymptotics.is_O_zero_right_iff

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
- \+/\- *lemma* measure_theory.simple_func.integral_congr

Modified src/measure_theory/measure_space.lean
- \+/\- *def* measure_theory.all_ae

Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually.exists_forall_of_at_top
- \+ *lemma* filter.eventually_Sup
- \+ *lemma* filter.eventually_at_top
- \+ *lemma* filter.eventually_bot
- \+ *lemma* filter.eventually_principal
- \+ *lemma* filter.eventually_sup
- \+ *lemma* filter.eventually_supr
- \+ *lemma* filter.eventually_top
- \+ *lemma* filter.frequently.forall_exists_of_at_top
- \+ *lemma* filter.frequently_Sup
- \+ *lemma* filter.frequently_at_top
- \+ *lemma* filter.frequently_bot
- \+ *lemma* filter.frequently_false
- \+ *lemma* filter.frequently_principal
- \+ *lemma* filter.frequently_sup
- \+ *lemma* filter.frequently_supr
- \+ *lemma* filter.frequently_top
- \+ *lemma* filter.frequently_true_iff_ne_bot
- \+ *lemma* filter.not_eventually
- \+ *lemma* filter.not_frequently
- \+/\- *lemma* filter.tendsto_principal

Modified src/order/filter/extr.lean
- \+/\- *def* is_max_filter
- \+/\- *def* is_min_filter

Modified src/order/filter/filter_product.lean
- \+/\- *theorem* filter.filter_product.of_seq_fun
- \+/\- *theorem* filter.filter_product.of_seq_fun₂

Modified src/order/liminf_limsup.lean
- \+/\- *def* filter.Liminf
- \+/\- *theorem* filter.Liminf_eq_supr_Inf
- \+/\- *def* filter.Limsup
- \+/\- *theorem* filter.Limsup_eq_infi_Sup
- \+/\- *def* filter.is_bounded
- \+/\- *lemma* filter.is_cobounded.mk
- \+/\- *def* filter.is_cobounded
- \+/\- *theorem* filter.liminf_eq
- \+/\- *theorem* filter.liminf_eq_supr_infi
- \+/\- *theorem* filter.limsup_eq
- \+/\- *theorem* filter.limsup_eq_infi_supr

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* ge_mem_nhds
- \+/\- *lemma* gt_mem_nhds
- \+/\- *lemma* le_mem_nhds
- \+/\- *lemma* lt_mem_nhds

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
- \+ *lemma* finset.prod_cancels_of_partition_cancels
- \+ *lemma* finset.prod_ite_eq'
- \+/\- *lemma* finset.prod_ite_eq

Modified src/data/finset.lean
- \+ *lemma* finset.filter_eq'

Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.transpose_one
- \+ *lemma* matrix.transpose_smul
- \+ *lemma* matrix.transpose_val

Modified src/data/matrix/pequiv.lean
- \+ *lemma* pequiv.equiv_to_pequiv_to_matrix
- \+ *lemma* pequiv.to_pequiv_mul_matrix

Modified src/data/pequiv.lean
- \+ *lemma* equiv.to_pequiv_apply

Modified src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.swap_mul_eq_iff
- \+ *lemma* equiv.perm.swap_mul_self_mul

Modified src/linear_algebra/determinant.lean
- \+ *lemma* matrix.det_permutation
- \+ *lemma* matrix.det_permute
- \+ *lemma* matrix.det_transpose
- \+ *theorem* matrix.det_zero_of_column_eq
- \+ *def* matrix.mod_swap

Added src/linear_algebra/nonsingular_inverse.lean
- \+ *def* matrix.adjugate
- \+ *lemma* matrix.adjugate_def
- \+ *lemma* matrix.adjugate_mul
- \+ *lemma* matrix.adjugate_transpose
- \+ *lemma* matrix.adjugate_val
- \+ *def* matrix.cramer
- \+ *lemma* matrix.cramer_apply
- \+ *lemma* matrix.cramer_column_self
- \+ *lemma* matrix.cramer_is_linear
- \+ *def* matrix.cramer_map
- \+ *lemma* matrix.cramer_map_is_linear
- \+ *lemma* matrix.mul_adjugate
- \+ *lemma* matrix.mul_adjugate_val
- \+ *theorem* matrix.mul_nonsing_inv
- \+ *def* matrix.nonsing_inv
- \+ *theorem* matrix.nonsing_inv_mul
- \+ *lemma* matrix.nonsing_inv_val
- \+ *lemma* matrix.sum_cramer
- \+ *lemma* matrix.sum_cramer_apply
- \+ *lemma* matrix.transpose_nonsing_inv
- \+ *def* matrix.update_column
- \+ *lemma* matrix.update_column_ne
- \+ *lemma* matrix.update_column_self
- \+ *lemma* matrix.update_column_transpose
- \+ *lemma* matrix.update_column_val
- \+ *def* matrix.update_row
- \+ *lemma* matrix.update_row_ne
- \+ *lemma* matrix.update_row_self
- \+ *lemma* matrix.update_row_val



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
- \+ *def* matrix.diag
- \+ *lemma* matrix.diag_one
- \+ *def* matrix.trace
- \+ *lemma* matrix.trace_one

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
- \+ *lemma* filter.join_pure
- \+ *lemma* filter.le_pure_iff
- \- *lemma* filter.mem_pure
- \- *lemma* filter.mem_pure_iff
- \+/\- *lemma* filter.mem_pure_sets
- \+ *lemma* filter.pure_bind
- \- *lemma* filter.pure_def
- \+ *lemma* filter.pure_eq_principal
- \+ *lemma* filter.pure_inj
- \+ *lemma* filter.pure_sets
- \+/\- *lemma* filter.tendsto_const_pure
- \+ *lemma* filter.tendsto_pure

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
- \+ *lemma* finset.prod_piecewise
- \+ *lemma* finset.prod_powerset_insert

Modified src/data/finset.lean
- \+ *lemma* finset.empty_sdiff
- \+ *lemma* finset.insert_sdiff_of_mem
- \+ *lemma* finset.insert_sdiff_of_not_mem
- \+/\- *theorem* finset.lt_wf
- \+ *lemma* finset.ne_insert_of_not_mem
- \+ *lemma* finset.not_mem_of_mem_powerset_of_not_mem
- \+ *def* finset.piecewise
- \+ *lemma* finset.piecewise_coe
- \+ *lemma* finset.piecewise_empty
- \+ *lemma* finset.piecewise_eq_of_mem
- \+ *lemma* finset.piecewise_eq_of_not_mem
- \+ *lemma* finset.piecewise_insert
- \+ *lemma* finset.piecewise_insert_of_ne
- \+ *lemma* finset.piecewise_insert_self
- \+ *lemma* finset.powerset_empty
- \+ *lemma* finset.powerset_insert

Modified src/data/fintype.lean
- \+ *lemma* finset.piecewise_univ

Modified src/data/set/basic.lean
- \- *theorem* set.insert_diff
- \+ *theorem* set.insert_diff_of_mem
- \+ *theorem* set.insert_diff_of_not_mem
- \+ *lemma* set.ne_insert_of_not_mem

Modified src/data/set/function.lean
- \+ *lemma* set.piecewise_empty
- \+ *lemma* set.piecewise_eq_of_mem
- \+ *lemma* set.piecewise_eq_of_not_mem
- \+ *lemma* set.piecewise_insert
- \+ *lemma* set.piecewise_insert_of_ne
- \+ *lemma* set.piecewise_insert_self
- \+ *lemma* set.piecewise_univ

Modified src/linear_algebra/multilinear.lean
- \+ *lemma* multilinear_map.map_add_univ
- \+ *lemma* multilinear_map.map_piecewise_add
- \+ *lemma* multilinear_map.map_piecewise_smul
- \+ *lemma* multilinear_map.map_smul_univ
- \+ *lemma* multilinear_map.map_sub

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
- \+/\- *lemma* finset.sum_smul
- \+ *lemma* list.sum_smul
- \+ *lemma* multiset.sum_smul
- \+ *lemma* nat.smul_def
- \- *lemma* smul_smul

Modified src/group_theory/group_action.lean
- \+ *lemma* finset.smul_sum
- \+ *lemma* list.smul_sum
- \+ *lemma* multiset.smul_sum
- \+ *lemma* smul_smul

Modified src/linear_algebra/basic.lean
- \- *lemma* finset.smul_sum'
- \- *lemma* finset.smul_sum

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


Added src/tactic/clear.lean


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
- \+ *theorem* finset.exists_le_of_sum_le
- \+/\- *lemma* finset.exists_ne_one_of_prod_ne_one
- \+ *lemma* finset.nonempty_of_prod_ne_one
- \+/\- *lemma* finset.prod_Ico_id_eq_fact
- \+ *lemma* finset.prod_filter_ne_one
- \+ *theorem* finset.sum_lt_sum

Modified src/algebra/module.lean
- \+ *theorem* finset.exists_card_smul_ge_sum
- \+ *theorem* finset.exists_card_smul_le_sum
- \+/\- *lemma* finset.sum_const'

Modified src/data/finset.lean
- \+/\- *theorem* finset.card_pos
- \+ *lemma* finset.coe_nonempty
- \+ *theorem* finset.eq_empty_or_nonempty
- \- *theorem* finset.exists_mem_iff_ne_empty
- \- *theorem* finset.exists_mem_of_ne_empty
- \+/\- *lemma* finset.exists_min
- \+/\- *lemma* finset.image_const
- \+/\- *def* finset.max'
- \- *theorem* finset.max_of_ne_empty
- \+ *theorem* finset.max_of_nonempty
- \+/\- *def* finset.min'
- \- *theorem* finset.min_of_ne_empty
- \+ *theorem* finset.min_of_nonempty
- \+ *lemma* finset.nonempty.bex
- \+ *lemma* finset.nonempty.image
- \+ *lemma* finset.nonempty.mono
- \+ *theorem* finset.nonempty_iff_ne_empty
- \- *lemma* finset.nonempty_iff_ne_empty
- \+ *theorem* finset.nonempty_of_ne_empty

Modified src/data/finsupp.lean
- \+/\- *def* finsupp.split_support

Modified src/data/fintype.lean
- \+ *theorem* fin.prod_univ_succ
- \+ *theorem* fin.prod_univ_zero
- \+ *theorem* fin.sum_univ_succ
- \+ *lemma* fin.univ_succ

Modified src/data/nat/totient.lean


Modified src/data/set/finite.lean
- \+/\- *lemma* set.exists_min

Modified src/data/set/lattice.lean
- \+ *lemma* set.Inter_subset_Inter2
- \+ *lemma* set.Inter_subset_Inter
- \+ *lemma* set.Inter_subset_of_subset
- \+/\- *theorem* set.Union_subset_iff
- \+/\- *theorem* set.mem_Inter_of_mem
- \+/\- *theorem* set.subset_Inter

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
Added src/data/real/ereal.lean
- \+ *theorem* ereal.le_neg_of_le_neg
- \+ *theorem* ereal.neg_eq_iff_neg_eq
- \+ *theorem* ereal.neg_inj
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
- \+/\- *lemma* nnreal.sub_eq_zero
- \+ *lemma* nnreal.sub_le_self
- \+ *lemma* nnreal.sub_self
- \+ *lemma* nnreal.sub_sub_cancel_of_le
- \+ *lemma* nnreal.sub_zero



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
Added .github/workflows/build.yml


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


Added src/tactic/simp_rw.lean


Added test/simp_rw.lean


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
Added src/order/filter/bases.lean
- \+ *lemma* filter.at_top_basis'
- \+ *lemma* filter.at_top_basis
- \+ *lemma* filter.basis_sets
- \+ *lemma* filter.has_basis.comap
- \+ *lemma* filter.has_basis.eq_binfi
- \+ *lemma* filter.has_basis.eq_infi
- \+ *lemma* filter.has_basis.forall_nonempty_iff_ne_bot
- \+ *theorem* filter.has_basis.ge_iff
- \+ *lemma* filter.has_basis.inf
- \+ *lemma* filter.has_basis.inf_principal
- \+ *theorem* filter.has_basis.le_basis_iff
- \+ *theorem* filter.has_basis.le_iff
- \+ *lemma* filter.has_basis.map
- \+ *lemma* filter.has_basis.mem_iff
- \+ *lemma* filter.has_basis.mem_of_mem
- \+ *lemma* filter.has_basis.mem_of_superset
- \+ *lemma* filter.has_basis.prod
- \+ *lemma* filter.has_basis.prod_self
- \+ *lemma* filter.has_basis.tendsto_iff
- \+ *lemma* filter.has_basis.tendsto_left_iff
- \+ *lemma* filter.has_basis.tendsto_right_iff
- \+ *lemma* filter.has_basis_binfi_principal
- \+ *lemma* filter.has_basis_infi_principal
- \+ *lemma* filter.tendsto.basis_both
- \+ *lemma* filter.tendsto.basis_left
- \+ *lemma* filter.tendsto.basis_right



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
- \+ *lemma* lie_act
- \+/\- *def* lie_algebra.Ad
- \- *def* lie_algebra.bil_lie
- \+ *lemma* lie_algebra.endo_algebra_bracket
- \+ *lemma* lie_algebra.map_lie
- \+ *structure* lie_algebra.morphism
- \- *def* lie_algebra.of_endomorphism_algebra
- \+ *abbreviation* lie_ideal
- \+ *def* lie_ideal_subalgebra
- \+ *lemma* lie_mem_left
- \+ *lemma* lie_mem_right
- \+ *def* lie_module.of_endo_morphism
- \+ *structure* lie_subalgebra
- \+ *lemma* lie_submodule.quotient.is_quotient_mk
- \+ *abbreviation* lie_submodule.quotient.mk
- \+ *lemma* lie_submodule.quotient.mk_bracket
- \+ *abbreviation* lie_submodule.quotient
- \+ *structure* lie_submodule

Added src/linear_algebra/linear_action.lean
- \+ *def* linear_action.of_endo_map
- \+ *def* linear_action.to_endo_map
- \+ *lemma* linear_action_act_add
- \+ *lemma* linear_action_act_smul
- \+ *lemma* linear_action_add_act
- \+ *lemma* linear_action_smul_act
- \+ *lemma* linear_action_zero
- \+ *lemma* zero_linear_action



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
- \+ *theorem* set.infinite_univ
- \+ *theorem* set.infinite_univ_iff
- \- *lemma* set.infinite_univ_nat
- \- *lemma* set.not_injective_int_fintype
- \- *lemma* set.not_injective_nat_fintype

Modified src/group_theory/order_of_element.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.cofinite_ne_bot
- \+/\- *theorem* filter.compl_mem_hyperfilter_of_finite
- \+ *lemma* filter.frequently_cofinite_iff_infinite
- \+/\- *lemma* filter.hyperfilter_le_cofinite
- \+/\- *lemma* filter.is_ultrafilter_hyperfilter
- \+ *lemma* filter.mem_cofinite
- \+/\- *theorem* filter.mem_hyperfilter_of_finite_compl
- \+/\- *theorem* filter.nmem_hyperfilter_of_finite
- \+ *lemma* nat.cofinite_eq_at_top
- \+ *lemma* set.infinite_iff_frequently_cofinite



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
- \+ *lemma* finset.bUnion_insert
- \+ *theorem* finset.bUnion_singleton
- \+ *lemma* finset.bUnion_union
- \+ *theorem* finset.supr_union

Added src/data/indicator_function.lean
- \+ *def* set.indicator
- \+ *lemma* set.indicator_add
- \+ *lemma* set.indicator_compl
- \+ *lemma* set.indicator_congr
- \+ *lemma* set.indicator_empty
- \+ *lemma* set.indicator_finset_bUnion
- \+ *lemma* set.indicator_finset_sum
- \+ *lemma* set.indicator_indicator
- \+ *lemma* set.indicator_le_indicator
- \+ *lemma* set.indicator_le_indicator_of_subset
- \+ *lemma* set.indicator_neg
- \+ *lemma* set.indicator_of_mem
- \+ *lemma* set.indicator_of_not_mem
- \+ *lemma* set.indicator_preimage
- \+ *lemma* set.indicator_smul
- \+ *lemma* set.indicator_sub
- \+ *lemma* set.indicator_union_of_disjoint
- \+ *lemma* set.indicator_union_of_not_mem_inter
- \+ *lemma* set.indicator_univ
- \+ *lemma* set.indicator_zero

Modified src/data/set/basic.lean
- \+ *lemma* set.if_preimage

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* measure_theory.integral_div
- \+ *lemma* measure_theory.integral_finset_sum
- \+ *lemma* measure_theory.integral_le_integral
- \+ *lemma* measure_theory.integral_le_integral_ae
- \- *lemma* measure_theory.integral_le_integral_of_le_ae
- \+ *lemma* measure_theory.integral_mul_left
- \+ *lemma* measure_theory.integral_mul_right
- \+/\- *lemma* measure_theory.integral_neg
- \+/\- *lemma* measure_theory.integral_non_integrable
- \+/\- *lemma* measure_theory.integral_non_measurable
- \+/\- *lemma* measure_theory.integral_nonneg_of_nonneg_ae
- \+/\- *lemma* measure_theory.integral_nonpos_of_nonpos_ae
- \+/\- *lemma* measure_theory.integral_smul
- \+/\- *lemma* measure_theory.integral_undef
- \+/\- *lemma* measure_theory.integral_zero
- \+/\- *lemma* measure_theory.l1.simple_func.of_simple_func_zero
- \+/\- *lemma* measure_theory.norm_integral_le_integral_norm

Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_measurable_Icc
- \+ *lemma* is_measurable_Ici
- \+/\- *lemma* is_measurable_Ico
- \+ *lemma* is_measurable_Iic
- \+ *lemma* is_measurable_Ioc
- \+ *lemma* is_measurable_Ioi

Added src/measure_theory/indicator_function.lean
- \+ *lemma* indicator_congr_ae
- \+ *lemma* indicator_congr_of_set
- \+ *lemma* indicator_le_indicator_ae
- \+ *lemma* indicator_norm_le_norm_self
- \+ *lemma* indicator_union_ae
- \+ *lemma* norm_indicator_eq_indicator_norm
- \+ *lemma* norm_indicator_le_norm_self
- \+ *lemma* norm_indicator_le_of_subset
- \+ *lemma* tendsto_indicator_bUnion_finset
- \+ *lemma* tendsto_indicator_of_antimono
- \+ *lemma* tendsto_indicator_of_monotone

Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* measure_theory.integrable.add
- \+/\- *lemma* measure_theory.integrable.neg
- \+/\- *lemma* measure_theory.integrable.smul
- \+/\- *lemma* measure_theory.integrable.sub
- \+ *lemma* measure_theory.integrable_congr_ae
- \+ *lemma* measure_theory.integrable_finset_sum
- \- *lemma* measure_theory.integrable_iff_of_ae_eq
- \+/\- *lemma* measure_theory.integrable_neg_iff
- \+ *lemma* measure_theory.integrable_of_le
- \+/\- *lemma* measure_theory.integrable_smul_iff
- \+/\- *lemma* measure_theory.integrable_zero
- \+/\- *lemma* measure_theory.l1.of_fun_zero

Added src/measure_theory/set_integral.lean
- \+ *lemma* integrable_on.add
- \+ *lemma* integrable_on.divide
- \+ *lemma* integrable_on.mul_left
- \+ *lemma* integrable_on.mul_right
- \+ *lemma* integrable_on.neg
- \+ *lemma* integrable_on.smul
- \+ *lemma* integrable_on.sub
- \+ *lemma* integrable_on.subset
- \+ *lemma* integrable_on.union
- \+ *def* integrable_on
- \+ *lemma* integrable_on_congr
- \+ *lemma* integrable_on_congr_ae
- \+ *lemma* integrable_on_empty
- \+ *lemma* integrable_on_norm_iff
- \+ *lemma* integrable_on_of_integrable
- \+ *lemma* integral_on_Union
- \+ *lemma* integral_on_add
- \+ *lemma* integral_on_congr
- \+ *lemma* integral_on_congr_of_ae_eq
- \+ *lemma* integral_on_congr_of_set
- \+ *lemma* integral_on_div
- \+ *lemma* integral_on_le_integral_on
- \+ *lemma* integral_on_le_integral_on_ae
- \+ *lemma* integral_on_mul_left
- \+ *lemma* integral_on_mul_right
- \+ *lemma* integral_on_neg
- \+ *lemma* integral_on_smul
- \+ *lemma* integral_on_sub
- \+ *lemma* integral_on_union
- \+ *lemma* integral_on_union_ae
- \+ *lemma* integral_on_zero
- \+ *lemma* is_measurable.inter_preimage
- \+ *lemma* measurable.measurable_on
- \+ *lemma* measurable_on.subset
- \+ *lemma* measurable_on.union
- \+ *def* measurable_on
- \+ *lemma* measurable_on_empty
- \+ *lemma* measurable_on_singleton
- \+ *lemma* measurable_on_univ
- \+ *lemma* tendsto_integral_on_of_antimono
- \+ *lemma* tendsto_integral_on_of_monotone

Modified src/topology/bases.lean
- \+ *lemma* filter.has_countable_basis_at_top_finset_nat



## [2020-01-21 18:58:28](https://github.com/leanprover-community/mathlib/commit/217b5e7)
refactor(algebra/char_zero): use `function.injective` ([#1894](https://github.com/leanprover-community/mathlib/pull/1894))
No need to require `↔` in the definition.
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+/\- *theorem* nat.cast_eq_zero
- \+/\- *theorem* nat.cast_injective
- \+/\- *theorem* nat.cast_ne_zero

Modified src/data/padics/padic_numbers.lean


Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.coe_nat_le_coe_nat
- \+/\- *lemma* ennreal.coe_nat_lt_coe_nat
- \+ *lemma* ennreal.coe_nat_mono

Modified src/data/zsqrtd/basic.lean




## [2020-01-21 09:56:58](https://github.com/leanprover-community/mathlib/commit/f3835fa)
feat(*): assorted simple lemmas, simplify some proofs ([#1895](https://github.com/leanprover-community/mathlib/pull/1895))
* feat(*): assorted simple lemmas, simplify some proofs
* +1 lemma, +1 simplified proof
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.of_real_lt_of_real_iff_of_nonneg

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.of_real_lt_of_real_iff_of_nonneg

Modified src/data/set/basic.lean
- \+ *lemma* set.inter_singleton_nonempty

Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.nonempty_Iio
- \+ *lemma* set.nonempty_Ioi

Modified src/order/basic.lean
- \+ *theorem* directed.mono_comp

Modified src/order/bounded_lattice.lean
- \+ *lemma* with_top.dense_coe

Modified src/order/filter/basic.lean
- \+ *lemma* filter.forall_sets_nonempty_iff_ne_bot

Modified src/topology/basic.lean


Modified src/topology/continuous_on.lean


Modified src/topology/sequences.lean




## [2020-01-18 08:16:09](https://github.com/leanprover-community/mathlib/commit/d32c797)
feat(data/bool): coe_bool_iff ([#1891](https://github.com/leanprover-community/mathlib/pull/1891))
#### Estimated changes
Modified src/data/bool.lean
- \+ *theorem* bool.coe_bool_iff



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
- \+ *lemma* measure_theory.tendsto_integral_filter_of_dominated_convergence
- \+/\- *theorem* measure_theory.tendsto_integral_of_dominated_convergence

Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.tendsto_lintegral_filter_of_dominated_convergence

Modified src/measure_theory/l1_space.lean


Modified src/topology/bases.lean
- \+ *lemma* filter.has_countable_basis.tendsto_iff_seq_tendsto
- \+ *lemma* filter.has_countable_basis.tendsto_of_seq_tendsto



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


Added src/geometry/manifold/mfderiv.lean
- \+ *def* bundle_mfderiv
- \+ *lemma* bundle_mfderiv_chart_inv_fun
- \+ *lemma* bundle_mfderiv_chart_to_fun
- \+ *lemma* bundle_mfderiv_comp
- \+ *lemma* bundle_mfderiv_comp_at
- \+ *lemma* bundle_mfderiv_proj
- \+ *lemma* bundle_mfderiv_tangent_bundle_proj
- \+ *def* bundle_mfderiv_within
- \+ *lemma* bundle_mfderiv_within_comp_at
- \+ *lemma* bundle_mfderiv_within_eq_bundle_mfderiv
- \+ *lemma* bundle_mfderiv_within_proj
- \+ *lemma* bundle_mfderiv_within_subset
- \+ *lemma* bundle_mfderiv_within_tangent_bundle_proj
- \+ *lemma* bundle_mfderiv_within_univ
- \+ *theorem* has_mfderiv_at.comp
- \+ *theorem* has_mfderiv_at.comp_has_mfderiv_within_at
- \+ *lemma* has_mfderiv_at.congr_of_mem_nhds
- \+ *theorem* has_mfderiv_at.continuous_at
- \+ *theorem* has_mfderiv_at.has_mfderiv_within_at
- \+ *lemma* has_mfderiv_at.mdifferentiable_at
- \+ *lemma* has_mfderiv_at.mfderiv
- \+ *def* has_mfderiv_at
- \+ *lemma* has_mfderiv_at_const
- \+ *lemma* has_mfderiv_at_id
- \+ *theorem* has_mfderiv_at_unique
- \+ *theorem* has_mfderiv_within_at.comp
- \+ *lemma* has_mfderiv_within_at.congr_mono
- \+ *lemma* has_mfderiv_within_at.congr_of_mem_nhds_within
- \+ *theorem* has_mfderiv_within_at.continuous_within_at
- \+ *lemma* has_mfderiv_within_at.has_mfderiv_at
- \+ *lemma* has_mfderiv_within_at.mdifferentiable_within_at
- \+ *lemma* has_mfderiv_within_at.mfderiv_within
- \+ *theorem* has_mfderiv_within_at.mono
- \+ *lemma* has_mfderiv_within_at.nhds_within
- \+ *lemma* has_mfderiv_within_at.union
- \+ *def* has_mfderiv_within_at
- \+ *theorem* has_mfderiv_within_at_const
- \+ *theorem* has_mfderiv_within_at_id
- \+ *lemma* has_mfderiv_within_at_inter'
- \+ *lemma* has_mfderiv_within_at_inter
- \+ *lemma* has_mfderiv_within_at_univ
- \+ *lemma* is_open.unique_mdiff_on
- \+ *lemma* is_open.unique_mdiff_within_at
- \+ *lemma* local_homeomorph.mdifferentiable.inv_fun_to_fun_deriv
- \+ *lemma* local_homeomorph.mdifferentiable.mdifferentiable_at_inv_fun
- \+ *lemma* local_homeomorph.mdifferentiable.mdifferentiable_at_to_fun
- \+ *lemma* local_homeomorph.mdifferentiable.range_mfderiv_eq_univ
- \+ *lemma* local_homeomorph.mdifferentiable.symm
- \+ *lemma* local_homeomorph.mdifferentiable.to_fun_inv_fun_deriv
- \+ *lemma* local_homeomorph.mdifferentiable.trans
- \+ *def* local_homeomorph.mdifferentiable
- \+ *lemma* mdifferentiable.comp
- \+ *lemma* mdifferentiable.continuous
- \+ *lemma* mdifferentiable.mdifferentiable_on
- \+ *lemma* mdifferentiable.mfderiv_within
- \+ *def* mdifferentiable
- \+ *lemma* mdifferentiable_at.comp
- \+ *lemma* mdifferentiable_at.congr_of_mem_nhds
- \+ *lemma* mdifferentiable_at.continuous_at
- \+ *lemma* mdifferentiable_at.has_mfderiv_at
- \+ *lemma* mdifferentiable_at.mdifferentiable_within_at
- \+ *lemma* mdifferentiable_at.mfderiv
- \+ *def* mdifferentiable_at
- \+ *lemma* mdifferentiable_at_atlas_inv_fun
- \+ *lemma* mdifferentiable_at_atlas_to_fun
- \+ *lemma* mdifferentiable_at_const
- \+ *lemma* mdifferentiable_at_id
- \+ *theorem* mdifferentiable_at_iff_differentiable_at
- \+ *lemma* mdifferentiable_chart
- \+ *lemma* mdifferentiable_const
- \+ *lemma* mdifferentiable_id
- \+ *theorem* mdifferentiable_iff_differentiable
- \+ *lemma* mdifferentiable_of_mem_atlas
- \+ *lemma* mdifferentiable_on.comp
- \+ *lemma* mdifferentiable_on.congr_mono
- \+ *lemma* mdifferentiable_on.continuous_on
- \+ *lemma* mdifferentiable_on.mono
- \+ *def* mdifferentiable_on
- \+ *lemma* mdifferentiable_on_atlas_inv_fun
- \+ *lemma* mdifferentiable_on_atlas_to_fun
- \+ *lemma* mdifferentiable_on_const
- \+ *lemma* mdifferentiable_on_id
- \+ *theorem* mdifferentiable_on_iff_differentiable_on
- \+ *lemma* mdifferentiable_on_of_locally_mdifferentiable_on
- \+ *lemma* mdifferentiable_on_univ
- \+ *lemma* mdifferentiable_within_at.comp
- \+ *lemma* mdifferentiable_within_at.congr
- \+ *lemma* mdifferentiable_within_at.congr_mono
- \+ *lemma* mdifferentiable_within_at.congr_of_mem_nhds_within
- \+ *lemma* mdifferentiable_within_at.continuous_within_at
- \+ *lemma* mdifferentiable_within_at.has_mfderiv_within_at
- \+ *lemma* mdifferentiable_within_at.mdifferentiable_at
- \+ *lemma* mdifferentiable_within_at.mfderiv_within
- \+ *lemma* mdifferentiable_within_at.mfderiv_within_congr_mono
- \+ *lemma* mdifferentiable_within_at.mono
- \+ *def* mdifferentiable_within_at
- \+ *lemma* mdifferentiable_within_at_congr_of_mem_nhds_within
- \+ *lemma* mdifferentiable_within_at_const
- \+ *lemma* mdifferentiable_within_at_id
- \+ *lemma* mdifferentiable_within_at_iff
- \+ *theorem* mdifferentiable_within_at_iff_differentiable_within_at
- \+ *lemma* mdifferentiable_within_at_inter'
- \+ *lemma* mdifferentiable_within_at_inter
- \+ *lemma* mdifferentiable_within_at_univ
- \+ *def* mfderiv
- \+ *lemma* mfderiv_comp
- \+ *lemma* mfderiv_congr_of_mem_nhds
- \+ *lemma* mfderiv_const
- \+ *theorem* mfderiv_eq_fderiv
- \+ *lemma* mfderiv_id
- \+ *def* mfderiv_within
- \+ *lemma* mfderiv_within_comp
- \+ *lemma* mfderiv_within_congr_of_mem_nhds_within
- \+ *lemma* mfderiv_within_const
- \+ *theorem* mfderiv_within_eq_fderiv_within
- \+ *lemma* mfderiv_within_id
- \+ *lemma* mfderiv_within_inter
- \+ *lemma* mfderiv_within_subset
- \+ *lemma* mfderiv_within_univ
- \+ *lemma* mfderiv_within_zero_of_not_mdifferentiable_within_at
- \+ *lemma* mfderiv_zero_of_not_mdifferentiable_at
- \+ *lemma* model_with_corners_mdifferentiable_on_inv_fun
- \+ *lemma* model_with_corners_mdifferentiable_on_to_fun
- \+ *theorem* unique_mdiff_on.eq
- \+ *lemma* unique_mdiff_on.inter
- \+ *lemma* unique_mdiff_on.smooth_bundle_preimage
- \+ *lemma* unique_mdiff_on.tangent_bundle_proj_preimage
- \+ *lemma* unique_mdiff_on.unique_diff_on
- \+ *lemma* unique_mdiff_on.unique_diff_on_inter_preimage
- \+ *lemma* unique_mdiff_on.unique_mdiff_on_preimage
- \+ *def* unique_mdiff_on
- \+ *lemma* unique_mdiff_on_iff_unique_diff_on
- \+ *theorem* unique_mdiff_within_at.eq
- \+ *lemma* unique_mdiff_within_at.inter'
- \+ *lemma* unique_mdiff_within_at.inter
- \+ *lemma* unique_mdiff_within_at.mono
- \+ *def* unique_mdiff_within_at
- \+ *lemma* unique_mdiff_within_at_iff
- \+ *lemma* unique_mdiff_within_at_iff_unique_diff_within_at
- \+ *lemma* unique_mdiff_within_at_univ
- \+ *def* written_in_ext_chart_at
- \+ *lemma* written_in_ext_chart_comp
- \+ *lemma* written_in_ext_chart_model_space

Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *def* ext_chart_at
- \+ *lemma* ext_chart_at_continuous_at_to_fun
- \+ *lemma* ext_chart_at_continuous_on_inv_fun
- \+ *lemma* ext_chart_at_continuous_on_to_fun
- \+ *lemma* ext_chart_at_open_source
- \+ *lemma* ext_chart_at_source
- \+ *lemma* ext_chart_at_source_mem_nhds
- \+ *lemma* ext_chart_at_target_mem_nhds_within
- \+ *lemma* ext_chart_at_to_inv
- \+ *lemma* ext_chart_continuous_at_inv_fun'
- \+ *lemma* ext_chart_continuous_at_inv_fun
- \+ *lemma* ext_chart_model_space_eq_id
- \+ *lemma* ext_chart_preimage_inter_eq
- \+ *lemma* ext_chart_preimage_mem_nhds
- \+ *lemma* ext_chart_preimage_mem_nhds_within'
- \+ *lemma* ext_chart_preimage_mem_nhds_within
- \+ *lemma* mem_ext_chart_source
- \+ *lemma* nhds_within_ext_chart_target_eq

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
- \+/\- *lemma* filter.lift'_cong
- \+/\- *lemma* filter.lift'_mono'
- \+/\- *lemma* filter.lift_mono'
- \- *lemma* filter.lift_sets_eq
- \+/\- *lemma* filter.mem_lift'
- \+/\- *lemma* filter.mem_lift'_sets
- \+/\- *lemma* filter.mem_lift
- \- *lemma* filter.mem_lift_iff
- \+/\- *lemma* filter.principal_le_lift'

Modified src/order/filter/pointwise.lean


Modified src/topology/algebra/ordered.lean




## [2020-01-16 08:11:17](https://github.com/leanprover-community/mathlib/commit/05457fd)
feat(analysis/calculus/tangent_cone): define and use `tangent_cone_congr` ([#1886](https://github.com/leanprover-community/mathlib/pull/1886))
* feat(analysis/calculus/tangent_cone): define and use `tangent_cone_congr`
This way some proofs become shorter and hopefully more readable.
* Add a docstring
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean
- \+ *lemma* tangent_cone_congr
- \+ *lemma* tangent_cone_mono_nhds
- \+ *lemma* unique_diff_within_at.mono_nhds
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
- \+ *theorem* lattice.ne_bot_of_le_ne_bot
- \- *theorem* lattice.neq_bot_of_le_neq_bot

Modified src/order/filter/basic.lean
- \+ *lemma* filter.comap_ne_bot
- \+ *lemma* filter.comap_ne_bot_of_surj
- \- *lemma* filter.comap_neq_bot
- \- *lemma* filter.comap_neq_bot_of_surj
- \+ *lemma* filter.forall_sets_ne_empty_iff_ne_bot
- \- *lemma* filter.forall_sets_neq_empty_iff_neq_bot
- \+ *lemma* filter.infi_ne_bot_iff_of_directed'
- \+ *lemma* filter.infi_ne_bot_iff_of_directed
- \+ *lemma* filter.infi_ne_bot_of_directed'
- \+ *lemma* filter.infi_ne_bot_of_directed
- \- *lemma* filter.infi_neq_bot_iff_of_directed
- \- *lemma* filter.infi_neq_bot_of_directed
- \+ *lemma* filter.mem_sets_of_eq_bot
- \- *lemma* filter.mem_sets_of_neq_bot
- \+ *lemma* filter.prod_ne_bot
- \- *lemma* filter.prod_neq_bot
- \+ *lemma* filter.pure_ne_bot
- \- *lemma* filter.pure_neq_bot

Modified src/order/filter/lift.lean
- \+ *lemma* filter.lift'_ne_bot_iff
- \- *lemma* filter.lift'_neq_bot_iff
- \+ *lemma* filter.lift_ne_bot_iff
- \- *lemma* filter.lift_neq_bot_iff

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
- \+ *lemma* dense_inducing.comap_nhds_ne_bot
- \- *lemma* dense_inducing.comap_nhds_neq_bot

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
- \+ *lemma* lattice.directed_of_antimono
- \+ *lemma* lattice.directed_of_mono

Modified src/topology/bases.lean


Modified src/topology/sequences.lean




## [2020-01-14 16:00:47](https://github.com/leanprover-community/mathlib/commit/9f7ae9a)
chore(data/set/lattice): use `∃ x ∈ s` instead of `∃ x, x ∈ s ∧` in `mem_bUnion_iff` ([#1877](https://github.com/leanprover-community/mathlib/pull/1877))
This seems to be more in line with the rest of the library
#### Estimated changes
Modified src/data/semiquot.lean
- \+/\- *def* semiquot.get

Modified src/data/set/lattice.lean


Modified src/group_theory/subgroup.lean
- \+/\- *lemma* group.mem_conjugates_of_set_iff

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


Added src/analysis/ODE/gronwall.lean
- \+ *theorem* ODE_solution_unique
- \+ *theorem* ODE_solution_unique_of_mem_set
- \+ *theorem* dist_le_of_approx_trajectories_ODE
- \+ *theorem* dist_le_of_approx_trajectories_ODE_of_mem_set
- \+ *theorem* dist_le_of_trajectories_ODE
- \+ *theorem* dist_le_of_trajectories_ODE_of_mem_set
- \+ *lemma* gronwall_bound_K0
- \+ *lemma* gronwall_bound_continuous_ε
- \+ *lemma* gronwall_bound_of_K_ne_0
- \+ *lemma* gronwall_bound_x0
- \+ *lemma* gronwall_bound_ε0
- \+ *lemma* gronwall_bound_ε0_δ0
- \+ *lemma* has_deriv_at_gronwall_bound
- \+ *lemma* has_deriv_at_gronwall_bound_shift
- \+ *theorem* le_gronwall_bound_of_liminf_deriv_right_le
- \+ *theorem* norm_le_gronwall_bound_of_norm_deriv_right_le

Modified src/analysis/calculus/mean_value.lean
- \+ *lemma* image_le_of_liminf_slope_right_lt_deriv_boundary'



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
- \+/\- *lemma* measure_theory.simple_func.approx_apply
- \+/\- *lemma* measure_theory.simple_func.approx_comp
- \+/\- *lemma* measure_theory.simple_func.supr_approx_apply

Modified src/tactic/lint.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* Inf_mem_closure
- \+/\- *lemma* Inf_mem_of_is_closed
- \+/\- *lemma* Sup_mem_closure
- \+/\- *lemma* Sup_mem_of_is_closed
- \+/\- *lemma* cInf_mem_closure
- \+/\- *lemma* cInf_mem_of_is_closed
- \+/\- *lemma* cSup_mem_closure
- \+/\- *lemma* cSup_mem_of_is_closed
- \+ *lemma* decidable_linear_ordered_comm_group.tendsto_nhds
- \+ *theorem* induced_order_topology'
- \+ *theorem* induced_order_topology
- \- *theorem* induced_orderable_topology'
- \- *theorem* induced_orderable_topology
- \+/\- *lemma* infi_eq_of_tendsto
- \+ *lemma* nhds_bot_order
- \- *lemma* nhds_bot_orderable
- \+ *lemma* nhds_eq_order
- \- *lemma* nhds_eq_orderable
- \+ *lemma* nhds_order_unbounded
- \- *lemma* nhds_orderable_unbounded
- \+ *lemma* nhds_top_order
- \- *lemma* nhds_top_orderable
- \+ *lemma* order_topology.t2_space
- \+ *lemma* order_topology_of_nhds_abs
- \- *lemma* orderable_topology.t2_space
- \- *lemma* orderable_topology_of_nhds_abs
- \+ *def* preorder.topology
- \+/\- *lemma* supr_eq_of_tendsto
- \+/\- *lemma* tendsto_at_top_infi_nat
- \+/\- *lemma* tendsto_at_top_supr_nat
- \+ *lemma* tendsto_order
- \+ *lemma* tendsto_order_unbounded
- \- *lemma* tendsto_orderable
- \- *lemma* tendsto_orderable_unbounded

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
- \+/\- *def* measure_theory.ae_eq_fun.comp_edist
- \+/\- *lemma* measure_theory.ae_eq_fun.smul_mk

Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* measure_theory.integral_add
- \+/\- *lemma* measure_theory.integral_eq
- \- *lemma* measure_theory.integral_eq_zero_of_non_integrable
- \- *lemma* measure_theory.integral_eq_zero_of_non_measurable
- \+ *lemma* measure_theory.integral_non_integrable
- \+ *lemma* measure_theory.integral_non_measurable
- \+/\- *lemma* measure_theory.integral_smul
- \+/\- *lemma* measure_theory.integral_sub
- \+ *lemma* measure_theory.integral_undef
- \+/\- *def* measure_theory.l1.simple_func

Modified src/measure_theory/borel_space.lean
- \+ *lemma* measurable.coe_nnnorm
- \+ *lemma* measurable.dist
- \+ *lemma* measurable.edist
- \+ *lemma* measurable.nndist
- \+ *lemma* measurable.nnnorm
- \+ *lemma* measurable.norm
- \+ *lemma* measurable.smul'
- \+ *lemma* measurable.smul
- \+ *lemma* measurable_dist
- \+ *lemma* measurable_edist
- \+ *lemma* measurable_nndist
- \+ *lemma* measurable_nnnorm
- \+ *lemma* measurable_norm
- \+ *lemma* measurable_smul_iff
- \- *lemma* measure_theory.measurable_coe_nnnorm
- \- *lemma* measure_theory.measurable_dist'
- \- *lemma* measure_theory.measurable_dist
- \- *lemma* measure_theory.measurable_edist'
- \- *lemma* measure_theory.measurable_edist
- \- *lemma* measure_theory.measurable_nndist'
- \- *lemma* measure_theory.measurable_nndist
- \- *lemma* measure_theory.measurable_nnnorm'
- \- *lemma* measure_theory.measurable_nnnorm
- \- *lemma* measure_theory.measurable_norm'
- \- *lemma* measure_theory.measurable_norm
- \- *lemma* measure_theory.measurable_smul'
- \- *lemma* measure_theory.measurable_smul
- \- *lemma* measure_theory.measurable_smul_iff

Modified src/measure_theory/l1_space.lean
- \- *lemma* measure_theory.integrable.smul_iff
- \+ *lemma* measure_theory.integrable_smul_iff
- \+/\- *def* measure_theory.l1

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_zero

Modified src/measure_theory/simple_func_dense.lean




## [2020-01-11 00:42:53](https://github.com/leanprover-community/mathlib/commit/f67df78)
chore(algebra/module): add some missing `*_cast` tags ([#1863](https://github.com/leanprover-community/mathlib/pull/1863))
#### Estimated changes
Modified src/algebra/module.lean
- \+/\- *lemma* submodule.coe_add
- \+/\- *lemma* submodule.coe_neg
- \+/\- *lemma* submodule.coe_smul
- \+/\- *lemma* submodule.coe_sub
- \+/\- *lemma* submodule.coe_zero



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
Added docs/commands.md


Deleted docs/extras/casts.md


Deleted docs/extras/cc.md


Modified docs/extras/conv.md


Modified docs/extras/simp.md


Modified docs/extras/tactic_writing.md


Modified docs/extras/well_founded_recursion.md


Modified docs/holes.md


Modified docs/mathlib-overview.md


Modified docs/tactics.md


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
- \+ *theorem* set.eq_or_ssubset_of_subset
- \+ *theorem* set.nonempty_diff
- \+/\- *theorem* set.not_subset
- \+/\- *theorem* set.ssubset_def
- \+ *lemma* set.ssubset_iff_subset_ne
- \- *lemma* set.ssubset_iff_subset_not_subset
- \+/\- *def* set.strict_subset

Modified src/data/set/finite.lean


Modified src/data/set/lattice.lean


Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.exists_of_lt
- \+/\- *lemma* submodule.le_def'
- \+/\- *lemma* submodule.le_def
- \+ *lemma* submodule.lt_def
- \+ *lemma* submodule.lt_iff_le_and_exists
- \+ *lemma* submodule.not_le_iff_exists
- \+/\- *def* submodule.of_le
- \+/\- *theorem* submodule.of_le_apply

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
- \+ *lemma* fin.cast_succ_ne_last
- \+/\- *def* fin.cons
- \+ *lemma* fin.cons_self_tail
- \+/\- *lemma* fin.cons_succ
- \+ *lemma* fin.cons_update
- \+/\- *lemma* fin.cons_zero
- \+ *lemma* fin.injective_cast_succ
- \+ *lemma* fin.injective_succ
- \+ *lemma* fin.succ_inj
- \+/\- *def* fin.tail
- \+/\- *lemma* fin.tail_cons
- \+ *lemma* fin.tail_update_succ
- \+ *lemma* fin.tail_update_zero
- \+ *lemma* fin.update_cons_zero
- \+ *def* fin_zero_elim'
- \- *def* {u}

Added src/linear_algebra/multilinear.lean
- \+ *lemma* multilinear_map.add_apply
- \+ *lemma* multilinear_map.cons_add
- \+ *lemma* multilinear_map.cons_smul
- \+ *theorem* multilinear_map.ext
- \+ *def* multilinear_map.linear_to_multilinear_equiv_multilinear
- \+ *lemma* multilinear_map.map_add
- \+ *lemma* multilinear_map.map_coord_zero
- \+ *lemma* multilinear_map.map_smul
- \+ *lemma* multilinear_map.map_zero
- \+ *def* multilinear_map.multilinear_to_linear_equiv_multilinear
- \+ *lemma* multilinear_map.neg_apply
- \+ *lemma* multilinear_map.smul_apply
- \+ *def* multilinear_map.to_linear_map
- \+ *lemma* multilinear_map.zero_apply
- \+ *structure* multilinear_map

Modified src/logic/function.lean
- \+ *lemma* function.update_comp
- \+ *lemma* function.update_eq_self
- \+/\- *lemma* function.update_noteq
- \+/\- *lemma* function.update_same

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
- \+ *lemma* has_deriv_within_at.liminf_right_norm_slope_le
- \+ *lemma* has_deriv_within_at.liminf_right_slope_le
- \+ *lemma* has_deriv_within_at.liminf_right_slope_norm_le
- \+ *lemma* has_deriv_within_at.limsup_norm_slope_le
- \+ *lemma* has_deriv_within_at.limsup_slope_le'
- \+ *lemma* has_deriv_within_at.limsup_slope_le
- \+ *lemma* has_deriv_within_at.limsup_slope_norm_le
- \+ *lemma* has_deriv_within_at_iff_tendsto_slope'

Modified src/analysis/calculus/mean_value.lean
- \+ *lemma* image_le_of_deriv_right_le_deriv_boundary
- \+ *lemma* image_le_of_deriv_right_lt_deriv_boundary'
- \+ *lemma* image_le_of_deriv_right_lt_deriv_boundary
- \+ *lemma* image_le_of_liminf_slope_right_le_deriv_boundary
- \+ *lemma* image_le_of_liminf_slope_right_lt_deriv_boundary
- \+ *lemma* image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary
- \+ *lemma* image_norm_le_of_norm_deriv_right_le_deriv_boundary'
- \+ *lemma* image_norm_le_of_norm_deriv_right_le_deriv_boundary
- \+ *lemma* image_norm_le_of_norm_deriv_right_lt_deriv_boundary'
- \+ *lemma* image_norm_le_of_norm_deriv_right_lt_deriv_boundary
- \+ *theorem* norm_image_sub_le_of_norm_deriv_le_segment'
- \+/\- *theorem* norm_image_sub_le_of_norm_deriv_le_segment
- \+ *theorem* norm_image_sub_le_of_norm_deriv_le_segment_01'
- \+ *theorem* norm_image_sub_le_of_norm_deriv_le_segment_01
- \+ *theorem* norm_image_sub_le_of_norm_deriv_right_le_segment

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* filter.tendsto.nnnorm
- \+ *lemma* filter.tendsto.norm

Modified src/topology/algebra/ordered.lean
- \+ *lemma* Icc_mem_nhds_within_Iio
- \+ *lemma* Ico_mem_nhds_within_Iio
- \+ *lemma* Ioc_mem_nhds_within_Iio
- \+ *lemma* Ioo_mem_nhds_within_Iio



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
- \+/\- *theorem* asymptotics.is_O.add
- \+ *theorem* asymptotics.is_O.add_is_o
- \- *theorem* asymptotics.is_O.comp
- \+ *theorem* asymptotics.is_O.comp_tendsto
- \+ *theorem* asymptotics.is_O.congr'
- \+/\- *theorem* asymptotics.is_O.congr
- \+/\- *theorem* asymptotics.is_O.congr_left
- \+/\- *theorem* asymptotics.is_O.congr_of_sub
- \+/\- *theorem* asymptotics.is_O.congr_right
- \+ *theorem* asymptotics.is_O.const_mul_left
- \+ *theorem* asymptotics.is_O.const_mul_right'
- \+ *theorem* asymptotics.is_O.const_mul_right
- \+ *theorem* asymptotics.is_O.exists_nonneg
- \+ *theorem* asymptotics.is_O.exists_pos
- \+ *theorem* asymptotics.is_O.join
- \+/\- *theorem* asymptotics.is_O.mono
- \+ *theorem* asymptotics.is_O.mul
- \+ *theorem* asymptotics.is_O.mul_is_o
- \+ *theorem* asymptotics.is_O.of_const_mul_right
- \+ *lemma* asymptotics.is_O.prod_left
- \+ *lemma* asymptotics.is_O.prod_left_fst
- \+ *lemma* asymptotics.is_O.prod_left_snd
- \+/\- *lemma* asymptotics.is_O.prod_rightl
- \+/\- *lemma* asymptotics.is_O.prod_rightr
- \+ *theorem* asymptotics.is_O.smul
- \+ *theorem* asymptotics.is_O.smul_is_o
- \+/\- *theorem* asymptotics.is_O.sub
- \+/\- *theorem* asymptotics.is_O.symm
- \+/\- *theorem* asymptotics.is_O.trans
- \+/\- *theorem* asymptotics.is_O.trans_is_o
- \+ *theorem* asymptotics.is_O.trans_le
- \+/\- *theorem* asymptotics.is_O.trans_tendsto
- \+ *theorem* asymptotics.is_O.trans_tendsto_nhds
- \- *theorem* asymptotics.is_O.tri
- \+ *theorem* asymptotics.is_O.triangle
- \+/\- *def* asymptotics.is_O
- \+ *theorem* asymptotics.is_O_bot
- \+/\- *theorem* asymptotics.is_O_comm
- \+/\- *theorem* asymptotics.is_O_congr
- \- *theorem* asymptotics.is_O_congr_left
- \- *theorem* asymptotics.is_O_congr_right
- \+ *theorem* asymptotics.is_O_const_const
- \- *theorem* asymptotics.is_O_const_mul_left
- \+ *theorem* asymptotics.is_O_const_mul_left_iff'
- \+/\- *theorem* asymptotics.is_O_const_mul_left_iff
- \+ *theorem* asymptotics.is_O_const_mul_right_iff'
- \+/\- *theorem* asymptotics.is_O_const_mul_right_iff
- \+ *theorem* asymptotics.is_O_const_mul_self
- \+ *theorem* asymptotics.is_O_const_of_tendsto
- \+/\- *theorem* asymptotics.is_O_const_one
- \- *theorem* asymptotics.is_O_const_smul_left
- \+/\- *theorem* asymptotics.is_O_const_smul_left_iff
- \+/\- *theorem* asymptotics.is_O_const_smul_right
- \+ *lemma* asymptotics.is_O_fst_prod
- \- *theorem* asymptotics.is_O_iff
- \- *theorem* asymptotics.is_O_join
- \- *theorem* asymptotics.is_O_mul
- \+/\- *theorem* asymptotics.is_O_neg_left
- \+/\- *theorem* asymptotics.is_O_neg_right
- \+/\- *theorem* asymptotics.is_O_norm_left
- \+ *theorem* asymptotics.is_O_norm_norm
- \+/\- *theorem* asymptotics.is_O_norm_right
- \- *theorem* asymptotics.is_O_of_is_O_const_mul_right
- \+ *theorem* asymptotics.is_O_of_le'
- \+ *theorem* asymptotics.is_O_of_le
- \+/\- *theorem* asymptotics.is_O_one_of_tendsto
- \+ *lemma* asymptotics.is_O_prod_left
- \- *theorem* asymptotics.is_O_prod_left
- \+/\- *theorem* asymptotics.is_O_refl
- \+/\- *theorem* asymptotics.is_O_refl_left
- \+ *theorem* asymptotics.is_O_self_const_mul'
- \+ *theorem* asymptotics.is_O_self_const_mul
- \- *theorem* asymptotics.is_O_smul
- \+ *lemma* asymptotics.is_O_snd_prod
- \+ *theorem* asymptotics.is_O_with.add
- \+ *theorem* asymptotics.is_O_with.add_is_o
- \+ *theorem* asymptotics.is_O_with.comp_tendsto
- \+ *theorem* asymptotics.is_O_with.congr'
- \+ *theorem* asymptotics.is_O_with.congr
- \+ *theorem* asymptotics.is_O_with.congr_const
- \+ *theorem* asymptotics.is_O_with.congr_left
- \+ *theorem* asymptotics.is_O_with.congr_right
- \+ *theorem* asymptotics.is_O_with.const_mul_left
- \+ *theorem* asymptotics.is_O_with.const_mul_right'
- \+ *theorem* asymptotics.is_O_with.const_mul_right
- \+ *theorem* asymptotics.is_O_with.const_smul_left
- \+ *theorem* asymptotics.is_O_with.exists_nonneg
- \+ *theorem* asymptotics.is_O_with.exists_pos
- \+ *theorem* asymptotics.is_O_with.is_O
- \+ *theorem* asymptotics.is_O_with.join'
- \+ *theorem* asymptotics.is_O_with.join
- \+ *theorem* asymptotics.is_O_with.mono
- \+ *theorem* asymptotics.is_O_with.mul
- \+ *theorem* asymptotics.is_O_with.of_const_mul_right
- \+ *lemma* asymptotics.is_O_with.prod_left
- \+ *lemma* asymptotics.is_O_with.prod_left_fst
- \+ *lemma* asymptotics.is_O_with.prod_left_same
- \+ *lemma* asymptotics.is_O_with.prod_left_snd
- \+ *lemma* asymptotics.is_O_with.prod_rightl
- \+ *lemma* asymptotics.is_O_with.prod_rightr
- \+ *theorem* asymptotics.is_O_with.right_le_add_of_lt_1
- \+ *theorem* asymptotics.is_O_with.right_le_sub_of_lt_1
- \+ *theorem* asymptotics.is_O_with.smul
- \+ *theorem* asymptotics.is_O_with.sub
- \+ *theorem* asymptotics.is_O_with.sub_is_o
- \+ *theorem* asymptotics.is_O_with.symm
- \+ *theorem* asymptotics.is_O_with.trans
- \+ *theorem* asymptotics.is_O_with.trans_is_o
- \+ *theorem* asymptotics.is_O_with.trans_le
- \+ *theorem* asymptotics.is_O_with.triangle
- \+ *theorem* asymptotics.is_O_with.weaken
- \+ *def* asymptotics.is_O_with
- \+ *theorem* asymptotics.is_O_with_bot
- \+ *theorem* asymptotics.is_O_with_comm
- \+ *theorem* asymptotics.is_O_with_congr
- \+ *theorem* asymptotics.is_O_with_const_const
- \+ *theorem* asymptotics.is_O_with_const_mul_self
- \+ *theorem* asymptotics.is_O_with_const_one
- \+ *lemma* asymptotics.is_O_with_fst_prod
- \+ *theorem* asymptotics.is_O_with_neg_left
- \+ *theorem* asymptotics.is_O_with_neg_right
- \+ *theorem* asymptotics.is_O_with_norm_left
- \+ *theorem* asymptotics.is_O_with_norm_norm
- \+ *theorem* asymptotics.is_O_with_norm_right
- \+ *theorem* asymptotics.is_O_with_of_le'
- \+ *theorem* asymptotics.is_O_with_of_le
- \+ *lemma* asymptotics.is_O_with_prod_left
- \+ *theorem* asymptotics.is_O_with_refl
- \+ *theorem* asymptotics.is_O_with_self_const_mul'
- \+ *theorem* asymptotics.is_O_with_self_const_mul
- \+ *lemma* asymptotics.is_O_with_snd_prod
- \+ *theorem* asymptotics.is_O_with_zero
- \+ *theorem* asymptotics.is_O_with_zero_right_iff
- \+/\- *theorem* asymptotics.is_O_zero
- \+/\- *theorem* asymptotics.is_O_zero_right_iff
- \+/\- *theorem* asymptotics.is_o.add
- \+ *theorem* asymptotics.is_o.add_is_O
- \+ *theorem* asymptotics.is_o.add_is_O_with
- \- *theorem* asymptotics.is_o.comp
- \+ *theorem* asymptotics.is_o.comp_tendsto
- \+ *theorem* asymptotics.is_o.congr'
- \+/\- *theorem* asymptotics.is_o.congr
- \+/\- *theorem* asymptotics.is_o.congr_left
- \+/\- *theorem* asymptotics.is_o.congr_of_sub
- \+/\- *theorem* asymptotics.is_o.congr_right
- \+ *theorem* asymptotics.is_o.const_mul_left
- \+ *theorem* asymptotics.is_o.const_mul_right'
- \+ *theorem* asymptotics.is_o.const_mul_right
- \+ *theorem* asymptotics.is_o.is_O
- \+ *theorem* asymptotics.is_o.is_O_with
- \+ *theorem* asymptotics.is_o.join
- \+/\- *theorem* asymptotics.is_o.mono
- \+ *theorem* asymptotics.is_o.mul
- \+ *theorem* asymptotics.is_o.mul_is_O
- \+ *theorem* asymptotics.is_o.of_const_mul_right
- \+ *lemma* asymptotics.is_o.prod_left
- \+ *lemma* asymptotics.is_o.prod_left_fst
- \+ *lemma* asymptotics.is_o.prod_left_snd
- \+/\- *lemma* asymptotics.is_o.prod_rightl
- \+/\- *lemma* asymptotics.is_o.prod_rightr
- \+ *theorem* asymptotics.is_o.smul
- \+ *theorem* asymptotics.is_o.smul_is_O
- \+/\- *theorem* asymptotics.is_o.sub
- \+/\- *theorem* asymptotics.is_o.symm
- \+ *theorem* asymptotics.is_o.tendsto_0
- \- *theorem* asymptotics.is_o.to_is_O
- \+ *theorem* asymptotics.is_o.trans'
- \+/\- *theorem* asymptotics.is_o.trans
- \+/\- *theorem* asymptotics.is_o.trans_is_O
- \+ *theorem* asymptotics.is_o.trans_is_O_with
- \+/\- *theorem* asymptotics.is_o.trans_tendsto
- \- *theorem* asymptotics.is_o.tri
- \+ *theorem* asymptotics.is_o.triangle
- \+/\- *def* asymptotics.is_o
- \+ *theorem* asymptotics.is_o_bot
- \+/\- *theorem* asymptotics.is_o_comm
- \+/\- *theorem* asymptotics.is_o_congr
- \- *theorem* asymptotics.is_o_congr_left
- \- *theorem* asymptotics.is_o_congr_right
- \+ *theorem* asymptotics.is_o_const_iff
- \+ *theorem* asymptotics.is_o_const_iff_is_o_one
- \- *theorem* asymptotics.is_o_const_mul_left
- \+ *theorem* asymptotics.is_o_const_mul_left_iff'
- \+/\- *theorem* asymptotics.is_o_const_mul_left_iff
- \- *theorem* asymptotics.is_o_const_mul_right
- \+ *theorem* asymptotics.is_o_const_mul_right_iff'
- \+ *theorem* asymptotics.is_o_const_mul_right_iff
- \+/\- *theorem* asymptotics.is_o_const_smul_left
- \+/\- *theorem* asymptotics.is_o_const_smul_left_iff
- \+/\- *theorem* asymptotics.is_o_const_smul_right
- \- *theorem* asymptotics.is_o_join
- \- *theorem* asymptotics.is_o_mul
- \- *theorem* asymptotics.is_o_mul_left
- \- *theorem* asymptotics.is_o_mul_right
- \+/\- *theorem* asymptotics.is_o_neg_left
- \+/\- *theorem* asymptotics.is_o_neg_right
- \+/\- *theorem* asymptotics.is_o_norm_left
- \+ *theorem* asymptotics.is_o_norm_norm
- \+/\- *theorem* asymptotics.is_o_norm_right
- \- *theorem* asymptotics.is_o_of_is_o_const_mul_right
- \+/\- *theorem* asymptotics.is_o_one_iff
- \+ *lemma* asymptotics.is_o_prod_left
- \- *theorem* asymptotics.is_o_prod_left
- \+/\- *theorem* asymptotics.is_o_refl_left
- \- *theorem* asymptotics.is_o_smul
- \+/\- *theorem* asymptotics.is_o_zero
- \+/\- *theorem* asymptotics.is_o_zero_right_iff
- \- *theorem* asymptotics.tendsto_nhds_zero_of_is_o

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
- \- *theorem* zorn.chain.directed
- \+/\- *def* zorn.succ_chain
- \+/\- *def* zorn.super_chain



## [2020-01-06 23:48:35](https://github.com/leanprover-community/mathlib/commit/a1b7312)
feat(topology/maps): a few lemmas about `is_open_map` ([#1855](https://github.com/leanprover-community/mathlib/pull/1855))
* feat(topology/maps): a few lemmas about `is_open_map`
Also fix arguments order in all `*.comp` in this file.
* Use restricted version of `continuous_of_left_inverse` to prove non-restricted
* Fix compile by reverting a name change
#### Estimated changes
Modified src/topology/constructions.lean
- \+ *lemma* is_closed.closed_embedding_subtype_val
- \+ *lemma* is_open.is_open_map_subtype_val
- \+ *lemma* is_open.open_embedding_subtype_val
- \+ *lemma* is_open_map.restrict
- \- *lemma* subtype_val.closed_embedding
- \- *lemma* subtype_val.open_embedding

Modified src/topology/continuous_on.lean
- \+ *theorem* is_open_map.continuous_on_image_of_left_inv_on
- \+ *theorem* is_open_map.continuous_on_range_of_left_inverse

Modified src/topology/maps.lean
- \+/\- *lemma* closed_embedding.comp
- \+/\- *lemma* embedding.comp
- \- *lemma* inducing.comp
- \+ *lemma* is_open_map.is_open_range
- \+ *lemma* is_open_map.nhds_le
- \+/\- *lemma* is_open_map_iff_nhds_le
- \+/\- *lemma* open_embedding.comp
- \+/\- *def* quotient_map



## [2020-01-06 03:49:33](https://github.com/leanprover-community/mathlib/commit/15c434a)
chore(*): various simple lemmas about `*_equiv`, add missing attrs ([#1854](https://github.com/leanprover-community/mathlib/pull/1854))
* chore(*): various simple lemmas about `*_equiv`, add missing attrs
* Fix compile of `ring_theory/localization`
#### Estimated changes
Modified src/data/equiv/algebra.lean
- \+/\- *lemma* mul_equiv.map_eq_one_iff
- \+/\- *lemma* mul_equiv.map_ne_one_iff
- \+/\- *lemma* ring_equiv.map_add
- \+ *lemma* ring_equiv.map_eq_one_iff
- \+ *lemma* ring_equiv.map_eq_zero_iff
- \+/\- *lemma* ring_equiv.map_mul
- \+ *lemma* ring_equiv.map_ne_one_iff
- \+ *lemma* ring_equiv.map_ne_zero_iff
- \+/\- *lemma* ring_equiv.map_neg
- \+/\- *lemma* ring_equiv.map_neg_one
- \+/\- *lemma* ring_equiv.map_one
- \+/\- *lemma* ring_equiv.map_sub
- \+/\- *lemma* ring_equiv.map_zero

Modified src/data/set/function.lean
- \+ *lemma* set.inj_on.to_bij_on

Modified src/linear_algebra/basic.lean
- \+ *theorem* linear_equiv.map_add
- \+ *theorem* linear_equiv.map_eq_zero_iff
- \+ *theorem* linear_equiv.map_ne_zero_iff
- \+ *theorem* linear_equiv.map_neg
- \+ *theorem* linear_equiv.map_smul
- \+ *theorem* linear_equiv.map_sub
- \+ *theorem* linear_equiv.map_zero
- \+/\- *def* linear_equiv.refl
- \+/\- *def* linear_equiv.symm
- \+ *def* linear_equiv.to_add_equiv
- \+/\- *def* linear_equiv.trans

Modified src/ring_theory/localization.lean


Modified src/topology/algebra/module.lean
- \+ *theorem* continuous_linear_equiv.coe_comp_coe_symm
- \+ *theorem* continuous_linear_equiv.coe_symm_comp_coe
- \+ *lemma* continuous_linear_equiv.map_eq_zero_iff



## [2020-01-05 21:25:17](https://github.com/leanprover-community/mathlib/commit/63670b5)
feat(data/real/nnreal): add a few simple lemmas ([#1856](https://github.com/leanprover-community/mathlib/pull/1856))
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.div_mul_cancel
- \+ *lemma* nnreal.div_pos
- \+ *lemma* nnreal.half_pos
- \+ *lemma* nnreal.mul_div_cancel'
- \+ *lemma* nnreal.mul_div_cancel



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
- \+ *def* linear_equiv.to_continuous_linear_equiv
- \+ *def* linear_map.to_continuous_linear_map

Modified src/analysis/normed_space/operator_norm.lean


Modified src/topology/algebra/module.lean
- \+/\- *lemma* continuous.smul
- \+ *theorem* continuous_linear_equiv.apply_symm_apply
- \+ *theorem* continuous_linear_equiv.coe_apply
- \+ *lemma* continuous_linear_equiv.coe_coe
- \+ *lemma* continuous_linear_equiv.ext
- \+ *lemma* continuous_linear_equiv.map_add
- \+ *lemma* continuous_linear_equiv.map_neg
- \+ *lemma* continuous_linear_equiv.map_smul
- \+ *lemma* continuous_linear_equiv.map_sub
- \+ *lemma* continuous_linear_equiv.map_zero
- \+ *theorem* continuous_linear_equiv.symm_apply_apply
- \+ *lemma* continuous_linear_equiv.symm_to_linear_equiv
- \+ *def* continuous_linear_equiv.to_continuous_linear_map
- \+ *def* continuous_linear_equiv.to_homeomorph
- \+ *lemma* continuous_linear_equiv.trans_to_linear_equiv
- \+ *structure* continuous_linear_equiv
- \+/\- *lemma* continuous_linear_map.add_comp
- \+/\- *lemma* continuous_linear_map.coe_add'
- \+/\- *lemma* continuous_linear_map.coe_add
- \+/\- *lemma* continuous_linear_map.coe_apply'
- \+/\- *lemma* continuous_linear_map.coe_apply
- \+/\- *lemma* continuous_linear_map.coe_coe
- \+/\- *lemma* continuous_linear_map.coe_comp'
- \+/\- *lemma* continuous_linear_map.coe_comp
- \+/\- *lemma* continuous_linear_map.coe_id'
- \+/\- *lemma* continuous_linear_map.coe_id
- \+/\- *lemma* continuous_linear_map.coe_neg'
- \+/\- *lemma* continuous_linear_map.coe_neg
- \+/\- *lemma* continuous_linear_map.coe_sub'
- \+/\- *lemma* continuous_linear_map.coe_sub
- \+/\- *lemma* continuous_linear_map.coe_zero'
- \+/\- *lemma* continuous_linear_map.coe_zero
- \+/\- *def* continuous_linear_map.comp
- \+/\- *lemma* continuous_linear_map.comp_add
- \+/\- *theorem* continuous_linear_map.comp_zero
- \+/\- *theorem* continuous_linear_map.ext
- \+/\- *theorem* continuous_linear_map.ext_iff
- \+/\- *def* continuous_linear_map.id
- \+/\- *lemma* continuous_linear_map.id_apply
- \+/\- *lemma* continuous_linear_map.map_zero
- \+/\- *lemma* continuous_linear_map.one_apply
- \+/\- *def* continuous_linear_map.prod
- \+/\- *def* continuous_linear_map.smul_right
- \+/\- *lemma* continuous_linear_map.smul_right_apply
- \+/\- *lemma* continuous_linear_map.smul_right_one_eq_iff
- \+/\- *lemma* continuous_linear_map.smul_right_one_one
- \+/\- *lemma* continuous_linear_map.sub_apply
- \+/\- *def* continuous_linear_map.zero
- \+/\- *lemma* continuous_linear_map.zero_apply
- \+/\- *theorem* continuous_linear_map.zero_comp
- \+/\- *lemma* continuous_smul
- \+/\- *lemma* is_closed_map_smul_of_ne_zero
- \+/\- *lemma* is_closed_map_smul_of_unit
- \+/\- *lemma* is_open_map_smul_of_ne_zero
- \+/\- *lemma* is_open_map_smul_of_unit
- \+/\- *abbreviation* topological_vector_space



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
- \+ *lemma* filter.eventually.exists
- \+ *lemma* filter.eventually.frequently
- \+ *lemma* filter.eventually.mono
- \+ *lemma* filter.eventually.mp
- \+ *lemma* filter.eventually_false_iff_eq_bot
- \+ *lemma* filter.eventually_of_forall
- \+ *lemma* filter.eventually_true
- \+ *lemma* filter.frequently.and_eventually
- \+ *lemma* filter.frequently.exists
- \+ *lemma* filter.frequently.mono
- \+ *lemma* filter.frequently.mp
- \+ *lemma* filter.frequently_iff_forall_eventually_exists_and



## [2020-01-02 19:10:24](https://github.com/leanprover-community/mathlib/commit/840bd1f)
feat(analysis/calculus/deriv): add aliases for `const op f` and `f op const` ([#1843](https://github.com/leanprover-community/mathlib/pull/1843))
* feat(analysis/calculus/deriv): add aliases for `const op f` and `f op const`
Often this leads to simpler answers.
* Docs
* Fix compile of `mean_value.lean`
* Drop comments, use `open_locale classical`
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_add_const
- \+ *lemma* deriv_const_add
- \+ *lemma* deriv_const_mul
- \+ *lemma* deriv_const_smul
- \+ *lemma* deriv_const_sub
- \+ *lemma* deriv_mul_const
- \- *lemma* deriv_smul'
- \+ *lemma* deriv_smul
- \+ *lemma* deriv_smul_const
- \+ *lemma* deriv_sub_const
- \+ *lemma* deriv_within_add_const
- \+ *lemma* deriv_within_const_add
- \+ *lemma* deriv_within_const_mul
- \+ *lemma* deriv_within_const_smul
- \+ *lemma* deriv_within_const_sub
- \+ *lemma* deriv_within_mul_const
- \- *lemma* deriv_within_smul'
- \+ *lemma* deriv_within_smul
- \+ *lemma* deriv_within_smul_const
- \+ *lemma* deriv_within_sub_const
- \+ *theorem* has_deriv_at.add_const
- \+ *theorem* has_deriv_at.const_add
- \+ *theorem* has_deriv_at.const_mul
- \+ *theorem* has_deriv_at.const_smul
- \+ *theorem* has_deriv_at.const_sub
- \+ *theorem* has_deriv_at.mul_const
- \- *theorem* has_deriv_at.smul'
- \+ *theorem* has_deriv_at.smul
- \+ *theorem* has_deriv_at.smul_const
- \+ *theorem* has_deriv_at.sub_const
- \+ *theorem* has_deriv_at_filter.add_const
- \+ *theorem* has_deriv_at_filter.const_add
- \+ *theorem* has_deriv_at_filter.const_sub
- \+ *theorem* has_deriv_at_filter.sub_const
- \+ *theorem* has_deriv_within_at.add_const
- \+ *theorem* has_deriv_within_at.const_add
- \+ *theorem* has_deriv_within_at.const_mul
- \+ *theorem* has_deriv_within_at.const_smul
- \+ *theorem* has_deriv_within_at.const_sub
- \+ *theorem* has_deriv_within_at.mul_const
- \- *theorem* has_deriv_within_at.smul'
- \+ *theorem* has_deriv_within_at.smul
- \+ *theorem* has_deriv_within_at.smul_const
- \+ *theorem* has_deriv_within_at.sub_const

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable.add_const
- \+ *lemma* differentiable.const_add
- \+ *lemma* differentiable.const_mul
- \+ *lemma* differentiable.const_smul
- \+ *lemma* differentiable.const_sub
- \+ *lemma* differentiable.mul_const
- \- *lemma* differentiable.smul'
- \+/\- *lemma* differentiable.smul
- \+ *lemma* differentiable.smul_const
- \+ *lemma* differentiable.sub_const
- \+ *lemma* differentiable_at.add_const
- \+ *lemma* differentiable_at.const_add
- \+ *lemma* differentiable_at.const_mul
- \+ *lemma* differentiable_at.const_smul
- \+ *lemma* differentiable_at.const_sub
- \+ *lemma* differentiable_at.mul_const
- \- *lemma* differentiable_at.smul'
- \+/\- *lemma* differentiable_at.smul
- \+ *lemma* differentiable_at.smul_const
- \+ *lemma* differentiable_at.sub_const
- \+ *lemma* differentiable_on.add_const
- \+ *lemma* differentiable_on.const_add
- \+ *lemma* differentiable_on.const_mul
- \+ *lemma* differentiable_on.const_smul
- \+ *lemma* differentiable_on.const_sub
- \+ *lemma* differentiable_on.mul_const
- \- *lemma* differentiable_on.smul'
- \+/\- *lemma* differentiable_on.smul
- \+ *lemma* differentiable_on.smul_const
- \+ *lemma* differentiable_on.sub_const
- \+ *lemma* differentiable_within_at.add_const
- \+ *lemma* differentiable_within_at.const_add
- \+ *lemma* differentiable_within_at.const_mul
- \+ *lemma* differentiable_within_at.const_smul
- \+ *lemma* differentiable_within_at.const_sub
- \+ *lemma* differentiable_within_at.mul_const
- \- *lemma* differentiable_within_at.smul'
- \+/\- *lemma* differentiable_within_at.smul
- \+ *lemma* differentiable_within_at.smul_const
- \+ *lemma* differentiable_within_at.sub_const
- \+ *lemma* fderiv_add_const
- \+ *lemma* fderiv_const_add
- \+ *lemma* fderiv_const_mul
- \+ *lemma* fderiv_const_smul
- \+ *lemma* fderiv_const_sub
- \+ *lemma* fderiv_mul_const
- \- *lemma* fderiv_smul'
- \+/\- *lemma* fderiv_smul
- \+ *lemma* fderiv_smul_const
- \+ *lemma* fderiv_sub_const
- \+ *lemma* fderiv_within_add_const
- \+ *lemma* fderiv_within_const_add
- \+ *lemma* fderiv_within_const_mul
- \+ *lemma* fderiv_within_const_smul
- \+ *lemma* fderiv_within_const_sub
- \+ *lemma* fderiv_within_mul_const
- \- *lemma* fderiv_within_smul'
- \+ *lemma* fderiv_within_smul_const
- \+ *lemma* fderiv_within_sub_const
- \+ *theorem* has_fderiv_at.add_const
- \+ *theorem* has_fderiv_at.const_add
- \+ *theorem* has_fderiv_at.const_mul
- \+ *theorem* has_fderiv_at.const_smul
- \+ *theorem* has_fderiv_at.const_sub
- \+ *theorem* has_fderiv_at.mul_const
- \- *theorem* has_fderiv_at.smul'
- \+/\- *theorem* has_fderiv_at.smul
- \+ *theorem* has_fderiv_at.smul_const
- \+ *theorem* has_fderiv_at.sub_const
- \+ *theorem* has_fderiv_at_filter.add_const
- \+ *theorem* has_fderiv_at_filter.const_add
- \+ *theorem* has_fderiv_at_filter.const_smul
- \+ *theorem* has_fderiv_at_filter.const_sub
- \- *theorem* has_fderiv_at_filter.smul
- \+ *theorem* has_fderiv_at_filter.sub_const
- \+ *theorem* has_fderiv_within_at.add_const
- \+ *theorem* has_fderiv_within_at.const_add
- \+ *theorem* has_fderiv_within_at.const_mul
- \+ *theorem* has_fderiv_within_at.const_smul
- \+ *theorem* has_fderiv_within_at.const_sub
- \+ *theorem* has_fderiv_within_at.mul_const
- \- *theorem* has_fderiv_within_at.smul'
- \+/\- *theorem* has_fderiv_within_at.smul
- \+ *theorem* has_fderiv_within_at.smul_const
- \+ *theorem* has_fderiv_within_at.sub_const

Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/complex/exponential.lean
- \+ *lemma* has_deriv_at.cexp
- \+ *lemma* has_deriv_at.rexp
- \+ *lemma* has_deriv_within_at.cexp
- \+ *lemma* has_deriv_within_at.rexp



## [2020-01-02 18:35:24](https://github.com/leanprover-community/mathlib/commit/7b18bbf)
feat(topology/algebra/ordered): add `*_mem_nhds_within_Ioi`, reorder args of `is_closed.Icc_subset_of_forall_exists_gt` ([#1844](https://github.com/leanprover-community/mathlib/pull/1844))
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+ *lemma* Icc_mem_nhds_within_Ioi
- \+ *lemma* Ico_mem_nhds_within_Ioi
- \+ *lemma* Ioc_mem_nhds_within_Ioi
- \+ *lemma* Ioo_mem_nhds_within_Ioi
- \+ *lemma* mem_nhds_within_Iio_iff_exists_mem_Ico_Ioo_subset
- \+ *lemma* mem_nhds_within_Ioi_iff_exists_mem_Ioc_Ioo_subset



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
- \+ *lemma* continuous_on_id
- \+ *lemma* continuous_within_at_const
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
- \+ *lemma* nhds_within_Iio_ne_bot'
- \+ *lemma* nhds_within_Iio_ne_bot
- \+ *lemma* nhds_within_Iio_self_ne_bot'
- \+ *lemma* nhds_within_Iio_self_ne_bot
- \+ *lemma* nhds_within_Ioi_ne_bot'
- \+ *lemma* nhds_within_Ioi_ne_bot
- \+ *lemma* nhds_within_Ioi_self_ne_bot'
- \+ *lemma* nhds_within_Ioi_self_ne_bot



## [2020-01-01 22:13:19](https://github.com/leanprover-community/mathlib/commit/d08d509)
fix(metric_space/gromo_hausdorff): lemma should be instance + linting ([#1840](https://github.com/leanprover-community/mathlib/pull/1840))
#### Estimated changes
Modified src/topology/metric_space/gromov_hausdorff.lean
- \+/\- *theorem* Gromov_Hausdorff.GH_dist_le_of_approx_subsets
- \- *lemma* Gromov_Hausdorff.second_countable

