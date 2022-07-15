## [2019-07-31 16:48:18](https://github.com/leanprover-community/mathlib/commit/49be50f)
doc(data/padics, data/real/cau_seq, algebra): add doc strings, remove unnecessary assumptions ([#1283](https://github.com/leanprover-community/mathlib/pull/1283))
* doc(data/padics): add doc strings, remove unnecessary prime assumptions
* fix(data/real/cau_seq): remove unnecessary hypotheses
* fix(algebra/{field, ordered_field}): remove unused assumptions
* doc(data/real/cau_seq): document Cauchy sequences
* fix(algebra/field): remove obsolete lemma
* fix build
* fix build
* more unnecessary arguments
* Update src/data/padics/padic_numbers.lean
* Update src/data/padics/padic_numbers.lean
* remove another unnecessary argument (suggested by @sgouezel)
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/field.lean
- \+/\- *lemma* div_mul_div_cancel
- \- *lemma* field.div_mul_div_cancel
- \+/\- *lemma* units.units.mk0_inj

Modified src/algebra/ordered_field.lean
- \+/\- *lemma* nat.inv_pos_of_nat
- \+/\- *lemma* nat.one_div_pos_of_nat

Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_integers.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean
- \+/\- *lemma* padic.coe_inj

Modified src/data/real/cau_seq.lean


Modified src/topology/instances/complex.lean


Modified src/topology/instances/real.lean




## [2019-07-31 14:37:08](https://github.com/leanprover-community/mathlib/commit/88d60dc)
feat(data/pnat/basic): coe_bit0 and coe_bit1 ([#1288](https://github.com/leanprover-community/mathlib/pull/1288))
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *lemma* pnat.coe_bit0
- \+ *lemma* pnat.coe_bit1



## [2019-07-31 13:28:58](https://github.com/leanprover-community/mathlib/commit/53680f9)
feat(data/matrix): mul_sum and sum_mul ([#1253](https://github.com/leanprover-community/mathlib/pull/1253))
* feat(data/matrix): mul_sum and sum_mul
* Update matrix.lean
* add comment explaing funny proof
#### Estimated changes
Modified src/data/matrix.lean
- \+ *lemma* matrix.is_add_monoid_hom_mul_left
- \+ *def* matrix.is_add_monoid_hom_mul_right



## [2019-07-31 10:41:10](https://github.com/leanprover-community/mathlib/commit/da46b32)
feat(tactic/symmetry_at): apply symmetry on assumptions ([#1269](https://github.com/leanprover-community/mathlib/pull/1269))
* feat(tactic/symmetry_at): apply symmetry on assumptions
* add docstrings
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Modified test/tactics.lean




## [2019-07-31 08:37:56](https://github.com/leanprover-community/mathlib/commit/badeb48)
feat(data/equiv/algebra): change mul_equiv field to map_mul ([#1287](https://github.com/leanprover-community/mathlib/pull/1287))
* feat(data/equiv/algebra): bundle field for mul_equiv
* adding docs
* Update src/data/equiv/algebra.lean
* Update src/data/equiv/algebra.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
#### Estimated changes
Modified src/category_theory/endomorphism.lean


Modified src/data/equiv/algebra.lean
- \+ *def* add_equiv.apply_symm_apply
- \+ *def* add_equiv.map_add
- \+ *def* add_equiv.map_zero
- \+ *def* add_equiv.refl
- \+ *def* add_equiv.symm
- \+ *def* add_equiv.symm_apply_apply
- \+ *def* add_equiv.to_add_monoid_hom
- \+ *theorem* add_equiv.to_equiv_symm
- \+ *def* add_equiv.trans
- \+ *def* mul_equiv.apply_symm_apply
- \+ *def* mul_equiv.map_mul
- \+ *def* mul_equiv.map_one
- \+ *def* mul_equiv.symm_apply_apply
- \+ *theorem* mul_equiv.to_equiv_symm
- \+ *def* mul_equiv.to_monoid_hom

Modified src/data/mv_polynomial.lean


Modified src/linear_algebra/basic.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/noetherian.lean




## [2019-07-30 11:45:46](https://github.com/leanprover-community/mathlib/commit/9d589d7)
feat(data/nat/fib): add Fibonacci sequence ([#1279](https://github.com/leanprover-community/mathlib/pull/1279))
#### Estimated changes
Added src/data/nat/fib.lean
- \+ *def* nat.fib
- \+ *lemma* nat.fib_le_fib_succ
- \+ *lemma* nat.fib_mono
- \+ *lemma* nat.fib_one
- \+ *lemma* nat.fib_pos
- \+ *lemma* nat.fib_succ_succ
- \+ *lemma* nat.fib_zero
- \+ *lemma* nat.le_fib_self



## [2019-07-30 06:58:24](https://github.com/leanprover-community/mathlib/commit/0b47675)
feat(algebra,data/complex/exponential): add abs_neg_one_pow, remove hyp from div_le_div_of_le_left ([#1280](https://github.com/leanprover-community/mathlib/pull/1280))
#### Estimated changes
Modified src/algebra/field.lean
- \+/\- *lemma* inv_eq_zero

Modified src/algebra/group_power.lean
- \+ *lemma* abs_neg_one_pow

Modified src/algebra/ordered_field.lean
- \+/\- *lemma* div_le_div_of_le_left

Modified src/data/complex/exponential.lean




## [2019-07-29 21:10:06](https://github.com/leanprover-community/mathlib/commit/132bc56)
doc(windows.md): clarify windows instructions ([#1165](https://github.com/leanprover-community/mathlib/pull/1165))
* doc(windows.md): clarify windows instructions
* fix headers
* remove msys2 from windows installation instructions
* fix sentence
* typo
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* doc(windows.md): small changes
typos, and explicitly discourage msys2
#### Estimated changes
Modified docs/install/windows.md




## [2019-07-29 16:17:43](https://github.com/leanprover-community/mathlib/commit/363f187)
feat(tactic/extract_goal): create stand-alone examples out of current goal ([#1233](https://github.com/leanprover-community/mathlib/pull/1233))
* feat(tactic/extract_example): create stand-alone examples out of current goal
* feat(tactic/extract_example): add formatting and options
* feat(tactic/extract_goal): rename to `extract_goal`
* Update src/tactic/interactive.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* make instances anonymous when the name starts with `_`
* add doc strings
* feat(tactic/interactive): exact_goal works on defs
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.ilast'_mem
- \- *theorem* list.last'_mem

Modified src/data/list/defs.lean
- \+ *def* list.ilast'
- \+/\- *def* list.last'

Modified src/data/string/defs.lean
- \+ *def* string.is_prefix_of
- \+ *def* string.is_suffix_of

Modified src/tactic/core.lean


Modified src/tactic/interactive.lean




## [2019-07-29 14:13:00](https://github.com/leanprover-community/mathlib/commit/ee15f68)
doc(category_theory): adding headers and basic comments to files without ([#1264](https://github.com/leanprover-community/mathlib/pull/1264))
* doc(category_theory): adding headers and basic comments to files without
* Update src/category_theory/instances/rel.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* fix imports
* more comments, references
* refs
* Update src/category_theory/monad/adjunction.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* fixing all the copyright headers
* Update src/category_theory/monad/adjunction.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* fix import
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/CommRing/colimits.lean


Modified src/algebra/CommRing/limits.lean


Modified src/algebra/Mon/colimits.lean


Modified src/algebraic_geometry/presheafed_space.lean


Modified src/algebraic_geometry/stalks.lean


Modified src/category_theory/adjunction/fully_faithful.lean


Modified src/category_theory/comma.lean


Modified src/category_theory/const.lean


Modified src/category_theory/currying.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/elements.lean


Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/full_subcategory.lean


Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/functor_category.lean


Modified src/category_theory/instances/kleisli.lean


Modified src/category_theory/instances/rel.lean
- \+ *def* category_theory.Rel
- \- *def* category_theory.rel

Modified src/category_theory/isomorphism.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/limits/limits.lean


Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/default.lean


Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean


Modified src/category_theory/limits/types.lean


Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monad/algebra.lean


Modified src/category_theory/monad/limits.lean


Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/category_aux.lean


Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/monoidal/types.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/category_theory/opposites.lean


Modified src/category_theory/pempty.lean


Modified src/category_theory/products/associator.lean


Modified src/category_theory/products/bifunctor.lean


Modified src/category_theory/products/default.lean


Modified src/category_theory/punit.lean


Modified src/category_theory/sparse.lean


Modified src/category_theory/types.lean


Modified src/category_theory/whiskering.lean


Modified src/category_theory/yoneda.lean


Modified src/tactic/auto_cases.lean


Modified src/tactic/chain.lean


Modified src/tactic/library_search.lean


Modified src/tactic/local_cache.lean


Modified src/tactic/rewrite_all/basic.lean


Modified src/tactic/rewrite_all/congr.lean


Modified src/tactic/rewrite_all/default.lean


Modified src/tactic/slice.lean


Modified src/tactic/tidy.lean


Modified src/topology/Top/adjunctions.lean


Modified src/topology/Top/basic.lean


Modified src/topology/Top/default.lean


Modified src/topology/Top/epi_mono.lean


Modified src/topology/Top/limits.lean


Modified src/topology/Top/open_nhds.lean


Modified src/topology/Top/opens.lean


Modified src/topology/Top/presheaf.lean


Modified src/topology/Top/presheaf_of_functions.lean


Modified src/topology/Top/stalks.lean


Modified src/topology/algebra/TopCommRing/basic.lean


Modified src/topology/algebra/continuous_functions.lean


Modified test/fin_cases.lean


Modified test/library_search/basic.lean


Modified test/library_search/ordered_ring.lean


Modified test/library_search/ring_theory.lean


Modified test/mllist.lean


Modified test/rewrite_all.lean


Modified test/tidy.lean




## [2019-07-29 11:22:47](https://github.com/leanprover-community/mathlib/commit/5adeebf)
feat(algebra/group/hom): bundled monoid and group homs ([#1271](https://github.com/leanprover-community/mathlib/pull/1271))
* feat(algebra/group/hom): adding bundled group homs
* adding module docstring
* moving some group stuff into monoid
* responding to PR comments
* mk'' -> mk'
* spaces before `}`
* Update src/algebra/group/hom.lean
* Update src/algebra/group/hom.lean
* Update src/algebra/group/hom.lean
* Update src/algebra/group/hom.lean
* Update hom.lean
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *def* add_monoid_hom.comp
- \+ *def* add_monoid_hom.ext
- \+ *def* add_monoid_hom.id
- \+ *def* add_monoid_hom.map_add
- \+ *theorem* add_monoid_hom.map_neg
- \+ *theorem* add_monoid_hom.map_sub
- \+ *def* add_monoid_hom.map_zero
- \+ *def* add_monoid_hom.mk'
- \+ *def* add_monoid_hom.neg
- \+ *structure* add_monoid_hom
- \+ *def* monoid_hom.comp
- \+ *def* monoid_hom.ext
- \+ *def* monoid_hom.id
- \+ *theorem* monoid_hom.map_div
- \+ *theorem* monoid_hom.map_inv
- \+ *lemma* monoid_hom.map_mul
- \+ *lemma* monoid_hom.map_one
- \+ *def* monoid_hom.mk'
- \+ *structure* monoid_hom



## [2019-07-28 10:35:05](https://github.com/leanprover-community/mathlib/commit/879da1c)
fix(algebraic_geometry/presheafedspace): fix lame proofs ([#1273](https://github.com/leanprover-community/mathlib/pull/1273))
* fix(algebraic_geometry/presheafedspace): fix lame proofs
* fix
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean
- \- *lemma* algebraic_geometry.PresheafedSpace.comp_c

Modified src/algebraic_geometry/stalks.lean




## [2019-07-28 05:13:16](https://github.com/leanprover-community/mathlib/commit/9689f4d)
feat(tactic/interactive): move `rotate` into interactive namespace ([#1272](https://github.com/leanprover-community/mathlib/pull/1272))
also document `swap`
Add test
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/interactive.lean


Modified test/tactics.lean




## [2019-07-25 14:09:56+02:00](https://github.com/leanprover-community/mathlib/commit/d5a5393)
doc(contribute/index.md): add line about large PRs [ci skip] ([#1267](https://github.com/leanprover-community/mathlib/pull/1267))
#### Estimated changes
Modified docs/contribute/index.md




## [2019-07-25 10:40:50](https://github.com/leanprover-community/mathlib/commit/03c0d6c)
feat(algebra/group/basic): add_add_neg_cancel'_right ([#1261](https://github.com/leanprover-community/mathlib/pull/1261))
* feat(algebra/group/basic): add_add_neg_cancel'_right
* fix build
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* add_add_neg_cancel'_right

Modified src/analysis/convex.lean


Modified src/number_theory/pell.lean


Modified src/topology/metric_space/isometry.lean




## [2019-07-25 10:48:28+02:00](https://github.com/leanprover-community/mathlib/commit/926467d)
doc(contribute/style.md): fix section on comments [ci skip] ([#1265](https://github.com/leanprover-community/mathlib/pull/1265))
#### Estimated changes
Modified docs/contribute/style.md




## [2019-07-25 08:45:56](https://github.com/leanprover-community/mathlib/commit/1000ae8)
doc(*): new documentation requirements ([#1229](https://github.com/leanprover-community/mathlib/pull/1229))
* feat(docs/contribute/doc): template for documentation
* doc(data/padics/padic_norm): new doc style
* doc(docs/contribute/code-review): add link to doc requirements
* doc(.github/PULL_REQUEST_TEMPLATE): add link to doc requirements
* doc(topology/basic): adds new style documentation
* feat(tactic/doc_blame): a user command #doc_blame
It lists definitions without docstrings in the current file
* perf(tactic/doc_blame): filter declarations earlier
* doc(contribute/doc): More doc style explanations
* doc(data/padics/padic_norm): finish documenting
* doc(docs/contribute/docs): more text about documentation requirements
* feat(tactic/doc_blame): add option to blame theorems also
* doc(cardinal/ordinal): add some documentation
add header to cardinal.lean
fix some information in topological_spaces.md (but not all)
* fix(data/padics): remove leftover exit command
* doc(*): update proposed doc style
* doc(docs/contribute/doc.md): update doc style guide
* feat(docs/references): add mathlib references bibtex
* update doc style in times_cont_diff and add to list of examples
* fix(docs/contribute/doc): clarify implementation notes
* doc(tactic/doc_blame): add header
#### Estimated changes
Modified .github/PULL_REQUEST_TEMPLATE.md


Modified docs/contribute/code-review.md


Added docs/contribute/doc.md


Added docs/references.bib


Modified docs/theories/topological_spaces.md


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/data/padics/padic_norm.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/ordinal.lean


Modified src/tactic/basic.lean


Added src/tactic/doc_blame.lean
- \+ *def* name.is_not_auto

Modified src/topology/basic.lean




## [2019-07-24 15:32:15](https://github.com/leanprover-community/mathlib/commit/5125f11)
feat(data/matrix): smul_val ([#1262](https://github.com/leanprover-community/mathlib/pull/1262))
* feat(data/matrix): smul_val
* Update src/data/matrix.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/matrix.lean
- \+ *lemma* matrix.smul_val



## [2019-07-24 11:03:46](https://github.com/leanprover-community/mathlib/commit/ed57916)
feat(category_theory): functions to convert is_lawful_functor and is_… ([#1258](https://github.com/leanprover-community/mathlib/pull/1258))
* feat(category_theory): functions to convert is_lawful_functor and is_lawful_monad to their corresponding category_theory concepts
* Fix typo
* feat(category): add mjoin_map_pure, mjoin_pure to the simpset (and use <$> notation)
#### Estimated changes
Modified src/category/basic.lean
- \+ *lemma* mjoin_map_map
- \+ *lemma* mjoin_map_mjoin
- \+ *lemma* mjoin_map_pure
- \+ *lemma* mjoin_pure

Modified src/category_theory/monad/default.lean


Added src/category_theory/monad/types.lean


Modified src/category_theory/types.lean
- \+ *def* category_theory.of_type_functor
- \+ *lemma* category_theory.of_type_functor_map
- \+ *lemma* category_theory.of_type_functor_obj



## [2019-07-24 05:14:48](https://github.com/leanprover-community/mathlib/commit/b0c5251)
cleanup(category_theory/monoidal): use equiv on prod/punit intead of adding new constants ([#1257](https://github.com/leanprover-community/mathlib/pull/1257))
#### Estimated changes
Modified src/category_theory/monoidal/types.lean
- \- *def* category_theory.monoidal.types_associator
- \- *def* category_theory.monoidal.types_associator_inv
- \- *def* category_theory.monoidal.types_braiding
- \- *def* category_theory.monoidal.types_braiding_inv
- \- *def* category_theory.monoidal.types_left_unitor
- \- *def* category_theory.monoidal.types_left_unitor_inv
- \- *def* category_theory.monoidal.types_right_unitor
- \- *def* category_theory.monoidal.types_right_unitor_inv



## [2019-07-23 11:10:07](https://github.com/leanprover-community/mathlib/commit/4a5529a)
feat(data/array): add some simp attributes ([#1255](https://github.com/leanprover-community/mathlib/pull/1255))
#### Estimated changes
Modified src/data/array/lemmas.lean
- \+/\- *theorem* array.read_foreach
- \+/\- *theorem* array.read_map₂



## [2019-07-22 19:45:42](https://github.com/leanprover-community/mathlib/commit/a33315d)
feat(linear_algebra/dim): findim equivalence ([#1217](https://github.com/leanprover-community/mathlib/pull/1217))
* feat(linear_algebra/dim): findim equivalence
* feat(linear_algebra/dim): two versions of dim_fun
* feat(linear_algebra/dim): clean up
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_fin_fun
- \+/\- *lemma* dim_fun
- \+ *lemma* dim_fun_eq_lift_mul

Modified src/linear_algebra/finsupp_vector_space.lean
- \+/\- *lemma* eq_bot_iff_dim_eq_zero
- \+ *def* equiv_of_dim_eq_dim
- \- *lemma* equiv_of_dim_eq_dim
- \+ *lemma* equiv_of_dim_eq_lift_dim
- \+ *lemma* fin_dim_vectorspace_equiv
- \+/\- *lemma* injective_of_surjective

Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.mk_prod
- \+ *theorem* cardinal.sum_const_eq_lift_mul



## [2019-07-22 16:29:29](https://github.com/leanprover-community/mathlib/commit/3e77fec)
feat(linear_algebra/finite_dimensional): finite dimensional vector spaces ([#1241](https://github.com/leanprover-community/mathlib/pull/1241))
* feat(linear_algebra/finite_dimensional): finite dimensional vector spaces
* rw `of_span_finite_eq_top` to `of_fg`
* prove infinite.nat_embedding
* generalize finite_of_linear_independent to noetherian modules
* fix build
* fix build (ring_theory/polynomial)
#### Estimated changes
Modified src/data/fintype.lean


Modified src/linear_algebra/basis.lean
- \+/\- *lemma* eq_of_linear_independent_of_span_subtype
- \+ *lemma* le_of_span_le_span
- \+ *lemma* span_le_span_iff

Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_bot
- \+ *lemma* dim_top

Added src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.card_eq_findim
- \+ *lemma* finite_dimensional.dim_lt_omega
- \+ *lemma* finite_dimensional.eq_top_of_findim_eq
- \+ *lemma* finite_dimensional.exists_is_basis_finite
- \+ *lemma* finite_dimensional.findim_eq_dim
- \+ *lemma* finite_dimensional.finite_dimensional_iff_dim_lt_omega
- \+ *lemma* finite_dimensional.of_fg
- \+ *def* finite_dimensional
- \+ *lemma* linear_map.injective_iff_surjective
- \+ *lemma* linear_map.ker_eq_bot_iff_range_eq_top
- \+ *lemma* linear_map.mul_eq_one_comm
- \+ *lemma* linear_map.mul_eq_one_of_mul_eq_one
- \+ *lemma* linear_map.surjective_of_injective

Modified src/ring_theory/noetherian.lean
- \+ *lemma* finite_of_linear_independent
- \+/\- *lemma* well_founded_submodule_gt

Modified src/ring_theory/polynomial.lean




## [2019-07-22 11:20:31](https://github.com/leanprover-community/mathlib/commit/fd91660)
feat(data/power_series): Add multivariate power series and prove basic API ([#1244](https://github.com/leanprover-community/mathlib/pull/1244))
* First start on power_series
* Innocent changes
* Almost a comm_semiring
* Defined hom from mv_polynomial to mv_power_series; sorrys remain
* Attempt that seem to go nowhere
* Working on coeff_mul for polynomials
* Small progress
* Finish mv_polynomial.coeff_mul
* Cleaner proof of mv_polynomial.coeff_mul
* Fix build
* WIP
* Finish proof of mul_assoc
* WIP
* Golfing coeff_mul
* WIP
* Crazy wf is crazy
* mv_power_series over local ring is local
* WIP
* Add empty line
* wip
* wip
* WIP
* WIP
* WIP
* Add header comments
* WIP
* WIP
* Fix finsupp build
* Fix build, hopefully
* Fix build: ideals
* More docs
* Update src/data/power_series.lean
Fix typo.
* Fix build -- bump instance search depth
* Make changes according to some of the review comments
* Use 'formal' in the names
* Use 'protected' in more places, remove '@simp's
* Make 'inv_eq_zero' an iff
* Generalize to non-commutative scalars
* Move file
* Undo name change, back to 'power_series'
* spelling mistake
* spelling mistake
#### Estimated changes
Modified src/analysis/calculus/mean_value.lean


Modified src/data/finsupp.lean
- \+ *lemma* finsupp.le_iff
- \+ *def* finsupp.lt_wf
- \+ *lemma* finsupp.single_eq_zero
- \+ *lemma* finsupp.single_right_inj
- \+ *lemma* finsupp.sum_id_lt_of_lt
- \+ *lemma* finsupp.to_multiset_strict_mono
- \+ *lemma* finsupp.unique_single_eq_iff

Modified src/ring_theory/ideals.lean


Added src/ring_theory/power_series.lean
- \+ *def* mv_polynomial.to_mv_power_series
- \+ *lemma* mv_polynomial.to_mv_power_series_coeff
- \+ *def* mv_power_series.C
- \+ *lemma* mv_power_series.C_add
- \+ *lemma* mv_power_series.C_mul
- \+ *lemma* mv_power_series.C_one
- \+ *lemma* mv_power_series.C_zero
- \+ *def* mv_power_series.X
- \+ *def* mv_power_series.coeff
- \+ *lemma* mv_power_series.coeff_C
- \+ *lemma* mv_power_series.coeff_C_zero
- \+ *lemma* mv_power_series.coeff_X''
- \+ *lemma* mv_power_series.coeff_X'
- \+ *lemma* mv_power_series.coeff_X
- \+ *lemma* mv_power_series.coeff_add
- \+ *lemma* mv_power_series.coeff_inv
- \+ *lemma* mv_power_series.coeff_inv_aux
- \+ *lemma* mv_power_series.coeff_inv_of_unit
- \+ *lemma* mv_power_series.coeff_map
- \+ *lemma* mv_power_series.coeff_monomial'
- \+ *lemma* mv_power_series.coeff_monomial
- \+ *lemma* mv_power_series.coeff_mul
- \+ *lemma* mv_power_series.coeff_neg
- \+ *lemma* mv_power_series.coeff_one
- \+ *lemma* mv_power_series.coeff_one_zero
- \+ *lemma* mv_power_series.coeff_trunc
- \+ *lemma* mv_power_series.coeff_zero
- \+ *lemma* mv_power_series.coeff_zero_inv
- \+ *lemma* mv_power_series.coeff_zero_inv_of_unit
- \+ *lemma* mv_power_series.ext
- \+ *lemma* mv_power_series.ext_iff
- \+ *lemma* mv_power_series.inv_eq_zero
- \+ *def* mv_power_series.inv_of_unit
- \+ *lemma* mv_power_series.inv_of_unit_eq'
- \+ *lemma* mv_power_series.inv_of_unit_eq
- \+ *def* mv_power_series.is_local_ring
- \+ *lemma* mv_power_series.is_unit_coeff_zero
- \+ *def* mv_power_series.map
- \+ *lemma* mv_power_series.map_add
- \+ *lemma* mv_power_series.map_comp
- \+ *lemma* mv_power_series.map_id
- \+ *lemma* mv_power_series.map_mul
- \+ *lemma* mv_power_series.map_one
- \+ *lemma* mv_power_series.map_zero
- \+ *def* mv_power_series.monomial
- \+ *lemma* mv_power_series.monomial_add
- \+ *lemma* mv_power_series.monomial_zero
- \+ *lemma* mv_power_series.mul_inv_of_unit
- \+ *def* mv_power_series.trunc
- \+ *lemma* mv_power_series.trunc_C
- \+ *lemma* mv_power_series.trunc_add
- \+ *lemma* mv_power_series.trunc_one
- \+ *lemma* mv_power_series.trunc_zero
- \+ *def* mv_power_series
- \+ *def* polynomial.to_power_series
- \+ *lemma* polynomial.to_power_series_coeff
- \+ *def* power_series.C
- \+ *lemma* power_series.C_add
- \+ *lemma* power_series.C_mul
- \+ *lemma* power_series.C_one
- \+ *lemma* power_series.C_zero
- \+ *def* power_series.X
- \+ *def* power_series.coeff
- \+ *lemma* power_series.coeff_C
- \+ *lemma* power_series.coeff_C_zero
- \+ *lemma* power_series.coeff_X'
- \+ *lemma* power_series.coeff_X
- \+ *lemma* power_series.coeff_add
- \+ *lemma* power_series.coeff_inv
- \+ *lemma* power_series.coeff_inv_aux
- \+ *lemma* power_series.coeff_inv_of_unit
- \+ *lemma* power_series.coeff_map
- \+ *lemma* power_series.coeff_mk
- \+ *lemma* power_series.coeff_monomial'
- \+ *lemma* power_series.coeff_monomial
- \+ *lemma* power_series.coeff_mul
- \+ *lemma* power_series.coeff_one
- \+ *lemma* power_series.coeff_one_zero
- \+ *lemma* power_series.coeff_trunc
- \+ *lemma* power_series.coeff_zero
- \+ *lemma* power_series.coeff_zero_inv
- \+ *lemma* power_series.coeff_zero_inv_of_unit
- \+ *lemma* power_series.ext
- \+ *lemma* power_series.ext_iff
- \+ *lemma* power_series.inv_eq_zero
- \+ *def* power_series.inv_of_unit
- \+ *lemma* power_series.inv_of_unit_eq'
- \+ *lemma* power_series.inv_of_unit_eq
- \+ *lemma* power_series.is_local_ring
- \+ *def* power_series.map
- \+ *lemma* power_series.map_add
- \+ *lemma* power_series.map_comp
- \+ *lemma* power_series.map_id
- \+ *lemma* power_series.map_mul
- \+ *lemma* power_series.map_one
- \+ *lemma* power_series.map_zero
- \+ *def* power_series.mk
- \+ *def* power_series.monomial
- \+ *lemma* power_series.monomial_add
- \+ *lemma* power_series.monomial_eq_mk
- \+ *lemma* power_series.monomial_zero
- \+ *lemma* power_series.mul_inv_of_unit
- \+ *def* power_series.trunc
- \+ *lemma* power_series.trunc_C
- \+ *lemma* power_series.trunc_add
- \+ *lemma* power_series.trunc_one
- \+ *lemma* power_series.trunc_zero
- \+ *def* power_series



## [2019-07-22 08:00:24](https://github.com/leanprover-community/mathlib/commit/7c09ed5)
feat(category_theory/*): define `Cat` and a fully faithful functor `Mon ⥤ Cat` ([#1235](https://github.com/leanprover-community/mathlib/pull/1235))
* feat(category_theory/*): define `Cat` and a fully faithful functor `Mon ⥤ Cat`
* Drop 2 commas
* Drop `functor.id_comp` etc, add `Cat.str` instance, adjust module-level comments
* Make `α` and `β` arguments of `map_hom_equiv` explicit
This way `e α β f` is automatically interpreted as `(e α β).to_fun f`.
#### Estimated changes
Added src/category_theory/Cat.lean
- \+ *def* category_theory.Cat.objects
- \+ *def* category_theory.Cat.of
- \+ *def* category_theory.Cat

Modified src/category_theory/functor.lean


Added src/category_theory/single_obj.lean
- \+ *def* Mon.to_Cat
- \+ *def* category_theory.single_obj.map_hom
- \+ *lemma* category_theory.single_obj.map_hom_comp
- \+ *def* category_theory.single_obj.map_hom_equiv
- \+ *lemma* category_theory.single_obj.map_hom_id
- \+ *def* category_theory.single_obj.to_End
- \+ *lemma* category_theory.single_obj.to_End_def
- \+ *def* category_theory.single_obj.to_End_equiv
- \+ *def* category_theory.single_obj



## [2019-07-22 09:13:12+02:00](https://github.com/leanprover-community/mathlib/commit/b5a641e)
chore(data/polynomial): clean up commented code ([#1251](https://github.com/leanprover-community/mathlib/pull/1251))
Commented code that wasn't removed after a refactor.
#### Estimated changes
Modified src/data/polynomial.lean




## [2019-07-22 01:35:42](https://github.com/leanprover-community/mathlib/commit/f24dc98)
feat(logic/unique): forall_iff and exists_iff ([#1249](https://github.com/leanprover-community/mathlib/pull/1249))
Maybe these should be `@[simp]`. My use case in `fin 1` and it's slightly annoying to have `default (fin 1)` everwhere instead of `0`, but maybe that should also be a `@[simp]` lemma.
#### Estimated changes
Modified src/logic/unique.lean
- \+ *lemma* unique.exists_iff
- \+ *lemma* unique.forall_iff



## [2019-07-22 01:13:25](https://github.com/leanprover-community/mathlib/commit/a8c2923)
refactor(ring_theory/noetherian): change order of instance arguments ([#1250](https://github.com/leanprover-community/mathlib/pull/1250))
Zulip discussion https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Type.20class.20failure
This change makes some type class searches work better.
#### Estimated changes
Modified src/ring_theory/noetherian.lean




## [2019-07-20 18:50:28](https://github.com/leanprover-community/mathlib/commit/93419b3)
chore(data/equiv/algebra): add `ring.to_mul/add_equiv`, DRY ([#1247](https://github.com/leanprover-community/mathlib/pull/1247))
#### Estimated changes
Modified src/data/equiv/algebra.lean
- \+ *def* ring_equiv.to_add_equiv
- \+ *def* ring_equiv.to_mul_equiv



## [2019-07-20 17:33:46](https://github.com/leanprover-community/mathlib/commit/d371da6)
fix(group_theory/subgroup): fix some typos introduced in 66a86ffe0 ([#1246](https://github.com/leanprover-community/mathlib/pull/1246))
#### Estimated changes
Modified src/group_theory/subgroup.lean




## [2019-07-20 06:49:37](https://github.com/leanprover-community/mathlib/commit/6e3516d)
feat(category_theory/monad): monadic adjunctions ([#1176](https://github.com/leanprover-community/mathlib/pull/1176))
* feat(category_theory/limits): equivalences create limits
* equivalence lemma
* feat(category_theory/monad): monadic adjunctions
* move file
* fix
* add @[simp]
* use right_adjoint_preserves_limits
* fix
* fix
* undo weird changes in topology files
* formatting
* do colimits too
* missing proofs
* convert monad to a typeclass decorating a functor
* changing name
* cleaning up
* oops
* minor
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean
- \+ *def* category_theory.left_adjoint
- \+ *def* category_theory.right_adjoint

Added src/category_theory/adjunction/fully_faithful.lean


Added src/category_theory/monad/adjunction.lean
- \+ *lemma* category_theory.adjunction.monad_η_app
- \+ *lemma* category_theory.adjunction.monad_μ_app
- \+ *def* category_theory.monad.comparison
- \+ *def* category_theory.monad.comparison_forget
- \+ *lemma* category_theory.monad.comparison_map_f
- \+ *lemma* category_theory.monad.comparison_obj_a
- \+ *lemma* category_theory.reflective.comparison_ess_surj_aux

Added src/category_theory/monad/algebra.lean
- \+ *def* category_theory.monad.adj
- \+ *lemma* category_theory.monad.algebra.comp_f
- \+ *def* category_theory.monad.algebra.hom.comp
- \+ *lemma* category_theory.monad.algebra.hom.comp_f
- \+ *lemma* category_theory.monad.algebra.hom.ext
- \+ *def* category_theory.monad.algebra.hom.id
- \+ *lemma* category_theory.monad.algebra.hom.id_f
- \+ *structure* category_theory.monad.algebra.hom
- \+ *lemma* category_theory.monad.algebra.id_f
- \+ *structure* category_theory.monad.algebra
- \+ *def* category_theory.monad.forget
- \+ *lemma* category_theory.monad.forget_map
- \+ *def* category_theory.monad.free
- \+ *lemma* category_theory.monad.free_map_f
- \+ *lemma* category_theory.monad.free_obj_a

Added src/category_theory/monad/basic.lean


Added src/category_theory/monad/default.lean


Added src/category_theory/monad/limits.lean
- \+ *def* category_theory.has_limits_of_reflective
- \+ *def* category_theory.monad.forget_creates_limits.c
- \+ *lemma* category_theory.monad.forget_creates_limits.c_π
- \+ *def* category_theory.monad.forget_creates_limits.cone_point
- \+ *lemma* category_theory.monad.forget_creates_limits.cone_point_a
- \+ *def* category_theory.monad.forget_creates_limits.γ
- \+ *lemma* category_theory.monad.forget_creates_limits.γ_app
- \+ *def* category_theory.monad.forget_creates_limits
- \+ *def* category_theory.monadic_creates_limits

Modified src/category_theory/natural_isomorphism.lean
- \+ *def* category_theory.nat_iso.is_iso_app_of_is_iso

Modified src/topology/algebra/TopCommRing/basic.lean




## [2019-07-19 17:09:12](https://github.com/leanprover-community/mathlib/commit/9505e5b)
fix(data/matrix): use pi.module for the module structure ([#1242](https://github.com/leanprover-community/mathlib/pull/1242))
* fix(data/matrix): use pi.module for the module structure
* Update matrix.lean
* Update matrix.lean
* Update matrix.lean
#### Estimated changes
Modified src/data/matrix.lean




## [2019-07-19 14:39:27](https://github.com/leanprover-community/mathlib/commit/07ae80f)
refactor(algebra/*): delete `free_monoid` from `algebra/free`, restore some functions in `algebra/group/with_one` ([#1227](https://github.com/leanprover-community/mathlib/pull/1227))
* refactor(algebra/*): Remove `free_monoid` from `algebra/free`, fixes [#929](https://github.com/leanprover-community/mathlib/pull/929)
* use `namespace with_one`
* Add `with_one.coe_is_mul_hom`
* Restore `with_one.lift` etc from `algebra/free` `free_monoid.lift` etc
* Define `with_one.map` based on the deleted `free_monoid.map`
Define using `option.map`, and prove equivalence to `λ f, lift $ coe ∘ f`.
#### Estimated changes
Modified src/algebra/free.lean
- \- *def* semigroup.free_monoid.lift
- \- *lemma* semigroup.free_monoid.lift_mul
- \- *lemma* semigroup.free_monoid.lift_of
- \- *lemma* semigroup.free_monoid.lift_one
- \- *theorem* semigroup.free_monoid.lift_unique
- \- *def* semigroup.free_monoid.map
- \- *lemma* semigroup.free_monoid.map_mul
- \- *lemma* semigroup.free_monoid.map_of
- \- *def* semigroup.free_monoid.of
- \- *lemma* semigroup.free_monoid.of_mul
- \- *def* semigroup.free_monoid

Modified src/algebra/group/with_one.lean
- \+/\- *lemma* with_one.coe_inj
- \+/\- *lemma* with_one.coe_ne_one
- \+ *def* with_one.lift
- \+ *lemma* with_one.lift_coe
- \+ *lemma* with_one.lift_one
- \+ *theorem* with_one.lift_unique
- \+ *def* with_one.map
- \+ *lemma* with_one.map_eq
- \+/\- *lemma* with_one.mul_coe
- \+/\- *lemma* with_one.ne_one_iff_exists
- \+/\- *lemma* with_one.one_ne_coe



## [2019-07-19 14:09:02](https://github.com/leanprover-community/mathlib/commit/74754ac)
feat(analysis/calculus/times_cont_diff): multiple differentiability ([#1226](https://github.com/leanprover-community/mathlib/pull/1226))
* feat(analysis/calculus/times_cont_diff): multiple differentiability
* style
* style
* style and documentation
* better wording
#### Estimated changes
Added src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* is_bounded_bilinear_map.times_cont_diff
- \+ *lemma* is_bounded_linear_map.times_cont_diff
- \+ *def* iterated_continuous_linear_map.normed_group_rec
- \+ *def* iterated_continuous_linear_map.normed_space_rec
- \+ *def* iterated_continuous_linear_map
- \+ *def* iterated_fderiv
- \+ *lemma* iterated_fderiv_succ
- \+ *def* iterated_fderiv_within
- \+ *lemma* iterated_fderiv_within_congr
- \+ *lemma* iterated_fderiv_within_inter
- \+ *lemma* iterated_fderiv_within_inter_open
- \+ *lemma* iterated_fderiv_within_succ
- \+ *theorem* iterated_fderiv_within_univ
- \+ *lemma* iterated_fderiv_within_zero
- \+ *lemma* iterated_fderiv_zero
- \+ *lemma* times_cont_diff.comp
- \+ *lemma* times_cont_diff.comp_is_bounded_linear
- \+ *lemma* times_cont_diff.continuous
- \+ *lemma* times_cont_diff.continuous_fderiv
- \+ *lemma* times_cont_diff.continuous_fderiv_apply
- \+ *lemma* times_cont_diff.of_le
- \+ *lemma* times_cont_diff.of_succ
- \+ *lemma* times_cont_diff.prod
- \+ *lemma* times_cont_diff.times_cont_diff_fderiv_apply
- \+ *lemma* times_cont_diff.times_cont_diff_on
- \+ *def* times_cont_diff
- \+ *lemma* times_cont_diff_const
- \+ *lemma* times_cont_diff_fst
- \+ *lemma* times_cont_diff_id
- \+ *theorem* times_cont_diff_iff_times_cont_diff_rec
- \+ *lemma* times_cont_diff_on.comp
- \+ *lemma* times_cont_diff_on.comp_is_bounded_linear
- \+ *lemma* times_cont_diff_on.congr
- \+ *lemma* times_cont_diff_on.congr_mono'
- \+ *lemma* times_cont_diff_on.congr_mono
- \+ *lemma* times_cont_diff_on.continuous_on
- \+ *lemma* times_cont_diff_on.continuous_on_fderiv_within
- \+ *lemma* times_cont_diff_on.continuous_on_fderiv_within_apply
- \+ *lemma* times_cont_diff_on.mono
- \+ *lemma* times_cont_diff_on.of_le
- \+ *lemma* times_cont_diff_on.of_succ
- \+ *lemma* times_cont_diff_on.prod
- \+ *def* times_cont_diff_on
- \+ *lemma* times_cont_diff_on_fderiv_within
- \+ *lemma* times_cont_diff_on_fderiv_within_apply
- \+ *lemma* times_cont_diff_on_fderiv_within_nat
- \+ *theorem* times_cont_diff_on_iff_times_cont_diff_on_rec
- \+ *lemma* times_cont_diff_on_of_locally_times_cont_diff_on
- \+ *lemma* times_cont_diff_on_rec.continuous_on_iterated_fderiv_within
- \+ *lemma* times_cont_diff_on_rec.differentiable_on
- \+ *lemma* times_cont_diff_on_rec.of_succ
- \+ *def* times_cont_diff_on_rec
- \+ *lemma* times_cont_diff_on_rec_succ
- \+ *lemma* times_cont_diff_on_rec_univ
- \+ *lemma* times_cont_diff_on_rec_zero
- \+ *lemma* times_cont_diff_on_succ
- \+ *lemma* times_cont_diff_on_top
- \+ *lemma* times_cont_diff_on_univ
- \+ *lemma* times_cont_diff_on_zero
- \+ *lemma* times_cont_diff_rec.continuous
- \+ *lemma* times_cont_diff_rec.differentiable
- \+ *lemma* times_cont_diff_rec.of_succ
- \+ *def* times_cont_diff_rec
- \+ *lemma* times_cont_diff_rec_succ
- \+ *lemma* times_cont_diff_rec_zero
- \+ *lemma* times_cont_diff_snd
- \+ *lemma* times_cont_diff_succ
- \+ *lemma* times_cont_diff_top
- \+ *lemma* times_cont_diff_zero

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* is_bounded_bilinear_map_apply
- \+ *lemma* is_bounded_linear_map.fst
- \+ *lemma* is_bounded_linear_map.snd



## [2019-07-18 15:15:54](https://github.com/leanprover-community/mathlib/commit/8b102eb)
feat(topology/algebra/group): define filter pointwise addition ([#1215](https://github.com/leanprover-community/mathlib/pull/1215))
* Create .DS_Store
* Revert "Create .DS_Store"
This reverts commit 5612886d493aef59205eddc5a34a75e6e5ba22c1.
* feat (topology/algebral/uniform_group) : prove dense_embedding.extend extends continuous linear maps linearly
* Update src/algebra/pointwise.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Fix styles
* Add homomorphism instances; fix conflicting names
* Update group.lean
* Update uniform_group.lean
* Add header; prove every topological group is regular
* Fix headers and errors
* Update pi_instances.lean
#### Estimated changes
Modified src/algebra/pi_instances.lean


Modified src/algebra/pointwise.lean
- \+ *lemma* set.image_pointwise_mul
- \- *lemma* set.mul_subset_mul
- \+ *lemma* set.pointwise_mul_eq_Union_mul_left
- \+ *lemma* set.pointwise_mul_eq_Union_mul_right
- \+ *lemma* set.pointwise_mul_ne_empty
- \+ *lemma* set.preimage_pointwise_mul_preimage_subset
- \+ *lemma* set.univ_pointwise_mul_univ

Added src/order/filter/pointwise.lean
- \+ *lemma* filter.comap_mul_comap_le
- \+ *lemma* filter.map_pointwise_mul
- \+ *lemma* filter.map_pointwise_one
- \+ *lemma* filter.mem_pointwise_mul
- \+ *lemma* filter.mem_pointwise_one
- \+ *lemma* filter.mul_mem_pointwise_mul
- \+ *def* filter.pointwise_add
- \+ *def* filter.pointwise_add_map_is_add_monoid_hom
- \+ *def* filter.pointwise_mul
- \+ *lemma* filter.pointwise_mul_assoc
- \+ *lemma* filter.pointwise_mul_le_mul
- \+ *def* filter.pointwise_mul_map_is_monoid_hom
- \+ *def* filter.pointwise_mul_monoid
- \+ *lemma* filter.pointwise_mul_ne_bot
- \+ *lemma* filter.pointwise_mul_one
- \+ *def* filter.pointwise_one
- \+ *lemma* filter.pointwise_one_mul
- \+ *lemma* filter.tendsto_mul_mul

Modified src/topology/algebra/group.lean
- \+ *lemma* is_closed_map_mul_left
- \+ *lemma* is_closed_map_mul_right
- \+ *lemma* is_open_pointwise_mul_left
- \+ *lemma* is_open_pointwise_mul_right
- \+ *def* nhds_is_mul_hom
- \+ *lemma* nhds_pointwise_mul
- \+ *lemma* topological_group.regular_space
- \+ *lemma* topological_group.t1_space
- \+ *lemma* topological_group.t2_space

Modified src/topology/constructions.lean




## [2019-07-18 06:27:03](https://github.com/leanprover-community/mathlib/commit/e704f94)
fix(data/{nat,int}/parity): fix definition of 'even' ([#1240](https://github.com/leanprover-community/mathlib/pull/1240))
#### Estimated changes
Modified src/data/int/parity.lean
- \+/\- *def* int.even

Modified src/data/nat/parity.lean
- \+/\- *def* nat.even



## [2019-07-17 17:57:06+02:00](https://github.com/leanprover-community/mathlib/commit/86e7287)
fix(data/zmod/basic) remove unused argument from instance ([#1239](https://github.com/leanprover-community/mathlib/pull/1239))
#### Estimated changes
Modified src/data/zmod/basic.lean




## [2019-07-17 09:56:01](https://github.com/leanprover-community/mathlib/commit/d6fd044)
feat(*): add nat.antidiagonal and use it for polynomial.mul_coeff ([#1237](https://github.com/leanprover-community/mathlib/pull/1237))
#### Estimated changes
Modified src/data/finset.lean
- \+ *def* finset.nat.antidiagonal
- \+ *lemma* finset.nat.antidiagonal_zero
- \+ *lemma* finset.nat.card_antidiagonal
- \+ *lemma* finset.nat.mem_antidiagonal

Modified src/data/list/basic.lean
- \+ *def* list.nat.antidiagonal
- \+ *lemma* list.nat.antidiagonal_zero
- \+ *lemma* list.nat.length_antidiagonal
- \+ *lemma* list.nat.mem_antidiagonal
- \+ *lemma* list.nat.nodup_antidiagonal

Modified src/data/multiset.lean
- \+ *def* multiset.nat.antidiagonal
- \+ *lemma* multiset.nat.antidiagonal_zero
- \+ *lemma* multiset.nat.card_antidiagonal
- \+ *lemma* multiset.nat.mem_antidiagonal
- \+ *lemma* multiset.nat.nodup_antidiagonal

Modified src/data/polynomial.lean
- \+ *lemma* polynomial.coeff_mul
- \- *lemma* polynomial.coeff_mul_left
- \- *lemma* polynomial.coeff_mul_right



## [2019-07-16 22:00:41](https://github.com/leanprover-community/mathlib/commit/8785bd0)
refactor(data/multiset): rename diagonal to antidiagonal ([#1236](https://github.com/leanprover-community/mathlib/pull/1236))
* refactor(data/multiset): rename diagonal to antidiagonal
* Add docstrings
* fix build
* Fix build
#### Estimated changes



## [2019-07-16 21:01:49](https://github.com/leanprover-community/mathlib/commit/e186fbb)
feat(data/mv_polynomial): coeff_mul ([#1216](https://github.com/leanprover-community/mathlib/pull/1216))
* feat(data/mv_polynomial): coeff_mul
* refactor(data/multiset): rename diagonal to antidiagonal
* Rename diagonal to antidiagonal
* Define antidiagonal as to_finsupp instead of to_finset
* Add docstrings
* fix build
* Fix build
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *def* finsupp.antidiagonal
- \+ *lemma* finsupp.antidiagonal_zero
- \+ *lemma* finsupp.mem_antidiagonal_support
- \+ *lemma* finsupp.swap_mem_antidiagonal_support
- \+ *lemma* finsupp.to_multiset_to_finsupp
- \+ *def* multiset.to_finsupp
- \+ *lemma* multiset.to_finsupp_add
- \+ *lemma* multiset.to_finsupp_apply
- \+ *lemma* multiset.to_finsupp_singleton
- \+ *lemma* multiset.to_finsupp_support
- \+ *lemma* multiset.to_finsupp_to_multiset
- \+ *lemma* multiset.to_finsupp_zero

Modified src/data/multiset.lean
- \+ *def* multiset.antidiagonal
- \+ *theorem* multiset.antidiagonal_coe'
- \+ *theorem* multiset.antidiagonal_coe
- \+ *theorem* multiset.antidiagonal_cons
- \+ *theorem* multiset.antidiagonal_map_fst
- \+ *theorem* multiset.antidiagonal_map_snd
- \+ *theorem* multiset.antidiagonal_zero
- \+ *theorem* multiset.card_antidiagonal
- \- *theorem* multiset.card_diagonal
- \- *def* multiset.diagonal
- \- *theorem* multiset.diagonal_coe'
- \- *theorem* multiset.diagonal_coe
- \- *theorem* multiset.diagonal_cons
- \- *theorem* multiset.diagonal_map_fst
- \- *theorem* multiset.diagonal_map_snd
- \- *theorem* multiset.diagonal_zero
- \+ *theorem* multiset.mem_antidiagonal
- \- *theorem* multiset.mem_diagonal
- \+/\- *theorem* multiset.revzip_powerset_aux'
- \+/\- *theorem* multiset.revzip_powerset_aux

Modified src/data/mv_polynomial.lean
- \+ *lemma* mv_polynomial.coeff_X'
- \+/\- *lemma* mv_polynomial.coeff_X
- \+ *lemma* mv_polynomial.coeff_X_pow
- \+ *lemma* mv_polynomial.coeff_mul
- \+/\- *lemma* mv_polynomial.coeff_mul_X'
- \+/\- *lemma* mv_polynomial.coeff_mul_X



## [2019-07-15 21:35:36](https://github.com/leanprover-community/mathlib/commit/92ac50c)
chore(data/finset): rename le_min_of_mem to min_le_of_mem ([#1231](https://github.com/leanprover-community/mathlib/pull/1231))
* chore(data/finset): rename le_min_of_mem to min_le_of_mem
* fix build
#### Estimated changes
Modified src/data/finset.lean
- \- *theorem* finset.le_min_of_mem
- \+/\- *theorem* finset.min'_le
- \+ *theorem* finset.min_le_of_mem



## [2019-07-15 14:48:52](https://github.com/leanprover-community/mathlib/commit/7217f13)
feat(data/option/basic): bind_eq_none ([#1232](https://github.com/leanprover-community/mathlib/pull/1232))
* feat(data/option/basis): bind_eq_none
* delete extra line
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *theorem* option.bind_eq_none



## [2019-07-15 13:09:35](https://github.com/leanprover-community/mathlib/commit/46074fc)
chore(data/fintype): change `unique.fintype` to priority 0 ([#1230](https://github.com/leanprover-community/mathlib/pull/1230))
#### Estimated changes
Modified src/data/fintype.lean
- \+ *def* unique.fintype



## [2019-07-15 00:44:50](https://github.com/leanprover-community/mathlib/commit/0e9ac84)
feat(tactic/rcases): add obtain tactic ([#1218](https://github.com/leanprover-community/mathlib/pull/1218))
* feat(tactic/rcases): add obtain tactic
* style(tactic/rcases): line break
* doc(docs/tactics): document obtain
* feat(tactic/obtain): support := syntax
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/core.lean


Modified src/tactic/rcases.lean


Modified test/rcases.lean




## [2019-07-14 11:14:14](https://github.com/leanprover-community/mathlib/commit/dcf0130)
feat(data/pequiv): partial equivalences ([#1206](https://github.com/leanprover-community/mathlib/pull/1206))
* feat(data/pequiv): partial equivalences
* Update src/data/pequiv.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
* use notation
#### Estimated changes
Added src/data/pequiv.lean
- \+ *def* equiv.to_pequiv
- \+ *lemma* equiv.to_pequiv_refl
- \+ *lemma* equiv.to_pequiv_symm
- \+ *lemma* equiv.to_pequiv_trans
- \+ *lemma* pequiv.bot_apply
- \+ *lemma* pequiv.bot_trans
- \+ *lemma* pequiv.coe_mk_apply
- \+ *lemma* pequiv.eq_some_iff
- \+ *lemma* pequiv.ext
- \+ *lemma* pequiv.ext_iff
- \+ *lemma* pequiv.injective_of_forall_is_some
- \+ *lemma* pequiv.injective_of_forall_ne_is_some
- \+ *lemma* pequiv.is_some_symm_get
- \+ *lemma* pequiv.le_def
- \+ *lemma* pequiv.mem_iff_mem
- \+ *lemma* pequiv.mem_of_set_iff
- \+ *lemma* pequiv.mem_of_set_self_iff
- \+ *lemma* pequiv.mem_single
- \+ *lemma* pequiv.mem_single_iff
- \+ *lemma* pequiv.mem_trans
- \+ *def* pequiv.of_set
- \+ *lemma* pequiv.of_set_eq_refl
- \+ *lemma* pequiv.of_set_eq_some_iff
- \+ *lemma* pequiv.of_set_eq_some_self_iff
- \+ *lemma* pequiv.of_set_symm
- \+ *lemma* pequiv.of_set_univ
- \+ *lemma* pequiv.refl_apply
- \+ *lemma* pequiv.refl_trans
- \+ *lemma* pequiv.refl_trans_apply
- \+ *def* pequiv.single
- \+ *lemma* pequiv.single_apply
- \+ *lemma* pequiv.single_apply_of_ne
- \+ *lemma* pequiv.single_subsingleton_eq_refl
- \+ *lemma* pequiv.single_trans_of_eq_none
- \+ *lemma* pequiv.single_trans_of_mem
- \+ *lemma* pequiv.single_trans_single
- \+ *lemma* pequiv.single_trans_single_of_ne
- \+ *lemma* pequiv.symm_bot
- \+ *lemma* pequiv.symm_injective
- \+ *lemma* pequiv.symm_refl
- \+ *lemma* pequiv.symm_refl_apply
- \+ *lemma* pequiv.symm_single
- \+ *lemma* pequiv.symm_symm
- \+ *lemma* pequiv.symm_symm_apply
- \+ *lemma* pequiv.symm_trans
- \+ *lemma* pequiv.symm_trans_rev
- \+ *lemma* pequiv.trans_assoc
- \+ *lemma* pequiv.trans_bot
- \+ *lemma* pequiv.trans_eq_none
- \+ *lemma* pequiv.trans_eq_some
- \+ *lemma* pequiv.trans_refl
- \+ *lemma* pequiv.trans_refl_apply
- \+ *lemma* pequiv.trans_single_of_eq_none
- \+ *lemma* pequiv.trans_single_of_mem
- \+ *lemma* pequiv.trans_symm
- \+ *lemma* pequiv.trans_symm_eq_iff_forall_is_some
- \+ *structure* pequiv



## [2019-07-14 05:25:05](https://github.com/leanprover-community/mathlib/commit/03e6d0e)
chore(algebra/group/hom): add `is_monoid_hom.of_mul`, use it ([#1225](https://github.com/leanprover-community/mathlib/pull/1225))
* Let `to_additive` generate `is_add_monoid_hom.map_add`
* Converting `is_mul_hom` into `is_monoid_hom` doesn't require `α` to be a group
* Simplify the proof of `is_add_group_hom.map_sub`
Avoid `simp` (without `only`)
#### Estimated changes
Modified src/algebra/group/hom.lean
- \- *lemma* is_add_monoid_hom.map_add
- \+ *lemma* is_group_hom.map_one
- \- *theorem* is_group_hom.map_one
- \- *lemma* is_group_hom.to_is_monoid_hom
- \+ *theorem* is_monoid_hom.of_mul



## [2019-07-13 20:54:54](https://github.com/leanprover-community/mathlib/commit/51f2645)
feat(pformat): provide `trace!` and `fail!` and allow tactic values ([#1222](https://github.com/leanprover-community/mathlib/pull/1222))
#### Estimated changes
Modified src/tactic/core.lean




## [2019-07-13 18:17:06](https://github.com/leanprover-community/mathlib/commit/a1cfc5c)
feat(logic,data/equiv,prod): various lemmas ([#1224](https://github.com/leanprover-community/mathlib/pull/1224))
* feat(logic,data/equiv,prod): various lemmas
* Update basic.lean
* Update basic.lean
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.Pi_curry

Modified src/data/prod.lean
- \+ *lemma* prod.map_fst'
- \+ *lemma* prod.map_snd'

Modified src/logic/basic.lean
- \+ *lemma* exists_imp_exists'
- \+/\- *theorem* exists_swap
- \+/\- *theorem* forall_swap



## [2019-07-13 16:25:07](https://github.com/leanprover-community/mathlib/commit/0eea0d9)
feat(data/{nat,int}/parity): the 'even' predicate on nat and int ([#1219](https://github.com/leanprover-community/mathlib/pull/1219))
* feat(data/{nat,int}/parity): the 'even' predicate on nat and int
* fix(data/{nat,int}/parity): shorten proof
* delete extra comma
#### Estimated changes
Added src/data/int/parity.lean
- \+ *def* int.even
- \+ *theorem* int.even_add
- \+ *theorem* int.even_bit0
- \+ *theorem* int.even_coe_nat
- \+ *theorem* int.even_iff
- \+ *theorem* int.even_mul
- \+ *theorem* int.even_pow
- \+ *theorem* int.even_sub
- \+ *theorem* int.even_zero
- \+ *theorem* int.mod_two_ne_one
- \+ *theorem* int.mod_two_ne_zero
- \+ *theorem* int.not_even_bit1
- \+ *theorem* int.not_even_one

Added src/data/nat/parity.lean
- \+ *def* nat.even
- \+ *theorem* nat.even_add
- \+ *theorem* nat.even_bit0
- \+ *theorem* nat.even_iff
- \+ *theorem* nat.even_mul
- \+ *theorem* nat.even_pow
- \+ *theorem* nat.even_sub
- \+ *theorem* nat.even_succ
- \+ *theorem* nat.even_zero
- \+ *theorem* nat.mod_two_ne_one
- \+ *theorem* nat.mod_two_ne_zero
- \+ *theorem* nat.not_even_bit1
- \+ *theorem* nat.not_even_one



## [2019-07-13 01:46:58](https://github.com/leanprover-community/mathlib/commit/6db5829)
feat(data/finmap): extend the API ([#1223](https://github.com/leanprover-community/mathlib/pull/1223))
#### Estimated changes
Modified src/data/finmap.lean
- \+ *def* finmap.all
- \+ *def* finmap.any
- \+ *lemma* finmap.disjoint.symm
- \+ *lemma* finmap.disjoint.symm_iff
- \+ *def* finmap.disjoint
- \+ *lemma* finmap.disjoint_empty
- \+ *lemma* finmap.disjoint_union_left
- \+ *lemma* finmap.disjoint_union_right
- \+/\- *theorem* finmap.empty_to_finmap
- \+ *theorem* finmap.empty_union
- \+ *theorem* finmap.erase_erase
- \+ *theorem* finmap.erase_union_singleton
- \+ *theorem* finmap.ext_lookup
- \+ *theorem* finmap.insert_insert
- \+ *theorem* finmap.insert_insert_of_ne
- \+ *theorem* finmap.insert_singleton_eq
- \+ *theorem* finmap.insert_union
- \+ *theorem* finmap.lookup_insert_of_ne
- \+ *theorem* finmap.lookup_list_to_finmap
- \+ *lemma* finmap.lookup_singleton_eq
- \+ *theorem* finmap.lookup_union_left_of_not_in
- \+ *lemma* finmap.mem_iff
- \+ *theorem* finmap.mem_list_to_finmap
- \+ *lemma* finmap.mem_of_lookup_eq_some
- \+ *lemma* finmap.mem_singleton
- \+ *theorem* finmap.not_mem_erase_self
- \+ *def* finmap.sdiff
- \+ *theorem* finmap.to_finmap_cons
- \+ *theorem* finmap.to_finmap_nil
- \+ *theorem* finmap.union_assoc
- \+ *theorem* finmap.union_cancel
- \+ *theorem* finmap.union_comm_of_disjoint
- \+ *theorem* finmap.union_empty
- \+ *def* list.to_finmap

Modified src/data/list/alist.lean
- \+ *def* alist.disjoint
- \+ *theorem* alist.entries_to_alist
- \+ *theorem* alist.erase_erase
- \+ *theorem* alist.insert_insert
- \+ *theorem* alist.insert_insert_of_ne
- \+ *lemma* alist.insert_singleton_eq
- \+ *theorem* alist.insert_union
- \+ *theorem* alist.lookup_to_alist
- \+ *theorem* alist.to_alist_cons
- \+ *theorem* alist.union_assoc
- \+ *theorem* alist.union_comm_of_disjoint
- \+ *theorem* alist.union_erase
- \+ *def* list.to_alist

Modified src/data/list/basic.lean
- \+ *theorem* list.foldl_eq_foldr'
- \+ *theorem* list.foldl_eq_of_comm'
- \+ *theorem* list.foldr_eq_of_comm'
- \+ *theorem* list.mem_enum_from
- \+ *theorem* list.pw_filter_map

Modified src/data/list/sigma.lean
- \+ *def* list.erase_dupkeys
- \+ *lemma* list.erase_dupkeys_cons
- \+ *theorem* list.kerase_kerase
- \+ *lemma* list.lookup_erase_dupkeys
- \+ *lemma* list.lookup_ext
- \+ *lemma* list.mem_ext
- \+ *lemma* list.nodupkeys_erase_dupkeys



## [2019-07-12 21:47:13](https://github.com/leanprover-community/mathlib/commit/5a48be3)
chore(data/src/pending): remove unused folder ([#1221](https://github.com/leanprover-community/mathlib/pull/1221))
#### Estimated changes
Deleted src/pending/default.lean




## [2019-07-12 20:05:55](https://github.com/leanprover-community/mathlib/commit/fb7dfa1)
feat(data/{nat,int,zmod,finset}): add a few useful facts ([#1220](https://github.com/leanprover-community/mathlib/pull/1220))
* feat(data/finset): add a few useful facts
* feat(data/zmod/basic): express neg in terms of residues
* feat(data/{nat,int}): add theorem 'mod_mod_of_dvd'
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* finset.bind_inter
- \+ *theorem* finset.filter_insert
- \+ *theorem* finset.filter_inter
- \+ *theorem* finset.filter_singleton
- \+ *theorem* finset.inter_bind
- \+ *theorem* finset.inter_filter
- \+ *theorem* finset.inter_sdiff

Modified src/data/int/basic.lean
- \+ *theorem* int.mod_mod
- \- *lemma* int.mod_mod
- \+ *theorem* int.mod_mod_of_dvd

Modified src/data/nat/basic.lean
- \+ *theorem* nat.mod_mod_of_dvd

Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.neg_val'
- \+ *lemma* zmod.neg_val



## [2019-07-12 01:43:22](https://github.com/leanprover-community/mathlib/commit/3d36966)
feat(analysis/calculus/mean_value): the mean value inequality ([#1212](https://github.com/leanprover-community/mathlib/pull/1212))
* feat(analysis/calculus/mean_value): the mean value inequality
* remove blank lines
#### Estimated changes
Added src/analysis/calculus/mean_value.lean
- \+ *theorem* norm_image_sub_le_of_norm_deriv_le_convex
- \+ *theorem* norm_image_sub_le_of_norm_deriv_le_segment

Modified src/analysis/convex.lean
- \+ *lemma* image_Icc_zero_one_eq_segment



## [2019-07-11 21:03:56](https://github.com/leanprover-community/mathlib/commit/7806586)
feat(analysis/calculus/deriv): extended API for derivatives ([#1213](https://github.com/leanprover-community/mathlib/pull/1213))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* differentiable.comp
- \- *lemma* differentiable.congr'
- \- *lemma* differentiable.congr
- \+/\- *lemma* differentiable.differentiable_on
- \- *lemma* differentiable_at.congr
- \+ *lemma* differentiable_at.congr_of_mem_nhds
- \- *lemma* differentiable_at.fderiv_congr'
- \- *lemma* differentiable_at.fderiv_congr
- \+/\- *lemma* differentiable_on.mono
- \+ *lemma* differentiable_within_at.congr_of_mem_nhds_within
- \- *lemma* differentiable_within_at.differentiable_at'
- \+/\- *lemma* differentiable_within_at.mono
- \+/\- *lemma* differentiable_within_at_inter
- \+ *lemma* differentiable_within_at_univ
- \- *lemma* differentiable_within_univ_at
- \+ *lemma* fderiv_congr_of_mem_nhds
- \+ *lemma* fderiv_within_congr
- \+ *lemma* fderiv_within_congr_of_mem_nhds_within
- \+ *lemma* fderiv_within_inter
- \+ *lemma* fderiv_within_subset
- \- *theorem* has_fderiv_at.congr
- \+ *lemma* has_fderiv_at.congr_of_mem_nhds
- \+/\- *lemma* has_fderiv_at.fderiv
- \- *theorem* has_fderiv_at_congr
- \- *lemma* has_fderiv_at_filter.congr'
- \- *theorem* has_fderiv_at_filter.congr
- \+ *lemma* has_fderiv_at_filter.congr_of_mem_sets
- \- *theorem* has_fderiv_at_filter_congr'
- \- *theorem* has_fderiv_at_filter_congr
- \+ *theorem* has_fderiv_at_filter_congr_of_mem_sets
- \- *theorem* has_fderiv_within_at.congr
- \+ *lemma* has_fderiv_within_at.congr_of_mem_nhds_within
- \+/\- *lemma* has_fderiv_within_at.fderiv_within
- \- *theorem* has_fderiv_within_at_congr
- \+ *lemma* has_fderiv_within_at_inter'
- \+ *lemma* has_fderiv_within_at_inter
- \+ *lemma* has_fderiv_within_at_univ
- \- *lemma* has_fderiv_within_univ_at



## [2019-07-11 18:24:16](https://github.com/leanprover-community/mathlib/commit/2511faf)
feat(tactic/localized): localized notation ([#1081](https://github.com/leanprover-community/mathlib/pull/1081))
* first prototype of localized notation
* update
* add test file
* shorten command, fix test
* update documentation
* rename files, add to tactic/default
* typo
* mention that we can use other commands
* optimize
* only use 1 attribute
* add localized command classical instance
* use rb_lmap
This changes the internal code to avoid import clashes and adds a test to that effect
* move rb_lmap.of_list to correct file
also update docstring
* rename open_notation to open_locale
#### Estimated changes
Modified docs/tactics.md


Modified src/meta/rb_map.lean


Modified src/tactic/default.lean


Added src/tactic/localized.lean
- \+ *def* string_hash

Added test/localized/import1.lean


Added test/localized/import2.lean


Added test/localized/import3.lean


Added test/localized/localized.lean




## [2019-07-11 13:58:17](https://github.com/leanprover-community/mathlib/commit/c2cc9a9)
refactor(*): change priority of \simeq ([#1210](https://github.com/leanprover-community/mathlib/pull/1210))
* change priority of \simeq
Also change priority of similar notations
Remove many unnecessary parentheses
* lower precedence on order_embedding and similar
also add parentheses in 1 place where they were needed
* spacing
* add parenthesis
#### Estimated changes
Modified src/algebra/gcd_domain.lean
- \+/\- *def* associates_int_equiv_nat

Modified src/category_theory/endomorphism.lean
- \+/\- *def* category_theory.Aut.units_End_eqv_Aut

Modified src/data/equiv/algebra.lean


Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.arrow_prod_equiv_prod_arrow
- \+/\- *def* equiv.bool_equiv_punit_sum_punit
- \+/\- *def* equiv.bool_prod_equiv_sum
- \+/\- *def* equiv.empty_prod
- \+/\- *def* equiv.empty_sum
- \+/\- *def* equiv.int_equiv_nat_sum_nat
- \+/\- *def* equiv.nat_equiv_nat_sum_punit
- \+/\- *def* equiv.nat_sum_punit_equiv_nat
- \+/\- *def* equiv.option_equiv_sum_punit
- \+/\- *def* equiv.pempty_prod
- \+/\- *def* equiv.pempty_sum
- \+/\- *def* equiv.prod_assoc
- \+/\- *def* equiv.prod_comm
- \+/\- *def* equiv.prod_congr
- \+/\- *def* equiv.prod_empty
- \+/\- *def* equiv.prod_pempty
- \+/\- *def* equiv.prod_punit
- \+/\- *def* equiv.prod_sum_distrib
- \+/\- *def* equiv.psum_equiv_sum
- \+/\- *def* equiv.punit_prod
- \+/\- *theorem* equiv.refl_trans
- \+/\- *def* equiv.sigma_equiv_prod
- \+/\- *def* equiv.sigma_equiv_prod_of_equiv
- \+/\- *def* equiv.sum_arrow_equiv_prod_arrow
- \+/\- *def* equiv.sum_assoc
- \+/\- *def* equiv.sum_comm
- \+/\- *def* equiv.sum_congr
- \+/\- *def* equiv.sum_empty
- \+/\- *def* equiv.sum_equiv_sigma_bool
- \+/\- *def* equiv.sum_pempty
- \+/\- *def* equiv.sum_prod_distrib
- \+/\- *theorem* equiv.symm_symm
- \+/\- *theorem* equiv.symm_symm_apply
- \+/\- *theorem* equiv.trans_refl

Modified src/data/equiv/denumerable.lean
- \+/\- *def* denumerable.pair

Modified src/data/equiv/fin.lean
- \+/\- *def* fin_prod_fin_equiv
- \+/\- *def* sum_fin_sum_equiv

Modified src/data/equiv/nat.lean
- \+/\- *def* equiv.bool_prod_nat_equiv_nat
- \+/\- *def* equiv.nat_prod_nat_equiv_nat
- \+/\- *def* equiv.nat_sum_nat_equiv_nat
- \+/\- *def* equiv.prod_equiv_of_equiv_nat

Modified src/data/finsupp.lean
- \+/\- *def* finsupp.equiv_multiset

Modified src/data/list/sort.lean


Modified src/group_theory/coset.lean


Modified src/linear_algebra/basic.lean


Modified src/order/basic.lean


Modified src/order/filter/basic.lean


Modified src/order/order_iso.lean


Modified src/set_theory/ordinal.lean
- \+/\- *def* initial_seg.lt_or_eq

Modified src/topology/constructions.lean
- \+/\- *def* homeomorph.prod_assoc
- \+/\- *def* homeomorph.prod_comm
- \+/\- *def* homeomorph.prod_congr

Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/isometry.lean




## [2019-07-11 10:12:31](https://github.com/leanprover-community/mathlib/commit/86d0f29)
refactor(*): make `is_group_hom` extend `is_mul_hom` ([#1214](https://github.com/leanprover-community/mathlib/pull/1214))
* map_mul/map_add: use explicit parameters
Preparing to merge `is_mul_hom` with `is_group_hom`
* make `is_group_hom` extend `is_mul_hom`, adjust many proof terms
* Add a comment
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/algebra/direct_limit.lean
- \+/\- *lemma* add_comm_group.direct_limit.lift_add
- \+/\- *lemma* add_comm_group.direct_limit.of_add

Modified src/algebra/direct_sum.lean


Modified src/algebra/group/conj.lean


Modified src/algebra/group/hom.lean
- \+/\- *lemma* is_add_monoid_hom.map_add
- \+/\- *lemma* is_group_hom.inv
- \+ *lemma* is_group_hom.mk'
- \+/\- *lemma* is_group_hom.mul
- \+/\- *lemma* is_monoid_hom.map_mul
- \- *lemma* is_mul_hom.comp'
- \- *lemma* is_mul_hom.comp
- \- *lemma* is_mul_hom.id
- \+ *lemma* is_mul_hom.inv
- \+ *lemma* is_mul_hom.mul

Modified src/algebra/group/units_hom.lean
- \- *lemma* units.map_comp'

Modified src/algebra/group_power.lean


Modified src/algebra/module.lean


Modified src/algebra/punit_instances.lean


Modified src/algebra/ring.lean


Modified src/data/dfinsupp.lean


Modified src/data/equiv/algebra.lean


Modified src/data/mv_polynomial.lean


Modified src/group_theory/abelianization.lean


Modified src/group_theory/free_abelian_group.lean
- \+ *theorem* free_abelian_group.lift.add'

Modified src/group_theory/free_group.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/presented_group.lean


Modified src/group_theory/quotient_group.lean


Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/topology/algebra/group_completion.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/algebra/uniform_ring.lean




## [2019-07-11 07:41:05](https://github.com/leanprover-community/mathlib/commit/1b1c64b)
perf(algebraic_geometry/presheafed_space): replace/optimize tidy scripts ([#1204](https://github.com/leanprover-community/mathlib/pull/1204))
* perf(algebraic_geometry/presheafed_space): replace/optimize tidy scripts
This file now takes 20 seconds to compile on my desktop instead of 160. This is a 9% speedup to mathlib overall.
* doc(algebraic_geometry/presheafed_space): comments
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean




## [2019-07-11 04:18:40](https://github.com/leanprover-community/mathlib/commit/cc5870d)
feat(algebra/ordered_ring): with_top.nat_induction ([#1211](https://github.com/leanprover-community/mathlib/pull/1211))
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* with_top.nat_induction



## [2019-07-10 21:33:20](https://github.com/leanprover-community/mathlib/commit/5cdebb7)
feat(*): Miscellaneous lemmas in algebra ([#1188](https://github.com/leanprover-community/mathlib/pull/1188))
* Trying things out
* feat(ring_theory/*): Misc little lemmas
* More little lemmas
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \- *theorem* add_group.closure_mono
- \- *theorem* add_group.mclosure_inv_subset
- \- *theorem* add_group.mclosure_subset
- \+ *lemma* group.closure_subgroup

Modified src/ring_theory/algebra.lean
- \+ *lemma* span_int_eq
- \+ *lemma* span_int_eq_add_group_closure

Modified src/ring_theory/algebra_operations.lean
- \+ *lemma* submodule.mul_subset_mul
- \+ *lemma* submodule.pow_subset_pow
- \+ *lemma* submodule.smul_def
- \+ *lemma* submodule.smul_le_smul
- \+ *lemma* submodule.smul_singleton

Modified src/ring_theory/ideal_operations.lean
- \+ *lemma* ideal.map_quotient_self
- \+ *lemma* ideal.pow_le_pow

Modified src/ring_theory/ideals.lean
- \+ *lemma* ideal.eq_bot_of_prime
- \+ *lemma* ideal.eq_bot_or_top

Modified src/ring_theory/noetherian.lean
- \+ *lemma* submodule.fg_pow



## [2019-07-10 19:39:24](https://github.com/leanprover-community/mathlib/commit/5aebdc4)
fix(*): fix line endings ([#1209](https://github.com/leanprover-community/mathlib/pull/1209))
#### Estimated changes
Modified src/data/complex/exponential.lean


Modified src/data/nat/totient.lean


Modified src/meta/rb_map.lean


Modified src/tactic/linarith.lean




## [2019-07-10 18:25:32](https://github.com/leanprover-community/mathlib/commit/0bc4a50)
feat(tactic/apply_fun): adds `apply_fun` tactic ([#1184](https://github.com/leanprover-community/mathlib/pull/1184))
* feat(tactic/apply_fun): adds `apply_fun` tactic
* move tests to test folder
* elaborate function with expected type
* fix merge mistake
#### Estimated changes
Modified docs/tactics.md


Added src/tactic/apply_fun.lean


Modified src/tactic/default.lean


Added test/apply_fun.lean




## [2019-07-10 15:57:51](https://github.com/leanprover-community/mathlib/commit/d2b4380)
feat(data/list/basic): list.prod_range_succ, list.sum_range_succ ([#1197](https://github.com/leanprover-community/mathlib/pull/1197))
* feat(data/list/basic): list.prod_range_succ, list.sum_range_succ
* changes from review
* remove simp
* shorten proof
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.prod_range_succ
- \+/\- *theorem* list.range_concat



## [2019-07-10 11:22:33-04:00](https://github.com/leanprover-community/mathlib/commit/8939d95)
docs(contribute/index.md): [#1131](https://github.com/leanprover-community/mathlib/pull/1131) [skip ci]
#### Estimated changes
Modified docs/contribute/index.md




## [2019-07-10 09:10:06-04:00](https://github.com/leanprover-community/mathlib/commit/b00460c)
doc(README): Add link to website
#### Estimated changes
Modified README.md




## [2019-07-10 05:49:09](https://github.com/leanprover-community/mathlib/commit/fb1848b)
refactor(topology/algebra/open_subgroup) Finish TODO ([#1202](https://github.com/leanprover-community/mathlib/pull/1202))
* Create .DS_Store
* Revert "Create .DS_Store"
This reverts commit 5612886d493aef59205eddc5a34a75e6e5ba22c1.
* Finish TODO
* Update src/topology/algebra/open_subgroup.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/topology/algebra/open_subgroup.lean




## [2019-07-10 02:24:53](https://github.com/leanprover-community/mathlib/commit/e25a597)
feat(analysis/calculus/tangent_cone): more properties of the tangent cone ([#1136](https://github.com/leanprover-community/mathlib/pull/1136))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/tangent_cone.lean
- \+/\- *lemma* is_open.unique_diff_within_at
- \+ *lemma* mem_tangent_cone_of_segment_subset
- \+ *lemma* subset_tangent_cone_prod_left
- \+ *lemma* subset_tangent_cone_prod_right
- \+/\- *lemma* tangent_cone_at.lim_zero
- \+ *lemma* tangent_cone_inter_nhds
- \- *lemma* tangent_cone_inter_open
- \+ *lemma* unique_diff_on.prod
- \+ *lemma* unique_diff_on_Icc_zero_one
- \+ *theorem* unique_diff_on_convex
- \+ *lemma* unique_diff_on_univ
- \+ *lemma* unique_diff_within_at.inter
- \+ *lemma* unique_diff_within_at.mono
- \+ *lemma* unique_diff_within_at.prod
- \+/\- *lemma* unique_diff_within_at_inter
- \+ *lemma* unique_diff_within_at_univ
- \- *lemma* unique_diff_within_univ_at



## [2019-07-10 00:10:18](https://github.com/leanprover-community/mathlib/commit/0cd0d4e)
feat(meta/pformat): format! macro using `pp` instead of `to_fmt` ([#1194](https://github.com/leanprover-community/mathlib/pull/1194))
* feat(meta/pformat): format! macro which uses `pp` instead of `to_fmt`
* Update core.lean
#### Estimated changes
Modified src/tactic/core.lean




## [2019-07-09 22:27:43](https://github.com/leanprover-community/mathlib/commit/60e4bb9)
refactor(category_theory/endomorphism): move to a dedicated file; prove simple lemmas ([#1195](https://github.com/leanprover-community/mathlib/pull/1195))
* Move definitions of `End` and `Aut` to a dedicated file
* Adjust some proofs, use `namespace`, add docstrings
* `functor.map` and `functor.map_iso` define homomorphisms of `End/Aut`
* Define `functor.map_End` and `functor.map_Aut`
#### Estimated changes
Modified src/category/fold.lean


Modified src/category_theory/category.lean
- \- *lemma* category_theory.End.mul_def
- \- *lemma* category_theory.End.one_def
- \- *def* category_theory.End

Added src/category_theory/endomorphism.lean
- \+ *def* category_theory.Aut.units_End_eqv_Aut
- \+ *def* category_theory.Aut
- \+ *lemma* category_theory.End.mul_def
- \+ *lemma* category_theory.End.one_def
- \+ *def* category_theory.End
- \+ *def* category_theory.functor.map_Aut
- \+ *def* category_theory.functor.map_End

Modified src/category_theory/isomorphism.lean
- \- *def* category_theory.Aut
- \+ *lemma* category_theory.functor.map_iso_trans



## [2019-07-09 20:34:02](https://github.com/leanprover-community/mathlib/commit/3a7c661)
refactor(topology/*): define and use dense_inducing ([#1193](https://github.com/leanprover-community/mathlib/pull/1193))
* refactor(topology/*): define and dense_inducing
Traditionally, topology extends functions defined on dense subspaces
(equipped by the induced topology).
In mathlib, this was made type-theory-friendly by rather factoring
through `dense_embedding` maps. A map `f : α  → β` between topological
spaces is a dense embedding if its image is dense, it is injective, and
it pulls back the topology from `β` to the topology on `α`. It turns out
that the injectivity was never used in any serious way. It used not to
be used at all until we noticed it could be used to ensure the
factorization equation `dense_embedding.extend_e_eq` could be made to
hold without any assumption on the map to be extended. But of course
this formalization trick is mathematically completely irrelevant.
On the other hand, assuming injectivity prevents direct use in uniform
spaces completion, because the map from a space to its (separated)
completion is injective only when the original space is separated. This
is why mathlib ring completion currently assumes a separated topological
ring, and the perfectoid spaces project needed a lot of effort to drop
that assumption. This commit makes all this completely painless.
Along the way, we improve consistency and readability by turning
a couple of conjunctions into structures. It also introduces long
overdue fix to `function.uncurry` (which suffered from abusive pattern
matching, similar to `prod.map`).
* Apply suggestions from code review
Co-Authored-By: Johan Commelin <johan@commelin.net>
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* minor fixes following review
* Some more dot notation, consistent naming and field naming
#### Estimated changes
Modified src/data/prod.lean
- \+ *lemma* function.injective_prod

Modified src/logic/function.lean
- \+ *lemma* function.curry_uncurry'
- \+ *def* function.uncurry'
- \+ *lemma* function.uncurry'_bicompr
- \+ *lemma* function.uncurry'_curry

Modified src/measure_theory/bochner_integration.lean


Modified src/topology/algebra/group_completion.lean
- \+/\- *lemma* coe_zero

Modified src/topology/algebra/ordered.lean


Modified src/topology/algebra/uniform_group.lean
- \- *lemma* dense_embedding.continuous_extend_of_cauchy
- \- *theorem* dense_embedding.extend_Z_bilin
- \+ *theorem* dense_inducing.extend_Z_bilin

Modified src/topology/algebra/uniform_ring.lean
- \+/\- *lemma* uniform_space.completion.continuous_mul'

Modified src/topology/constructions.lean
- \+ *lemma* dense_range_prod

Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/real.lean
- \+/\- *theorem* embedding_of_rat

Modified src/topology/maps.lean
- \+ *lemma* closed_embedding.comp
- \- *lemma* closed_embedding_compose
- \- *lemma* dense_embedding.closure_image_nhds_of_nhds
- \- *lemma* dense_embedding.closure_range
- \- *lemma* dense_embedding.comap_nhds_neq_bot
- \- *lemma* dense_embedding.continuous_extend
- \- *def* dense_embedding.extend
- \- *lemma* dense_embedding.extend_e_eq
- \- *lemma* dense_embedding.extend_eq
- \+/\- *lemma* dense_embedding.inj_iff
- \- *lemma* dense_embedding.self_sub_closure_image_preimage_of_open
- \- *lemma* dense_embedding.tendsto_comap_nhds_nhds
- \- *lemma* dense_embedding.tendsto_extend
- \+ *lemma* dense_embedding.to_embedding
- \+/\- *structure* dense_embedding
- \+ *lemma* dense_inducing.closure_image_nhds_of_nhds
- \+ *lemma* dense_inducing.closure_range
- \+ *lemma* dense_inducing.comap_nhds_neq_bot
- \+ *lemma* dense_inducing.continuous_extend
- \+ *def* dense_inducing.extend
- \+ *lemma* dense_inducing.extend_e_eq
- \+ *lemma* dense_inducing.extend_eq
- \+ *lemma* dense_inducing.extend_eq_of_cont
- \+ *lemma* dense_inducing.mk'
- \+ *lemma* dense_inducing.nhds_eq_comap
- \+ *lemma* dense_inducing.self_sub_closure_image_preimage_of_open
- \+ *lemma* dense_inducing.tendsto_comap_nhds_nhds
- \+ *lemma* dense_inducing.tendsto_extend
- \+ *structure* dense_inducing
- \+ *lemma* dense_range.comp
- \+ *lemma* dense_range.inhabited
- \+ *def* dense_range
- \+ *lemma* dense_range_iff_closure_eq
- \+ *lemma* embedding.comp
- \+ *def* embedding.mk'
- \+ *lemma* embedding.prod_mk
- \+ *structure* embedding
- \- *def* embedding
- \- *lemma* embedding_compose
- \- *lemma* embedding_prod_mk
- \+ *lemma* inducing.comp
- \+ *lemma* inducing.continuous
- \+ *lemma* inducing.continuous_iff
- \+ *lemma* inducing.map_nhds_eq
- \+ *lemma* inducing.nhds_eq_comap
- \+ *lemma* inducing.prod_mk
- \+ *lemma* inducing.tendsto_nhds_iff
- \+ *structure* inducing
- \+ *lemma* inducing_id
- \+ *lemma* inducing_is_closed
- \+ *lemma* inducing_of_inducing_compose
- \+ *lemma* inducing_open

Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/order.lean
- \+ *lemma* induced_iff_nhds_eq
- \- *lemma* nhds_induced_eq_comap

Modified src/topology/stone_cech.lean
- \+ *lemma* dense_inducing_pure

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* uniform_continuous₂.comp
- \+ *def* uniform_continuous₂
- \+ *lemma* uniform_continuous₂_curry
- \+ *lemma* uniform_continuous₂_def

Modified src/topology/uniform_space/complete_separated.lean
- \+ *lemma* dense_inducing.continuous_extend_of_cauchy
- \+/\- *lemma* is_closed_of_is_complete

Modified src/topology/uniform_space/completion.lean
- \+ *lemma* Cauchy.dense_inducing_pure_cauchy
- \- *def* Cauchy.prod
- \- *lemma* Cauchy.prod_pure_cauchy_pure_cauchy
- \- *lemma* Cauchy.uniform_continuous_prod
- \+ *lemma* Cauchy.uniform_inducing_pure_cauchy
- \+ *lemma* uniform_space.completion.dense_inducing_coe
- \+ *lemma* uniform_space.completion.extension_unique
- \+ *lemma* uniform_space.completion.extension₂_coe_coe
- \+/\- *lemma* uniform_space.completion.map₂_coe_coe
- \+ *lemma* uniform_space.completion.nonempty_completion_iff
- \+/\- *lemma* uniform_space.completion.prod_coe_coe
- \+ *lemma* uniform_space.completion.uniform_continuous_extension₂
- \- *lemma* uniform_space.completion.uniform_continuous_map₂'
- \+ *lemma* uniform_space.completion.uniform_continuous_map₂
- \+ *lemma* uniform_space.completion.uniform_inducing_coe

Modified src/topology/uniform_space/uniform_embedding.lean
- \- *lemma* closure_image_mem_nhds_of_uniform_embedding
- \+ *lemma* closure_image_mem_nhds_of_uniform_inducing
- \+/\- *lemma* complete_space_extension
- \+/\- *lemma* is_complete_image_iff
- \+/\- *lemma* totally_bounded_preimage
- \+ *lemma* uniform_embedding.comp
- \+/\- *lemma* uniform_embedding.dense_embedding
- \+/\- *lemma* uniform_embedding.embedding
- \+/\- *lemma* uniform_embedding.prod
- \- *lemma* uniform_embedding.uniform_continuous
- \- *lemma* uniform_embedding.uniform_continuous_iff
- \+ *structure* uniform_embedding
- \- *def* uniform_embedding
- \+/\- *lemma* uniform_embedding_comap
- \+/\- *theorem* uniform_embedding_def'
- \+/\- *theorem* uniform_embedding_def
- \+/\- *lemma* uniform_embedding_subtype_emb
- \+/\- *lemma* uniform_extend_subtype
- \+ *lemma* uniform_inducing.comp
- \+ *lemma* uniform_inducing.dense_inducing
- \+ *lemma* uniform_inducing.inducing
- \+ *def* uniform_inducing.mk'
- \+ *lemma* uniform_inducing.prod
- \+ *lemma* uniform_inducing.uniform_continuous
- \+ *lemma* uniform_inducing.uniform_continuous_iff
- \+ *structure* uniform_inducing
- \- *lemma* uniformly_extend_of_emb
- \+ *lemma* uniformly_extend_of_ind
- \+/\- *lemma* uniformly_extend_spec



## [2019-07-09 15:55:54](https://github.com/leanprover-community/mathlib/commit/0460815)
fix(docs/tactics): fix code block ([#1201](https://github.com/leanprover-community/mathlib/pull/1201))
#### Estimated changes
Modified docs/tactics.md




## [2019-07-09 15:04:11](https://github.com/leanprover-community/mathlib/commit/0099f06)
perf(data/polynomial, field_theory/splitting_field): memory problems ([#1200](https://github.com/leanprover-community/mathlib/pull/1200))
* perf(data/polynomial): avoid bad instance search
* perf(field_theory/splitting_field): local intance priority makes a big difference
#### Estimated changes
Modified src/data/polynomial.lean


Modified src/field_theory/splitting_field.lean




## [2019-07-09 12:15:39](https://github.com/leanprover-community/mathlib/commit/13f76d3)
feat(tactic): add `convert_to` and `ac_change` ([#944](https://github.com/leanprover-community/mathlib/pull/944))
* feat(tactic): add `convert_to` and `ac_change`
* style fixes
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/interactive.lean


Modified test/tactics.lean




## [2019-07-09 13:05:07+02:00](https://github.com/leanprover-community/mathlib/commit/d50f634)
feat(data/matrix): simp attributes on one_mul and mul_one ([#1199](https://github.com/leanprover-community/mathlib/pull/1199))
#### Estimated changes
Modified src/data/matrix.lean




## [2019-07-09 11:06:35+02:00](https://github.com/leanprover-community/mathlib/commit/6670e66)
feat(data/matrix): simp attributes on zero_mul and mul_zero ([#1198](https://github.com/leanprover-community/mathlib/pull/1198))
#### Estimated changes
Modified src/data/matrix.lean
- \+/\- *theorem* matrix.mul_zero
- \+/\- *theorem* matrix.zero_mul



## [2019-07-09 09:00:44](https://github.com/leanprover-community/mathlib/commit/9071969)
feat(data/nat/basic): some nat inequalities ([#1189](https://github.com/leanprover-community/mathlib/pull/1189))
* feat(data/nat/basic): some inequalities
* remove redundant lemmas
* simplify proofs
* make implicit
* shorter proof
* rename
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.not_succ_lt_self
- \+ *theorem* nat.two_mul_ne_two_mul_add_one



## [2019-07-08 20:51:06-04:00](https://github.com/leanprover-community/mathlib/commit/7fc3283)
fix(README.md): Remove the AppVeyor badge [skip ci] ([#1192](https://github.com/leanprover-community/mathlib/pull/1192))
It seems to me that we don't really care about whether the AppVeyor build fails or not. And I don't like the red badge. So I propose to remove it.
#### Estimated changes
Modified README.md




## [2019-07-09 00:20:18+02:00](https://github.com/leanprover-community/mathlib/commit/0cc67a1)
chore(data/matrix): remove unnecessary decidable_eq ([#1196](https://github.com/leanprover-community/mathlib/pull/1196))
This was generating annoying `decidable_eq (fin n)` goals when rewriting.
#### Estimated changes
Modified src/data/matrix.lean




## [2019-07-07 20:48:20](https://github.com/leanprover-community/mathlib/commit/8917419)
chore(data/equiv/algebra): use `to_additive` ([#1191](https://github.com/leanprover-community/mathlib/pull/1191))
- Define `add_equiv` and `add_equiv.*` using `to_additive`
- Simplify some instances
#### Estimated changes
Modified src/data/equiv/algebra.lean
- \- *def* add_equiv.refl
- \- *def* add_equiv.symm
- \- *def* add_equiv.trans
- \- *lemma* mul_equiv.one



## [2019-07-06 22:30:41](https://github.com/leanprover-community/mathlib/commit/55b0b80)
fix(src/logic/basic): add [symm] attribute to ne. ([#1190](https://github.com/leanprover-community/mathlib/pull/1190))
#### Estimated changes
Modified src/logic/basic.lean




## [2019-07-06 11:29:31](https://github.com/leanprover-community/mathlib/commit/ccf5636)
feat(data/option/basic): not_is_some_iff_eq_none and ne_none_iff_is_some ([#1186](https://github.com/leanprover-community/mathlib/pull/1186))
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* option.ne_none_iff_is_some
- \+ *lemma* option.not_is_some_iff_eq_none



## [2019-07-05 20:30:47](https://github.com/leanprover-community/mathlib/commit/12763b9)
chore(algebra/group/type_tags): add some missing instances ([#1164](https://github.com/leanprover-community/mathlib/pull/1164))
* chore(algebra/group/type_tags): add some missing instances
* Drop an unused import
#### Estimated changes
Modified src/algebra/group/type_tags.lean




## [2019-07-05 17:03:44](https://github.com/leanprover-community/mathlib/commit/05283d2)
fix(category_theory/limits): make is_limit a class, clean up proofs ([#1187](https://github.com/leanprover-community/mathlib/pull/1187))
* feat(category_theory/limits): equivalences create limits
* equivalence lemma
* add @[simp]
* use right_adjoint_preserves_limits
* blech
* undo weird changes in topology files
* formatting
* do colimits too
* working!
* ?
#### Estimated changes
Modified src/algebra/CommRing/colimits.lean


Modified src/algebra/Mon/colimits.lean


Modified src/category_theory/adjunction/basic.lean
- \- *structure* category_theory.adjunction.is_left_adjoint
- \- *structure* category_theory.adjunction.is_right_adjoint

Modified src/category_theory/adjunction/limits.lean
- \- *def* category_theory.adjunction.is_colimit_map_cocone
- \- *def* category_theory.adjunction.is_limit_map_cone

Modified src/category_theory/limits/limits.lean
- \- *def* category_theory.limits.colimit.is_colimit
- \- *def* category_theory.limits.limit.is_limit

Modified src/category_theory/limits/preserves.lean




## [2019-07-05 15:44:22](https://github.com/leanprover-community/mathlib/commit/05550ea)
feat(category_theory/limits): equivalences create limits ([#1175](https://github.com/leanprover-community/mathlib/pull/1175))
* feat(category_theory/limits): equivalences create limits
* equivalence lemma
* add @[simp]
* use right_adjoint_preserves_limits
* undo weird changes in topology files
* formatting
* do colimits too
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean
- \- *def* category_theory.adjunction.equivalence.to_adjunction
- \+ *def* category_theory.equivalence.to_adjunction
- \+ *def* category_theory.functor.adjunction

Modified src/category_theory/adjunction/limits.lean
- \+ *def* category_theory.adjunction.has_colimit_of_comp_equivalence
- \+ *def* category_theory.adjunction.has_limit_of_comp_equivalence
- \+ *def* category_theory.adjunction.is_colimit_map_cocone
- \+ *def* category_theory.adjunction.is_limit_map_cone
- \- *def* category_theory.adjunction.left_adjoint_preserves_colimits
- \- *def* category_theory.adjunction.right_adjoint_preserves_limits

Modified src/category_theory/equivalence.lean
- \+/\- *lemma* category_theory.equivalence.counit_inv_functor_comp
- \+/\- *lemma* category_theory.equivalence.functor_unit_comp
- \+/\- *lemma* category_theory.equivalence.inverse_counit_inv_comp
- \+/\- *lemma* category_theory.equivalence.unit_inverse_comp
- \+ *lemma* category_theory.is_equivalence.counit_inv_functor_comp
- \+ *lemma* category_theory.is_equivalence.functor_unit_comp

Modified src/category_theory/limits/cones.lean
- \+ *lemma* category_theory.functor.map_cocone_X
- \+ *lemma* category_theory.functor.map_cone_X
- \+ *def* category_theory.functor.map_cone_inv
- \+ *lemma* category_theory.functor.map_cone_inv_X

Modified src/category_theory/limits/limits.lean




## [2019-07-05 05:31:07](https://github.com/leanprover-community/mathlib/commit/27ae77c)
feat(tactic/tidy): lower the priority of ext in tidy ([#1178](https://github.com/leanprover-community/mathlib/pull/1178))
* feat(category_theory/adjunction): additional simp lemmas
* experimenting with deferring ext in tidy
* abbreviate some proofs
* refactoring CommRing/adjunctions
* renaming
#### Estimated changes
Modified src/algebra/CommRing/adjunctions.lean
- \+ *def* CommRing.adj
- \+ *def* CommRing.free
- \+ *lemma* CommRing.free_map_val
- \+ *lemma* CommRing.free_obj_α
- \+ *def* CommRing.hom_equiv
- \- *lemma* CommRing.polynomial_ring_map_val
- \- *lemma* CommRing.polynomial_ring_obj_α

Modified src/category_theory/adjunction/limits.lean


Modified src/tactic/tidy.lean




## [2019-07-05 05:02:40](https://github.com/leanprover-community/mathlib/commit/4af3976)
chore(category_theory): cleanup ([#1173](https://github.com/leanprover-community/mathlib/pull/1173))
* chore(category_theory): cleanup
* oops
* remove comment
* more uniform?
* fix stalks proof?
* Update src/algebra/CommRing/basic.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Apply suggestions from code review
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/algebra/CommRing/basic.lean
- \- *lemma* CommRing.comp_val
- \- *lemma* CommRing.id_val
- \+ *abbreviation* CommRing.is_comm_ring_hom
- \- *def* CommRing.is_comm_ring_hom

Modified src/algebra/CommRing/colimits.lean
- \+/\- *lemma* CommRing.colimits.cocone_naturality_components

Modified src/algebra/Mon/colimits.lean
- \+/\- *lemma* Mon.colimits.cocone_naturality_components

Modified src/category_theory/concrete_category.lean
- \+ *lemma* category_theory.bundled.coe_comp

Modified src/category_theory/isomorphism.lean
- \+ *lemma* category_theory.functor.map_inv

Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/opposites.lean
- \+ *def* category_theory.is_iso_of_op

Modified src/category_theory/whiskering.lean


Modified src/topology/Top/stalks.lean


Modified src/topology/algebra/TopCommRing/basic.lean
- \+/\- *def* TopCommRing.forget



## [2019-07-04 19:49:02](https://github.com/leanprover-community/mathlib/commit/569bcf9)
feat(algebra/ordered_group): eq_of_abs_non_pos ([#1185](https://github.com/leanprover-community/mathlib/pull/1185))
* feat(algebra/ordered_group): decidable_linear_ordered_comm_group.eq_of_abs_non_pos
* fix(algebra/ordered_group): new line and name
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* decidable_linear_ordered_comm_group.eq_of_abs_sub_nonpos



## [2019-07-04 18:17:29](https://github.com/leanprover-community/mathlib/commit/c5d4140)
feat(data/fin): fin.mk.inj_iff ([#1182](https://github.com/leanprover-community/mathlib/pull/1182))
Quite surprised this insn't already there.
#### Estimated changes
Modified src/data/fin.lean




## [2019-07-04 16:47:39](https://github.com/leanprover-community/mathlib/commit/1723bee)
chore(algebra/order_functions): some proofs work for semirings ([#1183](https://github.com/leanprover-community/mathlib/pull/1183))
* chore(algebra/order_functions): some proofs work for semirings, not only rings
* Update order_functions.lean
#### Estimated changes
Modified src/algebra/order_functions.lean




## [2019-07-04 14:31:11](https://github.com/leanprover-community/mathlib/commit/0818bb2)
feat(data/fin): mem_find_of_unique ([#1181](https://github.com/leanprover-community/mathlib/pull/1181))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.mem_find_of_unique



## [2019-07-04 12:14:42](https://github.com/leanprover-community/mathlib/commit/32ce121)
chore(topology/maps.lean): Delete a redundant argument ([#1179](https://github.com/leanprover-community/mathlib/pull/1179))
* Create .DS_Store
* Revert "Create .DS_Store"
This reverts commit 5612886d493aef59205eddc5a34a75e6e5ba22c1.
* Redundant argument
#### Estimated changes
Modified src/topology/maps.lean




## [2019-07-04 10:24:53](https://github.com/leanprover-community/mathlib/commit/34d69b5)
chore(data/set): set.mem_preimage_eq becomes an iff  ([#1174](https://github.com/leanprover-community/mathlib/pull/1174))
* chore(data/set): set.mem_preimage_eq becomes an iff named set.mem_preimage
* fix(measure_theory/measurable_space): proof broken by mem_preimage
change
* fix(data/filter/basic)
* fix(topology/uniform_space/separation)
* fix(measure_theory/integration)
#### Estimated changes
Modified src/data/pfun.lean


Modified src/data/set/basic.lean
- \+ *theorem* set.mem_preimage
- \- *theorem* set.mem_preimage_eq

Modified src/data/set/finite.lean


Modified src/data/set/function.lean


Modified src/linear_algebra/basis.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/simple_func_dense.lean


Modified src/order/filter/basic.lean


Modified src/set_theory/cofinality.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/maps.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/order.lean


Modified src/topology/uniform_space/separation.lean




## [2019-07-04 08:45:49](https://github.com/leanprover-community/mathlib/commit/6493bb6)
feat(data/list/basic): nodup_update_nth, mem_diff_iff_of_nodup ([#1170](https://github.com/leanprover-community/mathlib/pull/1170))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.diff_eq_filter_of_nodup
- \+ *lemma* list.mem_diff_iff_of_nodup
- \+ *lemma* list.mem_or_eq_of_mem_update_nth
- \+ *lemma* list.nodup_update_nth



## [2019-07-04 06:57:24](https://github.com/leanprover-community/mathlib/commit/00de1cb)
feat(data/list/basic): list.nodup_diff ([#1168](https://github.com/leanprover-community/mathlib/pull/1168))
* feat(data/list/basic): list.nodup_diff
* Update basic.lean
* Update basic.lean
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.nodup_diff



## [2019-07-04 05:16:33](https://github.com/leanprover-community/mathlib/commit/e6b9696)
feat(data/option): not_mem_none and bind_assoc ([#1177](https://github.com/leanprover-community/mathlib/pull/1177))
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* option.bind_assoc
- \+ *lemma* option.not_mem_none



## [2019-07-04 03:33:42](https://github.com/leanprover-community/mathlib/commit/4cca114)
feat(data/fin): fin.find ([#1167](https://github.com/leanprover-community/mathlib/pull/1167))
* feat(data/fin): fin.find
* add nat_find_mem_find
#### Estimated changes
Modified src/data/fin.lean
- \+ *def* fin.find
- \+ *lemma* fin.find_eq_none_iff
- \+ *lemma* fin.find_min'
- \+ *lemma* fin.find_min
- \+ *lemma* fin.find_spec
- \+ *lemma* fin.is_some_find_iff
- \+ *lemma* fin.nat_find_mem_find



## [2019-07-04 01:39:56](https://github.com/leanprover-community/mathlib/commit/3ee1f85)
feat(order/basic): order_dual.inhabited ([#1163](https://github.com/leanprover-community/mathlib/pull/1163))
#### Estimated changes
Modified src/order/basic.lean




## [2019-07-03 23:52:50](https://github.com/leanprover-community/mathlib/commit/ae9615c)
feat(order/pilex): lexicographic ordering on pi types ([#1157](https://github.com/leanprover-community/mathlib/pull/1157))
* feat(order/pilex): lexicographic ordering on pi types
* fix instance name
* fix instance name properly
* Update basic.lean
* remove unnecessary import
#### Estimated changes
Modified src/order/basic.lean


Added src/order/pilex.lean
- \+ *def* pi.lex
- \+ *def* pilex



## [2019-07-03 22:09:24](https://github.com/leanprover-community/mathlib/commit/992354c)
feat(data/fintype): well_foundedness lemmas on fintypes ([#1156](https://github.com/leanprover-community/mathlib/pull/1156))
* feat(data/fintype): well_foundedness lemmas on fintypes
* Update fintype.lean
* minor fixes
#### Estimated changes
Modified src/data/fintype.lean
- \+ *lemma* fintype.linear_order.is_well_order
- \+ *lemma* fintype.preorder.well_founded
- \+ *lemma* fintype.well_founded_of_trans_of_irrefl



## [2019-07-03 18:10:52](https://github.com/leanprover-community/mathlib/commit/cb84234)
feat(category_theory/yoneda): coyoneda lemmas ([#1172](https://github.com/leanprover-community/mathlib/pull/1172))
* feat(category_theory/yoneda): coyoneda lemmas
* oops, didn't include everything I needed
* oops
* removing fully_faithful
* missing underscore...
#### Estimated changes
Modified src/category_theory/equivalence.lean


Modified src/category_theory/full_subcategory.lean


Modified src/category_theory/fully_faithful.lean
- \+ *def* category_theory.is_iso_of_fully_faithful
- \+ *lemma* category_theory.preimage_comp
- \+/\- *lemma* category_theory.preimage_id
- \+ *lemma* category_theory.preimage_map

Modified src/category_theory/types.lean


Modified src/category_theory/yoneda.lean
- \+ *def* category_theory.coyoneda.is_iso
- \+ *lemma* category_theory.coyoneda.naturality
- \+ *def* category_theory.yoneda.is_iso



## [2019-07-03 15:25:41](https://github.com/leanprover-community/mathlib/commit/e4ee18b)
feat(category_theory/adjunction): additional simp lemmas ([#1143](https://github.com/leanprover-community/mathlib/pull/1143))
* feat(category_theory/adjunction): additional simp lemmas
* spaces
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean
- \+ *lemma* category_theory.adjunction.counit_naturality
- \+ *lemma* category_theory.adjunction.counit_naturality_assoc
- \+ *lemma* category_theory.adjunction.left_triangle_components_assoc
- \+ *lemma* category_theory.adjunction.right_triangle_components_assoc
- \+ *lemma* category_theory.adjunction.unit_naturality
- \+ *lemma* category_theory.adjunction.unit_naturality_assoc



## [2019-07-03 12:44:32](https://github.com/leanprover-community/mathlib/commit/f1b5473)
feat(data/list/basic): fin_range ([#1159](https://github.com/leanprover-community/mathlib/pull/1159))
* feat(data/list/basic): fin_range
fin_range is like `list.range` but returns a `list (fin n)` instead of a `list nat`
* Update basic.lean
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *def* list.fin_range
- \+ *lemma* list.length_fin_range
- \+ *lemma* list.mem_fin_range
- \+ *lemma* list.nodup_fin_range



## [2019-07-03 09:42:00](https://github.com/leanprover-community/mathlib/commit/d2c5309)
refactor(linear_algebra/lc): use families not sets ([#943](https://github.com/leanprover-community/mathlib/pull/943))
* refactor(linear_algebra/lc): use families not sets
* refactor(linear_algebra/lc): merge lc into finsupp
* refactor(linear_algebra/lc): localize decidability
* refactor(linear_algebra/lc): finsupp instances
* refactor(linear_algebra/lc): use families instead of sets
* refactor(linear_algebra/lc): remove set argument in lin_indep
* refactor(linear_algebra/lc): clean up
* refactor(linear_algebra/lc): more clean up
* refactor(linear_algebra/lc): set_option in section
* refactor(linear_algebra/lc): decidability proof
* refactor(linear_algebra/lc): arrow precedence
* refactor(linear_algebra/lc): more cleanup
* refactor(linear_algebra/lc): move finset.preimage
* refactor(linear_algebra/lc): use families not sets
* refactor(linear_algebra/lc): merge lc into finsupp
* refactor(linear_algebra/lc): localize decidability
* refactor(linear_algebra/lc): finsupp instances
* refactor(linear_algebra/lc): use families instead of sets
* refactor(linear_algebra/lc): remove set argument in lin_indep
* refactor(linear_algebra/lc): clean up
* refactor(linear_algebra/lc): more clean up
* refactor(linear_algebra/lc): set_option in section
* refactor(linear_algebra/lc): decidability proof
* refactor(linear_algebra/lc): arrow precedence
* refactor(linear_algebra/lc): more cleanup
* refactor(linear_algebra/lc): move finset.preimage
* tidying up. Remove unnecessary dec_eq from dim. Shorten finset.preimage.
* fix build
* make travis rebuild
*  fix build
* shorten finsupp proofs
* shorten more proofs
* shorten more proofs
* speed up dim_bot
* fix build
* shorten dimension proof
#### Estimated changes
Modified src/algebra/direct_limit.lean


Modified src/algebra/module.lean
- \+ *lemma* semimodule.eq_zero_of_zero_eq_one
- \+ *lemma* submodule.subtype_eq_val

Modified src/data/finset.lean
- \+ *theorem* finset.exists_mem_iff_ne_empty

Modified src/data/finsupp.lean
- \+ *lemma* finsupp.comap_domain_apply
- \+ *lemma* finsupp.emb_domain_inj
- \+ *lemma* finsupp.eq_zero_of_comap_domain_eq_zero
- \+ *lemma* finsupp.map_domain_comap_domain
- \+ *lemma* finsupp.mem_split_support_iff_nonzero
- \+ *lemma* finsupp.sigma_sum
- \+ *lemma* finsupp.sigma_support
- \+ *lemma* finsupp.single_of_emb_domain_single
- \+ *lemma* finsupp.single_swap
- \+ *lemma* finsupp.split_apply
- \+ *def* finsupp.split_support
- \+ *lemma* finsupp.sum_comap_domain
- \- *def* finsupp.to_comm_ring
- \- *def* finsupp.to_comm_semiring
- \- *def* finsupp.to_has_scalar'
- \- *def* finsupp.to_has_scalar
- \- *def* finsupp.to_module
- \- *def* finsupp.to_ring
- \- *def* finsupp.to_semimodule
- \- *def* finsupp.to_semiring
- \+ *lemma* finsupp.unique_single

Modified src/data/mv_polynomial.lean


Modified src/data/polynomial.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.range_comp_subset_range
- \+ *lemma* set.sum.elim_range

Modified src/data/set/finite.lean
- \+ *lemma* finset.coe_preimage
- \+ *lemma* finset.image_preimage
- \+ *lemma* finset.mem_preimage
- \+ *lemma* finset.prod_preimage
- \+/\- *theorem* set.finite_of_finite_image

Modified src/data/set/function.lean
- \+ *lemma* set.inj_on_of_injective

Modified src/data/sum.lean
- \+ *lemma* sum.elim_injective
- \+ *lemma* sum.elim_inl
- \+ *lemma* sum.elim_inr

Modified src/field_theory/finite_card.lean


Modified src/field_theory/mv_polynomial.lean
- \+ *lemma* mv_polynomial.dim_mv_polynomial
- \+ *lemma* mv_polynomial.is_basis_monomials
- \+ *lemma* mv_polynomial.map_range_eq_map
- \+ *lemma* mv_polynomial.mem_restrict_degree
- \+ *lemma* mv_polynomial.mem_restrict_degree_iff_sup
- \+ *lemma* mv_polynomial.mem_restrict_total_degree
- \+ *def* mv_polynomial.restrict_degree
- \+ *def* mv_polynomial.restrict_total_degree

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.disjoint_inl_inr
- \+ *lemma* linear_map.map_le_range
- \+ *lemma* linear_map.sup_range_inl_inr
- \+ *lemma* submodule.eq_bot_of_zero_eq_one
- \+ *lemma* submodule.linear_eq_on

Modified src/linear_algebra/basis.lean
- \+/\- *lemma* constr_add
- \+/\- *lemma* constr_basis
- \- *lemma* constr_congr
- \+/\- *lemma* constr_eq
- \+/\- *lemma* constr_neg
- \+/\- *lemma* constr_range
- \+/\- *lemma* constr_self
- \+/\- *lemma* constr_smul
- \+/\- *lemma* constr_sub
- \+/\- *lemma* constr_zero
- \- *lemma* eq_of_linear_independent_of_span
- \+ *lemma* eq_of_linear_independent_of_span_subtype
- \+/\- *def* equiv_of_is_basis
- \+/\- *lemma* exists_is_basis
- \+/\- *lemma* exists_linear_independent
- \+/\- *lemma* exists_subset_is_basis
- \+ *lemma* is_basis.comp
- \+/\- *def* is_basis.constr
- \+/\- *theorem* is_basis.constr_apply
- \+/\- *lemma* is_basis.ext
- \+ *lemma* is_basis.injective
- \+/\- *lemma* is_basis.mem_span
- \+/\- *def* is_basis.repr
- \+/\- *lemma* is_basis.repr_eq_single
- \+/\- *lemma* is_basis.repr_ker
- \+/\- *lemma* is_basis.repr_range
- \- *lemma* is_basis.repr_supported
- \+/\- *lemma* is_basis.repr_total
- \+/\- *lemma* is_basis.total_comp_repr
- \+/\- *lemma* is_basis.total_repr
- \+/\- *def* is_basis
- \+/\- *lemma* is_basis_empty
- \+/\- *lemma* is_basis_empty_bot
- \- *lemma* is_basis_injective
- \+/\- *lemma* is_basis_inl_union_inr
- \+/\- *lemma* is_basis_singleton_one
- \+/\- *lemma* is_basis_span
- \+/\- *lemma* linear_equiv.is_basis
- \+ *lemma* linear_independent.comp
- \- *lemma* linear_independent.disjoint_ker
- \+/\- *lemma* linear_independent.image
- \+ *lemma* linear_independent.image_subtype
- \- *lemma* linear_independent.inj_span_iff_inj
- \+ *lemma* linear_independent.injective
- \+/\- *lemma* linear_independent.insert
- \+/\- *lemma* linear_independent.mono
- \- *lemma* linear_independent.of_image
- \+ *lemma* linear_independent.of_subtype_range
- \+/\- *def* linear_independent.repr
- \+/\- *lemma* linear_independent.repr_eq
- \- *lemma* linear_independent.repr_eq_repr_of_subset
- \+/\- *lemma* linear_independent.repr_eq_single
- \+/\- *lemma* linear_independent.repr_ker
- \+/\- *lemma* linear_independent.repr_range
- \- *lemma* linear_independent.repr_supported
- \+ *lemma* linear_independent.restrict_of_comp_subtype
- \- *lemma* linear_independent.supported_disjoint_ker
- \+ *lemma* linear_independent.to_subtype_range
- \+/\- *lemma* linear_independent.total_comp_repr
- \+/\- *def* linear_independent.total_equiv
- \+/\- *lemma* linear_independent.total_repr
- \+/\- *lemma* linear_independent.unique
- \+/\- *def* linear_independent
- \+/\- *lemma* linear_independent_Union_finite
- \+ *lemma* linear_independent_Union_finite_subtype
- \+/\- *lemma* linear_independent_Union_of_directed
- \+/\- *lemma* linear_independent_bUnion_of_directed
- \+ *theorem* linear_independent_comp_subtype
- \+ *theorem* linear_independent_comp_subtype_disjoint
- \+/\- *lemma* linear_independent_empty
- \+ *lemma* linear_independent_empty_type
- \+/\- *theorem* linear_independent_iff
- \+/\- *lemma* linear_independent_iff_not_mem_span
- \+/\- *theorem* linear_independent_iff_total_on
- \+ *lemma* linear_independent_inl_union_inr'
- \+/\- *lemma* linear_independent_of_finite
- \+ *lemma* linear_independent_of_zero_eq_one
- \+/\- *lemma* linear_independent_singleton
- \+ *lemma* linear_independent_span
- \+ *theorem* linear_independent_subtype
- \+ *theorem* linear_independent_subtype_disjoint
- \+ *lemma* linear_independent_unique
- \- *lemma* linear_map.linear_independent_image_iff
- \+ *def* module_equiv_finsupp
- \- *def* module_equiv_lc
- \+ *lemma* ne_zero_of_linear_independent
- \+/\- *lemma* pi.is_basis_fun
- \+ *lemma* pi.is_basis_fun₀
- \+/\- *lemma* pi.is_basis_std_basis
- \+/\- *lemma* pi.linear_independent_std_basis
- \+ *lemma* surjective_of_linear_independent_of_span
- \+/\- *theorem* vector_space.card_fintype'
- \+/\- *theorem* vector_space.card_fintype
- \- *lemma* zero_not_mem_of_linear_independent

Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_fun'
- \+/\- *lemma* dim_le_injective
- \+/\- *theorem* dim_quotient
- \+/\- *lemma* dim_range_of_surjective
- \+/\- *lemma* dim_span
- \+/\- *lemma* dim_span_of_finset
- \+ *lemma* dim_span_set
- \+/\- *lemma* exists_is_basis_fintype
- \+/\- *theorem* is_basis.le_span
- \+/\- *theorem* is_basis.mk_eq_dim
- \+ *theorem* is_basis.mk_range_eq_dim
- \+/\- *theorem* linear_equiv.dim_eq
- \+/\- *theorem* linear_equiv.dim_eq_lift
- \+/\- *theorem* mk_eq_mk_of_basis
- \+/\- *lemma* rank_finset_sum_le

Modified src/linear_algebra/dual.lean
- \+/\- *def* is_basis.coord_fun
- \+/\- *lemma* is_basis.coord_fun_eq_repr
- \+/\- *def* is_basis.dual_basis
- \+/\- *theorem* is_basis.dual_basis_is_basis
- \+/\- *theorem* is_basis.dual_dim_eq
- \+ *def* is_basis.eval_finsupp_at
- \- *def* is_basis.eval_lc_at
- \+/\- *lemma* is_basis.to_dual_apply
- \+/\- *lemma* is_basis.to_dual_eq_repr
- \+/\- *def* is_basis.to_dual_equiv
- \+/\- *theorem* is_basis.to_dual_range
- \+/\- *lemma* is_basis.to_dual_to_dual

Modified src/linear_algebra/finsupp.lean
- \- *lemma* cardinal_lt_omega_of_dim_lt_omega
- \- *lemma* cardinal_mk_eq_cardinal_mk_field_pow_dim
- \- *lemma* eq_bot_iff_dim_eq_zero
- \- *lemma* equiv_of_dim_eq_dim
- \- *lemma* finsupp.dim_eq
- \- *lemma* finsupp.is_basis_single
- \+/\- *lemma* finsupp.ker_lsingle
- \+/\- *lemma* finsupp.lapply_apply
- \- *lemma* finsupp.linear_independent_single
- \+/\- *def* finsupp.lmap_domain
- \+ *theorem* finsupp.lmap_domain_apply
- \- *lemma* finsupp.lmap_domain_apply
- \+ *theorem* finsupp.lmap_domain_comp
- \+ *theorem* finsupp.lmap_domain_disjoint_ker
- \+ *theorem* finsupp.lmap_domain_id
- \+ *theorem* finsupp.lmap_domain_supported
- \+ *theorem* finsupp.lmap_domain_total
- \+/\- *lemma* finsupp.lsingle_apply
- \+ *def* finsupp.lsum
- \+ *theorem* finsupp.lsum_apply
- \- *lemma* finsupp.mem_restrict_dom
- \+ *theorem* finsupp.mem_span_iff_total
- \+ *lemma* finsupp.mem_supported'
- \+ *lemma* finsupp.mem_supported
- \+ *theorem* finsupp.range_restrict_dom
- \+ *lemma* finsupp.range_total
- \+/\- *def* finsupp.restrict_dom
- \+ *theorem* finsupp.restrict_dom_apply
- \+ *theorem* finsupp.restrict_dom_comp_subtype
- \- *def* finsupp.restrict_dom_equiv_finsupp
- \+ *lemma* finsupp.single_mem_supported
- \+ *theorem* finsupp.span_eq_map_total
- \+ *def* finsupp.supported
- \+ *theorem* finsupp.supported_Inter
- \+ *theorem* finsupp.supported_Union
- \+ *theorem* finsupp.supported_comap_lmap_domain
- \+ *theorem* finsupp.supported_empty
- \+ *lemma* finsupp.supported_eq_span_single
- \+ *def* finsupp.supported_equiv_finsupp
- \+ *theorem* finsupp.supported_mono
- \+ *theorem* finsupp.supported_union
- \+ *theorem* finsupp.supported_univ
- \+ *theorem* finsupp.total_apply
- \+ *lemma* finsupp.total_comap_domain
- \+ *theorem* finsupp.total_comp
- \+ *theorem* finsupp.total_emb_domain
- \+ *theorem* finsupp.total_map_domain
- \+ *theorem* finsupp.total_on_range
- \+ *theorem* finsupp.total_range
- \+ *theorem* finsupp.total_single
- \- *lemma* injective_of_surjective
- \- *lemma* mv_polynomial.dim_mv_polynomial
- \- *lemma* mv_polynomial.is_basis_monomials
- \- *lemma* mv_polynomial.map_range_eq_map
- \- *lemma* mv_polynomial.mem_restrict_degree
- \- *lemma* mv_polynomial.mem_restrict_degree_iff_sup
- \- *lemma* mv_polynomial.mem_restrict_total_degree
- \- *def* mv_polynomial.restrict_degree
- \- *def* mv_polynomial.restrict_total_degree

Added src/linear_algebra/finsupp_vector_space.lean
- \+ *lemma* cardinal_lt_omega_of_dim_lt_omega
- \+ *lemma* cardinal_mk_eq_cardinal_mk_field_pow_dim
- \+ *lemma* eq_bot_iff_dim_eq_zero
- \+ *lemma* equiv_of_dim_eq_dim
- \+ *lemma* finsupp.dim_eq
- \+ *lemma* finsupp.is_basis_single
- \+ *lemma* finsupp.linear_independent_single
- \+ *lemma* injective_of_surjective

Deleted src/linear_algebra/linear_combination.lean
- \- *def* lc.apply
- \- *theorem* lc.apply_apply
- \- *theorem* lc.lsum_apply
- \- *theorem* lc.map_apply
- \- *theorem* lc.map_comp
- \- *theorem* lc.map_disjoint_ker
- \- *theorem* lc.map_id
- \- *theorem* lc.map_supported
- \- *theorem* lc.map_total
- \- *theorem* lc.mem_supported'
- \- *theorem* lc.mem_supported
- \- *theorem* lc.range_restrict_dom
- \- *def* lc.restrict_dom
- \- *theorem* lc.restrict_dom_apply
- \- *theorem* lc.restrict_dom_comp_subtype
- \- *theorem* lc.single_mem_supported
- \- *def* lc.supported
- \- *theorem* lc.supported_Inter
- \- *theorem* lc.supported_Union
- \- *theorem* lc.supported_comap_map
- \- *theorem* lc.supported_empty
- \- *theorem* lc.supported_eq_span_single
- \- *theorem* lc.supported_mono
- \- *theorem* lc.supported_union
- \- *theorem* lc.supported_univ
- \- *theorem* lc.total_apply
- \- *def* lc.total_on
- \- *theorem* lc.total_on_range
- \- *theorem* lc.total_range
- \- *theorem* lc.total_single
- \- *def* lc
- \- *lemma* linear_eq_on
- \- *theorem* mem_span_iff_lc
- \- *theorem* span_eq_map_lc

Modified src/linear_algebra/matrix.lean


Modified src/logic/basic.lean
- \+ *lemma* nonempty_pempty
- \+/\- *lemma* not_nonempty_iff_imp_false

Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/noetherian.lean


Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.lift_max
- \+ *lemma* cardinal.mk_range_eq_of_inj

Modified src/topology/metric_space/closeds.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2019-07-03 09:02:02](https://github.com/leanprover-community/mathlib/commit/9a33885)
chore(data/matrix): rows and columns the right way around ([#1171](https://github.com/leanprover-community/mathlib/pull/1171))
* chore(data/matrix): rows and columns the right way around
* update matrix.lean
#### Estimated changes
Modified src/data/matrix.lean
- \+/\- *def* matrix.col
- \+/\- *def* matrix.minor
- \+/\- *def* matrix.row



## [2019-07-03 00:58:19](https://github.com/leanprover-community/mathlib/commit/fd5617c)
feat(measure_theory): Define Bochner integration ([#1149](https://github.com/leanprover-community/mathlib/pull/1149))
* Create .DS_Store
* Revert "Create .DS_Store"
This reverts commit 5612886d493aef59205eddc5a34a75e6e5ba22c1.
* Define bochner integral
* Define bochner integral
* Headings
* Change used names
* Fix styles; Get rid of redundant lemmas
* Delete dash lines
* changes
* Fix everything
Things remaining:
* extend comments in headings
* `integrable` predicate should include measurability
* better proofs for simple_func_dense.lean
* Fix everything
Things remaining:
* extend comments in headings
* `integrable` predicate should include measurability
* better proofs for simple_func_dense.lean
* Remove redundant lemma
* Fix styles
#### Estimated changes
Modified src/algebra/CommRing/colimits.lean
- \+/\- *lemma* CommRing.colimits.cocone_naturality_components

Modified src/algebra/Mon/colimits.lean
- \+/\- *lemma* Mon.colimits.cocone_naturality_components

Modified src/algebra/big_operators.lean
- \+/\- *lemma* finset.prod_map

Modified src/algebra/module.lean
- \+/\- *lemma* is_linear_map.is_linear_map_smul'
- \+/\- *lemma* is_linear_map.is_linear_map_smul

Modified src/algebra/ordered_field.lean
- \+ *lemma* nat.inv_pos_of_nat
- \+ *lemma* nat.one_div_pos_of_nat

Modified src/analysis/asymptotics.lean


Modified src/analysis/complex/exponential.lean
- \+/\- *lemma* real.mul_rpow
- \+/\- *lemma* real.rpow_le_rpow

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* real.norm_eq_abs

Modified src/category_theory/limits/cones.lean
- \+/\- *lemma* category_theory.limits.cones.postcompose_map_hom

Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* category_theory.limits.colim.ι_map_assoc
- \+/\- *lemma* category_theory.limits.colimit.hom_iso_hom
- \+/\- *lemma* category_theory.limits.colimit.ι_post_assoc
- \+/\- *lemma* category_theory.limits.colimit.ι_pre_assoc
- \+/\- *lemma* category_theory.limits.limit.hom_iso_hom

Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/pullbacks.lean


Modified src/category_theory/limits/types.lean
- \+/\- *lemma* category_theory.limits.types.types_limit_lift

Modified src/data/dfinsupp.lean


Modified src/data/fin.lean
- \+/\- *lemma* fin.cast_succ_cast_lt

Modified src/data/finset.lean
- \+/\- *theorem* finset.Ico.image_sub

Modified src/data/finsupp.lean
- \+/\- *lemma* finsupp.support_add_eq

Modified src/data/holor.lean
- \+/\- *lemma* holor.holor_index_cons_decomp
- \+/\- *lemma* holor.mul_assoc
- \+/\- *lemma* holor.slice_add

Modified src/data/lazy_list2.lean


Modified src/data/list/basic.lean
- \+/\- *theorem* list.Ico.map_sub

Modified src/data/mv_polynomial.lean
- \+/\- *lemma* mv_polynomial.monomial_add_single
- \+/\- *lemma* mv_polynomial.monomial_single_add

Modified src/data/nat/basic.lean
- \+ *lemma* nat.find_greatest_eq_zero
- \+ *lemma* nat.find_greatest_of_ne_zero
- \+/\- *lemma* nat.mul_left_eq_self_iff
- \+/\- *lemma* nat.mul_right_eq_self_iff

Modified src/data/nat/cast.lean
- \+ *lemma* nat.cast_add_one_pos

Modified src/data/polynomial.lean
- \+/\- *def* polynomial.decidable_dvd_monic
- \+/\- *lemma* polynomial.leading_coeff_comp

Modified src/data/quot.lean
- \+/\- *lemma* nonempty_quotient_iff
- \+/\- *lemma* quotient.lift_beta
- \+/\- *lemma* quotient.lift_on_beta

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.coe_nnreal_eq
- \+/\- *lemma* ennreal.le_of_forall_epsilon_le
- \+ *lemma* ennreal.le_of_real_iff_to_real_le
- \+ *lemma* ennreal.lt_of_real_iff_to_real_lt
- \+ *lemma* ennreal.mem_Iio_self_add
- \+ *lemma* ennreal.mem_Ioo_self_sub_add
- \+ *lemma* ennreal.not_mem_Ioo_self_sub
- \+ *lemma* ennreal.of_real_eq_coe_nnreal
- \+ *lemma* ennreal.of_real_le_iff_le_to_real
- \+ *lemma* ennreal.of_real_lt_iff_lt_to_real
- \+ *lemma* ennreal.of_real_mul
- \+/\- *lemma* ennreal.sub_left_inj
- \+ *lemma* ennreal.sub_self
- \+ *lemma* ennreal.to_real_of_real_mul

Modified src/data/real/hyperreal.lean
- \+/\- *theorem* hyperreal.abs_lt_real_iff_infinitesimal
- \+/\- *lemma* hyperreal.epsilon_lt_pos
- \+/\- *theorem* hyperreal.exists_st_iff_not_infinite
- \+/\- *theorem* hyperreal.exists_st_of_not_infinite
- \+/\- *theorem* hyperreal.gt_of_neg_of_infinitesimal
- \+/\- *lemma* hyperreal.infinite_iff_abs_lt_abs
- \+/\- *lemma* hyperreal.infinite_iff_infinite_abs
- \+/\- *lemma* hyperreal.infinite_iff_infinite_neg
- \+/\- *lemma* hyperreal.infinite_iff_infinite_pos_abs
- \+/\- *theorem* hyperreal.infinite_iff_infinitesimal_inv
- \+/\- *theorem* hyperreal.infinite_iff_not_exists_st
- \+/\- *lemma* hyperreal.infinite_mul_infinite
- \+/\- *lemma* hyperreal.infinite_mul_of_infinite_not_infinitesimal
- \+/\- *lemma* hyperreal.infinite_mul_of_not_infinitesimal_infinite
- \+/\- *lemma* hyperreal.infinite_neg_add_infinite_neg
- \+/\- *lemma* hyperreal.infinite_neg_add_not_infinite
- \+/\- *lemma* hyperreal.infinite_neg_add_not_infinite_pos
- \+/\- *lemma* hyperreal.infinite_neg_iff_infinite_and_neg
- \+/\- *lemma* hyperreal.infinite_neg_iff_infinite_of_neg
- \+/\- *lemma* hyperreal.infinite_neg_iff_infinite_pos_neg
- \+/\- *lemma* hyperreal.infinite_neg_iff_infinitesimal_inv_neg
- \+/\- *lemma* hyperreal.infinite_neg_mul_infinite_neg
- \+/\- *lemma* hyperreal.infinite_neg_mul_infinite_pos
- \+/\- *lemma* hyperreal.infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos
- \+/\- *lemma* hyperreal.infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg
- \+/\- *lemma* hyperreal.infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos
- \+/\- *lemma* hyperreal.infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg
- \+/\- *lemma* hyperreal.infinite_neg_neg_of_infinite_pos
- \+/\- *theorem* hyperreal.infinite_neg_of_tendsto_bot
- \+/\- *theorem* hyperreal.infinite_of_infinitesimal_inv
- \+/\- *lemma* hyperreal.infinite_omega
- \+/\- *lemma* hyperreal.infinite_pos_abs_iff_infinite_abs
- \+/\- *lemma* hyperreal.infinite_pos_add_infinite_pos
- \+/\- *lemma* hyperreal.infinite_pos_add_not_infinite
- \+/\- *lemma* hyperreal.infinite_pos_add_not_infinite_neg
- \+/\- *lemma* hyperreal.infinite_pos_iff_infinite_and_pos
- \+/\- *lemma* hyperreal.infinite_pos_iff_infinite_neg_neg
- \+/\- *lemma* hyperreal.infinite_pos_iff_infinite_of_nonneg
- \+/\- *lemma* hyperreal.infinite_pos_iff_infinite_of_pos
- \+/\- *lemma* hyperreal.infinite_pos_iff_infinitesimal_inv_pos
- \+/\- *lemma* hyperreal.infinite_pos_mul_infinite_neg
- \+/\- *lemma* hyperreal.infinite_pos_mul_infinite_pos
- \+/\- *lemma* hyperreal.infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg
- \+/\- *lemma* hyperreal.infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos
- \+/\- *lemma* hyperreal.infinite_pos_mul_of_not_infinitesimal_neg_infinite_neg
- \+/\- *lemma* hyperreal.infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos
- \+/\- *lemma* hyperreal.infinite_pos_neg_of_infinite_neg
- \+/\- *theorem* hyperreal.infinite_pos_of_tendsto_top
- \+/\- *lemma* hyperreal.infinite_pos_omega
- \+/\- *lemma* hyperreal.infinitesimal_add
- \+/\- *theorem* hyperreal.infinitesimal_def
- \+/\- *theorem* hyperreal.infinitesimal_epsilon
- \+/\- *theorem* hyperreal.infinitesimal_iff_infinite_inv
- \+/\- *theorem* hyperreal.infinitesimal_inv_of_infinite
- \+/\- *lemma* hyperreal.infinitesimal_mul
- \+/\- *lemma* hyperreal.infinitesimal_neg
- \+/\- *lemma* hyperreal.infinitesimal_neg_iff
- \+/\- *lemma* hyperreal.infinitesimal_neg_iff_infinite_neg_inv
- \+/\- *lemma* hyperreal.infinitesimal_pos_iff_infinite_pos_inv
- \+/\- *theorem* hyperreal.infinitesimal_sub_is_st
- \+/\- *theorem* hyperreal.infinitesimal_sub_st
- \+/\- *theorem* hyperreal.is_st_Sup
- \+/\- *lemma* hyperreal.is_st_add
- \+/\- *lemma* hyperreal.is_st_iff_abs_sub_lt_delta
- \+/\- *lemma* hyperreal.is_st_inj_real
- \+/\- *lemma* hyperreal.is_st_inv
- \+/\- *lemma* hyperreal.is_st_mul
- \+/\- *lemma* hyperreal.is_st_neg
- \+/\- *lemma* hyperreal.is_st_real_iff_eq
- \+/\- *lemma* hyperreal.is_st_refl_real
- \+/\- *lemma* hyperreal.is_st_st'
- \+/\- *lemma* hyperreal.is_st_st
- \+/\- *lemma* hyperreal.is_st_st_of_is_st
- \+/\- *lemma* hyperreal.is_st_symm_real
- \+/\- *lemma* hyperreal.is_st_trans_real
- \+/\- *theorem* hyperreal.lt_neg_of_pos_of_infinitesimal
- \+/\- *theorem* hyperreal.lt_of_pos_of_infinitesimal
- \+/\- *lemma* hyperreal.lt_of_st_lt
- \+/\- *lemma* hyperreal.ne_zero_of_infinite
- \+/\- *lemma* hyperreal.not_infinite_add
- \+/\- *theorem* hyperreal.not_infinite_iff_exist_lt_gt
- \+/\- *lemma* hyperreal.not_infinite_mul
- \+/\- *lemma* hyperreal.not_infinite_neg
- \+/\- *lemma* hyperreal.not_infinite_neg_add_infinite_pos
- \+/\- *lemma* hyperreal.not_infinite_neg_of_infinite_pos
- \+/\- *theorem* hyperreal.not_infinite_of_exists_st
- \+/\- *lemma* hyperreal.not_infinite_of_infinitesimal
- \+/\- *lemma* hyperreal.not_infinite_pos_add_infinite_neg
- \+/\- *lemma* hyperreal.not_infinite_pos_of_infinite_neg
- \+/\- *lemma* hyperreal.not_infinitesimal_of_infinite
- \+/\- *lemma* hyperreal.not_infinitesimal_of_infinite_neg
- \+/\- *lemma* hyperreal.not_infinitesimal_of_infinite_pos
- \+/\- *theorem* hyperreal.not_real_of_infinite
- \+/\- *lemma* hyperreal.not_real_of_infinitesimal_ne_zero
- \+/\- *lemma* hyperreal.st_add
- \+/\- *theorem* hyperreal.st_infinite
- \+/\- *lemma* hyperreal.st_inv
- \+/\- *lemma* hyperreal.st_le_of_le
- \+/\- *lemma* hyperreal.st_mul
- \+/\- *lemma* hyperreal.st_neg
- \+/\- *lemma* hyperreal.st_of_is_st
- \+/\- *lemma* hyperreal.zero_iff_infinitesimal_real

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.le_of_real_iff_coe_le
- \+ *lemma* nnreal.lt_of_real_iff_coe_lt
- \+ *lemma* nnreal.of_real_le_iff_le_coe
- \+ *lemma* nnreal.of_real_lt_iff_lt_coe
- \+ *lemma* nnreal.of_real_mul

Modified src/data/rel.lean
- \+/\- *lemma* rel.core_id
- \+/\- *def* rel

Modified src/data/set/basic.lean
- \+/\- *lemma* set.range_coe_subtype
- \+ *lemma* set.range_ite_subset'
- \+ *lemma* set.range_ite_subset

Modified src/data/set/countable.lean
- \+ *def* set.enumerate_countable
- \+ *lemma* set.subset_range_enumerate

Modified src/data/set/disjointed.lean
- \+ *lemma* set.disjoint_disjointed'
- \+ *lemma* set.disjointed_subset

Modified src/data/set/finite.lean
- \+ *lemma* set.finite_range_const
- \+ *lemma* set.finite_range_find_greatest
- \+ *lemma* set.finite_range_ite
- \+ *lemma* set.range_find_greatest_subset

Modified src/data/set/lattice.lean
- \+/\- *theorem* set.Union_subset_iff

Modified src/group_theory/subgroup.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_map_le

Modified src/logic/function.lean
- \+/\- *theorem* function.restrict_eq

Added src/measure_theory/ae_eq_fun.lean
- \+ *def* measure_theory.ae_eq_fun.comp
- \+ *def* measure_theory.ae_eq_fun.comp_edist
- \+ *lemma* measure_theory.ae_eq_fun.comp_edist_self
- \+ *def* measure_theory.ae_eq_fun.comp₂
- \+ *lemma* measure_theory.ae_eq_fun.comp₂_mk_mk
- \+ *def* measure_theory.ae_eq_fun.const
- \+ *lemma* measure_theory.ae_eq_fun.edist_eq_add_add
- \+ *lemma* measure_theory.ae_eq_fun.edist_mk_mk'
- \+ *lemma* measure_theory.ae_eq_fun.edist_mk_mk
- \+ *lemma* measure_theory.ae_eq_fun.edist_smul
- \+ *def* measure_theory.ae_eq_fun.eintegral
- \+ *lemma* measure_theory.ae_eq_fun.eintegral_add
- \+ *lemma* measure_theory.ae_eq_fun.eintegral_eq_zero_iff
- \+ *lemma* measure_theory.ae_eq_fun.eintegral_le_eintegral
- \+ *lemma* measure_theory.ae_eq_fun.eintegral_mk
- \+ *lemma* measure_theory.ae_eq_fun.eintegral_zero
- \+ *def* measure_theory.ae_eq_fun.lift_pred
- \+ *def* measure_theory.ae_eq_fun.lift_rel
- \+ *def* measure_theory.ae_eq_fun.lift_rel_mk_mk
- \+ *def* measure_theory.ae_eq_fun.mk
- \+ *lemma* measure_theory.ae_eq_fun.mk_add_mk
- \+ *lemma* measure_theory.ae_eq_fun.mk_eq_mk
- \+ *lemma* measure_theory.ae_eq_fun.mk_le_mk
- \+ *lemma* measure_theory.ae_eq_fun.neg_mk
- \+ *lemma* measure_theory.ae_eq_fun.one_def
- \+ *lemma* measure_theory.ae_eq_fun.quot_mk_eq_mk
- \+ *lemma* measure_theory.ae_eq_fun.smul_mk
- \+ *lemma* measure_theory.ae_eq_fun.zero_def
- \+ *def* measure_theory.ae_eq_fun

Added src/measure_theory/bochner_integration.lean
- \+ *def* measure_theory.integral
- \+ *def* measure_theory.l1.integral
- \+ *lemma* measure_theory.l1.simple_func.dense_embedding_of_simple_func
- \+ *lemma* measure_theory.l1.simple_func.exists_simple_func_near
- \+ *def* measure_theory.l1.simple_func.integral
- \+ *def* measure_theory.l1.simple_func.mk
- \+ *def* measure_theory.l1.simple_func.to_simple_func
- \+ *lemma* measure_theory.l1.simple_func.uniform_continuous_of_simple_func
- \+ *lemma* measure_theory.l1.simple_func.uniform_embedding_of_simple_func
- \+ *def* measure_theory.l1.simple_func

Modified src/measure_theory/borel_space.lean
- \+ *lemma* ennreal.measurable_of_real
- \+ *lemma* measure_theory.is_measurable_ball
- \+ *lemma* measure_theory.is_measurable_singleton
- \+ *lemma* measure_theory.measurable_coe_nnnorm
- \+ *lemma* measure_theory.measurable_dist'
- \+ *lemma* measure_theory.measurable_dist
- \+ *lemma* measure_theory.measurable_edist'
- \+ *lemma* measure_theory.measurable_edist
- \+ *lemma* measure_theory.measurable_nndist'
- \+ *lemma* measure_theory.measurable_nndist
- \+ *lemma* measure_theory.measurable_nnnorm'
- \+ *lemma* measure_theory.measurable_nnnorm
- \+ *lemma* measure_theory.measurable_norm'
- \+ *lemma* measure_theory.measurable_norm
- \+ *lemma* measure_theory.measurable_smul'
- \+ *lemma* measure_theory.measurable_smul
- \+ *lemma* nnreal.measurable_of_real

Modified src/measure_theory/integration.lean


Added src/measure_theory/l1_space.lean
- \+ *def* measure_theory.ae_eq_fun.integrable
- \+ *lemma* measure_theory.ae_eq_fun.integrable_add
- \+ *lemma* measure_theory.ae_eq_fun.integrable_mk
- \+ *lemma* measure_theory.ae_eq_fun.integrable_neg
- \+ *lemma* measure_theory.ae_eq_fun.integrable_smul
- \+ *lemma* measure_theory.ae_eq_fun.integrable_zero
- \+ *def* measure_theory.integrable
- \+ *lemma* measure_theory.integrable_add
- \+ *lemma* measure_theory.integrable_neg
- \+ *lemma* measure_theory.integrable_smul
- \+ *lemma* measure_theory.integrable_zero
- \+ *lemma* measure_theory.l1.add_def
- \+ *lemma* measure_theory.l1.dist_def
- \+ *def* measure_theory.l1.mk
- \+ *lemma* measure_theory.l1.norm_def
- \+ *lemma* measure_theory.l1.smul_def
- \+ *lemma* measure_theory.l1.zero_def
- \+ *def* measure_theory.l1
- \+ *lemma* measure_theory.lintegral_nnnorm_add
- \+ *lemma* measure_theory.lintegral_nnnorm_neg
- \+ *lemma* measure_theory.lintegral_nnnorm_zero

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_find_greatest
- \+ *lemma* measurable_from_nat
- \+ *lemma* measurable_to_nat

Modified src/measure_theory/measure_space.lean


Added src/measure_theory/simple_func_dense.lean
- \+ *lemma* measure_theory.simple_func_sequence_tendsto'
- \+ *lemma* measure_theory.simple_func_sequence_tendsto

Modified src/order/complete_lattice.lean


Modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* bdd_below_bot

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.mem_infi
- \+/\- *lemma* filter.mem_infi_finite
- \+/\- *lemma* filter.univ_mem_sets'

Modified src/order/filter/filter_product.lean
- \+/\- *def* filter.filter_product.of
- \+/\- *theorem* filter.filter_product.of_inj

Modified src/order/filter/lift.lean


Modified src/order/fixed_points.lean


Modified src/ring_theory/polynomial.lean
- \+/\- *theorem* polynomial.degree_le_mono

Modified src/tactic/ext.lean


Modified src/tactic/solve_by_elim.lean


Modified src/tactic/tfae.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean
- \+/\- *theorem* liminf_eq_of_tendsto
- \+/\- *theorem* limsup_eq_of_tendsto
- \+/\- *lemma* mem_of_is_glb_of_is_closed
- \+/\- *lemma* mem_of_is_lub_of_is_closed
- \+/\- *theorem* tendsto_of_liminf_eq_limsup

Modified src/topology/basic.lean
- \+ *lemma* dense_of_subset_dense

Modified src/topology/constructions.lean


Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.Icc_mem_nhds
- \+ *lemma* ennreal.is_open_Ico_zero
- \+ *lemma* ennreal.nhds_of_ne_top
- \+ *lemma* ennreal.nhds_top
- \+ *lemma* ennreal.nhds_zero

Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* nnreal.tendsto_of_real

Modified src/topology/metric_space/basic.lean
- \+ *lemma* continuous_nndist
- \+ *lemma* metric.mem_closure_range_iff
- \+ *lemma* metric.mem_closure_range_iff_nat

Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* emetric.ball_subset

Modified src/topology/order.lean


Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* uniformity_lift_le_comp

Modified src/topology/uniform_space/separation.lean
- \+/\- *lemma* uniform_space.separation_quotient.uniform_continuous_map

Modified test/ext.lean


Modified test/linarith.lean


Modified test/omega.lean


Modified test/solve_by_elim.lean


Modified test/tidy.lean
- \+/\- *def* tidy.test.tidy_test_1



## [2019-07-02 13:11:09](https://github.com/leanprover-community/mathlib/commit/1ef2c2d)
feat(data/list/basic): filter_true and filter_false ([#1169](https://github.com/leanprover-community/mathlib/pull/1169))
* feat(data/list/basic): filter_true and filter_false
* Update basic.lean
* Update basic.lean
* Update basic.lean
* Update basic.lean
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.filter_false
- \+ *lemma* list.filter_true



## [2019-07-02 11:28:23](https://github.com/leanprover-community/mathlib/commit/b4989a0)
compute the cardinality of real ([#1096](https://github.com/leanprover-community/mathlib/pull/1096))
* compute the cardinality of real
* minor improvements
* fix(data/rat/denumerable): change namespace of of_rat
* style(src/topology/algebra/infinite_sum): structure proof
#### Estimated changes
Modified src/data/equiv/denumerable.lean


Modified src/data/equiv/nat.lean
- \+ *def* equiv.pnat_equiv_nat

Modified src/data/fintype.lean
- \+ *lemma* not_nonempty_fintype

Modified src/data/rat/denumerable.lean
- \+ *lemma* cardinal.mk_rat

Added src/data/real/cardinality.lean
- \+ *def* cardinal.cantor_function
- \+ *def* cardinal.cantor_function_aux
- \+ *lemma* cardinal.cantor_function_aux_eq
- \+ *lemma* cardinal.cantor_function_aux_ff
- \+ *lemma* cardinal.cantor_function_aux_nonneg
- \+ *lemma* cardinal.cantor_function_aux_succ
- \+ *lemma* cardinal.cantor_function_aux_tt
- \+ *lemma* cardinal.cantor_function_le
- \+ *lemma* cardinal.cantor_function_succ
- \+ *lemma* cardinal.increasing_cantor_function
- \+ *lemma* cardinal.injective_cantor_function
- \+ *lemma* cardinal.mk_real
- \+ *lemma* cardinal.not_countable_real
- \+ *lemma* cardinal.summable_cantor_function

Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.denumerable_iff
- \+ *theorem* cardinal.infinite_iff
- \+ *lemma* cardinal.mk_int
- \+ *lemma* cardinal.mk_nat
- \+ *lemma* cardinal.mk_pnat
- \+/\- *theorem* cardinal.mul_def

Modified src/set_theory/ordinal.lean
- \+ *lemma* cardinal.power_self_eq

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* tsum_eq_zero_add



## [2019-07-02 04:29:06](https://github.com/leanprover-community/mathlib/commit/57b57b3)
feat(data/equiv/basic): improve arrow_congr, define conj ([#1119](https://github.com/leanprover-community/mathlib/pull/1119))
* feat(data/equiv/basic): improve arrow_congr, define conj
- redefine `equiv.arrow_congr` without an enclosing `match`
- prove some trivial lemmas about `equiv.arrow_congr`
- define `equiv.conj`, and prove trivial lemmas about it
* chore(data/equiv/basic): add @[simp]
Also split some long lines, and swap lhs with rhs in a few lemmas.
* Reorder, drop TODO
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.arrow_congr
- \+ *lemma* equiv.arrow_congr_apply
- \+ *lemma* equiv.arrow_congr_comp
- \+ *lemma* equiv.arrow_congr_refl
- \+ *lemma* equiv.arrow_congr_symm
- \+ *lemma* equiv.arrow_congr_trans
- \+ *def* equiv.conj
- \+ *lemma* equiv.conj_apply
- \+ *lemma* equiv.conj_comp
- \+ *lemma* equiv.conj_refl
- \+ *lemma* equiv.conj_symm
- \+ *lemma* equiv.conj_trans



## [2019-07-01 19:35:44](https://github.com/leanprover-community/mathlib/commit/a2c291d)
feat(data/mv_polynomial): miscellaneous lemmas on eval, rename, etc ([#1134](https://github.com/leanprover-community/mathlib/pull/1134))
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *lemma* mv_polynomial.C_eq_coe_nat
- \+ *lemma* mv_polynomial.C_pow
- \+/\- *lemma* mv_polynomial.coeff_X
- \+ *lemma* mv_polynomial.eval_rename_prodmk
- \+ *lemma* mv_polynomial.eval₂_assoc
- \+ *lemma* mv_polynomial.eval₂_congr
- \+/\- *lemma* mv_polynomial.eval₂_eta
- \+/\- *lemma* mv_polynomial.eval₂_mul
- \+/\- *lemma* mv_polynomial.eval₂_pow
- \+ *lemma* mv_polynomial.eval₂_prod
- \+ *lemma* mv_polynomial.eval₂_rename
- \+ *lemma* mv_polynomial.eval₂_rename_prodmk
- \+ *lemma* mv_polynomial.eval₂_sum
- \+ *lemma* mv_polynomial.ext_iff
- \+ *lemma* mv_polynomial.map_injective
- \+ *lemma* mv_polynomial.map_pow
- \+ *lemma* mv_polynomial.rename_eval₂
- \+ *lemma* mv_polynomial.rename_prodmk_eval₂



## [2019-07-01 17:57:38](https://github.com/leanprover-community/mathlib/commit/fcfa2a4)
refactor(set_theory/ordinal): restate well_ordering_thm ([#1115](https://github.com/leanprover-community/mathlib/pull/1115))
Define the relation rather than using an `exists` statement
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+ *def* well_ordering_rel
- \- *theorem* well_ordering_thm



## [2019-07-01 17:01:12](https://github.com/leanprover-community/mathlib/commit/f0bf43b)
feat(order/zorn): chain.image ([#1084](https://github.com/leanprover-community/mathlib/pull/1084))
* feat(order/zorn): chain.image
* golf
#### Estimated changes
Modified src/order/zorn.lean
- \+ *theorem* zorn.chain.image

