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
- \+/\- *lemma* units.mk0_inj
- \+/\- *lemma* div_mul_div_cancel
- \- *lemma* field.div_mul_div_cancel

Modified src/algebra/ordered_field.lean
- \+/\- *lemma* inv_pos_of_nat
- \+/\- *lemma* one_div_pos_of_nat

Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_integers.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean
- \+/\- *lemma* coe_inj

Modified src/data/real/cau_seq.lean
- \+/\- *def* of_eq

Modified src/topology/instances/complex.lean


Modified src/topology/instances/real.lean




## [2019-07-31 14:37:08](https://github.com/leanprover-community/mathlib/commit/88d60dc)
feat(data/pnat/basic): coe_bit0 and coe_bit1 ([#1288](https://github.com/leanprover-community/mathlib/pull/1288))
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *lemma* coe_bit0
- \+ *lemma* coe_bit1



## [2019-07-31 13:28:58](https://github.com/leanprover-community/mathlib/commit/53680f9)
feat(data/matrix): mul_sum and sum_mul ([#1253](https://github.com/leanprover-community/mathlib/pull/1253))
* feat(data/matrix): mul_sum and sum_mul
* Update matrix.lean
* add comment explaing funny proof
#### Estimated changes
Modified src/data/matrix.lean
- \+ *lemma* is_add_monoid_hom_mul_left
- \+ *def* is_add_monoid_hom_mul_right



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
- \+ *theorem* to_equiv_symm
- \+ *def* map_mul
- \+/\- *def* trans
- \+ *def* apply_symm_apply
- \+ *def* symm_apply_apply
- \+ *def* map_one
- \+ *def* to_monoid_hom
- \+ *def* map_add
- \+ *def* refl
- \+ *def* symm
- \+ *def* map_zero
- \+ *def* to_add_monoid_hom

Modified src/data/mv_polynomial.lean


Modified src/linear_algebra/basic.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/noetherian.lean




## [2019-07-30 11:45:46](https://github.com/leanprover-community/mathlib/commit/9d589d7)
feat(data/nat/fib): add Fibonacci sequence ([#1279](https://github.com/leanprover-community/mathlib/pull/1279))
#### Estimated changes
Created src/data/nat/fib.lean
- \+ *lemma* fib_zero
- \+ *lemma* fib_one
- \+ *lemma* fib_succ_succ
- \+ *lemma* fib_pos
- \+ *lemma* fib_le_fib_succ
- \+ *lemma* fib_mono
- \+ *lemma* le_fib_self
- \+ *def* fib



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
- \+ *theorem* ilast'_mem
- \- *theorem* last'_mem

Modified src/data/list/defs.lean
- \+ *def* ilast'
- \+/\- *def* last'

Modified src/data/string/defs.lean
- \+ *def* is_prefix_of
- \+ *def* is_suffix_of

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
- \+ *def* Rel
- \- *def* rel

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
- \+ *lemma* map_one
- \+ *lemma* map_mul
- \+ *theorem* map_inv
- \+ *theorem* map_div
- \+ *theorem* map_neg
- \+ *theorem* map_sub
- \+ *def* ext
- \+ *def* id
- \+ *def* comp
- \+ *def* mk'
- \+ *def* map_zero
- \+ *def* map_add
- \+ *def* neg



## [2019-07-28 10:35:05](https://github.com/leanprover-community/mathlib/commit/879da1c)
fix(algebraic_geometry/presheafedspace): fix lame proofs ([#1273](https://github.com/leanprover-community/mathlib/pull/1273))
* fix(algebraic_geometry/presheafedspace): fix lame proofs
* fix
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean
- \- *lemma* comp_c

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


Created docs/contribute/doc.md
- \+ *def* padic_norm
- \+ *def* padic_val_rat

Created docs/references.bib


Modified docs/theories/topological_spaces.md


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/data/padics/padic_norm.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/ordinal.lean


Modified src/tactic/basic.lean


Created src/tactic/doc_blame.lean
- \+ *def* name.is_not_auto

Modified src/topology/basic.lean




## [2019-07-24 15:32:15](https://github.com/leanprover-community/mathlib/commit/5125f11)
feat(data/matrix): smul_val ([#1262](https://github.com/leanprover-community/mathlib/pull/1262))
* feat(data/matrix): smul_val
* Update src/data/matrix.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/data/matrix.lean
- \+ *lemma* smul_val



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


Created src/category_theory/monad/types.lean


Modified src/category_theory/types.lean
- \+ *lemma* of_type_functor_obj
- \+ *lemma* of_type_functor_map
- \+ *def* of_type_functor



## [2019-07-24 05:14:48](https://github.com/leanprover-community/mathlib/commit/b0c5251)
cleanup(category_theory/monoidal): use equiv on prod/punit intead of adding new constants ([#1257](https://github.com/leanprover-community/mathlib/pull/1257))
#### Estimated changes
Modified src/category_theory/monoidal/types.lean
- \- *def* types_left_unitor
- \- *def* types_left_unitor_inv
- \- *def* types_right_unitor
- \- *def* types_right_unitor_inv
- \- *def* types_associator
- \- *def* types_associator_inv
- \- *def* types_braiding
- \- *def* types_braiding_inv



## [2019-07-23 11:10:07](https://github.com/leanprover-community/mathlib/commit/4a5529a)
feat(data/array): add some simp attributes ([#1255](https://github.com/leanprover-community/mathlib/pull/1255))
#### Estimated changes
Modified src/data/array/lemmas.lean
- \+/\- *theorem* read_foreach
- \+/\- *theorem* read_map₂



## [2019-07-22 19:45:42](https://github.com/leanprover-community/mathlib/commit/a33315d)
feat(linear_algebra/dim): findim equivalence ([#1217](https://github.com/leanprover-community/mathlib/pull/1217))
* feat(linear_algebra/dim): findim equivalence
* feat(linear_algebra/dim): two versions of dim_fun
* feat(linear_algebra/dim): clean up
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_fun
- \+ *lemma* dim_fun_eq_lift_mul
- \+ *lemma* dim_fin_fun

Modified src/linear_algebra/finsupp_vector_space.lean
- \+ *lemma* equiv_of_dim_eq_lift_dim
- \+ *lemma* fin_dim_vectorspace_equiv
- \+/\- *lemma* eq_bot_iff_dim_eq_zero
- \+/\- *lemma* injective_of_surjective
- \- *lemma* equiv_of_dim_eq_dim
- \+ *def* equiv_of_dim_eq_dim

Modified src/set_theory/cardinal.lean
- \+ *theorem* mk_prod
- \+ *theorem* sum_const_eq_lift_mul



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

Created src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional_iff_dim_lt_omega
- \+ *lemma* dim_lt_omega
- \+ *lemma* of_fg
- \+ *lemma* exists_is_basis_finite
- \+ *lemma* findim_eq_dim
- \+ *lemma* card_eq_findim
- \+ *lemma* eq_top_of_findim_eq
- \+ *lemma* surjective_of_injective
- \+ *lemma* injective_iff_surjective
- \+ *lemma* ker_eq_bot_iff_range_eq_top
- \+ *lemma* mul_eq_one_of_mul_eq_one
- \+ *lemma* mul_eq_one_comm
- \+ *def* finite_dimensional

Modified src/ring_theory/noetherian.lean
- \+/\- *lemma* well_founded_submodule_gt
- \+ *lemma* finite_of_linear_independent

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
- \+ *lemma* single_right_inj
- \+ *lemma* single_eq_zero
- \+ *lemma* unique_single_eq_iff
- \+ *lemma* le_iff
- \+ *lemma* to_multiset_strict_mono
- \+ *lemma* sum_id_lt_of_lt
- \+ *def* lt_wf

Modified src/ring_theory/ideals.lean


Created src/ring_theory/power_series.lean
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* coeff_monomial
- \+ *lemma* coeff_monomial'
- \+ *lemma* coeff_C
- \+ *lemma* coeff_C_zero
- \+ *lemma* monomial_zero
- \+ *lemma* coeff_X
- \+ *lemma* coeff_X'
- \+ *lemma* coeff_X''
- \+ *lemma* coeff_zero
- \+ *lemma* C_zero
- \+ *lemma* coeff_one
- \+ *lemma* coeff_one_zero
- \+ *lemma* C_one
- \+ *lemma* coeff_add
- \+ *lemma* monomial_add
- \+ *lemma* C_add
- \+ *lemma* coeff_mul
- \+ *lemma* C_mul
- \+ *lemma* is_unit_coeff_zero
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *lemma* coeff_map
- \+ *lemma* map_zero
- \+ *lemma* map_one
- \+ *lemma* map_add
- \+ *lemma* map_mul
- \+ *lemma* coeff_trunc
- \+ *lemma* trunc_zero
- \+ *lemma* trunc_one
- \+ *lemma* trunc_C
- \+ *lemma* trunc_add
- \+ *lemma* coeff_neg
- \+ *lemma* coeff_inv_aux
- \+ *lemma* coeff_inv_of_unit
- \+ *lemma* coeff_zero_inv_of_unit
- \+ *lemma* mul_inv_of_unit
- \+ *lemma* coeff_inv
- \+ *lemma* coeff_zero_inv
- \+ *lemma* inv_eq_zero
- \+ *lemma* inv_of_unit_eq
- \+ *lemma* inv_of_unit_eq'
- \+ *lemma* to_mv_power_series_coeff
- \+ *lemma* coeff_mk
- \+ *lemma* monomial_eq_mk
- \+ *lemma* is_local_ring
- \+ *lemma* to_power_series_coeff
- \+ *def* mv_power_series
- \+ *def* coeff
- \+ *def* monomial
- \+ *def* C
- \+ *def* X
- \+ *def* map
- \+ *def* trunc
- \+ *def* inv_of_unit
- \+ *def* is_local_ring
- \+ *def* to_mv_power_series
- \+ *def* power_series
- \+ *def* mk
- \+ *def* to_power_series



## [2019-07-22 08:00:24](https://github.com/leanprover-community/mathlib/commit/7c09ed5)
feat(category_theory/*): define `Cat` and a fully faithful functor `Mon ⥤ Cat` ([#1235](https://github.com/leanprover-community/mathlib/pull/1235))
* feat(category_theory/*): define `Cat` and a fully faithful functor `Mon ⥤ Cat`
* Drop 2 commas
* Drop `functor.id_comp` etc, add `Cat.str` instance, adjust module-level comments
* Make `α` and `β` arguments of `map_hom_equiv` explicit
This way `e α β f` is automatically interpreted as `(e α β).to_fun f`.
#### Estimated changes
Created src/category_theory/Cat.lean
- \+ *def* Cat
- \+ *def* of
- \+ *def* objects

Modified src/category_theory/functor.lean


Created src/category_theory/single_obj.lean
- \+ *lemma* to_End_def
- \+ *lemma* map_hom_id
- \+ *lemma* map_hom_comp
- \+ *def* single_obj
- \+ *def* to_End_equiv
- \+ *def* to_End
- \+ *def* map_hom_equiv
- \+ *def* map_hom
- \+ *def* to_Cat



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
- \+ *lemma* forall_iff
- \+ *lemma* exists_iff



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
- \+ *def* to_mul_equiv
- \+ *def* to_add_equiv



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
- \+ *def* left_adjoint
- \+ *def* right_adjoint

Created src/category_theory/adjunction/fully_faithful.lean


Created src/category_theory/monad/adjunction.lean
- \+ *lemma* monad_η_app
- \+ *lemma* monad_μ_app
- \+ *lemma* comparison_map_f
- \+ *lemma* comparison_obj_a
- \+ *lemma* comparison_ess_surj_aux
- \+ *def* comparison
- \+ *def* comparison_forget

Created src/category_theory/monad/algebra.lean
- \+ *lemma* ext
- \+ *lemma* id_f
- \+ *lemma* comp_f
- \+ *lemma* forget_map
- \+ *lemma* free_obj_a
- \+ *lemma* free_map_f
- \+ *def* id
- \+ *def* comp
- \+ *def* forget
- \+ *def* free
- \+ *def* adj

Created src/category_theory/monad/basic.lean


Created src/category_theory/monad/default.lean


Created src/category_theory/monad/limits.lean
- \+ *lemma* γ_app
- \+ *lemma* c_π
- \+ *lemma* cone_point_a
- \+ *def* γ
- \+ *def* c
- \+ *def* cone_point
- \+ *def* forget_creates_limits
- \+ *def* monadic_creates_limits
- \+ *def* has_limits_of_reflective

Modified src/category_theory/natural_isomorphism.lean
- \+ *def* is_iso_app_of_is_iso

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
- \- *lemma* of_mul
- \- *lemma* lift_of
- \- *lemma* lift_one
- \- *lemma* lift_mul
- \- *lemma* map_of
- \- *lemma* map_mul
- \- *theorem* lift_unique
- \- *def* free_monoid
- \- *def* of
- \- *def* lift
- \- *def* map

Modified src/algebra/group/with_one.lean
- \+ *lemma* one_ne_coe
- \+ *lemma* coe_ne_one
- \+ *lemma* ne_one_iff_exists
- \+ *lemma* coe_inj
- \+ *lemma* mul_coe
- \+ *lemma* lift_coe
- \+ *lemma* lift_one
- \+ *lemma* map_eq
- \- *lemma* with_one.one_ne_coe
- \- *lemma* with_one.coe_ne_one
- \- *lemma* with_one.ne_one_iff_exists
- \- *lemma* with_one.coe_inj
- \- *lemma* with_one.mul_coe
- \+ *theorem* lift_unique
- \+ *def* lift
- \+ *def* map



## [2019-07-19 14:09:02](https://github.com/leanprover-community/mathlib/commit/74754ac)
feat(analysis/calculus/times_cont_diff): multiple differentiability ([#1226](https://github.com/leanprover-community/mathlib/pull/1226))
* feat(analysis/calculus/times_cont_diff): multiple differentiability
* style
* style
* style and documentation
* better wording
#### Estimated changes
Created src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* iterated_fderiv_zero
- \+ *lemma* iterated_fderiv_succ
- \+ *lemma* iterated_fderiv_within_zero
- \+ *lemma* iterated_fderiv_within_succ
- \+ *lemma* iterated_fderiv_within_congr
- \+ *lemma* iterated_fderiv_within_inter_open
- \+ *lemma* iterated_fderiv_within_inter
- \+ *lemma* times_cont_diff_rec_zero
- \+ *lemma* times_cont_diff_rec_succ
- \+ *lemma* times_cont_diff_rec.of_succ
- \+ *lemma* times_cont_diff_rec.continuous
- \+ *lemma* times_cont_diff_rec.differentiable
- \+ *lemma* times_cont_diff_on_rec_zero
- \+ *lemma* times_cont_diff_on_rec_succ
- \+ *lemma* times_cont_diff_on_rec.of_succ
- \+ *lemma* times_cont_diff_on_rec.continuous_on_iterated_fderiv_within
- \+ *lemma* times_cont_diff_on_rec.differentiable_on
- \+ *lemma* times_cont_diff_on_rec_univ
- \+ *lemma* times_cont_diff_on_zero
- \+ *lemma* times_cont_diff_on_succ
- \+ *lemma* times_cont_diff_on.of_le
- \+ *lemma* times_cont_diff_on.of_succ
- \+ *lemma* times_cont_diff_on.continuous_on
- \+ *lemma* times_cont_diff_on.continuous_on_fderiv_within
- \+ *lemma* times_cont_diff_on.continuous_on_fderiv_within_apply
- \+ *lemma* times_cont_diff_on_top
- \+ *lemma* times_cont_diff_on_fderiv_within_nat
- \+ *lemma* times_cont_diff_on_fderiv_within
- \+ *lemma* times_cont_diff_on.congr_mono
- \+ *lemma* times_cont_diff_on.congr
- \+ *lemma* times_cont_diff_on.congr_mono'
- \+ *lemma* times_cont_diff_on.mono
- \+ *lemma* times_cont_diff_on_of_locally_times_cont_diff_on
- \+ *lemma* times_cont_diff_on_univ
- \+ *lemma* times_cont_diff_zero
- \+ *lemma* times_cont_diff_succ
- \+ *lemma* times_cont_diff.of_le
- \+ *lemma* times_cont_diff.of_succ
- \+ *lemma* times_cont_diff.continuous
- \+ *lemma* times_cont_diff.continuous_fderiv
- \+ *lemma* times_cont_diff.continuous_fderiv_apply
- \+ *lemma* times_cont_diff_top
- \+ *lemma* times_cont_diff.times_cont_diff_on
- \+ *lemma* times_cont_diff_const
- \+ *lemma* is_bounded_linear_map.times_cont_diff
- \+ *lemma* times_cont_diff_fst
- \+ *lemma* times_cont_diff_snd
- \+ *lemma* times_cont_diff_id
- \+ *lemma* is_bounded_bilinear_map.times_cont_diff
- \+ *lemma* times_cont_diff_on.comp_is_bounded_linear
- \+ *lemma* times_cont_diff.comp_is_bounded_linear
- \+ *lemma* times_cont_diff_on.prod
- \+ *lemma* times_cont_diff.prod
- \+ *lemma* times_cont_diff_on.comp
- \+ *lemma* times_cont_diff.comp
- \+ *lemma* times_cont_diff_on_fderiv_within_apply
- \+ *lemma* times_cont_diff.times_cont_diff_fderiv_apply
- \+ *theorem* iterated_fderiv_within_univ
- \+ *theorem* times_cont_diff_on_iff_times_cont_diff_on_rec
- \+ *theorem* times_cont_diff_iff_times_cont_diff_rec
- \+ *def* iterated_continuous_linear_map
- \+ *def* iterated_continuous_linear_map.normed_group_rec
- \+ *def* iterated_continuous_linear_map.normed_space_rec
- \+ *def* iterated_fderiv
- \+ *def* iterated_fderiv_within
- \+ *def* times_cont_diff_rec
- \+ *def* times_cont_diff_on_rec
- \+ *def* times_cont_diff_on
- \+ *def* times_cont_diff

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* fst
- \+ *lemma* snd
- \+ *lemma* is_bounded_bilinear_map_apply



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
- \+ *lemma* pointwise_mul_eq_Union_mul_left
- \+ *lemma* pointwise_mul_eq_Union_mul_right
- \+ *lemma* pointwise_mul_ne_empty
- \+ *lemma* univ_pointwise_mul_univ
- \+ *lemma* image_pointwise_mul
- \+ *lemma* preimage_pointwise_mul_preimage_subset
- \- *lemma* mul_subset_mul

Created src/order/filter/pointwise.lean
- \+ *lemma* mem_pointwise_one
- \+ *lemma* mem_pointwise_mul
- \+ *lemma* mul_mem_pointwise_mul
- \+ *lemma* pointwise_mul_le_mul
- \+ *lemma* pointwise_mul_ne_bot
- \+ *lemma* pointwise_mul_assoc
- \+ *lemma* pointwise_one_mul
- \+ *lemma* pointwise_mul_one
- \+ *lemma* map_pointwise_mul
- \+ *lemma* map_pointwise_one
- \+ *lemma* comap_mul_comap_le
- \+ *lemma* tendsto_mul_mul
- \+ *def* pointwise_one
- \+ *def* pointwise_mul
- \+ *def* pointwise_add
- \+ *def* pointwise_mul_monoid
- \+ *def* pointwise_mul_map_is_monoid_hom
- \+ *def* pointwise_add_map_is_add_monoid_hom

Modified src/topology/algebra/group.lean
- \+ *lemma* is_closed_map_mul_left
- \+ *lemma* is_closed_map_mul_right
- \+ *lemma* is_open_pointwise_mul_left
- \+ *lemma* is_open_pointwise_mul_right
- \+ *lemma* topological_group.t1_space
- \+ *lemma* topological_group.regular_space
- \+ *lemma* topological_group.t2_space
- \+ *lemma* nhds_pointwise_mul
- \+ *def* nhds_is_mul_hom

Modified src/topology/constructions.lean




## [2019-07-18 06:27:03](https://github.com/leanprover-community/mathlib/commit/e704f94)
fix(data/{nat,int}/parity): fix definition of 'even' ([#1240](https://github.com/leanprover-community/mathlib/pull/1240))
#### Estimated changes
Modified src/data/int/parity.lean
- \+/\- *def* even

Modified src/data/nat/parity.lean
- \+/\- *def* even



## [2019-07-17 17:57:06+02:00](https://github.com/leanprover-community/mathlib/commit/86e7287)
fix(data/zmod/basic) remove unused argument from instance ([#1239](https://github.com/leanprover-community/mathlib/pull/1239))
#### Estimated changes
Modified src/data/zmod/basic.lean




## [2019-07-17 09:56:01](https://github.com/leanprover-community/mathlib/commit/d6fd044)
feat(*): add nat.antidiagonal and use it for polynomial.mul_coeff ([#1237](https://github.com/leanprover-community/mathlib/pull/1237))
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* mem_antidiagonal
- \+ *lemma* card_antidiagonal
- \+ *lemma* antidiagonal_zero
- \+ *def* antidiagonal

Modified src/data/list/basic.lean
- \+ *lemma* mem_antidiagonal
- \+ *lemma* length_antidiagonal
- \+ *lemma* antidiagonal_zero
- \+ *lemma* nodup_antidiagonal
- \+ *def* antidiagonal

Modified src/data/multiset.lean
- \+ *lemma* mem_antidiagonal
- \+ *lemma* card_antidiagonal
- \+ *lemma* antidiagonal_zero
- \+ *lemma* nodup_antidiagonal
- \+ *def* antidiagonal

Modified src/data/polynomial.lean
- \+ *lemma* coeff_mul
- \- *lemma* coeff_mul_left
- \- *lemma* coeff_mul_right



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
- \+ *lemma* to_finsupp_support
- \+ *lemma* to_finsupp_apply
- \+ *lemma* to_finsupp_zero
- \+ *lemma* to_finsupp_add
- \+ *lemma* to_finsupp_singleton
- \+ *lemma* to_finsupp_to_multiset
- \+ *lemma* to_multiset_to_finsupp
- \+ *lemma* mem_antidiagonal_support
- \+ *lemma* antidiagonal_zero
- \+ *lemma* swap_mem_antidiagonal_support
- \+ *def* to_finsupp
- \+ *def* antidiagonal

Modified src/data/multiset.lean
- \+/\- *theorem* revzip_powerset_aux
- \+/\- *theorem* revzip_powerset_aux'
- \+ *theorem* antidiagonal_coe
- \+ *theorem* antidiagonal_coe'
- \+ *theorem* mem_antidiagonal
- \+ *theorem* antidiagonal_map_fst
- \+ *theorem* antidiagonal_map_snd
- \+ *theorem* antidiagonal_zero
- \+ *theorem* antidiagonal_cons
- \+ *theorem* card_antidiagonal
- \- *theorem* diagonal_coe
- \- *theorem* diagonal_coe'
- \- *theorem* mem_diagonal
- \- *theorem* diagonal_map_fst
- \- *theorem* diagonal_map_snd
- \- *theorem* diagonal_zero
- \- *theorem* diagonal_cons
- \- *theorem* card_diagonal
- \+ *def* antidiagonal
- \- *def* diagonal

Modified src/data/mv_polynomial.lean
- \+ *lemma* coeff_X_pow
- \+ *lemma* coeff_X'
- \+/\- *lemma* coeff_X
- \+ *lemma* coeff_mul
- \+/\- *lemma* coeff_mul_X
- \+/\- *lemma* coeff_mul_X'



## [2019-07-15 21:35:36](https://github.com/leanprover-community/mathlib/commit/92ac50c)
chore(data/finset): rename le_min_of_mem to min_le_of_mem ([#1231](https://github.com/leanprover-community/mathlib/pull/1231))
* chore(data/finset): rename le_min_of_mem to min_le_of_mem
* fix build
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* min_le_of_mem
- \+/\- *theorem* min'_le
- \- *theorem* le_min_of_mem



## [2019-07-15 14:48:52](https://github.com/leanprover-community/mathlib/commit/7217f13)
feat(data/option/basic): bind_eq_none ([#1232](https://github.com/leanprover-community/mathlib/pull/1232))
* feat(data/option/basis): bind_eq_none
* delete extra line
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *theorem* bind_eq_none



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
Created src/data/pequiv.lean
- \+ *lemma* coe_mk_apply
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* mem_iff_mem
- \+ *lemma* eq_some_iff
- \+ *lemma* refl_apply
- \+ *lemma* symm_refl
- \+ *lemma* symm_refl_apply
- \+ *lemma* symm_symm
- \+ *lemma* symm_symm_apply
- \+ *lemma* symm_injective
- \+ *lemma* trans_assoc
- \+ *lemma* mem_trans
- \+ *lemma* trans_eq_some
- \+ *lemma* trans_eq_none
- \+ *lemma* refl_trans
- \+ *lemma* trans_refl
- \+ *lemma* refl_trans_apply
- \+ *lemma* trans_refl_apply
- \+ *lemma* injective_of_forall_ne_is_some
- \+ *lemma* injective_of_forall_is_some
- \+ *lemma* mem_of_set_self_iff
- \+ *lemma* mem_of_set_iff
- \+ *lemma* of_set_eq_some_self_iff
- \+ *lemma* of_set_eq_some_iff
- \+ *lemma* of_set_symm
- \+ *lemma* of_set_univ
- \+ *lemma* of_set_eq_refl
- \+ *lemma* symm_trans_rev
- \+ *lemma* trans_symm
- \+ *lemma* symm_trans
- \+ *lemma* trans_symm_eq_iff_forall_is_some
- \+ *lemma* bot_apply
- \+ *lemma* symm_bot
- \+ *lemma* trans_bot
- \+ *lemma* bot_trans
- \+ *lemma* is_some_symm_get
- \+ *lemma* mem_single
- \+ *lemma* mem_single_iff
- \+ *lemma* symm_single
- \+ *lemma* single_apply
- \+ *lemma* single_apply_of_ne
- \+ *lemma* single_trans_of_mem
- \+ *lemma* trans_single_of_mem
- \+ *lemma* single_trans_single
- \+ *lemma* single_subsingleton_eq_refl
- \+ *lemma* trans_single_of_eq_none
- \+ *lemma* single_trans_of_eq_none
- \+ *lemma* single_trans_single_of_ne
- \+ *lemma* le_def
- \+ *lemma* to_pequiv_refl
- \+ *lemma* to_pequiv_trans
- \+ *lemma* to_pequiv_symm
- \+ *def* of_set
- \+ *def* single
- \+ *def* to_pequiv



## [2019-07-14 05:25:05](https://github.com/leanprover-community/mathlib/commit/03e6d0e)
chore(algebra/group/hom): add `is_monoid_hom.of_mul`, use it ([#1225](https://github.com/leanprover-community/mathlib/pull/1225))
* Let `to_additive` generate `is_add_monoid_hom.map_add`
* Converting `is_mul_hom` into `is_monoid_hom` doesn't require `α` to be a group
* Simplify the proof of `is_add_group_hom.map_sub`
Avoid `simp` (without `only`)
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* map_one
- \- *lemma* map_add
- \- *lemma* to_is_monoid_hom
- \+ *theorem* is_monoid_hom.of_mul
- \- *theorem* map_one



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
- \+ *def* Pi_curry

Modified src/data/prod.lean
- \+ *lemma* map_fst'
- \+ *lemma* map_snd'

Modified src/logic/basic.lean
- \+ *lemma* exists_imp_exists'
- \+/\- *theorem* forall_swap
- \+/\- *theorem* exists_swap



## [2019-07-13 16:25:07](https://github.com/leanprover-community/mathlib/commit/0eea0d9)
feat(data/{nat,int}/parity): the 'even' predicate on nat and int ([#1219](https://github.com/leanprover-community/mathlib/pull/1219))
* feat(data/{nat,int}/parity): the 'even' predicate on nat and int
* fix(data/{nat,int}/parity): shorten proof
* delete extra comma
#### Estimated changes
Created src/data/int/parity.lean
- \+ *theorem* mod_two_ne_one
- \+ *theorem* mod_two_ne_zero
- \+ *theorem* even_coe_nat
- \+ *theorem* even_iff
- \+ *theorem* even_zero
- \+ *theorem* not_even_one
- \+ *theorem* even_bit0
- \+ *theorem* even_add
- \+ *theorem* not_even_bit1
- \+ *theorem* even_sub
- \+ *theorem* even_mul
- \+ *theorem* even_pow
- \+ *def* even

Created src/data/nat/parity.lean
- \+ *theorem* mod_two_ne_one
- \+ *theorem* mod_two_ne_zero
- \+ *theorem* even_iff
- \+ *theorem* even_zero
- \+ *theorem* not_even_one
- \+ *theorem* even_bit0
- \+ *theorem* even_add
- \+ *theorem* not_even_bit1
- \+ *theorem* even_sub
- \+ *theorem* even_succ
- \+ *theorem* even_mul
- \+ *theorem* even_pow
- \+ *def* even



## [2019-07-13 01:46:58](https://github.com/leanprover-community/mathlib/commit/6db5829)
feat(data/finmap): extend the API ([#1223](https://github.com/leanprover-community/mathlib/pull/1223))
#### Estimated changes
Modified src/data/finmap.lean
- \+ *lemma* mem_singleton
- \+ *lemma* lookup_singleton_eq
- \+ *lemma* mem_iff
- \+ *lemma* mem_of_lookup_eq_some
- \+ *lemma* disjoint_empty
- \+ *lemma* disjoint.symm
- \+ *lemma* disjoint.symm_iff
- \+ *lemma* disjoint_union_left
- \+ *lemma* disjoint_union_right
- \+/\- *theorem* empty_to_finmap
- \+ *theorem* to_finmap_nil
- \+ *theorem* lookup_list_to_finmap
- \+ *theorem* not_mem_erase_self
- \+ *theorem* erase_erase
- \+ *theorem* lookup_insert_of_ne
- \+ *theorem* insert_insert
- \+ *theorem* insert_insert_of_ne
- \+ *theorem* to_finmap_cons
- \+ *theorem* mem_list_to_finmap
- \+ *theorem* insert_singleton_eq
- \+ *theorem* lookup_union_left_of_not_in
- \+ *theorem* insert_union
- \+ *theorem* union_assoc
- \+ *theorem* empty_union
- \+ *theorem* union_empty
- \+ *theorem* ext_lookup
- \+ *theorem* erase_union_singleton
- \+ *theorem* union_comm_of_disjoint
- \+ *theorem* union_cancel
- \+ *def* list.to_finmap
- \+ *def* any
- \+ *def* all
- \+ *def* sdiff
- \+ *def* disjoint

Modified src/data/list/alist.lean
- \+ *lemma* insert_singleton_eq
- \+ *theorem* erase_erase
- \+ *theorem* lookup_to_alist
- \+ *theorem* insert_insert
- \+ *theorem* insert_insert_of_ne
- \+ *theorem* entries_to_alist
- \+ *theorem* to_alist_cons
- \+ *theorem* union_erase
- \+ *theorem* insert_union
- \+ *theorem* union_assoc
- \+ *theorem* union_comm_of_disjoint
- \+ *def* list.to_alist
- \+ *def* disjoint

Modified src/data/list/basic.lean
- \+ *theorem* mem_enum_from
- \+ *theorem* pw_filter_map

Modified src/data/list/sigma.lean
- \+ *lemma* mem_ext
- \+ *lemma* lookup_ext
- \+ *lemma* erase_dupkeys_cons
- \+ *lemma* nodupkeys_erase_dupkeys
- \+ *lemma* lookup_erase_dupkeys
- \+ *theorem* kerase_kerase
- \+ *def* erase_dupkeys



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
- \+ *theorem* inter_sdiff
- \+ *theorem* filter_inter
- \+ *theorem* inter_filter
- \+ *theorem* filter_insert
- \+ *theorem* filter_singleton
- \+ *theorem* bind_inter
- \+ *theorem* inter_bind

Modified src/data/int/basic.lean
- \- *lemma* mod_mod
- \+ *theorem* mod_mod
- \+ *theorem* mod_mod_of_dvd

Modified src/data/nat/basic.lean
- \+ *theorem* mod_mod_of_dvd

Modified src/data/zmod/basic.lean
- \+ *lemma* neg_val'
- \+ *lemma* neg_val



## [2019-07-12 01:43:22](https://github.com/leanprover-community/mathlib/commit/3d36966)
feat(analysis/calculus/mean_value): the mean value inequality ([#1212](https://github.com/leanprover-community/mathlib/pull/1212))
* feat(analysis/calculus/mean_value): the mean value inequality
* remove blank lines
#### Estimated changes
Created src/analysis/calculus/mean_value.lean
- \+ *theorem* norm_image_sub_le_of_norm_deriv_le_segment
- \+ *theorem* norm_image_sub_le_of_norm_deriv_le_convex

Modified src/analysis/convex.lean
- \+ *lemma* image_Icc_zero_one_eq_segment



## [2019-07-11 21:03:56](https://github.com/leanprover-community/mathlib/commit/7806586)
feat(analysis/calculus/deriv): extended API for derivatives ([#1213](https://github.com/leanprover-community/mathlib/pull/1213))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_fderiv_within_at_univ
- \+ *lemma* has_fderiv_within_at_inter'
- \+ *lemma* has_fderiv_within_at_inter
- \+/\- *lemma* has_fderiv_at.fderiv
- \+/\- *lemma* has_fderiv_within_at.fderiv_within
- \+/\- *lemma* differentiable_within_at.mono
- \+ *lemma* differentiable_within_at_univ
- \+/\- *lemma* differentiable_within_at_inter
- \+/\- *lemma* differentiable_within_at.differentiable_at
- \+/\- *lemma* differentiable_on.mono
- \+/\- *lemma* differentiable.differentiable_on
- \+/\- *lemma* differentiable_on_of_locally_differentiable_on
- \+ *lemma* fderiv_within_subset
- \+ *lemma* fderiv_within_inter
- \+ *lemma* has_fderiv_at_filter.congr_of_mem_sets
- \+ *lemma* has_fderiv_within_at.congr_of_mem_nhds_within
- \+ *lemma* has_fderiv_at.congr_of_mem_nhds
- \+ *lemma* differentiable_within_at.congr_of_mem_nhds_within
- \+ *lemma* differentiable_at.congr_of_mem_nhds
- \+ *lemma* fderiv_within_congr_of_mem_nhds_within
- \+ *lemma* fderiv_within_congr
- \+ *lemma* fderiv_congr_of_mem_nhds
- \+ *lemma* differentiable.comp
- \- *lemma* differentiable_within_univ_at
- \- *lemma* has_fderiv_within_univ_at
- \- *lemma* differentiable_within_at.differentiable_at'
- \- *lemma* has_fderiv_at_filter.congr'
- \- *lemma* differentiable_at.congr
- \- *lemma* differentiable.congr
- \- *lemma* differentiable.congr'
- \- *lemma* differentiable_at.fderiv_congr
- \- *lemma* differentiable_at.fderiv_congr'
- \+/\- *theorem* has_fderiv_at_unique
- \+ *theorem* has_fderiv_at_filter_congr_of_mem_sets
- \- *theorem* has_fderiv_at_filter_congr'
- \- *theorem* has_fderiv_at_filter_congr
- \- *theorem* has_fderiv_at_filter.congr
- \- *theorem* has_fderiv_within_at_congr
- \- *theorem* has_fderiv_within_at.congr
- \- *theorem* has_fderiv_at_congr
- \- *theorem* has_fderiv_at.congr



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


Created src/tactic/localized.lean
- \+ *def* string_hash

Created test/localized/import1.lean


Created test/localized/import2.lean


Created test/localized/import3.lean


Created test/localized/localized.lean




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
- \+/\- *def* units_End_eqv_Aut

Modified src/data/equiv/algebra.lean


Modified src/data/equiv/basic.lean
- \+/\- *theorem* symm_symm
- \+/\- *theorem* symm_symm_apply
- \+/\- *theorem* trans_refl
- \+/\- *theorem* refl_trans
- \+/\- *def* prod_congr
- \+/\- *def* prod_comm
- \+/\- *def* prod_assoc
- \+/\- *def* prod_punit
- \+/\- *def* punit_prod
- \+/\- *def* prod_empty
- \+/\- *def* empty_prod
- \+/\- *def* prod_pempty
- \+/\- *def* pempty_prod
- \+/\- *def* psum_equiv_sum
- \+/\- *def* sum_congr
- \+/\- *def* bool_equiv_punit_sum_punit
- \+/\- *def* sum_comm
- \+/\- *def* sum_assoc
- \+/\- *def* sum_empty
- \+/\- *def* empty_sum
- \+/\- *def* sum_pempty
- \+/\- *def* pempty_sum
- \+/\- *def* option_equiv_sum_punit
- \+/\- *def* sum_equiv_sigma_bool
- \+/\- *def* sigma_equiv_prod
- \+/\- *def* sigma_equiv_prod_of_equiv
- \+/\- *def* arrow_prod_equiv_prod_arrow
- \+/\- *def* sum_arrow_equiv_prod_arrow
- \+/\- *def* sum_prod_distrib
- \+/\- *def* prod_sum_distrib
- \+/\- *def* bool_prod_equiv_sum
- \+/\- *def* nat_equiv_nat_sum_punit
- \+/\- *def* nat_sum_punit_equiv_nat
- \+/\- *def* int_equiv_nat_sum_nat

Modified src/data/equiv/denumerable.lean
- \+/\- *def* pair

Modified src/data/equiv/fin.lean
- \+/\- *def* sum_fin_sum_equiv
- \+/\- *def* fin_prod_fin_equiv

Modified src/data/equiv/nat.lean
- \+/\- *def* nat_prod_nat_equiv_nat
- \+/\- *def* bool_prod_nat_equiv_nat
- \+/\- *def* nat_sum_nat_equiv_nat
- \+/\- *def* prod_equiv_of_equiv_nat

Modified src/data/finsupp.lean
- \+/\- *def* equiv_multiset

Modified src/data/list/sort.lean


Modified src/group_theory/coset.lean


Modified src/linear_algebra/basic.lean


Modified src/order/basic.lean


Modified src/order/filter/basic.lean


Modified src/order/order_iso.lean


Modified src/set_theory/ordinal.lean
- \+/\- *def* initial_seg.lt_or_eq

Modified src/topology/constructions.lean
- \+/\- *def* prod_congr
- \+/\- *def* prod_comm
- \+/\- *def* prod_assoc

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
- \+/\- *lemma* of_add
- \+/\- *lemma* lift_add

Modified src/algebra/direct_sum.lean


Modified src/algebra/group/conj.lean


Modified src/algebra/group/hom.lean
- \+ *lemma* mul
- \+ *lemma* inv
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_add
- \+ *lemma* is_group_hom.mk'
- \- *lemma* id
- \- *lemma* comp
- \- *lemma* comp'
- \- *lemma* is_group_hom.mul
- \- *lemma* is_group_hom.inv

Modified src/algebra/group/units_hom.lean
- \- *lemma* map_comp'

Modified src/algebra/group_power.lean


Modified src/algebra/module.lean


Modified src/algebra/punit_instances.lean


Modified src/algebra/ring.lean


Modified src/data/dfinsupp.lean


Modified src/data/equiv/algebra.lean


Modified src/data/mv_polynomial.lean


Modified src/group_theory/abelianization.lean


Modified src/group_theory/free_abelian_group.lean
- \+ *theorem* lift.add'

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
- \+ *lemma* nat_induction



## [2019-07-10 21:33:20](https://github.com/leanprover-community/mathlib/commit/5cdebb7)
feat(*): Miscellaneous lemmas in algebra ([#1188](https://github.com/leanprover-community/mathlib/pull/1188))
* Trying things out
* feat(ring_theory/*): Misc little lemmas
* More little lemmas
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* closure_subgroup
- \- *theorem* closure_mono
- \- *theorem* mclosure_subset
- \- *theorem* mclosure_inv_subset

Modified src/ring_theory/algebra.lean
- \+ *lemma* span_int_eq_add_group_closure
- \+ *lemma* span_int_eq

Modified src/ring_theory/algebra_operations.lean
- \+ *lemma* mul_subset_mul
- \+ *lemma* pow_subset_pow
- \+ *lemma* smul_def
- \+ *lemma* smul_le_smul
- \+ *lemma* smul_singleton

Modified src/ring_theory/ideal_operations.lean
- \+ *lemma* pow_le_pow
- \+ *lemma* map_quotient_self

Modified src/ring_theory/ideals.lean
- \+ *lemma* eq_bot_or_top
- \+ *lemma* eq_bot_of_prime

Modified src/ring_theory/noetherian.lean
- \+ *lemma* fg_pow



## [2019-07-10 19:39:24](https://github.com/leanprover-community/mathlib/commit/5aebdc4)
fix(*): fix line endings ([#1209](https://github.com/leanprover-community/mathlib/pull/1209))
#### Estimated changes
Modified src/data/complex/exponential.lean
- \+/\- *lemma* forall_ge_le_of_forall_le_succ
- \+/\- *lemma* is_cau_of_decreasing_bounded
- \+/\- *lemma* is_cau_of_mono_bounded
- \+/\- *lemma* is_cau_series_of_abv_le_cau
- \+/\- *lemma* is_cau_series_of_abv_cau
- \+/\- *lemma* is_cau_geo_series
- \+/\- *lemma* is_cau_geo_series_const
- \+/\- *lemma* series_ratio_test
- \+/\- *lemma* sum_range_diag_flip
- \+/\- *lemma* abv_sum_le_sum_abv
- \+/\- *lemma* sum_range_sub_sum_range
- \+/\- *lemma* cauchy_product
- \+/\- *lemma* is_cau_abs_exp
- \+/\- *lemma* is_cau_exp
- \+/\- *lemma* exp_zero
- \+/\- *lemma* exp_add
- \+/\- *lemma* exp_nat_mul
- \+/\- *lemma* exp_ne_zero
- \+/\- *lemma* exp_neg
- \+/\- *lemma* exp_sub
- \+/\- *lemma* exp_conj
- \+/\- *lemma* of_real_exp_of_real_re
- \+/\- *lemma* of_real_exp
- \+/\- *lemma* exp_of_real_im
- \+/\- *lemma* exp_of_real_re
- \+/\- *lemma* two_sinh
- \+/\- *lemma* two_cosh
- \+/\- *lemma* sinh_zero
- \+/\- *lemma* sinh_neg
- \+/\- *lemma* sinh_add
- \+/\- *lemma* cosh_zero
- \+/\- *lemma* cosh_neg
- \+/\- *lemma* cosh_add
- \+/\- *lemma* sinh_sub
- \+/\- *lemma* cosh_sub
- \+/\- *lemma* sinh_conj
- \+/\- *lemma* of_real_sinh_of_real_re
- \+/\- *lemma* of_real_sinh
- \+/\- *lemma* sinh_of_real_im
- \+/\- *lemma* sinh_of_real_re
- \+/\- *lemma* cosh_conj
- \+/\- *lemma* of_real_cosh_of_real_re
- \+/\- *lemma* of_real_cosh
- \+/\- *lemma* cosh_of_real_im
- \+/\- *lemma* cosh_of_real_re
- \+/\- *lemma* tanh_eq_sinh_div_cosh
- \+/\- *lemma* tanh_zero
- \+/\- *lemma* tanh_neg
- \+/\- *lemma* tanh_conj
- \+/\- *lemma* of_real_tanh_of_real_re
- \+/\- *lemma* of_real_tanh
- \+/\- *lemma* tanh_of_real_im
- \+/\- *lemma* tanh_of_real_re
- \+/\- *lemma* cosh_add_sinh
- \+/\- *lemma* sinh_add_cosh
- \+/\- *lemma* cosh_sub_sinh
- \+/\- *lemma* cosh_sq_sub_sinh_sq
- \+/\- *lemma* sin_zero
- \+/\- *lemma* sin_neg
- \+/\- *lemma* two_sin
- \+/\- *lemma* two_cos
- \+/\- *lemma* sinh_mul_I
- \+/\- *lemma* cosh_mul_I
- \+/\- *lemma* sin_add
- \+/\- *lemma* cos_zero
- \+/\- *lemma* cos_neg
- \+/\- *lemma* cos_add
- \+/\- *lemma* sin_sub
- \+/\- *lemma* cos_sub
- \+/\- *lemma* sin_conj
- \+/\- *lemma* of_real_sin_of_real_re
- \+/\- *lemma* of_real_sin
- \+/\- *lemma* sin_of_real_im
- \+/\- *lemma* sin_of_real_re
- \+/\- *lemma* cos_conj
- \+/\- *lemma* of_real_cos_of_real_re
- \+/\- *lemma* of_real_cos
- \+/\- *lemma* cos_of_real_im
- \+/\- *lemma* cos_of_real_re
- \+/\- *lemma* tan_zero
- \+/\- *lemma* tan_eq_sin_div_cos
- \+/\- *lemma* tan_neg
- \+/\- *lemma* tan_conj
- \+/\- *lemma* of_real_tan_of_real_re
- \+/\- *lemma* of_real_tan
- \+/\- *lemma* tan_of_real_im
- \+/\- *lemma* tan_of_real_re
- \+/\- *lemma* cos_add_sin_I
- \+/\- *lemma* cos_sub_sin_I
- \+/\- *lemma* sin_sq_add_cos_sq
- \+/\- *lemma* cos_two_mul'
- \+/\- *lemma* cos_two_mul
- \+/\- *lemma* sin_two_mul
- \+/\- *lemma* cos_square
- \+/\- *lemma* sin_square
- \+/\- *lemma* exp_mul_I
- \+/\- *lemma* exp_add_mul_I
- \+/\- *lemma* exp_eq_exp_re_mul_sin_add_cos
- \+/\- *lemma* sin_sq_le_one
- \+/\- *lemma* cos_sq_le_one
- \+/\- *lemma* abs_sin_le_one
- \+/\- *lemma* abs_cos_le_one
- \+/\- *lemma* sin_le_one
- \+/\- *lemma* cos_le_one
- \+/\- *lemma* neg_one_le_sin
- \+/\- *lemma* neg_one_le_cos
- \+/\- *lemma* add_one_le_exp_of_nonneg
- \+/\- *lemma* one_le_exp
- \+/\- *lemma* exp_pos
- \+/\- *lemma* abs_exp
- \+/\- *lemma* exp_strict_mono
- \+/\- *lemma* exp_lt_exp
- \+/\- *lemma* exp_le_exp
- \+/\- *lemma* exp_injective
- \+/\- *lemma* exp_eq_one_iff
- \+/\- *lemma* sum_div_fact_le
- \+/\- *lemma* exp_bound
- \+/\- *lemma* abs_exp_sub_one_le
- \+/\- *lemma* cos_bound
- \+/\- *lemma* sin_bound
- \+/\- *lemma* cos_pos_of_le_one
- \+/\- *lemma* sin_pos_of_pos_of_le_one
- \+/\- *lemma* sin_pos_of_pos_of_le_two
- \+/\- *lemma* cos_one_le
- \+/\- *lemma* cos_one_pos
- \+/\- *lemma* cos_two_neg
- \+/\- *lemma* abs_cos_add_sin_mul_I
- \+/\- *lemma* abs_exp_eq_iff_re_eq
- \+/\- *lemma* abs_exp_of_real
- \+/\- *theorem* cos_add_sin_mul_I_pow
- \+/\- *def* exp'
- \+/\- *def* exp
- \+/\- *def* sin
- \+/\- *def* cos
- \+/\- *def* tan
- \+/\- *def* sinh
- \+/\- *def* cosh
- \+/\- *def* tanh

Modified src/data/nat/totient.lean
- \+/\- *lemma* totient_le
- \+/\- *lemma* totient_pos
- \+/\- *lemma* sum_totient
- \+/\- *def* totient

Modified src/meta/rb_map.lean


Modified src/tactic/linarith.lean
- \+/\- *lemma* int.coe_nat_bit0
- \+/\- *lemma* int.coe_nat_bit1
- \+/\- *lemma* int.coe_nat_bit0_mul
- \+/\- *lemma* int.coe_nat_bit1_mul
- \+/\- *lemma* int.coe_nat_one_mul
- \+/\- *lemma* int.coe_nat_zero_mul
- \+/\- *lemma* int.coe_nat_mul_bit0
- \+/\- *lemma* int.coe_nat_mul_bit1
- \+/\- *lemma* int.coe_nat_mul_one
- \+/\- *lemma* int.coe_nat_mul_zero
- \+/\- *lemma* nat_eq_subst
- \+/\- *lemma* nat_le_subst
- \+/\- *lemma* nat_lt_subst
- \+/\- *lemma* eq_of_eq_of_eq
- \+/\- *lemma* le_of_eq_of_le
- \+/\- *lemma* lt_of_eq_of_lt
- \+/\- *lemma* le_of_le_of_eq
- \+/\- *lemma* lt_of_lt_of_eq
- \+/\- *lemma* mul_neg
- \+/\- *lemma* mul_nonpos
- \+/\- *lemma* mul_eq
- \+/\- *lemma* eq_of_not_lt_of_not_gt
- \+/\- *lemma* add_subst
- \+/\- *lemma* sub_subst
- \+/\- *lemma* neg_subst
- \+/\- *lemma* mul_subst
- \+/\- *lemma* div_subst
- \+/\- *lemma* sub_into_lt
- \+/\- *def* ineq.max
- \+/\- *def* ineq.is_lt
- \+/\- *def* ineq.to_string
- \+/\- *def* tree.repr



## [2019-07-10 18:25:32](https://github.com/leanprover-community/mathlib/commit/0bc4a50)
feat(tactic/apply_fun): adds `apply_fun` tactic ([#1184](https://github.com/leanprover-community/mathlib/pull/1184))
* feat(tactic/apply_fun): adds `apply_fun` tactic
* move tests to test folder
* elaborate function with expected type
* fix merge mistake
#### Estimated changes
Modified docs/tactics.md


Created src/tactic/apply_fun.lean


Modified src/tactic/default.lean


Created test/apply_fun.lean




## [2019-07-10 15:57:51](https://github.com/leanprover-community/mathlib/commit/d2b4380)
feat(data/list/basic): list.prod_range_succ, list.sum_range_succ ([#1197](https://github.com/leanprover-community/mathlib/pull/1197))
* feat(data/list/basic): list.prod_range_succ, list.sum_range_succ
* changes from review
* remove simp
* shorten proof
#### Estimated changes
Modified src/data/list/basic.lean
- \+/\- *theorem* range_concat
- \+ *theorem* prod_range_succ



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
- \+/\- *lemma* tangent_cone_at.lim_zero
- \+ *lemma* tangent_cone_inter_nhds
- \+ *lemma* subset_tangent_cone_prod_left
- \+ *lemma* subset_tangent_cone_prod_right
- \+ *lemma* mem_tangent_cone_of_segment_subset
- \+ *lemma* unique_diff_within_at_univ
- \+ *lemma* unique_diff_on_univ
- \+/\- *lemma* unique_diff_within_at_inter
- \+ *lemma* unique_diff_within_at.inter
- \+ *lemma* unique_diff_within_at.mono
- \+/\- *lemma* is_open.unique_diff_within_at
- \+ *lemma* unique_diff_within_at.prod
- \+ *lemma* unique_diff_on.prod
- \+ *lemma* unique_diff_on_Icc_zero_one
- \- *lemma* tangent_cone_inter_open
- \- *lemma* unique_diff_within_univ_at
- \+ *theorem* unique_diff_on_convex



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
- \- *lemma* End.one_def
- \- *lemma* End.mul_def
- \- *def* End

Created src/category_theory/endomorphism.lean
- \+ *lemma* one_def
- \+ *lemma* mul_def
- \+ *def* End
- \+ *def* Aut
- \+ *def* units_End_eqv_Aut
- \+ *def* map_End
- \+ *def* map_Aut

Modified src/category_theory/isomorphism.lean
- \+ *lemma* map_iso_trans
- \- *def* Aut



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
- \+ *lemma* curry_uncurry'
- \+ *lemma* uncurry'_curry
- \+ *lemma* uncurry'_bicompr
- \+ *def* uncurry'

Modified src/measure_theory/bochner_integration.lean


Modified src/topology/algebra/group_completion.lean
- \+/\- *lemma* coe_zero

Modified src/topology/algebra/ordered.lean


Modified src/topology/algebra/uniform_group.lean
- \- *lemma* continuous_extend_of_cauchy
- \+/\- *theorem* extend_Z_bilin

Modified src/topology/algebra/uniform_ring.lean
- \+/\- *lemma* continuous_mul'

Modified src/topology/constructions.lean
- \+ *lemma* dense_range_prod

Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/real.lean
- \+/\- *theorem* embedding_of_rat

Modified src/topology/maps.lean
- \+ *lemma* dense_range_iff_closure_eq
- \+ *lemma* dense_range.comp
- \+ *lemma* dense_range.inhabited
- \+ *lemma* inducing_id
- \+ *lemma* inducing.comp
- \+ *lemma* inducing.prod_mk
- \+ *lemma* inducing_of_inducing_compose
- \+ *lemma* inducing_open
- \+ *lemma* inducing_is_closed
- \+ *lemma* inducing.nhds_eq_comap
- \+ *lemma* inducing.map_nhds_eq
- \+ *lemma* inducing.tendsto_nhds_iff
- \+ *lemma* inducing.continuous_iff
- \+ *lemma* inducing.continuous
- \+ *lemma* embedding.comp
- \+ *lemma* embedding.prod_mk
- \+ *lemma* nhds_eq_comap
- \+/\- *lemma* closure_range
- \+/\- *lemma* self_sub_closure_image_preimage_of_open
- \+/\- *lemma* closure_image_nhds_of_nhds
- \+/\- *lemma* tendsto_comap_nhds_nhds
- \+/\- *lemma* comap_nhds_neq_bot
- \+/\- *lemma* extend_eq
- \+/\- *lemma* extend_e_eq
- \+ *lemma* extend_eq_of_cont
- \+/\- *lemma* tendsto_extend
- \+/\- *lemma* continuous_extend
- \+ *lemma* mk'
- \+/\- *lemma* inj_iff
- \+ *lemma* to_embedding
- \+ *lemma* closed_embedding.comp
- \- *lemma* embedding_compose
- \- *lemma* embedding_prod_mk
- \- *lemma* closed_embedding_compose
- \+/\- *theorem* dense_embedding.mk'
- \+ *def* dense_range
- \+ *def* embedding.mk'
- \+/\- *def* extend
- \- *def* embedding

Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/order.lean
- \+ *lemma* induced_iff_nhds_eq
- \- *lemma* nhds_induced_eq_comap

Modified src/topology/stone_cech.lean
- \+ *lemma* dense_inducing_pure
- \+/\- *lemma* dense_embedding_pure

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* uniform_continuous₂_def
- \+ *lemma* uniform_continuous₂_curry
- \+ *lemma* uniform_continuous₂.comp
- \+ *def* uniform_continuous₂

Modified src/topology/uniform_space/complete_separated.lean
- \+/\- *lemma* is_closed_of_is_complete
- \+ *lemma* continuous_extend_of_cauchy

Modified src/topology/uniform_space/completion.lean
- \+ *lemma* uniform_inducing_pure_cauchy
- \+ *lemma* dense_inducing_pure_cauchy
- \+ *lemma* nonempty_completion_iff
- \+ *lemma* uniform_inducing_coe
- \+ *lemma* dense_inducing_coe
- \+ *lemma* extension_unique
- \+/\- *lemma* prod_coe_coe
- \+ *lemma* uniform_continuous_extension₂
- \+ *lemma* extension₂_coe_coe
- \+ *lemma* uniform_continuous_map₂
- \+/\- *lemma* map₂_coe_coe
- \- *lemma* prod_pure_cauchy_pure_cauchy
- \- *lemma* uniform_continuous_prod
- \- *lemma* uniform_continuous_map₂'
- \- *def* prod

Modified src/topology/uniform_space/uniform_embedding.lean
- \+ *lemma* uniform_inducing.comp
- \+ *lemma* uniform_embedding.comp
- \+ *lemma* uniform_inducing.uniform_continuous
- \+ *lemma* uniform_inducing.uniform_continuous_iff
- \+ *lemma* uniform_inducing.inducing
- \+ *lemma* uniform_inducing.prod
- \+ *lemma* uniform_inducing.dense_inducing
- \+/\- *lemma* uniform_embedding.embedding
- \+/\- *lemma* uniform_embedding.dense_embedding
- \+ *lemma* closure_image_mem_nhds_of_uniform_inducing
- \+/\- *lemma* uniform_embedding_subtype_emb
- \+/\- *lemma* uniform_embedding.prod
- \+/\- *lemma* is_complete_image_iff
- \+/\- *lemma* complete_space_extension
- \+/\- *lemma* totally_bounded_preimage
- \+/\- *lemma* uniform_embedding_comap
- \+ *lemma* uniformly_extend_of_ind
- \+/\- *lemma* uniformly_extend_spec
- \+/\- *lemma* uniform_extend_subtype
- \- *lemma* uniform_embedding.uniform_continuous
- \- *lemma* uniform_embedding.uniform_continuous_iff
- \- *lemma* closure_image_mem_nhds_of_uniform_embedding
- \- *lemma* uniformly_extend_of_emb
- \+/\- *theorem* uniform_embedding_def
- \+/\- *theorem* uniform_embedding_def'
- \+ *def* uniform_inducing.mk'
- \- *def* uniform_embedding



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
- \+/\- *theorem* mul_zero
- \+/\- *theorem* zero_mul



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
- \+ *lemma* not_succ_lt_self
- \+ *theorem* two_mul_ne_two_mul_add_one



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
- \- *lemma* one
- \- *def* refl
- \- *def* symm
- \- *def* trans



## [2019-07-06 22:30:41](https://github.com/leanprover-community/mathlib/commit/55b0b80)
fix(src/logic/basic): add [symm] attribute to ne. ([#1190](https://github.com/leanprover-community/mathlib/pull/1190))
#### Estimated changes
Modified src/logic/basic.lean




## [2019-07-06 11:29:31](https://github.com/leanprover-community/mathlib/commit/ccf5636)
feat(data/option/basic): not_is_some_iff_eq_none and ne_none_iff_is_some ([#1186](https://github.com/leanprover-community/mathlib/pull/1186))
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* not_is_some_iff_eq_none
- \+ *lemma* ne_none_iff_is_some



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


Modified src/category_theory/adjunction/limits.lean
- \- *def* is_colimit_map_cocone
- \- *def* is_limit_map_cone

Modified src/category_theory/limits/limits.lean
- \- *def* limit.is_limit
- \- *def* colimit.is_colimit

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
- \+ *def* adjunction

Modified src/category_theory/adjunction/limits.lean
- \+ *def* is_colimit_map_cocone
- \+ *def* has_colimit_of_comp_equivalence
- \+ *def* is_limit_map_cone
- \+ *def* has_limit_of_comp_equivalence
- \- *def* left_adjoint_preserves_colimits
- \- *def* right_adjoint_preserves_limits

Modified src/category_theory/equivalence.lean
- \+/\- *lemma* functor_unit_comp
- \+/\- *lemma* counit_inv_functor_comp
- \+/\- *lemma* unit_inverse_comp
- \+/\- *lemma* inverse_counit_inv_comp

Modified src/category_theory/limits/cones.lean
- \+ *lemma* map_cone_X
- \+ *lemma* map_cocone_X
- \+ *lemma* map_cone_inv_X
- \+ *def* map_cone_inv

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
- \+ *lemma* free_obj_α
- \+ *lemma* free_map_val
- \- *lemma* polynomial_ring_obj_α
- \- *lemma* polynomial_ring_map_val
- \+ *def* free
- \+ *def* hom_equiv
- \+ *def* adj

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
- \- *lemma* id_val
- \- *lemma* comp_val
- \- *def* is_comm_ring_hom

Modified src/algebra/CommRing/colimits.lean
- \+/\- *lemma* cocone_naturality_components

Modified src/algebra/Mon/colimits.lean
- \+/\- *lemma* cocone_naturality_components

Modified src/category_theory/concrete_category.lean
- \+ *lemma* coe_comp

Modified src/category_theory/isomorphism.lean
- \+ *lemma* map_inv

Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/opposites.lean
- \+ *def* is_iso_of_op

Modified src/category_theory/whiskering.lean


Modified src/topology/Top/stalks.lean


Modified src/topology/algebra/TopCommRing/basic.lean
- \+/\- *def* forget



## [2019-07-04 19:49:02](https://github.com/leanprover-community/mathlib/commit/569bcf9)
feat(algebra/ordered_group): eq_of_abs_non_pos ([#1185](https://github.com/leanprover-community/mathlib/pull/1185))
* feat(algebra/ordered_group): decidable_linear_ordered_comm_group.eq_of_abs_non_pos
* fix(algebra/ordered_group): new line and name
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* eq_of_abs_sub_nonpos



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
- \+/\- *lemma* abs_one



## [2019-07-04 14:31:11](https://github.com/leanprover-community/mathlib/commit/0818bb2)
feat(data/fin): mem_find_of_unique ([#1181](https://github.com/leanprover-community/mathlib/pull/1181))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* mem_find_of_unique



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
- \+ *theorem* mem_preimage
- \- *theorem* mem_preimage_eq

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
- \+ *lemma* mem_or_eq_of_mem_update_nth
- \+ *lemma* diff_eq_filter_of_nodup
- \+ *lemma* mem_diff_iff_of_nodup
- \+ *lemma* nodup_update_nth



## [2019-07-04 06:57:24](https://github.com/leanprover-community/mathlib/commit/00de1cb)
feat(data/list/basic): list.nodup_diff ([#1168](https://github.com/leanprover-community/mathlib/pull/1168))
* feat(data/list/basic): list.nodup_diff
* Update basic.lean
* Update basic.lean
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* nodup_diff



## [2019-07-04 05:16:33](https://github.com/leanprover-community/mathlib/commit/e6b9696)
feat(data/option): not_mem_none and bind_assoc ([#1177](https://github.com/leanprover-community/mathlib/pull/1177))
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* not_mem_none
- \+ *lemma* bind_assoc



## [2019-07-04 03:33:42](https://github.com/leanprover-community/mathlib/commit/4cca114)
feat(data/fin): fin.find ([#1167](https://github.com/leanprover-community/mathlib/pull/1167))
* feat(data/fin): fin.find
* add nat_find_mem_find
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* find_spec
- \+ *lemma* is_some_find_iff
- \+ *lemma* find_eq_none_iff
- \+ *lemma* find_min
- \+ *lemma* find_min'
- \+ *lemma* nat_find_mem_find
- \+ *def* find



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


Created src/order/pilex.lean
- \+ *def* pi.lex
- \+ *def* pilex



## [2019-07-03 22:09:24](https://github.com/leanprover-community/mathlib/commit/992354c)
feat(data/fintype): well_foundedness lemmas on fintypes ([#1156](https://github.com/leanprover-community/mathlib/pull/1156))
* feat(data/fintype): well_foundedness lemmas on fintypes
* Update fintype.lean
* minor fixes
#### Estimated changes
Modified src/data/fintype.lean
- \+ *lemma* well_founded_of_trans_of_irrefl
- \+ *lemma* preorder.well_founded
- \+ *lemma* linear_order.is_well_order



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
- \+/\- *lemma* preimage_id
- \+ *lemma* preimage_comp
- \+ *lemma* preimage_map
- \+ *def* is_iso_of_fully_faithful

Modified src/category_theory/types.lean


Modified src/category_theory/yoneda.lean
- \+ *lemma* naturality
- \+ *def* is_iso



## [2019-07-03 15:25:41](https://github.com/leanprover-community/mathlib/commit/e4ee18b)
feat(category_theory/adjunction): additional simp lemmas ([#1143](https://github.com/leanprover-community/mathlib/pull/1143))
* feat(category_theory/adjunction): additional simp lemmas
* spaces
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean
- \+ *lemma* left_triangle_components_assoc
- \+ *lemma* right_triangle_components_assoc
- \+ *lemma* counit_naturality
- \+ *lemma* unit_naturality
- \+ *lemma* counit_naturality_assoc
- \+ *lemma* unit_naturality_assoc



## [2019-07-03 12:44:32](https://github.com/leanprover-community/mathlib/commit/f1b5473)
feat(data/list/basic): fin_range ([#1159](https://github.com/leanprover-community/mathlib/pull/1159))
* feat(data/list/basic): fin_range
fin_range is like `list.range` but returns a `list (fin n)` instead of a `list nat`
* Update basic.lean
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* mem_fin_range
- \+ *lemma* nodup_fin_range
- \+ *lemma* length_fin_range
- \+ *def* fin_range



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
- \+ *lemma* subtype_eq_val

Modified src/data/finset.lean
- \+ *theorem* exists_mem_iff_ne_empty

Modified src/data/finsupp.lean
- \+ *lemma* single_swap
- \+ *lemma* unique_single
- \+ *lemma* emb_domain_inj
- \+ *lemma* single_of_emb_domain_single
- \+ *lemma* comap_domain_apply
- \+ *lemma* sum_comap_domain
- \+ *lemma* eq_zero_of_comap_domain_eq_zero
- \+ *lemma* map_domain_comap_domain
- \+ *lemma* split_apply
- \+ *lemma* mem_split_support_iff_nonzero
- \+ *lemma* sigma_support
- \+ *lemma* sigma_sum
- \+ *def* split_support
- \- *def* to_semiring
- \- *def* to_comm_semiring
- \- *def* to_ring
- \- *def* to_comm_ring
- \- *def* to_has_scalar'
- \- *def* to_semimodule
- \- *def* to_module
- \- *def* to_has_scalar

Modified src/data/mv_polynomial.lean


Modified src/data/polynomial.lean


Modified src/data/set/basic.lean
- \+ *lemma* range_comp_subset_range
- \+ *lemma* sum.elim_range

Modified src/data/set/finite.lean
- \+ *lemma* mem_preimage
- \+ *lemma* coe_preimage
- \+ *lemma* image_preimage
- \+ *lemma* prod_preimage
- \+/\- *theorem* finite_of_finite_image

Modified src/data/set/function.lean
- \+ *lemma* inj_on_of_injective

Modified src/data/sum.lean
- \+ *lemma* elim_inl
- \+ *lemma* elim_inr
- \+ *lemma* elim_injective

Modified src/field_theory/finite_card.lean


Modified src/field_theory/mv_polynomial.lean
- \+ *lemma* mem_restrict_total_degree
- \+ *lemma* mem_restrict_degree
- \+ *lemma* mem_restrict_degree_iff_sup
- \+ *lemma* map_range_eq_map
- \+ *lemma* is_basis_monomials
- \+ *lemma* dim_mv_polynomial
- \+ *def* restrict_total_degree
- \+ *def* restrict_degree

Modified src/linear_algebra/basic.lean
- \+ *lemma* eq_bot_of_zero_eq_one
- \+ *lemma* linear_eq_on
- \+ *lemma* map_le_range
- \+ *lemma* sup_range_inl_inr
- \+ *lemma* disjoint_inl_inr

Modified src/linear_algebra/basis.lean
- \+ *lemma* linear_independent_empty_type
- \+ *lemma* ne_zero_of_linear_independent
- \+ *lemma* linear_independent.comp
- \+ *lemma* linear_independent_of_zero_eq_one
- \+/\- *lemma* linear_independent.unique
- \+ *lemma* linear_independent.injective
- \+ *lemma* linear_independent_span
- \+ *lemma* linear_independent.to_subtype_range
- \+ *lemma* linear_independent.of_subtype_range
- \+ *lemma* linear_independent.restrict_of_comp_subtype
- \+/\- *lemma* linear_independent_empty
- \+/\- *lemma* linear_independent.mono
- \+/\- *lemma* linear_independent_of_finite
- \+/\- *lemma* linear_independent_Union_of_directed
- \+/\- *lemma* linear_independent_bUnion_of_directed
- \+ *lemma* linear_independent_Union_finite_subtype
- \+/\- *lemma* linear_independent_Union_finite
- \+/\- *lemma* linear_independent.total_repr
- \+/\- *lemma* linear_independent.total_comp_repr
- \+/\- *lemma* linear_independent.repr_ker
- \+/\- *lemma* linear_independent.repr_range
- \+/\- *lemma* linear_independent.repr_eq
- \+/\- *lemma* linear_independent.repr_eq_single
- \+ *lemma* surjective_of_linear_independent_of_span
- \+ *lemma* eq_of_linear_independent_of_span_subtype
- \+/\- *lemma* linear_independent.image
- \+ *lemma* linear_independent.image_subtype
- \+ *lemma* linear_independent_inl_union_inr'
- \+/\- *lemma* is_basis.mem_span
- \+ *lemma* is_basis.comp
- \+ *lemma* is_basis.injective
- \+/\- *lemma* is_basis.total_repr
- \+/\- *lemma* is_basis.total_comp_repr
- \+/\- *lemma* is_basis.repr_ker
- \+/\- *lemma* is_basis.repr_range
- \+/\- *lemma* is_basis.repr_total
- \+/\- *lemma* is_basis.repr_eq_single
- \+/\- *lemma* is_basis.ext
- \+/\- *lemma* constr_basis
- \+/\- *lemma* constr_eq
- \+/\- *lemma* constr_self
- \+/\- *lemma* constr_zero
- \+/\- *lemma* constr_add
- \+/\- *lemma* constr_neg
- \+/\- *lemma* constr_sub
- \+/\- *lemma* constr_smul
- \+/\- *lemma* constr_range
- \+/\- *lemma* is_basis_inl_union_inr
- \+/\- *lemma* is_basis_singleton_one
- \+/\- *lemma* linear_equiv.is_basis
- \+/\- *lemma* is_basis_span
- \+/\- *lemma* is_basis_empty
- \+/\- *lemma* is_basis_empty_bot
- \+/\- *lemma* linear_independent_iff_not_mem_span
- \+ *lemma* linear_independent_unique
- \+/\- *lemma* linear_independent_singleton
- \+/\- *lemma* linear_independent.insert
- \+/\- *lemma* exists_linear_independent
- \+/\- *lemma* exists_subset_is_basis
- \+/\- *lemma* exists_is_basis
- \+/\- *lemma* linear_independent_std_basis
- \+/\- *lemma* is_basis_std_basis
- \+ *lemma* is_basis_fun₀
- \+/\- *lemma* is_basis_fun
- \- *lemma* zero_not_mem_of_linear_independent
- \- *lemma* linear_independent.repr_supported
- \- *lemma* linear_independent.repr_eq_repr_of_subset
- \- *lemma* eq_of_linear_independent_of_span
- \- *lemma* linear_independent.supported_disjoint_ker
- \- *lemma* linear_independent.of_image
- \- *lemma* linear_independent.disjoint_ker
- \- *lemma* linear_independent.inj_span_iff_inj
- \- *lemma* linear_map.linear_independent_image_iff
- \- *lemma* is_basis.repr_supported
- \- *lemma* constr_congr
- \- *lemma* is_basis_injective
- \+/\- *theorem* linear_independent_iff
- \+ *theorem* linear_independent_comp_subtype
- \+ *theorem* linear_independent_subtype
- \+ *theorem* linear_independent_comp_subtype_disjoint
- \+ *theorem* linear_independent_subtype_disjoint
- \+/\- *theorem* linear_independent_iff_total_on
- \+/\- *theorem* is_basis.constr_apply
- \+/\- *theorem* vector_space.card_fintype
- \+/\- *theorem* vector_space.card_fintype'
- \+/\- *def* linear_independent
- \+/\- *def* linear_independent.total_equiv
- \+/\- *def* linear_independent.repr
- \+/\- *def* is_basis
- \+/\- *def* is_basis.repr
- \+/\- *def* is_basis.constr
- \+ *def* module_equiv_finsupp
- \+/\- *def* equiv_of_is_basis
- \- *def* module_equiv_lc

Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_span
- \+ *lemma* dim_span_set
- \+/\- *lemma* dim_span_le
- \+/\- *lemma* dim_span_of_finset
- \+/\- *lemma* dim_range_of_surjective
- \+/\- *lemma* dim_le_injective
- \+/\- *lemma* dim_fun'
- \+/\- *lemma* exists_is_basis_fintype
- \+/\- *lemma* rank_finset_sum_le
- \+/\- *theorem* is_basis.le_span
- \+/\- *theorem* mk_eq_mk_of_basis
- \+ *theorem* is_basis.mk_range_eq_dim
- \+/\- *theorem* is_basis.mk_eq_dim
- \+/\- *theorem* linear_equiv.dim_eq
- \+/\- *theorem* dim_quotient
- \+/\- *theorem* linear_equiv.dim_eq_lift

Modified src/linear_algebra/dual.lean
- \+/\- *lemma* to_dual_apply
- \+/\- *lemma* coord_fun_eq_repr
- \+/\- *lemma* to_dual_eq_repr
- \+/\- *lemma* to_dual_to_dual
- \+/\- *theorem* to_dual_range
- \+/\- *theorem* dual_basis_is_basis
- \+/\- *theorem* dual_dim_eq
- \+ *def* eval_finsupp_at
- \+/\- *def* coord_fun
- \+/\- *def* dual_basis
- \+/\- *def* to_dual_equiv
- \- *def* eval_lc_at

Modified src/linear_algebra/finsupp.lean
- \+/\- *lemma* lsingle_apply
- \+/\- *lemma* lapply_apply
- \+/\- *lemma* ker_lsingle
- \+ *lemma* mem_supported
- \+ *lemma* mem_supported'
- \+ *lemma* single_mem_supported
- \+ *lemma* supported_eq_span_single
- \+ *lemma* range_total
- \+ *lemma* total_comap_domain
- \- *lemma* lmap_domain_apply
- \- *lemma* linear_independent_single
- \- *lemma* mem_restrict_dom
- \- *lemma* is_basis_single
- \- *lemma* dim_eq
- \- *lemma* equiv_of_dim_eq_dim
- \- *lemma* eq_bot_iff_dim_eq_zero
- \- *lemma* injective_of_surjective
- \- *lemma* cardinal_mk_eq_cardinal_mk_field_pow_dim
- \- *lemma* cardinal_lt_omega_of_dim_lt_omega
- \- *lemma* mem_restrict_total_degree
- \- *lemma* mem_restrict_degree
- \- *lemma* mem_restrict_degree_iff_sup
- \- *lemma* map_range_eq_map
- \- *lemma* is_basis_monomials
- \- *lemma* dim_mv_polynomial
- \+ *theorem* restrict_dom_apply
- \+ *theorem* restrict_dom_comp_subtype
- \+ *theorem* range_restrict_dom
- \+ *theorem* supported_mono
- \+ *theorem* supported_empty
- \+ *theorem* supported_univ
- \+ *theorem* supported_Union
- \+ *theorem* supported_union
- \+ *theorem* supported_Inter
- \+ *theorem* lsum_apply
- \+ *theorem* lmap_domain_apply
- \+ *theorem* lmap_domain_id
- \+ *theorem* lmap_domain_comp
- \+ *theorem* supported_comap_lmap_domain
- \+ *theorem* lmap_domain_supported
- \+ *theorem* lmap_domain_disjoint_ker
- \+ *theorem* total_apply
- \+ *theorem* total_single
- \+ *theorem* total_range
- \+ *theorem* lmap_domain_total
- \+ *theorem* total_emb_domain
- \+ *theorem* total_map_domain
- \+ *theorem* span_eq_map_total
- \+ *theorem* mem_span_iff_total
- \+ *theorem* total_on_range
- \+ *theorem* total_comp
- \+ *def* supported
- \+/\- *def* restrict_dom
- \+ *def* supported_equiv_finsupp
- \+ *def* lsum
- \+/\- *def* lmap_domain
- \- *def* restrict_dom_equiv_finsupp
- \- *def* restrict_total_degree
- \- *def* restrict_degree

Created src/linear_algebra/finsupp_vector_space.lean
- \+ *lemma* linear_independent_single
- \+ *lemma* is_basis_single
- \+ *lemma* dim_eq
- \+ *lemma* equiv_of_dim_eq_dim
- \+ *lemma* eq_bot_iff_dim_eq_zero
- \+ *lemma* injective_of_surjective
- \+ *lemma* cardinal_mk_eq_cardinal_mk_field_pow_dim
- \+ *lemma* cardinal_lt_omega_of_dim_lt_omega

Deleted src/linear_algebra/linear_combination.lean
- \- *lemma* linear_eq_on
- \- *theorem* mem_supported
- \- *theorem* mem_supported'
- \- *theorem* single_mem_supported
- \- *theorem* supported_eq_span_single
- \- *theorem* restrict_dom_apply
- \- *theorem* restrict_dom_comp_subtype
- \- *theorem* range_restrict_dom
- \- *theorem* supported_mono
- \- *theorem* supported_empty
- \- *theorem* supported_univ
- \- *theorem* supported_Union
- \- *theorem* supported_union
- \- *theorem* supported_Inter
- \- *theorem* apply_apply
- \- *theorem* lsum_apply
- \- *theorem* total_apply
- \- *theorem* total_single
- \- *theorem* total_range
- \- *theorem* map_apply
- \- *theorem* map_id
- \- *theorem* map_comp
- \- *theorem* supported_comap_map
- \- *theorem* map_supported
- \- *theorem* map_disjoint_ker
- \- *theorem* map_total
- \- *theorem* span_eq_map_lc
- \- *theorem* mem_span_iff_lc
- \- *theorem* lc.total_on_range
- \- *def* lc
- \- *def* supported
- \- *def* restrict_dom
- \- *def* apply
- \- *def* lc.total_on

Modified src/linear_algebra/matrix.lean


Modified src/logic/basic.lean
- \+ *lemma* nonempty_pempty
- \+/\- *lemma* not_nonempty_iff_imp_false

Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/noetherian.lean


Modified src/set_theory/cardinal.lean
- \+ *lemma* mk_range_eq_of_inj
- \+ *theorem* lift_max

Modified src/topology/metric_space/closeds.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2019-07-03 09:02:02](https://github.com/leanprover-community/mathlib/commit/9a33885)
chore(data/matrix): rows and columns the right way around ([#1171](https://github.com/leanprover-community/mathlib/pull/1171))
* chore(data/matrix): rows and columns the right way around
* update matrix.lean
#### Estimated changes
Modified src/data/matrix.lean
- \+/\- *def* col
- \+/\- *def* row
- \+/\- *def* minor



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
- \+/\- *lemma* cocone_naturality_components

Modified src/algebra/Mon/colimits.lean
- \+/\- *lemma* cocone_naturality_components

Modified src/algebra/big_operators.lean
- \+/\- *lemma* prod_map

Modified src/algebra/module.lean
- \+/\- *lemma* is_linear_map_smul
- \+/\- *lemma* is_linear_map_smul'

Modified src/algebra/ordered_field.lean
- \+ *lemma* inv_pos_of_nat
- \+ *lemma* one_div_pos_of_nat

Modified src/analysis/asymptotics.lean


Modified src/analysis/complex/exponential.lean
- \+/\- *lemma* mul_rpow
- \+/\- *lemma* rpow_le_rpow

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* real.norm_eq_abs

Modified src/category_theory/limits/cones.lean
- \+/\- *lemma* postcompose_map_hom

Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* limit.hom_iso_hom
- \+/\- *lemma* colimit.hom_iso_hom
- \+/\- *lemma* colimit.ι_pre_assoc
- \+/\- *lemma* colimit.ι_post_assoc
- \+/\- *lemma* colim.ι_map_assoc

Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/pullbacks.lean


Modified src/category_theory/limits/types.lean
- \+/\- *lemma* types_limit_lift

Modified src/data/dfinsupp.lean


Modified src/data/fin.lean
- \+/\- *lemma* cast_succ_cast_lt

Modified src/data/finset.lean
- \+/\- *theorem* image_sub

Modified src/data/finsupp.lean
- \+/\- *lemma* support_add_eq

Modified src/data/holor.lean
- \+/\- *lemma* mul_assoc
- \+/\- *lemma* holor_index_cons_decomp
- \+/\- *lemma* slice_add

Modified src/data/lazy_list2.lean


Modified src/data/list/basic.lean
- \+/\- *theorem* map_sub

Modified src/data/mv_polynomial.lean
- \+/\- *lemma* monomial_add_single
- \+/\- *lemma* monomial_single_add

Modified src/data/nat/basic.lean
- \+/\- *lemma* mul_right_eq_self_iff
- \+/\- *lemma* mul_left_eq_self_iff
- \+ *lemma* find_greatest_eq_zero
- \+ *lemma* find_greatest_of_ne_zero

Modified src/data/nat/cast.lean
- \+ *lemma* cast_add_one_pos

Modified src/data/polynomial.lean
- \+/\- *lemma* leading_coeff_comp
- \+/\- *def* decidable_dvd_monic

Modified src/data/quot.lean
- \+/\- *lemma* quotient.lift_beta
- \+/\- *lemma* quotient.lift_on_beta
- \+/\- *lemma* nonempty_quotient_iff

Modified src/data/real/ennreal.lean
- \+ *lemma* coe_nnreal_eq
- \+ *lemma* of_real_eq_coe_nnreal
- \+/\- *lemma* le_of_forall_epsilon_le
- \+ *lemma* sub_self
- \+/\- *lemma* sub_left_inj
- \+ *lemma* mem_Iio_self_add
- \+ *lemma* not_mem_Ioo_self_sub
- \+ *lemma* mem_Ioo_self_sub_add
- \+ *lemma* of_real_le_iff_le_to_real
- \+ *lemma* of_real_lt_iff_lt_to_real
- \+ *lemma* le_of_real_iff_to_real_le
- \+ *lemma* lt_of_real_iff_to_real_lt
- \+ *lemma* of_real_mul
- \+ *lemma* to_real_of_real_mul

Modified src/data/real/hyperreal.lean
- \+/\- *lemma* epsilon_lt_pos
- \+/\- *lemma* st_of_is_st
- \+/\- *lemma* is_st_st_of_is_st
- \+/\- *lemma* is_st_st
- \+/\- *lemma* is_st_st'
- \+/\- *lemma* is_st_refl_real
- \+/\- *lemma* is_st_real_iff_eq
- \+/\- *lemma* is_st_symm_real
- \+/\- *lemma* is_st_trans_real
- \+/\- *lemma* is_st_inj_real
- \+/\- *lemma* is_st_iff_abs_sub_lt_delta
- \+/\- *lemma* is_st_add
- \+/\- *lemma* is_st_neg
- \+/\- *lemma* st_le_of_le
- \+/\- *lemma* lt_of_st_lt
- \+/\- *lemma* ne_zero_of_infinite
- \+/\- *lemma* not_infinite_pos_of_infinite_neg
- \+/\- *lemma* not_infinite_neg_of_infinite_pos
- \+/\- *lemma* infinite_neg_neg_of_infinite_pos
- \+/\- *lemma* infinite_pos_neg_of_infinite_neg
- \+/\- *lemma* infinite_pos_iff_infinite_neg_neg
- \+/\- *lemma* infinite_neg_iff_infinite_pos_neg
- \+/\- *lemma* infinite_iff_infinite_neg
- \+/\- *lemma* not_infinite_of_infinitesimal
- \+/\- *lemma* not_infinitesimal_of_infinite
- \+/\- *lemma* not_infinitesimal_of_infinite_pos
- \+/\- *lemma* not_infinitesimal_of_infinite_neg
- \+/\- *lemma* infinite_pos_iff_infinite_and_pos
- \+/\- *lemma* infinite_neg_iff_infinite_and_neg
- \+/\- *lemma* infinite_pos_iff_infinite_of_pos
- \+/\- *lemma* infinite_pos_iff_infinite_of_nonneg
- \+/\- *lemma* infinite_neg_iff_infinite_of_neg
- \+/\- *lemma* infinite_pos_abs_iff_infinite_abs
- \+/\- *lemma* infinite_iff_infinite_pos_abs
- \+/\- *lemma* infinite_iff_infinite_abs
- \+/\- *lemma* infinite_iff_abs_lt_abs
- \+/\- *lemma* infinite_pos_add_not_infinite_neg
- \+/\- *lemma* not_infinite_neg_add_infinite_pos
- \+/\- *lemma* infinite_neg_add_not_infinite_pos
- \+/\- *lemma* not_infinite_pos_add_infinite_neg
- \+/\- *lemma* infinite_pos_add_infinite_pos
- \+/\- *lemma* infinite_neg_add_infinite_neg
- \+/\- *lemma* infinite_pos_add_not_infinite
- \+/\- *lemma* infinite_neg_add_not_infinite
- \+/\- *lemma* not_infinite_neg
- \+/\- *lemma* not_infinite_add
- \+/\- *lemma* is_st_mul
- \+/\- *lemma* not_infinite_mul
- \+/\- *lemma* st_add
- \+/\- *lemma* st_neg
- \+/\- *lemma* st_mul
- \+/\- *lemma* zero_iff_infinitesimal_real
- \+/\- *lemma* infinitesimal_add
- \+/\- *lemma* infinitesimal_neg
- \+/\- *lemma* infinitesimal_neg_iff
- \+/\- *lemma* infinitesimal_mul
- \+/\- *lemma* not_real_of_infinitesimal_ne_zero
- \+/\- *lemma* infinite_pos_iff_infinitesimal_inv_pos
- \+/\- *lemma* infinite_neg_iff_infinitesimal_inv_neg
- \+/\- *lemma* infinitesimal_pos_iff_infinite_pos_inv
- \+/\- *lemma* infinitesimal_neg_iff_infinite_neg_inv
- \+/\- *lemma* is_st_inv
- \+/\- *lemma* st_inv
- \+/\- *lemma* infinite_pos_omega
- \+/\- *lemma* infinite_omega
- \+/\- *lemma* infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos
- \+/\- *lemma* infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos
- \+/\- *lemma* infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg
- \+/\- *lemma* infinite_pos_mul_of_not_infinitesimal_neg_infinite_neg
- \+/\- *lemma* infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg
- \+/\- *lemma* infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos
- \+/\- *lemma* infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos
- \+/\- *lemma* infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg
- \+/\- *lemma* infinite_pos_mul_infinite_pos
- \+/\- *lemma* infinite_neg_mul_infinite_neg
- \+/\- *lemma* infinite_pos_mul_infinite_neg
- \+/\- *lemma* infinite_neg_mul_infinite_pos
- \+/\- *lemma* infinite_mul_of_infinite_not_infinitesimal
- \+/\- *lemma* infinite_mul_of_not_infinitesimal_infinite
- \+/\- *lemma* infinite_mul_infinite
- \+/\- *theorem* not_infinite_of_exists_st
- \+/\- *theorem* is_st_Sup
- \+/\- *theorem* exists_st_of_not_infinite
- \+/\- *theorem* exists_st_iff_not_infinite
- \+/\- *theorem* infinite_iff_not_exists_st
- \+/\- *theorem* st_infinite
- \+/\- *theorem* infinite_pos_of_tendsto_top
- \+/\- *theorem* infinite_neg_of_tendsto_bot
- \+/\- *theorem* not_infinite_iff_exist_lt_gt
- \+/\- *theorem* not_real_of_infinite
- \+/\- *theorem* infinitesimal_def
- \+/\- *theorem* lt_of_pos_of_infinitesimal
- \+/\- *theorem* lt_neg_of_pos_of_infinitesimal
- \+/\- *theorem* gt_of_neg_of_infinitesimal
- \+/\- *theorem* abs_lt_real_iff_infinitesimal
- \+/\- *theorem* infinitesimal_epsilon
- \+/\- *theorem* infinitesimal_sub_is_st
- \+/\- *theorem* infinitesimal_sub_st
- \+/\- *theorem* infinitesimal_inv_of_infinite
- \+/\- *theorem* infinite_of_infinitesimal_inv
- \+/\- *theorem* infinite_iff_infinitesimal_inv
- \+/\- *theorem* infinitesimal_iff_infinite_inv

Modified src/data/real/nnreal.lean
- \+ *lemma* of_real_le_iff_le_coe
- \+ *lemma* le_of_real_iff_coe_le
- \+ *lemma* of_real_lt_iff_lt_coe
- \+ *lemma* lt_of_real_iff_coe_lt
- \+ *lemma* of_real_mul

Modified src/data/rel.lean
- \+/\- *lemma* core_id
- \+/\- *def* rel

Modified src/data/set/basic.lean
- \+ *lemma* range_ite_subset'
- \+ *lemma* range_ite_subset
- \+/\- *lemma* range_coe_subtype

Modified src/data/set/countable.lean
- \+ *lemma* subset_range_enumerate
- \+ *def* enumerate_countable

Modified src/data/set/disjointed.lean
- \+ *lemma* disjoint_disjointed'
- \+ *lemma* disjointed_subset

Modified src/data/set/finite.lean
- \+ *lemma* finite_range_ite
- \+ *lemma* finite_range_const
- \+ *lemma* range_find_greatest_subset
- \+ *lemma* finite_range_find_greatest

Modified src/data/set/lattice.lean
- \+/\- *theorem* Union_subset_iff

Modified src/group_theory/subgroup.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* dim_map_le

Modified src/logic/function.lean
- \+/\- *theorem* restrict_eq

Created src/measure_theory/ae_eq_fun.lean
- \+ *lemma* quot_mk_eq_mk
- \+ *lemma* mk_eq_mk
- \+ *lemma* comp₂_mk_mk
- \+ *lemma* mk_le_mk
- \+ *lemma* zero_def
- \+ *lemma* one_def
- \+ *lemma* mk_add_mk
- \+ *lemma* neg_mk
- \+ *lemma* smul_mk
- \+ *lemma* eintegral_mk
- \+ *lemma* eintegral_zero
- \+ *lemma* eintegral_eq_zero_iff
- \+ *lemma* eintegral_add
- \+ *lemma* eintegral_le_eintegral
- \+ *lemma* comp_edist_self
- \+ *lemma* edist_mk_mk
- \+ *lemma* edist_mk_mk'
- \+ *lemma* edist_eq_add_add
- \+ *lemma* edist_smul
- \+ *def* ae_eq_fun
- \+ *def* mk
- \+ *def* comp
- \+ *def* comp₂
- \+ *def* lift_pred
- \+ *def* lift_rel
- \+ *def* lift_rel_mk_mk
- \+ *def* const
- \+ *def* eintegral
- \+ *def* comp_edist

Created src/measure_theory/bochner_integration.lean
- \+ *lemma* exists_simple_func_near
- \+ *lemma* uniform_continuous_of_simple_func
- \+ *lemma* uniform_embedding_of_simple_func
- \+ *lemma* dense_embedding_of_simple_func
- \+ *def* simple_func
- \+ *def* mk
- \+ *def* to_simple_func
- \+ *def* integral

Modified src/measure_theory/borel_space.lean
- \+ *lemma* is_measurable_ball
- \+ *lemma* is_measurable_singleton
- \+ *lemma* measurable_of_real
- \+ *lemma* measurable_smul'
- \+ *lemma* measurable_smul
- \+ *lemma* measurable_dist'
- \+ *lemma* measurable_dist
- \+ *lemma* measurable_nndist'
- \+ *lemma* measurable_nndist
- \+ *lemma* measurable_edist'
- \+ *lemma* measurable_edist
- \+ *lemma* measurable_norm'
- \+ *lemma* measurable_norm
- \+ *lemma* measurable_nnnorm'
- \+ *lemma* measurable_nnnorm
- \+ *lemma* measurable_coe_nnnorm

Modified src/measure_theory/integration.lean


Created src/measure_theory/l1_space.lean
- \+ *lemma* lintegral_nnnorm_zero
- \+ *lemma* integrable_zero
- \+ *lemma* lintegral_nnnorm_add
- \+ *lemma* integrable_add
- \+ *lemma* lintegral_nnnorm_neg
- \+ *lemma* integrable_neg
- \+ *lemma* integrable_smul
- \+ *lemma* integrable_mk
- \+ *lemma* dist_def
- \+ *lemma* zero_def
- \+ *lemma* add_def
- \+ *lemma* norm_def
- \+ *lemma* smul_def
- \+ *def* integrable
- \+ *def* l1
- \+ *def* mk

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_from_nat
- \+ *lemma* measurable_to_nat
- \+ *lemma* measurable_find_greatest

Modified src/measure_theory/measure_space.lean


Created src/measure_theory/simple_func_dense.lean
- \+ *lemma* simple_func_sequence_tendsto
- \+ *lemma* simple_func_sequence_tendsto'

Modified src/order/complete_lattice.lean
- \+/\- *theorem* infi_le₂'

Modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* bdd_below_bot

Modified src/order/filter/basic.lean
- \+/\- *lemma* univ_mem_sets'
- \+/\- *lemma* mem_infi
- \+/\- *lemma* mem_infi_finite

Modified src/order/filter/filter_product.lean
- \+/\- *theorem* of_inj
- \+/\- *def* of

Modified src/order/filter/lift.lean


Modified src/order/fixed_points.lean


Modified src/ring_theory/polynomial.lean
- \+/\- *theorem* degree_le_mono

Modified src/tactic/ext.lean


Modified src/tactic/solve_by_elim.lean


Modified src/tactic/tfae.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* mem_of_is_lub_of_is_closed
- \+/\- *lemma* mem_of_is_glb_of_is_closed
- \+/\- *theorem* tendsto_of_liminf_eq_limsup
- \+/\- *theorem* limsup_eq_of_tendsto
- \+/\- *theorem* liminf_eq_of_tendsto

Modified src/topology/basic.lean
- \+ *lemma* dense_of_subset_dense

Modified src/topology/constructions.lean


Modified src/topology/instances/ennreal.lean
- \+ *lemma* is_open_Ico_zero
- \+ *lemma* nhds_top
- \+ *lemma* nhds_zero
- \+ *lemma* Icc_mem_nhds
- \+ *lemma* nhds_of_ne_top

Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* tendsto_of_real

Modified src/topology/metric_space/basic.lean
- \+ *lemma* continuous_nndist
- \+ *lemma* mem_closure_range_iff
- \+ *lemma* mem_closure_range_iff_nat

Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* ball_subset

Modified src/topology/order.lean


Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* uniformity_lift_le_comp

Modified src/topology/uniform_space/separation.lean
- \+/\- *lemma* uniform_continuous_map

Modified test/ext.lean


Modified test/linarith.lean


Modified test/omega.lean


Modified test/solve_by_elim.lean


Modified test/tidy.lean
- \+/\- *def* tidy_test_1



## [2019-07-02 13:11:09](https://github.com/leanprover-community/mathlib/commit/1ef2c2d)
feat(data/list/basic): filter_true and filter_false ([#1169](https://github.com/leanprover-community/mathlib/pull/1169))
* feat(data/list/basic): filter_true and filter_false
* Update basic.lean
* Update basic.lean
* Update basic.lean
* Update basic.lean
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* filter_true
- \+ *lemma* filter_false



## [2019-07-02 11:28:23](https://github.com/leanprover-community/mathlib/commit/b4989a0)
compute the cardinality of real ([#1096](https://github.com/leanprover-community/mathlib/pull/1096))
* compute the cardinality of real
* minor improvements
* fix(data/rat/denumerable): change namespace of of_rat
* style(src/topology/algebra/infinite_sum): structure proof
#### Estimated changes
Modified src/data/equiv/denumerable.lean


Modified src/data/equiv/nat.lean
- \+ *def* pnat_equiv_nat

Modified src/data/fintype.lean
- \+ *lemma* not_nonempty_fintype

Modified src/data/rat/denumerable.lean
- \+ *lemma* mk_rat

Created src/data/real/cardinality.lean
- \+ *lemma* cantor_function_aux_tt
- \+ *lemma* cantor_function_aux_ff
- \+ *lemma* cantor_function_aux_nonneg
- \+ *lemma* cantor_function_aux_eq
- \+ *lemma* cantor_function_aux_succ
- \+ *lemma* summable_cantor_function
- \+ *lemma* cantor_function_le
- \+ *lemma* cantor_function_succ
- \+ *lemma* increasing_cantor_function
- \+ *lemma* injective_cantor_function
- \+ *lemma* mk_real
- \+ *lemma* not_countable_real
- \+ *def* cantor_function_aux
- \+ *def* cantor_function

Modified src/set_theory/cardinal.lean
- \+ *lemma* mk_nat
- \+ *lemma* denumerable_iff
- \+ *lemma* mk_int
- \+ *lemma* mk_pnat
- \+/\- *theorem* mul_def
- \+ *theorem* infinite_iff

Modified src/set_theory/ordinal.lean
- \+ *lemma* power_self_eq

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
- \+ *lemma* arrow_congr_apply
- \+ *lemma* arrow_congr_comp
- \+ *lemma* arrow_congr_refl
- \+ *lemma* arrow_congr_trans
- \+ *lemma* arrow_congr_symm
- \+ *lemma* conj_apply
- \+ *lemma* conj_refl
- \+ *lemma* conj_symm
- \+ *lemma* conj_trans
- \+ *lemma* conj_comp
- \+/\- *def* arrow_congr
- \+ *def* conj



## [2019-07-01 19:35:44](https://github.com/leanprover-community/mathlib/commit/a2c291d)
feat(data/mv_polynomial): miscellaneous lemmas on eval, rename, etc ([#1134](https://github.com/leanprover-community/mathlib/pull/1134))
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *lemma* C_pow
- \+ *lemma* C_eq_coe_nat
- \+ *lemma* ext_iff
- \+/\- *lemma* coeff_X
- \+/\- *lemma* eval₂_zero
- \+/\- *lemma* eval₂_add
- \+/\- *lemma* eval₂_monomial
- \+/\- *lemma* eval₂_C
- \+/\- *lemma* eval₂_one
- \+/\- *lemma* eval₂_X
- \+/\- *lemma* eval₂_mul_monomial
- \+/\- *lemma* eval₂_mul
- \+/\- *lemma* eval₂_pow
- \+/\- *lemma* eval₂_comp_left
- \+/\- *lemma* eval₂_eta
- \+ *lemma* eval₂_congr
- \+ *lemma* eval₂_prod
- \+ *lemma* eval₂_sum
- \+ *lemma* eval₂_assoc
- \+ *lemma* map_pow
- \+ *lemma* map_injective
- \+ *lemma* eval₂_rename
- \+ *lemma* rename_eval₂
- \+ *lemma* rename_prodmk_eval₂
- \+ *lemma* eval₂_rename_prodmk
- \+ *lemma* eval_rename_prodmk
- \+/\- *def* eval₂



## [2019-07-01 17:57:38](https://github.com/leanprover-community/mathlib/commit/fcfa2a4)
refactor(set_theory/ordinal): restate well_ordering_thm ([#1115](https://github.com/leanprover-community/mathlib/pull/1115))
Define the relation rather than using an `exists` statement
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \- *theorem* well_ordering_thm
- \+ *def* well_ordering_rel



## [2019-07-01 17:01:12](https://github.com/leanprover-community/mathlib/commit/f0bf43b)
feat(order/zorn): chain.image ([#1084](https://github.com/leanprover-community/mathlib/pull/1084))
* feat(order/zorn): chain.image
* golf
#### Estimated changes
Modified src/order/zorn.lean
- \+ *theorem* chain.image

