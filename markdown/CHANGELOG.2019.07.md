### [2019-07-31 16:48:18](https://github.com/leanprover-community/mathlib/commit/49be50f)
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

### [2019-07-31 14:37:08](https://github.com/leanprover-community/mathlib/commit/88d60dc)
feat(data/pnat/basic): coe_bit0 and coe_bit1 ([#1288](https://github.com/leanprover-community/mathlib/pull/1288))

### [2019-07-31 13:28:58](https://github.com/leanprover-community/mathlib/commit/53680f9)
feat(data/matrix): mul_sum and sum_mul ([#1253](https://github.com/leanprover-community/mathlib/pull/1253))
* feat(data/matrix): mul_sum and sum_mul
* Update matrix.lean
* add comment explaing funny proof

### [2019-07-31 10:41:10](https://github.com/leanprover-community/mathlib/commit/da46b32)
feat(tactic/symmetry_at): apply symmetry on assumptions ([#1269](https://github.com/leanprover-community/mathlib/pull/1269))
* feat(tactic/symmetry_at): apply symmetry on assumptions
* add docstrings

### [2019-07-31 08:37:56](https://github.com/leanprover-community/mathlib/commit/badeb48)
feat(data/equiv/algebra): change mul_equiv field to map_mul ([#1287](https://github.com/leanprover-community/mathlib/pull/1287))
* feat(data/equiv/algebra): bundle field for mul_equiv
* adding docs
* Update src/data/equiv/algebra.lean
* Update src/data/equiv/algebra.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>

### [2019-07-30 11:45:46](https://github.com/leanprover-community/mathlib/commit/9d589d7)
feat(data/nat/fib): add Fibonacci sequence ([#1279](https://github.com/leanprover-community/mathlib/pull/1279))

### [2019-07-30 06:58:24](https://github.com/leanprover-community/mathlib/commit/0b47675)
feat(algebra,data/complex/exponential): add abs_neg_one_pow, remove hyp from div_le_div_of_le_left ([#1280](https://github.com/leanprover-community/mathlib/pull/1280))

### [2019-07-29 21:10:06](https://github.com/leanprover-community/mathlib/commit/132bc56)
doc(windows.md): clarify windows instructions ([#1165](https://github.com/leanprover-community/mathlib/pull/1165))
* doc(windows.md): clarify windows instructions
* fix headers
* remove msys2 from windows installation instructions
* fix sentence
* typo
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* doc(windows.md): small changes
typos, and explicitly discourage msys2

### [2019-07-29 16:17:43](https://github.com/leanprover-community/mathlib/commit/363f187)
feat(tactic/extract_goal): create stand-alone examples out of current goal ([#1233](https://github.com/leanprover-community/mathlib/pull/1233))
* feat(tactic/extract_example): create stand-alone examples out of current goal
* feat(tactic/extract_example): add formatting and options
* feat(tactic/extract_goal): rename to `extract_goal`
* Update src/tactic/interactive.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* make instances anonymous when the name starts with `_`
* add doc strings
* feat(tactic/interactive): exact_goal works on defs

### [2019-07-29 14:13:00](https://github.com/leanprover-community/mathlib/commit/ee15f68)
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

### [2019-07-29 11:22:47](https://github.com/leanprover-community/mathlib/commit/5adeebf)
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

### [2019-07-28 10:35:05](https://github.com/leanprover-community/mathlib/commit/879da1c)
fix(algebraic_geometry/presheafedspace): fix lame proofs ([#1273](https://github.com/leanprover-community/mathlib/pull/1273))
* fix(algebraic_geometry/presheafedspace): fix lame proofs
* fix
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-07-28 05:13:16](https://github.com/leanprover-community/mathlib/commit/9689f4d)
feat(tactic/interactive): move `rotate` into interactive namespace ([#1272](https://github.com/leanprover-community/mathlib/pull/1272))
also document `swap`
Add test

### [2019-07-25 14:09:56+02:00](https://github.com/leanprover-community/mathlib/commit/d5a5393)
doc(contribute/index.md): add line about large PRs [ci skip] ([#1267](https://github.com/leanprover-community/mathlib/pull/1267))

### [2019-07-25 10:40:50](https://github.com/leanprover-community/mathlib/commit/03c0d6c)
feat(algebra/group/basic): add_add_neg_cancel'_right ([#1261](https://github.com/leanprover-community/mathlib/pull/1261))
* feat(algebra/group/basic): add_add_neg_cancel'_right
* fix build

### [2019-07-25 10:48:28+02:00](https://github.com/leanprover-community/mathlib/commit/926467d)
doc(contribute/style.md): fix section on comments [ci skip] ([#1265](https://github.com/leanprover-community/mathlib/pull/1265))

### [2019-07-25 08:45:56](https://github.com/leanprover-community/mathlib/commit/1000ae8)
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

### [2019-07-24 15:32:15](https://github.com/leanprover-community/mathlib/commit/5125f11)
feat(data/matrix): smul_val ([#1262](https://github.com/leanprover-community/mathlib/pull/1262))
* feat(data/matrix): smul_val
* Update src/data/matrix.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-07-24 11:03:46](https://github.com/leanprover-community/mathlib/commit/ed57916)
feat(category_theory): functions to convert is_lawful_functor and is_… ([#1258](https://github.com/leanprover-community/mathlib/pull/1258))
* feat(category_theory): functions to convert is_lawful_functor and is_lawful_monad to their corresponding category_theory concepts
* Fix typo
* feat(category): add mjoin_map_pure, mjoin_pure to the simpset (and use <$> notation)

### [2019-07-24 05:14:48](https://github.com/leanprover-community/mathlib/commit/b0c5251)
cleanup(category_theory/monoidal): use equiv on prod/punit intead of adding new constants ([#1257](https://github.com/leanprover-community/mathlib/pull/1257))

### [2019-07-23 11:10:07](https://github.com/leanprover-community/mathlib/commit/4a5529a)
feat(data/array): add some simp attributes ([#1255](https://github.com/leanprover-community/mathlib/pull/1255))

### [2019-07-22 19:45:42](https://github.com/leanprover-community/mathlib/commit/a33315d)
feat(linear_algebra/dim): findim equivalence ([#1217](https://github.com/leanprover-community/mathlib/pull/1217))
* feat(linear_algebra/dim): findim equivalence
* feat(linear_algebra/dim): two versions of dim_fun
* feat(linear_algebra/dim): clean up

### [2019-07-22 16:29:29](https://github.com/leanprover-community/mathlib/commit/3e77fec)
feat(linear_algebra/finite_dimensional): finite dimensional vector spaces ([#1241](https://github.com/leanprover-community/mathlib/pull/1241))
* feat(linear_algebra/finite_dimensional): finite dimensional vector spaces
* rw `of_span_finite_eq_top` to `of_fg`
* prove infinite.nat_embedding
* generalize finite_of_linear_independent to noetherian modules
* fix build
* fix build (ring_theory/polynomial)

### [2019-07-22 11:20:31](https://github.com/leanprover-community/mathlib/commit/fd91660)
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

### [2019-07-22 08:00:24](https://github.com/leanprover-community/mathlib/commit/7c09ed5)
feat(category_theory/*): define `Cat` and a fully faithful functor `Mon ⥤ Cat` ([#1235](https://github.com/leanprover-community/mathlib/pull/1235))
* feat(category_theory/*): define `Cat` and a fully faithful functor `Mon ⥤ Cat`
* Drop 2 commas
* Drop `functor.id_comp` etc, add `Cat.str` instance, adjust module-level comments
* Make `α` and `β` arguments of `map_hom_equiv` explicit
This way `e α β f` is automatically interpreted as `(e α β).to_fun f`.

### [2019-07-22 09:13:12+02:00](https://github.com/leanprover-community/mathlib/commit/b5a641e)
chore(data/polynomial): clean up commented code ([#1251](https://github.com/leanprover-community/mathlib/pull/1251))
Commented code that wasn't removed after a refactor.

### [2019-07-22 01:35:42](https://github.com/leanprover-community/mathlib/commit/f24dc98)
feat(logic/unique): forall_iff and exists_iff ([#1249](https://github.com/leanprover-community/mathlib/pull/1249))
Maybe these should be `@[simp]`. My use case in `fin 1` and it's slightly annoying to have `default (fin 1)` everwhere instead of `0`, but maybe that should also be a `@[simp]` lemma.

### [2019-07-22 01:13:25](https://github.com/leanprover-community/mathlib/commit/a8c2923)
refactor(ring_theory/noetherian): change order of instance arguments ([#1250](https://github.com/leanprover-community/mathlib/pull/1250))
Zulip discussion https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Type.20class.20failure
This change makes some type class searches work better.

### [2019-07-20 18:50:28](https://github.com/leanprover-community/mathlib/commit/93419b3)
chore(data/equiv/algebra): add `ring.to_mul/add_equiv`, DRY ([#1247](https://github.com/leanprover-community/mathlib/pull/1247))

### [2019-07-20 17:33:46](https://github.com/leanprover-community/mathlib/commit/d371da6)
fix(group_theory/subgroup): fix some typos introduced in 66a86ffe0 ([#1246](https://github.com/leanprover-community/mathlib/pull/1246))

### [2019-07-20 06:49:37](https://github.com/leanprover-community/mathlib/commit/6e3516d)
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

### [2019-07-19 17:09:12](https://github.com/leanprover-community/mathlib/commit/9505e5b)
fix(data/matrix): use pi.module for the module structure ([#1242](https://github.com/leanprover-community/mathlib/pull/1242))
* fix(data/matrix): use pi.module for the module structure
* Update matrix.lean
* Update matrix.lean
* Update matrix.lean

### [2019-07-19 14:39:27](https://github.com/leanprover-community/mathlib/commit/07ae80f)
refactor(algebra/*): delete `free_monoid` from `algebra/free`, restore some functions in `algebra/group/with_one` ([#1227](https://github.com/leanprover-community/mathlib/pull/1227))
* refactor(algebra/*): Remove `free_monoid` from `algebra/free`, fixes [#929](https://github.com/leanprover-community/mathlib/pull/929)
* use `namespace with_one`
* Add `with_one.coe_is_mul_hom`
* Restore `with_one.lift` etc from `algebra/free` `free_monoid.lift` etc
* Define `with_one.map` based on the deleted `free_monoid.map`
Define using `option.map`, and prove equivalence to `λ f, lift $ coe ∘ f`.

### [2019-07-19 14:09:02](https://github.com/leanprover-community/mathlib/commit/74754ac)
feat(analysis/calculus/times_cont_diff): multiple differentiability ([#1226](https://github.com/leanprover-community/mathlib/pull/1226))
* feat(analysis/calculus/times_cont_diff): multiple differentiability
* style
* style
* style and documentation
* better wording

### [2019-07-18 15:15:54](https://github.com/leanprover-community/mathlib/commit/8b102eb)
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

### [2019-07-18 06:27:03](https://github.com/leanprover-community/mathlib/commit/e704f94)
fix(data/{nat,int}/parity): fix definition of 'even' ([#1240](https://github.com/leanprover-community/mathlib/pull/1240))

### [2019-07-17 17:57:06+02:00](https://github.com/leanprover-community/mathlib/commit/86e7287)
fix(data/zmod/basic) remove unused argument from instance ([#1239](https://github.com/leanprover-community/mathlib/pull/1239))

### [2019-07-17 09:56:01](https://github.com/leanprover-community/mathlib/commit/d6fd044)
feat(*): add nat.antidiagonal and use it for polynomial.mul_coeff ([#1237](https://github.com/leanprover-community/mathlib/pull/1237))

### [2019-07-16 22:00:41](https://github.com/leanprover-community/mathlib/commit/8785bd0)
refactor(data/multiset): rename diagonal to antidiagonal ([#1236](https://github.com/leanprover-community/mathlib/pull/1236))
* refactor(data/multiset): rename diagonal to antidiagonal
* Add docstrings
* fix build
* Fix build

### [2019-07-16 21:01:49](https://github.com/leanprover-community/mathlib/commit/e186fbb)
feat(data/mv_polynomial): coeff_mul ([#1216](https://github.com/leanprover-community/mathlib/pull/1216))
* feat(data/mv_polynomial): coeff_mul
* refactor(data/multiset): rename diagonal to antidiagonal
* Rename diagonal to antidiagonal
* Define antidiagonal as to_finsupp instead of to_finset
* Add docstrings
* fix build
* Fix build

### [2019-07-15 21:35:36](https://github.com/leanprover-community/mathlib/commit/92ac50c)
chore(data/finset): rename le_min_of_mem to min_le_of_mem ([#1231](https://github.com/leanprover-community/mathlib/pull/1231))
* chore(data/finset): rename le_min_of_mem to min_le_of_mem
* fix build

### [2019-07-15 14:48:52](https://github.com/leanprover-community/mathlib/commit/7217f13)
feat(data/option/basic): bind_eq_none ([#1232](https://github.com/leanprover-community/mathlib/pull/1232))
* feat(data/option/basis): bind_eq_none
* delete extra line

### [2019-07-15 13:09:35](https://github.com/leanprover-community/mathlib/commit/46074fc)
chore(data/fintype): change `unique.fintype` to priority 0 ([#1230](https://github.com/leanprover-community/mathlib/pull/1230))

### [2019-07-15 00:44:50](https://github.com/leanprover-community/mathlib/commit/0e9ac84)
feat(tactic/rcases): add obtain tactic ([#1218](https://github.com/leanprover-community/mathlib/pull/1218))
* feat(tactic/rcases): add obtain tactic
* style(tactic/rcases): line break
* doc(docs/tactics): document obtain
* feat(tactic/obtain): support := syntax

### [2019-07-14 11:14:14](https://github.com/leanprover-community/mathlib/commit/dcf0130)
feat(data/pequiv): partial equivalences ([#1206](https://github.com/leanprover-community/mathlib/pull/1206))
* feat(data/pequiv): partial equivalences
* Update src/data/pequiv.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
* use notation

### [2019-07-14 05:25:05](https://github.com/leanprover-community/mathlib/commit/03e6d0e)
chore(algebra/group/hom): add `is_monoid_hom.of_mul`, use it ([#1225](https://github.com/leanprover-community/mathlib/pull/1225))
* Let `to_additive` generate `is_add_monoid_hom.map_add`
* Converting `is_mul_hom` into `is_monoid_hom` doesn't require `α` to be a group
* Simplify the proof of `is_add_group_hom.map_sub`
Avoid `simp` (without `only`)

### [2019-07-13 20:54:54](https://github.com/leanprover-community/mathlib/commit/51f2645)
feat(pformat): provide `trace!` and `fail!` and allow tactic values ([#1222](https://github.com/leanprover-community/mathlib/pull/1222))

### [2019-07-13 18:17:06](https://github.com/leanprover-community/mathlib/commit/a1cfc5c)
feat(logic,data/equiv,prod): various lemmas ([#1224](https://github.com/leanprover-community/mathlib/pull/1224))
* feat(logic,data/equiv,prod): various lemmas
* Update basic.lean
* Update basic.lean

### [2019-07-13 16:25:07](https://github.com/leanprover-community/mathlib/commit/0eea0d9)
feat(data/{nat,int}/parity): the 'even' predicate on nat and int ([#1219](https://github.com/leanprover-community/mathlib/pull/1219))
* feat(data/{nat,int}/parity): the 'even' predicate on nat and int
* fix(data/{nat,int}/parity): shorten proof
* delete extra comma

### [2019-07-13 01:46:58](https://github.com/leanprover-community/mathlib/commit/6db5829)
feat(data/finmap): extend the API ([#1223](https://github.com/leanprover-community/mathlib/pull/1223))

### [2019-07-12 21:47:13](https://github.com/leanprover-community/mathlib/commit/5a48be3)
chore(data/src/pending): remove unused folder ([#1221](https://github.com/leanprover-community/mathlib/pull/1221))

### [2019-07-12 20:05:55](https://github.com/leanprover-community/mathlib/commit/fb7dfa1)
feat(data/{nat,int,zmod,finset}): add a few useful facts ([#1220](https://github.com/leanprover-community/mathlib/pull/1220))
* feat(data/finset): add a few useful facts
* feat(data/zmod/basic): express neg in terms of residues
* feat(data/{nat,int}): add theorem 'mod_mod_of_dvd'

### [2019-07-12 01:43:22](https://github.com/leanprover-community/mathlib/commit/3d36966)
feat(analysis/calculus/mean_value): the mean value inequality ([#1212](https://github.com/leanprover-community/mathlib/pull/1212))
* feat(analysis/calculus/mean_value): the mean value inequality
* remove blank lines

### [2019-07-11 21:03:56](https://github.com/leanprover-community/mathlib/commit/7806586)
feat(analysis/calculus/deriv): extended API for derivatives ([#1213](https://github.com/leanprover-community/mathlib/pull/1213))

### [2019-07-11 18:24:16](https://github.com/leanprover-community/mathlib/commit/2511faf)
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

### [2019-07-11 13:58:17](https://github.com/leanprover-community/mathlib/commit/c2cc9a9)
refactor(*): change priority of \simeq ([#1210](https://github.com/leanprover-community/mathlib/pull/1210))
* change priority of \simeq
Also change priority of similar notations
Remove many unnecessary parentheses
* lower precedence on order_embedding and similar
also add parentheses in 1 place where they were needed
* spacing
* add parenthesis

### [2019-07-11 10:12:31](https://github.com/leanprover-community/mathlib/commit/86d0f29)
refactor(*): make `is_group_hom` extend `is_mul_hom` ([#1214](https://github.com/leanprover-community/mathlib/pull/1214))
* map_mul/map_add: use explicit parameters
Preparing to merge `is_mul_hom` with `is_group_hom`
* make `is_group_hom` extend `is_mul_hom`, adjust many proof terms
* Add a comment

### [2019-07-11 07:41:05](https://github.com/leanprover-community/mathlib/commit/1b1c64b)
perf(algebraic_geometry/presheafed_space): replace/optimize tidy scripts ([#1204](https://github.com/leanprover-community/mathlib/pull/1204))
* perf(algebraic_geometry/presheafed_space): replace/optimize tidy scripts
This file now takes 20 seconds to compile on my desktop instead of 160. This is a 9% speedup to mathlib overall.
* doc(algebraic_geometry/presheafed_space): comments

### [2019-07-11 04:18:40](https://github.com/leanprover-community/mathlib/commit/cc5870d)
feat(algebra/ordered_ring): with_top.nat_induction ([#1211](https://github.com/leanprover-community/mathlib/pull/1211))

### [2019-07-10 21:33:20](https://github.com/leanprover-community/mathlib/commit/5cdebb7)
feat(*): Miscellaneous lemmas in algebra ([#1188](https://github.com/leanprover-community/mathlib/pull/1188))
* Trying things out
* feat(ring_theory/*): Misc little lemmas
* More little lemmas

### [2019-07-10 19:39:24](https://github.com/leanprover-community/mathlib/commit/5aebdc4)
fix(*): fix line endings ([#1209](https://github.com/leanprover-community/mathlib/pull/1209))

### [2019-07-10 18:25:32](https://github.com/leanprover-community/mathlib/commit/0bc4a50)
feat(tactic/apply_fun): adds `apply_fun` tactic ([#1184](https://github.com/leanprover-community/mathlib/pull/1184))
* feat(tactic/apply_fun): adds `apply_fun` tactic
* move tests to test folder
* elaborate function with expected type
* fix merge mistake

### [2019-07-10 15:57:51](https://github.com/leanprover-community/mathlib/commit/d2b4380)
feat(data/list/basic): list.prod_range_succ, list.sum_range_succ ([#1197](https://github.com/leanprover-community/mathlib/pull/1197))
* feat(data/list/basic): list.prod_range_succ, list.sum_range_succ
* changes from review
* remove simp
* shorten proof

### [2019-07-10 11:22:33-04:00](https://github.com/leanprover-community/mathlib/commit/8939d95)
docs(contribute/index.md): [#1131](https://github.com/leanprover-community/mathlib/pull/1131) [skip ci]

### [2019-07-10 09:10:06-04:00](https://github.com/leanprover-community/mathlib/commit/b00460c)
doc(README): Add link to website

### [2019-07-10 05:49:09](https://github.com/leanprover-community/mathlib/commit/fb1848b)
refactor(topology/algebra/open_subgroup) Finish TODO ([#1202](https://github.com/leanprover-community/mathlib/pull/1202))
* Create .DS_Store
* Revert "Create .DS_Store"
This reverts commit 5612886d493aef59205eddc5a34a75e6e5ba22c1.
* Finish TODO
* Update src/topology/algebra/open_subgroup.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-07-10 02:24:53](https://github.com/leanprover-community/mathlib/commit/e25a597)
feat(analysis/calculus/tangent_cone): more properties of the tangent cone ([#1136](https://github.com/leanprover-community/mathlib/pull/1136))

### [2019-07-10 00:10:18](https://github.com/leanprover-community/mathlib/commit/0cd0d4e)
feat(meta/pformat): format! macro using `pp` instead of `to_fmt` ([#1194](https://github.com/leanprover-community/mathlib/pull/1194))
* feat(meta/pformat): format! macro which uses `pp` instead of `to_fmt`
* Update core.lean

### [2019-07-09 22:27:43](https://github.com/leanprover-community/mathlib/commit/60e4bb9)
refactor(category_theory/endomorphism): move to a dedicated file; prove simple lemmas ([#1195](https://github.com/leanprover-community/mathlib/pull/1195))
* Move definitions of `End` and `Aut` to a dedicated file
* Adjust some proofs, use `namespace`, add docstrings
* `functor.map` and `functor.map_iso` define homomorphisms of `End/Aut`
* Define `functor.map_End` and `functor.map_Aut`

### [2019-07-09 20:34:02](https://github.com/leanprover-community/mathlib/commit/3a7c661)
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

### [2019-07-09 15:55:54](https://github.com/leanprover-community/mathlib/commit/0460815)
fix(docs/tactics): fix code block ([#1201](https://github.com/leanprover-community/mathlib/pull/1201))

### [2019-07-09 15:04:11](https://github.com/leanprover-community/mathlib/commit/0099f06)
perf(data/polynomial, field_theory/splitting_field): memory problems ([#1200](https://github.com/leanprover-community/mathlib/pull/1200))
* perf(data/polynomial): avoid bad instance search
* perf(field_theory/splitting_field): local intance priority makes a big difference

### [2019-07-09 12:15:39](https://github.com/leanprover-community/mathlib/commit/13f76d3)
feat(tactic): add `convert_to` and `ac_change` ([#944](https://github.com/leanprover-community/mathlib/pull/944))
* feat(tactic): add `convert_to` and `ac_change`
* style fixes

### [2019-07-09 13:05:07+02:00](https://github.com/leanprover-community/mathlib/commit/d50f634)
feat(data/matrix): simp attributes on one_mul and mul_one ([#1199](https://github.com/leanprover-community/mathlib/pull/1199))

### [2019-07-09 11:06:35+02:00](https://github.com/leanprover-community/mathlib/commit/6670e66)
feat(data/matrix): simp attributes on zero_mul and mul_zero ([#1198](https://github.com/leanprover-community/mathlib/pull/1198))

### [2019-07-09 09:00:44](https://github.com/leanprover-community/mathlib/commit/9071969)
feat(data/nat/basic): some nat inequalities ([#1189](https://github.com/leanprover-community/mathlib/pull/1189))
* feat(data/nat/basic): some inequalities
* remove redundant lemmas
* simplify proofs
* make implicit
* shorter proof
* rename

### [2019-07-08 20:51:06-04:00](https://github.com/leanprover-community/mathlib/commit/7fc3283)
fix(README.md): Remove the AppVeyor badge [skip ci] ([#1192](https://github.com/leanprover-community/mathlib/pull/1192))
It seems to me that we don't really care about whether the AppVeyor build fails or not. And I don't like the red badge. So I propose to remove it.

### [2019-07-09 00:20:18+02:00](https://github.com/leanprover-community/mathlib/commit/0cc67a1)
chore(data/matrix): remove unnecessary decidable_eq ([#1196](https://github.com/leanprover-community/mathlib/pull/1196))
This was generating annoying `decidable_eq (fin n)` goals when rewriting.

### [2019-07-07 20:48:20](https://github.com/leanprover-community/mathlib/commit/8917419)
chore(data/equiv/algebra): use `to_additive` ([#1191](https://github.com/leanprover-community/mathlib/pull/1191))
- Define `add_equiv` and `add_equiv.*` using `to_additive`
- Simplify some instances

### [2019-07-06 22:30:41](https://github.com/leanprover-community/mathlib/commit/55b0b80)
fix(src/logic/basic): add [symm] attribute to ne. ([#1190](https://github.com/leanprover-community/mathlib/pull/1190))

### [2019-07-06 11:29:31](https://github.com/leanprover-community/mathlib/commit/ccf5636)
feat(data/option/basic): not_is_some_iff_eq_none and ne_none_iff_is_some ([#1186](https://github.com/leanprover-community/mathlib/pull/1186))

### [2019-07-05 20:30:47](https://github.com/leanprover-community/mathlib/commit/12763b9)
chore(algebra/group/type_tags): add some missing instances ([#1164](https://github.com/leanprover-community/mathlib/pull/1164))
* chore(algebra/group/type_tags): add some missing instances
* Drop an unused import

### [2019-07-05 17:03:44](https://github.com/leanprover-community/mathlib/commit/05283d2)
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

### [2019-07-05 15:44:22](https://github.com/leanprover-community/mathlib/commit/05550ea)
feat(category_theory/limits): equivalences create limits ([#1175](https://github.com/leanprover-community/mathlib/pull/1175))
* feat(category_theory/limits): equivalences create limits
* equivalence lemma
* add @[simp]
* use right_adjoint_preserves_limits
* undo weird changes in topology files
* formatting
* do colimits too

### [2019-07-05 05:31:07](https://github.com/leanprover-community/mathlib/commit/27ae77c)
feat(tactic/tidy): lower the priority of ext in tidy ([#1178](https://github.com/leanprover-community/mathlib/pull/1178))
* feat(category_theory/adjunction): additional simp lemmas
* experimenting with deferring ext in tidy
* abbreviate some proofs
* refactoring CommRing/adjunctions
* renaming

### [2019-07-05 05:02:40](https://github.com/leanprover-community/mathlib/commit/4af3976)
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

### [2019-07-04 19:49:02](https://github.com/leanprover-community/mathlib/commit/569bcf9)
feat(algebra/ordered_group): eq_of_abs_non_pos ([#1185](https://github.com/leanprover-community/mathlib/pull/1185))
* feat(algebra/ordered_group): decidable_linear_ordered_comm_group.eq_of_abs_non_pos
* fix(algebra/ordered_group): new line and name

### [2019-07-04 18:17:29](https://github.com/leanprover-community/mathlib/commit/c5d4140)
feat(data/fin): fin.mk.inj_iff ([#1182](https://github.com/leanprover-community/mathlib/pull/1182))
Quite surprised this insn't already there.

### [2019-07-04 16:47:39](https://github.com/leanprover-community/mathlib/commit/1723bee)
chore(algebra/order_functions): some proofs work for semirings ([#1183](https://github.com/leanprover-community/mathlib/pull/1183))
* chore(algebra/order_functions): some proofs work for semirings, not only rings
* Update order_functions.lean

### [2019-07-04 14:31:11](https://github.com/leanprover-community/mathlib/commit/0818bb2)
feat(data/fin): mem_find_of_unique ([#1181](https://github.com/leanprover-community/mathlib/pull/1181))

### [2019-07-04 12:14:42](https://github.com/leanprover-community/mathlib/commit/32ce121)
chore(topology/maps.lean): Delete a redundant argument ([#1179](https://github.com/leanprover-community/mathlib/pull/1179))
* Create .DS_Store
* Revert "Create .DS_Store"
This reverts commit 5612886d493aef59205eddc5a34a75e6e5ba22c1.
* Redundant argument

### [2019-07-04 10:24:53](https://github.com/leanprover-community/mathlib/commit/34d69b5)
chore(data/set): set.mem_preimage_eq becomes an iff  ([#1174](https://github.com/leanprover-community/mathlib/pull/1174))
* chore(data/set): set.mem_preimage_eq becomes an iff named set.mem_preimage
* fix(measure_theory/measurable_space): proof broken by mem_preimage
change
* fix(data/filter/basic)
* fix(topology/uniform_space/separation)
* fix(measure_theory/integration)

### [2019-07-04 08:45:49](https://github.com/leanprover-community/mathlib/commit/6493bb6)
feat(data/list/basic): nodup_update_nth, mem_diff_iff_of_nodup ([#1170](https://github.com/leanprover-community/mathlib/pull/1170))

### [2019-07-04 06:57:24](https://github.com/leanprover-community/mathlib/commit/00de1cb)
feat(data/list/basic): list.nodup_diff ([#1168](https://github.com/leanprover-community/mathlib/pull/1168))
* feat(data/list/basic): list.nodup_diff
* Update basic.lean
* Update basic.lean

### [2019-07-04 05:16:33](https://github.com/leanprover-community/mathlib/commit/e6b9696)
feat(data/option): not_mem_none and bind_assoc ([#1177](https://github.com/leanprover-community/mathlib/pull/1177))

### [2019-07-04 03:33:42](https://github.com/leanprover-community/mathlib/commit/4cca114)
feat(data/fin): fin.find ([#1167](https://github.com/leanprover-community/mathlib/pull/1167))
* feat(data/fin): fin.find
* add nat_find_mem_find

### [2019-07-04 01:39:56](https://github.com/leanprover-community/mathlib/commit/3ee1f85)
feat(order/basic): order_dual.inhabited ([#1163](https://github.com/leanprover-community/mathlib/pull/1163))

### [2019-07-03 23:52:50](https://github.com/leanprover-community/mathlib/commit/ae9615c)
feat(order/pilex): lexicographic ordering on pi types ([#1157](https://github.com/leanprover-community/mathlib/pull/1157))
* feat(order/pilex): lexicographic ordering on pi types
* fix instance name
* fix instance name properly
* Update basic.lean
* remove unnecessary import

### [2019-07-03 22:09:24](https://github.com/leanprover-community/mathlib/commit/992354c)
feat(data/fintype): well_foundedness lemmas on fintypes ([#1156](https://github.com/leanprover-community/mathlib/pull/1156))
* feat(data/fintype): well_foundedness lemmas on fintypes
* Update fintype.lean
* minor fixes

### [2019-07-03 18:10:52](https://github.com/leanprover-community/mathlib/commit/cb84234)
feat(category_theory/yoneda): coyoneda lemmas ([#1172](https://github.com/leanprover-community/mathlib/pull/1172))
* feat(category_theory/yoneda): coyoneda lemmas
* oops, didn't include everything I needed
* oops
* removing fully_faithful
* missing underscore...

### [2019-07-03 15:25:41](https://github.com/leanprover-community/mathlib/commit/e4ee18b)
feat(category_theory/adjunction): additional simp lemmas ([#1143](https://github.com/leanprover-community/mathlib/pull/1143))
* feat(category_theory/adjunction): additional simp lemmas
* spaces
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-07-03 12:44:32](https://github.com/leanprover-community/mathlib/commit/f1b5473)
feat(data/list/basic): fin_range ([#1159](https://github.com/leanprover-community/mathlib/pull/1159))
* feat(data/list/basic): fin_range
fin_range is like `list.range` but returns a `list (fin n)` instead of a `list nat`
* Update basic.lean

### [2019-07-03 09:42:00](https://github.com/leanprover-community/mathlib/commit/d2c5309)
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

### [2019-07-03 09:02:02](https://github.com/leanprover-community/mathlib/commit/9a33885)
chore(data/matrix): rows and columns the right way around ([#1171](https://github.com/leanprover-community/mathlib/pull/1171))
* chore(data/matrix): rows and columns the right way around
* update matrix.lean

### [2019-07-03 00:58:19](https://github.com/leanprover-community/mathlib/commit/fd5617c)
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

### [2019-07-02 13:11:09](https://github.com/leanprover-community/mathlib/commit/1ef2c2d)
feat(data/list/basic): filter_true and filter_false ([#1169](https://github.com/leanprover-community/mathlib/pull/1169))
* feat(data/list/basic): filter_true and filter_false
* Update basic.lean
* Update basic.lean
* Update basic.lean
* Update basic.lean

### [2019-07-02 11:28:23](https://github.com/leanprover-community/mathlib/commit/b4989a0)
compute the cardinality of real ([#1096](https://github.com/leanprover-community/mathlib/pull/1096))
* compute the cardinality of real
* minor improvements
* fix(data/rat/denumerable): change namespace of of_rat
* style(src/topology/algebra/infinite_sum): structure proof

### [2019-07-02 04:29:06](https://github.com/leanprover-community/mathlib/commit/57b57b3)
feat(data/equiv/basic): improve arrow_congr, define conj ([#1119](https://github.com/leanprover-community/mathlib/pull/1119))
* feat(data/equiv/basic): improve arrow_congr, define conj
- redefine `equiv.arrow_congr` without an enclosing `match`
- prove some trivial lemmas about `equiv.arrow_congr`
- define `equiv.conj`, and prove trivial lemmas about it
* chore(data/equiv/basic): add @[simp]
Also split some long lines, and swap lhs with rhs in a few lemmas.
* Reorder, drop TODO

### [2019-07-01 19:35:44](https://github.com/leanprover-community/mathlib/commit/a2c291d)
feat(data/mv_polynomial): miscellaneous lemmas on eval, rename, etc ([#1134](https://github.com/leanprover-community/mathlib/pull/1134))

### [2019-07-01 17:57:38](https://github.com/leanprover-community/mathlib/commit/fcfa2a4)
refactor(set_theory/ordinal): restate well_ordering_thm ([#1115](https://github.com/leanprover-community/mathlib/pull/1115))
Define the relation rather than using an `exists` statement

### [2019-07-01 17:01:12](https://github.com/leanprover-community/mathlib/commit/f0bf43b)
feat(order/zorn): chain.image ([#1084](https://github.com/leanprover-community/mathlib/pull/1084))
* feat(order/zorn): chain.image
* golf