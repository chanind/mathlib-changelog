### [2019-08-31 22:37:28](https://github.com/leanprover-community/mathlib/commit/df65dde)
feat(data/option/basic): eq_some_iff_get_eq ([#1370](https://github.com/leanprover-community/mathlib/pull/1370))
* feat(data/option/basic): eq_some_iff_get_eq
* Update basic.lean

### [2019-08-31 20:38:30](https://github.com/leanprover-community/mathlib/commit/72ce940)
feat(category_theory/limits/of_nat_iso): missing parts of the limits API ([#1355](https://github.com/leanprover-community/mathlib/pull/1355))
* feat(category_theory/limits/of_nat_isp)
* Update src/category_theory/limits/limits.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/category_theory/limits/limits.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* use @[reassoc]
* fixing after rename
* fix renaming

### [2019-08-30 20:07:24](https://github.com/leanprover-community/mathlib/commit/455f060)
chore(unicode): improve arrows ([#1373](https://github.com/leanprover-community/mathlib/pull/1373))
* chore(unicode): improve arrows
* grammar
Co-Authored-By: Johan Commelin <johan@commelin.net>
* moar

### [2019-08-30 13:16:52-04:00](https://github.com/leanprover-community/mathlib/commit/4c5c4dc)
doc(contribute): add detailed instructions for cache-olean [skip ci] ([#1367](https://github.com/leanprover-community/mathlib/pull/1367))

### [2019-08-30 16:13:59](https://github.com/leanprover-community/mathlib/commit/2db7fa4)
feat(sanity_check): improve sanity_check ([#1369](https://github.com/leanprover-community/mathlib/pull/1369))
* feat(sanity_check): improve sanity_check
- add hole command for sanity check (note: hole commands only work when an expression is expected, not when a command is expected, which is unfortunate)
- print the type of the unused arguments
- print whether an unused argument is a duplicate
- better check to filter automatically generated declarations
- do not print arguments of type `parse _`
- The binding brackets from `tactic.where` are moved to `meta.expr`. The definition is changed so that strict implicit arguments are printed as `{{ ... }}`
* typos
* improve docstring
* Also check for duplicated namespaces
Fun fact: I had to remove an unused argument from `decidable_chain'` for my function to work.

### [2019-08-30 11:48:46](https://github.com/leanprover-community/mathlib/commit/afe51c7)
feat(category_theory/limits): special shapes ([#1339](https://github.com/leanprover-community/mathlib/pull/1339))
* providing minimal API for limits of special shapes
* apis for special shapes
* fintype instances
* associators, unitors, braidings for binary product
* map
* instances
* assoc lemma
* coprod
* fix import
* names
* adding some docs
* updating tutorial on limits
* minor
* uniqueness of morphisms to terminal object
* better treatment of has_terminal
* various
* not there yet
* deleting a dumb file
* remove constructions for a later PR
* use @[reassoc]
* Update src/category_theory/limits/shapes/finite_products.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* improving the colimits tutorial
* minor
* notation for `prod_obj` and `sigma_obj`.
* reverting to `condition`
* implicit arguments
* more implicit arguments
* minor
* notational for initial and terminal objects
* various
* fix notation priorities
* remove unused case bash tactic
* fix whitespace
* comment
* notations

### [2019-08-29 21:31:25](https://github.com/leanprover-community/mathlib/commit/1278efd)
Fix `tactic.exact` timeout in `apply'` ([#1371](https://github.com/leanprover-community/mathlib/pull/1371))
Sometimes `tactic.exact` may timeout for no reason. See zulip discussion https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.60apply'.60timeout/near/174415043

### [2019-08-29 12:31:24](https://github.com/leanprover-community/mathlib/commit/1ff3585)
feat(analysis/calculus/times_cont_diff): adding a lemma ([#1358](https://github.com/leanprover-community/mathlib/pull/1358))
* feat(analysis/calculus/times_cont_diff): adding a lemma
* doc
* change k to \bbk

### [2019-08-28 21:31:26](https://github.com/leanprover-community/mathlib/commit/3b19503)
refactor(category_theory/single_obj): migrate to bundled morphisms ([#1330](https://github.com/leanprover-community/mathlib/pull/1330))
* Define equivalence between `{ f // is_monoid_hom f }` and `monoid_hom`
* Migrate `single_obj` to bundled homomorphisms
Fix a bug in `to_End`: the old implementation used a wrong monoid
structure on `End`.
* Fix `Mon.hom_equiv_monoid_hom` as suggested by @jcommelin

### [2019-08-28 16:20:58](https://github.com/leanprover-community/mathlib/commit/d4c1c0f)
fix(tactic.basic): add sanity_check import ([#1365](https://github.com/leanprover-community/mathlib/pull/1365))

### [2019-08-28 10:14:09](https://github.com/leanprover-community/mathlib/commit/721d67a)
fix(topology/uniform_space): sanity_check pass ([#1364](https://github.com/leanprover-community/mathlib/pull/1364))

### [2019-08-28 09:17:30](https://github.com/leanprover-community/mathlib/commit/79dccba)
refactor: change field notation from k to \bbk ([#1363](https://github.com/leanprover-community/mathlib/pull/1363))
* refactor: change field notation from k to \bbK
* change \bbK to \bbk

### [2019-08-27 23:19:25+02:00](https://github.com/leanprover-community/mathlib/commit/45df75b)
fix(topology/algebra/uniform_group): tiny priority tweak

### [2019-08-26 17:11:07](https://github.com/leanprover-community/mathlib/commit/cc04ba7)
chore(algebra/ring): change semiring_hom to ring_hom ([#1361](https://github.com/leanprover-community/mathlib/pull/1361))
* added bundled ring homs
* removed comment
* Tidy and making docstrings consistent
* fix spacing
* fix typo
Co-Authored-By: Johan Commelin <johan@commelin.net>
* fix typo
Co-Authored-By: Johan Commelin <johan@commelin.net>
* whoops, actually removing instances
* change semiring_hom to ring_hom
* corrected docstring

### [2019-08-26 14:50:25](https://github.com/leanprover-community/mathlib/commit/914c572)
feat(data/rat): add lt, le, and eq def lemmas, move casts into rat to basic ([#1348](https://github.com/leanprover-community/mathlib/pull/1348))

### [2019-08-26 08:13:13](https://github.com/leanprover-community/mathlib/commit/7bc18a8)
feat(data/fin): coe_eq_val and coe_mk ([#1321](https://github.com/leanprover-community/mathlib/pull/1321))

### [2019-08-23 12:07:10+02:00](https://github.com/leanprover-community/mathlib/commit/253a9f7)
fix(docs/install): resize extensions icons for consistency [ci skip]

### [2019-08-23 12:00:49+02:00](https://github.com/leanprover-community/mathlib/commit/91a9b4b)
doc(install/*): new VS-code icon [ci skip]

### [2019-08-23 08:45:41](https://github.com/leanprover-community/mathlib/commit/9a42572)
feat(tactic/apply'): apply without unfolding type definitions ([#1234](https://github.com/leanprover-community/mathlib/pull/1234))
* feat(tactic/apply'): apply without unfolding type definitions
* Update src/tactic/interactive.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* improve doc
* more doc
* Update core.lean
* add test case
* add test case
* improve treatment of type class instances for apply'
* tweak application of instance resolution
* fix
* move `apply'` to its own file
* adjust docs
* import apply from tactic.default
* fix import in test
* Update tactics.lean

### [2019-08-22 18:22:53](https://github.com/leanprover-community/mathlib/commit/f74cc70)
fix(tactic/tauto): use intro1 to deal with negations ([#1354](https://github.com/leanprover-community/mathlib/pull/1354))
* fix(tactic/tauto): use intro1 to deal with negations
* test(tactic/tauto): add tests

### [2019-08-22 15:27:06](https://github.com/leanprover-community/mathlib/commit/40b09aa)
feat(*): small lemmas from the sensitivity formalization ([#1352](https://github.com/leanprover-community/mathlib/pull/1352))
* feat(set_theory/cardinal): norm_cast attributes and extra lemma
* feat(logic/basic): ne.symm_iff
* feat(data/fin): succ_ne_zero
* feat(data/bool): bxor_of_ne
* feat(algebra/big_operators, data/fintype): {finset,fintype}.card_eq_sum_ones
* feat(data/set): range_restrict
* feat(data/finset): inter lemmas
* Reid's corrections
* fixes
* fix cardinal power lemma
* fixes
* Update bool.lean

### [2019-08-22 10:31:24](https://github.com/leanprover-community/mathlib/commit/f442a41)
docs(category/monad,bitraversable): add module docstrings [#1260](https://github.com/leanprover-community/mathlib/pull/1260)  ([#1286](https://github.com/leanprover-community/mathlib/pull/1286))
* docs(category/monad,bitraversable): add module docstrings
* more docs
* still more doc
* doc about traversable

### [2019-08-22 09:32:22+02:00](https://github.com/leanprover-community/mathlib/commit/a489719)
Rename Groupoid.lean to groupoid_category.lean ([#1353](https://github.com/leanprover-community/mathlib/pull/1353))
This fixes a problem with `category_theory/groupoid` and `category_theory/Groupoid` having the same name except for the case of the first letter, which causes a problem on case insensitive file systems.

### [2019-08-21 19:35:06](https://github.com/leanprover-community/mathlib/commit/8de4273)
feat(category_theory/Groupoid): category of groupoids ([#1325](https://github.com/leanprover-community/mathlib/pull/1325))
* feat(category_theory/Groupoid): category of groupoids
* fix comment
* more articles

### [2019-08-21 12:19:41](https://github.com/leanprover-community/mathlib/commit/35144f2)
feat(conv/conv): conv tactics for zooming/saving state ([#1351](https://github.com/leanprover-community/mathlib/pull/1351))
* feat(conv/conv): conv tactics for zooming/saving state
* rob's doc fixes
* nicer docs

### [2019-08-21 11:04:30](https://github.com/leanprover-community/mathlib/commit/3f915fc)
feat(archive): add the cubing a cube proof ([#1343](https://github.com/leanprover-community/mathlib/pull/1343))
* feat(archive): add the cubing a cube proof
* rename file
* add leanpkg configure to travis

### [2019-08-21 05:42:55](https://github.com/leanprover-community/mathlib/commit/c512875)
refactor(*): rewrite `to_additive` attribute ([#1345](https://github.com/leanprover-community/mathlib/pull/1345))
* chore(algebra/group/to_additive): auto add structure fields
* Snapshot
* Rewrite `@[to_additive]`
* Drop more explicit `name` arguments to `to_additive`
* Drop more explicit arguments to `to_additive`
* Map namespaces with `run_cmd to_additive.map_namespace`
* fix(`group_theory/perm/sign`): fix compile
* Fix handling of equational lemmas; fix warnings
* Use `list.mmap'`

### [2019-08-21 03:42:10](https://github.com/leanprover-community/mathlib/commit/733f616)
chore(gitignore): ignore files generated by mk_all script ([#1328](https://github.com/leanprover-community/mathlib/pull/1328))

### [2019-08-21 01:39:40](https://github.com/leanprover-community/mathlib/commit/8070049)
feat(tactic/lift): add lift tactic ([#1315](https://github.com/leanprover-community/mathlib/pull/1315))
* start on lift_to tactic
* finish lift tactic
* add instance to lift rat to int
this required me to move some lemmas from rat/order to rat/basic which had nothing to do with the order on rat
* move test to test/tactic.lean
* add header and documentation
* add more/better documentation
* typo
* more documentation
* rewrite, minor
* move import
* remove can_lift attribute
now we automatically construct the simp set used to simplify
Thanks to @cipher1024 for the idea and writing the main part of this code
* remove occurrence of [can_lift]

### [2019-08-20 23:38:53](https://github.com/leanprover-community/mathlib/commit/26a3e31)
chore(category_theory/monoidal): monoidal_category doesn't extend category ([#1338](https://github.com/leanprover-community/mathlib/pull/1338))
* chore(category_theory/monoidal): monoidal_category doesn't extend category
* remove _aux file, simplifying
* make notations global, and add doc-strings

### [2019-08-20 21:37:32](https://github.com/leanprover-community/mathlib/commit/0dbe3a9)
feat(algebra,equiv,logic): add various lemmas ([#1342](https://github.com/leanprover-community/mathlib/pull/1342))
* add various lemmas
* add simp lemma
* fix simp
* rename to subtype_sigma_equiv

### [2019-08-20 15:42:54](https://github.com/leanprover-community/mathlib/commit/14024a3)
feat(linear_algebra/bilinear_form, linear_algebra/sesquilinear_form, ring_theory/maps): bilinear/sesquilinear forms ([#1300](https://github.com/leanprover-community/mathlib/pull/1300))
* Create involution.lean
* Update involution.lean
* Update involution.lean
* Rename involution.lean to maps.lean
* Create bilinear_form.lean
* Create sesquilinear_form.lean
* Update sesquilinear_form.lean
* Style fixes
* Update sesquilinear_form.lean
* Style fixes
* fix typo

### [2019-08-20 13:12:03](https://github.com/leanprover-community/mathlib/commit/6f747ec)
feat(data/vector2): nth_map ([#1349](https://github.com/leanprover-community/mathlib/pull/1349))
* feat(data/vector2): nth_map
* Update vector2.lean
* Update vector2.lean

### [2019-08-20 12:14:30](https://github.com/leanprover-community/mathlib/commit/8771432)
doc(tactic/ring2): document parts of ring2 ([#1208](https://github.com/leanprover-community/mathlib/pull/1208))
* doc(tactic/ring2): document parts of ring2
* feat(data/tree): refactor binary trees into their own module
* feat(tactic/ring2): resolve correct correctness
* chore(tactic/ring2): move copyright into comment
* doc(tactic/ring2): wording

### [2019-08-20 11:13:39+02:00](https://github.com/leanprover-community/mathlib/commit/f3eb8c2)
chore(data/matrix): simp attribute for transpose_tranpose ([#1350](https://github.com/leanprover-community/mathlib/pull/1350))

### [2019-08-19 21:05:01](https://github.com/leanprover-community/mathlib/commit/5a309a3)
fix(category_theory/eq_to_hom): remove bad simp lemmas ([#1346](https://github.com/leanprover-community/mathlib/pull/1346))

### [2019-08-19 19:01:37](https://github.com/leanprover-community/mathlib/commit/9eefd40)
refactor(data/list/min_max): use with_top for maximum and define argmax ([#1320](https://github.com/leanprover-community/mathlib/pull/1320))
* refactor(data/list/min_max): use option for maximum and define argmax
* prove minimum_singleton
* fix build
* use with_bot for maximum
* update comments

### [2019-08-19 17:09:44](https://github.com/leanprover-community/mathlib/commit/92fa24c)
feat(data/fin): val simp lemmas ([#1347](https://github.com/leanprover-community/mathlib/pull/1347))
* feat(data/fin): val simp lemmas
* Update fin.lean

### [2019-08-19 09:36:05-04:00](https://github.com/leanprover-community/mathlib/commit/6fbcc04)
feat(tactic/reassoc_axiom): produce associativity-friendly lemmas in category theory ([#1341](https://github.com/leanprover-community/mathlib/pull/1341))

### [2019-08-19 13:15:20](https://github.com/leanprover-community/mathlib/commit/8f09b0f)
fix(tactic/omega): simplify with mul_one and one_mul ([#1344](https://github.com/leanprover-community/mathlib/pull/1344))
* Simplify multiplication by one
* Remove debug trace
* Fix integer version of omega

### [2019-08-19 11:20:20](https://github.com/leanprover-community/mathlib/commit/9c1718a)
feat(tactic/obtain): make type argument optional ([#1327](https://github.com/leanprover-community/mathlib/pull/1327))
* feat(tactic/obtain): make type argument optional
* fix(tactic/obtain): unnecessary steps
* feat(tactic/obtain): simplify cases

### [2019-08-18 19:43:51](https://github.com/leanprover-community/mathlib/commit/ab7d39b)
feat(data/vector2): update_nth ([#1334](https://github.com/leanprover-community/mathlib/pull/1334))
* feat(data/vector2): update_nth
* naming and docstrings
* remove double namespace fom vector.nth_mem

### [2019-08-17 20:50:04](https://github.com/leanprover-community/mathlib/commit/538d3f6)
feat(data/vector2): to_list_map ([#1335](https://github.com/leanprover-community/mathlib/pull/1335))

### [2019-08-17 18:55:40](https://github.com/leanprover-community/mathlib/commit/66fa499)
feat(data/list/basic): list.mem_insert_nth ([#1336](https://github.com/leanprover-community/mathlib/pull/1336))
* feat(data/list/basic): list.mem_insert_nth
* Update src/data/list/basic.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>

### [2019-08-16 10:20:57](https://github.com/leanprover-community/mathlib/commit/a1dda1e)
feat(linear_algebra/matrix): linear maps are linearly equivalent to matrices ([#1310](https://github.com/leanprover-community/mathlib/pull/1310))
* linear map to matrix (WIP)
* WIP
* feat (linear_algebra/matrix): lin_equiv_matrix
* feat (linear_algebra.basic): linear_equiv.arrow_congr, std_basis_eq_single
* change unnecessary vector_space assumption for equiv_fun_basis to module
* add docstrings and refactor
* add docstrings
* move instance to pi_instances
* add docstrings + name change
* remove duplicate instance

### [2019-08-16 02:19:14](https://github.com/leanprover-community/mathlib/commit/2e76f36)
feat(tactic/sanity_check): add #sanity_check command ([#1318](https://github.com/leanprover-community/mathlib/pull/1318))
* create a file sanity_check
Currently it contains a tactic that detects unused arguments in declarations
In the future I want to add other cleaning tactics
* fix last tactic
* update comment
* checkpoint
* checkpoint
* rewrite sanity_check
* update sanity_check
* move results to appropriate files
* move some declarations
Some declarations in tactic.core made more sense in meta.expr
tactic.core now imports string.defs (which adds very little)
add documentation
* add entry to docs/tactic.md
* fix errors
* some extra documentation
* add test
* add doc to meta.expr

### [2019-08-16 00:19:33](https://github.com/leanprover-community/mathlib/commit/397c016)
feat(tactic/finish): parse ematch lemmas with `finish using ...` ([#1326](https://github.com/leanprover-community/mathlib/pull/1326))
* feat(tactic/finish): parse ematch lemmas with `finish using ...`
Add test
Add documentation
* Add docstrings
* Formatting and docstrings
* Clean up test
* Add even more docstrings
clean up match expressions
Fix typo

### [2019-08-15 22:29:27](https://github.com/leanprover-community/mathlib/commit/2e90bed)
feat(analysis/complex/exponential): prove that rpow is continuous ([#1306](https://github.com/leanprover-community/mathlib/pull/1306))
* rpow is continuous
* Update exponential.lean
* Fix things
* Fix things
* Fix things
* Fix things

### [2019-08-15 20:26:47](https://github.com/leanprover-community/mathlib/commit/74c25a5)
feat(*): lemmas needed for two projects ([#1294](https://github.com/leanprover-community/mathlib/pull/1294))
* feat(multiplicity|enat): add facts needed for IMO 2019-4
* feat(*): various lemmas needed for the cubing a cube proof
* typo
* some cleanup
* fixes, add choose_two_right
* projections for associated.prime and irreducible

### [2019-08-15 18:18:27](https://github.com/leanprover-community/mathlib/commit/fa68342)
feat(data/rat): move lemmas to right file, add nat cast lemmas, remove ([#1333](https://github.com/leanprover-community/mathlib/pull/1333))
redundant lemma

### [2019-08-15 15:09:08](https://github.com/leanprover-community/mathlib/commit/73cc56c)
refactor(data/fintype): shorten proof of card_eq ([#1332](https://github.com/leanprover-community/mathlib/pull/1332))

### [2019-08-15 11:27:01](https://github.com/leanprover-community/mathlib/commit/ebbbb76)
doc(contribute/style): remove outdated syntax [ci skip] ([#1329](https://github.com/leanprover-community/mathlib/pull/1329))
* doc(contribute/style): remove outdated syntax [ci skip]
* doc(contribute/style): mistaken find/replace

### [2019-08-15 10:26:30](https://github.com/leanprover-community/mathlib/commit/3d512f7)
chore(category_theory/isomorphism): docstring, DRY, add some trivial lemmas ([#1309](https://github.com/leanprover-community/mathlib/pull/1309))
- add module docstring;
- use `as_iso` more aggressively to avoid repeating proofs;
- add more trivial lemmas.

### [2019-08-15 05:08:24](https://github.com/leanprover-community/mathlib/commit/e48ad0d)
chore(*): migrate `units.map` to bundled homs ([#1331](https://github.com/leanprover-community/mathlib/pull/1331))

### [2019-08-14 18:01:25](https://github.com/leanprover-community/mathlib/commit/02548ad)
fix(data/mllist): fix off-by-one bug in mllist.take ([#1298](https://github.com/leanprover-community/mathlib/pull/1298))
* Update mllist.lean
Changed `n` to `n+1` in line 72. This fixes a bug in the `take` function for monadic lazy lists (mllist).
* add a test showing correct behaviour of take

### [2019-08-14 15:58:41](https://github.com/leanprover-community/mathlib/commit/0bc4a40)
feat(data/pequiv): symm_single_apply ([#1324](https://github.com/leanprover-community/mathlib/pull/1324))

### [2019-08-13 15:12:57](https://github.com/leanprover-community/mathlib/commit/2a131d9)
fix(.github): typo ([#1323](https://github.com/leanprover-community/mathlib/pull/1323))

### [2019-08-13 15:19:45+02:00](https://github.com/leanprover-community/mathlib/commit/5796465)
fix(algebra/ring): fix typo in docstring ([#1322](https://github.com/leanprover-community/mathlib/pull/1322))

### [2019-08-12 17:42:15](https://github.com/leanprover-community/mathlib/commit/900c53a)
feat(scripts): add scripts to import all mathlib files ([#1281](https://github.com/leanprover-community/mathlib/pull/1281))
* add scripts to import all mathlib files
mk_all makes a file all.lean in each subdirectory of src/, importing all files in that directory, including subdirectories
rm_all removes the files all.lean
* also delete all.olean files
* remove unnecessary maxdepth
* add comments, and generate comments

### [2019-08-12 17:59:16+02:00](https://github.com/leanprover-community/mathlib/commit/df1fb07)
doc(contribute): add link to doc requirements ([#1317](https://github.com/leanprover-community/mathlib/pull/1317))

### [2019-08-12 15:28:09](https://github.com/leanprover-community/mathlib/commit/92a5424)
feat(data/fin): mem_find_iff ([#1307](https://github.com/leanprover-community/mathlib/pull/1307))
* feat(data/fin): mem_find_iff
* add find_eq_some_iff ([#1308](https://github.com/leanprover-community/mathlib/pull/1308))

### [2019-08-12 13:41:27](https://github.com/leanprover-community/mathlib/commit/f46b0dc)
feat(algebra/ordered_field): le_div_iff_of_neg ([#1311](https://github.com/leanprover-community/mathlib/pull/1311))
* feat(algebra/ordered_field): le_div_iff_of_neg
* Update ordered_field.lean
* Update ordered_field.lean
* Update ordered_field.lean
* Update ordered_field.lean

### [2019-08-12 11:55:24](https://github.com/leanprover-community/mathlib/commit/3bd3dcd)
feat(data/option/basic): bind_eq_none' ([#1312](https://github.com/leanprover-community/mathlib/pull/1312))
* feat(data/option/basic): bind_eq_none'
* Update basic.lean
* fix build and add simp

### [2019-08-12 10:14:40](https://github.com/leanprover-community/mathlib/commit/01cb33c)
feat(algebra/ordered_ring): pos_of_mul_neg_left and similar ([#1313](https://github.com/leanprover-community/mathlib/pull/1313))

### [2019-08-11 09:21:07](https://github.com/leanprover-community/mathlib/commit/37d4eda)
Delete repeated item ([#1316](https://github.com/leanprover-community/mathlib/pull/1316))

### [2019-08-10 04:04:40](https://github.com/leanprover-community/mathlib/commit/3aad7f1)
feat(data/matrix/pequiv): partial equivalences to represent matrices ([#1228](https://github.com/leanprover-community/mathlib/pull/1228))
* feat(matrix/pequiv): partial equivalences to represent matrices
* use notation for pequiv
* correct imports
* finish correcting imports
* add some docs
* Add documentation
* improve documentation

### [2019-08-09 09:57:38](https://github.com/leanprover-community/mathlib/commit/a79794a)
feat(archive): add archive ([#1295](https://github.com/leanprover-community/mathlib/pull/1295))
* feat(archive): add archive
* reformulate sentence

### [2019-08-08 14:14:07+02:00](https://github.com/leanprover-community/mathlib/commit/dd4db5f)
fix(tactic/linarith): handle neq goals ([#1303](https://github.com/leanprover-community/mathlib/pull/1303))

### [2019-08-08 02:35:57](https://github.com/leanprover-community/mathlib/commit/9c4dd95)
feat (analysis/normed_space): Define real inner product space ([#1248](https://github.com/leanprover-community/mathlib/pull/1248))
* Inner product space
* Change the definition of inner_product_space
The original definition introduces an instance loop.
See Zulip talks: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/ring.20tactic.20works.20at.20one.20place.2C.20fails.20at.20another
* Orthogonal Projection
Prove the existence of orthogonal projections onto complete subspaces in an inner product space.
* Fix names
* small fixes

### [2019-08-07 07:50:47](https://github.com/leanprover-community/mathlib/commit/a2a867e)
feat(algebra/ring): bundled semiring homs ([#1305](https://github.com/leanprover-community/mathlib/pull/1305))
* added bundled ring homs
* removed comment
* Tidy and making docstrings consistent
* fix spacing
* fix typo
Co-Authored-By: Johan Commelin <johan@commelin.net>
* fix typo
Co-Authored-By: Johan Commelin <johan@commelin.net>
* whoops, actually removing instances

### [2019-08-06 15:58:05+02:00](https://github.com/leanprover-community/mathlib/commit/57c1d6d)
chore(data/matrix): protect some lemmas ([#1304](https://github.com/leanprover-community/mathlib/pull/1304))

### [2019-08-05 21:37:42](https://github.com/leanprover-community/mathlib/commit/88ad3cf)
feat(tactic/push_neg): add optional name argument to contrapose ([#1302](https://github.com/leanprover-community/mathlib/pull/1302))

### [2019-08-05 15:01:21](https://github.com/leanprover-community/mathlib/commit/de83205)
refactor(algebra/big_operators) delete duplicates and change names ([#1301](https://github.com/leanprover-community/mathlib/pull/1301))
* refactor(algebra/big_operators) delete duplicates and change names
* fix build

### [2019-08-05 09:15:59](https://github.com/leanprover-community/mathlib/commit/fc56c85)
feat(algebra/order_functions): abs_nonpos_iff ([#1299](https://github.com/leanprover-community/mathlib/pull/1299))
* feat(algebra/ordered_group): abs_nonpos_iff
* Update ordered_group.lean
* move to order_functions

### [2019-08-04 04:21:08](https://github.com/leanprover-community/mathlib/commit/b46665f)
chore(ring_theory/algebra): make first type argument explicit in alg_hom ([#1296](https://github.com/leanprover-community/mathlib/pull/1296))
* chore(ring_theory/algebra): make first type argument explicit in alg_hom
Now this works, and it didn't work previously even with `@`
```lean
structure alg_equiv (α β γ : Type*) [comm_ring α] [ring β] [ring γ]
  [algebra α β] [algebra α γ] extends alg_hom α β γ :=
```
* Update algebra.lean

### [2019-08-03 04:14:56](https://github.com/leanprover-community/mathlib/commit/27d34b3)
feat(algebra/direct_limit): discrete_field ([#1293](https://github.com/leanprover-community/mathlib/pull/1293))

### [2019-08-02 17:15:07](https://github.com/leanprover-community/mathlib/commit/8fe73f3)
feat(data/fintype): psigma.fintype ([#1291](https://github.com/leanprover-community/mathlib/pull/1291))
* feat(data/fintype): psigma.fintype
* Update fintype.lean
* Swap instance argument order

### [2019-08-02 15:14:38](https://github.com/leanprover-community/mathlib/commit/3af92be)
feat(algebra/module): linear_map.coe_mk ([#1290](https://github.com/leanprover-community/mathlib/pull/1290))

### [2019-08-02 14:52:18](https://github.com/leanprover-community/mathlib/commit/1061238)
feat(topology): category of uniform spaces ([#1275](https://github.com/leanprover-community/mathlib/pull/1275))
* feat(category_theory): uniform spaces
* feat(topology/uniform_spaces): CpltSepUniformSpace is a reflective subcategory

### [2019-08-02 12:48:54](https://github.com/leanprover-community/mathlib/commit/5b4b208)
feat(data/fintype): univ_unique ([#1289](https://github.com/leanprover-community/mathlib/pull/1289))

### [2019-08-01 17:01:15](https://github.com/leanprover-community/mathlib/commit/766807f)
feat(data/rat): refactor into smaller files and add documentation ([#1284](https://github.com/leanprover-community/mathlib/pull/1284))

### [2019-08-01 15:02:26](https://github.com/leanprover-community/mathlib/commit/0d66c87)
feat(data/seq): add ext proof, nats def, zip_with lemmas, and extract seq property ([#1278](https://github.com/leanprover-community/mathlib/pull/1278))