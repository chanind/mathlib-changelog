### [2019-09-30 14:17:53](https://github.com/leanprover-community/mathlib/commit/374c290)
chore(linear_algebra): continue removing decidable_eq assumptions ([#1404](https://github.com/leanprover-community/mathlib/pull/1404))
* chore(linear_algebra): continue remocing decidable_eq assumptions
* chore(data/mv_polynomial): get rid of unnecessary changes to instance depth
* fix build
* change class instance depth
* class_instance depth
t Please enter the commit message for your changes. Lines starting
* delete some more decidable_eq
* Update finite_dimensional.lean
* Update finite_dimensional.lean
* Update finite_dimensional.lean

### [2019-09-30 08:55:58](https://github.com/leanprover-community/mathlib/commit/c6fab42)
feat(ring_theory/power_series): order ([#1292](https://github.com/leanprover-community/mathlib/pull/1292))
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
* Order of a power series
* Start on formal Laurent series
* WIP
* Remove file. It's for another PR.
* Add stuff about order
* Remove old file
* Basics on order of power series
* Lots of stuff
* Move stuff on kernels
* Move stuff on ker to the right place
* Fix build
* Add elim_cast attributes, update documentation
* Bundle homs
* Fix build
* Remove duplicate trunc_C
* Fix build

### [2019-09-28 22:44:16](https://github.com/leanprover-community/mathlib/commit/30aa8d2)
chore(order/basic): rename `monotone_comp` to `monotone.comp`, reorder arguments ([#1497](https://github.com/leanprover-community/mathlib/pull/1497))

### [2019-09-27 22:59:45](https://github.com/leanprover-community/mathlib/commit/708faa9)
feat(geometry/manifold/manifold): define manifolds ([#1422](https://github.com/leanprover-community/mathlib/pull/1422))
* feat(geometry/manifold/manifold): define manifolds
* Update src/geometry/manifold/manifold.lean
Typo
Co-Authored-By: Johan Commelin <johan@commelin.net>
* reviewer comments
* notations, comments
* Update src/geometry/manifold/manifold.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/geometry/manifold/manifold.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* manifolds: reviewers comments
* comment on notation for composition
* add documentation on atlases and structomorphisms

### [2019-09-27 18:10:21](https://github.com/leanprover-community/mathlib/commit/e0c204e)
chore(algebra/group_power): move inv_one from group_power to field ([#1495](https://github.com/leanprover-community/mathlib/pull/1495))
* chore(algebra/group_power): move inv_one from group_power to field
*  fix

### [2019-09-27 16:05:10](https://github.com/leanprover-community/mathlib/commit/74f09d0)
chore(algebra/char_p): remove some decidable_eq assumptions ([#1492](https://github.com/leanprover-community/mathlib/pull/1492))
* chore(algebra/char_p): remove some decidable_eq assumptions
*  fix build

### [2019-09-27 14:10:25](https://github.com/leanprover-community/mathlib/commit/ce7c94f)
feat(reduce_projections): add reduce_projections attribute ([#1402](https://github.com/leanprover-community/mathlib/pull/1402))
* feat(reduce_projections): add attribute
This attribute automatically generates simp-lemmas for an instance of a structure stating what the projections of this instance are
* add tactic doc
* use lean code blocks
* missing `lemma`
* checkpoint
* recursively apply reduce_projections and eta-reduce structures
* reviewer comments, shorten name
new name is simps
* avoid name clashes
* remove recursive import
* fix eta-expansion bug
* typo
* apply whnf to type
* add test
* replace nm by decl_name

### [2019-09-27 11:47:32](https://github.com/leanprover-community/mathlib/commit/efd5ab2)
feat(logic/function): define `function.involutive` ([#1474](https://github.com/leanprover-community/mathlib/pull/1474))
* feat(logic/function): define `function.involutive`
* Prove that `inv`, `neg`, and `complex.conj` are involutive.
* Move `inv_inv'` to `algebra/field`

### [2019-09-27 09:36:44](https://github.com/leanprover-community/mathlib/commit/6a79f8a)
feat(data/int/basic): to_nat lemmas ([#1479](https://github.com/leanprover-community/mathlib/pull/1479))
* feat(data/int/basic): of_nat lemmas
* Adding lt_of_to_nat_lt
* reversing sides of <->

### [2019-09-27 07:02:36](https://github.com/leanprover-community/mathlib/commit/0bc5de5)
chore(*): drop some unused args reported by `#sanity_check_mathlib` ([#1490](https://github.com/leanprover-community/mathlib/pull/1490))
* Drop some unused arguments
* Drop more unused arguments
* Move `round` to the bottom of `algebra/archimedean`
Suggested by @rwbarton

### [2019-09-26 20:42:25](https://github.com/leanprover-community/mathlib/commit/15ed039)
fix(scripts/mk_all): ignore hidden files ([#1488](https://github.com/leanprover-community/mathlib/pull/1488))
* fix(scripts/mk_all): ignore hidden files
Emacs sometimes creates temporary files with names like `.#name.lean`.
* Fix comment
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>

### [2019-09-26 13:55:55](https://github.com/leanprover-community/mathlib/commit/3cd3341)
feat(field_theory/minimal_polynomial): Basics on minimal polynomials ([#1449](https://github.com/leanprover-community/mathlib/pull/1449))
* chore(ring_theory/algebra): make first type argument explicit in alg_hom
Now this works, and it didn't work previously even with `@`
```lean
structure alg_equiv (α β γ : Type*) [comm_ring α] [ring β] [ring γ]
  [algebra α β] [algebra α γ] extends alg_hom α β γ :=
```
* Update algebra.lean
* feat(field_theory/algebraic_closure)
* Remove sorries about minimal polynomials
* Define alg_equiv.symm
* typo
* Remove another sorry, in base_extension
* Work in progress
* Remove a sorry in maximal_extension_chain
* Merge two sorries
* More sorries removed
* More work on transitivity of algebraicity
* WIP
* Sorry-free definition of algebraic closure
* More or less sorries
* Removing some sorries
* WIP
* feat(field_theory/minimal_polynomial): Basics on minimal polynomials
* Remove protected; add docstrings
* Open classical locale
* Stuff is broken
* Rewrite the module doc a bit, revert change to classical
* Little fixes
* explicit-ify proof
* feat(algebra/big_operators): simp lemmas
* Remove decidable_eq instances
* fix(ring_theory/algebra): get ris of dec_eq assumptions so simp triggers again
* break as_sum into its constituent pieces
* fix namespace
* not sure if this is better or worse
* Fix ext naming
* More fixes
* Fix some renaming issues

### [2019-09-26 12:04:21](https://github.com/leanprover-community/mathlib/commit/f92e812)
feat(data/setoid): create file about setoids ([#1453](https://github.com/leanprover-community/mathlib/pull/1453))
* setoid complete lattice
* order iso and Galois insertion
* added documentation
* editing docstrings
* not opening lattice twice
* partitions
* typo
* minor edits
* editing docstrings
* applying review comments
* editing implementation notes
* partly applied review comments
* moved length_scanl
* whoops, and removed length_scanl from setoid
* editing implementation notes
* generalising `of_quotient` a bit more
* style tweaks + reviewer changes
* removing Bell numbers for now
* revert docstring
* applying review comments
* generalising to_quotient
* partly applying review comments
* applying review comments
* readding list length lemmas

### [2019-09-26 07:39:54](https://github.com/leanprover-community/mathlib/commit/7afdab6)
refactor(data/equiv/algebra): rewrite `ring_equiv` using bundled homs ([#1482](https://github.com/leanprover-community/mathlib/pull/1482))
* refactor(data/equiv/algebra): rewrite `ring_equiv` using bundled homs
Fix some compile errors
* Fix compile, add missing docs
* Docstrings
* Use less `ring_equiv.to_equiv` outside of `data/equiv/algebra`
* Join lines

### [2019-09-26 00:29:27](https://github.com/leanprover-community/mathlib/commit/2e35a7a)
feat(int/basic): add simp-lemma int.of_nat_eq_coe ([#1486](https://github.com/leanprover-community/mathlib/pull/1486))
* feat(int/basic): add simp-lemma int.of_nat_eq_coe
* fix errors
in the process also add some lemmas about bxor to simplify proofs
* use coercion in rat.mk

### [2019-09-25 18:11:13](https://github.com/leanprover-community/mathlib/commit/b39040f)
feat(sanity_check): improvements  ([#1487](https://github.com/leanprover-community/mathlib/pull/1487))
* checkpoint
* checkpoint
* checkpoint
* feat(sanity_check): improvements
* Now check for classical.[some|choice] and [gt|ge] in theorem statements
* Add [sanity_skip] attribute to skip checks
* Add #sanity_check_all to check all declarations
* Add `-` after command to only execute fast tests
* Reduce code duplication
* Make the performed checks configurable.
* some cleanup
* fix tests
* clarification
* reviewer comments
* fix typo in docstring
* reviewer comments
* update docstring
* Update tactics.md

### [2019-09-25 04:39:17](https://github.com/leanprover-community/mathlib/commit/3e5dc88)
chore(scripts): add executable bit to scripts/mk_all.sh, and create/delete sanity_check_mathlib.lean ([#1480](https://github.com/leanprover-community/mathlib/pull/1480))
* chore(scripts): add executable bit to scripts/mk_all.sh
* another
* modify mk_all/rm_all to create a file containing #sanity_check_mathlib
* add sanity_check_mathlib.lean to .gitignore
* Update scripts/mk_all.sh
* Update scripts/mk_all.sh
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-09-25 01:30:42](https://github.com/leanprover-community/mathlib/commit/491a68e)
cleanup(*): use priority 10 for low priority ([#1485](https://github.com/leanprover-community/mathlib/pull/1485))
Now we can locally use priorities lower than this low-priority

### [2019-09-24 15:16:11](https://github.com/leanprover-community/mathlib/commit/00d440a)
feat(tactic/import_private): make private definitions available outside of their scope ([#1450](https://github.com/leanprover-community/mathlib/pull/1450))
* new user command: `import_private`
* test case
* Update expr.lean
* Update examples.lean
* Update tactics.md
* Update src/tactic/core.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update tactics.md
* Update examples.lean
* Update core.lean
* Update core.lean
* Update src/meta/expr.lean
* Update docs/tactics.md
* Update examples.lean
* Update examples.lean

### [2019-09-24 13:36:31](https://github.com/leanprover-community/mathlib/commit/1eaa292)
feat(finset): add has_sep instance ([#1477](https://github.com/leanprover-community/mathlib/pull/1477))

### [2019-09-24 08:39:19](https://github.com/leanprover-community/mathlib/commit/5344da4)
feat(algebra/big_operators): simp lemmas ([#1471](https://github.com/leanprover-community/mathlib/pull/1471))
* feat(algebra/big_operators): simp lemmas
* remove @[simp]

### [2019-09-24 08:13:37](https://github.com/leanprover-community/mathlib/commit/201174d)
feat(algebra/continued_fractions): add basic defs/lemmas for continued fractions ([#1433](https://github.com/leanprover-community/mathlib/pull/1433))
* feat(algebra/continued_fractions): add basic defs/lemmas for continued fractions
* Rename termiantes_at to terminated_at, use long names for cont. fracts.
* Fix indentation, remove subfolders, fix docstrings

### [2019-09-24 05:46:35](https://github.com/leanprover-community/mathlib/commit/327098b)
feat(tactic/library_search): a more powerful library_search ([#1470](https://github.com/leanprover-community/mathlib/pull/1470))
* experimental extensions to library_search
* upgrades to library_search
* remove ! for a later PR
* move `run_norm_num`
* oops
* Update src/tactic/library_search.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
* remove run_norm_num for later

### [2019-09-24 03:51:35](https://github.com/leanprover-community/mathlib/commit/88f37b5)
fix(tactic.lift): fix error messages ([#1478](https://github.com/leanprover-community/mathlib/pull/1478))

### [2019-09-24 00:00:49](https://github.com/leanprover-community/mathlib/commit/425644f)
refactor(algebra/*): Make `monoid_hom.ext` etc use `∀ x, f x = g x` as an assumption ([#1476](https://github.com/leanprover-community/mathlib/pull/1476))

### [2019-09-23 22:04:22](https://github.com/leanprover-community/mathlib/commit/604699b)
feat(data|set_theory): various new lemmas ([#1466](https://github.com/leanprover-community/mathlib/pull/1466))
* various changes
* move section on map down
I need some lemmas about nth for maps, and this seemed like the nicest way to do it
* some lemmas
* replace app by append in names
* lemmas from various proving grounds problems
* sanity_check on list.basic
* small fixes in ordinal and cardinal
also open namespace equiv in ordinal
* small changes
* add docstring
* fix
* rename variable
* simp caused a problem
* update docstring
* fix last two comments

### [2019-09-23 19:57:18](https://github.com/leanprover-community/mathlib/commit/fd7840a)
feat(topology/constructions): is_open_prod_iff' ([#1454](https://github.com/leanprover-community/mathlib/pull/1454))
* feat(topology/constructions): open_prod_iff'
* reviewer's comments
* fix build
* golfed; is_open_map_fst

### [2019-09-23 17:36:28](https://github.com/leanprover-community/mathlib/commit/87d1240)
feat(tactic/core): derive handler for simple instances ([#1475](https://github.com/leanprover-community/mathlib/pull/1475))
* feat(tactic/core): derive handler for simple algebraic instances
* change comment
* use mk_definition
* Update src/tactic/core.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-09-22 04:34:09](https://github.com/leanprover-community/mathlib/commit/61ccaf6)
chore(*): fix various issues reported by `sanity_check_mathlib` ([#1469](https://github.com/leanprover-community/mathlib/pull/1469))
* chore(*): fix various issues reported by `sanity_check_mathlib`
* Drop a misleading comment, fix the proof

### [2019-09-21 06:12:35](https://github.com/leanprover-community/mathlib/commit/65bf45c)
fix(category_theory/finite_limits): fix definition, and construct from finite products and equalizers ([#1427](https://github.com/leanprover-community/mathlib/pull/1427))
* chore(category_theory): require morphisms live in Type
* move back to Type
* fix(category_theory/finite_limits): fix definition, and construct from finite products and equalizers
* fixes
* fix duplicate name
* make fin_category a mixin
* fix
* fix
* oops
* fixes
* oops missing universe change
* finish documentation
* fix namespace
* move variables to the right place
* don't repeat yourself
* update module doc-string now that the files have been merged
* inlining has_limit instances

### [2019-09-21 00:47:17](https://github.com/leanprover-community/mathlib/commit/9c89fa5)
feat(tactic/interactive): add fconstructor ([#1467](https://github.com/leanprover-community/mathlib/pull/1467))

### [2019-09-20 11:08:05](https://github.com/leanprover-community/mathlib/commit/708a28c)
chore(algebra/group/units): use `def to_units` instead of `has_lift` ([#1431](https://github.com/leanprover-community/mathlib/pull/1431))
* chore(algebra/group/units): use `def to_units` instead of `has_lift`
* Move, upgrade to `mul_equiv`, add documentation

### [2019-09-20 03:28:58](https://github.com/leanprover-community/mathlib/commit/bfe9c6c)
chore(data/pfun): run `#sanity_check` ([#1463](https://github.com/leanprover-community/mathlib/pull/1463))

### [2019-09-19 15:32:04](https://github.com/leanprover-community/mathlib/commit/ce105fd)
chore(algebra/group): rename `as_monoid_hom` into `monoid_hom.of`, define `ring_hom.of` ([#1443](https://github.com/leanprover-community/mathlib/pull/1443))
* chore(algebra/group): rename `as_monoid_hom` into `monoid_hom.of`
This is similar to `Mon.of` etc.
* Fix compile
* Docs, missing universe
* Move variables declaration up as suggested by @jcommelin
* doc-string

### [2019-09-19 13:17:33](https://github.com/leanprover-community/mathlib/commit/d910283)
chore(category_theory/endomorphism): make `map_End` and `map_Aut` use bundled homs ([#1461](https://github.com/leanprover-community/mathlib/pull/1461))
* Migrate `functor.map_End` and `functor.map_Aut` to bundled homs
Adjust implicit arguments of `iso.ext`
* Add docstrings

### [2019-09-19 13:21:35+02:00](https://github.com/leanprover-community/mathlib/commit/1b8285e)
chore(readme): Add new maintainers [ci skip]

### [2019-09-19 02:38:18](https://github.com/leanprover-community/mathlib/commit/b11f0f1)
refactor(category_theory): refactor concrete categories ([#1380](https://github.com/leanprover-community/mathlib/pull/1380))
* trying to use bundled homs
* bundled monoids should use bundled homs
* fixes
* fixes
* refactor(*): rewrite concrete categories
* Add module documentation
* local instance
* Move files around; don't touch content yet
* Move code around, fix some compile errors
* Add `unbundled_hom.lean`
* Turn `hom` into an argument of `(un)bundled_hom`
For some reason, it helps Lean find coercions from `Ring` category
morphisms to functions.
* Define `unbundled_hom.mk_has_forget`; fix compile
* Add some documentation
* Fix compile
* chore(category_theory): require morphisms live in Type
* move back to Type
* tweaks to doc-comments
* fixing some formatting
* Revert most of the changes to `data/mv_polynomials`
* Drop unused argument, add a comment
* Simplify universe levels in `concrete_category/basic`.
Still fails to compile.
* Simplify universe levels in `concrete_category/{un,}bundled_hom`
* fixes
* Fix an `import`
* Doc cleanup
* update post [#1412](https://github.com/leanprover-community/mathlib/pull/1412)
* Drop `simp`
* Rename variable
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Rename variable
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Fix more issues reported by @rwbarton
* Rename variable
Co-Authored-By: Reid Barton <rwbarton@gmail.com>
* Use `subtype.eq` instead of `subtype.ext.2`
* Cleanup
* Fix compile: now `ring_hom.ext` takes fewer explicit args
* Fix compile
* Run `sanity_check` on all files modified in this branch
* Fix most of the issues reported
* Except for the old ones in `mv_polynomial` (postponed to a separate
  PR) and a false positive in `single_obj`
* Review `∀` vs `Π`
* Remove some unnecessary parentheses
* add comment
* punit_instances: no need to explicitly provide constants and operations
* Rename `has_forget` to `has_forget₂`
* add comment, simplify comm_ring punit
* Drop `private def free_obj`
* documentation
* fix comment
* tweaks
* comments
* documentation on touched files
* many doc-strings

### [2019-09-18 17:59:44](https://github.com/leanprover-community/mathlib/commit/066d053)
chore(topology/maps): a few tweaks to open_embedding and closed embeddings ([#1459](https://github.com/leanprover-community/mathlib/pull/1459))
* chore(topology/maps): a few tweaks to open_embedding and closed
embeddings
aligning them with recent modification to embedding. From the perfectoid
project.
* chore(topology/maps): add missing empty line

### [2019-09-18 15:46:57](https://github.com/leanprover-community/mathlib/commit/08390f5)
refactor(algebra/big_operators,data/finset): use `finset.disjoint` in definitions ([#1456](https://github.com/leanprover-community/mathlib/pull/1456))
* Use `finset.disjoint` in `algebra/big_operators`
* New lemma `disjoint_filter`
It should be a painless step from using `filter_inter_filter_neg_eq`
to using this lemma
* Update other dependencies of finset.prod_union and finset.prod_bind
* Reformat some lines to make them fit within 100 characters
* We can actually do away with two non-terminal `simp`s now

### [2019-09-18 15:43:01+02:00](https://github.com/leanprover-community/mathlib/commit/b51978d)
chore(data/mllist): Typo in author name [ci skip] ([#1458](https://github.com/leanprover-community/mathlib/pull/1458))

### [2019-09-18 15:40:20+02:00](https://github.com/leanprover-community/mathlib/commit/874a15a)
Update lattice.lean ([#1457](https://github.com/leanprover-community/mathlib/pull/1457))

### [2019-09-17 18:02:24](https://github.com/leanprover-community/mathlib/commit/b41277c)
feat(set_theory/game): the theory of combinatorial games ([#1274](https://github.com/leanprover-community/mathlib/pull/1274))
* correcting definition of addition, and splitting content into two files, one about games, one about surreals
* add_le_zero_of_le_zero, but without well-foundedness
* progress
* Mario's well-foundedness proof
* getting there!
* success!
* minor
* almost there
* progress
* off to write some tactics
* not quite there
* hmmm
* getting there!
* domineering is hard
* removing unneeded theorems
* cleanup
* add_semigroup surreal
* cleanup
* short proof
* cleaning up
* remove equiv_rw
* move lemmas about pempty to logic.basic
* slightly more comments; still lots to go
* documentation
* finishing documentation
* typo
* Update src/logic/basic.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* fix references
* oops
* change statement of equiv.refl_symm
* more card_erase lemmas; golf domineering proofs
* style changes
* fix comment
* fixes after Reid's review
* some improvements
* golfing
* subsingleton short
* diagnosing decidable
* hmmmhmmm
* computational domineering
* fix missing proofs (need golfing?)
* minor
* short_of_relabelling
* abbreviating
* various minor
* removing short games and domineering from this PR
* style / proof simplification / golfing
* some minor golfing
* adding Reid to the author line
* add @[simp]
* adding two lemmas characterising the order relation
* separating out game and pgame, and discarding lame lemmas
* comment
* fixes

### [2019-09-17 15:50:00](https://github.com/leanprover-community/mathlib/commit/19a246c)
fix(category_theory): require morphisms are in Type, again ([#1412](https://github.com/leanprover-community/mathlib/pull/1412))
* chore(category_theory): require morphisms live in Type
* move back to Type
* fixes

### [2019-09-17 05:06:09](https://github.com/leanprover-community/mathlib/commit/ab2c546)
feat(data/quot): define `quotient.map` and `quotient.map₂` (dep: 1441) ([#1442](https://github.com/leanprover-community/mathlib/pull/1442))
* chore(algebra/group,logic/relator): review some explicit/implicit arguments
* ring_hom.ext too
* feat(data/quot): define `quotient.map` and `quotient.map₂`
* Add comments
* Fix a typo
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2019-09-17 02:44:20](https://github.com/leanprover-community/mathlib/commit/d4cc179)
feat(logic/basic): eq_iff_eq_cancel ([#1447](https://github.com/leanprover-community/mathlib/pull/1447))
* feat(logic/basic): eq_iff_eq_cancel
These lemmas or not meant for `rw` but to be applied, as a sort of congruence lemma.
* State lemmas as iff
* Make'm simp

### [2019-09-17 00:58:35](https://github.com/leanprover-community/mathlib/commit/c412527)
feat(data/list/sort): ordered_insert lemmas ([#1437](https://github.com/leanprover-community/mathlib/pull/1437))
* feat(data/list/sort): ordered_insert lemmas
* add a lemma about L.tail.count

### [2019-09-16 23:07:50](https://github.com/leanprover-community/mathlib/commit/dd0ff1c)
feat(data/nat/basic): dvd_add_self_{left,right} ([#1448](https://github.com/leanprover-community/mathlib/pull/1448))
* feat(data/nat/basic): dvd_add_self_{left,right}
Two simp-lemmas of the form
```lean
@[simp] protected lemma dvd_add_self_left {m n : ℕ} :
  m ∣ m + n ↔ m ∣ n :=
dvd_add_right (dvd_refl m)
```
* Oops, lemmas were protected
* Provide version for rings

### [2019-09-16 22:49:24](https://github.com/leanprover-community/mathlib/commit/929c186)
fix(docs/tutorial/category_theory): fix import ([#1440](https://github.com/leanprover-community/mathlib/pull/1440))
* fix(docs/tutorial/category_theory): fix import
* fix(.travis.yml): Travis stages to build docs/
* cache docs/ in travis build

### [2019-09-16 21:07:29](https://github.com/leanprover-community/mathlib/commit/a3ccc7a)
chore(category_theory/notation): update notation for prod and coprod ([#1413](https://github.com/leanprover-community/mathlib/pull/1413))
* updating notation for categorical prod and coprod
* update notation

### [2019-09-16 16:01:04+02:00](https://github.com/leanprover-community/mathlib/commit/b2b0de4)
feat(algebra/group/basic): mul_left_eq_self etc ([#1446](https://github.com/leanprover-community/mathlib/pull/1446))
Simp-lemmas for groups of the form a * b = b ↔ a = 1.

### [2019-09-16 09:26:53](https://github.com/leanprover-community/mathlib/commit/d7f0e68)
chore(algebra/group,logic/relator): review some explicit/implicit args ([#1441](https://github.com/leanprover-community/mathlib/pull/1441))
* chore(algebra/group,logic/relator): review some explicit/implicit arguments
* ring_hom.ext too

### [2019-09-14 05:00:40](https://github.com/leanprover-community/mathlib/commit/81a31ca)
chore(data/*): flipping inequalities ([#1436](https://github.com/leanprover-community/mathlib/pull/1436))
* chore(data/*): flipping inequalities
* some more
* Update src/algebra/order_functions.lean
* fixing some names
* fix
* fixes
* fixes
* making names/comments uniform
* fixes
* fixes
* fix
* rename
* fixes
* fixes
* fix
* renames
* I'm so bad at this
* ...
* fixes

### [2019-09-13 07:38:04](https://github.com/leanprover-community/mathlib/commit/e3234f0)
feat(algebra/ring): add coercions from →+* to →* and →+ ([#1435](https://github.com/leanprover-community/mathlib/pull/1435))
* feat(algebra/ring): add coercions from →+* to →* and →+
* two lemmas simplifying casts
* add squash_cast attributes

### [2019-09-11 23:51:16](https://github.com/leanprover-community/mathlib/commit/590fb89)
chore(category_theory/functor_category): improve comment warning about hcomp_assoc [ci skip] ([#1434](https://github.com/leanprover-community/mathlib/pull/1434))
* expanding comment
* no scare quotes

### [2019-09-11 17:42:41](https://github.com/leanprover-community/mathlib/commit/140a606)
feat(well_founded_tactics):  patch default_dec_tac ([#1419](https://github.com/leanprover-community/mathlib/pull/1419))
* let simp flip inequalities
* feat(well_founded_tactics):  patch default_dec_tac
* Keeley's suggested syntax, and adding to the docs
* more
* add docs

### [2019-09-11 12:46:21](https://github.com/leanprover-community/mathlib/commit/e27142a)
chore(*): renaming files constructing category instances ([#1432](https://github.com/leanprover-community/mathlib/pull/1432))

### [2019-09-11 03:52:18](https://github.com/leanprover-community/mathlib/commit/8a5156f)
fix(algebra/*/colimits): avoid explicit `infer_instance` ([#1430](https://github.com/leanprover-community/mathlib/pull/1430))
With an explicit universe level Lean can do it automatically.

### [2019-09-11 01:49:04](https://github.com/leanprover-community/mathlib/commit/45fe081)
feat(logic): make some decidability proofs [inline] ([#1393](https://github.com/leanprover-community/mathlib/pull/1393))
* feat(logic): make some decidability proofs [inline]
* inline more decidability proofs
* test
* import logic.basic in test

### [2019-09-10 23:38:55](https://github.com/leanprover-community/mathlib/commit/8e46fa5)
chore(algebra/group/to_additive): map_namespace should make a meta constant ([#1409](https://github.com/leanprover-community/mathlib/pull/1409))
* chore(algebra/group/to_additive): map_namespace should make a meta constance
`map_namespace` now produces a `meta constant` instead of a constant. This means that after importing `group_theory/coset` and typing `#print axioms`, `quotient_group._to_additive` is not in the list, since it is now a `meta constant`. This is a little bit neater, and it doesn't look like we're adding any axioms.
* Update to_additive.lean
* Update to_additive.lean

### [2019-09-10 22:44:22](https://github.com/leanprover-community/mathlib/commit/e2f904e)
feat(tactic/auto_cases): run auto_cases on false and psigma ([#1428](https://github.com/leanprover-community/mathlib/pull/1428))

### [2019-09-10 19:55:17](https://github.com/leanprover-community/mathlib/commit/c87ec0e)
feat(tactic/{abel,ring}): state conditions of tactics more precisely ([#1423](https://github.com/leanprover-community/mathlib/pull/1423))

### [2019-09-10 15:33:29](https://github.com/leanprover-community/mathlib/commit/2dd6398)
let simp flip inequalities ([#1418](https://github.com/leanprover-community/mathlib/pull/1418))

### [2019-09-10 11:26:37](https://github.com/leanprover-community/mathlib/commit/0935e8b)
feat(algebra/group/units): add some lemmas about `divp` ([#1388](https://github.com/leanprover-community/mathlib/pull/1388))
* feat(algebra/group/units): add some lemmas about `divp`
* Rename lemmas, add new ones

### [2019-09-10 09:32:30](https://github.com/leanprover-community/mathlib/commit/fe1575a)
chore(topology): sanity_check pass ([#1416](https://github.com/leanprover-community/mathlib/pull/1416))
* chore(topology): sanity_check pass
* improvement
* avoid _inst_3 to recover instance

### [2019-09-10 01:55:13](https://github.com/leanprover-community/mathlib/commit/72d6325)
feat(sanity_check): greatly improve performance ([#1389](https://github.com/leanprover-community/mathlib/pull/1389))
* feat(sanity_check): greatly improve performance
* move and rename is_in_mathlib_aux
* use boolean connectives in some other places
* remove some whitespace
* fix parentheses, fix tests
the tests correctly spotted a mistake I made
* add ! as boolean negation
* fix binding strength
* undo the use of boolean connectives
* add back notation ! for bnot

### [2019-09-09 21:11:13](https://github.com/leanprover-community/mathlib/commit/228d5ba)
feat(algebra/big_operators): sum_eq_zero_iff_of_nonpos ([#1424](https://github.com/leanprover-community/mathlib/pull/1424))
* feat(algebra/big_operators): sum_eq_zero_iff_of_nonpos
* more order_dual instances

### [2019-09-08 16:37:05](https://github.com/leanprover-community/mathlib/commit/313fe11)
feat(algebra/floor): Split floor from archimedean file. ([#1372](https://github.com/leanprover-community/mathlib/pull/1372))
* feat(algebra/floor): Split floor from archimedean file.
* feat({algebra,rat}/floor): move lemmas/defs from rat.floor to algebra.floor

### [2019-09-08 12:00:15](https://github.com/leanprover-community/mathlib/commit/37b6746)
feat(data/list/basic): make chain.nil a simp lemma ([#1414](https://github.com/leanprover-community/mathlib/pull/1414))

### [2019-09-08 08:47:37](https://github.com/leanprover-community/mathlib/commit/6f7224c)
feat(data/list/defs): move list.sum to list/defs.lean ([#1415](https://github.com/leanprover-community/mathlib/pull/1415))
* feat(data/list/defs): move list.sum to list/defs.lean
* add comment

### [2019-09-08 06:22:25](https://github.com/leanprover-community/mathlib/commit/8bdb147)
feat(topology/local_homeomorph): local homeomorphisms ([#1398](https://github.com/leanprover-community/mathlib/pull/1398))
* feat(topology/local_homeomorph): local homeomorphisms
* local_homeomorph: reviewer comments

### [2019-09-07 05:32:33](https://github.com/leanprover-community/mathlib/commit/10cb0d1)
feat(topology/constructions): distributivity of products over sums ([#1059](https://github.com/leanprover-community/mathlib/pull/1059))
* feat(topology/constructions): distributivity of products over sums
* Update src/topology/maps.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Reverse direction of sigma_prod_distrib

### [2019-09-07 05:17:43](https://github.com/leanprover-community/mathlib/commit/d6a0ac5)
refactor(category_theory/limits/shapes/pullbacks): proof golf ([#1407](https://github.com/leanprover-community/mathlib/pull/1407))
* refactor(category_theory/limits): make is_[co]limit not a class
* refactor(category_theory/limits/shapes/pullbacks): proof golf

### [2019-09-07 05:00:00](https://github.com/leanprover-community/mathlib/commit/8eab714)
refactor(category_theory/limits): make is_[co]limit not a class ([#1405](https://github.com/leanprover-community/mathlib/pull/1405))

### [2019-09-06 22:20:07+02:00](https://github.com/leanprover-community/mathlib/commit/a7f268b)
fix(category_theory/limits/shapes): doc typo [ci skip] ([#1406](https://github.com/leanprover-community/mathlib/pull/1406))

### [2019-09-06 12:45:57+02:00](https://github.com/leanprover-community/mathlib/commit/a5fa162)
chore(data/mv_polynomial): use classical logic ([#1391](https://github.com/leanprover-community/mathlib/pull/1391))
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
* make data.finsupp classical
* trouble with data/polynomial
* ...
* more classical
* merge
* merge
* merge
* fix
* removing more
* minor
* ?
* progress, using convert
* working?
* remove some unnecessary converts
* fixes
* err
* oops
* various
* various
* fix free_comm_ring
* remove test lines
* fix linear_algebra/matrix.lean
* Fix errors in power_series.lean
* trying to turn instances back on
* restore some instances
* no joy
* fix mv_polynomial errors
* another convert

### [2019-09-05 21:37:18](https://github.com/leanprover-community/mathlib/commit/1a0ed80)
fix(naming): typo [ci skip] ([#1401](https://github.com/leanprover-community/mathlib/pull/1401))
* fix(naming): typo [ci skip]
* more typos

### [2019-09-05 11:03:20](https://github.com/leanprover-community/mathlib/commit/b1920f5)
chore(algebra/ordered_field): add simp attributes to inv_pos' and others ([#1400](https://github.com/leanprover-community/mathlib/pull/1400))

### [2019-09-05 09:22:42](https://github.com/leanprover-community/mathlib/commit/7f20843)
chore(order/filter): rephrase filter.has_le ([#1399](https://github.com/leanprover-community/mathlib/pull/1399))
The goal of this tiny refactor is to prevent `filter.sets` leaking when
proving a filter g is finer than another one f. We want the goal to be
`s ∈ f → s ∈ g` instead of the definitionaly equivalent
`s ∈ f.sets ∈ g.sets`

### [2019-09-05 02:48:09](https://github.com/leanprover-community/mathlib/commit/2854909)
feat(bounded_lattice/has_lt): add a `lt` relation independent from `l… ([#1366](https://github.com/leanprover-community/mathlib/pull/1366))
* feat(bounded_lattice/has_lt): add a `lt` relation independent from `le` for `has_top`
* use priority 10 instead of 0

### [2019-09-05 00:46:57](https://github.com/leanprover-community/mathlib/commit/6292825)
feat(data/equiv/local_equiv): define local equivalences  ([#1359](https://github.com/leanprover-community/mathlib/pull/1359))
* feat(data/equiv/local_equiv): define local equivalences
* add doc
* add extensionality attribute
* sanity_check

### [2019-09-04 22:48:55](https://github.com/leanprover-community/mathlib/commit/79a1f84)
fix(tactic/norm_num): bugfix bad proof application ([#1387](https://github.com/leanprover-community/mathlib/pull/1387))
* fix(tactic/norm_num): bugfix bad proof application
* add test case that used to fail
* add try_for
* fix typecheck test
* increase test timeout

### [2019-09-04 20:52:45](https://github.com/leanprover-community/mathlib/commit/3c224f0)
feat (logic/basic): exists_eq' ([#1397](https://github.com/leanprover-community/mathlib/pull/1397))
Not a great name, but `exists_eq_left` and `exists_eq_right` are taken, and it's unlikely to be used except in `simp`

### [2019-09-04 19:28:57](https://github.com/leanprover-community/mathlib/commit/65ffb7b)
fix(topology/uniform_space): simplify continuity proof ([#1396](https://github.com/leanprover-community/mathlib/pull/1396))

### [2019-09-04 17:22:01](https://github.com/leanprover-community/mathlib/commit/06cffeb)
feat(order): add lemma ([#1375](https://github.com/leanprover-community/mathlib/pull/1375))

### [2019-09-04 12:59:55](https://github.com/leanprover-community/mathlib/commit/5d59e8b)
feat(category_theory): finite products give a monoidal structure ([#1340](https://github.com/leanprover-community/mathlib/pull/1340))
* providing minimal API for limits of special shapes
* apis for special shapes
* start
* fintype instances
* copy-paste from monoidal-categories-reboot
* associators, unitors, braidings for binary product
* minor
* minor
* map
* minor
* instances
* blah
* chore(category_theory/monoidal): monoidal_category doesn't extend category
* minor
* minor
* assoc lemma
* coprod
* done?
* fix import
* names
* cleanup
* fix reassoc
* comments
* comments

### [2019-09-04 12:27:02](https://github.com/leanprover-community/mathlib/commit/8cd16b9)
feat(category_theory/sums): sums (disjoint unions) of categories ([#1357](https://github.com/leanprover-community/mathlib/pull/1357))
* feat(category_theory/sum): direct sums of categories
* minor
* tidying
* Fix white space, remove old comments
* rearranging, associator
* add TODO comment about unitors
* fix import
* create /basic.lean files

### [2019-09-04 06:33:49](https://github.com/leanprover-community/mathlib/commit/b079298)
feat(tactic/doc_blame): Use is_auto_generated ([#1395](https://github.com/leanprover-community/mathlib/pull/1395))

### [2019-09-03 21:08:11](https://github.com/leanprover-community/mathlib/commit/ff47fa3)
feat(measure_theory): prove that the Giry monad is a monad in the category_theory sense ([#1259](https://github.com/leanprover-community/mathlib/pull/1259))
* feat(measure_theory): prove that the Giry monad is a monad in the category_theory sense
* Add spaces to fix alignment
* document Measure
* Add documentation
* Add space before colon

### [2019-09-03 18:22:38](https://github.com/leanprover-community/mathlib/commit/b5b40c7)
chore(*): use localized command in mathlib ([#1319](https://github.com/leanprover-community/mathlib/pull/1319))
* chore(*): use localized command in mathlib
remove some open_locale instances
in files that do not import tactic.basic
fix some errors
type class inference failure
fix some more errors
typo
fully specify all names in localized notation
also add some comments to the doc
one more localized import
checkpoint
there is something seriously wrong with type class inference + the transition from constructive to classical logic. Suppose you want to work purely classically, and state a lemma where the statement requires a proof of decidable equality on one of the types. For an abstract type, the only instance of this is classical.prop_decidable, unless you add explicitly an argument that the respective type has decidable equality (which you tend to not want to do if you only work classically). Now when you apply this lemma to a concrete type, where we can infer decidability of equality, type class inference will complain that we used the wrong instance (which is kinda insane: by unification it knows exactly which instance we want to use). A big problem with this, is that you have no idea you will run into this issues later when stating the lemma: Lean will happily accept it
* add TODOs
* fix some errors
* update .gitignore
* fix some timeouts
* replace a couple more local notations

### [2019-09-03 17:52:30](https://github.com/leanprover-community/mathlib/commit/4b6fcd9)
perf(data/gaussian_int): speed up div and mod ([#1394](https://github.com/leanprover-community/mathlib/pull/1394))
avoid using `int.cast`, and use `rat.of_int`.
This sped up `#eval (⟨1414,152⟩ : gaussian_int) % ⟨123,456⟩` from about 5 seconds to 2 milliseconds

### [2019-09-03 17:20:07](https://github.com/leanprover-community/mathlib/commit/974d413)
chore(linear_algebra/determinant): simplify det_mul proof ([#1392](https://github.com/leanprover-community/mathlib/pull/1392))
* chore(linear_algebra/determinant): simplify det_mul proof
Minor improvement to the proof of `det_mul`
* make det_mul_aux more readable

### [2019-09-03 15:36:36](https://github.com/leanprover-community/mathlib/commit/3a58b50)
feat(data/equiv/basic): add more functions for equivalences between complex types ([#1384](https://github.com/leanprover-community/mathlib/pull/1384))
* Add more `equiv` combinators
* Fix compile
* Minor fixes
* Update src/data/equiv/basic.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

### [2019-09-03 13:42:57](https://github.com/leanprover-community/mathlib/commit/a199f85)
feat(topology/uniform_space): Abstract completions ([#1374](https://github.com/leanprover-community/mathlib/pull/1374))
* feat(topology/uniform_space): Abstract completions
Define abstract completions, study their properties and derived
constructions. Use this study in the concrete completion files,
and for comparing completions constructed at different level of
generality, especially for real numbers.
This comes from the perfectoid spaces project.
* Apply suggestions from code review by Johan
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Fix build.
When I created the PR, github complained it couldn't automatically
merge, and I was not careful enough when I merged...
* chore(topology/uniform_space): rename completion_pkg
* fix(compare_reals): create namespace
* Fix build

### [2019-09-03 11:51:43](https://github.com/leanprover-community/mathlib/commit/c7d3629)
fix(restate_axiom): create lemmas from lemmas ([#1390](https://github.com/leanprover-community/mathlib/pull/1390))

### [2019-09-03 09:24:11+02:00](https://github.com/leanprover-community/mathlib/commit/94205c4)
feat(data/fintype): prove `card (subtype p) ≤ card α` ([#1383](https://github.com/leanprover-community/mathlib/pull/1383))
* feat(data/fintype): prove `card (subtype p) ≤ card α`
* Add `cardinal.mk_le_of_subtype`
* Rename `mk_le_of_subtype` to `mk_subtype_le`, use it in `mk_set_le`
Earlier both `mk_subtype_le` and `mk_set_le` took `set α` as an
argument. Now `mk_subtype_le` takes `α → Prop`.

### [2019-09-02 14:19:49](https://github.com/leanprover-community/mathlib/commit/227b682)
feat(category_theory): define `iso.conj` and friends ([#1381](https://github.com/leanprover-community/mathlib/pull/1381))
* feat(category_theory): define `iso.conj` and friends
* Drop 2 `@[simp]` attributes

### [2019-09-02 12:18:38](https://github.com/leanprover-community/mathlib/commit/57d4b41)
feat(category_theory/limits): construct limits from products and equalizers ([#1362](https://github.com/leanprover-community/mathlib/pull/1362))
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
* getting there
* oops
* of_nat_iso
* feat(category_theory/limits/of_nat_isp)
* progress on limits from products and equalizers
* Update src/category_theory/limits/limits.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/category_theory/limits/limits.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* use @[reassoc]
* fixing after rename
* use @[reassoc]
* fix renaming
* complete construction of limits from products and equalizers
* cleanup
* cleanup
* name instance
* whitespace
* Update src/category_theory/limits/limits.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* use simpa

### [2019-09-02 07:54:36](https://github.com/leanprover-community/mathlib/commit/fe7695b)
chore(data/nat/gcd): remove pointless parentheses ([#1386](https://github.com/leanprover-community/mathlib/pull/1386))

### [2019-09-02 06:00:19](https://github.com/leanprover-community/mathlib/commit/d35dc13)
feat(data/nat/gcd): add simple lemmas ([#1382](https://github.com/leanprover-community/mathlib/pull/1382))
* feat(data/nat/gcd): more simple lemmas
* Prove `iff` instead of one side implication

### [2019-09-01 11:29:41](https://github.com/leanprover-community/mathlib/commit/6d2b3ed)
chore(category_theory/notation): consistently use notation for functor.id ([#1378](https://github.com/leanprover-community/mathlib/pull/1378))
* chore(category_theory/notation): consistently use notation for functor.id
* oops, overzealous search-and-replace
* more
* more
* more