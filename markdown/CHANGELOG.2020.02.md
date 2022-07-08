### [2020-02-28 18:23:59+01:00](https://github.com/leanprover-community/mathlib/commit/19a9bdc)
fix(tactic/omega): reify nonconstant ints and nats ([#1748](https://github.com/leanprover-community/mathlib/pull/1748))

### [2020-02-28 16:36:14+01:00](https://github.com/leanprover-community/mathlib/commit/354a4ed)
chore(ci): remove unneeded Lean version restrictions ([#2065](https://github.com/leanprover-community/mathlib/pull/2065))
* remove lean version from CI
* more version references
* fix?
* persist environment var between steps

### [2020-02-28 15:33:18](https://github.com/leanprover-community/mathlib/commit/0760829)
feat(ring_theory): Fractional ideals ([#2062](https://github.com/leanprover-community/mathlib/pull/2062))
* Some WIP work on fractional ideals
* Fill in the `sorry`
* A lot of instances for fractional_ideal
* Show that an invertible fractional ideal `I` has inverse `1 : I`
* Cleanup and documentation
* Move `has_div submodule` to algebra_operations
* More cleanup and documentation
* Explain the `non_zero_divisors R` in the `quotient` section
* whitespace
Co-Authored-By: Scott Morrison <scott@tqft.net>
* `has_inv` instance for `fractional_ideal`
* `set.univ.image` -> `set.range`
* Fix: `mem_div_iff.mpr` should be `mem_div_iff.mp`
(but both reduce to reflexivity anyway)
* Add `mem_div_iff_smul_subset`
Since that is how the definition of `I / J` is traditionally done,
but it is not as convenient to work with, I didn't change the definition
but added a lemma stating the two are equivalent
* whitespace again
(it got broken because I merged changes incorrectly)
* Fix unused argument to `inv_nonzero`

### [2020-02-28 13:49:48](https://github.com/leanprover-community/mathlib/commit/4149099)
fix(tactic/ring): more precise pattern match for div ([#1557](https://github.com/leanprover-community/mathlib/pull/1557))
* fix(tactic/ring): more precise pattern match for div
* add test
* fix instance check for div
* chore(algebra/quadratic_discriminant): add braces in have steps
* use norm_num instead of ring to evaluate exponents
* fix norm_num uses
* fix norm_num pow bug
* bugfix
* fix proof

### [2020-02-28 04:02:06](https://github.com/leanprover-community/mathlib/commit/0bf2064)
chore(scripts): update nolints.txt

### [2020-02-28 01:50:01](https://github.com/leanprover-community/mathlib/commit/4637e5c)
refactor(analysis/calculus/times_cont_diff): massive refactor ([#2012](https://github.com/leanprover-community/mathlib/pull/2012))
* feat(data/fin): append
* Update fin.lean
* Update fintype.lean
* replace but_last with init
* cons and append commute
* feat(*/multilinear): better multilinear
* docstrings
* snoc
* fix build
* comp_snoc and friends
* refactor(analysis/calculus/times_cont_diff): massive refactor
* fix docstring
* move notation
* fix build
* linter
* linter again
* Update src/analysis/calculus/times_cont_diff.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/analysis/calculus/times_cont_diff.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/analysis/calculus/times_cont_diff.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/analysis/calculus/times_cont_diff.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/analysis/calculus/times_cont_diff.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* curryfication -> currying

### [2020-02-27 22:04:31](https://github.com/leanprover-community/mathlib/commit/0e4eb09)
feat(ci): avoid push to Azure if branch has been updated ([#2048](https://github.com/leanprover-community/mathlib/pull/2048))
* avoid push to Azure if branch has been updated
* changes to git config in deploy_nightly.sh break git fetch
* I don't understand why this is different than on my own repo
* artifact upload breaks fetch, I guess?
* factor out git config
* fix env variable
* adjustments
* removed repo check

### [2020-02-27 17:35:47](https://github.com/leanprover-community/mathlib/commit/691456c)
chore(scripts): update nolints.txt

### [2020-02-27 15:18:39](https://github.com/leanprover-community/mathlib/commit/7907f8f)
feat(tactic/tidy): include norm_cast in tidy ([#2063](https://github.com/leanprover-community/mathlib/pull/2063))
* feat(tactic/tidy): include norm_cast in tidy
* Update src/tactic/core.lean

### [2020-02-27 13:32:50](https://github.com/leanprover-community/mathlib/commit/6c2411b)
chore(scripts): update nolints.txt

### [2020-02-27 11:54:47](https://github.com/leanprover-community/mathlib/commit/a46b3e5)
doc(data/finsupp): module docs and docstrings  ([#2059](https://github.com/leanprover-community/mathlib/pull/2059))
* doc(data/finsupp): module docs and docstrings
* chore(data/finsupp): squeeze_simp, cleanup, style
* reviewer comments

### [2020-02-27 01:35:32](https://github.com/leanprover-community/mathlib/commit/ef1e38e)
chore(scripts): update nolints.txt

### [2020-02-26 23:31:28](https://github.com/leanprover-community/mathlib/commit/f0bb2f8)
feat(ring_theory/polynomial): mv_polynomial.integral_domain ([#2021](https://github.com/leanprover-community/mathlib/pull/2021))
* feat(ring_theory/polynomial): mv_polynomial.integral_domain
* Add docstrings
* Add docstrings
* Fix import
* Fix build
* Please linter, please
* Update src/algebra/ring.lean
* Clean up code, process comments
* Update src/data/equiv/fin.lean
* Update src/data/equiv/fin.lean
* Update src/data/equiv/fin.lean
* Update src/ring_theory/polynomial.lean

### [2020-02-26 10:53:53](https://github.com/leanprover-community/mathlib/commit/73b41b2)
chore(data/prod): rename `injective_prod` to `injective.prod` ([#2058](https://github.com/leanprover-community/mathlib/pull/2058))
This way we can use dot notation

### [2020-02-25 22:59:53](https://github.com/leanprover-community/mathlib/commit/6a6beaa)
chore(data/list/basic): drop `append_foldl` and `append_foldr`, add `map_nil` and `prod_singleton` ([#2057](https://github.com/leanprover-community/mathlib/pull/2057))
`append_foldl` and `append_foldr` were unused duplicates of
`foldl_append` and `foldr_append`

### [2020-02-25 21:09:35](https://github.com/leanprover-community/mathlib/commit/7be3e93)
chore(field_theory/minimal_polynomial): fix timeout ([#2054](https://github.com/leanprover-community/mathlib/pull/2054))
* chore(field_theory/minimal_polynomial): fix timeout
* Update src/field_theory/minimal_polynomial.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2020-02-25 19:22:49](https://github.com/leanprover-community/mathlib/commit/06c5594)
chore(analyis/normed_space/banach): split proof to avoid timeout ([#2053](https://github.com/leanprover-community/mathlib/pull/2053))
* chore(analyis/normed_space/banach): split proof to avoid timeout
* delay introducing unnecessary variable
* Apply suggestions from code review
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* fix indent

### [2020-02-25 16:06:50](https://github.com/leanprover-community/mathlib/commit/089d058)
feat(tactic/lint): linter for commutativity lemmas that are marked simp ([#2045](https://github.com/leanprover-community/mathlib/pull/2045))
* feat(tactic/lint): linter for commutativity lemmas that are marked simp
* chore(*): remove simp from commutativity lemmas
* doc(*): document simp_comm linter

### [2020-02-25 14:16:23](https://github.com/leanprover-community/mathlib/commit/450dcdf)
refactor(order/bounds): use dot notation, reorder, prove more properties ([#2028](https://github.com/leanprover-community/mathlib/pull/2028))
* refactor(order/bounds): use dot notation, prove more properties
Also make parts of `complete_lattice` and
`conditionally_complete_lattice` use these lemmas.
* Comments
* Add a module docstring
* Fixes from review, +4 lemmas about images
* Fix a typo in the previous commit
* Update src/order/bounds.lean
* Update src/order/bounds.lean

### [2020-02-25 12:27:02](https://github.com/leanprover-community/mathlib/commit/a227e06)
Unify naming of lemmas related to the (co)lim functor ([#2040](https://github.com/leanprover-community/mathlib/pull/2040))

### [2020-02-25 10:39:52](https://github.com/leanprover-community/mathlib/commit/f77cb57)
chore(data/fintype): move  results depending on big_operators ([#2044](https://github.com/leanprover-community/mathlib/pull/2044))

### [2020-02-25 08:51:21](https://github.com/leanprover-community/mathlib/commit/61d75bb)
chore(scripts): update nolints.txt

### [2020-02-25 06:38:57](https://github.com/leanprover-community/mathlib/commit/17a33f0)
refactor(order/copy): move complete_lattice.copy to its own file ([#2050](https://github.com/leanprover-community/mathlib/pull/2050))
* refactor(order/copy): move complete_lattice.copy to its own file
* Docstrings
* Update src/order/copy.lean

### [2020-02-24 23:51:03](https://github.com/leanprover-community/mathlib/commit/5770369)
refactor(topology/metric_space/isometry): remove isometry_inv_fun from isometric ([#2051](https://github.com/leanprover-community/mathlib/pull/2051))
* refactor(topology/metric_space/isometry): remove isometry_inv_fun from isometric; it is automatic
* Alternative constructor for isometric bijections

### [2020-02-24 22:06:59](https://github.com/leanprover-community/mathlib/commit/3ff50d9)
chore(scripts): update nolints.txt

### [2020-02-24 19:58:16](https://github.com/leanprover-community/mathlib/commit/fb878e7)
feat(tactic/lint): add linter for simp lemmas whose lhs has a variable as head symbol ([#2038](https://github.com/leanprover-community/mathlib/pull/2038))

### [2020-02-24 18:12:09](https://github.com/leanprover-community/mathlib/commit/cb4bdd8)
doc(category_theory): add a few docstrings ([#2046](https://github.com/leanprover-community/mathlib/pull/2046))
* doc(category_theory): add a few docstrings
* Apply suggestions from code review
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2020-02-24 17:33:16+01:00](https://github.com/leanprover-community/mathlib/commit/8030469)
Revert "Update README.md"
This reverts commit 4d3ef8368051e45e1b20e77462b958be3e427c87.

### [2020-02-24 17:31:46+01:00](https://github.com/leanprover-community/mathlib/commit/4d3ef83)
Update README.md

### [2020-02-24 15:43:04](https://github.com/leanprover-community/mathlib/commit/0fc45dc)
feat(tactic/lint): support @[nolint unused_arguments] ([#2041](https://github.com/leanprover-community/mathlib/pull/2041))
* feat(tactic/lint): support @[nolint unused_arguments]
* refactor(scripts/mk_nolint): include failing linter name in nolints.txt
* chore(scripts/nolints): update nolints.txt
* doc(category/functor): add docstrings

### [2020-02-24 11:42:56](https://github.com/leanprover-community/mathlib/commit/32b32ad)
docs(data/set/basic): add module docstring ([#1991](https://github.com/leanprover-community/mathlib/pull/1991))
* adding module docstring
* tidying up
* markdown fixes
* more md tidying
* remove some unnecessary {alpha : Type*}
* responding to comments
* responding to comments

### [2020-02-23 17:01:48](https://github.com/leanprover-community/mathlib/commit/28e4bdf)
feat(topology): an `is_complete` set is a `complete_space` ([#2037](https://github.com/leanprover-community/mathlib/pull/2037))
* feat(*): misc simple lemmas
* +1 lemma
* Rename `inclusion_range` to `range_inclusion`
Co-Authored-By: Johan Commelin <johan@commelin.net>
* feat(topology): an `is_complete` set is a `complete_space`
Also simplify a proof in `topology/metric_space/closeds`.
* Use in `finite_dimension`

### [2020-02-23 13:57:52](https://github.com/leanprover-community/mathlib/commit/16c1d9d)
chore(*): minimise imports of data.list.basic ([#2042](https://github.com/leanprover-community/mathlib/pull/2042))

### [2020-02-23 12:16:38](https://github.com/leanprover-community/mathlib/commit/256bedc)
chore(test): don't use sorry in tests, to reduce noise ([#2043](https://github.com/leanprover-community/mathlib/pull/2043))

### [2020-02-22 22:26:53](https://github.com/leanprover-community/mathlib/commit/bfa2465)
refactor(topology/metric_space/lipschitz): redefine for an `emetric_space` ([#2035](https://github.com/leanprover-community/mathlib/pull/2035))
* refactor(topology/metric_space/lipschitz): redefine for an `emetric_space`
* Fix compile
* Fixes, thanks @sgouzel

### [2020-02-22 20:47:15](https://github.com/leanprover-community/mathlib/commit/ea149c8)
feat(algebraic_geometry/prime_spectrum): prime spectrum of a ring is compact ([#1987](https://github.com/leanprover-community/mathlib/pull/1987))
* wip
* wip
* wip
* wip
* WIP
* WIP
* Reset changes that belong to other PR
* Docstrings
* Add Heine--Borel to docstring
* Cantor's intersection theorem
* Cantor for sequences
* Revert "Reset changes that belong to other PR"
This reverts commit e6026b8819570ef6a763582a25d7ae5ad508134b.
* Move submodule lemmas to other file
* Fix build
* Update prime_spectrum.lean
* Docstring
* Update prime_spectrum.lean
* Slight improvement?
* Slightly improve structure of proof
* WIP
* Cleaning up proofs
* Final fixes

### [2020-02-22 19:10:31](https://github.com/leanprover-community/mathlib/commit/d615ee6)
feat(ci): skip Azure upload if archive already exists ([#2039](https://github.com/leanprover-community/mathlib/pull/2039))
* skip upload if archive already exists
* simplify script
* remove unused variable
* fix

### [2020-02-22 16:24:24](https://github.com/leanprover-community/mathlib/commit/1c6a317)
feat(*): misc simple lemmas ([#2036](https://github.com/leanprover-community/mathlib/pull/2036))
* feat(*): misc simple lemmas
* +1 lemma
* Rename `inclusion_range` to `range_inclusion`
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2020-02-22 13:59:03](https://github.com/leanprover-community/mathlib/commit/603c7ba)
chore(scripts): update nolints.txt

### [2020-02-22 12:05:43](https://github.com/leanprover-community/mathlib/commit/eabcd13)
feat(category_theory/limits): kernels ([#1988](https://github.com/leanprover-community/mathlib/pull/1988))
* chore(category_theory): require morphisms live in Type
* move back to Type
* fixes
* feat(category_theory/limits): kernels
* finishing basic API for kernels
* update post [#1412](https://github.com/leanprover-community/mathlib/pull/1412)
* fix
* documentation
* documentation
* more docs
* replacing dumb code
* forall -> Pi
* removing all instances
* working on Reid's suggested lemmas
* experiments
* lots to do
* Show that equalizers are monomorphisms
* Show that equalizer of (f, f) is always an iso
* Show that an equalizer that is an epimorphism is an isomorphism
* Clean up
* Show that the kernel of a monomorphism is zero
* Fix
* Show that the kernel of a linear map is a kernel in the categorical sense
* Modify proof
* Compactify proof
* Various cleanup
* Some more cleanup
* Fix bibtex
* Address some issues raised during discussion of the PR
* Fix some more incorrect indentation
* Some more minor fixes
* Unify capitalization in Bibtex entries
* Replace equalizer.lift.uniq with equalizer.hom_ext
* Some more slight refactors
* Typo

### [2020-02-22 11:14:19+01:00](https://github.com/leanprover-community/mathlib/commit/a9ed54c)
feat(ci): upload all branch builds to Azure server ([#2032](https://github.com/leanprover-community/mathlib/pull/2032))

### [2020-02-22 09:45:22](https://github.com/leanprover-community/mathlib/commit/928496a)
feat(category_theory/limits) Binary product from pullbacks and terminal object ([#1998](https://github.com/leanprover-community/mathlib/pull/1998))
* Binary product from pullbacks and terminal object
* Update binary_products.lean
* simplifications
* pare down the proof a bit more
* changes from review
* adjust simp to rw

### [2020-02-22 08:15:14](https://github.com/leanprover-community/mathlib/commit/03af46c)
chore(presheafed_space): avoid deterministic timeout ([#1617](https://github.com/leanprover-community/mathlib/pull/1617))
* chore(presheafed_space): avoid deterministic timeout
* fix proofs: now works with -T16000
* fix

### [2020-02-22 00:36:59](https://github.com/leanprover-community/mathlib/commit/11797e6)
chore(topology/metric_space/emetric_space): use filter bases in 2 proofs ([#2034](https://github.com/leanprover-community/mathlib/pull/2034))

### [2020-02-21 22:47:11](https://github.com/leanprover-community/mathlib/commit/ffb6d6e)
feat(tactic): add various tactics about local definitions ([#1953](https://github.com/leanprover-community/mathlib/pull/1953))
* feat(tactic): add various tactics about local definitions
* remove {α β}
* rename generalize' in monotonicity.
* updates after reviews

### [2020-02-21 21:54:18+01:00](https://github.com/leanprover-community/mathlib/commit/86c9417)
doc(topology/dense_embedding): fix list syntax in a comment ([#2033](https://github.com/leanprover-community/mathlib/pull/2033))

### [2020-02-21 19:29:22](https://github.com/leanprover-community/mathlib/commit/ff36e0f)
chore(scripts): update nolints.txt

### [2020-02-21 17:46:31](https://github.com/leanprover-community/mathlib/commit/472156f)
feat(tactic/lint): check that left-hand side of all simp lemmas is in simp-normal form ([#2017](https://github.com/leanprover-community/mathlib/pull/2017))
* feat(tactic/lint): check that lhs of simp lemmas are in simp nf
* fix(topology/metric_space/basic): remove @[simp] from lemmas with {x,y} on the lhs
* chore(topology/local_homeomorph): remove redundant lemmas from the simp set
* fix(topology/algebra/module): fix simp-nf lints
* chore(ring_theory/localization): mark fewer things as simp
* fix(set_theory/ordinal): put lhs into simp-normal form
* chore(algebra/big_operators): fix simp lemmas
* chore(data/set/lattice): remove redundant simp lemmas
* chore(data/set/basic): remove redundant simp lemma
* chore(data/zsqrtd/basic): make simp_nf lint happy
* fix(order/complete_lattice): remove lemmas from simp set
* chore(order/filter/filter_product): fix linting issues
* feat(data/mv_polynomial): add simp lemmas about neg
* fix(data/multiset): fix simp_nf linter issues
* chore(data/list/sigma): fix simp_nf linter issues
* fix(data/list/basic): remove redundant and unapplicable simp lemmas
* fix(measure_theory/set_integral): remove redundant simp lemma
* fix(measure_theory/l1_space): remove redundant simp lemmas
* fix(algebra/group_power): remove simp lemmas that are not in nf
* fix(algebra/field): remove redundant simp lemma
* chore(data/list/alist): remove simp lemmas
* fix(data/int/basic): simp-normal form for coercions...
* fix(data/finset): formulate simp-lemmas for simp-nf
* fix(data/int/parity): use simp-normal form
* fix(data/equiv/denumerable): remove redundant simp lemma
* fix(category_theory/**): fix simp-normal forms
* fix(set_theory/zfc): put simp lemmas in simp-normal form
* fix(tactlic/lint): ignore sub_eq_add_neg for simp_nf lint
* doc(tactic/lint): add simp_nf linter to module doc
* doc(docs/commands): add simp_nf linter
* fix(*): put lemmas in simp-normal form

### [2020-02-21 11:26:12](https://github.com/leanprover-community/mathlib/commit/bb7631f)
feat(algebraic_geometry/prime_spectrum): vanishing ideal ([#1972](https://github.com/leanprover-community/mathlib/pull/1972))
* wip
* wip
* Remove stuff for next PR
* Update prime_spectrum.lean
* Process comments

### [2020-02-21 05:36:39](https://github.com/leanprover-community/mathlib/commit/b30b5e9)
feat(tactic/hint): update tactic list ([#2024](https://github.com/leanprover-community/mathlib/pull/2024))
* feat(tactic/hint): update tactic list
* Removing `fsplit` in favour of `fconstructor`.
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
* fix test
* silence a test

### [2020-02-21 02:50:57](https://github.com/leanprover-community/mathlib/commit/888e75b)
refactor(*/multilinear): better right curryfication ([#1985](https://github.com/leanprover-community/mathlib/pull/1985))
* feat(data/fin): append
* Update fin.lean
* Update fintype.lean
* replace but_last with init
* cons and append commute
* feat(*/multilinear): better multilinear
* docstrings
* snoc
* fix build
* comp_snoc and friends
* fix docstring
* typo

### [2020-02-20 15:52:23-08:00](https://github.com/leanprover-community/mathlib/commit/eeedc6a)
fix(*): remove loopy simp lemmas ([#2026](https://github.com/leanprover-community/mathlib/pull/2026))

### [2020-02-20 21:25:20](https://github.com/leanprover-community/mathlib/commit/b0eeea4)
fix(data/bool): remove simp attribute from commutativity lemmas ([#2027](https://github.com/leanprover-community/mathlib/pull/2027))

### [2020-02-20 16:55:22](https://github.com/leanprover-community/mathlib/commit/aefdb86)
feat(data/int/basic): format -42 as -42 instead of -(41+1) ([#2025](https://github.com/leanprover-community/mathlib/pull/2025))

### [2020-02-20 15:24:23](https://github.com/leanprover-community/mathlib/commit/d933ea5)
doc(lint): add linter missing from list of defaults ([#2023](https://github.com/leanprover-community/mathlib/pull/2023))

### [2020-02-20 14:50:00+01:00](https://github.com/leanprover-community/mathlib/commit/43dd938)
chore(ci): check roadmap directory ([#2022](https://github.com/leanprover-community/mathlib/pull/2022))
* chore(ci): check roadmap directory
partially addresses [#2016](https://github.com/leanprover-community/mathlib/pull/2016)
* fix roadmap compilation

### [2020-02-20 11:06:30](https://github.com/leanprover-community/mathlib/commit/4e398cc)
chore(scripts): update nolints.txt

### [2020-02-20 09:21:34](https://github.com/leanprover-community/mathlib/commit/68b9c16)
feat(algebra/group): add `units.lift_right` and `is_unit.lift_right` ([#2020](https://github.com/leanprover-community/mathlib/pull/2020))
* Rename type variables, add a docstring
* feat(algebra/group): add `units.lift_right` and `is_unit.lift_right`
These defs/lemmas may be useful for `monoid_localization`.

### [2020-02-20 02:23:59](https://github.com/leanprover-community/mathlib/commit/d42d29b)
fix(tactic/tauto): fix typos ([#2019](https://github.com/leanprover-community/mathlib/pull/2019))
* fix(tactic/tauto): fix typos
* fix same error in tactics.md

### [2020-02-20 00:52:33](https://github.com/leanprover-community/mathlib/commit/34724f4)
chore(scripts): update nolints.txt

### [2020-02-19 23:20:36](https://github.com/leanprover-community/mathlib/commit/2d6556d)
feat(analysis/mean_inequalities) : Prove AM-GM ([#1836](https://github.com/leanprover-community/mathlib/pull/1836))
* feat(analysis/mean_inequalities) : Prove AM-GM
* Update, add more inequalities
* Update src/analysis/convex/specific_functions.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/analysis/mean_inequalities.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/analysis/mean_inequalities.lean
* Small fixes, thanks @sgouezel
* Update src/analysis/mean_inequalities.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2020-02-19 21:46:28](https://github.com/leanprover-community/mathlib/commit/5b77b64)
refactor(analysis/calculus/tangent_cone): split a proof into parts ([#2013](https://github.com/leanprover-community/mathlib/pull/2013))
* refactor(analysis/calculus/tangent_cone): split a proof into parts
Prove `submodule.eq_top_of_nonempty_interior` and use it in the
proof of `unique_diff_on_convex`.
* Update src/analysis/normed_space/basic.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Fix a docstring.
* Update src/topology/algebra/module.lean

### [2020-02-19 12:42:42](https://github.com/leanprover-community/mathlib/commit/bcdb4c3)
chore(scripts): update nolints.txt

### [2020-02-19 11:05:33](https://github.com/leanprover-community/mathlib/commit/8563695)
refactor(algebra/associated): move `is_unit` def to `algebra/group` ([#2015](https://github.com/leanprover-community/mathlib/pull/2015))
* refactor(algebra/associated): move `is_unit` def to `algebra/group`
I think it makes sense to have it near `units`.
* Add a docstring to `units`, mention `is_unit` there.

### [2020-02-19 08:48:40](https://github.com/leanprover-community/mathlib/commit/177c06f)
chore(measure_theory/*): make a few proofs slightly shorter ([#2014](https://github.com/leanprover-community/mathlib/pull/2014))

### [2020-02-18 23:13:13](https://github.com/leanprover-community/mathlib/commit/8700aa7)
feat(docs): install mathlibtools package with pip ([#2010](https://github.com/leanprover-community/mathlib/pull/2010))

### [2020-02-18 20:06:18](https://github.com/leanprover-community/mathlib/commit/2198d2c)
feat(roadmap): add some formal roadmaps in topology ([#1914](https://github.com/leanprover-community/mathlib/pull/1914))
* feat(roadmap): add some formal roadmaps in topology
* Update roadmap/topology/paracompact.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update roadmap/todo.lean
* Update roadmap/topology/shrinking_lemma.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* add `todo` tactic as a wrapper for `exact todo`
* Update roadmap/topology/shrinking_lemma.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* copyright notices and module docs
* oops

### [2020-02-18 17:07:17](https://github.com/leanprover-community/mathlib/commit/0c2dbd5)
chore(analysis/normed_space/basic): implicit args ([#2011](https://github.com/leanprover-community/mathlib/pull/2011))
Arguments to these `iff`s should be implicit.

### [2020-02-18 14:56:44](https://github.com/leanprover-community/mathlib/commit/8a660ec)
feat(scripts/deploy_nightly): change pre-release to release ([#2009](https://github.com/leanprover-community/mathlib/pull/2009))
The `--pre-release` doesn't really achieve anything as far as we can tell, and complicates some scripting: see https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20nightlies

### [2020-02-18 12:09:47](https://github.com/leanprover-community/mathlib/commit/115e513)
chore(topology/constructions): rename `tendsto_prod_mk_nhds` ([#2008](https://github.com/leanprover-community/mathlib/pull/2008))
New name is `tendsto.prod_mk_nhds`. Also use it in a few proofs and
generalize `tendsto_smul` to a `topological_semimodule`.

### [2020-02-18 09:33:08](https://github.com/leanprover-community/mathlib/commit/1435a19)
refactor(topology/maps): split the proof of `is_open_map_iff_nhds_le` ([#2007](https://github.com/leanprover-community/mathlib/pull/2007))
Extract a lemma `is_open_map.image_mem_nhds` from the proof, and make
the proof use this lemma.

### [2020-02-18 02:10:56](https://github.com/leanprover-community/mathlib/commit/2d00f20)
feat(data/fin): init and snoc ([#1978](https://github.com/leanprover-community/mathlib/pull/1978))
* feat(data/fin): append
* Update fin.lean
* Update fintype.lean
* replace but_last with init
* cons and append commute
* change append to snoc
* comp_snoc and friends
* markdown in docstrings
* fix docstring

### [2020-02-18 00:40:07](https://github.com/leanprover-community/mathlib/commit/b373dae)
feat(linear_algebra/contraction): define contraction maps between a module and its dual ([#1973](https://github.com/leanprover-community/mathlib/pull/1973))
* feat(linear_algebra/contraction): define contraction maps between a module and its dual
* Implicit carrier types for smul_comm
* Add comment with license and file description
* Build on top of extant linear_map.smul_right
* Feedback from code review

### [2020-02-17 23:10:41](https://github.com/leanprover-community/mathlib/commit/4299a80)
refactor(topology/subset_properties): use finite subcovers indexed by types ([#1980](https://github.com/leanprover-community/mathlib/pull/1980))
* wip
* wip
* wip
* wip
* WIP
* WIP
* Reset changes that belong to other PR
* Docstrings
* Add Heine--Borel to docstring
* Cantor's intersection theorem
* Cantor for sequences
* Generalise Cantor intersection thm
* More fixes

### [2020-02-17 21:45:03](https://github.com/leanprover-community/mathlib/commit/bbf5d1a)
refactor(algebra/field): partially migrate to bundled homs ([#1999](https://github.com/leanprover-community/mathlib/pull/1999))
* refactor(algebra/field): partially migrate to bundled homs
* Add a few `@[simp]` attrs

### [2020-02-17 20:10:20](https://github.com/leanprover-community/mathlib/commit/6cdd96b)
chore(*): reduce proof size ([#2006](https://github.com/leanprover-community/mathlib/pull/2006))

### [2020-02-17 18:37:15](https://github.com/leanprover-community/mathlib/commit/5eefae2)
chore(set_theory/ordinal): shorten proofs ([#2005](https://github.com/leanprover-community/mathlib/pull/2005))

### [2020-02-17 17:00:24](https://github.com/leanprover-community/mathlib/commit/5f06692)
feat(data/set/intervals): add `Ici_subset_Ici`, `Iic_subset_Iic` ([#2003](https://github.com/leanprover-community/mathlib/pull/2003))

### [2020-02-17 13:55:11](https://github.com/leanprover-community/mathlib/commit/f8d0931)
feat(tactic/rename_var): A teaching tactic ([#1974](https://github.com/leanprover-community/mathlib/pull/1974))
* feat(tactic/rename_var): A teaching tactic
The goal is to teach that bound variables names are irrelevant, and also
help clarify local context.
* allow rename_var to act on several locations at once
* Apply suggestions from code review
by Rob.
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>

### [2020-02-17 12:19:30](https://github.com/leanprover-community/mathlib/commit/cd0e2f6)
add "Try this: " to squeeze_simp and suggest ([#1990](https://github.com/leanprover-community/mathlib/pull/1990))
* add "Try this" to squeeze_simp and suggest
* update docs
* fix suggest tests
* add "try this" to rcases, rintro, and tidy
* add "try this" to hint

### [2020-02-17 10:45:46](https://github.com/leanprover-community/mathlib/commit/557b01d)
chore(analysis/calculus/tangent_cone): simplify a proof ([#2002](https://github.com/leanprover-community/mathlib/pull/2002))
Use `linear_map.span_inl_union_inr` instead of repeating its proof.

### [2020-02-17 09:07:47](https://github.com/leanprover-community/mathlib/commit/b42e568)
chore(algebra/group_power): rename type vars, minor cleanup ([#1997](https://github.com/leanprover-community/mathlib/pull/1997))
The only non-BC change should be removing
is_group_hom.map_gpow` / `is_add_group_hom.map_gsmul` in favor of `monoid_hom.map_gpow`.

### [2020-02-17 07:29:08](https://github.com/leanprover-community/mathlib/commit/d673e55)
feat(ring_theory/algebra): add ext_iff ([#1996](https://github.com/leanprover-community/mathlib/pull/1996))
* feat(ring_theory/algebra): add ext_iff
* also add eq_top_iff
* Update src/ring_theory/algebra.lean

### [2020-02-17 05:59:51](https://github.com/leanprover-community/mathlib/commit/770c56b)
doc(topology/metric_space/basic): add 1 docstring ([#2000](https://github.com/leanprover-community/mathlib/pull/2000))
* doc(topology/metric_space/basic): add 1 docstring
* Update src/topology/metric_space/basic.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2020-02-17 04:35:05](https://github.com/leanprover-community/mathlib/commit/dbb21c8)
chore(scripts): update nolints.txt

### [2020-02-17 02:59:50](https://github.com/leanprover-community/mathlib/commit/1b1b626)
chore(topology/sequences): use filter bases, minor fixes ([#2001](https://github.com/leanprover-community/mathlib/pull/2001))

### [2020-02-15 23:38:34](https://github.com/leanprover-community/mathlib/commit/c7eb6f8)
chore(algebra/group/hom): add a missing `simp` lemma ([#1994](https://github.com/leanprover-community/mathlib/pull/1994))

### [2020-02-15 13:33:39](https://github.com/leanprover-community/mathlib/commit/dbb61ea)
feat(tactic/hint): try out a customisable list of tactics, and report which ones make progress ([#1955](https://github.com/leanprover-community/mathlib/pull/1955))
* feat(tactic/hint): try out a fixed list of tactics, and report which ones make progress
* add hint to tactic.default
* make the list of hint tactics customisable
* suggestion
* fix linting errors
* simplify use of add_hint, and add hints
* remove TODO
* Update src/tactic/hint.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* various
* Update docs/tactics.md

### [2020-02-15 09:59:41](https://github.com/leanprover-community/mathlib/commit/0b6d398)
chore(algebra/group/basic): rename type vars ([#1989](https://github.com/leanprover-community/mathlib/pull/1989))

### [2020-02-14 17:55:38](https://github.com/leanprover-community/mathlib/commit/d36930b)
chore(scripts): update nolints.txt

### [2020-02-14 16:27:08](https://github.com/leanprover-community/mathlib/commit/edefe20)
feat(ci): update nolints.txt after master builds ([#1979](https://github.com/leanprover-community/mathlib/pull/1979))
* feat(ci): update nolints.txt after master builds
* avoid failure when no changes
* update for production
* update condition
* header override is already unset

### [2020-02-14 10:30:14](https://github.com/leanprover-community/mathlib/commit/938960e)
fix(scripts/deploy_docs): remove last trace of nightly builds ([#1986](https://github.com/leanprover-community/mathlib/pull/1986))

### [2020-02-14 01:44:12](https://github.com/leanprover-community/mathlib/commit/4441394)
chore(category_theory/conj): avoid `is_mul_hom` ([#1984](https://github.com/leanprover-community/mathlib/pull/1984))

### [2020-02-14 00:07:30](https://github.com/leanprover-community/mathlib/commit/9a91125)
chore(group_theory/sub*) : rename type vars ([#1982](https://github.com/leanprover-community/mathlib/pull/1982))
Use `M`, `G`, `A` instead of greek letters

### [2020-02-13 22:27:55](https://github.com/leanprover-community/mathlib/commit/db1c500)
refactor(data/set/function): use dot notation ([#1934](https://github.com/leanprover-community/mathlib/pull/1934))

### [2020-02-13 21:47:45+01:00](https://github.com/leanprover-community/mathlib/commit/0372fb0)
fix(scripts/deploy_docs.sh): header override is already unset
Before, the nightly and doc deploys were running in different builds.
Now they're in the same build, so we don't need to (and can't) unset the
variable twice.

### [2020-02-13 20:44:53](https://github.com/leanprover-community/mathlib/commit/56a5240)
feat(calculus/fderiv): invariance of fderiv under linear equivs ([#1977](https://github.com/leanprover-community/mathlib/pull/1977))
* feat(calculus/fderiv): invariance of fderiv under linear equivs
* missing material
* coherent naming conventions
* fix build
* coherent naming conventions
* yury's comments

### [2020-02-13 19:03:11](https://github.com/leanprover-community/mathlib/commit/a79a055)
refactor(group_theory/submonoid): redefine `subtype.monoid` manually ([#1981](https://github.com/leanprover-community/mathlib/pull/1981))
* refactor(group_theory/submonoid): redefine `subtype.monoid` manually
This way `group.to_monoid subtype.group` is defeq `subtype.monoid group.to_monoid`.
* Fix compile of `ring_theory/integral_closure`

### [2020-02-13 18:26:28+01:00](https://github.com/leanprover-community/mathlib/commit/b7ffc6f)
fix(mergify): remove references to nightly builds

### [2020-02-13 13:18:09+01:00](https://github.com/leanprover-community/mathlib/commit/aa4da84)
chore(ci): don't build with Lean nightly ([#1975](https://github.com/leanprover-community/mathlib/pull/1975))
* chore(ci): don't build with Lean nightly
* fix condition for doc upload

### [2020-02-11 15:33:16](https://github.com/leanprover-community/mathlib/commit/abd412b)
chore(scripts): update nolints ([#1976](https://github.com/leanprover-community/mathlib/pull/1976))

### [2020-02-11 13:43:45](https://github.com/leanprover-community/mathlib/commit/176852d)
feat(tactic/lint): check if inhabited instances should be nonempty ([#1971](https://github.com/leanprover-community/mathlib/pull/1971))
* add inhabited vs nonempty linter
* add new linter to ci
* start updating files to pass linter
* more linter fixes
* fix more linter errors
* more fixes
* fix build
* remove unnecessary instances
* nicer proof
* adjust inhabit tactic
* improve proof
* move instance to better place
* generalize instance
* fix build
* inhabited -> nonempty
* fix build

### [2020-02-11 09:25:41](https://github.com/leanprover-community/mathlib/commit/4e2c7e3)
feat(topology/subset_properties): alternative definitions of irreducible and connected ([#1970](https://github.com/leanprover-community/mathlib/pull/1970))
* refactor(topology/*): irreducible and connected sets are nonempty
* Fix typos
* Fix more typos
* Update src/topology/subset_properties.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/topology/subset_properties.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Refactor 'nonempty' fields
* Fix spacing in set-builder
* Use dot notation
* Write a comment on the nonempty assumption
* Apply suggestions from code review
* irreducible_iff statements
* Fix build
* Tiny improvements
* Justify that connected spaces are nonempty
* Add docstrings
* Update src/topology/subset_properties.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update subset_properties.lean

### [2020-02-10 16:32:09](https://github.com/leanprover-community/mathlib/commit/93ba8b6)
refactor(topology/metric_space): introduce&use `edist`/`dist` bases ([#1969](https://github.com/leanprover-community/mathlib/pull/1969))
* refactor(topology/metric_space): introduce&use `edist`/`dist` bases
* Introduce bases for `emetric_space` and `metric_space`.
* Make some proofs use general facts about filter bases.
* Fix some lint errors
* Update src/topology/metric_space/emetric_space.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* +2 docstrings

### [2020-02-09 09:33:32](https://github.com/leanprover-community/mathlib/commit/777f214)
refactor(data/matrix,linear_algebra): Use `matrix.mul` as default multiplication in matrix lemmas ([#1959](https://github.com/leanprover-community/mathlib/pull/1959))
* Change `has_mul.mul` to `matrix.mul` in a few `simp` lemmas
* Standardise more lemmas for matrix multiplication
* Generalize `to_pequiv_mul_matrix` to rectangular matrices

### [2020-02-08 13:25:39](https://github.com/leanprover-community/mathlib/commit/bcb63eb)
refactor(topology/*): irreducible and connected sets are nonempty ([#1964](https://github.com/leanprover-community/mathlib/pull/1964))
* refactor(topology/*): irreducible and connected sets are nonempty
* Fix typos
* Fix more typos
* Update src/topology/subset_properties.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/topology/subset_properties.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Refactor 'nonempty' fields
* Fix spacing in set-builder
* Use dot notation
* Write a comment on the nonempty assumption
* Apply suggestions from code review
* Fix build
* Tiny improvements

### [2020-02-08 10:42:31](https://github.com/leanprover-community/mathlib/commit/2e18388)
feat(linear_algebra): The Special linear group SL(n, R) ([#1960](https://github.com/leanprover-community/mathlib/pull/1960))
* Define the special linear group
* Make definitions independent of PR [#1959](https://github.com/leanprover-community/mathlib/pull/1959)
That PR changes `det_mul` to have another, still definitionally equal, type.
If the invocations to `det_mul` are independent of syntactic equality, i.e. we
only pass `det_mul` to `erw`, this branch should be compatible with the state
before the change and after.
* Documentation and code style improvements
* Improve module docstring
* Fix documentation
`matrix.special_linear_group` is not a set but a type
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Don't directly coerce from SL to linear maps
Now we coerce from `matrix.special_linear_group n R` to `matrix n n R` instead
of `general_linear_group R (n -> R)`
* Whitespace fixes
* Fix failing build in `src/linear_algebra/dual.lean`
* Give an almost generic formula for `det_adjugate`
* Move `det_eq_one_of_card_eq_zero` to the correct section
* Replace the ad-hoc assumption of `det_adjugate_of_invertible` with `is_unit`
* Fix linting error
There was an unnecessary assumption [decidable_eq α] floating around
* Replace `special_linear_group.val` with the appropriate coercions
* whitespace
Correctly indent continued line
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Docstrings for the `det_adjugate_of_...` lemmas

### [2020-02-07 16:57:48](https://github.com/leanprover-community/mathlib/commit/2007d34)
feat(analysis/normed_space/multilinear): norm on continuous multilinear maps ([#1956](https://github.com/leanprover-community/mathlib/pull/1956))
* feat(analysis/normed_space/multilinear): norm on continuous multilinear maps
* docstring
* improved docstrings

### [2020-02-07 06:21:24](https://github.com/leanprover-community/mathlib/commit/f912a6b)
feat(algebraic_geometry/prime_spectrum): first definitions ([#1957](https://github.com/leanprover-community/mathlib/pull/1957))
* Start on prime spectrum
* Define comap betwee prime spectra; prove continuity
* Update src/algebraic_geometry/prime_spectrum.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* chore(*): rename `filter.inhabited_of_mem_sets` to `nonempty_of_mem_sets` ([#1943](https://github.com/leanprover-community/mathlib/pull/1943))
In other names `inhabited` means that we have a `default` element.
* refactor(linear_algebra/multilinear): cleanup of multilinear maps ([#1921](https://github.com/leanprover-community/mathlib/pull/1921))
* staging [ci skip]
* staging
* staging
* cleanup norms
* complete currying
* docstrings
* docstrings
* cleanup
* nonterminal simp
* golf
* missing bits for derivatives
* sub_apply
* cleanup
* better docstrings
* remove two files
* reviewer's comments
* use fintype
* line too long
* feat(ring_theory/power_series): several simp lemmas ([#1945](https://github.com/leanprover-community/mathlib/pull/1945))
* Small start on generating functions
* Playing with Bernoulli
* Finished sum_bernoulli
* Some updates after PRs
* Analogue for mv_power_series
* Cleanup after merged PRs
* feat(ring_theory/power_series): several simp lemmas
* Remove file that shouldn't be there yet
* Update src/ring_theory/power_series.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Generalise lemma to canonically_ordered_monoid
* Update name
* Fix build
* feat(tactic/lint): Three new linters, update illegal_constants ([#1947](https://github.com/leanprover-community/mathlib/pull/1947))
* add three new linters
* fix failing declarations
* restrict and rename illegal_constants linter
* update doc
* update ge_or_gt test
* update mk_nolint
* fix error
* Update scripts/mk_nolint.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update src/meta/expr.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* clarify unfolds_to_class
* fix names since name is no longer protected
also change one declaration back to instance, since it did not cause a linter failure
* fix errors, move notes to docstrings
* add comments to docstring
* update mk_all.sh
* fix linter errors
* feat(number_theory/bernoulli): Add definition of Bernoulli numbers ([#1952](https://github.com/leanprover-community/mathlib/pull/1952))
* Small start on generating functions
* Playing with Bernoulli
* Finished sum_bernoulli
* Some updates after PRs
* Analogue for mv_power_series
* Cleanup after merged PRs
* feat(number_theory/bernoulli): Add definition of Bernoulli numbers
* Remove old file
* Process comments
* feat(topology/algebra/multilinear): define continuous multilinear maps ([#1948](https://github.com/leanprover-community/mathlib/pull/1948))
* feat(data/set/intervals): define intervals and prove basic properties ([#1949](https://github.com/leanprover-community/mathlib/pull/1949))
* things about intervals
* better documentation
* better file name
* add segment_eq_interval
* better proof for is_measurable_interval
* better import and better proof
* better proof
* refactor(*): migrate from `≠ ∅` to `set.nonempty` ([#1954](https://github.com/leanprover-community/mathlib/pull/1954))
* refactor(*): migrate from `≠ ∅` to `set.nonempty`
Sorry for a huge PR but it's easier to do it in one go.
Basically, I got rid of all `≠ ∅` in theorem/def types, then fixed
compile.
I also removed most lemmas about `≠ ∅` from `set/basic` to make sure
that I didn't miss something I should change elsewhere. Should I
restore (some of) them?
* Fix compile of `archive/`
* Drop +1 unneeded argument, thanks @sgouezel.
* Fix build
* Update src/algebraic_geometry/prime_spectrum.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Update src/algebraic_geometry/prime_spectrum.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Change I to s, and little fixes
* Update src/algebraic_geometry/prime_spectrum.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* Update src/algebraic_geometry/prime_spectrum.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* Update src/algebraic_geometry/prime_spectrum.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* Update src/algebraic_geometry/prime_spectrum.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
* Indentation
* Update prime_spectrum.lean
* fix build

### [2020-02-06 15:25:57](https://github.com/leanprover-community/mathlib/commit/fb160f0)
refactor(topology/continuous_on): use filter bases ([#1968](https://github.com/leanprover-community/mathlib/pull/1968))

### [2020-02-06 12:20:38](https://github.com/leanprover-community/mathlib/commit/0e533d0)
refactor(topology/basic): rewrite some proofs using filter bases ([#1967](https://github.com/leanprover-community/mathlib/pull/1967))

### [2020-02-06 10:51:04](https://github.com/leanprover-community/mathlib/commit/b4c2ec2)
chore(topology/metric_space/basic): simplify `tendsto_nhds` ([#1966](https://github.com/leanprover-community/mathlib/pull/1966))
* chore(topology/metric_space/basic): simplify `tendsto_nhds`
No reason to have an extra `∃ n ∈ f`.
* whitespace
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2020-02-06 09:12:40](https://github.com/leanprover-community/mathlib/commit/34f9a17)
feat(*): a few simple lemmas ([#1965](https://github.com/leanprover-community/mathlib/pull/1965))

### [2020-02-05 20:37:51](https://github.com/leanprover-community/mathlib/commit/8c086a6)
chore(tactic/basic,default): add missing tactics ([#1962](https://github.com/leanprover-community/mathlib/pull/1962))

### [2020-02-05 17:46:23](https://github.com/leanprover-community/mathlib/commit/8786ea6)
refactor(measure_theory/set_integral): move set integral into namespace set and add some lemmas ([#1950](https://github.com/leanprover-community/mathlib/pull/1950))
* move set integral into namespace set and add some lemmas
* Update bochner_integration.lean
* better theorem names
* Update set_integral.lean
* Update set_integral.lean

### [2020-02-05 14:27:45](https://github.com/leanprover-community/mathlib/commit/08581cc)
feat(tactic/rename): Add improved renaming tactic ([#1916](https://github.com/leanprover-community/mathlib/pull/1916))
* feat(tactic/rename): Add improved renaming tactic
We add a tactic `rename'` which works like `rename`, with the following
improvements:
* Multiple hypotheses can be renamed at once.
* Renaming always preserve the position of a hypothesis in the context.
* Move private def `drop_until_inclusive` to `list.after`
* Change `rename'` docs to rely less on knowledge of `rename`
* Improve formatting of list.after docs

### [2020-02-05 13:11:44+01:00](https://github.com/leanprover-community/mathlib/commit/6845aaa)
chore(*): bump Lean version to 3.5.1c ([#1958](https://github.com/leanprover-community/mathlib/pull/1958))
* chore(leanpkg.toml): bump lean version to 3.5.0
* update CI to build with 3.5.0
* update mergify
* update contribute docs
* update deploy_nightly.sh
* 3.5.0 -> 3.5.1

### [2020-02-05 06:25:59](https://github.com/leanprover-community/mathlib/commit/dd8da51)
refactor(*): migrate from `≠ ∅` to `set.nonempty` ([#1954](https://github.com/leanprover-community/mathlib/pull/1954))
* refactor(*): migrate from `≠ ∅` to `set.nonempty`
Sorry for a huge PR but it's easier to do it in one go.
Basically, I got rid of all `≠ ∅` in theorem/def types, then fixed
compile.
I also removed most lemmas about `≠ ∅` from `set/basic` to make sure
that I didn't miss something I should change elsewhere. Should I
restore (some of) them?
* Fix compile of `archive/`
* Drop +1 unneeded argument, thanks @sgouezel.

### [2020-02-04 22:11:27](https://github.com/leanprover-community/mathlib/commit/253f75c)
feat(data/set/intervals): define intervals and prove basic properties ([#1949](https://github.com/leanprover-community/mathlib/pull/1949))
* things about intervals
* better documentation
* better file name
* add segment_eq_interval
* better proof for is_measurable_interval
* better import and better proof
* better proof

### [2020-02-04 19:56:41](https://github.com/leanprover-community/mathlib/commit/475a669)
feat(topology/algebra/multilinear): define continuous multilinear maps ([#1948](https://github.com/leanprover-community/mathlib/pull/1948))

### [2020-02-04 14:32:21](https://github.com/leanprover-community/mathlib/commit/9dbc894)
feat(number_theory/bernoulli): Add definition of Bernoulli numbers ([#1952](https://github.com/leanprover-community/mathlib/pull/1952))
* Small start on generating functions
* Playing with Bernoulli
* Finished sum_bernoulli
* Some updates after PRs
* Analogue for mv_power_series
* Cleanup after merged PRs
* feat(number_theory/bernoulli): Add definition of Bernoulli numbers
* Remove old file
* Process comments

### [2020-02-04 12:42:22](https://github.com/leanprover-community/mathlib/commit/c5febb5)
feat(tactic/lint): Three new linters, update illegal_constants ([#1947](https://github.com/leanprover-community/mathlib/pull/1947))
* add three new linters
* fix failing declarations
* restrict and rename illegal_constants linter
* update doc
* update ge_or_gt test
* update mk_nolint
* fix error
* Update scripts/mk_nolint.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* Update src/meta/expr.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* clarify unfolds_to_class
* fix names since name is no longer protected
also change one declaration back to instance, since it did not cause a linter failure
* fix errors, move notes to docstrings
* add comments to docstring
* update mk_all.sh
* fix linter errors

### [2020-02-03 13:52:06](https://github.com/leanprover-community/mathlib/commit/bfa7055)
feat(ring_theory/power_series): several simp lemmas ([#1945](https://github.com/leanprover-community/mathlib/pull/1945))
* Small start on generating functions
* Playing with Bernoulli
* Finished sum_bernoulli
* Some updates after PRs
* Analogue for mv_power_series
* Cleanup after merged PRs
* feat(ring_theory/power_series): several simp lemmas
* Remove file that shouldn't be there yet
* Update src/ring_theory/power_series.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Generalise lemma to canonically_ordered_monoid
* Update name
* Fix build

### [2020-02-03 11:26:46](https://github.com/leanprover-community/mathlib/commit/6264667)
refactor(linear_algebra/multilinear): cleanup of multilinear maps ([#1921](https://github.com/leanprover-community/mathlib/pull/1921))
* staging [ci skip]
* staging
* staging
* cleanup norms
* complete currying
* docstrings
* docstrings
* cleanup
* nonterminal simp
* golf
* missing bits for derivatives
* sub_apply
* cleanup
* better docstrings
* remove two files
* reviewer's comments
* use fintype
* line too long

### [2020-02-03 09:55:20](https://github.com/leanprover-community/mathlib/commit/59629da)
chore(*): rename `filter.inhabited_of_mem_sets` to `nonempty_of_mem_sets` ([#1943](https://github.com/leanprover-community/mathlib/pull/1943))
In other names `inhabited` means that we have a `default` element.

### [2020-02-03 07:14:34](https://github.com/leanprover-community/mathlib/commit/a342132)
refactor(topology/metric_space/emetric_space): redefine `diam` ([#1941](https://github.com/leanprover-community/mathlib/pull/1941))
* feat(data/set/basic): define `set.subsingleton`
Also rename `nonempty.of_subset` to `nonempty.mono`
* Add a missing lemma
* refactor(topology/metric_space/emetric_space): redefine `diam`
* Give a more readable definition of `emetric.diam`;
* Add a few lemmas including diameter of a pair and of a triple of
  points;
* Simplify some proofs;
* Reformulate some theorems to use `∀ (x ∈ s) (y ∈ s)` instead
  of `∀ x y ∈ s` because the former plays better with existing `simp`
  lemmas.
* Redefine `set.subsingleton` using `(x ∈ s) (y ∈ s)`, prove `metric.diam_triangle`

### [2020-02-02 12:18:31](https://github.com/leanprover-community/mathlib/commit/1843bfc)
feat(algebra/pointwise): pointwise scalar-multiplication lemmas ([#1925](https://github.com/leanprover-community/mathlib/pull/1925))
* feat(algebra/pointwise): more lemmas about scaling sets
- rename `smul_set` to `scale_set` for disambiguation
- define `scale_set_action`, which subsumes `one_smul_set`
- additional lemmas lemmas
* fix(analysis/convex): refactor proofs for `scale_set`
* feat(algebra/pointwise): re-organise file
- subsume `pointwise_mul_action`
* feat(algebra/pointwise): remove `pointwise_mul_action`
- subsumed by `smul_set_action` with left-regular action.

### [2020-02-02 10:49:49](https://github.com/leanprover-community/mathlib/commit/58899d4)
feat(data/set/basic): define `set.subsingleton` ([#1939](https://github.com/leanprover-community/mathlib/pull/1939))
* feat(data/set/basic): define `set.subsingleton`
Also rename `nonempty.of_subset` to `nonempty.mono`
* Add a missing lemma

### [2020-02-02 01:12:16](https://github.com/leanprover-community/mathlib/commit/bacd4da)
chore(data/subtype): fix `∀` vs `Π` ([#1940](https://github.com/leanprover-community/mathlib/pull/1940))

### [2020-02-01 23:40:10](https://github.com/leanprover-community/mathlib/commit/11b9497)
feat(data/fintype): range_prod_eq_univ_prod ([#1937](https://github.com/leanprover-community/mathlib/pull/1937))
* feat(algebra/big_operators): range_prod_eq_univ_prod
* fix build, part 1
* fix build, part 2
* fix build, part 3
* Fix build, part 4

### [2020-02-01 18:15:45](https://github.com/leanprover-community/mathlib/commit/6e6e6da)
feat(data/nat/basic): two identities for `choose` ([#1936](https://github.com/leanprover-community/mathlib/pull/1936))
* feat(data/nat/basic): two identities for `choose`
* fix build

### [2020-02-01 16:26:13](https://github.com/leanprover-community/mathlib/commit/a500c24)
Update units.lean ([#1938](https://github.com/leanprover-community/mathlib/pull/1938))

### [2020-02-01 10:59:44](https://github.com/leanprover-community/mathlib/commit/50bbb8d)
fix(data/nat/basic): make arguments to `choose_succ_right_eq` explicit ([#1935](https://github.com/leanprover-community/mathlib/pull/1935))