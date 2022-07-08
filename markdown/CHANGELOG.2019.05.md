### [2019-05-31 20:59:47](https://github.com/leanprover-community/mathlib/commit/4f6307e)
feat(topology/algebra/open_subgroup): basics on open subgroups  ([#1067](https://github.com/leanprover-community/mathlib/pull/1067))
* Dump the file into mathlib
* feat(algebra/pi_instances): product of submonoids/groups/rings
From the perfectoid project.
* Small changes
* feat(topology/algebra/open_subgroup): basics on open subgroups
* Some proof compression
* Update src/topology/algebra/open_subgroup.lean

### [2019-05-31 19:49:44](https://github.com/leanprover-community/mathlib/commit/6237939)
fix(data/nat/enat): change [] to {} in some lemmas ([#1054](https://github.com/leanprover-community/mathlib/pull/1054))
* fix(data/nat/enat): change [] to {} in some lemmas
* Update enat.lean
* remove space

### [2019-05-31 17:26:55](https://github.com/leanprover-community/mathlib/commit/8ebea31)
feat(category_theory/monoidal): the monoidal category of types ([#1100](https://github.com/leanprover-community/mathlib/pull/1100))
* feat(category_theory/iso): missing lemmas
* formatting
* formatting
* almost
* oops
* getting there
* one more
* sleep
* good to go
* monoidal category of types
* fix names
* renaming
* linebreak
* temporary notations
* notations for associator, unitors?
* more notation
* names
* more names
* oops
* renaming, and namespaces
* comment
* fix comment
* remove unnecessary open, formatting
* removing dsimps
* replace with simp lemmas
* fix
* Update types.lean
* fix namespace

### [2019-05-31 06:43:58](https://github.com/leanprover-community/mathlib/commit/2db435d)
chore(category_theory): move all instances (e.g. Top, CommRing, Meas) into the root namespace ([#1074](https://github.com/leanprover-community/mathlib/pull/1074))
* splitting adjunction.lean
* chore(CommRing/adjunctions): refactor proofs
* remove unnecessary assumptions
* add helpful doc-string
* cleanup
* chore(category_theory): move all instances (e.g. Top, CommRing, Meas) to the root namespace
* minor
* breaking things, haven't finished yet
* deterministic timeout
* unfold_coes to the rescue
* one more int.cast
* yet another int.cast
* fix merge
* minor
* merge
* fix imports
* fix merge
* fix imports/namespaces
* more namespace fixes
* fixes
* delete stray file

### [2019-05-30 12:43:47](https://github.com/leanprover-community/mathlib/commit/c49ac06)
feat(category_theory/monoidal): monoidal categories, monoidal functors ([#1002](https://github.com/leanprover-community/mathlib/pull/1002))
* feat(category_theory/iso): missing lemmas
* formatting
* formatting
* almost
* oops
* getting there
* one more
* sleep
* good to go
* fix names
* renaming
* linebreak
* temporary notations
* notations for associator, unitors?
* more notation
* names
* more names
* oops
* renaming, and namespaces
* comment
* fix comment
* remove unnecessary open, formatting
* removing dsimps
* replace with simp lemmas
* fix

### [2019-05-29 22:06:00](https://github.com/leanprover-community/mathlib/commit/4845b66)
feat(ring_theory): free_ring and free_comm_ring ([#734](https://github.com/leanprover-community/mathlib/pull/734))
* feat(ring_theory): free_ring and free_comm_ring
* Define isomorphism with mv_polynomial int
* Ring hom free_ring -> free_comm_ring; 1 sorry left
* Coe from free_ring to free_comm_ring is ring_hom
* WIP
* WIP
* WIP
* WIP
* Refactoring a bunch of stuff
* functor.map_equiv
* Fix build
* Fix build
* Make multiset.subsingleton_equiv computable
* Define specific equivs using general machinery
* Fix build
* Remove old commented code
* feat(data/equiv/functor): map_equiv
* fix(data/multiset): remove duplicate setoid instance
* namespace changes

### [2019-05-29 11:10:22](https://github.com/leanprover-community/mathlib/commit/d935bc3)
feat(presheaves/stalks): stalks of presheafs, and presheafed spaces with extra structure on stalks ([#1018](https://github.com/leanprover-community/mathlib/pull/1018))
* feat(category_theory/colimits): missing simp lemmas
* feat(category_theory): functor.map_nat_iso
* define `functor.map_nat_iso`, and relate to whiskering
* rename `functor.on_iso` to `functor.map_iso`
* add some missing lemmas about whiskering
* fix(category_theory): presheaves, unbundled and bundled, and pushforwards
* restoring `(opens X)ᵒᵖ`
* various changes from working on stalks
* rename `nbhds` to `open_nhds`
* fix introduced typo
* typo
* compactify a proof
* rename `presheaf` to `presheaf_on_space`
* fix(category_theory): turn `has_limits` classes into structures
* naming instances to avoid collisions
* breaking up instances.topological_spaces
* fixing all the other pi-type typclasses
* fix import
* oops
* fix import
* feat(category_theory): stalks of sheaves
* renaming
* fixes after rebase
* nothing
* yay, got rid of the @s
* attempting a very general version of structured stalks
* missed one
* typo
* WIP
* oops
* the presheaf of continuous functions to ℂ
* restoring eq_to_hom simp lemmas
* removing unnecessary simp lemma
* remove another superfluous lemma
* removing the nat_trans and vcomp notations; use \hom and \gg
* a simpler proposal
* getting rid of vcomp
* fix
* splitting files
* renaming
* probably working again?
* update notation
* remove old lemma
* fix
* comment out unfinished stuff
* cleanup
* use iso_whisker_right instead of map_nat_iso
* proofs magically got easier?
* improve some proofs
* moving instances
* remove crap
* tidy
* minimise imports
* chore(travis): disable the check for minimal imports
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: semorrison <scott@tqft.net>
* writing `op_induction` tactic, and improving proofs
* squeeze_simping
* cleanup
* rearranging
* cleanup
* cleaning up
* cleaning up
* move
* cleaning up
* structured stalks
* comment
* structured stalks
* more simp lemmas
* formatting
* Update src/category_theory/instances/Top/presheaf_of_functions.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
* fixes in response to review
* tidy regressions... :-(
* oops
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/category_theory/instances/TopCommRing/basic.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* def to lemma
* remove useless lemma
* explicit associator
* broken
* can't get proofs to work...
* remove superfluous imports
* missing headers
* change example
* reverting changes to tidy
* remove presheaf_Z, as it doesn't work at the moment
* fixes
* fixes
* fix
* postponing stuff on structured stalks for a later PR
* coercions
* getting rid of all the `erw`
* omitting some proofs
* deleting more proofs
* convert begin ... end to by
* local

### [2019-05-29 06:03:02](https://github.com/leanprover-community/mathlib/commit/0de4bba)
feat(ordered_group): add missing instance ([#1094](https://github.com/leanprover-community/mathlib/pull/1094))

### [2019-05-28 15:01:35](https://github.com/leanprover-community/mathlib/commit/b20b722)
fix(tactic/rcases): add parse desc to rcases/rintro ([#1091](https://github.com/leanprover-community/mathlib/pull/1091))

### [2019-05-26 20:12:00](https://github.com/leanprover-community/mathlib/commit/d434397)
feat(group_theory/conjugates) : define conjugates ([#1029](https://github.com/leanprover-community/mathlib/pull/1029))
* feat(algebra/order_functions): generalize strict_mono.monotone ([#1022](https://github.com/leanprover-community/mathlib/pull/1022))
* moving stuff to where it belongs
* removed unecessary import
* Changed to union
* Update src/group_theory/subgroup.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Stylistic changes
* Added authorship
* Moved mem_conjugates_of_set
* Authorship
* Trying fixes
* Putting everything in the right order
* removed import

### [2019-05-24 05:29:59](https://github.com/leanprover-community/mathlib/commit/c6a7f30)
refactor(set_theory/ordinal): shorten proof of well_ordering_thm ([#1078](https://github.com/leanprover-community/mathlib/pull/1078))
* refactor(set_theory/ordinal): shorten proof of well_ordering_thm§
* Update ordinal.lean
* Update ordinal.lean
* Update ordinal.lean
* Improve readability
* shorten proof
* Shorten proof

### [2019-05-23 13:50:06](https://github.com/leanprover-community/mathlib/commit/62acd6b)
chore(CommRing/adjunctions): refactor proofs ([#1049](https://github.com/leanprover-community/mathlib/pull/1049))
* splitting adjunction.lean
* chore(CommRing/adjunctions): refactor proofs
* remove unnecessary assumptions
* add helpful doc-string
* cleanup
* breaking things, haven't finished yet
* deterministic timeout
* unfold_coes to the rescue
* one more int.cast
* yet another int.cast
* Update src/data/mv_polynomial.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/data/mv_polynomial.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* WIP
* Fix build
* Fix build

### [2019-05-23 11:08:00](https://github.com/leanprover-community/mathlib/commit/15fecbd)
doc(finsupp,category_theory): fixes ([#1075](https://github.com/leanprover-community/mathlib/pull/1075))
* doc
* update emb_domain doc string
* typo

### [2019-05-22 19:04:36](https://github.com/leanprover-community/mathlib/commit/d07e3b3)
feat(linear_algebra/basic): general_linear_group basics ([#1064](https://github.com/leanprover-community/mathlib/pull/1064))
* feat(linear_algebra/basic): general_linear_group basics
This patch proves that the general_linear_group (defined as units in the
endomorphism ring) are equivalent to the group of linear equivalences.
* shorten proof of ext
* Add mul_equiv
* Use coe
* Fix stupid error

### [2019-05-22 16:32:40](https://github.com/leanprover-community/mathlib/commit/f004d32)
feat(data/nat): various lemmas ([#1017](https://github.com/leanprover-community/mathlib/pull/1017))
* feat(data/nat): various lemmas
* protect a definition
* fixes
* Rob's suggestions
* Mario’s proof
(Working offline, let’s see what Travis says)
* minigolf

### [2019-05-21 21:29:42](https://github.com/leanprover-community/mathlib/commit/971ddcc)
feat(*): image_closure ([#1069](https://github.com/leanprover-community/mathlib/pull/1069))
Prove that the image of the closure is the closure of the image,
for submonoids/groups/rings.
From the perfectoid project.

### [2019-05-21 16:01:07](https://github.com/leanprover-community/mathlib/commit/3461399)
refactor(integration.lean): changing `measure_space` to `measurable_space` ([#1072](https://github.com/leanprover-community/mathlib/pull/1072))
I've been using this file and `range_const` doesn't seem to require the spurious `measure_space` instance. `measurable_space` seems to suffice.

### [2019-05-20 19:27:04](https://github.com/leanprover-community/mathlib/commit/cb30c97)
feat(algebra/pi_instances): product of submonoids/groups/rings ([#1066](https://github.com/leanprover-community/mathlib/pull/1066))
From the perfectoid project.

### [2019-05-20 18:35:19](https://github.com/leanprover-community/mathlib/commit/0ab8a89)
feat(category_theory): limits in CommRing ([#1006](https://github.com/leanprover-community/mathlib/pull/1006))
* feat(category_theory): limits in CommRing
* by
* rename
* sections
* Update src/category_theory/types.lean
Co-Authored-By: Johannes Hölzl <johannes.hoelzl@gmx.de>

### [2019-05-20 15:36:59](https://github.com/leanprover-community/mathlib/commit/8cf7c4c)
chore(topology/algebra/monoid): continuous_mul_left/right ([#1065](https://github.com/leanprover-community/mathlib/pull/1065))

### [2019-05-20 15:11:50](https://github.com/leanprover-community/mathlib/commit/593938c)
chore(ring_theory/algebra): simp-lemmas for alg_hom.to_linear_map ([#1062](https://github.com/leanprover-community/mathlib/pull/1062))
* chore(ring_theory/algebra): simp-lemmas for alg_hom.to_linear_map
From the perfectoid project.
* Stupid error
* Update src/ring_theory/algebra.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>

### [2019-05-20 11:52:29](https://github.com/leanprover-community/mathlib/commit/d001abf)
feat(tactic/basic): adds `contrapose` tactic ([#1015](https://github.com/leanprover-community/mathlib/pull/1015))
* feat(tactic/basic): adds `contrapose` tactic
* fix(tactic/push_neg): fix is_prop testing
* Setup error message testing following Rob, add tests for `contrapose`
* refactor(tactic/interactive): move noninteractive success_if_fail_with_msg to tactic/core

### [2019-05-20 11:16:53](https://github.com/leanprover-community/mathlib/commit/15a6af2)
feat(topology/opens): continuous.comap : opens Y → opens X ([#1061](https://github.com/leanprover-community/mathlib/pull/1061))
* feat(topology/opens): continuous.comap : opens Y → opens X
From the perfectoid project.
* Update opens.lean

### [2019-05-20 09:26:59](https://github.com/leanprover-community/mathlib/commit/d4c7b7a)
feat(tactic/linarith): better input syntax linarith only [...] ([#1056](https://github.com/leanprover-community/mathlib/pull/1056))
* feat(tactic/ring, tactic/linarith): add reducibility parameter
* fix(tactic/ring): interactive parsing for argument to ring1
* feat(tactic/linarith): better input syntax linarith only [...]
* fix(docs/tactics): fix linarith doc

### [2019-05-19 17:40:09](https://github.com/leanprover-community/mathlib/commit/f253401)
refactor: coherent composition order ([#1055](https://github.com/leanprover-community/mathlib/pull/1055))

### [2019-05-19 13:39:22](https://github.com/leanprover-community/mathlib/commit/cb4c9ee)
refactor(topology/metric/gromov_hausdorff): make Hausdorff_edist irreducible ([#1052](https://github.com/leanprover-community/mathlib/pull/1052))
* refactor(topology/metric/gromov_hausdorff): remove linarith calls
* refactor(topology/metric/hausdorff_dist): make hausdorff_dist irreducible

### [2019-05-19 12:47:56](https://github.com/leanprover-community/mathlib/commit/b9cb69c)
feat(topology/order): make nhds irreducible ([#1043](https://github.com/leanprover-community/mathlib/pull/1043))
* feat(topology/order): make nhds irreducible
* move nhds irreducible to topology.basic

### [2019-05-18 16:36:44-04:00](https://github.com/leanprover-community/mathlib/commit/73c3f71)
feat(tactic/squeeze): remove noise from output ([#1047](https://github.com/leanprover-community/mathlib/pull/1047))

### [2019-05-18 13:27:57](https://github.com/leanprover-community/mathlib/commit/fa0e757)
refactor(data/complex/exponential): improve trig proofs ([#1041](https://github.com/leanprover-community/mathlib/pull/1041))
* fix(data/complex/exponential): make complex.exp irreducible
See discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/-T50000.20challenge
Using `ring` (and other tactics) on terms involving `exp` can lead to some unpleasant and unnecessary unfolding.
* refactor(data/complex/exponential): improve trig proofs
* fix build
* fix(algebra/group): prove lemma for comm_semigroup instead of comm_monoid

### [2019-05-17 20:21:42](https://github.com/leanprover-community/mathlib/commit/5e5298b)
feat(adjointify): make definition easier for elaborator ([#1045](https://github.com/leanprover-community/mathlib/pull/1045))

### [2019-05-17 18:53:41](https://github.com/leanprover-community/mathlib/commit/45afa86)
fix(topology/stone_cech): faster proof from @PatrickMassot ([#1042](https://github.com/leanprover-community/mathlib/pull/1042))

### [2019-05-17 17:38:35](https://github.com/leanprover-community/mathlib/commit/901178e)
feat(set_theory/surreal): surreal numbers ([#958](https://github.com/leanprover-community/mathlib/pull/958))
* feat(set_theory/surreal): surreal numbers
* doc(set_theory/surreal): surreal docs
* minor changes in surreal

### [2019-05-17 16:13:20](https://github.com/leanprover-community/mathlib/commit/0b35022)
refactor: change variables order in some composition lemmas ([#1035](https://github.com/leanprover-community/mathlib/pull/1035))

### [2019-05-17 14:46:24](https://github.com/leanprover-community/mathlib/commit/f633c94)
feat(tactic/basic): add tactic.rewrite, and sort list ([#1039](https://github.com/leanprover-community/mathlib/pull/1039))

### [2019-05-17 13:20:21](https://github.com/leanprover-community/mathlib/commit/a6c1f37)
fix(data/complex/exponential): make complex.exp irreducible ([#1040](https://github.com/leanprover-community/mathlib/pull/1040))
See discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/-T50000.20challenge
Using `ring` (and other tactics) on terms involving `exp` can lead to some unpleasant and unnecessary unfolding.

### [2019-05-17 06:56:38](https://github.com/leanprover-community/mathlib/commit/96ea9b9)
chore(opposites): merge two definitions of `opposite` ([#1036](https://github.com/leanprover-community/mathlib/pull/1036))
* chore(opposites): merge two definitions of `opposite`
* merge `opposite.opposite` from `algebra/opposites` with
  `category_theory.opposite` from `category_theory/opposites`, and put
  it into `data/opposite`
* main reasons: DRY, avoid confusion if both namespaces are open
* see https://github.com/leanprover-community/mathlib/pull/538#issuecomment-459488227
* Authors merged from `git blame` output on both original files;
  I assume my contribution to be trivial
* Update opposite.lean

### [2019-05-17 00:16:39](https://github.com/leanprover-community/mathlib/commit/def48b0)
feat(data/nat/basic): make decreasing induction eliminate to Sort ([#1032](https://github.com/leanprover-community/mathlib/pull/1032))
* add interface for decreasing_induction to Sort
* make decreasing_induction a def
* add simp tags and explicit type

### [2019-05-16 12:58:27](https://github.com/leanprover-community/mathlib/commit/ad0f42d)
fix(data/nat/enat): Fix typo in lemma name ([#1037](https://github.com/leanprover-community/mathlib/pull/1037))

### [2019-05-16 07:24:12](https://github.com/leanprover-community/mathlib/commit/c75c096)
chore(*): reduce imports ([#1033](https://github.com/leanprover-community/mathlib/pull/1033))
* chore(*): reduce imports
* restoring import in later file
* fix import

### [2019-05-15 17:08:22](https://github.com/leanprover-community/mathlib/commit/b5aae18)
feat(category_theory): monos and epis in Type and Top ([#1030](https://github.com/leanprover-community/mathlib/pull/1030))
* feat(category_theory): monos and epis in Type and Top
* imports
* add file header
* use notation for adjunction

### [2019-05-15 13:26:27](https://github.com/leanprover-community/mathlib/commit/136e67a)
refactor(topology): change continuous_at_within to continuous_within_at ([#1034](https://github.com/leanprover-community/mathlib/pull/1034))

### [2019-05-15 09:44:25](https://github.com/leanprover-community/mathlib/commit/3022caf)
feat(tactic/terminal_goal): determine if other goals depend on the current one ([#984](https://github.com/leanprover-community/mathlib/pull/984))
* feat(tactics): add "terminal_goal" tactic and relatives
* fix(test/tactics): renaming test functions to avoid a name collision
* fix(tactic): moving terminal_goal to tactic/basic.lean
* fix(test/tactics): open tactics
* touching a file, to prompt travis to try again
* terminal_goal
* fix
* merge

### [2019-05-14 20:21:21](https://github.com/leanprover-community/mathlib/commit/7b579b7)
feat(category_theory): adjoint equivalences and limits under equivalences ([#986](https://github.com/leanprover-community/mathlib/pull/986))
* feat(category_theory): adjoint equivalences and limits
* Define equivalences to be adjoint equivalences.
  * Show that one triangle law implies the other for equivalences
  * Prove that having a limit of shape `J` is preserved under an equivalence `J ≌ J'`.
  * Construct an adjoint equivalence from a (non-adjoint) equivalence
* Put `nat_iso.app` in the `iso` namespace, so that we can write `α.app` for `α : F ≅ G`.
* Add some basic lemmas about equivalences, isomorphisms.
* Move some lemmas from `nat_trans` to `functor_category` and state them using `F ⟶ G` instead of `nat_trans F G` (maybe these files should just be merged?)
* Some small tweaks, improvements
* opposite of discrete is discrete
This also shows that C^op has coproducts if C has products and vice versa
Also fix rebase errors
* fix error (I don't know what caused this to break)
* Use tidy a bit more
* construct an adjunction from an equivalence
add notation `⊣` for an adjunction.
make some arguments of adjunction constructors implicit
* use adjunction notation
* formatting
* do adjointify_η as a natural iso directly, to avoid checking naturality
* tersifying
* fix errors, a bit of cleanup
* fix elements.lean
* fix error, address comments

### [2019-05-14 18:15:35](https://github.com/leanprover-community/mathlib/commit/ae8f197)
feat(data/nat/basic): decreasing induction ([#1031](https://github.com/leanprover-community/mathlib/pull/1031))
* feat(data/nat/basic): decreasing induction
* feat(data/nat/basic): better proof of decreasing induction

### [2019-05-14 14:46:29](https://github.com/leanprover-community/mathlib/commit/e7b64c5)
feat(data/equiv/functor): map_equiv ([#1026](https://github.com/leanprover-community/mathlib/pull/1026))
* feat(data/equiv/functor): map_equiv
* golf proofs

### [2019-05-14 15:06:32+02:00](https://github.com/leanprover-community/mathlib/commit/02857d5)
fix(docs/tactics): fix layout, remove noise

### [2019-05-14 12:43:19](https://github.com/leanprover-community/mathlib/commit/22790e0)
feat(tactic): new tactics to normalize casts inside expressions ([#988](https://github.com/leanprover-community/mathlib/pull/988))
* new tactics for normalizing casts
* update using the norm_cast tactics
* minor proof update
* minor changes
* moved a norm_cast lemma
* minor changes
* fix(doc/tactics): make headers uniform
* nicer proof using discharger
* fixed numerals handling by adding simp_cast lemmas
* add documentation
* fixed unnecessary normalizations in assumption_mod_cast
* minor proof update
* minor coding style update
* documentation update
* rename flip_equation to expr.flip_eq
* update proofs to remove boiler plate code about casts
* revert to old proof
* fixed imports and moved attributes
* add test file
* new attribute system
- the attribute norm_cast is split into norm_cast and norm_cast_rev
- update of the equation flipping mechanism
- update of the numerals handling
* syntax fix
* change attributes names
* test update
* small update
* add elim_cast attribute
* add examples for attributes
* new examples

### [2019-05-14 11:13:33](https://github.com/leanprover-community/mathlib/commit/fe19bdb)
fix(data/multiset): remove duplicate setoid instance ([#1027](https://github.com/leanprover-community/mathlib/pull/1027))
* fix(data/multiset): remove duplicate setoid instance
* s/ : Type uu//

### [2019-05-14 10:24:51](https://github.com/leanprover-community/mathlib/commit/ade99c8)
feat(analysis/normed_space/deriv): more material on derivatives ([#966](https://github.com/leanprover-community/mathlib/pull/966))
* feat(analysis/normed_space/deriv): more material on derivatives
* feat(analysis/normed_space/deriv): minor improvements
* feat(analysis/normed_space/deriv) rename fderiv_at_within to fderiv_within_at
* feat(analysis/normed_space/deriv): more systematic renaming
* feat(analysis/normed_space/deriv): fix style
* modify travis.yml as advised by Simon Hudon
* fix travis.yml, second try
* feat(analysis/normed_space/deriv): add two missing lemmas

### [2019-05-14 07:24:40](https://github.com/leanprover-community/mathlib/commit/a72641b)
squeeze_simp ([#1019](https://github.com/leanprover-community/mathlib/pull/1019))

### [2019-05-14 05:35:17](https://github.com/leanprover-community/mathlib/commit/cefb9d4)
feat(category_theory/opposites): iso.op ([#1021](https://github.com/leanprover-community/mathlib/pull/1021))

### [2019-05-14 01:23:18](https://github.com/leanprover-community/mathlib/commit/6dc0682)
feat(algebra/order_functions): generalize strict_mono.monotone ([#1022](https://github.com/leanprover-community/mathlib/pull/1022))

### [2019-05-13 23:54:13](https://github.com/leanprover-community/mathlib/commit/07ba43e)
feat(topology/constructions): topology of sum types ([#1016](https://github.com/leanprover-community/mathlib/pull/1016))

### [2019-05-13 22:28:23](https://github.com/leanprover-community/mathlib/commit/f8385b1)
feat(data/equiv/basic): equiv.nonempty_iff_nonempty ([#1020](https://github.com/leanprover-community/mathlib/pull/1020))

### [2019-05-13 20:36:11](https://github.com/leanprover-community/mathlib/commit/01b345c)
feat(tactics/interactive): choose uses exists_prop ([#1014](https://github.com/leanprover-community/mathlib/pull/1014))
* feat(tactics/interactive): choose uses exists_prop
* fix build

### [2019-05-13 20:00:57](https://github.com/leanprover-community/mathlib/commit/c8a0bb6)
feat(category_theory/products): missing simp lemmas ([#1003](https://github.com/leanprover-community/mathlib/pull/1003))
* feat(category_theory/products): missing simp lemmas
* cleanup proofs
* fix proof
* squeeze_simp

### [2019-05-13 19:33:32](https://github.com/leanprover-community/mathlib/commit/6c35df0)
feat(category_theory/iso): missing lemmas ([#1001](https://github.com/leanprover-community/mathlib/pull/1001))
* feat(category_theory/iso): missing lemmas
* formatting
* formatting
* oops
* one more
* sleep

### [2019-05-13 18:39:56+02:00](https://github.com/leanprover-community/mathlib/commit/82f151f)
document the change in scripts ([#1024](https://github.com/leanprover-community/mathlib/pull/1024))

### [2019-05-13 15:42:01](https://github.com/leanprover-community/mathlib/commit/70cd00b)
feat(Top.presheaf_ℂ): presheaves of functions to topological commutative rings ([#976](https://github.com/leanprover-community/mathlib/pull/976))
* feat(category_theory/colimits): missing simp lemmas
* feat(category_theory): functor.map_nat_iso
* define `functor.map_nat_iso`, and relate to whiskering
* rename `functor.on_iso` to `functor.map_iso`
* add some missing lemmas about whiskering
* fix(category_theory): presheaves, unbundled and bundled, and pushforwards
* restoring `(opens X)ᵒᵖ`
* various changes from working on stalks
* rename `nbhds` to `open_nhds`
* fix introduced typo
* typo
* compactify a proof
* rename `presheaf` to `presheaf_on_space`
* fix(category_theory): turn `has_limits` classes into structures
* naming instances to avoid collisions
* breaking up instances.topological_spaces
* fixing all the other pi-type typclasses
* fix import
* oops
* fix import
* missed one
* typo
* WIP
* oops
* the presheaf of continuous functions to ℂ
* restoring eq_to_hom simp lemmas
* removing unnecessary simp lemma
* remove another superfluous lemma
* removing the nat_trans and vcomp notations; use \hom and \gg
* a simpler proposal
* getting rid of vcomp
* fix
* splitting files
* renaming
* update notation
* fix
* cleanup
* use iso_whisker_right instead of map_nat_iso
* proofs magically got easier?
* improve some proofs
* moving instances
* remove crap
* tidy
* minimise imports
* chore(travis): disable the check for minimal imports
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: semorrison <scott@tqft.net>
* writing `op_induction` tactic, and improving proofs
* squeeze_simping
* cleanup
* rearranging
* cleanup
* cleaning up
* cleaning up
* move
* Update src/category_theory/instances/Top/presheaf_of_functions.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
* fixes in response to review

### [2019-05-13 11:21:50-04:00](https://github.com/leanprover-community/mathlib/commit/b9b5bb4)
chore(Github): no need to wait for Appveyor anymopre

### [2019-05-13 11:12:35-04:00](https://github.com/leanprover-community/mathlib/commit/e42d808)
chore(scripts): migrate scripts to own repo ([#1011](https://github.com/leanprover-community/mathlib/pull/1011))

### [2019-05-13 18:20:20+10:00](https://github.com/leanprover-community/mathlib/commit/4864515)
feat(category_theory): lemmas about cancellation ([#1005](https://github.com/leanprover-community/mathlib/pull/1005))
* feat(category_theory): lemmas about cancellation
* rename hypotheses
* Squeeze proofs

### [2019-05-12 14:51:35](https://github.com/leanprover-community/mathlib/commit/1e0761e)
feat(topology/maps): closed embeddings ([#1013](https://github.com/leanprover-community/mathlib/pull/1013))
* feat(topology/maps): closed embeddings
* fix "is_open_map"

### [2019-05-12 01:21:18](https://github.com/leanprover-community/mathlib/commit/de5d038)
feat(logic/function): comp₂ -- useful for binary operations ([#993](https://github.com/leanprover-community/mathlib/pull/993))
* feat(logic/function): comp₂ -- useful for binary operations
For example, when working with topological groups
it does not suffice to look at `mul : G → G → G`;
we need to require that `G × G → G` is continuous.
This lemma helps with rewriting back and forth
between the curried and the uncurried versions.
* Fix: we are already in the function namespace, duh
* Replace comp₂ with a generalisation of bicompr
* fix error in bitraversable
* partially open function namespace in bitraversable

### [2019-05-11 18:16:49-04:00](https://github.com/leanprover-community/mathlib/commit/a154ded)
fix(docs/*): docs reorganization [skip ci] ([#1012](https://github.com/leanprover-community/mathlib/pull/1012))

### [2019-05-11 14:35:23-04:00](https://github.com/leanprover-community/mathlib/commit/8e71cee)
chore(build): remove script testing on PRs [skip ci]

### [2019-05-11 13:26:30-04:00](https://github.com/leanprover-community/mathlib/commit/e6d959d)
docs(algebra/ring): document compatibility hack [skip ci]

### [2019-05-11 12:46:31-04:00](https://github.com/leanprover-community/mathlib/commit/c7d870e)
chore(compatibility): compatibility with Lean 3.5.0c ([#1007](https://github.com/leanprover-community/mathlib/pull/1007))

### [2019-05-11 15:00:03](https://github.com/leanprover-community/mathlib/commit/60da4f4)
feat(data/polynomial): degree_eq_one_of_irreducible_of_root ([#1010](https://github.com/leanprover-community/mathlib/pull/1010))

### [2019-05-11 13:14:21](https://github.com/leanprover-community/mathlib/commit/8603e6b)
refactor(algebra/associated): rename nonzero_of_irreducible to ne_zero_of_irreducible ([#1009](https://github.com/leanprover-community/mathlib/pull/1009))

### [2019-05-11 00:09:41](https://github.com/leanprover-community/mathlib/commit/6858c2f)
fix(category/fold): use correct `opposite` ([#1008](https://github.com/leanprover-community/mathlib/pull/1008))

### [2019-05-10 02:32:26](https://github.com/leanprover-community/mathlib/commit/91a7fc2)
fix(tactic/basic): missing `conv` from tactic.basic ([#1004](https://github.com/leanprover-community/mathlib/pull/1004))

### [2019-05-10 00:53:48](https://github.com/leanprover-community/mathlib/commit/e66e1f3)
feat(set_theory): add to cardinal, ordinal, cofinality ([#963](https://github.com/leanprover-community/mathlib/pull/963))
* feat(set_theory): add to cardinal, ordinal, cofinality
The main new fact is the infinite pigeonhole principle
Also includes many basic additions
* fix name change in other files
* address all of Mario's comments
* use classical tactic in order/basic
I did not use it for well_founded.succ, because that resulted in an error in lt_succ
* fix error

### [2019-05-09 09:29:20](https://github.com/leanprover-community/mathlib/commit/5329bf3)
feat(algebra/pointwise): More lemmas on pointwise multiplication ([#997](https://github.com/leanprover-community/mathlib/pull/997))
* feat(algebra/pointwise): More lemmas on pointwise multiplication
* Fix build, hopefully
* Fix build
* to_additive + fix formatting

### [2019-05-09 05:36:49](https://github.com/leanprover-community/mathlib/commit/df5edde)
refactor(strict_mono): make definition + move to order_functions ([#998](https://github.com/leanprover-community/mathlib/pull/998))
* refactor(strict_mono): make definition + move to order_functions
* Weaken assumptions from preorder to has_lt

### [2019-05-08 22:40:27](https://github.com/leanprover-community/mathlib/commit/8f5d240)
refactor(order/basic): make type class args explicit in {*}order.lift ([#995](https://github.com/leanprover-community/mathlib/pull/995))
* refactor(order/basic): make type class arguments explicit for {*}order.lift
* Let's try again
* And another try
* Silly typo
* Fix error
* Oops, missed this one

### [2019-05-08 20:20:16](https://github.com/leanprover-community/mathlib/commit/7f9717f)
feat(*): preorder instances for with_bot and with_zero ([#996](https://github.com/leanprover-community/mathlib/pull/996))
* feat(*): preorder instances for with_bot and with_zero
* Let's try again

### [2019-05-08 11:42:00](https://github.com/leanprover-community/mathlib/commit/c9cfafc)
chore(tactics): splitting tactics and tests into more files ([#985](https://github.com/leanprover-community/mathlib/pull/985))
* chore(tactics): splitting tactics and tests into more files, cleaning up dependencies
* tweaking comment
* introducing `tactic.basic` and fixing imports
* fixes
* fix copyright
* fix some things

### [2019-05-08 09:47:14](https://github.com/leanprover-community/mathlib/commit/73a30da)
feat(group_theory/subgroup): is_subgroup.inter ([#994](https://github.com/leanprover-community/mathlib/pull/994))

### [2019-05-07 20:44:11-05:00](https://github.com/leanprover-community/mathlib/commit/87cf6e3)
feat(category_theory/category_of_elements) ([#990](https://github.com/leanprover-community/mathlib/pull/990))
* feat(category_theory/category_of_elements)
* Update src/category_theory/elements.lean
Co-Authored-By: semorrison <scott@tqft.net>
* Update src/category_theory/elements.lean
Co-Authored-By: semorrison <scott@tqft.net>
* Update src/category_theory/elements.lean
Co-Authored-By: semorrison <scott@tqft.net>
* Update src/category_theory/punit.lean
Co-Authored-By: semorrison <scott@tqft.net>
* various
* remaining simp lemmas

### [2019-05-07 19:03:46](https://github.com/leanprover-community/mathlib/commit/820bac3)
building the hyperreal library ([#835](https://github.com/leanprover-community/mathlib/pull/835))
* more instances
* fix stuff that got weirded
* fix stuff that got weird
* fix stuff that became weird
* build hyperreal library (with sorries)
* fix weirdness, prettify etc.
* spaces
* st lt le lemmas fix type
* Update src/data/real/hyperreal.lean
Co-Authored-By: abhimanyupallavisudhir <43954672+abhimanyupallavisudhir@users.noreply.github.com>
* if then
* more stuff
* Update hyperreal.lean
* Update hyperreal.lean
* Update basic.lean
* Update basic.lean
* Update hyperreal.lean
* of_max, of_min, of_abs
* Update filter_product.lean
* Update hyperreal.lean
* abs_def etc.
* Update filter_product.lean
* hole
* Update hyperreal.lean
* Update filter_product.lean
* Update filter_product.lean
* Update filter_product.lean
* Update hyperreal.lean
* Update hyperreal.lean
* Update filter_product.lean
* Update hyperreal.lean
* Update hyperreal.lean
* finally done with all sorries!
* Update hyperreal.lean
* fix (?)
* fix (?) ring issue
* real.Sup_univ
* st is Sup
* st_id_real spacebar
* sup --> Sup
* fix weirds
* dollar signs
* 100-column
* 100 columns rule
* Update hyperreal.lean
* removing uparrows
* uparrows
* some stuff that got away
* fix
* lift_id
* fix?
* fix mono, hopefully
* fix mono, hopefully
* this should work
* fix -- no more mono
* fixes
* fixes
* fixes
* fixes
* ok, fixed

### [2019-05-07 17:27:55](https://github.com/leanprover-community/mathlib/commit/4a38d2e)
feat(scripts): add --build-new flag to cache-olean ([#992](https://github.com/leanprover-community/mathlib/pull/992))

### [2019-05-07 10:49:02-04:00](https://github.com/leanprover-community/mathlib/commit/717033e)
chore(build): cron build restarts from scratch

### [2019-05-07 08:45:19](https://github.com/leanprover-community/mathlib/commit/c726c12)
feat(category/monad/cont): monad_cont instances for state_t, reader_t, except_t and option_t ([#733](https://github.com/leanprover-community/mathlib/pull/733))
* feat(category/monad/cont): monad_cont instances for state_t, reader_t,
except_t and option_t
* feat(category/monad/writer): writer monad transformer

### [2019-05-07 01:25:54-04:00](https://github.com/leanprover-community/mathlib/commit/98ba07b)
chore(build): fix stages in cron job

### [2019-05-07 00:28:50-04:00](https://github.com/leanprover-community/mathlib/commit/505f748)
chore(build): build against Lean 3.5 nightly build ([#989](https://github.com/leanprover-community/mathlib/pull/989))

### [2019-05-06 16:50:37](https://github.com/leanprover-community/mathlib/commit/6eba20b)
feat(category_theory): currying for functors ([#981](https://github.com/leanprover-community/mathlib/pull/981))
* feat(category_theory): currying for functors
* Update src/category_theory/currying.lean
Co-Authored-By: semorrison <scott@tqft.net>
* compacting
* fix import
* change from review
* rfl on same line

### [2019-05-06 05:34:58](https://github.com/leanprover-community/mathlib/commit/f536dac)
six(style.md): fix broken code ([#987](https://github.com/leanprover-community/mathlib/pull/987))

### [2019-05-05 11:57:30](https://github.com/leanprover-community/mathlib/commit/23270e7)
feat(ring_theory/adjoin): adjoining elements to form subalgebras ([#756](https://github.com/leanprover-community/mathlib/pull/756))
* feat(ring_theory/adjoin): adjoining elements to form subalgebras
* Fix build
* Change to_submodule into a coercion
* Use pointwise_mul
* add simp attribute to adjoin_empty

### [2019-05-05 07:50:10](https://github.com/leanprover-community/mathlib/commit/3f26ba8)
feat(category_theory/products): associators ([#982](https://github.com/leanprover-community/mathlib/pull/982))

### [2019-05-05 07:02:45](https://github.com/leanprover-community/mathlib/commit/1e8f438)
feat(presheaves) ([#886](https://github.com/leanprover-community/mathlib/pull/886))
* feat(category_theory/colimits): missing simp lemmas
* feat(category_theory): functor.map_nat_iso
* define `functor.map_nat_iso`, and relate to whiskering
* rename `functor.on_iso` to `functor.map_iso`
* add some missing lemmas about whiskering
* fix(category_theory): presheaves, unbundled and bundled, and pushforwards
* restoring `(opens X)ᵒᵖ`
* various changes from working on stalks
* rename `nbhds` to `open_nhds`
* fix introduced typo
* typo
* compactify a proof
* rename `presheaf` to `presheaf_on_space`
* fix(category_theory): turn `has_limits` classes into structures
* naming instances to avoid collisions
* breaking up instances.topological_spaces
* fixing all the other pi-type typclasses
* fix import
* oops
* fix import
* missed one
* typo
* restoring eq_to_hom simp lemmas
* removing unnecessary simp lemma
* remove another superfluous lemma
* removing the nat_trans and vcomp notations; use \hom and \gg
* a simpler proposal
* getting rid of vcomp
* fix
* splitting files
* update notation
* fix
* cleanup
* use iso_whisker_right instead of map_nat_iso
* proofs magically got easier?
* improve some proofs
* remove crap
* minimise imports
* chore(travis): disable the check for minimal imports
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: semorrison <scott@tqft.net>
* writing `op_induction` tactic, and improving proofs
* squeeze_simping
* cleanup
* rearranging
* Update src/category_theory/instances/Top/presheaf.lean
Co-Authored-By: semorrison <scott@tqft.net>
* fix `open` statements, and use `op_induction`
* rename terms of PresheafedSpace to X Y Z. rename field from .X to .to_Top
* forgetful functor
* update comments about unfortunate proofs
* add coercion from morphisms of PresheafedSpaces to morphisms in Top

### [2019-05-05 02:40:54](https://github.com/leanprover-community/mathlib/commit/fc8b08b)
feat(data/set/basic): prod_subset_iff ([#980](https://github.com/leanprover-community/mathlib/pull/980))
* feat(data/set/basic): prod_subset_iff
* syntax

### [2019-05-04 23:56:50](https://github.com/leanprover-community/mathlib/commit/fbce6e4)
fix(data/set/finite): make fintype_seq an instance ([#979](https://github.com/leanprover-community/mathlib/pull/979))

### [2019-05-04 22:16:39](https://github.com/leanprover-community/mathlib/commit/7dea60b)
feat(logic/basic): forall_iff_forall_surj ([#977](https://github.com/leanprover-community/mathlib/pull/977))
a lemma from the perfectoid project

### [2019-05-04 20:01:33](https://github.com/leanprover-community/mathlib/commit/b4d483e)
feat(colimits): arbitrary colimits in Mon and CommRing ([#910](https://github.com/leanprover-community/mathlib/pull/910))
* feat(category_theory): working in Sort rather than Type, as far as possible
* missed one
* adding a comment about working in Type
* remove imax
* removing `props`, it's covered by `types`.
* fixing comment on `rel`
* tweak comment
* add matching extend_π lemma
* remove unnecessary universe annotation
* another missing s/Type/Sort/
* feat(category_theory/shapes): basic shapes of cones and conversions
minor tweaks
* Moving into src. Everything is borked.
* investigating sparse
* blech
* maybe working again?
* removing terrible square/cosquare names
* returning to filtered colimits
* colimits in Mon
* rename
* actually jump through the final hoop
* experiments
* fixing use of ext
* feat(colimits): colimits in Mon and CommRing
* fixes
* removing stuff I didn't mean to have in here
* minor
* fixes
* merge
* update after merge
* fix import

### [2019-05-04 12:06:04-05:00](https://github.com/leanprover-community/mathlib/commit/c7baf8e)
feat(option/injective_map) ([#978](https://github.com/leanprover-community/mathlib/pull/978))

### [2019-05-03 21:34:29](https://github.com/leanprover-community/mathlib/commit/f98ffde)
feat(tactic/decl_mk_const): performance improvement for library_search ([#967](https://github.com/leanprover-community/mathlib/pull/967))
* feat(tactic/decl_mk_const): auxiliary tactic for library_search [WIP]
* use decl_mk_const in library_search
* use decl_mk_const
* move into tactic/basic.lean

### [2019-05-03 13:58:06-04:00](https://github.com/leanprover-community/mathlib/commit/7b1105b)
chore(build): build only master and its related PRs

### [2019-05-03 13:37:08-04:00](https://github.com/leanprover-community/mathlib/commit/e747c91)
chore(README): put the badges in the README on one line ([#975](https://github.com/leanprover-community/mathlib/pull/975))

### [2019-05-03 12:35:46-04:00](https://github.com/leanprover-community/mathlib/commit/f2db636)
feat(docs/install_debian): Debian startup guide ([#974](https://github.com/leanprover-community/mathlib/pull/974))
* feat(docs/install_debian): Debian startup guide
* feat(scripts/install_debian): One-line install for Debian  [ci skip]
* fix(docs/install_debian*): Typos pointed out by Johan
Also adds a summary of what will be installed

### [2019-05-03 11:30:19-05:00](https://github.com/leanprover-community/mathlib/commit/f5060c4)
feat(category_theory/limits): support for special shapes of (co)limits ([#938](https://github.com/leanprover-community/mathlib/pull/938))
feat(category_theory/limits): support for special shapes of (co)limits

### [2019-05-03 15:24:11+02:00](https://github.com/leanprover-community/mathlib/commit/219cb1a)
chore(travis): disable the check for minimal imports ([#973](https://github.com/leanprover-community/mathlib/pull/973))

### [2019-05-03 14:11:01+01:00](https://github.com/leanprover-community/mathlib/commit/44386cd)
chore(docs): delete docs/wip.md ([#972](https://github.com/leanprover-community/mathlib/pull/972))
* chore(docs): delete docs/wip.md
long outdated
* remove link in README

### [2019-05-03 10:59:45](https://github.com/leanprover-community/mathlib/commit/3eb7ebc)
remove code duplication ([#971](https://github.com/leanprover-community/mathlib/pull/971))

### [2019-05-02 22:55:52+01:00](https://github.com/leanprover-community/mathlib/commit/6956daa)
fix(data/polynomial): change instance order in polynomial.subsingleton ([#970](https://github.com/leanprover-community/mathlib/pull/970))

### [2019-05-02 17:32:09](https://github.com/leanprover-community/mathlib/commit/60b3c19)
fix(scripts/remote-install-update-mathlib): apt shouldn't ask ([#969](https://github.com/leanprover-community/mathlib/pull/969))

### [2019-05-02 12:29:34-04:00](https://github.com/leanprover-community/mathlib/commit/d288905)
fix(script/remote-install-update-mathlib) fix answer reading and requests/urllib3 version conflict ([#968](https://github.com/leanprover-community/mathlib/pull/968))

### [2019-05-02 08:40:53](https://github.com/leanprover-community/mathlib/commit/8a097f1)
feat(ring_theory/ideal_operations): inj_iff_trivial_ker for ring homomorphisms ([#951](https://github.com/leanprover-community/mathlib/pull/951))
* feat(ring_theory/ideal_operations): inj_iff_trivial_ker for ring homomorphisms
* Update subgroup.lean
* Update ideal_operations.lean

### [2019-05-02 08:08:14](https://github.com/leanprover-community/mathlib/commit/ef11fb3)
feat(category_theory/limits/opposites): (co)limits in opposite categories ([#926](https://github.com/leanprover-community/mathlib/pull/926))
* (co)limits in opposite categories
* moving lemmas
* moving stuff about complete lattices to separate PR
* renaming category_of_preorder elsewhere
* build limits functor/shape at a time
* removing stray commas, and making one-liners
* remove non-terminal simps

### [2019-05-02 04:37:39](https://github.com/leanprover-community/mathlib/commit/69094fc)
fix(tactic/library_search): iff lemmas with universes ([#935](https://github.com/leanprover-community/mathlib/pull/935))
* fix(tactic/library_search): iff lemmas with universes
* cleaning up
* add crossreference

### [2019-05-02 02:35:03](https://github.com/leanprover-community/mathlib/commit/9b7fb5f)
feat(category_theory/limits): complete lattices have (co)limits ([#931](https://github.com/leanprover-community/mathlib/pull/931))
* feat(category_theory/limits): complete lattices have (co)limits
* Update lattice.lean

### [2019-05-01 08:53:51-04:00](https://github.com/leanprover-community/mathlib/commit/b3433a5)
feat(script/auth_github): improve messages [ci skip] ([#965](https://github.com/leanprover-community/mathlib/pull/965))