### [2020-01-31 17:07:56](https://github.com/leanprover-community/mathlib/commit/5ce0c0a)
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

### [2020-01-31 14:13:56+01:00](https://github.com/leanprover-community/mathlib/commit/ddba2ae)
chore(scripts/nolints): regenerate

### [2020-01-31 12:11:16](https://github.com/leanprover-community/mathlib/commit/a8ba81b)
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

### [2020-01-30 15:28:23-08:00](https://github.com/leanprover-community/mathlib/commit/cae9cc9)
chore(ci): remove unused olean-rs setup from build ([#1932](https://github.com/leanprover-community/mathlib/pull/1932))

### [2020-01-30 18:49:20](https://github.com/leanprover-community/mathlib/commit/80f5bd5)
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

### [2020-01-30 17:24:56](https://github.com/leanprover-community/mathlib/commit/4c2d678)
fix(data/set/finite): finite.fintype is a def ([#1931](https://github.com/leanprover-community/mathlib/pull/1931))

### [2020-01-30 15:16:25](https://github.com/leanprover-community/mathlib/commit/b7e5f75)
fix(tactic/scc): detect Props ([#1930](https://github.com/leanprover-community/mathlib/pull/1930))
* fix(tactic/scc): detect Props
* test(test/tactics): add test

### [2020-01-30 13:41:06](https://github.com/leanprover-community/mathlib/commit/1bd23bf)
feat(tactic/use): apply exists_prop after use ([#1882](https://github.com/leanprover-community/mathlib/pull/1882))
* feat(tactic/use): apply exists_prop after use
* change implementation

### [2020-01-30 11:13:26](https://github.com/leanprover-community/mathlib/commit/dcbc719)
fix(tactic/squeeze): compatibility with `simp [<-...]` ([#1923](https://github.com/leanprover-community/mathlib/pull/1923))
* Add polyfills to `squeeze_simp` which should ensure compatibility with Lean 3.4 and 3.5
* Use `decode_simp_arg_list` so `squeeze_simp` doesn't have to pattern-match
(Except of course for the polyfill `has_to_tactic_format simp_arg_type` instance...)
* Reword comment for `erase_simp_args`

### [2020-01-30 08:20:49](https://github.com/leanprover-community/mathlib/commit/9bc0178)
fix(tactic/finish): fix one classical leak, document another ([#1929](https://github.com/leanprover-community/mathlib/pull/1929))
* fix(tactic/finish): fix one classical leak, document another
* fix(src/tactic): deprecate intuitionistic versions in docstrings. Closes [#1927](https://github.com/leanprover-community/mathlib/pull/1927).

### [2020-01-30 00:09:21](https://github.com/leanprover-community/mathlib/commit/868333b)
feat(data/W): show finitely branching W types are encodable ([#1817](https://github.com/leanprover-community/mathlib/pull/1817))
* feat(data/equiv,data/fintype): an encodable fintype is equiv to a fin
* feat(data/W): finitely branching W types are encodable
* feat(archive/examples/prop_encodable): show a type of propositional formulas is encodable
* fix(data/W): remove unused type class argument
* fix(data/equiv): add two docstrings
* fix(*): multiple fixes from code review

### [2020-01-29 18:36:33](https://github.com/leanprover-community/mathlib/commit/4ac87ab)
chore(category_theory): use the new @[ext] attribute on structures ([#1663](https://github.com/leanprover-community/mathlib/pull/1663))
* chore(category_theory): use the new @[ext] attribute on structures
* fixes
* unnecessary repeated exts

### [2020-01-29 17:00:12](https://github.com/leanprover-community/mathlib/commit/4aa3eee)
chore(*): add inhabited instances ([#1898](https://github.com/leanprover-community/mathlib/pull/1898))
* chore(*): add inhabited instances
* Fix linting errors.

### [2020-01-28 21:32:29+01:00](https://github.com/leanprover-community/mathlib/commit/b368312)
fix(ci): set GITHUB_TOKEN environment variable for gothub ([#1920](https://github.com/leanprover-community/mathlib/pull/1920))

### [2020-01-28 20:04:21+01:00](https://github.com/leanprover-community/mathlib/commit/99962ad)
fix(ci): unshallow repo before pushing nightly tags ([#1919](https://github.com/leanprover-community/mathlib/pull/1919))

### [2020-01-28 18:53:21](https://github.com/leanprover-community/mathlib/commit/a948e31)
chore(analysis/convex): move to `analysis/convex/basic` ([#1918](https://github.com/leanprover-community/mathlib/pull/1918))

### [2020-01-28 18:27:54+01:00](https://github.com/leanprover-community/mathlib/commit/e36d7ec)
fix(ci): work around github hack

### [2020-01-28 16:36:42+01:00](https://github.com/leanprover-community/mathlib/commit/8e0d47a)
fix(ci): try again to fix authentication

### [2020-01-28 14:09:28+01:00](https://github.com/leanprover-community/mathlib/commit/75743ac)
fix(scripts/deploy_nightly.sh): try to fix CI ([#1917](https://github.com/leanprover-community/mathlib/pull/1917))

### [2020-01-28 11:49:19](https://github.com/leanprover-community/mathlib/commit/cafd193)
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

### [2020-01-27 20:50:19](https://github.com/leanprover-community/mathlib/commit/bba8473)
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

### [2020-01-27 16:29:02](https://github.com/leanprover-community/mathlib/commit/5f01591)
fix(.github/workflows/build): set pipefail ([#1911](https://github.com/leanprover-community/mathlib/pull/1911))
Without `pipefail`, the shell command `false | cat` terminates
successfully.

### [2020-01-27 14:52:05](https://github.com/leanprover-community/mathlib/commit/898cd70)
fix(archive/cubing_a_cube): roof broken by [#1903](https://github.com/leanprover-community/mathlib/pull/1903) ([#1912](https://github.com/leanprover-community/mathlib/pull/1912))

### [2020-01-26 21:08:12](https://github.com/leanprover-community/mathlib/commit/497e692)
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

### [2020-01-26 19:37:06](https://github.com/leanprover-community/mathlib/commit/587b312)
refactor(order/filter/basic): redefine `filter.pure` ([#1889](https://github.com/leanprover-community/mathlib/pull/1889))
* refactor(order/filter/basic): redefine `filter.pure`
New definition has `s ∈ pure a` definitionally equal to `a ∈ s`.
* Update src/order/filter/basic.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* Minor fixes suggested by @gebner
* Fix compile
* Update src/order/filter/basic.lean

### [2020-01-26 15:54:48](https://github.com/leanprover-community/mathlib/commit/ce2e7a8)
feat(linear_algebra/multilinear): image of sum ([#1908](https://github.com/leanprover-community/mathlib/pull/1908))
* staging
* fix build
* linting
* staging
* docstring

### [2020-01-26 13:49:29](https://github.com/leanprover-community/mathlib/commit/ab155ef)
refactor(*): refactor `sum_smul`/`smul_sum` ([#1910](https://github.com/leanprover-community/mathlib/pull/1910))
* refactor(*): refactor `sum_smul`/`smul_sum`
API changes:
* Define both versions for `list, `multiset`, and `finset`;
* new `finset.smul_sum` is the old `finset.smul_sum` or `_root_.sum_smul.symm``
* new `finset.sum_smul` is the old `finset.smul_sum'`
* new `smul_smul` doesn't need a `Type` argument
* some lemmas are generalized to a `semimodule` or a `distrib_mul_action`
* Fix compile

### [2020-01-26 03:58:09](https://github.com/leanprover-community/mathlib/commit/2297d20)
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

### [2020-01-26 01:12:21](https://github.com/leanprover-community/mathlib/commit/9decec2)
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

### [2020-01-25 23:45:34](https://github.com/leanprover-community/mathlib/commit/d3e5621)
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

### [2020-01-25 21:18:30](https://github.com/leanprover-community/mathlib/commit/d4aa088)
fix(scripts/deploy_nightly): fill in blank env vars ([#1909](https://github.com/leanprover-community/mathlib/pull/1909))
* fix(scripts/deploy_nightly): fill in blank env vars
* fix: LEAN_VERSION="lean-3.4.2"

### [2020-01-25 14:01:56](https://github.com/leanprover-community/mathlib/commit/7077242)
doc (analysis/normed_space/operator_norm): cleanup ([#1906](https://github.com/leanprover-community/mathlib/pull/1906))
* doc (analysis/normed_space/operator_norm): cleanup
* typo

### [2020-01-25 12:31:17](https://github.com/leanprover-community/mathlib/commit/8c9a15e)
feat(topology/instances/ennreal): continuity of multiplication by const ([#1905](https://github.com/leanprover-community/mathlib/pull/1905))
* feat(topology/instances/ennreal): continuity of multiplication by const
* Fix compile

### [2020-01-25 10:51:17](https://github.com/leanprover-community/mathlib/commit/20f153a)
fix(scripts/deploy_nightly): token is now just the PAT, need to add user ([#1907](https://github.com/leanprover-community/mathlib/pull/1907))

### [2020-01-25 08:42:04](https://github.com/leanprover-community/mathlib/commit/3bbf8eb)
feat(data/real/nnreal): a few lemmas about subtraction ([#1904](https://github.com/leanprover-community/mathlib/pull/1904))

### [2020-01-24 23:34:43](https://github.com/leanprover-community/mathlib/commit/3b9ee8e)
doc(geometry/manifold): fix markdown ([#1901](https://github.com/leanprover-community/mathlib/pull/1901))
* doc(geometry/manifold): fix markdown
* Update src/geometry/manifold/manifold.lean
* Update src/geometry/manifold/manifold.lean
* Update src/geometry/manifold/manifold.lean
* Update src/geometry/manifold/manifold.lean

### [2020-01-24 21:56:45+01:00](https://github.com/leanprover-community/mathlib/commit/d075695)
fix(build): typo in deploy_nightly script name ([#1902](https://github.com/leanprover-community/mathlib/pull/1902))

### [2020-01-24 20:01:58+01:00](https://github.com/leanprover-community/mathlib/commit/2db02b8)
feat(.github): switch to github actions for ci ([#1893](https://github.com/leanprover-community/mathlib/pull/1893))

### [2020-01-24 12:07:12](https://github.com/leanprover-community/mathlib/commit/601d5b1)
feat(tactic/simp_rw): add `simp_rw` tactic, a mix of `simp` and `rw` ([#1900](https://github.com/leanprover-community/mathlib/pull/1900))
* add `simp_rw` tactic that is a mix of `simp` and `rw`
* Style fixes
* Module documentation for the file `tactic/simp_rw.lean`
* Apply suggestions to improve documentation of `simp_rw`
* Documentation and tests for `simp_rw [...] at ...`

### [2020-01-24 09:09:29](https://github.com/leanprover-community/mathlib/commit/69099f0)
feat(order/filter/bases): define `filter.has_basis` ([#1896](https://github.com/leanprover-community/mathlib/pull/1896))
* feat(*): assorted simple lemmas, simplify some proofs
* feat(order/filter/bases): define `filter.has_basis`
* Add `@[nolint]`
* +1 lemma, +1 simplified proof
* Remove whitespaces
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Ref. note nolint_ge

### [2020-01-24 00:47:07](https://github.com/leanprover-community/mathlib/commit/aad853b)
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

### [2020-01-22 20:10:27](https://github.com/leanprover-community/mathlib/commit/b686bc2)
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

### [2020-01-22 00:57:34](https://github.com/leanprover-community/mathlib/commit/96ee2a6)
feat(order/filter/basic): prove `@cofinite ℕ = at_top` ([#1888](https://github.com/leanprover-community/mathlib/pull/1888))
* feat(order/filter/basic): prove `@cofinite ℕ = at_top`
Also generalize `not_injective_(nat/int)_fintype`, and use `[infinite
α]` instead of `set.infinite (@univ α)` as an argument.
* Update src/data/equiv/basic.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* Drop a duplicate definition, thanks @ChrisHughes24

### [2020-01-21 21:29:04](https://github.com/leanprover-community/mathlib/commit/aa6cc06)
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

### [2020-01-21 18:58:28](https://github.com/leanprover-community/mathlib/commit/217b5e7)
refactor(algebra/char_zero): use `function.injective` ([#1894](https://github.com/leanprover-community/mathlib/pull/1894))
No need to require `↔` in the definition.

### [2020-01-21 09:56:58](https://github.com/leanprover-community/mathlib/commit/f3835fa)
feat(*): assorted simple lemmas, simplify some proofs ([#1895](https://github.com/leanprover-community/mathlib/pull/1895))
* feat(*): assorted simple lemmas, simplify some proofs
* +1 lemma, +1 simplified proof

### [2020-01-18 08:16:09](https://github.com/leanprover-community/mathlib/commit/d32c797)
feat(data/bool): coe_bool_iff ([#1891](https://github.com/leanprover-community/mathlib/pull/1891))

### [2020-01-18 05:20:13](https://github.com/leanprover-community/mathlib/commit/d548d92)
chore(ring_theory/polynomial): remove decidable_eq assumptions ([#1890](https://github.com/leanprover-community/mathlib/pull/1890))

### [2020-01-17 18:46:09](https://github.com/leanprover-community/mathlib/commit/c8ae79d)
feat(measure_theory/bochner_integration): dominated convergence theorem for filters ([#1884](https://github.com/leanprover-community/mathlib/pull/1884))
* Dominated convergence theorem for filters
* Update bases.lean
* Update bochner_integration.lean
* reviewer's comments

### [2020-01-17 03:02:01](https://github.com/leanprover-community/mathlib/commit/9ac26cb)
feat(geometry/manifold/mfderiv): derivative of functions between smooth manifolds ([#1872](https://github.com/leanprover-community/mathlib/pull/1872))
* feat(geometry/manifold/mfderiv): derivative of functions between smooth manifolds
* Update src/geometry/manifold/mfderiv.lean
Co-Authored-By: Yury G. Kudryashov <urkud@ya.ru>
* more details in docstrings [ci skip]
* fix docstrings [ci skip]
* reviewer's comments

### [2020-01-16 11:40:38](https://github.com/leanprover-community/mathlib/commit/4f81942)
feat(logic/basic): forall_or_distrib ([#1887](https://github.com/leanprover-community/mathlib/pull/1887))

### [2020-01-16 10:23:06](https://github.com/leanprover-community/mathlib/commit/58610ff)
chore(order/filter/*): use `s ∈ f` instead of `s ∈ f.sets` ([#1885](https://github.com/leanprover-community/mathlib/pull/1885))
Other changes:
* compose old `mem_infi` and `mem_binfi` with `mem_Union` and
  `mem_bUnion_iff` to avoid `.sets` and simplify usage (it was
  `rw [mem_infi, mem_Union]` every time)
* drop `lift_sets_eq` and `mem_lift_iff` in favor of `mem_lift_sets`

### [2020-01-16 08:11:17](https://github.com/leanprover-community/mathlib/commit/05457fd)
feat(analysis/calculus/tangent_cone): define and use `tangent_cone_congr` ([#1886](https://github.com/leanprover-community/mathlib/pull/1886))
* feat(analysis/calculus/tangent_cone): define and use `tangent_cone_congr`
This way some proofs become shorter and hopefully more readable.
* Add a docstring

### [2020-01-15 15:04:46](https://github.com/leanprover-community/mathlib/commit/b3ed6e6)
chore(*): use `ne_` instead of `neq_` in lemma names ([#1878](https://github.com/leanprover-community/mathlib/pull/1878))
One exception: `mem_sets_of_neq_bot` is now `mem_sets_of_eq_bot`
because it has an equality as an assumption.
Also add `filter.infi_ne_bot_(iff_?)of_directed'` with a different
`nonempty` assumption, and use it to simplify the proof of
`lift_ne_bot_iff`.

### [2020-01-15 10:13:40](https://github.com/leanprover-community/mathlib/commit/8e70388)
docs(README): add new maintainers ([#1881](https://github.com/leanprover-community/mathlib/pull/1881))

### [2020-01-15 09:15:30](https://github.com/leanprover-community/mathlib/commit/d614736)
feat(linear_algebra/tensor_product): tensor product right identity ([#1880](https://github.com/leanprover-community/mathlib/pull/1880))
* feat(linear_algebra/tensor_product): tensor product right identity
* Golf proof of tensor_product.rid
* Add missing docstrings

### [2020-01-15 07:24:37](https://github.com/leanprover-community/mathlib/commit/819939f)
refactor(order/lattice): generalize `directed_of_mono` ([#1879](https://github.com/leanprover-community/mathlib/pull/1879))
It suffices to have `semilattice_sup`, not `decidable_linear_order`.
Also add `directed_of_antimono`.

### [2020-01-14 16:00:47](https://github.com/leanprover-community/mathlib/commit/9f7ae9a)
chore(data/set/lattice): use `∃ x ∈ s` instead of `∃ x, x ∈ s ∧` in `mem_bUnion_iff` ([#1877](https://github.com/leanprover-community/mathlib/pull/1877))
This seems to be more in line with the rest of the library

### [2020-01-14 14:20:21](https://github.com/leanprover-community/mathlib/commit/416b7d8)
fix doc strings ([#1876](https://github.com/leanprover-community/mathlib/pull/1876))

### [2020-01-14 06:33:00](https://github.com/leanprover-community/mathlib/commit/e095e30)
feat(analysis/ODE/gronwall): A version of Grönwall's inequality ([#1846](https://github.com/leanprover-community/mathlib/pull/1846))
* feat(analysis/ODE/gronwall): A version of Gronwall's inequality
+ uniqueness of solutions of an ODE with a Lipschitz continuous RHS
* Consistently use ö in Grönwall
* Fix a typo
* Fix docs, drop assumption `0 < K`, add a version for functions `ℝ → ℝ`.
* Fix docs
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* Fix docs

### [2020-01-12 06:48:46](https://github.com/leanprover-community/mathlib/commit/c5d91bc)
feat(topology/algebra/ordered): add order topology for partial orders… ([#1276](https://github.com/leanprover-community/mathlib/pull/1276))
* feat(topology/algebra/ordered): doc, add convergence in ordered groups criterion
* docstring
* reviewer's comments

### [2020-01-11 14:51:07](https://github.com/leanprover-community/mathlib/commit/25dded2)
chore(measure_theory/bochner_integration): make proofs shorter ([#1871](https://github.com/leanprover-community/mathlib/pull/1871))
* More consistent use of the dot notation
* Revert "More consistent use of the dot notation"
This reverts commit 854a499a9be105b42ca486eb25593a2379b07404.
* Revert "Revert "More consistent use of the dot notation""
This reverts commit 57aaf22695c031fc8dcc581110cc9d1ac397f695.
* fix things

### [2020-01-11 00:42:53](https://github.com/leanprover-community/mathlib/commit/f67df78)
chore(algebra/module): add some missing `*_cast` tags ([#1863](https://github.com/leanprover-community/mathlib/pull/1863))

### [2020-01-10 01:05:49](https://github.com/leanprover-community/mathlib/commit/ff2a41e)
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

### [2020-01-09 22:58:55](https://github.com/leanprover-community/mathlib/commit/baa3aa7)
refactor(data/set/basic): change def of `⊂` to match `<` ([#1862](https://github.com/leanprover-community/mathlib/pull/1862))

### [2020-01-09 21:23:09](https://github.com/leanprover-community/mathlib/commit/d7cebcf)
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

### [2020-01-09 04:14:44](https://github.com/leanprover-community/mathlib/commit/39c10cd)
docs(tactic/tauto): elaborate tauto docs [ci skip] ([#1869](https://github.com/leanprover-community/mathlib/pull/1869))

### [2020-01-09 02:47:17](https://github.com/leanprover-community/mathlib/commit/5289994)
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

### [2020-01-08 20:16:58](https://github.com/leanprover-community/mathlib/commit/9afc6f2)
docs(tactics): tautology ([#1860](https://github.com/leanprover-community/mathlib/pull/1860))
* added a short description of the tautology tactic
* added a short description of the tautology tactic
* Update docs/tactics.md
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2020-01-08 13:16:54](https://github.com/leanprover-community/mathlib/commit/92841c2)
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

### [2020-01-07 00:44:17](https://github.com/leanprover-community/mathlib/commit/69e07e2)
chore(order/zorn): add docstrings, drop `chain.directed` ([#1861](https://github.com/leanprover-community/mathlib/pull/1861))
`chain.directed_on` is almost the same and uses a named predicate.

### [2020-01-06 23:48:35](https://github.com/leanprover-community/mathlib/commit/a1b7312)
feat(topology/maps): a few lemmas about `is_open_map` ([#1855](https://github.com/leanprover-community/mathlib/pull/1855))
* feat(topology/maps): a few lemmas about `is_open_map`
Also fix arguments order in all `*.comp` in this file.
* Use restricted version of `continuous_of_left_inverse` to prove non-restricted
* Fix compile by reverting a name change

### [2020-01-06 03:49:33](https://github.com/leanprover-community/mathlib/commit/15c434a)
chore(*): various simple lemmas about `*_equiv`, add missing attrs ([#1854](https://github.com/leanprover-community/mathlib/pull/1854))
* chore(*): various simple lemmas about `*_equiv`, add missing attrs
* Fix compile of `ring_theory/localization`

### [2020-01-05 21:25:17](https://github.com/leanprover-community/mathlib/commit/63670b5)
feat(data/real/nnreal): add a few simple lemmas ([#1856](https://github.com/leanprover-community/mathlib/pull/1856))

### [2020-01-04 15:28:27](https://github.com/leanprover-community/mathlib/commit/585e107)
feat(topology/algebra/module): continuous linear equiv ([#1839](https://github.com/leanprover-community/mathlib/pull/1839))
* feat(topology/algebra/module): continuous linear equiv
* linting
* reviewer's comments

### [2020-01-02 22:16:08](https://github.com/leanprover-community/mathlib/commit/5c3606d)
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

### [2020-01-02 19:10:24](https://github.com/leanprover-community/mathlib/commit/840bd1f)
feat(analysis/calculus/deriv): add aliases for `const op f` and `f op const` ([#1843](https://github.com/leanprover-community/mathlib/pull/1843))
* feat(analysis/calculus/deriv): add aliases for `const op f` and `f op const`
Often this leads to simpler answers.
* Docs
* Fix compile of `mean_value.lean`
* Drop comments, use `open_locale classical`

### [2020-01-02 18:35:24](https://github.com/leanprover-community/mathlib/commit/7b18bbf)
feat(topology/algebra/ordered): add `*_mem_nhds_within_Ioi`, reorder args of `is_closed.Icc_subset_of_forall_exists_gt` ([#1844](https://github.com/leanprover-community/mathlib/pull/1844))

### [2020-01-02 10:40:36](https://github.com/leanprover-community/mathlib/commit/033ecbf)
chore(topology/*): add a few more trivial `continuous_(within_)at` lemmas ([#1842](https://github.com/leanprover-community/mathlib/pull/1842))

### [2020-01-02 09:04:12](https://github.com/leanprover-community/mathlib/commit/ffa9785)
feat(topology/algebra/ordered): prove that `nhds_within (Ioi a) b ≠ ⊥` if `a ≤ b` ([#1841](https://github.com/leanprover-community/mathlib/pull/1841))
+ few similar statements
Also drop decidability assumption in `closure_Ioo` etc. We don't care
about using classical reasoning anyway, and usage of `classical.DLO`
here doesn't lead to any `noncomputable` defs.

### [2020-01-01 22:13:19](https://github.com/leanprover-community/mathlib/commit/d08d509)
fix(metric_space/gromo_hausdorff): lemma should be instance + linting ([#1840](https://github.com/leanprover-community/mathlib/pull/1840))